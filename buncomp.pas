program buncomp;

{                                                                           }
{ Bunnylin's Chromaticity Compressor                                        }
{                                                                           }
{ (compiles for win32 with FPC 3.0.4)                                       }
{                                                                           }
{ This utility compresses a source image's colors to 64k or less,           }
{ optimising the palette distribution for best visual presentation.         }
{ The algorithm is pretty heavy, so it's not appropriate for real-time use. }
{                                                                           }
{ CC0, 2014-2018 :: Kirinn Bunnylin / MoonCore                              }
{ This program and its source code may be freely used, studied, copied,     }
{ consumed, modified and distributed, by anyone, for any purpose.           }
{                                                                           }
{ This program assumes a reference white point of D65 as defined in BT.709  }
{ and BT.2020, the most common standard.                                    }
{                                                                           }

// TODO: The algorithm could be improved by using a least-total-error
// strategy, while taking dithering into account... could be slower, though.
// Try placing virtual palette entries at dithered color points; 50-50 puts
// one virtual pe halfway between its parent colors, 75-25 puts three, etc.

// - Rendered/dithered viewdata should always be 32bpp for easier
//   implementation, but with a flag indicating whether alpha data is real
// - Alpha in diffYCC too must be premultiplied, otherwise a preset palette
//   item with a colored alpha may be ignored in favor of a solid black
// - Diff result won't fit in 32bits without some loss of accuracy, since
//   premultiplied alpha and squaring adds up; use qword or double?
// - Test different diffRGB functions, pick one or two best:
//   (linear vs. sRGB while calculating delta) x
//   (super-weighed vs. weighed vs. non) x
//   (linear vs. sRGB while summing squares)
//   = 12 combinations; use on 2 photos, 2 vector art, 2 gradient stress pics
// - mclogo_wip with newdiffrgb gets stuck in infinite loop??
// - Paste to clipboard should use a fast PNG, with dib v4/5 as fallback
// - Further modularise the code
// - Source image hgram buckets should probably persist, and increase to 8k?
// - Colors should possibly keep alpha-multiplied copies of selves in cache?
// - Add command line functionality if not yet preset, add to documentation
// - Add menu select "Export using minimal palette", default yes; when off,
//   saves and copies to clipboard in 32-bit RGBA
// - Could the program accept new source images by drag and drop?
// - Switch to fpGUI to achieve cross-platform support
// - Change YCbCr to YCH, perhaps better suited
// - Try cielab again, the CIEDE2000 definition is the latest word on the
//   subject. A color comparison implementation exists already for Excel.
// - Revisit the flat color detector to dismiss any color areas that are not
//   bordered at some distance by a distinctive edge; otherwise chances are
//   that a seemingly flat expanse is just a part of a gradient
// - Does Preserve contrast even do anything??
// - take more attractive screenshots for site

{$mode fpc}
{$apptype GUI}
{$GOTO ON} // only used once and it improves code readability there :p
{$codepage UTF8}
{$I-}
{$resource bunny.res}

{$WARN 4079 off} // Spurious hints: Converting the operands to "Int64" before
{$WARN 4080 off} // doing the operation could prevent overflow errors.
{$WARN 4081 off}
{$WARN 5090 off} // Variable of a managed type not initialised, supposedly.

{$define !allowLAB} // <-- the diffLAB function isn't updated to use RGBA64

uses windows,
     commdlg,
     {$ifdef allowLAB}math,{$endif}
     mcgloder,
     mccommon;

type RGBtrio = packed record b, g, r : byte; end;
     RGBarray = array[0..$FFFFFF] of rgbtrio;
     // Defined in MCGLoder:
     // RGBA64 = packed record b, g, r, a : word; end;
     // RGBquad = packed record b, g, r, a : byte; end;
     // RGBAarray = array[0..$FFFFFF] of rgbquad;
     // bitmaptype = packed record
     //   image : pointer;
     //   palette : array of rgbquad;
     //   sizex, sizey : word;
     //   memformat, bitdepth : byte;
     // end;
     // pbitmaptype = ^bitmaptype;

const mv_ProgramName : string = 'BunComp' + chr(0);
      version = 'v1.19 02-May-2017';
      viewclass : string[9] = 'RDCVIEWC' + chr(0);
      magicclass : string[9] = 'RDCMAGIC' + chr(0);
      helpclass : string[9] = 'RDCHELPC' + chr(0);
      mainclass : string[9] = 'RDCMAINC' + chr(0);
      CSIDL_APPDATA = 26; // to use with winshell SHGetSpecialFolderLocation

var mainsizex, mainsizey, magicx, magicy : word;
    funsizex, funsizey, helpsizex, helpsizey : word;
    lastactiveview : byte;
    viewdata : array[0..16] of record
      bmpdata : bitmaptype;
      winsizex, winsizey : word;
      viewofsx, viewofsy : integer;
      buffy : pointer;
      winhandu : hwnd;
      deeku : hdc;
      buffyh, oldbuffyh : hbitmap;
      zoom, alpha : byte;
    end;

    numflats : dword;
    flats : array of record // viewdata[0] flat color auto-detection
      color : RGBquad;
      weight : dword;
    end;

    acolor : RGBquad; // the alpha-rendering color
    compressorthreadID : TThreadID; // color compression is done in a thread
    compressorthreadhandle : handle;
    rendimu : bitmaptype; // the end result goes here; the new window with
                          // this can only be spawned from the main thread...
    tempbmp : bitmaptype;

    mv_ListBuffy, mv_FunBuffy : pointer;
    neutralcolor : RGBquad; // used to render N/A elements, system grey
    mv_MainWinH, funwinhandle, HelpWinH : handle;
    funstatus, funpal, funbutton, helptxth : handle;
    mv_DC, mv_ListBuffyDC : hdc;
    mv_Contextmenu : hmenu;
    mv_ListBuffyHandle, mv_OldListBuffyHandle, mv_FunDIBhandle : hbitmap;
    mv_FontH, mv_EditH : array[1..2] of handle;
    mv_ListH : array[1..3] of handle;
    mv_ButtonH : array[1..6] of handle;
    mv_StaticH : array[0..7] of handle;
    mv_SliderH : array[1..2] of handle;
    mv_ColorBlockH, mv_CBBrushH, mv_AcceleratorTable : handle;
    bminfo : bitmapinfo;
    mousescrollx, mousescrolly : integer;
    mousescrolling, colorpicking, compressing, batchprocess : boolean;
    mv_EndProgram, updatefun : boolean;
    rr : rect;
    mv_Dlg : packed record // hacky thing for spawning dialog boxes
      headr : DLGTEMPLATE;
      data : array[0..31] of byte;
    end;

    homedir : string;

    option : record
      palsize : word; // target palette size
      maxcontrast, dithering, colorspace, flat_favor : byte;
    end;
    {$ifdef allowLAB}
    labtable : array[0..65535] of word;
    {$endif}

type pe_status = (PE_FREE, PE_ALLOCATED, PE_FIXED, PE_AUTOFLAT);
    // Palette entries, both presets and algorithmically calculated go here.
var pe : array of record
      colo : RGBquad;
      colog : RGBA64; // for the gamma-corrected values
      status : pe_status;
      rstack, gstack, bstack, astack : qword;
      matches : dword;
    end;
    pe_used : dword;
    // This function is dynamically grabbed from shfolder.dll, but only if
    // stdout.txt cannot be written into the program's own directory.
    // I prefer keeping programs neatly in one place, so by default
    // everything stays under the program directory. But Win7, Vista, and
    // potentially XP may disallow write access to the program directory, and
    // then all file output must go into \Application Data\BunComp\.
    SHGetSpecialFolderPath : function(hwndOwner : HWND; lpszPath : pointer; csidl : longint; fCreate : boolean) : boolean; stdcall;

const hgram_bucket_count = 4096;

{$ifdef allowLAB}
const colorspacename : array[0..2] of string[9] = (
'RGB', 'YCC', 'CIEDE2000');
{$else}
const colorspacename : array[0..1] of string[3] = (
'RGB', 'YCC');
{$endif}

const dithername : array[0..6] of string[24] = (
'No dithering', 'Checkerboard', 'Quarterdither', 'Ordered 4x4',
'Diffusive Sierra Lite', 'Horizontal bars', 'Ordered plus');

// OctaDTab is used as the pattern for the Bayerish ordered 4x4 dither
const octadtab : array[0..3,0..3] of byte = (
( 6,14, 7,15),
(10, 1,12, 3),
( 8,16, 5,13),
(11, 4, 9, 2));

// PlusDTab is used as the pattern for a less regular ordered dither.
const plusdtab : array[0..4,0..4] of byte = (
(2,5,1,3,4),
(1,3,4,2,5),
(4,2,5,1,3),
(5,1,3,4,2),
(3,4,2,5,1));

const helptxt : array[0..$16] of string = (
'Bunnylin''s Chromaticity Compressor' + chr(13) + chr(10) + version,
'You can use this program to reduce the colors used by an image!',
'First load a source image, either by pasting from the clipboard, or by selecting Open from the File menu. Since I could not think of a good way to handle multiple source images in the interface, you can only have one source image open at a time.',
'You can ZOOM in and out by activating the image window and pressing the PLUS and MINUS keys. If the image does not fit in the window, you can mouse-scroll by holding down the primary mouse button.',
'Select your desired output palette size, and hit Compress, and soon a reduced-color image will pop up. Right-clicking on the image opens an action menu, which allows you to copy the image to the clipboard, or save it as a PNG.',
'The right-click action menu also has the option "Import palette". It loads the image''s colors into the preset list. This is only available if the number of colors in the image is not greater than the maximum output palette size, by default 256 colors.',
'The preset palette list is used to force specific colors to be used in output images. If the color reduction algorithm does not recognise a color you believe is extremely important, you can make the color a preset to be sure it will be used.',
'To edit the preset list, click a row you wish to edit, and type an RGB color into the bigger field. Type the Alpha or transparency value in the smaller field. An alpha of 0 is transparent, FF is opaque. Press Apply to place the color on the list.',
'You can also pick a color directly from an image by pressing the "From image" button. A little note will appear above the button if the color you are picking is already somewhere in the presets.',
'You may have trouble pasting in an image with an alpha channel from the clipboard. Not all programs copy images with valid alpha data. You may have better luck saving as a PNG, and trying to open that.',
'If you have the opposite problem, and an image copied from the clipboard has an unexpected alpha channel, you can use "Scrap source''s alpha channel" from the Command menu.',
'The alpha channel, if present, will be rendered as shades of a single color. You can change this color by selecting "Set Alpha rendering color" from the Command menu.',
'Dithering means approximating intermediate colors by mixing other colors. Particularly photographic images will benefit from good dithering. It does not always improve image quality, so you can turn it off as well.',
'To compare different dithering types, render an image with one type, and import the palette from the result. You can then render new output images with other dithering options without having to wait for the program to recalculate all the colors.',
'',
'',
'The program can work in multiple color spaces. Currently RGB and YCbCr are available, but there''s not much difference between them. Try both and see which you like for each image.',
'Select "Favor flat colors" to make the algorithm try to auto-detect areas of flat color, and use those as temporarily preset colors. This is not useful for photographic images, but drawings, comics and cartoons can benefit greatly.',
'Normally the algorithm attempts to represent all colors of the original image with minimal error, but that option tells the algorithm that using flat colors exactly as they are in the source image is more important.',
'Settings are automatically stored in BUNCOMP.INI in the program''s directory. If you wish to keep a specific set of settings and palette presets, eg. for a game requiring a defined palette, select "Write settings to a file" in the File menu.',
'For feedback, bug reports, and improvement suggestions, visit the mooncore.eu website, or write to me at kirinn@mooncore.eu.',
chr(13) + chr(10) + '.....  -(^_^)-  .....' + chr(13) + chr(10) + 'CC0, 2014-2017 :: Kirinn Bunnylin / MoonCore',
'This program and its source code may be freely used, studied, copied, consumed, modified and distributed, by anyone, for any purpose.'
);

function hexifycolor(inco : RGBquad) : string;
// A macro for turning a color into a six-hex piece of text.
begin
 hexifycolor[0] := chr(6);
 hexifycolor[1] := hextable[inco.r shr 4];
 hexifycolor[2] := hextable[inco.r and $F];
 hexifycolor[3] := hextable[inco.g shr 4];
 hexifycolor[4] := hextable[inco.g and $F];
 hexifycolor[5] := hextable[inco.b shr 4];
 hexifycolor[6] := hextable[inco.b and $F];
end;

function errortxt(ernum : byte) : string;
begin
 case ernum of
   // FPC errors
   2: errortxt := 'File not found';
   3: errortxt := 'Path not found';
   5: errortxt := 'Access denied';
   6: errortxt := 'File handle variable trashed, memory corrupted!!';
   100: errortxt := 'Disk read error';
   101: errortxt := 'Disk write error, disk full?';
   103: errortxt := 'File not open';
   200: errortxt := 'Div by zero!!';
   201: errortxt := 'Range check error';
   203: errortxt := 'Heap overflow - not enough memory, possibly corrupted resource size?';
   204: errortxt := 'Invalid pointer operation';
   215: errortxt := 'Arithmetic overflow';
   216: errortxt := 'General protection fault';
   // BCC errors
   99: errortxt := 'CreateWindow failed!';
   98: errortxt := 'RegisterClass failed, while trying to create a window.';
   84: errortxt := 'Could not fetch WinSystem directory!';
   86: errortxt := 'Could not write to own directory, and SHGetSpecialFolderPathA was not found in shell32.dll!';
   87: errortxt := 'Could not write to own directory, and SHGetSpecialFolderPathA returned an error!';

   else errortxt := 'Unlisted error';
 end;
 errortxt := strdec(ernum) + ': ' + errortxt;
end;

procedure BunExit;
// Procedure called automatically on program exit.
var ert : string;
    i : dword;
begin
 mv_EndProgram := TRUE; compressing := FALSE;

 // Kill the worker thread.
 if compressorthreadID <> 0 then begin
  WaitForThreadTerminate(compressorthreadID, 1000);
  i := KillThread(compressorthreadID);
  CloseHandle(compressorthreadhandle); // trying to avoid handle leaking
 end;

 // Destroy the views.
 for i := 0 to high(viewdata) do begin
  mcg_ForgetImage(@viewdata[i].bmpdata);
  if viewdata[i].winhandu <> 0 then DestroyWindow(viewdata[i].winhandu);
  viewdata[i].winhandu := 0;
  if viewdata[i].BuffyH <> 0 then begin
   SelectObject(viewdata[i].deeku, viewdata[i].OldBuffyH);
   DeleteDC(viewdata[i].deeku);
   DeleteObject(viewdata[i].BuffyH);
   viewdata[i].buffyh := 0;
  end;
 end;
 // Destroy the entertainer.
 if funwinhandle <> 0 then DestroyWindow(funwinhandle);
 // Destroy the magic color list.
 if mv_ListH[1] <> 0 then DestroyWindow(mv_ListH[1]);
 if mv_ListBuffyHandle <> 0 then begin
  SelectObject(mv_ListBuffyDC, mv_OldListBuffyHandle);
  DeleteDC(mv_ListBuffyDC);
  DeleteObject(mv_ListBuffyHandle);
 end;
 // Destroy the help window.
 if HelpWinH <> 0 then DestroyWindow(HelpWinH);
 // Destroy the fun palette picture.
 if mv_FunDIBhandle <> 0 then DeleteObject(mv_FunDIBhandle);
 // Destroy the main window.
 if mv_MainWinH <> 0 then DestroyWindow(mv_MainWinH);

 // Destroy everything else.
 if mv_ContextMenu <> 0 then DestroyMenu(mv_ContextMenu);

 // Free whatever other memory was reserved.
 mcg_ForgetImage(@rendimu);
 mcg_ForgetImage(@tempbmp);

 // Release fonts.
 if mv_FontH[1] <> 0 then deleteObject(mv_FontH[1]);
 if mv_FontH[2] <> 0 then deleteObject(mv_FontH[2]);

 // Print out the error message if exiting unnaturally.
 if (erroraddr <> NIL) or (exitcode <> 0) then begin
  ert := errortxt(exitcode) + chr(0);
  MessageBoxA(0, @ert[1], NIL, MB_OK);
 end;
end;

// Uncomment this when compiling with HeapTrace. Call this whenever to test
// if at that moment the heap has yet been messed up.
{procedure CheckHeap;
var poku : pointer;
begin
 QuickTrace := FALSE;
 getmem(poku, 4); freemem(poku); poku := NIL;
 QuickTrace := TRUE;
end;}

procedure DrawMagicList; forward;

procedure GrabConfig;
begin
 // Grab the configuration from the UI, if it exists.
 if mv_MainWinH <> 0 then with option do begin
  if SendMessageA(mv_ButtonH[5], BM_GETCHECK, 0, 0) = BST_CHECKED
   then flat_favor := 1 else flat_favor := 0;
  if SendMessageA(mv_ButtonH[6], BM_GETCHECK, 0, 0) = BST_CHECKED
   then maxcontrast := 1 else maxcontrast := 0;
  palsize := SendMessageA(mv_SliderH[2], SBM_GETPOS, 0, 0);
  dithering := SendMessageA(mv_ListH[2], CB_GETCURSEL, 0, 0);
  colorspace := SendMessageA(mv_ListH[3], CB_GETCURSEL, 0, 0);
 end;
end;

procedure ClearPE(mini, maxi : word);
// Sets the preset palette entries between [mini..maxi] to unassigned, and
// makes them a uniform plain color.
var i : dword;
begin
 if mini > maxi then begin i := mini; mini := maxi; maxi := i; end;
 if mini > high(pe) then mini := high(pe);
 if maxi > high(pe) then maxi := high(pe);

 for i := maxi downto mini do begin
  dword(pe[i].colo) := dword(neutralcolor);
  pe[i].status := PE_FREE;
 end;
end;

function WriteIni(filunamu : string) : longint;
// Stores the present settings in a file with the given filename.
var conff : text;
    i : dword;
begin
 assign(conff, filunamu);
 filemode := 1; rewrite(conff); // write-only
 writeini := IOresult;
 if writeini <> 0 then exit;
 GrabConfig;

 writeln(conff, '### Bunnylin''s Chromaticity Compressor configuration ###');
 writeln(conff);
 writeln(conff, '// Target palette size [2..65535]');
 writeln(conff, 'P: ' + strdec(option.palsize)); writeln(conff);
 writeln(conff, '// Dithering mode:');
 writeln(conff, '// 0 - None, 1 - Checkerboard, 2 - Quarterdither, 3 - Ordered 4x4,');
 writeln(conff, '// 4 - Error-diffusive Sierra Lite, 5 - Horizontal bars, 6 - Ordered plus');
 writeln(conff, 'D: ' + strdec(option.dithering)); writeln(conff);
 writeln(conff, '// Preserve contrast: 0 - No, 1 - Yes');
 writeln(conff, 'B: ' + strdec(option.maxcontrast)); writeln(conff);
 writeln(conff, '// Colorspace: 0 - RGB, 1 - HCY, 2 - CIEDE2000');
 writeln(conff, 'S: ' + strdec(option.colorspace)); writeln(conff);
 writeln(conff, '// Try to autodetect flat colors: 0 - No, 1 - Yes');
 writeln(conff, 'F: ' + strdec(option.flat_favor)); writeln(conff);
 writeln(conff, '// Render the alpha channel with this color (hexadecimal RGB)');
 writeln(conff, 'A: ' + hexifycolor(acolor)); writeln(conff);
 writeln(conff, '### Color presets ###');
 writeln(conff, '// Use hex format RGBA (eg. C: 8020F0FF), 00 alpha is fully transparent');
 writeln(conff);
 for i := 0 to high(pe) do if pe[i].status <> PE_FREE then
  writeln(conff, 'C: ' + hexifycolor(pe[i].colo) + strhex(pe[i].colo.a));
 close(conff);
 WriteIni := 0;
end;

function ReadIni(filunamu : string) : longint;
// Tries to read the given ASCII text file, and loads configuration options
// based on code strings. See the WriteIni function for the code definitions.
var conff : text;
    i : dword;
    slideinfo : scrollinfo;
    tux : string;
begin
 assign(conff, filunamu);
 filemode := 0; reset(conff); // read-only
 ReadIni := IOresult;
 if readini <> 0 then exit;
 pe_used := 0;
 while not eof(conff) do begin
  readln(conff, tux);
  if (tux <> '') and (tux[1] <> '#') and (tux[1] <> '/') then begin
   tux := upcase(tux);
   case tux[1] of
     'A': dword(acolor) := valhex(copy(tux, 2, length(tux) - 1));
     'B': option.maxcontrast := valx(copy(tux, 2, length(tux) - 1)) and 1;
     'D': option.dithering := valx(copy(tux, 2, length(tux) - 1));
     'F': option.flat_favor := valx(copy(tux, 2, length(tux) - 1)) and 1;
     'S': option.colorspace := valx(copy(tux, 2, length(tux) - 1));

     'P':
     begin
      option.palsize := valx(copy(tux, 2, length(tux) - 1));
      // Normally we cap palsize at 256, but the user can override to up
      // to 65536 colors by writing it into a configuration file.
      if option.palsize < 2 then option.palsize := 2;
      if option.palsize > 256 then setlength(pe, 65536) else setlength(pe, 256);
      pe_used := 0;
      // The interface sliders must be reinitialised.
      slideinfo.cbSize := sizeof(slideinfo);
      slideinfo.fMask := SIF_ALL;
      slideinfo.nMin := 0;
      slideinfo.nMax := high(pe);
      slideinfo.nPage := 8;
      slideinfo.nPos := 0;
      SetScrollInfo(mv_SliderH[1], SB_CTL, @slideinfo, TRUE);
      slideinfo.nMin := 2;
      slideinfo.nPos := option.palsize;
      slideinfo.nPage := length(pe) shr 4;
      slideinfo.nMax := dword(length(pe)) + slideinfo.nPage - 1;
      SetScrollInfo(mv_SliderH[2], SB_CTL, @slideinfo, TRUE);
      // And the preset colors need to be reset.
      ClearPE(0, $FFFF);
     end;

     'C':
     begin
      i := valhex(copy(tux, 2, length(tux) - 1));
      dword(pe[pe_used].colo) := (i shr 8) or (i shl 24);
      pe[pe_used].status := PE_FIXED;
      pe_used := (pe_used + 1) mod dword(length(pe));
     end;
   end;
  end;
 end;
 close(conff);
 if option.dithering in [0..6] = FALSE then option.dithering := 0;
 if option.colorspace in [0..2] = FALSE then option.colorspace := 0;
 pe_used := 0;

 // Update the UI to reflect the selected options.
 DrawMagicList;
 EnableWindow(mv_ButtonH[3], FALSE);
 colorpicking := FALSE;
 SendMessageA(mv_ButtonH[1], bm_setcheck, BST_UNCHECKED, 0);
 ShowWindow(mv_StaticH[7], SW_HIDE);
 SendMessageA(mv_MainWinH, WM_HSCROLL, SB_THUMBTRACK or (option.palsize shl 16), mv_SliderH[2]);
 if option.flat_favor = 0
  then SendMessageA(mv_ButtonH[5], BM_SETCHECK, BST_UNCHECKED, 0)
  else SendMessageA(mv_ButtonH[5], BM_SETCHECK, BST_CHECKED, 0);
 if option.maxcontrast = 0
  then SendMessageA(mv_ButtonH[6], BM_SETCHECK, BST_UNCHECKED, 0)
  else SendMessageA(mv_ButtonH[6], BM_SETCHECK, BST_CHECKED, 0);
 SendMessageA(mv_ListH[2], CB_SETCURSEL, option.dithering, 0);
 SendMessageA(mv_ListH[3], CB_SETCURSEL, option.colorspace, 0);

 readini := 0;
end;

procedure SaveConfig(ownerWindow : hWnd);
var kind, txt, strutsi : string;
    openfilurec : openfilename;
    i : dword;
begin
 kind := 'Buncomp configuration files' + chr(0) + '*.ini' + chr(0) + chr(0);
 txt := chr(0); strutsi := homedir + chr(0);
 fillbyte(openfilurec, sizeof(openfilurec), 0);
 with openfilurec do begin
  lStructSize := 76; // sizeof gives incorrect result?
  hwndOwner := ownerWindow;
  lpstrFilter := @kind[1]; lpstrCustomFilter := NIL;
  nFilterIndex := 1;
  lpstrFile := @txt[1]; nMaxFile := 255;
  lpstrFileTitle := NIL; lpstrInitialDir := @strutsi[1]; lpstrTitle := NIL;
  lpstrDefExt := @kind[31]; // "ini"
  Flags := OFN_NOCHANGEDIR or OFN_OVERWRITEPROMPT or OFN_PATHMUSTEXIST;
 end;

 if GetSaveFileNameA(@openfilurec) then begin
  i := WriteIni(openfilurec.lpstrfile);
  if i <> 0 then begin
   txt := errortxt(i) + chr(0);
   MessageBoxA(ownerWindow, @txt[1], NIL, MB_OK);
  end;
 end;
end;

procedure LoadConfig(ownerWindow : hWnd);
var kind, txt, strutsi : string;
    openfilurec : openfilename;
    i : dword;
begin
 kind := 'Buncomp configuration files' + chr(0) + '*.ini' + chr(0) + chr(0);
 txt := chr(0); strutsi := homedir + chr(0);
 fillbyte(openfilurec, sizeof(openfilurec), 0);
 with openfilurec do begin
  lStructSize := 76; // sizeof gives incorrect result?
  hwndOwner := ownerWindow;
  lpstrFilter := @kind[1]; lpstrCustomFilter := NIL;
  nFilterIndex := 1;
  lpstrFile := @txt[1]; nMaxFile := 255;
  lpstrFileTitle := NIL; lpstrInitialDir := @strutsi[1]; lpstrTitle := NIL;
  Flags := OFN_FILEMUSTEXIST or OFN_NOCHANGEDIR;
 end;
 if GetOpenFileNameA(@openfilurec) then begin
  i := ReadIni(openfilurec.lpstrfile);
  if i <> 0 then begin
   txt := errortxt(i) + chr(0);
   MessageBoxA(ownerWindow, @txt[1], NIL, MB_OK);
  end;
 end;
end;

// ------------------------------------------------------------------

procedure outpal;
// Debugging function, prints the palette state into an attached console.
var lix : word;
begin
 writeln('=== Palette state ===');
 for lix := 0 to option.palsize - 1 do begin
  if lix and 7 = 0 then write(lix:5,': ');
  case pe[lix].status of
    PE_FREE: write('-------- ');
    PE_ALLOCATED: write(lowercase(hexifycolor(pe[lix].colo) + strhex(pe[lix].colo.a)) + ' ');
    PE_FIXED: write(hexifycolor(pe[lix].colo) + strhex(pe[lix].colo.a) + ' ');
    PE_AUTOFLAT: write(hexifycolor(pe[lix].colo) + strhex(pe[lix].colo.a) + '!');
  end;
  if (lix and 7 = 7) or (lix + 1 = option.palsize) then writeln;
 end;
end;

procedure ValidateHexaco;
// The edit box should only accept hexadecimals; flush out everything else.
// If the boxes are not empty, enable the apply button, otherwise disable.
var mur : byte;
    kind : string[7];
begin
 byte(kind[0]) := SendMessageA(mv_EditH[1], WM_GETTEXT, 7, ptrint(@kind[1]));
 if kind = '' then begin EnableWindow(mv_ButtonH[2], FALSE); exit; end;
 mur := length(kind);
 while mur <> 0 do begin
  if kind[mur] in ['0'..'9','A'..'F'] = FALSE then begin
   dec(mur);
   kind := copy(kind, 1, mur) + copy(kind, mur + 2, 5 - mur) + chr(0);
   SendMessageA(mv_EditH[1], WM_SETTEXT, 0, ptrint(@kind[1]));
   SendMessageA(mv_EditH[1], EM_SETSEL, mur, mur);
   EnableWindow(mv_ButtonH[2], FALSE);
   exit;
  end;
  dec(mur);
 end;

 if SendMessageA(mv_EditH[2], WM_GETTEXT, 7, ptrint(@kind[1])) <> 0 then
  EnableWindow(mv_ButtonH[2], TRUE);
end;

procedure ValidateAlfaco;
// The edit box should only accept hexadecimals; flush out everything else.
// If the boxes are not empty, enable the apply button, otherwise disable.
var mur : byte;
    kind : string[7];
begin
 byte(kind[0]) := SendMessageA(mv_EditH[2], WM_GETTEXT, 7, ptrint(@kind[1]));
 if kind = '' then begin EnableWindow(mv_ButtonH[2], FALSE); exit; end;
 mur := length(kind);
 while mur > 0 do begin
  if kind[mur] in ['0'..'9','A'..'F'] = FALSE then begin
   dec(mur);
   kind := copy(kind, 1, mur) + copy(kind, mur + 2, 5 - mur) + chr(0);
   SendMessageA(mv_EditH[2], WM_SETTEXT, 0, ptrint(@kind[1]));
   SendMessageA(mv_EditH[2], EM_SETSEL, mur, mur);
   EnableWindow(mv_ButtonH[2], FALSE);
   exit;
  end;
  dec(mur);
 end;

 if SendMessageA(mv_EditH[1], WM_GETTEXT, 7, ptrint(@kind[1])) <> 0 then
  EnableWindow(mv_ButtonH[2], TRUE);
end;

function fetchpixel(winpo : byte; cx, cy : word) : RGBquad;
// Grabs the RGB or RGBA color from coordinates cx,cy in view image winpo.
var ofsu : pointer;
begin
 if (winpo > high(viewdata)) or (viewdata[winpo].bmpdata.image = NIL) then begin
  dword(fetchpixel) := $FFFF0000; // red, full alpha, I hope
  exit;
 end;
 ofsu := viewdata[winpo].bmpdata.image;
 inc(ofsu, (cy * viewdata[winpo].bmpdata.sizex + cx) * viewdata[winpo].alpha);
 dword(fetchpixel) := dword(ofsu^);
 if viewdata[winpo].alpha <> 4 then dword(fetchpixel) := dword(fetchpixel) or $FF000000;
end;

procedure DrawMagicList;
// Fills the custom listbox bitmap with the color and text reference of the
// currently visible palette entries.
var mlp : byte;
    pali : word;
    areasize, osfet, blob : dword;
    blah : string[20];
begin
 areasize := magicx * magicy div 8;
 osfet := 0;
 pali := GetScrollPos(mv_SliderH[1], SB_CTL);
 for mlp := 0 to 7 do begin
  blob := areasize;
  while blob <> 0 do begin
   byte((mv_ListBuffy + osfet)^) := pe[pali].colo.b; inc(osfet);
   byte((mv_ListBuffy + osfet)^) := pe[pali].colo.g; inc(osfet);
   byte((mv_ListBuffy + osfet)^) := pe[pali].colo.r; inc(osfet);
   dec(blob);
  end;
  SetBkColor(mv_ListBuffyDC, SwapEndian(dword(pe[pali].colo)) shr 8);
  blob := $FFFFFF;
  if (pe[pali].colo.b shr 1)
   + (pe[pali].colo.g shl 1)
   + pe[pali].colo.r + (pe[pali].colo.r shr 2)
   >= 400
   then blob := 0;
  SetTextColor(mv_ListBuffyDC, blob);
  SetTextAlign(mv_ListBuffyDC, TA_LEFT);
  blah := strdec(pali) + ':';
  if pali = pe_used then begin
   SelectObject(mv_ListBuffyDC, mv_FontH[1]);
   TextOut(mv_ListBuffyDC, 3, mlp * (magicy shr 3) + 2, @blah[1], length(blah));
   SelectObject(mv_ListBuffyDC, mv_FontH[2]);
  end
  else begin
   SelectObject(mv_ListBuffyDC, mv_FontH[2]);
   TextOut(mv_ListBuffyDC, 4, mlp * (magicy shr 3) + 3, @blah[1], length(blah));
  end;

  if pe[pali].status = PE_FREE then
   blah := 'Not set'
  else
   blah := hexifycolor(pe[pali].colo);
  TextOut(mv_ListBuffyDC, (magicx shr 2) + 8, mlp * (magicy shr 3) + 3, @blah[1], length(blah));
  if pe[pali].status <> PE_FREE then begin
   SetTextAlign(mv_ListBuffyDC, TA_RIGHT);
   blah := hextable[pe[pali].colo.a shr 4] + hextable[pe[pali].colo.a and $F];
   TextOut(mv_ListBuffyDC, magicx - 4, mlp * (magicy shr 3) + 3, @blah[1], length(blah));
  end;

  inc(pali);
 end;
 InvalidateRect(mv_ListH[1], NIL, FALSE);
end;

procedure DrawFunBuffy;
// Renders the fun palette block that the user sees during CompressColors.
var funpoku : pointer;
    avar, q : dword;
    rootsizex, rootsizey, x, y, pvar : word;
    aval : byte;
begin
 if (mv_FunBuffy = NIL) or (funsizex = 0) or (funsizey = 0) or (option.palsize = 0)
 then exit;

 // Calculate good table display dimensions.
 rootsizex := 1;
 while rootsizex * rootsizex < option.palsize do inc(rootsizex);
 rootsizey := rootsizex;
 while (rootsizex - 1) * rootsizey >= option.palsize do dec(rootsizex);

 // Draw it.
 funpoku := mv_FunBuffy;
 for y := 0 to funsizey - 1 do begin
  pvar := (y * rootsizey div funsizey) * rootsizex;
  for x := 0 to funsizex - 1 do begin
   q := pvar + (x * rootsizex) div funsizex;
   aval := pe[q].colo.a;
   // For pretend alpha, a black and white xor pattern!
   avar := ((x xor y) and $3E) shl 1 + $40;
   avar := mcg_GammaTab[avar] * (aval xor $FF);
   byte(funpoku^) := mcg_RevGammaTab[(mcg_GammaTab[pe[q].colo.b] * aval + avar) div 255];
   inc(funpoku);
   byte(funpoku^) := mcg_RevGammaTab[(mcg_GammaTab[pe[q].colo.g] * aval + avar) div 255];
   inc(funpoku);
   byte(funpoku^) := mcg_RevGammaTab[(mcg_GammaTab[pe[q].colo.r] * aval + avar) div 255];
   inc(funpoku, 2);
  end;
 end;

 InvalidateRect(funpal, NIL, FALSE);
end;

{$include bcc_diff.pas}

procedure PackView(winpo : byte; bytealign : byte; whither : pbitmaptype);
// Takes a view and checks if the number of colors is 256 or less. In that
// case, creates an indexed-color image, otherwise returns the RGB or RGBA
// image straight from the view. The returned image has its scanlines padded
// to BYTE or DWORD -alignment, defined by the bytealign variable. The
// procedure returns the new image as a non-standard bitmap type, which the
// caller must free when finished. (Don't try to feed it to my other
// functions that accept bitmaptypes, they only accept byte-aligned images;
// this one also puts the byte width, not pixel width, in .sizex)
var srcofs, destofs : dword;
    packedpixel : longint;
    tempcolor : RGBquad;
    xvar, yvar, dibwidth : word;
    bitptr : byte;
begin
 if (winpo > high(viewdata)) or (viewdata[winpo].bmpdata.image = NIL) then exit;
 mcg_ForgetImage(whither);
 if bytealign = 0 then inc(bytealign);

 // 256 or less colors, index 'em!
 if length(viewdata[winpo].bmpdata.palette) <= 256 then
 with viewdata[winpo] do begin
  // Store the palette.
  setlength(whither^.palette, length(bmpdata.palette));
  move(bmpdata.palette[0], whither^.palette[0], length(bmpdata.palette) * 4);
  // Decide which bitdepth to pack into.
  case length(bmpdata.palette) of
    0..2: whither^.bitdepth := 1;
    3..4: if bytealign = 1 then whither^.bitdepth := 2
          // v4 DIBs are DWORD -aligned, and don't support 2 bpp.
          else whither^.bitdepth := 4;
    5..16: whither^.bitdepth := 4;
    17..256: whither^.bitdepth := 8;
  end;
  // Calculate various descriptive numbers.
  dec(bytealign);
  whither^.sizex := (((bmpdata.sizex * whither^.bitdepth + 7) shr 3) + bytealign) and ($FFFFFFFF - bytealign);
  whither^.sizey := bmpdata.sizey;
  getmem(whither^.image, whither^.sizex * bmpdata.sizey);
  fillbyte(whither^.image^, whither^.sizex * bmpdata.sizey, 0);
  whither^.memformat := 4 + (alpha - 3);
  // Match each pixel to the palette, store the indexes as the new image
  // svar is the source offset, zvar is the 29.3 fixed point target offset.
  destofs := 0; srcofs := 0; bitptr := 8;
  if alpha = 4 then begin
   // If the source image is 32-bit RGBA, do this.
   for yvar := bmpdata.sizey - 1 downto 0 do begin
    for xvar := bmpdata.sizex - 1 downto 0 do begin
     if bitptr = 0 then begin
      bitptr := 8;
      inc(destofs);
     end;
     dec(bitptr, whither^.bitdepth);

     packedpixel := mcg_MatchColorInPal(RGBAarray(bmpdata.image^)[srcofs], whither);
     byte((whither^.image + destofs)^) := byte((whither^.image + destofs)^) or byte(packedpixel shl bitptr);
     inc(srcofs);
    end;
    // All rows are padded to a full byte width.
    if bitptr < 8 then begin
     bitptr := 8;
     inc(destofs);
    end;
    // Byte align to the required width, byte for PNGs, dword for BMPs.
    destofs := (destofs + bytealign) and ($FFFFFFFF - bytealign);
   end;
  end else begin

   // If the source image is 24-bit RGB images, do this.
   for yvar := bmpdata.sizey - 1 downto 0 do begin
    for xvar := bmpdata.sizex - 1 downto 0 do begin
     if bitptr = 0 then begin
      bitptr := 8;
      inc(destofs);
     end;
     dec(bitptr, whither^.bitdepth);

     move(RGBarray(bmpdata.image^)[srcofs], tempcolor.b, 3);
     tempcolor.a := $FF;
     packedpixel := mcg_MatchColorInPal(tempcolor, whither);
     byte((whither^.image + destofs)^) := byte((whither^.image + destofs)^) or byte(packedpixel shl bitptr);
     inc(srcofs);
    end;
    // All rows are padded to a full byte width.
    if bitptr < 8 then begin
     bitptr := 8;
     inc(destofs);
    end;
    // Byte align to the required width, byte for PNGs, dword for BMPs.
    destofs := (destofs + bytealign) and ($FFFFFFFF - bytealign);
   end;
  end;

 end

 // More than 256 colors.
 else with viewdata[winpo] do begin
  dec(bytealign);
  dibwidth := ((bmpdata.sizex * alpha) + bytealign) and ($FFFFFFFF - bytealign);
  getmem(whither^.image, dibwidth * bmpdata.sizey);
  whither^.sizex := dibwidth;
  whither^.sizey := bmpdata.sizey;
  whither^.memformat := (alpha - 3); // RGB = 0, RGBA = 1
  whither^.bitdepth := alpha * 8;
  for yvar := 0 to bmpdata.sizey - 1 do
   move((bmpdata.image + yvar * bmpdata.sizex * alpha)^, (whither^.image + yvar * dibwidth)^, bmpdata.sizex * alpha);
 end;

end;

procedure SaveViewAsPNG(winpo : byte);
// Pops up a Save As dialog, then saves the image from
// viewdata[winpo].bmpdata into a PNG file using the given name.
var newimu : bitmaptype;
    openfilurec : openfilename;
    kind, txt : string;
    filu : file;
    i, j : dword;
    pingustream : pointer;
begin
 if (winpo > high(viewdata)) or (viewdata[winpo].bmpdata.image = NIL) then exit;
 kind := 'PNG image file' + chr(0) + '*.png' + chr(0) + chr(0);
 txt := chr(0);
 fillbyte(openfilurec, sizeof(openfilurec), 0);
 with openfilurec do begin
  lStructSize := 76; // sizeof gives incorrect result?
  hwndOwner := viewdata[winpo].winhandu;
  lpstrFilter := @kind[1]; lpstrCustomFilter := NIL;
  nFilterIndex := 1;
  lpstrFile := @txt[1]; nMaxFile := 255;
  lpstrFileTitle := NIL; lpstrInitialDir := NIL; lpstrTitle := NIL;
  Flags := OFN_OVERWRITEPROMPT or OFN_PATHMUSTEXIST;
 end;
 if GetSaveFileNameA(@openfilurec) = FALSE then exit;

 // We have the filename, so prepare the file.
 txt := openfilurec.lpstrfile;
 if upcase(copy(txt, length(txt) - 3, 4)) <> '.PNG' then txt := txt + '.png';
 assign(filu, txt);
 filemode := 1; rewrite(filu, 1); // write-only
 i := IOresult;
 if i <> 0 then begin
  txt := errortxt(i) + chr(0);
  MessageBoxA(viewdata[winpo].winhandu, @txt[1], NIL, MB_OK); exit;
 end;

 // Squash the image into the smallest uncompressed space possible.
 fillbyte(newimu, sizeof(newimu), 0);
 PackView(winpo, 1, @newimu);
 newimu.sizex := viewdata[winpo].bmpdata.sizex; // use pixel, not byte width

 // Render the image into a compressed PNG.
 pingustream := NIL;
 i := mcg_MemorytoPNG(@newimu, @pingustream, @j);
 if i <> 0 then begin
  mcg_ForgetImage(@newimu);
  txt := mcg_errortxt + chr(0);
  MessageBoxA(viewdata[winpo].winhandu, @txt[1], NIL, MB_OK); exit;
 end;

 // Write the PNG datastream into the file.
 blockwrite(filu, pingustream^, j);
 i := IOresult;
 if i <> 0 then begin
  txt := errortxt(i) + chr(0);
  MessageBoxA(viewdata[winpo].winhandu, @txt[1], NIL, MB_OK);
 end;

 // Clean up.
 mcg_ForgetImage(@newimu); close(filu);
 freemem(pingustream); pingustream := NIL;
end;

procedure CopyView(winpo : byte);
// Tries to place the image in viewdata[winpo] on the clipboard.
var workhand : hglobal;
    tonne : pointer;
    txt : string;
    hedari : bitmapv4header;
    newimu : bitmaptype;
    ofsu, ofx : dword;
begin
 if (winpo > high(viewdata)) or (viewdata[winpo].bmpdata.image = NIL) then exit;
 fillbyte(newimu, sizeof(newimu), 0);
 PackView(winpo, 4, @newimu);
 fillbyte(hedari, sizeof(hedari), 0);
 with hedari do begin // not all programs know what v4DIBs are
  bv4Size := sizeof(bitmapinfoheader); // so use lowest common denominator
  bv4Width := viewdata[winpo].bmpdata.sizex;
  bv4Height := viewdata[winpo].bmpdata.sizey;
  bv4BitCount := newimu.bitdepth;
  bv4v4Compression := BI_RGB; bv4SizeImage := newimu.sizex * newimu.sizey;
  bv4XPelsPerMeter := $AF0; bv4YPelsPerMeter := $AF0; bv4ClrImportant := 0;
  if newimu.memformat < 2 then bv4ClrUsed := 0 else bv4ClrUsed := length(newimu.palette);
  bv4RedMask := $FF0000; bv4GreenMask := $FF00;
  bv4BlueMask := $FF; bv4AlphaMask := $FF000000;
  bv4Planes := 1; bv4CSType := 0;
 end;

 if OpenClipboard(viewdata[winpo].winhandu) = FALSE then begin
  txt := 'Could not open clipboard.' + chr(0);
  MessageBoxA(viewdata[winpo].winhandu, @txt[1], NIL, MB_OK);
 end else begin
  EmptyClipboard;
  // Allocate a system-wide memory chunk.
  workhand := GlobalAlloc(GMEM_MOVEABLE, hedari.bv4Size + hedari.bv4ClrUsed * 4 + newimu.sizex * newimu.sizey);
  if workhand = 0 then begin
   txt := 'Could not allocate global memory.' + chr(0);
   MessageBoxA(viewdata[winpo].winhandu, @txt[1], NIL, MB_OK);
  end else begin
   // Stuff the memory chunk with goodies!
   tonne := GlobalLock(workhand);
   // First up: the bitmapinfoheader.
   move((@hedari)^, tonne^, hedari.bv4Size);
   inc(tonne, hedari.bv4Size);
   // Next up: the palette, if applicable.
   if hedari.bv4ClrUsed <> 0 then begin
    move(newimu.palette[0], tonne^, hedari.bv4ClrUsed * 4);
    inc(tonne, hedari.bv4ClrUsed * 4);
   end;

   // Last up: the image itself! Must be bottom-up, top-down doesn't seem to
   // work on the 9x clipboard.
   if newimu.memformat = 1 then begin
    // 32-bit ABGR, must be converted to Windows' preferred BGRA.
    ofsu := (newimu.sizex shr 2) * dword(hedari.bv4Height - 1);
    while ofsu <> 0 do begin
     for ofx := 0 to (newimu.sizex shr 2) - 1 do begin
      dword(tonne^) := dword((newimu.image + ofsu  *4)^);
      //dword(tonne^) := (dword(tonne^) shr 8) or (dword(tonne^) shl 24);
      inc(tonne, 4); inc(ofsu);
     end;
     dec(ofsu, (newimu.sizex shr 2) * 2);
    end;
   end
   else begin
    // Any other than 32-bit RGBA.
    ofsu := hedari.bv4SizeImage;
    while ofsu > 0 do begin
     dec(ofsu, newimu.sizex);
     move((newimu.image + ofsu)^, tonne^, newimu.sizex);
     inc(tonne, newimu.sizex);
    end;
   end;

   tonne := NIL;
   GlobalUnlock(workhand);
   if SetClipBoardData(CF_DIB, workhand) = 0 then begin
    txt := 'Could not place data on the clipboard.' + chr(0);
    MessageBoxA(viewdata[winpo].winhandu, @txt[1], NIL, MB_OK);
    GlobalFree(workhand);
   end;
  end;
  // Clean up.
  CloseClipboard;
 end;
 mcg_ForgetImage(@newimu);
end;

procedure ImportPalette(winpo : byte);
// Grabs the palette from viewdata[winpo] and uses it to reset the preset
// palette entries.
var txt : string;
    mur : dword;
begin
 // Safety checks.
 if (winpo > high(viewdata)) or (viewdata[winpo].bmpdata.image = NIL) then exit;
 if high(viewdata[winpo].bmpdata.palette) > high(pe) then begin
  txt := 'Cannot import: this image has more colors than the maximum palette size (' + strdec(length(pe)) + ').' + chr(0);
  MessageBoxA(viewdata[winpo].winhandu, @txt[1], NIL, MB_OK); exit;
 end;
 // Clear the previous palette.
 if high(viewdata[winpo].bmpdata.palette) < high(pe) then
  ClearPE(length(viewdata[winpo].bmpdata.palette), high(pe));
 // Copy the view's histogram to a new active palette.
 for mur := high(viewdata[winpo].bmpdata.palette) downto 0 do begin
  pe[mur].colo := viewdata[winpo].bmpdata.palette[mur];
  pe[mur].status := PE_FIXED;
 end;
 // Update the UI.
 DrawMagicList;
 EnableWindow(mv_ButtonH[3], FALSE);
 colorpicking := FALSE;
 SendMessageA(mv_ButtonH[1], bm_setcheck, BST_UNCHECKED, 0);
 ShowWindow(mv_StaticH[7], SW_HIDE);
end;

procedure ResizeView(viewnum : dword; newx, newy : word);
begin
 if (viewnum >= length(viewdata))
 or (viewdata[viewnum].bmpdata.image = NIL) then exit;

 with viewdata[viewnum] do begin
  winsizex := newx;
  winsizey := newy;
  // Adjust the view offset.
  if winsizex > bmpdata.sizex * zoom then
   viewofsx := -((winsizex - bmpdata.sizex * zoom) shr 1)
  else if viewofsx > bmpdata.sizex * zoom - winsizex then
   viewofsx := bmpdata.sizex * zoom - winsizex
  else if viewofsx < 0 then
   viewofsx := 0;
  if winsizey > bmpdata.sizey * zoom then
   viewofsy := -((winsizey - bmpdata.sizey * zoom) shr 1)
  else if viewofsy > bmpdata.sizey * zoom - winsizey then
   viewofsy := bmpdata.sizey * zoom - winsizey
  else if viewofsy < 0 then
   viewofsy := 0;
  invalidaterect(winhandu, NIL, TRUE);
 end;
end;

procedure ZoomIn(winh : handle; viewnum : byte);
begin
 with viewdata[viewnum] do if zoom < 8 then begin
  // Make sure the image does not scroll while zooming.
  viewofsx := (word(winsizex shr 1) + viewofsx) * (zoom + 1) div zoom - (winsizex shr 1);
  viewofsy := (word(winsizey shr 1) + viewofsy) * (zoom + 1) div zoom - (winsizey shr 1);
  inc(zoom);
  // Enforce bounds.
  if winsizex > bmpdata.sizex * zoom then viewofsx := -((winsizex - bmpdata.sizex * zoom) shr 1)
  else if viewofsx < 0 then viewofsx := 0
  else if viewofsx + winsizex >= longint(bmpdata.sizex * zoom) then viewofsx := bmpdata.sizex * zoom - winsizex;
  if winsizey > bmpdata.sizey * zoom then viewofsy := -((winsizey - bmpdata.sizey * zoom) shr 1)
  else if viewofsy < 0 then viewofsy := 0
  else if viewofsy + winsizey >= longint(bmpdata.sizey * zoom) then viewofsy := bmpdata.sizey * zoom - winsizey;
  // Redraw the image.
  invalidaterect(winh, NIL, FALSE);
 end;
end;

procedure ZoomOut(winh : handle; viewnum : byte);
begin
 with viewdata[viewnum] do if zoom > 1 then begin
  // Make sure the image does not scroll while zooming.
  dec(zoom);
  viewofsx := (word(winsizex shr 1) + viewofsx) * zoom div (zoom + 1) - (winsizex shr 1);
  viewofsy := (word(winsizey shr 1) + viewofsy) * zoom div (zoom + 1) - (winsizey shr 1);
  // Enforce bounds.
  if winsizex > bmpdata.sizex * zoom then viewofsx := -((winsizex - bmpdata.sizex * zoom) shr 1) else
  if viewofsx < 0 then viewofsx := 0 else
  if dword(viewofsx + winsizex) >= bmpdata.sizex * zoom then viewofsx := bmpdata.sizex * zoom - winsizex;
  if winsizey > bmpdata.sizey * zoom then viewofsy := -((winsizey - bmpdata.sizey * zoom) shr 1) else
  if viewofsy < 0 then viewofsy := 0 else
  if dword(viewofsy + winsizey) >= bmpdata.sizey * zoom then viewofsy := bmpdata.sizey * zoom - winsizey;
  // Redraw the image.
  invalidaterect(winh, NIL, TRUE);
 end;
end;

// --------------------------------------------------------------------------

function ViewProc (window : hwnd; amex : uint; wepu : wparam; lapu : lparam) : lresult; stdcall;
// Handles win32 messages for the source and result view windows.
var mv_PS : paintstruct;
    rrs, rrd : rect;
    pico : RGBquad;
    kind : string[32];
    winpo : byte;
begin
 ViewProc := 0;
 // Specify the view window this message is intended for
 winpo := GetWindowLong(window, GWL_USERDATA);

 case amex of
   // the Compress-button
   wm_Create: if winpo = 0 then EnableWindow(mv_ButtonH[4], TRUE);

   // Copy stuff to screen from our own buffer
   wm_Paint:
   begin
    mv_DC := beginPaint (window, @mv_PS);
    with viewdata[winpo] do begin
     if bmpdata.sizex * zoom <= winsizex then begin
      rrd.left := (winsizex - bmpdata.sizex * zoom) shr 1;
      rrd.right := bmpdata.sizex * zoom;
      rrs.left := 0;
      rrs.right := bmpdata.sizex;
     end else begin
      rrd.left := -viewofsx mod zoom;
      rrd.right := winsizex - (winsizex mod zoom) + zoom;
      rrs.left := viewofsx div zoom;
      rrs.right := (winsizex div zoom) + 1;
     end;
     if bmpdata.sizey * zoom <= winsizey then begin
      rrd.top := (winsizey - bmpdata.sizey * zoom) shr 1;
      rrd.bottom := bmpdata.sizey * zoom;
      rrs.top := 0;
      rrs.bottom := bmpdata.sizey;
     end else begin
      rrd.top := -viewofsy mod zoom;
      rrd.bottom := winsizey - (winsizey mod zoom) + zoom;
      rrs.top := viewofsy div zoom;
      rrs.bottom := (winsizey div zoom) + 1;
     end;
    end;
    StretchBlt (mv_DC,
      rrd.left, rrd.top, rrd.right, rrd.bottom,
      viewdata[winpo].deeku,
      rrs.left, rrs.top, rrs.right, rrs.bottom,
      SRCCOPY);
    endPaint (window, mv_PS);
   end;

   // Resizing
   wm_Size: ResizeView(winpo, word(lapu), word(lapu shr 16));

   // Losing or gaining window focus
   wm_Activate:
   begin
    if wepu and $FFFF = WA_INACTIVE then begin
     if mousescrolling then begin
      ReleaseCapture;
      mousescrolling := FALSE;
     end;
    end else
     lastactiveview := winpo;
    // do the default action too, why not
    ViewProc := DefWindowProc(Window, AMex, wepu, lapu);
   end;

   // Mouse stuff
   wm_MouseMove:
   if mousescrolling = FALSE then begin
    // If color picking is toggled, refresh the color selection
    if colorpicking then with viewdata[winpo] do begin
     rrs.left := (viewofsx + integer(lapu and $FFFF)) div zoom;
     rrs.top := (viewofsy + integer(lapu shr 16)) div zoom;
     if (rrs.left >= 0) and (rrs.left < bmpdata.sizex)
     and (rrs.top >= 0) and (rrs.top < bmpdata.sizey)
     then begin
      pico := fetchpixel(winpo, rrs.left, rrs.top);
      kind := hexifycolor(pico) + chr(0);
      SendMessageA(mv_EditH[1], WM_SETTEXT, 0, ptrint(@kind[1]));
      kind := hextable[pico.a shr 4] + hextable[pico.a and $F] + chr(0);
      SendMessageA(mv_EditH[2], WM_SETTEXT, 0, ptrint(@kind[1]));
      EnableWindow(mv_ButtonH[3], TRUE);
      InvalidateRect(mv_ColorBlockH, NIL, TRUE);
      // check for palette hits
      wepu := 0;
      for lapu := 0 to high(pe) do
       if dword(pe[lapu].colo) = dword(pico) then inc(wepu);
      if wepu = 0 then ShowWindow(mv_StaticH[7], SW_HIDE)
       else ShowWindow(mv_StaticH[7], SW_SHOW);
     end;
    end
    // If left button pressed, start mousescrolling
    else if wepu and MK_LBUTTON <> 0 then begin
     SetCapture(window);
     mousescrolling := TRUE;
     mousescrollx := lapu and $FFFF;
     mousescrolly := lapu shr 16;
    end;
   end

   // Mouse scrolling
   else with viewdata[winpo] do begin
    rrd.left := mousescrollx - integer(lapu and $FFFF);
    rrd.top := mousescrolly - integer(lapu shr 16);
    mousescrollx := integer(lapu and $FFFF);
    mousescrolly := integer(lapu shr 16);

    // images smaller than winsize can't be scrolled
    if bmpdata.sizex * zoom <= winsizex then rrd.left := 0;
    if bmpdata.sizey * zoom <= winsizey then rrd.top := 0;
    if (rrd.left or rrd.top) <> 0 then begin
     // can't scroll view beyond edges
     if viewofsx + rrd.left <= 0 then
      rrd.left := -viewofsx
     else if dword(viewofsx + rrd.left + winsizex) >= bmpdata.sizex * zoom then
      rrd.left := bmpdata.sizex * zoom - winsizex - viewofsx;
     if viewofsy + rrd.top <= 0 then
      rrd.top := -viewofsy
     else if dword(viewofsy + rrd.top + winsizey) >= bmpdata.sizey * zoom then
      rrd.top := bmpdata.sizey * zoom - winsizey - viewofsy;

     if (rrd.left or rrd.top) <> 0 then begin
      inc(viewofsx, rrd.left);
      inc(viewofsy, rrd.top);
      invalidaterect(window, NIL, FALSE);
     end;
    end;
   end;

   wm_LButtonUp:
   if colorpicking then begin
    colorpicking := FALSE;
    SendMessageA(mv_ButtonH[1], BM_SETCHECK, BST_UNCHECKED, 0);
    ShowWindow(mv_StaticH[7], SW_HIDE);
   end else
   if mousescrolling then begin
    ReleaseCapture;
    mousescrolling := FALSE;
   end;

   wm_MouseWheel:
   if integer(wepu shr 16) < 0 then ZoomOut(window, winpo)
   else ZoomIn(window, winpo);

   // Right-click menu popup
   wm_ContextMenu:
   begin
    if mousescrolling then begin
     ReleaseCapture; mousescrolling := FALSE;
    end;
    kind := 'Import palette ' + chr(8) + '(CTRL+M)' + chr(0);
    // If the view image has more distinct colors than the maximum palette
    // palette size, disable palette importing.
    wepu := MF_BYPOSITION;
    if length(viewdata[winpo].bmpdata.palette) > length(pe) then
     wepu := wepu or MF_GRAYED;
    ModifyMenu(mv_ContextMenu, 2, wepu, 96, @kind[1]);
    TrackPopupMenu(mv_ContextMenu, TPM_LEFTALIGN, lapu and $FFFF, lapu shr 16, 0, window, NIL);
   end;

   wm_Command:
   case wepu of
     91: SaveViewAsPNG(winpo);
     94: CopyView(winpo);
     96: ImportPalette(winpo);
   end;

   // Keypresses
   wm_Char:
   begin
    case wepu of
      27:
      if colorpicking then begin
       colorpicking := FALSE;
       SendMessageA(mv_ButtonH[1], bm_setcheck, BST_UNCHECKED, 0);
       ShowWindow(mv_StaticH[7], SW_HIDE);
      end;
      ord('+'): ZoomIn(window, winpo);
      ord('-'): ZoomOut(window, winpo);
    end;
   end;

   // Closing down...
   // Non-source views can be closed at any time; a source view may only be
   // closed if color compression is not ongoing.
   wm_Close:
   if (winpo <> 0) or (compressorthreadID = 0) then
    DestroyWindow(window);

   wm_Destroy:
   begin
    if lastactiveview = winpo then lastactiveview := $FF;
    // Clean the variables.
    if viewdata[winpo].winhandu <> 0 then viewdata[winpo].winhandu := 0;
    if viewdata[winpo].BuffyH <> 0 then begin
     SelectObject(viewdata[winpo].deeku, viewdata[winpo].OldBuffyH);
     DeleteDC(viewdata[winpo].deeku);
     DeleteObject(viewdata[winpo].BuffyH);
     viewdata[winpo].buffyh := 0;
    end;
    mcg_ForgetImage(@viewdata[winpo].bmpdata);
    // If the source view is closed, disable the Compress-button.
    if winpo = 0 then EnableWindow(mv_ButtonH[4], FALSE);
    SetForegroundWindow(mv_MainWinH);
    colorpicking := FALSE;
    SendMessageA(mv_ButtonH[1], bm_setcheck, BST_UNCHECKED, 0);
    ShowWindow(mv_StaticH[7], SW_HIDE);
    // If all views are closed, disable the From Image button.
    for winpo := 0 to high(viewdata) do
     if viewdata[winpo].buffyh <> 0 then exit;
    EnableWindow(mv_ButtonH[1], FALSE);
   end;

   // Default handler for every other message.
   else ViewProc := DefWindowProc(Window, AMex, wepu, lapu);
 end;
end;

{$include bcc_eval.pas}

procedure RedrawView(sr : byte);
// Renders the raw bitmap into a buffer that the system can display.
var srcp, destp : pointer;
    acolorg : RGBA64;
    srccolor : RGBquad;
    pixelcount : dword;
    a_inverse : byte;
begin
 if (sr > high(viewdata)) or (viewdata[sr].bmpdata.image = NIL) then exit;

 acolorg := mcg_GammaInput(acolor);

 with viewdata[sr] do begin
  // The DIBitmap in .buffy^ that is designated as our output buffer must
  // have rows that have a length in bytes divisible by 4. Happily, it is
  // a 32-bit RGBx DIB so this is not a problem.

  srcp := bmpdata.image;
  destp := buffy;
  pixelcount := bmpdata.sizex * bmpdata.sizey;
  // 24-bit RGB rendering.
  if alpha = 3 then begin
   while pixelcount <> 0 do begin
    // Always full alpha.
    dword(destp^) := dword(srcp^) or $FF000000;
    inc(srcp, 3);
    inc(destp, 4);
    dec(pixelcount);
   end;
  end
  // 32-bit RGBA rendering, alpha rendering using RGBquad "acolor".
  // Alpha mixing is most correctly done in linear RGB space.
  else begin
   while pixelcount <> 0 do begin
    dword(srccolor) := dword(srcp^);
    inc(srcp, 4);
    a_inverse := srccolor.a xor $FF;

    byte(destp^) := mcg_RevGammaTab[(mcg_GammaTab[srccolor.b] * srccolor.a + acolorg.b * a_inverse) div 255];
    inc(destp);
    byte(destp^) := mcg_RevGammaTab[(mcg_GammaTab[srccolor.g] * srccolor.a + acolorg.g * a_inverse) div 255];
    inc(destp);
    byte(destp^) := mcg_RevGammaTab[(mcg_GammaTab[srccolor.r] * srccolor.a + acolorg.r * a_inverse) div 255];
    inc(destp);
    byte(destp^) := srccolor.a;
    inc(destp);

    dec(pixelcount);
   end;
  end;

  invalidaterect(winhandu, NIL, FALSE);
 end;
end;

procedure SpawnView(sr : byte; imu : pbitmaptype);
// Creates a window with a bitmap for viewdata[sr]. SR is 0 for the source
// image, and non-zero for a processed result image.
// viewdata[sr] can be uninitialised.
// bitmaptype(imu^) must have a memformat 0 or 1 image.
// viewdata[sr].sizexy will be the window client area's dimensions.
// viewdata[sr].bmpdata.sizexy will be the bitmap's real pixel dimensions.
// The bitmaptype record imu^ will be copied to viewdata[sr].bmpdata, and the
// original will be wiped out.
var kind : string;
    z : dword;
begin
 if sr > high(viewdata) then sr := high(viewdata);
 if viewdata[sr].winhandu <> 0 then DestroyWindow(viewdata[sr].winhandu);

 // 24-bit RGB or 32-bit RGBA : accept no imitations
 if imu^.memformat > 1 then mcg_ExpandIndexed(imu);

 viewdata[sr].alpha := 3 + (imu^.memformat and 1);
 with viewdata[sr] do begin
  zoom := 1; viewofsx := 0; viewofsy := 0;
  bmpdata := imu^;
  setlength(bmpdata.palette, length(imu^.palette));
  if length(imu^.palette) > 0 then
   move(imu^.palette[0], bmpdata.palette[0], length(imu^.palette) * 4);
  setlength(imu^.palette, 0);
  fillbyte(imu^, sizeof(bitmaptype), 0);
 end;

 if batchprocess = FALSE then begin
  // Set up the new view window.
  kind := viewclass;
  z := WS_TILEDWINDOW;
  viewdata[sr].winsizex := viewdata[sr].bmpdata.sizex;
  viewdata[sr].winsizey := viewdata[sr].bmpdata.sizey;
  //GetClientRect(GetDesktopWindow, rr); // this gives desktop resolution
  // but we want a maximized window that does not overlap the taskbar!
  rr.right := GetSystemMetrics(SM_CXMAXIMIZED) - GetSystemMetrics(SM_CXFRAME) * 4;
  rr.bottom := GetSystemMetrics(SM_CYMAXIMIZED) - GetSystemMetrics(SM_CYFRAME) * 4 - GetSystemMetrics(SM_CYCAPTION);
  if viewdata[sr].winsizex > rr.right then viewdata[sr].winsizex := rr.right;
  if viewdata[sr].winsizey > rr.bottom then viewdata[sr].winsizey := rr.bottom;
  rr.left := 0; rr.right := viewdata[sr].winsizex;
  rr.top := 0; rr.bottom := viewdata[sr].winsizey;
  adjustWindowRect(@rr, z, FALSE);
  rr.right := rr.right - rr.left; rr.bottom := rr.bottom - rr.top;
  viewdata[sr].winhandu := CreateWindow(@kind[1], NIL, z,
    0, 0, rr.right, rr.bottom,
    0, 0, system.maininstance, NIL);
  if viewdata[sr].winhandu = 0 then halt(99);

  SetWindowLong(viewdata[sr].winhandu, GWL_USERDATA, sr);
  ShowWindow(viewdata[sr].winhandu, SW_SHOWNORMAL);

  with bminfo.bmiheader do begin
   bisize := sizeof(bminfo.bmiheader);
   biwidth := viewdata[sr].bmpdata.sizex;
   biheight := -viewdata[sr].bmpdata.sizey;
   bisizeimage := 0; biplanes := 1;
   bibitcount := 32; bicompression := bi_RGB;
   biclrused := 0; biclrimportant := 0;
   bixpelspermeter := 28000; biypelspermeter := 28000;
  end;
  dword(bminfo.bmicolors) := 0;
  mv_DC := getDC(viewdata[sr].winhandu);
  viewdata[sr].deeku := createCompatibleDC(mv_DC);
  ReleaseDC(viewdata[sr].winhandu, mv_DC);
  viewdata[sr].BuffyH := createDIBsection(viewdata[sr].deeku, bminfo, dib_rgb_colors, viewdata[sr].buffy, 0, 0);
  viewdata[sr].OldBuffyH := selectObject(viewdata[sr].deeku, viewdata[sr].BuffyH);

  RedrawView(sr);
  EnableWindow(mv_ButtonH[1], TRUE);
 end;

 MakeHistogram(sr);
 if sr = 0 then DetectFlats;
end;

{$include bcc_algo.pas}

// ------------------------------------------------------------------

function HelpProc(window : hwnd; amex : uint; wepu : wparam; lapu : lparam) : lresult; stdcall;
// A window for displaying helpful text.
var z : dword;
    i : byte;
    kind : string[9];
    bulkhelp : pointer;
begin
 HelpProc := 0;
 case amex of
   wm_Create:
   begin
    kind := 'EDIT' + chr(0);
    z := WS_CHILD or WS_VISIBLE or WS_VSCROLL or ES_WANTRETURN
      or ES_MULTILINE or ES_READONLY;
    HelpTxtH := CreateWindowEx(WS_EX_CLIENTEDGE, @kind[1], NIL, z,
      0, 0, helpsizex, helpsizey,
      window, 29, system.maininstance, NIL);
    SendMessageA(HelpTxtH, WM_SETFONT, longint(mv_FontH[1]), 0);
    SendMessageA(HelpTxtH, EM_SETMARGINS, EC_LEFTMARGIN or EC_RIGHTMARGIN, $100010);
    // Populate the help text.
    getmem(bulkhelp, 256 * length(helptxt) + 1);
    z := 0;
    for i := 0 to high(helptxt) do begin
     move(helptxt[i][1], (bulkhelp + z)^, length(helptxt[i]));
     inc(z, length(helptxt[i]));
     byte((bulkhelp + z)^) := 13; inc(z);
     byte((bulkhelp + z)^) := 10; inc(z);
     byte((bulkhelp + z)^) := 13; inc(z);
     byte((bulkhelp + z)^) := 10; inc(z);
    end;
    byte((bulkhelp + z)^) := 0; inc(z);
    SendMessageA(HelpTxtH, WM_SETTEXT, 0, ptrint(bulkhelp));
    freemem(bulkhelp);
   end;

   wm_MouseWheel:
   begin
    longint(z) := integer(wepu shr 16);
    if longint(z) < 0 then
     SendMessage(HelpTxtH, EM_SCROLL, SB_LINEDOWN, 0)
    else
     SendMessage(HelpTxtH, EM_SCROLL, SB_LINEUP, 0);
   end;

   wm_Size:
   begin
    // If resizing the window, also resize the edit field.
    helpsizex := word(lapu);
    helpsizey := lapu shr 16;
    SetWindowPos(HelpTxtH, 0, 0, 0, helpsizex, helpsizey,
    SWP_NOACTIVATE or SWP_NOCOPYBITS or SWP_NOMOVE or SWP_NOZORDER);
   end;

   wm_Close:
   begin
    DestroyWindow(window);
    HelpWinH := 0; HelpProc := 0;
   end;

   else HelpProc := DefWindowProc(window, amex, wepu, lapu);
 end;
end;

function AlfaSelectorProc(window : hwnd; amex : uint; wepu : wparam; lapu : lparam) : lresult; stdcall;
// A mini-dialog box for entering the color that alpha is rendered with.
var flaguz : dword;
    kind : string[9];
    txt : string;
    handuli : hwnd;
begin
 AlfaSelectorProc := 0;
 case amex of
   wm_InitDialog:
   begin
    flaguz := SWP_NOMOVE or SWP_NOREDRAW;
    rr.left := 0; rr.right := 384;
    rr.top := 0; rr.bottom := 144;
    AdjustWindowRect(rr, WS_CAPTION or DS_CENTER or DS_MODALFRAME, FALSE);
    SetWindowPos(window, HWND_TOP, 0, 0, rr.right - rr.left, rr.bottom - rr.top, flaguz);

    kind := 'STATIC' + chr(0);
    txt := 'Please enter the hexadecimal color to render the alpha channel with' + chr(13) + '(example: FF00FF would be pinkish violet)' + chr(0);
    flaguz := WS_CHILD or WS_VISIBLE or SS_CENTER;
    rr.left := 0; rr.right := 384;
    rr.top := 24; rr.bottom := 32;
    handuli := CreateWindow(@kind[1], @txt[1], flaguz,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 180, system.maininstance, NIL);
    SendMessageA(handuli, WM_SETFONT, longint(mv_FontH[2]), -1);

    kind := 'EDIT' + chr(0);
    txt := hexifycolor(acolor) + chr(0);
    flaguz := WS_CHILD or WS_VISIBLE or ES_UPPERCASE or WS_TABSTOP;
    rr.left := 96; rr.right := 192;
    rr.top := 64; rr.bottom := 24;
    handuli := CreateWindowEx(WS_EX_CLIENTEDGE, @kind[1], @txt[1], flaguz,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 181, system.maininstance, NIL);
    SendMessageA(handuli, WM_SETFONT, longint(mv_FontH[1]), -1);
    SendMessageA(handuli, EM_SETLIMITTEXT, 6, 0);

    kind := 'BUTTON' + chr(0);
    txt := 'OK' + chr(0);
    flaguz := WS_CHILD or WS_VISIBLE or BS_CENTER or BS_DEFPUSHBUTTON or WS_TABSTOP;
    rr.left := 160; rr.right := 56;
    rr.top := 96; rr.bottom := 24;
    handuli := CreateWindow(@kind[1], @txt[1], flaguz,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 182, system.maininstance, NIL);
    SendMessageA(handuli, WM_SETFONT, longint(mv_FontH[1]), -1);
    SendMessageA(window, DM_SETDEFID, 182, 0);

    AlfaSelectorProc := 1;
   end;

   wm_Command:
   if word(wepu) = 182 then begin
    SendMessageA(window, wm_Close, 0, 0);
    AlfaSelectorProc := 1;
   end
   else if word(wepu) = 181 then begin
    if wepu shr 16 = EN_UPDATE then begin
     txt[0] := chr(0);
     byte(kind[0]) := SendMessageA(lapu, WM_GETTEXT, 9, ptrint(@kind[1]));
     flaguz := length(kind);
     while flaguz <> 0 do begin
      if (kind[flaguz] in ['0'..'9','A'..'F'] = FALSE) then begin
       kind := copy(kind, 1, flaguz - 1) + copy(kind, flaguz + 1, length(kind) - flaguz);
       txt[0] := chr(flaguz);
      end;
      dec(flaguz);
     end;
     kind := kind + chr(0);
     flaguz := 0; flaguz := byte(txt[0]);
     if flaguz <> 0 then begin
      dec(flaguz);
      SendMessageA(lapu, WM_SETTEXT, length(kind), ptrint(@kind[1]));
      SendMessageA(lapu, EM_SETSEL, flaguz, flaguz);
     end;
     flaguz := valhex(kind);
     acolor.b := byte(flaguz);
     acolor.g := byte(flaguz shr 8);
     acolor.r := byte(flaguz shr 16);
    end;
   end;

   wm_Close:
   begin
    for flaguz := 0 to high(viewdata) do RedrawView(flaguz);
    EndDialog(window, 0);
    AlfaSelectorProc := 1;
   end;
 end;
end;

function FunProc(window : hwnd; amex : uint; wepu : wparam; lapu : lparam) : lresult; stdcall;
var flaguz : dword;
    kind : string[9];
    txt : string;
begin
 FunProc := 0;
 case amex of
   wm_InitDialog:
   begin
    // I think this used to show processing messages...
    {if (batchprocess) and (strutsi <> '') then begin
     strutsi := strutsi + chr(0);
     SendMessageA(window, WM_SETTEXT, 0, longint(@strutsi[1]));
    end;}
    // fun window: (8 + funsizex + 8) x (8 + funsizey + 76)
    funsizex := funsizex and $FFFC; // confirm DWORD-alignment
    funwinhandle := window;
    kind := 'STATIC' + chr(0);
    txt := 'Initialising...' + chr(0);
    flaguz := WS_CHILD or WS_VISIBLE or SS_CENTER;
    rr.left := 0; rr.right := funsizex + 16;
    rr.top := funsizey + 16; rr.bottom := 24;
    funstatus := CreateWindow(@kind[1], @txt[1], flaguz,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 71, system.maininstance, NIL);
    SendMessageA(funstatus, WM_SETFONT, longint(mv_FontH[2]), -1);

    kind := 'BUTTON' + chr(0);
    txt := 'Never mind' + chr(0);
    flaguz := WS_CHILD or WS_VISIBLE or BS_CENTER or BS_PUSHLIKE;
    rr.left := (funsizex shr 1) - 56; rr.right := 128;
    rr.top := funsizey + 48; rr.bottom := 24;
    funbutton := CreateWindow(@kind[1], @txt[1], flaguz,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 72, system.maininstance, NIL);
    SendMessageA(funbutton, WM_SETFONT, longint(mv_FontH[1]), -1);

    kind := 'STATIC' + chr(0); txt := chr(0);
    flaguz := SS_BITMAP or WS_CHILD or WS_VISIBLE;
    rr.left := 8; rr.right := funsizex;
    rr.top := 8; rr.bottom := funsizey;
    funpal := CreateWindow(@kind[1], NIL, flaguz,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 73, system.maininstance, NIL);

    with bminfo.bmiheader do begin
     bisize := sizeof(bminfo.bmiheader);
     biwidth := funsizex;
     biheight := -funsizey;
     bisizeimage := 0; biplanes := 1;
     bibitcount := 32; bicompression := bi_rgb;
     biclrused := 0; biclrimportant := 0;
     bixpelspermeter := 28000; biypelspermeter := 28000;
    end;
    dword(bminfo.bmicolors) := 0;
    mv_DC := getDC(funpal);
    mv_FunDIBhandle := createDIBsection(mv_DC, bminfo, dib_rgb_colors, mv_FunBuffy, 0, 0);
    ReleaseDC(funpal, mv_DC);
    SendMessageA(funpal, STM_SETIMAGE, IMAGE_BITMAP, longint(mv_FunDIBhandle));
    // Set a timed update.
    SetTimer(window, 123, 500, NIL);
    FunProc := 1;
   end;

   wm_Command:
   if word(wepu) = 72 then begin
    compressing := FALSE;
    FunProc := 1;
   end;

   wm_Timer:
   if updatefun then begin
    DrawFunBuffy;
    updatefun := FALSE;
    FunProc := 1;
   end;

   wm_Close:
   begin
    KillTimer(window, 123);
    deleteObject(mv_FunDIBHandle); mv_FunDIBHandle := 0;
    mv_FunBuffy := NIL; funwinhandle := 0;
    compressing := FALSE;
    EndDialog(window, 0);
    FunProc := 1;
   end;
 end;
end;

function MagicProc(window : hwnd; amex : uint; wepu : wparam; lapu : lparam) : lresult; stdcall;
// Handles win32 messages for the magic color list.
var mv_PS : paintstruct;
    kind : string[16];
begin
 case amex of
   // Copy stuff to screen from our own buffer
   wm_Paint:
   begin
    mv_DC := beginPaint (window, @mv_PS);
    bitBlt (mv_DC,
      mv_PS.rcPaint.left,
      mv_PS.rcPaint.top,
      mv_PS.rcPaint.right - mv_PS.rcPaint.left + 1,
      mv_PS.rcPaint.bottom - mv_PS.rcPaint.top + 1,
      mv_ListBuffyDC,
      mv_PS.rcPaint.left, mv_PS.rcPaint.top,
      SRCCOPY);
    endPaint (window, mv_PS);
    MagicProc := 0;
   end;

   // Mouseclicks
   wm_LButtonDown:
   begin
    pe_used := (lapu shr 16) div (160 shr 3) + GetScrollPos(mv_SliderH[1], SB_CTL);
    kind := 'Selected: ' + strdec(pe_used) + chr(0);
    SendMessageA(mv_StaticH[6], WM_SETTEXT, 0, ptrint(@kind[1]));
    DrawMagicList;
    if pe[pe_used].status = PE_FREE then begin
     kind := chr(0);
     SendMessageA(mv_EditH[1], WM_SETTEXT, 0, ptrint(@kind[1]));
     kind := 'FF' + chr(0);
     SendMessageA(mv_EditH[2], WM_SETTEXT, 0, ptrint(@kind[1]));
     EnableWindow(mv_ButtonH[3], FALSE);
    end
    else begin
     kind := hexifycolor(pe[pe_used].colo) + chr(0);
     SendMessageA(mv_EditH[1], WM_SETTEXT, 0, ptrint(@kind[1]));
     kind := hextable[pe[pe_used].colo.a shr 4] + hextable[pe[pe_used].colo.a and $F] + chr(0);
     SendMessageA(mv_EditH[2], WM_SETTEXT, 0, ptrint(@kind[1]));
     EnableWindow(mv_ButtonH[3], TRUE);
    end;
    colorpicking := FALSE;
    SendMessageA(mv_ButtonH[1], bm_setcheck, BST_UNCHECKED, 0);
    ShowWindow(mv_StaticH[7], SW_HIDE);
    InvalidateRect(mv_ColorBlockH, NIL, TRUE);
    MagicProc := 0;
   end;

   else MagicProc := DefWindowProc (Window, AMex, wepu, lapu);
 end;
end;

function mv_MainProc(window : hwnd; amex : uint; wepu : wparam; lapu : lparam) : lresult; stdcall;
// Message handler for the main work window that has everything on it.
var kind, strutsi, txt : string;
    slideinfo : scrollinfo;
    openfilurec : openfilename;
    cliphand : handle;
    objp, filulist : pointer;
    i, j, z : dword;
    f : file;
begin
 mv_MainProc := 0;
 case amex of
   // Initialization
   wm_Create:
   begin
    kind := 'Arial' + chr(0); // bold font
    mv_FontH[1] := CreateFont(16, 0, 0, 0, 600, 0, 0, 0,
      ANSI_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
      DEFAULT_QUALITY, DEFAULT_PITCH or FF_DONTCARE, @kind[1]);

    kind := 'Arial' + chr(0); // smaller normal font
    mv_FontH[2] := CreateFont(14, 0, 0, 0, 0, 0, 0, 0, ANSI_CHARSET,
      OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
      DEFAULT_QUALITY, DEFAULT_PITCH or FF_DONTCARE, @kind[1]);

    // Create static interface strings...
    kind := 'STATIC' + chr(0);
    z := WS_CHILD or WS_VISIBLE or SS_ETCHEDHORZ;
    rr.left := 0; rr.right := mainsizex + 8;
    rr.top := 0; rr.bottom := 1;
    mv_StaticH[1]:= CreateWindow(@kind[1], NIL, z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 51, system.maininstance, NIL);

    z := WS_CHILD or WS_VISIBLE or SS_LEFT;
    rr.left := 8; rr.right := mainsizex - 8;
    rr.top := 8; rr.bottom := 16;
    txt := 'Preset palette' + chr(0);
    mv_StaticH[2]:= CreateWindow(@kind[1], @txt[1], z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 52, system.maininstance, NIL);

    rr.left := 8; rr.right := mainsizex - 8;
    rr.top := mainsizey - 132; rr.bottom := 16;
    txt := 'Output palette size: 256 colors' + chr(0);
    mv_StaticH[3]:= CreateWindow(@kind[1], @txt[1], z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 53, system.maininstance, NIL);

    rr.left := 8; rr.right := (mainsizex shr 1) - 8;
    rr.top := mainsizey - 80; rr.bottom := 16;
    txt := 'Colorspace:' + chr(0);
    mv_StaticH[4]:= CreateWindow(@kind[1], @txt[1], z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 54, system.maininstance, NIL);

    rr.left := mainsizex shr 1; rr.right := (mainsizex shr 1) - 8;
    txt := 'Dithering:' + chr(0);
    mv_StaticH[5]:= CreateWindow(@kind[1], @txt[1], z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 55, system.maininstance, NIL);

    rr.top := 42; rr.bottom := 20;
    rr.left := mainsizex shr 1; rr.right := (mainsizex shr 2) - 8;
    txt := 'Selected: 0' + chr(0);
    mv_StaticH[6]:= CreateWindow(@kind[1], @txt[1], z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 56, system.maininstance, NIL);

    // Toggle visibility when colorpicking and color already set.
    z := WS_CHILD or SS_CENTER;
    rr.top := 10;
    rr.left := (mainsizex shr 2) * 3;
    rr.right := (mainsizex shr 2) - 8;
    txt := 'Already set' + chr(0);
    mv_StaticH[7]:= CreateWindow(@kind[1], @txt[1], z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 57, system.maininstance, NIL);

    // The sunken border around the magic color list.
    z := WS_CHILD or WS_VISIBLE or SS_SUNKEN;
    magicx := (mainsizex shr 1 - 42) and $FFFC;
    magicy := 160;
    rr.left := 8; rr.right := magicx + 2;
    rr.top := 29; rr.bottom := magicy + 2;
    mv_StaticH[0]:= CreateWindow(@kind[1], NIL, z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 58, system.maininstance, NIL);

    // Create the color block, to show which color is selected.
    z := WS_CHILD or WS_VISIBLE or SS_CENTER;
    rr.left := mainsizex - 32; rr.right := 24;
    rr.top := 64; rr.bottom := 24;
    txt := chr(0);
    mv_ColorBlockH := CreateWindow(@kind[1], @txt[1], z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 50, system.maininstance, NIL);

    // Create the magic color list, for color presets.
    kind := magicclass;
    z := WS_CHILD or WS_VISIBLE;
    rr.left := 9; rr.right := magicx;
    rr.top := 30; rr.bottom := magicy;
    mv_ListH[1] := CreateWindow(@kind[1], NIL, z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 59, system.maininstance, NIL);
    with bminfo.bmiheader do begin
     bisize := sizeof(bminfo.bmiheader);
     biwidth := magicx;
     biheight := -magicy;
     bisizeimage := 0; biplanes := 1;
     bibitcount := 24; bicompression := bi_rgb;
     biclrused := 0; biclrimportant := 0;
     bixpelspermeter := 28000; biypelspermeter := 28000;
    end;
    dword(bminfo.bmicolors) := 0;
    mv_DC := getDC(mv_ListH[1]);
    mv_ListBuffyDC := createCompatibleDC(mv_DC);
    ReleaseDC(mv_ListH[1], mv_DC);
    mv_ListBuffyHandle := createDIBsection(mv_ListBuffyDC, bminfo, dib_rgb_colors, mv_ListBuffy, 0, 0);
    mv_OldListBuffyHandle := selectObject(mv_ListBuffyDC, mv_ListBuffyHandle);
    DrawMagicList;

    // Create controls.
    kind := 'SCROLLBAR' + chr(0);
    z := WS_CHILD or WS_VISIBLE or SBS_VERT;
    rr.left := mainsizex shr 1 - 24; rr.right := 16;
    rr.top := 29; rr.bottom := magicy + 2;
    mv_SliderH[1]:= CreateWindow(@kind[1], NIL, z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 41, system.maininstance, NIL);

    kind := 'EDIT' + chr(0);
    z := WS_CHILD or WS_VISIBLE or ES_UPPERCASE or ES_AUTOHSCROLL;
    rr.left := (mainsizex shr 1) - 2;
    rr.right := (mainsizex shr 2) - 8 + 4;
    rr.top := 64; rr.bottom := 24;
    mv_EditH[1] := CreateWindowEx(WS_EX_CLIENTEDGE, @kind[1], NIL, z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 40, system.maininstance, NIL);

    rr.left := (mainsizex shr 2) * 3; rr.right := 32;
    mv_EditH[2] := CreateWindowEx(WS_EX_CLIENTEDGE, @kind[1], NIL, z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 39, system.maininstance, NIL);

    kind := 'BUTTON' + chr(0);
    z := WS_CHILD or WS_VISIBLE or BS_TEXT or BS_AUTOCHECKBOX or BS_PUSHLIKE;
    txt := 'From image' + chr(0);
    rr.right := (mainsizex shr 2) - 8;
    rr.top := 30; rr.bottom := 24;
    mv_ButtonH[1]:= CreateWindow(@kind[1], @txt[1], z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 61, system.maininstance, NIL);

    z := WS_CHILD or WS_VISIBLE or BS_TEXT or BS_PUSHBUTTON;
    txt := 'Apply' + chr(0);
    rr.left := (mainsizex shr 1);
    rr.right := mainsizex shr 2 - 8;
    rr.top := 96;
    mv_ButtonH[2]:= CreateWindow(@kind[1], @txt[1], z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 62, system.maininstance, NIL);

    txt := 'Delete' + chr(0);
    rr.left := mainsizex - rr.right - 8;
    mv_ButtonH[3]:= CreateWindow(@kind[1], @txt[1], z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 63, system.maininstance, NIL);

    txt := 'Compress!' + chr(0);
    rr.left := mainsizex shr 1; rr.right := rr.left - 8;
    rr.top := 23 + magicy - rr.bottom;
    mv_ButtonH[4]:= CreateWindow(@kind[1], @txt[1], z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 64, system.maininstance, NIL);

    kind := 'SCROLLBAR' + chr(0);
    z := WS_CHILD or WS_VISIBLE or SBS_HORZ;
    rr.left := 8; rr.right := mainsizex - 16;
    rr.top := mainsizey - 110; rr.bottom := 16;
    mv_SliderH[2]:= CreateWindow(@kind[1], NIL, z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 42, system.maininstance, NIL);

    kind := 'BUTTON' + chr(0);
    z := WS_CHILD or WS_VISIBLE or BS_TEXT or BS_AUTOCHECKBOX;
    txt := 'Favor flat colors' + chr(0);
    rr.left := mainsizex shr 1; rr.right := mainsizex - rr.left - 8;
    rr.top := mainsizey - 24; rr.bottom := 16;
    mv_ButtonH[5]:= CreateWindow(@kind[1], @txt[1], z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 65, system.maininstance, NIL);

    txt := 'Preserve contrast' + chr(0);
    rr.left := 8; rr.right := mainsizex shr 1 - 8;
    mv_ButtonH[6]:= CreateWindow(@kind[1], @txt[1], z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 66, system.maininstance, NIL);

    kind := 'COMBOBOX' + chr(0);
    z := WS_CHILD or WS_VISIBLE or CBS_DROPDOWNLIST;
    rr.left := 8; rr.right := (mainsizex shr 1) - 16;
    rr.top := mainsizey - 60; rr.bottom := 256;
    mv_ListH[3] := CreateWindow(@kind[1], NIL, z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 68, system.maininstance, NIL);

    rr.left := mainsizex shr 1; rr.right := (mainsizex shr 1) - 8;
    mv_ListH[2] := CreateWindow(@kind[1], NIL, z,
      rr.left, rr.top, rr.right, rr.bottom,
      window, 67, system.maininstance, NIL);

    // Initialize the controls.
    slideinfo.cbSize := sizeof(slideinfo);
    slideinfo.fMask := SIF_ALL;
    slideinfo.nMin := 0;
    slideinfo.nMax := 255;
    slideinfo.nPage := 8;
    slideinfo.nPos := 0;
    SetScrollInfo(mv_SliderH[1], SB_CTL, @slideinfo, TRUE);

    slideinfo.nMin := 2;
    slideinfo.nPos := 256;
    slideinfo.nPage := 16;
    slideinfo.nMax := slideinfo.nPos + slideinfo.nPage - 1;
    SetScrollInfo(mv_SliderH[2], SB_CTL, @slideinfo, TRUE);

    for i := 2 to 5 do SendMessageA(mv_StaticH[i], WM_SETFONT, longint(mv_FontH[1]), 1);
    for i := 6 to 7 do SendMessageA(mv_StaticH[i], WM_SETFONT, longint(mv_FontH[2]), 1);
    for i := 1 to 6 do SendMessageA(mv_ButtonH[i], WM_SETFONT, longint(mv_FontH[2]), 0);
    SendMessageA(mv_ButtonH[4], WM_SETFONT, longint(mv_FontH[1]), 0);

    for i := 1 to 4 do EnableWindow(mv_ButtonH[i], FALSE);
    SendMessageA(mv_ButtonH[6], BM_SETCHECK, BST_CHECKED, 0);
    SendMessageA(mv_EditH[1], EM_SETLIMITTEXT, 6, 0);
    SendMessageA(mv_EditH[1], WM_SETFONT, longint(mv_FontH[1]), 0);
    SendMessageA(mv_EditH[2], EM_SETLIMITTEXT, 2, 0);
    SendMessageA(mv_EditH[2], WM_SETFONT, longint(mv_FontH[1]), 0);
    txt := 'FF' + chr(0);
    SendMessageA(mv_EditH[2], WM_SETTEXT, 0, ptrint(@txt[1]));
    for i := 2 to 3 do SendMessageA(mv_ListH[i], WM_SETFONT, longint(mv_FontH[2]), 0);
    for i := 0 to high(dithername) do begin
     txt := dithername[i] + chr(0);
     SendMessageA(mv_ListH[2], CB_ADDSTRING, 0, ptrint(@txt[1]));
    end;
    for i := 0 to high(colorspacename) do begin
     txt := colorspacename[i] + chr(0);
     SendMessageA(mv_ListH[3], CB_ADDSTRING, 0, ptrint(@txt[1]));
    end;
    for i := 2 to 3 do SendMessageA(mv_ListH[i], CB_SETCURSEL, 1, 0);
    mv_CBBrushH := CreateSolidBrush(0);
   end;

   wm_Command:
   begin
    case word(wepu) of
      39:
      if (wepu shr 16 = EN_CHANGE) then ValidateAlfaco;

      40:
      if (wepu shr 16 = EN_CHANGE) then begin
       ValidateHexaco;
       InvalidateRect(mv_ColorBlockH, NIL, TRUE);
      end;

      // GUI button: Pick a color from the image
      61:
      begin
       if SendMessageA(mv_ButtonH[1], bm_getcheck, 0, 0) = BST_CHECKED
       then colorpicking := TRUE else colorpicking := FALSE;
       ShowWindow(mv_StaticH[7], SW_HIDE);
      end;

      // GUI button: Apply
      62:
      begin
       pe[pe_used].status := PE_FIXED;
       byte(kind[0]) := SendMessageA(mv_EditH[1], WM_GETTEXT, 7, ptrint(@kind[1]));
       i := valhex(kind);
       pe[pe_used].colo.r := byte(i shr 16);
       pe[pe_used].colo.g := byte(i shr 8);
       pe[pe_used].colo.b := byte(i);
       byte(kind[0]) := SendMessageA(mv_EditH[2], WM_GETTEXT, 3, ptrint(@kind[1]));
       i := valhex(kind);
       pe[pe_used].colo.a := i;
       DrawMagicList;
       EnableWindow(mv_ButtonH[3], TRUE);
       colorpicking := FALSE;
       SendMessageA(mv_ButtonH[1], bm_setcheck, BST_UNCHECKED, 0);
       ShowWindow(mv_StaticH[7], SW_HIDE);
      end;

      // GUI button: Delete
      63:
      begin
       ClearPE(pe_used, pe_used);
       DrawMagicList;
       EnableWindow(mv_ButtonH[3], FALSE);
       colorpicking := FALSE;
       SendMessageA(mv_ButtonH[1], bm_setcheck, BST_UNCHECKED, 0);
       ShowWindow(mv_StaticH[7], SW_HIDE);
      end;

      // GUI button: Compress!
      64:
      begin
       colorpicking := FALSE;
       compressorthreadID := 1;
       SendMessageA(mv_ButtonH[1], bm_setcheck, BST_UNCHECKED, 0);
       ShowWindow(mv_StaticH[7], SW_HIDE);
       GrabConfig; // get the option.settings
       // Get to work!
       compressing := TRUE;

       // Color compression is done in a new thread...
       compressorthreadhandle := beginthread
         (@CompressColors, NIL, compressorthreadID);

       // Meanwhile this prime thread launches FunBox, a modal dialog box,
       // and stops code execution until the box is closed. The FunBox
       // displays palette changes in real time to entertain the user.
       // It also has a "Cancel"-button.
       // Code execution continues when:
       // 1. Color compression is done (or fails), which sends a WM_CLOSE
       //    message to the Funbox.
       // 2. The user aborts, which sends a WM_CLOSE to the Funbox and sets
       //    compressing to FALSE. The compression work thread quits when it
       //    sees the flag changed.
       DialogBoxIndirect(system.maininstance, @mv_Dlg, mv_MainWinH, @FunProc);
       // To avoid winhandle leaking...
       CloseHandle(compressorthreadhandle);

       // Only the main thread can create a persistent window, so the
       // reduced-color image has been stuck in rendimu^.
       if rendimu.image <> NIL then begin
        // Find the first free view slot.
        i := 1;
        while (viewdata[i].winhandu <> 0) and (i < high(viewdata)) do inc(i);
        // And show the results!
        SpawnView(i, @rendimu);
        txt := 'Result - ' + strdec(length(viewdata[i].bmpdata.palette)) + ' colors';
        if viewdata[i].alpha = 4 then txt := txt + ' with alpha';
        txt := txt + ', ' + colorspacename[option.colorspace] + ', ' + dithername[option.dithering] + chr(0);
        SendMessageA(viewdata[i].winhandu, WM_SETTEXT, 0, ptrint(@txt[1]));
       end;
       compressorthreadID := 0;
      end;

      // Command: Scrap the source image's alpha channel
      88:
      if viewdata[0].winhandu = 0 then begin
       txt := 'There is no source image.' + chr(0);
       MessageBoxA(window, @txt[1], NIL, MB_OK);
      end
      else begin
       if viewdata[0].alpha <> 4 then begin
        txt := 'Source has no alpha.' + chr(0);
        MessageBoxA(window, @txt[1], NIL, MB_OK);
       end
       else begin
        // build a new 24-bit image from previous 32-bit
        z := viewdata[0].bmpdata.sizex * viewdata[0].bmpdata.sizey;
        getmem(objp, z * 3);
        while z <> 0 do begin
         dec(z);
         RGBarray(objp^)[z].r := RGBAarray(viewdata[0].bmpdata.image^)[z].r;
         RGBarray(objp^)[z].g := RGBAarray(viewdata[0].bmpdata.image^)[z].g;
         RGBarray(objp^)[z].b := RGBAarray(viewdata[0].bmpdata.image^)[z].b;
        end;
        freemem(viewdata[0].bmpdata.image);
        viewdata[0].bmpdata.image := objp;
        objp := NIL;
        // refresh all secondary image data
        viewdata[0].alpha := 3;
        setlength(viewdata[0].bmpdata.palette, 0);
        MakeHistogram(0);
        DetectFlats;
        RedrawView(0);
        // adjust the view's name
        byte(txt[0]) := GetWindowText(viewdata[0].winhandu, @txt[1], 255);
        z := length(txt);
        while (z <> 0) and (txt[z] <> '-') do dec(z);
        txt := copy(txt, 1, z) + ' ' + strdec(length(viewdata[0].bmpdata.palette)) + ' colors' + chr(0);
        SendMessageA(viewdata[0].winhandu, WM_SETTEXT, 0, ptrint(@txt[1]));
       end;
      end;

      // File: Batch process images
      89:
      begin
       colorpicking := FALSE;
       compressorthreadID := 1;
       batchprocess := TRUE;
       SendMessageA(mv_ButtonH[1], bm_setcheck, BST_UNCHECKED, 0);
       ShowWindow(mv_StaticH[7], SW_HIDE);
       GrabConfig; // get the option.settings

       kind := 'PNG or BMP' + chr(0) + '*.png;*.bmp' + chr(0) + chr(0);
       filulist := allocmem(65536); // pre-zeroed memalloc
       fillbyte(openfilurec, sizeof(openfilurec), 0);
       with openfilurec do begin
        lStructSize := 76; // sizeof gives incorrect result?
        hwndOwner := window;
        lpstrFilter := @kind[1]; lpstrCustomFilter := NIL;
        nFilterIndex := 1;
        lpstrFile := filulist; nMaxFile := 65536;
        lpstrFileTitle := NIL; lpstrInitialDir := NIL; lpstrTitle := NIL;
        Flags := OFN_FILEMUSTEXIST or OFN_ALLOWMULTISELECT or OFN_EXPLORER;
       end;

       if GetOpenFileNameA(@openfilurec) then begin
        // Count the number of returned strings.
        z := 0; openfilurec.nmaxfile := 0;
        while word((filulist + z)^) <> 0 do begin
         if byte((filulist + z)^) = 0 then inc(openfilurec.nmaxfile);
         inc(z);
        end;

        // Display a confirmation box.
        if openfilurec.nmaxfile = 0 then begin
         txt := 'The 1 file';
         inc(openfilurec.nmaxfile);
        end else
         txt := 'The ' + strdec(openfilurec.nmaxfile) + ' files';
        txt := txt + ' you selected will be color-reduced and overwritten using the current settings.' + chr(0);
        kind := 'Batch processing' + chr(0);

        if MessageBoxA(window, @txt[1], @kind[1], MB_OKCANCEL) = IDOK then begin
         // Grab the files' directory.
         z := 0;
         while byte((filulist + z)^) <> 0 do inc(z);
         move(filulist^, kind[1], z);
         byte(kind[0]) := z;
         inc(z);

         // If there was just one file, the filename and directory are
         // 1 string; otherwise the directory is its own string which must
         // end with a backslash.
         if openfilurec.nmaxfile > 1 then
          if kind[length(kind)] <> '\' then kind := kind + '\';

         // Grab the filenames and process them.
         while openfilurec.nmaxfile <> 0 do begin
          txt := '';
          while byte((filulist + z)^) <> 0 do begin
           txt := txt + char((filulist + z)^);
           inc(z);
          end;
          inc(z);

          // open the image
          strutsi := kind + txt;
          assign(f, strutsi);
          filemode := 0; reset(f, 1); // read-only
          i := IOresult; // problem opening the file?
          if i <> 0 then begin
           txt := errortxt(i) + chr(0);
           MessageBoxA(window, @txt[1], NIL, MB_OK);
          end
          else begin
           j := filesize(f);
           getmem(objp, j);
           // Read file into memory.
           blockread(f, objp^, j);
           close(f);
           // Unpack image into tempbmp.
           i := mcg_LoadGraphic(objp, j, @tempbmp);
           freemem(objp); objp := NIL;
           if i <> 0 then begin
            txt := mcg_errortxt + chr(0);
            MessageBoxA(window, @txt[1], NIL, MB_OK)
           end
           else begin
            // Stick the unpacked graphic into viewdata[0].
            SpawnView(0, @tempbmp);
            // Go to town on the image!
            compressing := TRUE;
            compressorthreadhandle := beginthread
              (@CompressColors, NIL, compressorthreadID);
            strutsi := '(' + strdec(openfilurec.nmaxfile) + ') ' + strutsi;
            DialogBoxIndirect(system.maininstance, @mv_Dlg, mv_MainWinH, @FunProc);

            // To avoid winhandle leaking...
            CloseHandle(compressorthreadhandle);

            // The compressor thread put the result in rendimu^.
            if rendimu.image <> NIL then begin
             // Display the result very briefly.
             SpawnView(1, @rendimu);
             // Try to open a temp output file.
             assign(f, kind + '#$T3MP$#.imu');
             filemode := 1; rewrite(f, 1); // write-only
             i := IOresult;
             if i <> 0 then begin
              txt := errortxt(i) + chr(0);
              MessageBoxA(window, @txt[1], NIL, MB_OK);
             end
             else begin
              // Squash the whitespace from the image.
              fillbyte(rendimu, sizeof(rendimu), 0);
              PackView(1, 1, @rendimu);
              rendimu.sizex := viewdata[1].bmpdata.sizex;
              // Compress rendimu^ into objp.
              i := mcg_MemorytoPNG(@rendimu, @objp, @j);
              if i <> 0 then begin
               txt := mcg_errortxt + chr(0);
               MessageBoxA(window, @txt[1], NIL, MB_OK);
              end
              else begin
               // Write the PNG datastream into the file.
               blockwrite(f, objp^, j);
               i := IOresult;
               if i <> 0 then begin
                txt := errortxt(i) + chr(0);
                MessageBoxA(window, @txt[1], NIL, MB_OK);
               end;
               close(f);
               assign(f, kind + txt);
               erase(f);
               assign(f, kind + '#$T3MP$#.imu');
               rename(f, kind + txt);
              end;
             end;

             // Clean up
             close(f);
             while IOresult <> 0 do ; // flush
             SendMessageA(viewdata[1].winhandu, WM_CLOSE, 0, 0);
             freemem(objp); objp := NIL;
            end;

           end;
           SendMessageA(viewdata[0].winhandu, WM_CLOSE, 0, 0);
          end;

          dec(openfilurec.nmaxfile);
         end;
        end;

        kind := 'Batch processing' + chr(0);
        txt := 'Processing complete.' + chr(0);
        MessageBoxA(window, @txt[1], @kind[1], MB_OK);
       end;
       freemem(filulist); filulist := NIL;
       batchprocess := FALSE;
       compressorthreadID := 0;
      end;

      // File: Open a PNG or BMP file
      90:
      begin
       kind := 'PNG or BMP' + chr(0) + '*.png;*.bmp' + chr(0) + chr(0);
       txt := chr(0);
       fillbyte(openfilurec, sizeof(openfilurec), 0);
       with openfilurec do begin
        lStructSize := 76; // sizeof gives incorrect result?
        hwndOwner := window;
        lpstrFilter := @kind[1]; lpstrCustomFilter := NIL;
        nFilterIndex := 1;
        lpstrFile := @txt[1]; nMaxFile := 255;
        lpstrFileTitle := NIL; lpstrInitialDir := NIL; lpstrTitle := NIL;
        Flags := OFN_FILEMUSTEXIST;
       end;

       if GetOpenFileNameA(@openfilurec) then begin
        // We got a filename the user wants to open!
        assign(f, openfilurec.lpstrfile);
        filemode := 0; reset(f, 1); // read-only
        i := IOresult; // problem opening the file?
        if i <> 0 then begin
         txt := errortxt(i) + chr(0);
         MessageBoxA(window, @txt[1], NIL, MB_OK);
        end
        else begin
         j := filesize(f);
         getmem(objp, j); // read file into memory
         blockread(f, objp^, j);
         close(f);
         i := mcg_LoadGraphic(objp, j, @tempbmp);
         freemem(objp); objp := NIL;
         if i <> 0 then begin
          txt := mcg_errortxt + chr(0);
          MessageBoxA(window, @txt[1], NIL, MB_OK)
         end
         else begin
          SpawnView(0, @tempbmp);
          // set the window name: filename, format, color count
          txt := openfilurec.lpstrfile;
          txt := copy(txt, openfilurec.nFileOffset + 1, length(txt) - openfilurec.nFileOffset);
          if length(txt) > 130 then txt := copy(txt, 1, 128) + '...';
          txt := 'Original: ' + txt + ' - ' + strdec(length(viewdata[0].bmpdata.palette)) + ' colors';
          if viewdata[0].alpha = 4 then txt := txt + ' with alpha';
          txt := txt + chr(0);
          SendMessageA(viewdata[0].winhandu, WM_SETTEXT, 0, ptrint(@txt[1]));
         end;
         mcg_ForgetImage(@tempbmp);
        end;
       end;
      end;

      // Save view as PNG
      91:
      if lastactiveview <> $FF then SaveViewAsPNG(lastactiveview);

      // Load config
      92: LoadConfig(window);

      // Save config
      93: SaveConfig(window);

      // Copy image to clipboard
      94: if lastactiveview <> $FF then CopyView(lastactiveview);

      // Command: Paste from clipboard
      95:
      begin
       OpenClipboard(window);
       {i := 0;
       repeat
        i := EnumClipboardFormats(i);
        byte(strutsi[0]) := GetClipBoardFormatName(i, @strutsi[1], 255);
        writeln(i,'=',strutsi);
       until i = 0;}

       if IsClipboardFormatAvailable(CF_DIB) then begin
        cliphand := GetClipboardData(CF_DIB);
        objp := GlobalLock(cliphand);
        i := mcg_BMPtoMemory(objp, @tempbmp);
        GlobalUnlock(cliphand);
        if i <> 0 then begin
         strutsi := mcg_errortxt + chr(0);
         MessageBoxA(mv_MainWinH, @strutsi[1], NIL, MB_OK);
        end
        else begin
         SpawnView(0, @tempbmp);
         // Set the window name: filename, format, color count.
         txt := 'Original - ' + strdec(length(viewdata[0].bmpdata.palette)) + ' colors';
         if viewdata[0].alpha = 4 then txt := txt + ' with alpha';
         txt := txt + chr(0);
         SendMessageA(viewdata[0].winhandu, WM_SETTEXT, 0, ptrint(@txt[1]));
        end;
        mcg_ForgetImage(@tempbmp);
       end else
        MessageBoxA(window, 'No graphic found on clipboard.' + chr(0), NIL, MB_OK);
       CloseClipboard;
      end;

      // Import palette from a view.
      96: if lastactiveview <> $FF then ImportPalette(lastactiveview);

      // Command: Clear preset palette entries
      97:
      begin
       ClearPE(0, $FFFF);
       DrawMagicList;
       EnableWindow(mv_ButtonH[3], FALSE);
       colorpicking := FALSE;
       SendMessageA(mv_ButtonH[1], bm_setcheck, BST_UNCHECKED, 0);
       ShowWindow(mv_StaticH[7], SW_HIDE);
      end;

      // Command: Set Alpha rendering color
      98: DialogBoxIndirect(system.maininstance, @mv_Dlg, mv_MainWinH, @AlfaSelectorProc);

      // Help: Manual
      99:
      if HelpWinH = 0 then begin
       z := WS_TILEDWINDOW or WS_VISIBLE or WS_CLIPCHILDREN;
       kind := 'Help' + chr(0);
       rr.left := 0; rr.right := helpsizex;
       rr.top := 0; rr.bottom := helpsizey;
       AdjustWindowRect(@rr, z, FALSE);
       HelpWinH := CreateWindow(@helpclass[1], @kind[1], z,
         $8000, $8000, rr.right - rr.left, rr.bottom - rr.top,
         0, 0, system.maininstance, NIL);
      end;

      // File: Exit
      100: SendMessageA(mv_MainWinH, wm_close, 0, 0);
    end;
   end;

   // Color Block coloring
   wm_ctlcolorstatic:
   if dword(lapu) = mv_ColorBlockH then begin
    byte(txt[0]) := SendMessageA(mv_EditH[1], wm_gettext, 255, ptrint(@txt[1]));
    i := valhex(txt);
    i := (i shr 16) or (i and $FF00) or ((i and $FF) shl 16);
    if txt = '' then i := SwapEndian(dword(neutralcolor)) shr 8;
    deleteObject(mv_CBBrushH);
    mv_CBBrushH := CreateSolidBrush(i);
    mv_MainProc := LResult(mv_CBBrushH);
   end;

   // Slider handling
   wm_VScroll, wm_HScroll:
   if wepu and $FFFF <> SB_ENDSCROLL then begin
    slideinfo.fMask := SIF_ALL;
    slideinfo.cbSize := sizeof(slideinfo);
    GetScrollInfo(lapu, SB_CTL, @slideinfo);
    i := slideinfo.nPos;
    case wepu and $FFFF of
      SB_LINELEFT: if i > 0 then dec(i);
      SB_LINERIGHT: inc(i);
      SB_BOTTOM: i := high(pe);
      SB_TOP: i := 0;

      SB_PAGELEFT:
      if i > slideinfo.nPage then
       dec(i, slideinfo.nPage)
      else
       i := 0;

      SB_PAGERIGHT: inc(i, slideinfo.nPage);
      SB_THUMBPOSITION, SB_THUMBTRACK: i := wepu shr 16;
    end;

    slideinfo.fMask := SIF_POS;
    slideinfo.nPos := i;
    i := SetScrollInfo(lapu, SB_CTL, @slideinfo, TRUE);
    if dword(lapu) = mv_SliderH[1] then
     DrawMagicList
    else if dword(lapu) = mv_SliderH[2] then begin
     txt := 'Output palette size: ' + strdec(i) + ' colors' + chr(0);
     SendMessageA(mv_StaticH[3], wm_settext, 0, ptrint(@txt[1]));
    end;
   end;

   // Somebody desires our destruction!
   wm_Close:
   begin
    // Autosave the settings into the default settings file.
    WriteIni(homedir + 'buncomp.ini');
    SelectObject(mv_ListBuffyDC, mv_OldListBuffyHandle);
    DeleteDC(mv_ListBuffyDC);
    DeleteObject(mv_ListBuffyHandle);
    DeleteObject(mv_CBBrushH);

    DestroyWindow(window); mv_MainWinH := 0;
   end;

   wm_Destroy: mv_EndProgram := TRUE;

   else mv_MainProc := DefWindowProc(window, amex, wepu, lapu);
 end;

end;

function SpawnMainWindow : boolean;
// Creates the main window and prepares other window types to be used later.
// It cannot be a dialog because dialogs have trouble processing accelerator
// keypresses; whereas a normal window cannot process ws_tabstop. The latter
// is a smaller loss...
var windowclass : wndclass;
    winmsg : msg;
    txt : string;
    z : dword;
begin
 SpawnMainWindow := FALSE;
 // Register the magic color list class (preset color list in main window).
 windowclass.style := CS_OWNDC;
 windowclass.lpfnwndproc := wndproc(@MagicProc);
 windowclass.cbclsextra := 0;
 windowclass.cbwndextra := 0;
 windowclass.hinstance := system.maininstance;
 windowclass.hicon := 0;
 windowclass.hcursor := loadcursor(0, idc_arrow);
 windowclass.hbrbackground := 0;
 windowclass.lpszmenuname := NIL;
 windowclass.lpszclassname := @magicclass[1];
 if RegisterClass(windowclass) = 0 then halt(98);

 // Register the view class for future use (for source and result images).
 windowclass.style := CS_OWNDC;
 windowclass.lpfnwndproc := wndproc(@ViewProc);
 windowclass.cbclsextra := 0;
 windowclass.cbwndextra := 0;
 windowclass.hinstance := system.maininstance;
 txt := 'BunnyIcon' + chr(0);
 windowclass.hicon := LoadIcon(system.maininstance, @txt[1]);
 windowclass.hcursor := LoadCursor(0, idc_arrow);
 windowclass.hbrbackground := GetSysColorBrush(color_3Dface);
 windowclass.lpszmenuname := NIL;
 windowclass.lpszclassname := @viewclass[1];
 if RegisterClass(windowclass) = 0 then halt(98);

 // Register the help class for future use.
 windowclass.style := 0;
 windowclass.lpfnwndproc := wndproc(@HelpProc);
 windowclass.cbclsextra := 0;
 windowclass.cbwndextra := 0;
 windowclass.hinstance := system.maininstance;
 txt := 'BunnyIcon' + chr(0);
 windowclass.hicon := LoadIcon(system.maininstance, @txt[1]);
 windowclass.hcursor := LoadCursor(0, idc_arrow);
 windowclass.hbrbackground := GetSysColorBrush(color_3Dface);
 windowclass.lpszmenuname := NIL;
 windowclass.lpszclassname := @helpclass[1];
 if RegisterClass(windowclass) = 0 then halt(98);

 // Register the main class for immediate use.
 windowclass.style := 0;
 windowclass.lpfnwndproc := wndproc(@mv_MainProc);
 windowclass.cbclsextra := 0;
 windowclass.cbwndextra := 0;
 windowclass.hinstance := system.maininstance;

 txt := 'BunnyIcon' + chr(0);
 windowclass.hicon := LoadIcon(system.maininstance, @txt[1]);
 windowclass.hcursor := LoadCursor(0, idc_arrow);
 windowclass.hbrbackground := GetSysColorBrush(color_btnface);

 txt := 'BunnyMenu' + chr(0);
 windowclass.lpszmenuname := @txt[1];
 windowclass.lpszclassname := @mainclass[1];
 if RegisterClass(windowclass) = 0 then halt(98);

 mainsizex := 300; mainsizey := 330;
 z := dword(WS_CAPTION or WS_SYSMENU or WS_MINIMIZEBOX or WS_CLIPCHILDREN or WS_VISIBLE);
 rr.left := 0; rr.right := mainsizex; rr.top := 0; rr.bottom := mainsizey;
 AdjustWindowRect(@rr, z, TRUE);
 mv_MainWinH := CreateWindowEx(WS_EX_CONTROLPARENT,
   @mainclass[1], @mv_ProgramName[1], z,
   8, GetSystemMetrics(SM_CYSCREEN) - (rr.bottom - rr.top) - 40,
   rr.right - rr.left, rr.bottom - rr.top,
   0, 0, system.maininstance, NIL);
 if mv_MainWinH = 0 then halt(99);

 // Load the keyboard shortcut table from bunny.res.
 txt := 'BunnyHop' + chr(0);
 mv_AcceleratorTable := LoadAccelerators(system.maininstance, @txt[1]);

 // Create a right-click pop-up menu for the views.
 mv_ContextMenu := CreatePopupMenu;
 txt := '&Copy to clipboard ' + chr(8) + '(CTRL+C)' + chr(0);
 InsertMenu(mv_ContextMenu, 0, MF_BYPOSITION, 94, @txt[1]);
 txt := '&Save as PNG ' + chr(8) + '(CTRL+S)' + chr(0);
 InsertMenu(mv_ContextMenu, 1, MF_BYPOSITION, 91, @txt[1]);
 txt := 'I&mport palette ' + chr(8) + '(CTRL+M)' + chr(0);
 InsertMenu(mv_ContextMenu, 2, MF_BYPOSITION, 96, @txt[1]);

 // Just in case, make sure we are in the user's face.
 SetForegroundWindow(mv_MainWinH);
 SetFocus(mv_MainWinH);

 winmsg.hWnd := 0; // silence a compiler warning
 // Get rid of init messages and give the window its first layer of paint.
 while PeekMessage(@winmsg, mv_MainWinH, 0, 0, PM_REMOVE) do begin
  TranslateMessage(winmsg);
  DispatchMessage(winmsg);
 end;
end;

// ------------------------------------------------------------------

procedure DoInits;
var ptxt : pchar;
    txt : string;
    i, j : dword;
begin
 // Get the current directory! It is used for the config file.
 // If the current directory is not accessible, then try for that silly
 // Win\AppData\ directory...
 homedir := paramstr(0);
 i := length(homedir);
 while (i <> 0) and (homedir[i] <> '\') do dec(i);
 homedir := copy(homedir, 1, i); // homedir always ends with \

 // Set up a test file for write-only access!
 // Try to use the current directory first...
 assign(stdout, homedir + 'stdout.txt');
 filemode := 1; rewrite(stdout);
 i := IOresult;
 if i = 5 then begin // access denied! Try the AppData directory...
  // First, load shell32.dll from the windows\system directory...
  // (For security, must specify the system directory explicitly)
  getmem(ptxt, MAX_PATH);
  j := GetSystemDirectoryA(ptxt, MAX_PATH);
  if j = 0 then begin freemem(ptxt); ptxt := NIL; halt(84); end;
  txt := '\shell32.dll' + chr(0);
  move(txt[1], ptxt[j], length(txt));
  HelpWinH := LoadLibraryA(ptxt);
  txt := 'SHGetSpecialFolderPathA' + chr(0);
  pointer(SHGetSpecialFolderPath) := GetProcAddress(HelpWinH, @txt[1]);
  if pointer(SHGetSpecialFolderPath) = NIL then halt(86);
  if SHGetSpecialFolderPath(0, ptxt, CSIDL_APPDATA, TRUE) = FALSE then begin
   freemem(ptxt); ptxt := NIL; halt(87);
  end;
  FreeLibrary(HelpWinH); HelpWinH := 0;
  i := length(ptxt);
  if i > 255 then i := 255;
  byte(homedir[0]) := i; move(ptxt[0], homedir[1], i);
  freemem(ptxt); ptxt := NIL;
  if homedir[length(homedir)] <> '\' then homedir := homedir + '\';
  homedir := homedir + 'BunComp\';
  mkdir(homedir); while IOresult <> 0 do ;
  assign(stdout, homedir + 'stdout.txt');
  filemode := 1; rewrite(stdout); // write-only
  i := IOresult;
 end;
 if i <> 0 then begin
  txt := errortxt(i) + ' trying to write in own directory as well as ' + homedir + chr(0);
  MessageBoxA(0, @txt[1], NIL, MB_OK); halt;
 end;
 close(stdout); erase(stdout);

 // Initialise various variables.
 mv_ListBuffyHandle := 0; mv_MainWinH := 0; HelpWinH := 0;
 mv_ListH[1] := 0; mv_ContextMenu := 0; lastactiveview := $FF;
 funwinhandle := 0; mv_FunDIBhandle := 0; mv_FunBuffy := NIL;
 mv_AcceleratorTable := 0;
 dword(neutralcolor) := SwapEndian(GetSysColor(color_3Dface)) shr 8;

 GetClientRect(GetDesktopWindow, rr); // this gives the desktop resolution
 funsizex := rr.right div 3; funsizey := rr.bottom div 3;
 helpsizex := 512; helpsizey := 450;
 mv_Dlg.headr.style := dword(WS_CAPTION or WS_VISIBLE or DS_CENTER or DS_MODALFRAME or DS_NOIDLEMSG or WS_CLIPCHILDREN);
 mv_Dlg.headr.cdit := 0;
 mv_Dlg.headr.x := 0; mv_Dlg.headr.y := 0;
 mv_Dlg.headr.cx := dword((funsizex + 16) * 4) div (dword(GetDialogBaseUnits) and $FFFF);
 mv_Dlg.headr.cy := dword((funsizey + 84) * 8) div (dword(GetDialogBaseUnits) shr 16);
 fillbyte(mv_Dlg.data[0], length(mv_Dlg.data), 0);
 fillbyte(viewdata[0], length(viewdata) * sizeof(viewdata[0]), 0);

 acolor.r := $DD; acolor.g := $33; acolor.b := $FF; acolor.a := 0;
 fillbyte(option, sizeof(option), 0); option.colorspace := 1;
 option.dithering := 1; option.palsize := 256; option.maxcontrast := 1;
 pe_used := 0; compressorthreadID := 0; compressorthreadhandle := 0;
 mousescrolling := FALSE; colorpicking := FALSE; compressing := FALSE;
 batchprocess := FALSE;

 // BunComp is GO!
 SpawnMainWindow;
 mv_EndProgram := FALSE;

 // Grab the default settings file, if one exists.
 i := ReadIni(homedir + 'buncomp.ini');
 if i = 2 then begin
  // if one does not, create a new one with vanilla values!
  ClearPE(0, $FFFF);
  DrawMagicList;
  WriteIni(homedir + 'buncomp.ini');
 end;
end;

procedure MainLoop;
var winmsg : msg;
begin
 while (mv_EndProgram = FALSE) and (getmessage(@winmsg, 0, 0, 0))
 do begin
  if TranslateAccelerator(mv_MainWinH, mv_AcceleratorTable, winmsg) = 0
  then begin
   TranslateMessage(winmsg);
   DispatchMessage(winmsg);
  end;
 end;
end;

// ------------------------------------------------------------------

begin
 AddExitProc(@bunexit);
 setlength(pe, 256);

 {$ifdef allowLAB} labtable[0] := 0; {$endif}
 {$ifdef difftest} DiffTest; exit; {$endif}

 DoInits;
 MainLoop;

 PostQuitMessage(0);
end.
