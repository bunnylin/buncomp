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

// - Alpha in diffRGB etc must be premultiplied, otherwise a preset palette
//   item with a colored alpha may be ignored in favor of a solid black
// - Sierra lite dithering broken? when alpha present?
// - Paste to clipboard should use a fast PNG, with dib v5 only secondarily
// - Modularise the code -> image analysis / color reduction / ui modules
// - Source image hgram buckets should probably persist, and increase to 8k?
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
// - take more attractive screenshots for site
// TODO: there's another thing to do at the image rendering thing

{$mode fpc}
{$apptype GUI}
{$GOTO ON} // only used once and it improves code readability there :p
{$codepage UTF8}
{$asmmode intel}
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
    viewdata : array[0..16] of packed record
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
    flats : array of packed record // viewdata[0] flat color auto-detection
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
    mv_AMessage : msg;
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

    i, j : dword; // my favorite variables for general use
    ptxt : pchar;
    strutsi, homedir : string;

    option : record
      palsize : word; // target palette size
      maxcontrast, dithering, colorspace, flat_favor : byte;
    end;
    {$ifdef allowLAB}
    labtable : array[0..65535] of word;
    {$endif}

    // palette entries, both presets and algorithmically calculated go here
    pe : array of packed record
      colo : RGBquad;
      colog : RGBA64; // for the gamma-corrected values
      status : byte; // 0 free, 1 used, 2 used fixed, 3 detected flat
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

// PlusDTab is used as the pattern for a non-regular ordered dither.
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

 // Kill the worker thread
 if compressorthreadID <> 0 then begin
  WaitForThreadTerminate(compressorthreadID, 1000);
  i := KillThread(compressorthreadID);
  CloseHandle(compressorthreadhandle); // trying to avoid handle leaking
 end;

 // Destroy the views
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
 // Destroy the entertainer
 if funwinhandle <> 0 then DestroyWindow(funwinhandle);
 // Destroy the magic color list
 if mv_ListH[1] <> 0 then DestroyWindow(mv_ListH[1]);
 if mv_ListBuffyHandle <> 0 then begin
  SelectObject(mv_ListBuffyDC, mv_OldListBuffyHandle);
  DeleteDC(mv_ListBuffyDC);
  DeleteObject(mv_ListBuffyHandle);
 end;
 // Destroy the help window
 if HelpWinH <> 0 then DestroyWindow(HelpWinH);
 // Destroy the fun palette picture
 if mv_FunDIBhandle <> 0 then DeleteObject(mv_FunDIBhandle);
 // Destroy the main window
 if mv_MainWinH <> 0 then DestroyWindow(mv_MainWinH);

 // Destroy everything else
 if mv_ContextMenu <> 0 then DestroyMenu(mv_ContextMenu);

 // Free whatever other memory was reserved
 mcg_ForgetImage(@rendimu);
 mcg_ForgetImage(@tempbmp);

 // Release fonts
 if mv_FontH[1] <> 0 then deleteObject(mv_FontH[1]);
 if mv_FontH[2] <> 0 then deleteObject(mv_FontH[2]);

 // Print out the error message if exiting unnaturally
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

procedure outpal;
// Debugging function, prints the palette state into an attached console
var lix : word;
begin
 writeln('=== Palette state ===');
 for lix := 0 to option.palsize - 1 do begin
  if lix and 7 = 0 then write(lix:5,': ');
  case pe[lix].status of
    0: write('-------- ');
    1: write(lowercase(hexifycolor(pe[lix].colo) + strhex(pe[lix].colo.a)) + ' ');
    2: write(hexifycolor(pe[lix].colo) + strhex(pe[lix].colo.a) + ' ');
    3: write(hexifycolor(pe[lix].colo) + strhex(pe[lix].colo.a) + '!');
  end;
  if (lix and 7 = 7) or (lix + 1 = option.palsize) then writeln;
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
  pe[i].status := 0;
 end;
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

  if pe[pali].status = 0 then blah := 'Not set' else blah := hexifycolor(pe[pali].colo);
  TextOut(mv_ListBuffyDC, (magicx shr 2) + 8, mlp * (magicy shr 3) + 3, @blah[1], length(blah));
  if pe[pali].status <> 0 then begin
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
    avar : dword;
    rootsizex, rootsizey, xvar, yvar, pvar, qvar : word;
    aval : byte;
begin
 if (mv_FunBuffy = NIL) or (funsizex = 0) or (funsizey = 0) or (option.palsize = 0)
 then exit;

 // Calculate good table display dimensions
 rootsizex := 1;
 while rootsizex * rootsizex < option.palsize do inc(rootsizex);
 rootsizey := rootsizex;
 while (rootsizex - 1) * rootsizey >= option.palsize do dec(rootsizex);

 // Draw it
 funpoku := mv_FunBuffy; yvar := 0;
 while yvar < funsizey do begin
  xvar := 0;
  pvar := (yvar * rootsizey div funsizey) * rootsizex;
  while xvar < funsizex do begin
   qvar := pvar + (xvar * rootsizex) div funsizex;
   aval := pe[qvar].colo.a;
   // for pretend alpha, a black and white xor pattern!
   avar := ((xvar xor yvar) and $3E) shl 1 + $40;
   avar := mcg_GammaTab[avar] * (aval xor $FF);
   byte(funpoku^) := mcg_RevGammaTab[(mcg_GammaTab[pe[qvar].colo.b] * aval + avar) div 255];
   inc(funpoku);
   byte(funpoku^) := mcg_RevGammaTab[(mcg_GammaTab[pe[qvar].colo.g] * aval + avar) div 255];
   inc(funpoku);
   byte(funpoku^) := mcg_RevGammaTab[(mcg_GammaTab[pe[qvar].colo.r] * aval + avar) div 255];
   inc(funpoku, 2);
   inc(xvar);
  end;
  inc(yvar);
 end;

 InvalidateRect(funpal, NIL, FALSE);
end;

// ------------------------------------------------------------------

procedure GrabConfig;
begin
 // grab the configuration from the UI, if it exists
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
 for i := 0 to high(pe) do if pe[i].status <> 0 then
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
      pe[pe_used].status := 2;
      pe_used := (pe_used + 1) mod dword(length(pe));
     end;
   end;
  end;
 end;
 close(conff);
 if option.dithering in [0..6] = FALSE then option.dithering := 0;
 if option.colorspace in [0..2] = FALSE then option.colorspace := 0;
 pe_used := 0;

 // update the UI to reflect the selected options
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

// ------------------------------------------------------------------

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

{$ifdef allowLAB}
procedure BuildLabTable;
// Precalculates the results of f(t), t = [0..65535], as used in the
// XYZ to LAB colorspace transformation. The table is stored in LabTable[].
var i : word;
begin
 for i := 0 to 65535 do
  if i > 580
  then LabTable[i] := round(power(i / 65535, 1/3) * 65535)
  else LabTable[i] := round(841 * i / 108 + 9039);
end;
{$endif}

var diff : function(c1, c2 : RGBA64) : dword;

// Function Diff(c1, c2 : RGBA64) : dword;
// Returns absolute distance between two RGBA64 colors.

{$define !asmdiff} // the current asm versions are outdated and won't work

function diffRGB(c1, c2 : RGBA64) : dword;
// Returns the squared difference between the two RGBA64 colors.
// The calculation is: value + (value * value) div 4
// The output will be within [0..$40020000]
var r, g, b, a : dword;
begin
 r := abs(c1.r - c2.r);
 g := abs(c1.g - c2.g);
 b := abs(c1.b - c2.b);
 a := abs(c1.a - c2.a);
 diffRGB := r + g + b + a;
 r := r shr 2;
 g := g shr 2;
 b := b shr 2;
 a := a shr 2;
 inc(diffRGB, r * r + g * g + b * b + a * a);
end;

{$ifdef allowLAB}
function diffLAB(c1, c2 : dword) : dword;
// Returns the perceived difference between the two RGBquad colors.
// This converts the RGB into CIE XYZ, then to CIE LAB, which is
// an "approximately uniform color space." The function takes the difference
// between the LAB values of both colors, squares each, and sums them with
// extra weight together with a squared Alpha difference.
// Unfortunately, this looks awful... an implementation error, no doubt.
var X1, Y1, Z1, X2, Y2, Z2 : longint;
    L1, A1, B1, A2 : word;
begin
 // The standard transformation sRGB --> CIE XYZ is given by ITU-R BT.709
 // (the ratios seem to come from the 1931 CIE definition; 2 degrees, D65)
 // I adjusted them to have uniform maximums (multipliers sum to 1).
 //
 // X := 0.4339500 * r + 0.3762098 * g + 0.1898402 * b;
 // Y := 0.2126728 * r + 0.7151522 * g + 0.0721750 * b;
 // Z := 0.0177566 * r + 0.1094680 * g + 0.8727754 * b;
 //
 // function f(t : word) : word
 // if t > tmax * 216/24389 then f := (t/tmax) ^1/3 * tmax
 // else f := 841/108 * t + 4/29 * tmax;
 //
 // L := 116 * (f(Y) / ymax) - 16;
 // A := 500 * (f(X) - f(Y)) / xmax;
 // B := 200 * (f(Y) - f(Z)) / zmax;
 // ====================
 // 2013 remark: Bruce Lindbloom's discontinuity study of L* conversions
 // suggests an improved linear RGB to Lab algorithm.

 {$ifdef SingleColorLABTransform}
 // RGB are [0..255], adjust multipliers by 32768*65535/255 = 8421376
 X1 := (3654456 * RGBquad(c1).r + 3168204 * RGBquad(c1).g + 1598716 * RGBquad(c1).b) div 32768;
 Y1 := (1790998 * RGBquad(c1).r + 6022565 * RGBquad(c1).g + 607813 * RGBquad(c1).b) div 32768;
 Z1 := (149535 * RGBquad(c1).r + 921871 * RGBquad(c1).g + 7349970 * RGBquad(c1).b) div 32768;
 // XYZ are [0..65535]
 // the LabTable values have theoretical ranges of [9039..65535]
 L1 := (round(47513.6 * LabTable[Y1]) + 327675) div 655350 - 655;
 A1 := 4096 * (LabTable[X1] - LabTable[Y1]) div 13107 + 17655;
 B1 := 8192 * (LabTable[Y1] - LabTable[Z1]) div 65535 + 7062;
 // L is scaled from [0..100]    to [0..4096]
 // A is scaled from [-431..431] to [0..35310]
 // B is scaled from [-172..172] to [0..14124]
 writeln(hexifycolor(RGBquad(c1)), ' > L:', L1, '  A:', A1, '  B:', B1);
 {$endif}

 X1 := (3654456 * RGBquad(c1).r + 3168204 * RGBquad(c1).g + 1598716 * RGBquad(c1).b) div 32768;
 Y1 := (1790998 * RGBquad(c1).r + 6022565 * RGBquad(c1).g + 607813 * RGBquad(c1).b) div 32768;
 Z1 := (149535 * RGBquad(c1).r + 921871 * RGBquad(c1).g + 7349970 * RGBquad(c1).b) div 32768;

 X2 := (3654456 * RGBquad(c2).r + 3168204 * RGBquad(c2).g + 1598716 * RGBquad(c2).b) div 32768;
 Y2 := (1790998 * RGBquad(c2).r + 6022565 * RGBquad(c2).g + 607813 * RGBquad(c2).b) div 32768;
 Z2 := (149535 * RGBquad(c2).r + 921871 * RGBquad(c2).g + 7349970 * RGBquad(c2).b) div 32768;

 X1 := LabTable[X1] - LabTable[X2];
 Z1 := LabTable[Z2] - LabTable[Z1];
 Y1 := LabTable[Y1] - LabTable[Y2];

 // L1 := (round(47513.6 * abs(Y1)) + 327675) div 655350;
 asm
  mov eax, Y1
  cdq; xor eax, edx; sub eax, edx
  mov edx, 475136; mul edx; mov ecx, 0
  add eax, 3276750; adc edx, ecx
  mov ecx, 6553500; div ecx // EDX:EAX is too big for magic division...
  mov L1, ax
 end ['EAX', 'ECX', 'EDX'];
 A1 := 4096 * abs(X1 - Y1) div 13107;
 B1 := 8192 * abs(Y1 + Z1) div 65535;
 A2 := abs(RGBquad(c1).a - RGBquad(c2).a); // alpha, separately

 diffLAB := (L1 * L1 + A1 * A1 + B1 * B1) * 2 + A2 * A2 + 1;
 // theoretical maximum output is $AE6A0FAA
end;
{$endif}

// ::: DiffYCC :::
// The distance is calculated with perceptual weighting. The colors are
// broken from RGB color space into YCbCr, where Y is sort of greenish luma,
// and Cb and Cr are the delta from it to the red and blue components.
//
// The calculations are done with fixed point maths. This entails shifting
// numbers up somewhat, and doing digital rounding upon divisions. Digital
// rounding means adding half of the divisor to the dividee before dividing.
// For example: 15 div 4 = 3    but (15 + 2) div 4 = 4
//
// Finally, for the distance calculation, the components are weighed.
// 2 Y : 3/2 Cr : 1 Cb : 1 a (and afterwards, they are squared)
function diffYCC(c1, c2 : RGBA64) : dword;
var Y : longint;
    Cb, Cr : dword;
    aeon : word;
begin
 { RGB-to-YCbCr conversion: (ITU-R BT.709) }
 { (not using BT.2020 yet, too advanced)   }
 {                                         }
 { Kb = 0.0722 = 2366 / 32768              }
 { Kr = 0.2126 = 6966 / 32768              }
 {                                         }
 { Y' = 0.2126r + 0.7152g + 0.0722b        }
 { Cr = (r - Y') / 1.5748                  }
 { Cb = (b - Y') / 1.8556                  }

 // This is the optimised version, the comparison can be unified without
 // breaking the expression! Here I use (c1 - c2).
 // Y ranges [-7FFF8000..7FFF8000], scaled to [-FFFF00..FFFF00]
 Y := (6966 * (c1.r - c2.r)
    + 23436 * (c1.g - c2.g)
     + 2366 * (c1.b - c2.b)) div 128;
 // Cr is in 24-bit scale, to start with; div 1.5748 becomes *256/403.1488
 // and when the *256 is dropped, Cr ends in a 16-bit scale [0..FFFF].
 Cr := (abs(c2.r shl 8 - c1.r shl 8 + Y) + 201) div 403;
 // Cb likewise, div 1.8556 becomes *256/475.0336, scaling to [0..FFFF].
 Cb := (abs(c2.b shl 8 - c1.b shl 8 + Y) + 237) div 475;

 // Shift Y from 24- to 17-bit scale (16-bit * 2, actually)
 Y := (abs(Y) + 64) shr 7;
 // Make Cr 16-bit * 1.5
 inc(Cr, Cr shr 1);
 // Keep Cb at 16-bit * 1
 // And let's not forget poor old alpha, also at 16-bit * 1 weight.
 aeon := abs(c2.a - c1.a);

 // For debugging verification
 //writeln('RGBA Color1: ',hexifycolor(rgbquad(c1))+strhex(rgbquad(c1).a));
 //writeln('RGBA Color2: ',hexifycolor(rgbquad(c2))+strhex(rgbquad(c2).a));
 //write('Diff: Y ',Y,'  Cr ',Cr,'  Cb ',Cb,'  a ',aeon,'  total ');

 // Finally, calculate the difference-value itself
 // Numbers have to be squared, while trying hard not to overflow a dword,
 // without losing the lower end's granularity completely.
 diffYCC := Y + Cr + Cb + aeon; // nominal range of sum = [0..360443]
 Y := Y shr 2; // nominal range [0..32767], square 1 073 676 289
 Cr := Cr shr 2; // nominal range [0..24575], square 603 930 625
 Cb := Cb shr 2; // nominal range [0..16383], square 268 402 689
 aeon := aeon shr 2; // nominal range [0..16383], square 268 402 689
 inc(diffYCC, dword(Y * Y) + Cr * Cr + Cb * Cb + aeon * aeon);
 // Summed squares can nominally total up to 2 214 412 292.
 // With previous non-squared, the function's nominal output range becomes
 // [0..2 214 772 735] or [0..$8402BFFF].
 // In practice, the biggest output is $50017FFF, between black and white.
 // This means you might safely use the top bit for something else when
 // storing returned diff values.
end;

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
  // store the palette
  setlength(whither^.palette, length(bmpdata.palette));
  move(bmpdata.palette[0], whither^.palette[0], length(bmpdata.palette) * 4);
  // decide which bitdepth to pack into
  case length(bmpdata.palette) of
    0..2: whither^.bitdepth := 1;
    3..4: if bytealign = 1 then whither^.bitdepth := 2
          // v4 DIBs are DWORD -aligned, and don't support 2 bpp.
          else whither^.bitdepth := 4;
    5..16: whither^.bitdepth := 4;
    17..256: whither^.bitdepth := 8;
  end;
  // calculate various descriptive numbers
  dec(bytealign);
  whither^.sizex := (((bmpdata.sizex * whither^.bitdepth + 7) shr 3) + bytealign) and ($FFFFFFFF - bytealign);
  whither^.sizey := bmpdata.sizey;
  getmem(whither^.image, whither^.sizex * bmpdata.sizey);
  fillbyte(whither^.image^, whither^.sizex * bmpdata.sizey, 0);
  whither^.memformat := 4 + (alpha - 3);
  // match each pixel to the palette, store the indexes as the new image
  // svar is the source offset, zvar is the 29.3 fixed point target offset
  destofs := 0; srcofs := 0; bitptr := 8;
  if alpha = 4 then begin
   // if the source image is 32-bit RGBA, do this
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
    // All rows are padded to a full byte width
    if bitptr < 8 then begin
     bitptr := 8;
     inc(destofs);
    end;
    // Byte align to the required width, byte for PNGs, dword for BMPs
    destofs := (destofs + bytealign) and ($FFFFFFFF - bytealign);
   end;
  end else begin

   // if the source image is 24-bit RGB images, do this
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
    // All rows are padded to a full byte width
    if bitptr < 8 then begin
     bitptr := 8;
     inc(destofs);
    end;
    // Byte align to the required width, byte for PNGs, dword for BMPs
    destofs := (destofs + bytealign) and ($FFFFFFFF - bytealign);
   end;
  end;

 end

 // More than 256 colors
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

 // We have the filename, so prepare the file
 txt := openfilurec.lpstrfile;
 if upcase(copy(txt, length(txt) - 3, 4)) <> '.PNG' then txt := txt + '.png';
 assign(filu, txt);
 filemode := 1; rewrite(filu, 1); // write-only
 i := IOresult;
 if i <> 0 then begin
  txt := errortxt(i) + chr(0);
  MessageBoxA(viewdata[winpo].winhandu, @txt[1], NIL, MB_OK); exit;
 end;

 // Squash the image into the smallest uncompressed space possible
 fillbyte(newimu, sizeof(newimu), 0);
 PackView(winpo, 1, @newimu);
 newimu.sizex := viewdata[winpo].bmpdata.sizex; // use pixel, not byte width

 // Render the image into a compressed PNG
 pingustream := NIL;
 i := mcg_MemorytoPNG(@newimu, @pingustream, @j);
 if i <> 0 then begin
  mcg_ForgetImage(@newimu);
  txt := mcg_errortxt + chr(0);
  MessageBoxA(viewdata[winpo].winhandu, @txt[1], NIL, MB_OK); exit;
 end;

 // Write the PNG datastream into the file
 blockwrite(filu, pingustream^, j);
 i := IOresult;
 if i <> 0 then begin
  txt := errortxt(i) + chr(0);
  MessageBoxA(viewdata[winpo].winhandu, @txt[1], NIL, MB_OK);
 end;

 // Clean up
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
  // Allocate a system-wide memory chunk
  workhand := GlobalAlloc(GMEM_MOVEABLE, hedari.bv4Size + hedari.bv4ClrUsed * 4 + newimu.sizex * newimu.sizey);
  if workhand = 0 then begin
   txt := 'Could not allocate global memory.' + chr(0);
   MessageBoxA(viewdata[winpo].winhandu, @txt[1], NIL, MB_OK);
  end else begin
   // Stuff the memory chunk with goodies!
   tonne := GlobalLock(workhand);
   // first up: the bitmapinfoheader
   move((@hedari)^, tonne^, hedari.bv4Size);
   inc(tonne, hedari.bv4Size);
   // next up: the palette, if applicable
   if hedari.bv4ClrUsed <> 0 then begin
    move(newimu.palette[0], tonne^, hedari.bv4ClrUsed * 4);
    inc(tonne, hedari.bv4ClrUsed * 4);
   end;

   // last up: the image itself! Must be bottom-up, top-down doesn't seem to
   // work on the 9x clipboard
   if newimu.memformat = 1 then begin
    // 32-bit ABGR, must be converted to Windows' preferred BGRA
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
    // any other than 32-bit RGBA
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
  // Clean up
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
 // safety checks
 if (winpo > high(viewdata)) or (viewdata[winpo].bmpdata.image = NIL) then exit;
 if high(viewdata[winpo].bmpdata.palette) > high(pe) then begin
  txt := 'Cannot import: this image has more colors than the maximum palette size (' + strdec(length(pe)) + ').' + chr(0);
  MessageBoxA(viewdata[winpo].winhandu, @txt[1], NIL, MB_OK); exit;
 end;
 // clear the previous palette
 if high(viewdata[winpo].bmpdata.palette) < high(pe) then
  ClearPE(length(viewdata[winpo].bmpdata.palette), high(pe));
 // copy the view's histogram to a new active palette
 for mur := high(viewdata[winpo].bmpdata.palette) downto 0 do begin
  pe[mur].colo := viewdata[winpo].bmpdata.palette[mur];
  pe[mur].status := 2;
 end;
 // update the UI
 DrawMagicList;
 EnableWindow(mv_ButtonH[3], FALSE);
 colorpicking := FALSE;
 SendMessageA(mv_ButtonH[1], bm_setcheck, BST_UNCHECKED, 0);
 ShowWindow(mv_StaticH[7], SW_HIDE);
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
   wm_Size:
   with viewdata[winpo] do begin
    // read the new window size
    winsizex := word(lapu);
    winsizey := lapu shr 16;
    // adjust the view offset
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
    invalidaterect(window, NIL, TRUE);
   end;

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

   // Closing down
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
    // If all views are closed, disable the From Image button
    for winpo := 0 to high(viewdata) do
     if viewdata[winpo].buffyh <> 0 then exit;
    EnableWindow(mv_ButtonH[1], FALSE);
   end;

   // Default handler for every other message.
   else ViewProc := DefWindowProc(Window, AMex, wepu, lapu);
 end;
end;

procedure AddFlat(cola : dword; weight : byte);
// Helper routine for DetectFlats - adds a new flat color to the list, or
// adds weight to it if the particular color is already on the list.
var afi : dword;
begin
 afi := numflats;
 while afi <> 0 do begin
  dec(afi);
  if dword(flats[afi].color) = cola then begin
   inc(flats[afi].weight, weight);
   // overflow protection in case of huge images
   if flats[afi].weight and $80000000 <> 0 then dec(flats[afi].weight, 16);
   exit;
  end;
 end;

 if dword(length(flats)) = numflats then setlength(flats, length(flats) + 256);
 dword(flats[numflats].color) := cola;
 flats[numflats].weight := weight;
 inc(numflats);
end;

procedure DetectFlats;
// Looks for blocks of 3x3 or 4x4 pixels of the same color in bmpdata.image^
// of view 0. Each match adds points to flats[color].weight, and at the end
// the array is sorted in order of descending weights.
var ofsx, ofsy, cmpw1 : word;
    poku, poku2, poku3, poku4 : pointer;
    refcolor, cmpd1, cmpd2, cmpd3 : dword;
    match : byte;
begin
 setlength(flats, 0); numflats := 0;
 if (viewdata[0].bmpdata.image = NIL) or (viewdata[0].bmpdata.sizey < 4)
 or (viewdata[0].bmpdata.sizex < 4)
 then exit;

 setlength(flats, 512);

 ofsy := viewdata[0].bmpdata.sizey - 3;
 while ofsy <> 0 do begin
  dec(ofsy);
  ofsx := viewdata[0].bmpdata.sizex - 3;
  poku := viewdata[0].bmpdata.image;
  inc(poku, (ofsy * viewdata[0].bmpdata.sizex + ofsx) * viewdata[0].alpha);
  poku2 := poku; inc(poku2, viewdata[0].bmpdata.sizex * viewdata[0].alpha);
  poku3 := poku2; inc(poku3, viewdata[0].bmpdata.sizex * viewdata[0].alpha);
  poku4 := poku3; inc(poku4, viewdata[0].bmpdata.sizex * viewdata[0].alpha);
  if viewdata[0].alpha = 4 then begin
   // 32-bit source
   while ofsx <> 0 do begin
    dec(ofsx); dec(poku, 4); dec(poku2, 4); dec(poku3, 4); dec(poku4, 4);
    refcolor := dword(poku^);
    // 3x3 match?
    if (dword((poku + 4)^) = refcolor)
    and (dword((poku + 8)^) = refcolor)
    and (dword(poku2^) = refcolor)
    and (dword((poku2 + 4)^) = refcolor)
    and (dword((poku2 + 8)^) = refcolor)
    and (dword(poku3^) = refcolor)
    and (dword((poku3 + 4)^) = refcolor)
    and (dword((poku3 + 8)^) = refcolor)
    then begin
     match := 3;
     // 4x4 match?
     if (dword((poku + 12)^) <> refcolor)
     or (dword((poku2 + 12)^) <> refcolor)
     or (dword((poku3 + 12)^) <> refcolor)
     or (dword(poku4^) <> refcolor)
     or (dword((poku4 + 4)^) <> refcolor)
     or (dword((poku4 + 8)^) <> refcolor)
     or (dword((poku4 + 12)^) <> refcolor)
     then match := 1;
     addflat(refcolor, match);
    end;
   end;
  end else begin
   // 24-bit source
   while ofsx <> 0 do begin
    dec(ofsx); dec(poku, 3); dec(poku2, 3); dec(poku3, 3); dec(poku4, 3);
    refcolor := dword(poku^) and $FFFFFF;
    // 3x3 match?
    if (dword(poku2^) and $FFFFFF = refcolor)
    and (dword(poku3^) and $FFFFFF = refcolor)
    and (dword((poku + 3)^) and $FFFFFF = refcolor)
    and (dword((poku2 + 3)^) and $FFFFFF = refcolor)
    and (dword((poku3 + 3)^) and $FFFFFF = refcolor)
    and (dword((poku + 6)^) and $FFFFFF = refcolor)
    and (dword((poku2 + 6)^) and $FFFFFF = refcolor)
    and (dword((poku3 + 6)^) and $FFFFFF = refcolor)
    then begin
     // 4x4 match?
     match := 3;
     if (dword(poku4^) and $FFFFFF <> refcolor)
     or (dword((poku4 + 3)^) and $FFFFFF <> refcolor)
     or (dword((poku4 + 6)^) and $FFFFFF <> refcolor)
     or (dword((poku4 + 9)^) and $FFFFFF <> refcolor)
     or (dword((poku + 9)^) and $FFFFFF <> refcolor)
     or (dword((poku2 + 9)^) and $FFFFFF <> refcolor)
     or (dword((poku3 + 9)^) and $FFFFFF <> refcolor)
     then match := 1;
     addflat(refcolor or $FF000000, match);
    end;
   end;
  end;
 end;

 if numflats = 0 then exit;

 // Sort the list (teleporting gnome sort).
 cmpd1 := 0; cmpd2 := $FFFFFFFF;
 while cmpd1 < numflats do begin
  if (cmpd1 = 0) or (flats[cmpd1].weight <= flats[cmpd1 - 1].weight)
  then begin
   if cmpd2 <> $FFFFFFFF then cmpd1 := cmpd2 else inc(cmpd1);
   cmpd2 := $FFFFFFFF;
  end else begin
   cmpd2 := flats[cmpd1 - 1].weight; cmpd3 := dword(flats[cmpd1 - 1].color);
   flats[cmpd1 - 1] := flats[cmpd1];
   flats[cmpd1].weight := cmpd2; dword(flats[cmpd1].color) := cmpd3;
   cmpd2 := cmpd1; dec(cmpd1);
  end;
 end;

 // Penalise near-matches on the flats list.
 cmpd1 := 0;
 repeat
  cmpd2 := cmpd1 + 1;
  while cmpd2 < numflats do begin
   cmpd3 := diffRGB(mcg_GammaInput(flats[cmpd1].color), mcg_GammaInput(flats[cmpd2].color));
   case cmpd3 of
     0..15: match := 10;
     16..63: match := 9;
     64..255: match := 8;
     256..1023: match := 7;
     1024..4095: match := 6;
     4096..16383: match := 5;
     16384..65535: match := 4;
     65536..262143: match := 3;
     262144..1048575: match := 2;
     1048576..4194303: match := 1;
     else match := 0;
   end;
   flats[cmpd2].weight := flats[cmpd2].weight shr match + 1;
   inc(cmpd2);
  end;
  inc(cmpd1);
 until cmpd1 >= numflats;

 // Sort the list again.
 cmpd1 := 0; cmpd2 := $FFFFFFFF;
 while cmpd1 < numflats do begin
  if (cmpd1 = 0) or (flats[cmpd1].weight <= flats[cmpd1 - 1].weight)
  then begin
   if cmpd2 <> $FFFFFFFF then cmpd1 := cmpd2 else inc(cmpd1);
   cmpd2 := $FFFFFFFF;
  end else begin
   cmpd2 := flats[cmpd1 - 1].weight; cmpd3 := dword(flats[cmpd1 - 1].color);
   flats[cmpd1 - 1] := flats[cmpd1];
   flats[cmpd1].weight := cmpd2; dword(flats[cmpd1].color) := cmpd3;
   cmpd2 := cmpd1; dec(cmpd1);
  end;
 end;

 // Filter the noise off the flats list.
 cmpd1 := 0; cmpd2 := numflats;
 while cmpd2 <> 0 do begin
  dec(cmpd2);
  inc(cmpd1, flats[cmpd2].weight);
 end;
 cmpd2 := 0; while cmpd2 * cmpd2 * cmpd2 < cmpd1 do inc(cmpd2);
 cmpd3 := viewdata[0].bmpdata.sizex * viewdata[0].bmpdata.sizey;
 cmpw1 := 0; while cmpw1 * cmpw1 < cmpd3 do inc(cmpw1);
 cmpd3 := (cmpd2 * cmpw1) div 512;
 //writeln('sum weight = ',cmpd1,'  ^.333 = ',cmpd2,'  noise floor = ',cmpd3,' (currently ',numflats,' flats)');
 // Every flat on the list has its weight decreased by this amount.
 for cmpd1 := numflats - 1 downto 0 do
  if flats[cmpd1].weight <= cmpd3 then
   flats[cmpd1].weight := 0
  else
   dec(flats[cmpd1].weight, cmpd3);

 // Crop the list at the far end, all flats of 0 weight must go.
 while (numflats > 1) and (flats[numflats - 1].weight = 0) do dec(numflats);

 //for cmpd1 := 0 to numflats - 1 do
 // write(cmpd1:4,':',strhex(dword(flats[cmpd1].color)):8,' x',flats[cmpd1].weight:5);
 //writeln; writeln('== image size: ',viewdata[0].bmpdata.sizex,'x',viewdata[0].bmpdata.sizey);
end;

procedure MakeHistogram(sr : byte);
// Fills the viewdata[sr].bmpdata.palette array with a series of RGBA dwords,
// one for each unique color present in the image.
// Uses dynamic array hashing.
var iofs, hvar, i, j, gramsize : dword;
    hash : array[0..4095] of array of dword;
    bucketitems : array[0..4095] of dword;
    bitmask : dword;
    existence : boolean;
begin
 if (sr > high(viewdata)) or (viewdata[sr].bmpdata.image = NIL) then exit;
 // If a palette already exists, this proc will not recalculate it. If you
 // want to force a recalculation, SetLength(.bmpdata.palette, 0) first.
 if length(viewdata[sr].bmpdata.palette) <> 0 then exit;

 gramsize := 0;
 filldword(bucketitems, 4096, 0);

 // Each 32-bit color (24-bit images are read as 32-bit) is read into HVAR,
 // then reduced to a 12-bit ID tag, placed in j. There are 4096 hashing
 // buckets, and each has a dynamic array list of the actual 32-bit colors
 // encountered whose ID tag pointed to that bucket. Doing this means that
 // checking for whether a particular color is already added to the list only
 // requires up to a few dozen comparisons in its bucket's list.

 bitmask := 0; if viewdata[sr].alpha = 3 then bitmask := $FF000000;
 iofs := viewdata[sr].bmpdata.sizex * viewdata[sr].bmpdata.sizey * viewdata[sr].alpha;
 while iofs <> 0 do begin
  dec(iofs, viewdata[sr].alpha);
  hvar := dword((viewdata[sr].bmpdata.image + iofs)^) or bitmask;
  j := (hvar and $7FF) xor (hvar shr 11);
  j := (j xor (j shr 11)) and $FFF;
  if bucketitems[j] = 0 then begin // empty bucket? allocate space
   setlength(hash[j], 64);
   bucketitems[j] := 1;
   hash[j][0] := hvar;
   inc(gramsize);
  end else begin // non-empty bucket; check for a match among listed colors
   existence := FALSE;
   i := bucketitems[j];
   while i <> 0 do begin
    dec(i);
    if hash[j][i] = hvar then begin existence := TRUE; break; end;
   end;
   if existence = FALSE then begin // no match exists! add new to bucket
    if bucketitems[j] = dword(length(hash[j])) then setlength(hash[j], length(hash[j]) + 64);
    hash[j][bucketitems[j]] := hvar;
    inc(bucketitems[j]);
    inc(gramsize);
   end;
  end;
 end;

 // Shift the color list into viewdata:
 // Go through all 4096 buckets, and sequentially dump the color list array
 // contents from each into the viewdata gram.
 setlength(viewdata[sr].bmpdata.palette, gramsize);
 iofs := 4096; hvar := 0;
 while iofs <> 0 do begin
  dec(iofs);
  if bucketitems[iofs] <> 0 then begin
   for i := 0 to bucketitems[iofs] - 1 do begin
    dword(viewdata[sr].bmpdata.palette[hvar]) := hash[iofs][i];
    inc(hvar);
   end;
  end;
 end;
end;

procedure RedrawView(sr : byte);
// Renders the raw bitmap into a buffer that the system can display.
var acolorg : RGBA64;
    sofs, dofs : dword;
    aval : byte;
begin
 if (sr > high(viewdata)) or (viewdata[sr].bmpdata.image = NIL) then exit;

 acolorg := mcg_GammaInput(acolor);

 with viewdata[sr] do begin
  // The DIBitmap that is designated as our output buffer must have rows that
  // have a length in bytes divisible by 4. Happily, it is a 32-bit RGBx DIB
  // so this is not a problem.

  sofs := bmpdata.sizex * bmpdata.sizey;
  // 24-bit RGB rendering
  {$note TODO: These should use direct ptr access}
  if alpha = 3 then begin
   dofs := sofs * 4;
   sofs := sofs * 3;
   while sofs <> 0 do begin
    dec(dofs, 4); dec(sofs, 3);
    dword((buffy + dofs)^) := dword((bmpdata.image + sofs)^);
    byte((buffy + dofs + 3)^) := 0; // alpha, zeroed
   end;
  end
  // 32-bit RGBA rendering, alpha rendering using RGBquad "acolor".
  // Alpha is calculated linearry in a gamma-adjusted colorspace.
  else begin
   sofs := sofs * 4;
   while sofs <> 0 do begin
    dec(sofs, 4);
    dofs := dword((bmpdata.image + sofs)^);
    aval := byte(dofs shr 24);
    byte((buffy + sofs    )^) := mcg_RevGammaTab[(mcg_GammaTab[byte(dofs       )] * aval + acolorg.b * (aval xor $FF)) div 255];
    byte((buffy + sofs + 1)^) := mcg_RevGammaTab[(mcg_GammaTab[byte(dofs shr  8)] * aval + acolorg.g * (aval xor $FF)) div 255];
    byte((buffy + sofs + 2)^) := mcg_RevGammaTab[(mcg_GammaTab[byte(dofs shr 16)] * aval + acolorg.r * (aval xor $FF)) div 255];
    byte((buffy + sofs + 3)^) := aval;
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
  // Set up the new view window
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

// --------------------------------------------------------------------------
// The color compression algorithm
//
// New ideas:
// - every pe whose sphere of influence reaches an outermost color may only
//   choose between the outermost colors when optimising its position
// - outermost colors should probably be marked as such during hgram creation
//   so any color ...?

// Working variables
var wgram : array of packed record
      color : RGBA64;
      pal : word;
    end;
    dithertab : array of packed record
      pal1, pal2 : word;
      mix : byte;
    end;
    offenders : array of packed record
      who : dword; // wgram index of biggest error mapped to its pal entry
      what : dword; // magnitude of deviation
    end;
    totalerror, lasttotalerror : qword;
    palusize, faktor : word;

procedure Error_Calc;
// Map every histogram color to a palette entry. Each mapping has a degree of
// error between the palette color and the real color. Each real color with
// the greatest deviation from the palette entry it is mapped to, is stored
// in the OFFENDERS list.
var i, j, k, l : dword;
begin
 filldword(offenders[0].who, faktor * 2, 0);
 for i := high(wgram) downto 0 do begin
  // map wgram to palette
  k := $FFFFFFFF; // k will be the lowest difference
  for j := high(pe) downto 0 do
  if pe[j].status <> 0 then begin
   l := diff(pe[j].colog, wgram[i].color);
   if l < k then begin
    k := l; wgram[i].pal := j; // new 1st place holder
   end;
  end;
  // The wgram color [i] has been mapped to a palette entry, on deviation
  // k. The next closest palette entry had deviation MVAR.

  // During this pass, FAKTOR new palette entries will be made. Therefore,
  // keep a FAKTOR-length list "OFFENDERS" about the biggest color deviates.
  // OFFENDERS[0..faktor - 1] is ordered from smallest to greatest deviation.
  if k > offenders[0].what then begin
   if offenders[faktor - 1].what = 0 then begin
    offenders[faktor - 1].what := k; offenders[faktor - 1].who := i;
   end else begin
    // Scan from the top of the list until same palette or lower error found.
    j := faktor; l := 0;
    while j <> 0 do begin
     dec(j);
     if wgram[offenders[j].who].pal = wgram[i].pal then begin l := 1; break; end;
     if offenders[j].what < k then begin l := 2; break; end;
    end;
    if l = 1 then begin // same palette was encountered!
     // if the existing offender, mapped to the same palette, has less error
     // than the new one, the old can be overwritten by the new. Otherwise
     // the new one can be scrapped right out.
     if offenders[j].what < k then begin
      offenders[j].what := k; offenders[j].who := i;
     end;
    end else begin // lower error was encountered at offenders[j].what!
     // scan down from j to 0 to see if the same palette is somewhere
     // there... if it is, it gets bumped out and everything between it and
     // j is shifted down by one slot. If it is not, then everything
     // between 0 and j is shifted down by one slot.
     l := j;
     while l <> 0 do begin
      dec(l);
      if offenders[l].who = i then break;
     end;
     while l < j do begin
      offenders[l].who := offenders[l + 1].who;
      offenders[l].what := offenders[l + 1].what;
      inc(l);
     end;
     offenders[j].who := i; offenders[j].what := k;
    end;
   end;
  end;
 end;

 // Check if any of the OFFENDERS are very close to each other. Sometimes
 // two high-deviation colors may be right next to each other, but on
 // different sides of a palette-mapping boundary. In such cases, scrap the
 // one that is lower on the list.
 i := faktor;
 while i > 1 do begin
  dec(i);
  j := i;
  while j <> 0 do begin
   dec(j);
   if diff(wgram[offenders[i].who].color, wgram[offenders[j].who].color)
    < offenders[j].what
   then begin
    for k := j to faktor - 2 do begin
     offenders[k].who := offenders[k + 1].who;
     offenders[k].what := offenders[k + 1].what;
    end;
    dec(i); dec(faktor);
   end;
  end;
 end;
end;

procedure Mean_Reloc;
// This shakes the palette up, reducing the total error of all allocations.
// First it maps all wgram colors to the palette entries. Then, any
// non-predefined palette entry without a single mapped color is released for
// reassigning. All other non-preset palette entries are moved to the average
// location of the colors mapped to that entry. Centering a palette entry in
// relation to its own colors is meant to minimise the distance from the
// palette color to everything mapped to it. As the palette entries shift
// around, some wgram colors get remapped.
// Mean relocation is repeated until hardly any remapping occurs.
var i, j, k, l, wptr, remapped : dword;
begin
 repeat
  totalerror := 0; remapped := 0;
  for i := high(pe) downto 0 do filldword(pe[i].rstack, 9, 0);

  for wptr := high(wgram) downto 0 do begin
   // Find the palette entry closest to each wgram color.
   j := $FFFFFFFF; l := 0;
   for i := high(pe) downto 0 do if pe[i].status <> 0 then begin
    k := diff(pe[i].colog, wgram[wptr].color);
    if k < j then begin
     j := k; l := i;
    end;
   end;
   // Add the color to the averaging stack of that palette entry.
   inc(pe[l].rstack, wgram[wptr].color.r);
   inc(pe[l].gstack, wgram[wptr].color.g);
   inc(pe[l].bstack, wgram[wptr].color.b);
   inc(pe[l].astack, wgram[wptr].color.a);
   inc(pe[l].matches);
   // Track if palette mapping changed.
   if wgram[wptr].pal <> l then begin
    wgram[wptr].pal := l;
    inc(remapped);
   end;
   // Track the total error.
   inc(totalerror, j);
  end;

  // For all palette entries that were set during CompressColors...
  for i := high(pe) downto 0 do
   if pe[i].status = 1 then
    if pe[i].matches = 0 then begin
     // If no wgram matches, release the palette entry.
     pe[i].status := 0;
     dword(pe[i].colo) := dword(neutralcolor);
     dec(palusize);
    end else begin
     // Recenter palette entries at the average location of their mapped
     // colors.
     j := pe[i].matches shr 1;
     pe[i].colog.r := (pe[i].rstack + j) div pe[i].matches;
     pe[i].colog.g := (pe[i].gstack + j) div pe[i].matches;
     pe[i].colog.b := (pe[i].bstack + j) div pe[i].matches;
     pe[i].colog.a := (pe[i].astack + j) div pe[i].matches;
     pe[i].colo := mcg_GammaOutput(pe[i].colog);
    end;

  updatefun := TRUE;
 until (longint(remapped * remapped shl 2) <= length(wgram) * ((option.palsize - palusize) + 1))
    or (compressing = FALSE);
end;

function CompressColors(turhuus : pointer) : ptrint;
// Takes viewdata[0] as source, and builds a new palette that closely matches
// the full-color image. The procedure then calculates a dithering table, and
// renders the original image into the next free viewdata-slot using the
// calculated palette and dithering.
// The input pointer "turhuus" does not do much, but is apparently required
// to be able to run this as a thread... :? The output ptrint too.
var i, j, k, wptr : dword;
    palu : array of dword;
    palug : array of RGBA64;
    diffuselist : array of dword;
    diffusecount : dword;
    palptr : word;
    palumiss : boolean;
    tempcolor : RGBA64;
    x, y, z, alf : longint;
    wassup : string;
label JustRender;
begin
 CompressColors := 0;
 if viewdata[0].bmpdata.image = NIL then begin
  SendMessageA(funwinhandle, WM_CLOSE, 0, 0);
  exit;
 end;
 // remain unobtrusive, humility is key to user satisfaction
 threadsetpriority(compressorthreadID, THREAD_PRIORITY_BELOW_NORMAL);
 sleep(50);
 if compressing = FALSE then exit;

 // Prepare the working variables.
 setlength(palu, option.palsize);
 palusize := 0; j := 0;
 for i := high(pe) downto 0 do
  if pe[i].status = 2 then begin
   if i >= option.palsize then inc(j);
   if palusize < option.palsize then begin
    palu[palusize] := dword(pe[i].colo);
    pe[i].colog := mcg_GammaInput(pe[i].colo);
    inc(palusize);
   end;
  end;
 if j <> 0 then begin
  wassup := 'You have ' + strdec(j) + ' pre-defined palette entries above the desired palette size. They may not be included in the processed image.' + chr(13) + 'Proceed anyway?' + chr(0);
  i := MessageBoxA(0, @wassup[1], 'Caution' + chr(0), MB_OKCANCEL or MB_TASKMODAL);
  if i = IDCANCEL then begin
   SendMessageA(funwinhandle, WM_CLOSE, 0, 0);
   exit;
  end;
 end;

 // Select the appropriate colorspace to work in.
 case option.colorspace of
   1: diff := @diffYCC;
   {$ifdef allowLAB}
   2: begin
       diff := @diffLAB; // this does not look pretty
       if LabTable[0] = 0 then BuildLabTable;
      end;
   {$endif}
   else diff := @diffRGB;
 end;

 // Add auto-detected flat colors to presets.
 if (option.flat_favor <> 0) and (numflats <> 0) then begin
  i := 0;
  while (i < numflats) and (palusize < option.palsize) do begin
   j := length(pe);
   while j <> 0 do begin
    dec(j);
    if (pe[j].status <> 0) and (dword(pe[j].colo) = dword(flats[i].color))
    then break;
   end;
   if dword(pe[j].colo) <> dword(flats[i].color) then begin
    j := 0;
    while pe[j].status <> 0 do inc(j);
    pe[j].status := 3;
    pe[j].colo := flats[i].color;
    pe[j].colog := mcg_GammaInput(flats[i].color);
    palu[palusize] := dword(flats[i].color);
    inc(palusize);
   end;
   inc(i);
  end;
 end;

 // PALU now contains all preset palette entries, and all detected flats that
 // could be fit in. The values in PALU[] are 32-bit RGBA.
 // Additionally, all PE[].colo have been gamma-corrected into PE[].colog.

 updatefun := TRUE;

 if compressing = FALSE then exit;

 // Reserve memory.
 setlength(offenders, (option.palsize shr 3) + 1);
 setlength(palu, palusize);
 setlength(palug, palusize);
 setlength(wgram, length(viewdata[0].bmpdata.palette) + palusize);
 wptr := 0;

 // The original palette must be copied into WGRAM, while doing some checks.
 // 1. Keep a list of preset palette entries in PALU. Compare all PALU items
 //    to each histogram entry, and remove matching ones from PALU. At the
 //    end, PALU only has those preset palette entries with no histogram hit.
 //    New histogram entries must be added to WGRAM for all remaining PALU.
 // 2. Check if the lightness of each histogram entry falls under the
 //    darkness bias threshold. If it does, apply the DBMASK to get
 //    a quantised DARKCOLOR. Check the DARKLIST for matches. If no match,
 //    add the DARKCOLOR to DARKLIST, and to WGRAM instead of the real color.
 //    If the real color was a preset PALU hit, add that to WGRAM too.

 for i := high(viewdata[0].bmpdata.palette) downto 0 do begin
  // check for PALU match
  palumiss := TRUE;
  j := palusize;
  while (j <> 0) and (palumiss) do begin
   dec(j);
   if palu[j] = dword(viewdata[0].bmpdata.palette[i]) then palumiss := FALSE;
  end;
  if palumiss = FALSE then begin
   // found a match! Remove that from PALU list and add it to the WorkingGRAM
   // with gamma correction
   wgram[wptr].color := mcg_GammaInput(viewdata[0].bmpdata.palette[i]);
   inc(wptr);
   dec(palusize);
   while j < palusize do begin
    palu[j] := palu[j + 1];
    inc(j);
   end;
  end;

  // add color to wgram w/gamma
  wgram[wptr].color := mcg_GammaInput(viewdata[0].bmpdata.palette[i]);
  inc(wptr);
 end;

 // Add remaining PALU to WGRAM.
 setlength(wgram, wptr + palusize);
 while palusize <> 0 do begin
  dec(palusize);
  wgram[wptr].color := mcg_GammaInput(RGBquad(palu[palusize]));
  inc(wptr);
 end;
 if compressing = FALSE then exit;

 // Distribute evenly around up to half of total desired palette.
 // Re-prep the palette array to check for double definitions.
 palusize := 0;
 for i := option.palsize - 1 downto 0 do
  if (pe[i].status <> 0) then begin
   palug[palusize] := pe[i].colog;
   inc(palusize);
  end;
 palptr := palusize mod option.palsize;

 if option.palsize - palusize = 0 then goto JustRender;

 // Initially place up to half of the free palette at evenly spaced values!
 // At minimum we must place one spot in every corner of the 3D RGB cube, or
 // 8 points. Just ignore alpha at this point, it's less important than the
 // actual colors.
 // option.palsize - palusize = free slots on the palette
 // i = 1 --> 2^3 = 8 points to place (place only if 16+ free slots)
 //     2 --> 3^3 = 27 points to place (place only if 54+ free slots)
 //     3 --> 4^3 = 64 points to place (place only if 128+ free slots) ...
 i := 2;
 while (i * i * i) shl 1 <= option.palsize - palusize do inc(i);
 dec(i, 2);

 // If the target palette size is too small for initial spot placement, and
 // no palette entries were predefined, then at least plop one initial one
 // right on the first pixel in the wgram. It'll get shaken to a better
 // position during mean_reloc.
 if (i = 0) and (palusize = 0) then begin
  pe[0].colog := wgram[0].color;
  pe[0].colo := mcg_GammaOutput(wgram[0].color);
  pe[0].status := 1;
  inc(palptr); inc(palusize);
 end;

 // Place the points; check first that no point was in the preset palette.
 if i <> 0 then begin
  for x := 0 to i do
  for y := 0 to i do
  for z := 0 to i do begin
   // Get the next free slot in the palette...
   while pe[palptr].status <> 0 do palptr := (palptr + 1) mod option.palsize;
   // Calculate the point's color...
   pe[palptr].colog.r := x * $FFFF div longint(i);
   pe[palptr].colog.g := y * $FFFF div longint(i);
   pe[palptr].colog.b := z * $FFFF div longint(i);
   pe[palptr].colog.a := $FFFF;
   // Scan the preset colors for a match...
   j := length(palu); palumiss := TRUE;
   while (j <> 0) and (palumiss) do begin
    dec(j);
    if qword(palug[j]) = qword(pe[palptr].colog) then palumiss := FALSE;
   end;
   if palumiss then begin
    // No such color in the preset palette!
    pe[palptr].status := 1;
    inc(palusize);
   end;
  end;
 end;

 // Shake the palette up a bit to start with, eliminate any matchless ones.
 sleep(50);
 if compressing = FALSE then exit;
 wassup := 'Mean relocation... (' + strdec(palusize) + ')' + chr(0);
 SendMessageA(funstatus, WM_SETTEXT, 0, ptrint(@wassup[1]));
 mean_reloc;

 // Main color compression loop!
 while (palusize < option.palsize) and (compressing) do begin
  sleep(0);
  // Calculate the number of new palette entries to set during this loop.
  faktor := ((option.palsize - palusize) shr 3) + 1;
  if faktor > palusize shr 1 then faktor := (palusize shr 1) + 1;
  // Map wgram to the existing palette, see where the biggest error is.
  wassup := 'Scoring deviation... (' + strdec(palusize) + ')' + chr(0);
  SendMessageA(funstatus, WM_SETTEXT, 0, ptrint(@wassup[1]));
  error_calc;

  //writeln; writeln('=== Allocating ===');
  // No colors left to allocate, but still space in palette? Call it a day.
  if offenders[faktor - 1].what <= 1 then break;
  // Allocate the new palette entries in the biggest error locations.
  for i := faktor - 1 downto 0 do begin
   while pe[palptr].status <> 0 do palptr := (palptr + 1) mod option.palsize;
   pe[palptr].colog := wgram[offenders[i].who].color;
   pe[palptr].colo := mcg_GammaOutput(wgram[offenders[i].who].color);
   pe[palptr].status := 1;
   inc(palusize);
  end;

  // Shake the new palette to represent colors optimally.
  wassup := 'Mean relocation... (' + strdec(palusize) + ')' + chr(0);
  SendMessageA(funstatus, WM_SETTEXT, 0, ptrint(@wassup[1]));
  sleep(0);
  mean_reloc;
 end;

 // This section does improve color allocation somewhat, by re-allocating
 // every palette entry one by one and seeing if it could be placed in
 // a location that would reduce total error. Unfortunately, it is very slow.
 // This could be optimised by being discriminating about which PE's to
 // attempt to re-allocate, for example only picking ones that have other
 // PE's as close neighbors (even though that shouldn't be a common state.)
 //
 // I think it might be best to rewrite the CompressColors procedure to
 // allocate everything through this least-total-error strategy, while
 // making sure to figure in benefits from dithering. When dithering, palette
 // entries should be pushed to far boundaries to preserve contrast, since
 // intermediate colors are handled by the dithering. The current algorithm
 // assumes the result will use flat rendering, so mean_reloc tends to shift
 // palette entries into the intermediate areas, thus losing contrast.
 //
 // Hmm. Treat pe pairs as lines instead of discrete points?

 {$define !postopop}
 {$ifdef postopop}
 // Post-operation optimisation
 if palusize = option.palsize then begin
  wassup := 'Optimising...' + chr(0);
  SendMessageA(funstatus, WM_SETTEXT, 0, ptrint(@wassup[1]));

  // Remember the current palette and its total error
  setlength(palu, length(pe));
  setlength(palug, length(pe));
  lasttotalerror := totalerror;
  for i := high(pe) downto 0 do begin
   palu[i] := dword(pe[i].colo);
   palug[i] := pe[i].colog;
  end;
  writeln('Initial total error: ',totalerror);

  k := 0; palumiss := FALSE; faktor := 1;
  repeat

   // try this for all non-preset palette entries
   i := option.palsize;
   while (i <> 0) and (palumiss = FALSE) do begin
    dec(i);
    if k = i then palumiss := TRUE else
    if pe[i].status = 1 then begin

     // release the palette entry
     pe[i].status := 0;
     mean_reloc;

     // reallocate it!
     error_calc;
     pe[i].colog := wgram[offenders[0].who].color;
     pe[i].colo := mcg_GammaOutput(wgram[offenders[0].who].color);
     pe[i].status := 1;
     mean_reloc;

     // was it an improvement?
     if totalerror < lasttotalerror then begin
      writeln(totalerror);
      // Yes! Save the new palette
      lasttotalerror := totalerror;
      for j := high(pe) downto 0 do begin
       palu[j] := dword(pe[j].colo);
       palug[j] := pe[j].colog;
      end;
      k := i;
     end else begin
      // No! Restore the old palette
      for j := high(pe) downto 0 do begin
       dword(pe[j].colo) := palu[j];
       pe[j].colog := palug[j];
      end;
     end;

    end;
   end;
  until palumiss;

 end;
 writeln('Final error score: ',lasttotalerror);
 {$endif}

 // Now to render, through the power of dithering!
 // Lots of useful information on this at Libcaca: http://caca.zoy.org/study/
 JustRender:
 wassup := 'Rendering...' + chr(0);
 SendMessageA(funstatus, WM_SETTEXT, 0, ptrint(@wassup[1]));

 if option.dithering = 4 then begin
  // Error-diffusive dithering - calculate best dither match per pixel.
  // This uses the Sierra Lite algorithm, in serpentine order.
  // Set up a bitmap to render the result in...
  mcg_ForgetImage(@rendimu);
  rendimu.sizex := viewdata[0].bmpdata.sizex;
  rendimu.sizey := viewdata[0].bmpdata.sizey;
  rendimu.memformat := viewdata[0].alpha - 3;
  rendimu.bitdepth := 8;
  getmem(rendimu.image, viewdata[0].bmpdata.sizex * viewdata[0].bmpdata.sizey * viewdata[0].alpha);

  // PALU is the diffusion buffer, wraps around using AND k
  // It has room for 3 rows: 2 headroom pixels + width pixels + 2 footer px
  // and each pixel is represented by four longint values, one per channel.
  i := (rendimu.sizex + 4) * 4 * 3;
  k := 1; while k < i do k := k shl 1;
  setlength(palu, k); filldword(palu[0], k, 0);
  dec(k);

  // Offenders[0] and [1] are temp variables for finding closest pal match.
  diffusecount := 0;
  setlength(offenders, 2);
  // Diffuselist is used to shuffle the processing order of pixels in each
  // row.
  setlength(diffuselist, viewdata[0].bmpdata.sizex);
  for palusize := viewdata[0].bmpdata.sizex - 1 downto 0 do
   diffuselist[palusize] := palusize;
  // Process the image, top-down, alternating L-to-R and R-to-L.
  for faktor := 0 to viewdata[0].bmpdata.sizey - 1 do begin

   if faktor and 7 = 0 then begin
    wassup := 'Rendering... ' + strdec(viewdata[0].bmpdata.sizey - faktor) + chr(0);
    SendMessageA(funstatus, WM_SETTEXT, 0, ptrint(@wassup[1]));
   end;

   // Rearrange the horizontal processing order.
   if diffuselist[0] = 0 then begin
    for palusize := viewdata[0].bmpdata.sizex - 1 downto 0 do
     diffuselist[palusize] := viewdata[0].bmpdata.sizex - 1 - palusize;
   end else
    for palusize := viewdata[0].bmpdata.sizex - 1 downto 0 do
     diffuselist[palusize] := palusize;

   for palusize := 0 to viewdata[0].bmpdata.sizex - 1 do begin
    // Apply diffusion mods to current pixel...
    i := (diffusecount + diffuselist[palusize] * 4 + 8) and k;
    wptr := faktor * viewdata[0].bmpdata.sizex + diffuselist[palusize];
    if viewdata[0].alpha = 3 then begin
     // 24-bit
     x := round(longint(palu[i]) / 4) + mcg_GammaTab[RGBarray(viewdata[0].bmpdata.image^)[wptr].r];
     if x < 0 then tempcolor.r := 0 else if x > 65535 then tempcolor.r := 65535 else tempcolor.r := word(x);
     x := round(longint(palu[i + 1]) / 4) + mcg_GammaTab[RGBarray(viewdata[0].bmpdata.image^)[wptr].g];
     if x < 0 then tempcolor.g := 0 else if x > 65535 then tempcolor.g := 65535 else tempcolor.g := word(x);
     x := round(longint(palu[i + 2]) / 4) + mcg_GammaTab[RGBarray(viewdata[0].bmpdata.image^)[wptr].b];
     if x < 0 then tempcolor.b := 0 else if x > 65535 then tempcolor.b := 65535 else tempcolor.b := word(x);
     tempcolor.a := $FF;
    end else begin
     // 32-bit
     tempcolor := mcg_GammaInput(RGBAarray(viewdata[0].bmpdata.image^)[wptr]);
     x := round(longint(palu[i]) / 4) + tempcolor.r;
     if x < 0 then tempcolor.r := 0 else if x > 65535 then tempcolor.r := 65535 else tempcolor.r := word(x);
     x := round(longint(palu[i + 1]) / 4) + tempcolor.g;
     if x < 0 then tempcolor.g := 0 else if x > 65535 then tempcolor.g := 65535 else tempcolor.g := word(x);
     x := round(longint(palu[i + 2]) / 4) + tempcolor.b;
     if x < 0 then tempcolor.b := 0 else if x > 65535 then tempcolor.b := 65535 else tempcolor.b := word(x);
     x := round(longint(palu[i + 3]) / 4) + tempcolor.a;
     if x < 0 then tempcolor.a := 0 else if x > 65535 then tempcolor.a := 65535 else tempcolor.a := word(x);
    end;
    // Tempcolor is now the modded current pixel.
    // Clear the processed spot in the diffusion buffer, for next cycle use.
    filldword(palu[i], 4, 0);
    // Find the closest palette entry.
    // Offenders[0].who tracks the closest match, [0].what tracks its error.
    offenders[0].what := $FFFFFFFF;
    palptr := option.palsize;
    while palptr <> 0 do begin
     dec(palptr);
     offenders[1].what := diff(tempcolor, pe[palptr].colog);
     if offenders[1].what < offenders[0].what then begin
      offenders[0].who := palptr; offenders[0].what := offenders[1].what;
     end;
    end;
    palptr := offenders[0].who;
    // Plot the pixel with the matched palette color.
    if viewdata[0].alpha = 3 then begin
     RGBarray(rendimu.image^)[wptr].b := pe[palptr].colo.b;
     RGBarray(rendimu.image^)[wptr].g := pe[palptr].colo.g;
     RGBarray(rendimu.image^)[wptr].r := pe[palptr].colo.r;
    end else
     dword((rendimu.image + wptr)^) := dword(pe[palptr].colo);
    // Calculate the per-channel error.
    x := tempcolor.r - pe[palptr].colog.r;
    y := tempcolor.g - pe[palptr].colog.g;
    z := tempcolor.b - pe[palptr].colog.b;
    alf := tempcolor.a - pe[palptr].colog.a;
    // Stuff the error into PALU to diffuse it.
    i := (diffusecount + diffuselist[palusize] * 4 + 4) and k; // -1x
    if diffuselist[0] = 0 then i := (i + 8) and k; // or +1x
    longint(palu[i]) := longint(palu[i]) + x * 2; inc(i);
    longint(palu[i]) := longint(palu[i]) + y * 2; inc(i);
    longint(palu[i]) := longint(palu[i]) + z * 2; inc(i);
    longint(palu[i]) := longint(palu[i]) + alf * 2; inc(i);
    if diffuselist[0] <> 0 then i := (i + 12) and k;
    // -1x, +1y (or +0x, +1y if in reverse mode)
    j := (i + viewdata[0].bmpdata.sizex * 4 + 4) and k;
    longint(palu[j]) := longint(palu[j]) + x; inc(j);
    longint(palu[j]) := longint(palu[j]) + y; inc(j);
    longint(palu[j]) := longint(palu[j]) + z; inc(j);
    longint(palu[j]) := longint(palu[j]) + alf; inc(j);
    j := j and k; // step right
    longint(palu[j]) := longint(palu[j]) + x; inc(j);
    longint(palu[j]) := longint(palu[j]) + y; inc(j);
    longint(palu[j]) := longint(palu[j]) + z; inc(j);
    longint(palu[j]) := longint(palu[j]) + alf;
   end;
   diffusecount := (diffusecount + viewdata[0].bmpdata.sizex * 4 + 16) and k;
  end;
 end
 else begin
  // Ordered dithering types - cache a dithering table for speed

  // Calculate histogram dithering values!
  // At the same time, make a hash table for the histogram, put it in PALU.
  // Each 32-bit RGBA color in the real gram is reduced to a hash ID, which
  // is a PALU index. PALU[colorhash] then has the index to that color in
  // viewdata[0].bmpdata.palette[]. Multiple colors per same hash ID get
  // pushed ahead to the next free hash table space.
  wptr := length(viewdata[0].bmpdata.palette);
  diffusecount := wptr + (wptr shr 2) + 1;
  setlength(dithertab, wptr);
  setlength(palu, diffusecount);
  filldword(palu[0], diffusecount, $FFFFFFFF);
  while wptr <> 0 do begin
   dec(wptr);
   // For every real histogram color, put a reference in the PALU hash table.
   // i is the hash ID for this color.
   i := dword(viewdata[0].bmpdata.palette[wptr]) mod diffusecount;
   // Find the first free hash table slot starting from i.
   while palu[i] <> $FFFFFFFF do i := (i + 1) mod diffusecount;
   // Store the palettegram index of this color.
   palu[i] := wptr;

   // For every palettegram color, also find the closest and second closest
   // palette entry. Then test which dithering mix gives the closest result.
   j := $FFFFFFFF; palptr := option.palsize;
   while palptr <> 0 do begin
    dec(palptr);
    if pe[palptr].status <> 0 then begin
     i := diff(mcg_GammaInput(viewdata[0].bmpdata.palette[wptr]), pe[palptr].colog);
     if i < j then begin
      // new closest result!
      dithertab[wptr].pal1 := palptr; j := i;
      if i = 0 then break; // exact match! nothing can be closer, move on
     end;
    end;
   end;
   // Dithertab[wptr].PAL1 points to the palette entry with the least
   // difference from the real color. j remembers the difference value.

   if j = 0 then begin
    // Special case - if the closest palette entry is exactly the real color,
    // we already know it need not be dithered, so move along.
    dithertab[wptr].pal2 := dithertab[wptr].pal1;
    dithertab[wptr].mix := 0;
    continue;
   end;

   // For dithering purposes, the real color must be between PAL1 and PAL2.
   // Now to find a PAL2 that is across the real color, from PAL1.
   // If the distance from the real color to PAL2 is less than the distance
   // from PAL1 to PAL2, then PAL2 is on the other side than PAL1.
   k := $FFFFFFFF; palptr := option.palsize;
   dithertab[wptr].pal2 := dithertab[wptr].pal1;
   while palptr <> 0 do begin
    dec(palptr);
    if pe[palptr].status <> 0 then begin
     i := diff(pe[palptr].colog, mcg_GammaInput(viewdata[0].bmpdata.palette[wptr]));
     if (i <= diff(pe[dithertab[wptr].pal1].colog, pe[palptr].colog))
     and (i < k) then begin
      dithertab[wptr].pal2 := palptr; k := i;
     end;
    end;
   end;

   // Now we have the two colors closest to our target - PAL1 and PAL2.
   // Which matches best: flat PAL1, 50-50 PAL1:PAL2, or 75-25 PAL1:PAL2?
   // (alpha is dithered just like red, green and blue, because, why not?)
   dithertab[wptr].mix := 0;
   if option.dithering <> 0 then begin
    // Calculate 50-50 diff from the real color
    tempcolor.r := (pe[dithertab[wptr].pal1].colog.r + pe[dithertab[wptr].pal2].colog.r + 1) shr 1;
    tempcolor.g := (pe[dithertab[wptr].pal1].colog.g + pe[dithertab[wptr].pal2].colog.g + 1) shr 1;
    tempcolor.b := (pe[dithertab[wptr].pal1].colog.b + pe[dithertab[wptr].pal2].colog.b + 1) shr 1;
    tempcolor.a := (pe[dithertab[wptr].pal1].colog.a + pe[dithertab[wptr].pal2].colog.a + 1) shr 1;
    i := diff(mcg_GammaInput(viewdata[0].bmpdata.palette[wptr]), tempcolor);
    case option.dithering of
      1,5: if i < j then dithertab[wptr].mix := option.dithering;

      2:
      begin
       // Calculate 75-25 diff from the real color
       tempcolor.r := (pe[dithertab[wptr].pal1].colog.r * 3 + pe[dithertab[wptr].pal2].colog.r + 2) shr 2;
       tempcolor.g := (pe[dithertab[wptr].pal1].colog.g * 3 + pe[dithertab[wptr].pal2].colog.g + 2) shr 2;
       tempcolor.b := (pe[dithertab[wptr].pal1].colog.b * 3 + pe[dithertab[wptr].pal2].colog.b + 2) shr 2;
       tempcolor.a := (pe[dithertab[wptr].pal1].colog.a * 3 + pe[dithertab[wptr].pal2].colog.a + 2) shr 2;
       k := diff(mcg_GammaInput(viewdata[0].bmpdata.palette[wptr]), tempcolor);
       if (k < j) and (k < i) then dithertab[wptr].mix := 2 else
       if (i < j) then dithertab[wptr].mix := 1;
      end;

      3:
      begin
       // linear weight calculation, scaled to 0..8
       k := (8 * j + (i + j) div 2) div (i + j);
       dithertab[wptr].mix := 32 + k;
      end;

      6:
      begin
       // linear weight calculation, scaled to 0..2.5 (x2 for fraction)
       k := (5 * j + (i + j) div 2) div (i + j);
       dithertab[wptr].mix := 64 + k;
      end;
    end;

    // Eliminate dither banding: make sure the dithering pair is in the same
    // order, whichever of the pair is closer.
    if (dword(pe[dithertab[wptr].pal1].colo) < dword(pe[dithertab[wptr].pal2].colo))
    and (dithertab[wptr].mix <> 0)
    then begin
     i := dithertab[wptr].pal1;
     dithertab[wptr].pal1 := dithertab[wptr].pal2;
     dithertab[wptr].pal2 := i;
     case dithertab[wptr].mix of
       2: dithertab[wptr].mix := 255;
       32..40: dithertab[wptr].mix := 80 - dithertab[wptr].mix;
       64..69: dithertab[wptr].mix := 139 - dithertab[wptr].mix;
     end;
    end;
   end;
  end;

  sleep(0);
  //outpal;
  //writeln('Histogram:');
  //for i := 0 to high(viewdata[0].bmpdata.palette) do begin
  // write(i:3,':',strhex(dword(viewdata[0].bmpdata.palette[i])):8,'    ');
  // if i and 3 = 3 then writeln;
  //end;
  //writeln; writeln('Hash table:');
  //for i := 0 to darklistentries - 1 do
  // write(i:3,':',strhex(palu[i]):8,'    ');
  //writeln; writeln('Dithertable:');
  //for i := 0 to high(dithertab) do begin
  // write(i:4,':  ',strhex(dithertab[i].pal1),'+',strhex(dithertab[i].pal2),'*',dithertab[i].mix,'  ');
  // if i and 3 = 3 then writeln;
  //end; writeln;

  // Render the image with dithering into a new view!
  palusize := viewdata[0].bmpdata.sizex; palptr := viewdata[0].bmpdata.sizey;
  wptr := palusize * palptr;
  mcg_ForgetImage(@rendimu);
  getmem(rendimu.image, wptr * viewdata[0].alpha);
  rendimu.sizex := palusize; rendimu.sizey := palptr;
  rendimu.memformat := viewdata[0].alpha - 3;
  rendimu.bitdepth := 8;
  // 1. get the next pixel from source image
  // 2. find the color in the hash table
  // 3. get palette indexes from the dithering table
  // 4. decide which palette color to use based on dithering
  {$note todo: use direct ptr access for speed}
  if viewdata[0].alpha = 4 then begin
   // 32-bit image rendering
   while wptr <> 0 do begin
    dec(wptr);
    if palusize = 0 then begin dec(palptr); palusize := viewdata[0].bmpdata.sizex; end;
    dec(palusize);
    i := dword((viewdata[0].bmpdata.image + wptr * 4)^);
    j := i mod diffusecount;
    while (palu[j] = $FFFFFFFF) or (dword(viewdata[0].bmpdata.palette[palu[j]]) <> i)
    do j := (j + 1) mod diffusecount;
    j := palu[j];
    dword((rendimu.image + wptr * 4)^) := dword(pe[dithertab[j].pal1].colo);
    case dithertab[j].mix of
      1:
      if (palptr + palusize) and 1 <> 0 then
       dword((rendimu.image + wptr * 4)^) := dword(pe[dithertab[j].pal2].colo);

      2:
      if ((palptr shl 1) + palusize) and 3 = 0 then
       dword((rendimu.image + wptr * 4)^) := dword(pe[dithertab[j].pal2].colo);

      255:
      if ((palptr shl 1) + palusize) and 3 <> 0 then
       dword((rendimu.image + wptr * 4)^) := dword(pe[dithertab[j].pal2].colo);

      5:
      if palptr and 1 <> 0 then
       dword((rendimu.image + wptr * 4)^) := dword(pe[dithertab[j].pal2].colo);

      32..48:
      if octadtab[palptr and 3, palusize and 3] <= dithertab[j].mix - 32 then
       dword((rendimu.image + wptr * 4)^) := dword(pe[dithertab[j].pal2].colo);

      64..75:
      if plusdtab[palptr mod 5, palusize mod 5] <= (dithertab[j].mix - 64) shr 1 then
       dword((rendimu.image + wptr * 4)^) := dword(pe[dithertab[j].pal2].colo);
    end;
   end;
  end else begin
   // 24-bit image rendering
   while wptr <> 0 do begin
    dec(wptr);
    if palusize = 0 then begin dec(palptr); palusize := viewdata[0].bmpdata.sizex; end;
    dec(palusize);
    i := (RGBarray(viewdata[0].bmpdata.image^)[wptr].r shl 16)
      or (RGBarray(viewdata[0].bmpdata.image^)[wptr].g shl 8)
      or (RGBarray(viewdata[0].bmpdata.image^)[wptr].b)
      or $FF000000;
    j := i mod diffusecount;
    while (palu[j] = $FFFFFFFF) or (dword(viewdata[0].bmpdata.palette[palu[j]]) <> i)
     do j := (j + 1) mod diffusecount;
    j := palu[j];
    k := dithertab[j].pal1;
    case dithertab[j].mix of
      1:
      if (palptr + palusize) and 1 <> 0 then
       k := dithertab[j].pal2;

      2:
      if ((palptr shl 1) + palusize) and 3 = 0 then
       k := dithertab[j].pal2;

      255:
      if ((palptr shl 1) + palusize) and 3 <> 0 then
       k := dithertab[j].pal2;

      5:
      if palptr and 1 <> 0 then
       k := dithertab[j].pal2;

      32..48:
      if octadtab[palptr and 3, palusize and 3] <= dithertab[j].mix - 32 then
       k := dithertab[j].pal2;

      64..75:
      if plusdtab[palptr mod 5, palusize mod 5] <= (dithertab[j].mix - 64) shr 1 then
       k := dithertab[j].pal2;
    end;

    RGBarray(rendimu.image^)[wptr].b := pe[k].colo.b;
    RGBarray(rendimu.image^)[wptr].g := pe[k].colo.g;
    RGBarray(rendimu.image^)[wptr].r := pe[k].colo.r;
   end;
  end;
 end;

 // Clean up!
 setlength(wgram, 0); setlength(dithertab, 0);
 setlength(palu, 0); setlength(palug, 0); setlength(diffuselist, 0);
 // Fill out rendimu.palette, colors use PE index values if possible, and
 // forget the non-preset palette entries.
 setlength(rendimu.palette, option.palsize);
 wptr := 0;
 for palptr := 0 to option.palsize - 1 do begin
  if pe[palptr].status <> 0 then begin
   rendimu.palette[wptr] := pe[palptr].colo;
   inc(wptr);
  end;
  if pe[palptr].status <> 2 then ClearPE(palptr, palptr);
 end;
 setlength(rendimu.palette, wptr);

 // Let the user know we're done.
 SendMessageA(funwinhandle, WM_CLOSE, 0, 0);
end;

// --------------------------------------------------------------------------

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

function HelpProc (window : hwnd; amex : uint; wepu : wparam; lapu : lparam) : lresult; stdcall;
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

function AlfaSelectorProc (window : hwnd; amex : uint; wepu : wparam; lapu : lparam) : lresult; stdcall;
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

function FunProc (window : hwnd; amex : uint; wepu : wparam; lapu : lparam) : lresult; stdcall;
var flaguz : dword;
    kind : string[9];
    txt : string;
begin
 FunProc := 0;
 case amex of
   wm_InitDialog:
   begin
    if (batchprocess) and (strutsi <> '') then begin
     strutsi := strutsi + chr(0);
     SendMessageA(window, WM_SETTEXT, 0, longint(@strutsi[1]));
    end;
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

function MagicProc (window : hwnd; amex : uint; wepu : wparam; lapu : lparam) : lresult; stdcall;
// Handles win32 messages for the magic color list.
var mv_PS : paintstruct;
    kind : string[16];
    z : longint;
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
    if pe[pe_used].status = 0 then begin
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

function mv_MainProc (window : hwnd; amex : uint; wepu : wparam; lapu : lparam) : lresult; stdcall;
// Message handler for the main work window that has everything on it.
var kind, txt : string;
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
       pe[pe_used].status := 2;
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

      // File:Batch process images
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
      92:
      begin
       kind := 'Buncomp configuration files' + chr(0) + '*.ini' + chr(0) + chr(0);
       txt := chr(0); strutsi := homedir + chr(0);
       fillbyte(openfilurec, sizeof(openfilurec), 0);
       with openfilurec do begin
        lStructSize := 76; // sizeof gives incorrect result?
        hwndOwner := window;
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
         MessageBoxA(window, @txt[1], NIL, MB_OK);
        end;
       end;
      end;

      // Save config
      93:
      begin
       kind := 'Buncomp configuration files' + chr(0) + '*.ini' + chr(0) + chr(0);
       txt := chr(0); strutsi := homedir + chr(0);
       fillbyte(openfilurec, sizeof(openfilurec), 0);
       with openfilurec do begin
        lStructSize := 76; // sizeof gives incorrect result?
        hwndOwner := window;
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
         MessageBoxA(window, @txt[1], NIL, MB_OK);
        end;
       end;
      end;

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
 if registerClass (windowclass) = 0 then halt(98);

 // Register the view class for future use (for source and result images).
 windowclass.style := CS_OWNDC;
 windowclass.lpfnwndproc := wndproc(@ViewProc);
 windowclass.cbclsextra := 0;
 windowclass.cbwndextra := 0;
 windowclass.hinstance := system.maininstance;
 strutsi := 'BunnyIcon' + chr(0);
 windowclass.hicon := LoadIcon(system.maininstance, @strutsi[1]);
 windowclass.hcursor := LoadCursor(0, idc_arrow);
 windowclass.hbrbackground := GetSysColorBrush(color_3Dface);
 windowclass.lpszmenuname := NIL;
 windowclass.lpszclassname := @viewclass[1];
 if registerClass (windowclass) = 0 then halt(98);

 // Register the help class for future use.
 windowclass.style := 0;
 windowclass.lpfnwndproc := wndproc(@HelpProc);
 windowclass.cbclsextra := 0;
 windowclass.cbwndextra := 0;
 windowclass.hinstance := system.maininstance;
 strutsi := 'BunnyIcon' + chr(0);
 windowclass.hicon := LoadIcon(system.maininstance, @strutsi[1]);
 windowclass.hcursor := LoadCursor(0, idc_arrow);
 windowclass.hbrbackground := GetSysColorBrush(color_3Dface);
 windowclass.lpszmenuname := NIL;
 windowclass.lpszclassname := @helpclass[1];
 if registerClass (windowclass) = 0 then halt(98);

 // Register the main class for immediate use.
 windowclass.style := 0;
 windowclass.lpfnwndproc := wndproc(@mv_MainProc);
 windowclass.cbclsextra := 0;
 windowclass.cbwndextra := 0;
 windowclass.hinstance := system.maininstance;
 strutsi := 'BunnyIcon' + chr(0);
 windowclass.hicon := LoadIcon(system.maininstance, @strutsi[1]);
 windowclass.hcursor := LoadCursor(0, idc_arrow);
 windowclass.hbrbackground := GetSysColorBrush(color_btnface);
 strutsi := 'BunnyMenu' + chr(0);
 windowclass.lpszmenuname := @strutsi[1];
 windowclass.lpszclassname := @mainclass[1];
 if registerClass (windowclass) = 0 then halt(98);

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
 strutsi := 'BunnyHop' + chr(0);
 mv_AcceleratorTable := LoadAccelerators(system.maininstance, @strutsi[1]);

 // Create a right-click pop-up menu for the views.
 mv_ContextMenu := CreatePopupMenu;
 strutsi := '&Copy to clipboard ' + chr(8) + '(CTRL+C)' + chr(0);
 InsertMenu(mv_ContextMenu, 0, MF_BYPOSITION, 94, @strutsi[1]);
 strutsi := '&Save as PNG ' + chr(8) + '(CTRL+S)' + chr(0);
 InsertMenu(mv_ContextMenu, 1, MF_BYPOSITION, 91, @strutsi[1]);
 strutsi := 'I&mport palette ' + chr(8) + '(CTRL+M)' + chr(0);
 InsertMenu(mv_ContextMenu, 2, MF_BYPOSITION, 96, @strutsi[1]);

 // Just in case, make sure we are in the user's face.
 SetForegroundWindow(mv_MainWinH);
 SetFocus(mv_MainWinH);

 // Get rid of init messages and give the window its first layer of paint.
 while peekmessage(@mv_amessage, mv_MainWinH, 0, 0, PM_REMOVE) do begin
  translatemessage(mv_amessage);
  dispatchmessage(mv_amessage);
 end;
end;

// ------------------------------------------------------------------

begin
 AddExitProc(@bunexit);
 setlength(pe, 256);

 {$ifdef allowLAB} labtable[0] := 0; {$endif}

 {$define !difftest}
 {$ifdef difftest}
 // tiny debug segment to confirm any changes to diff routines aren't broken
 writeln('=== Testing ===');
 diff := @diffYCC;
 for i := 0 to 5 do begin
  pe[i].colog.r := 0; pe[i].colog.g := 0; pe[i].colog.b := 0; pe[i].colog.a := $FFFF;
 end;
 pe[1].colog.r := $FFFF; pe[2].colog.r := $FFFF; pe[4].colog.r := $8000;
 pe[1].colog.g := $FFFF; pe[4].colog.g := $8000; pe[5].colog.g := $FFFF;
 pe[1].colog.b := $FFFF; pe[3].colog.b := $FFFF; pe[4].colog.b := $8000;

 writeln(diff(pe[0].colog, pe[1].colog));
 writeln(diff(pe[2].colog, pe[3].colog));
 writeln(diff(pe[4].colog, pe[5].colog));
 writeln(diff(pe[0].colog, pe[3].colog));
 //exit;

 for palusize := 10 to 19 do begin
  i := GetTickCount;
  for j := 0 to 256000 do begin
   pe_used := diff(pe[0].colog, pe[1].colog);
   pe_used := diff(pe[2].colog, pe[3].colog);
   pe_used := diff(pe[4].colog, pe[5].colog);
   pe_used := diff(pe[0].colog, pe[5].colog);
  end;
  i := GetTickCount - i;
  dword(pe[palusize].colo) := i;
  sleep(130);
 end;
 j := 0;
 for i := 10 to 19 do begin
  write(dword(pe[palusize].colo),',');
  inc(j,dword(pe[palusize].colo));
 end;
 writeln; writeln('Average: ',j div 10,' msec');
 exit;
 {$endif difftest}

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
  strutsi := '\shell32.dll' + chr(0);
  move(strutsi[1], ptxt[j], length(strutsi));
  HelpWinH := LoadLibraryA(ptxt);
  strutsi := 'SHGetSpecialFolderPathA' + chr(0);
  pointer(SHGetSpecialFolderPath) := GetProcAddress(HelpWinH, @strutsi[1]);
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
  strutsi := errortxt(i) + ' trying to write in own directory as well as ' + homedir + chr(0);
  MessageBoxA(0, @strutsi[1], NIL, MB_OK); halt;
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

 // Main message loop.
 while (mv_EndProgram = FALSE) and (getmessage(@mv_amessage, 0, 0, 0))
 do begin
  if translateaccelerator(mv_MainWinH, mv_AcceleratorTable, mv_amessage) = 0
  then begin
   translatemessage(mv_amessage);
   dispatchmessage(mv_amessage);
  end;
 end;

 PostQuitMessage(0);
end.
