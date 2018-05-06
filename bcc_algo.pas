// --------------------------------------------------------------------------
// The color compression algorithm
//
// New ideas:
// - every pe whose sphere of influence reaches an outermost color may only
//   choose between the outermost colors when optimising its position
// - outermost colors should probably be marked as such during hgram creation
//   so any color ...?

// Working variables
var wgram : array of record
      color : RGBA64;
      pal : word;
    end;
    dithertab : array of record
      pal1, pal2 : word;
      mix : byte;
    end;
    offenders : array of record
      who : dword; // wgram index of biggest error mapped to its pal entry
      what : dword; // magnitude of deviation
    end;
    totalerror : qword;
    //lasttotalerror : qword;
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
  if pe[j].status <> PE_FREE then begin
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
   for i := high(pe) downto 0 do if pe[i].status <> PE_FREE then begin
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
   if pe[i].status = PE_ALLOCATED then
    if pe[i].matches = 0 then begin
     // If no wgram matches, release the palette entry.
     pe[i].status := PE_FREE;
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
    loopx, loopy : dword;
    palu : array of dword;
    palug : array of RGBA64;
    diffuselist : array of dword;
    diffusecount : dword;
    palptr : word;
    palumiss : boolean;
    tempcolor : RGBA64;
    x, y, z, alf : longint;
    wassup : UTF8string;
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
  if pe[i].status = PE_FIXED then begin
   if i >= option.palsize then inc(j);
   if palusize < option.palsize then begin
    palu[palusize] := dword(pe[i].colo);
    pe[i].colog := mcg_GammaInput(pe[i].colo);
    inc(palusize);
   end;
  end;
 if j <> 0 then begin
  wassup := 'You have ' + strdec(j) + ' pre-defined palette entries above the desired palette size. They may not be included in the processed image.' + chr(13) + 'Proceed anyway?';
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
    if (pe[j].status <> PE_FREE) and (dword(pe[j].colo) = dword(flats[i].color))
    then break;
   end;
   if dword(pe[j].colo) <> dword(flats[i].color) then begin
    j := 0;
    while pe[j].status <> PE_FREE do inc(j);
    pe[j].status := PE_AUTOFLAT;
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
  if (pe[i].status <> PE_FREE) then begin
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
 while (i * i * i) shl 1 <= dword(option.palsize - palusize) do inc(i);
 dec(i, 2);

 // If the target palette size is too small for initial spot placement, and
 // no palette entries were predefined, then at least plop one initial one
 // right on the first pixel in the wgram. It'll get shaken to a better
 // position during mean_reloc.
 if (i = 0) and (palusize = 0) then begin
  pe[0].colog := wgram[0].color;
  pe[0].colo := mcg_GammaOutput(wgram[0].color);
  pe[0].status := PE_ALLOCATED;
  inc(palptr); inc(palusize);
 end;

 // Place the points; check first that no point was in the preset palette.
 if i <> 0 then begin
  for x := 0 to i do
  for y := 0 to i do
  for z := 0 to i do begin
   // Get the next free slot in the palette...
   while pe[palptr].status <> PE_FREE do palptr := (palptr + 1) mod option.palsize;
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
    pe[palptr].status := PE_ALLOCATED;
    inc(palusize);
   end;
  end;
 end;

 // Shake the palette up a bit to start with, eliminate any matchless ones.
 sleep(50);
 if compressing = FALSE then exit;
 wassup := 'Mean relocation... (' + strdec(palusize) + ')';
 SendMessageA(funstatus, WM_SETTEXT, 0, ptrint(@wassup[1]));
 mean_reloc;

 // Main color compression loop!
 while (palusize < option.palsize) and (compressing) do begin
  sleep(0);
  // Calculate the number of new palette entries to set during this loop.
  faktor := ((option.palsize - palusize) shr 3) + 1;
  if faktor > palusize shr 1 then faktor := (palusize shr 1) + 1;
  // Map wgram to the existing palette, see where the biggest error is.
  wassup := 'Scoring deviation... (' + strdec(palusize) + ')';
  SendMessageA(funstatus, WM_SETTEXT, 0, ptrint(@wassup[1]));
  error_calc;

  //writeln; writeln('=== Allocating ===');
  // No colors left to allocate, but still space in palette? Call it a day.
  if offenders[faktor - 1].what <= 1 then break;
  // Allocate the new palette entries in the biggest error locations.
  for i := faktor - 1 downto 0 do begin
   while pe[palptr].status <> PE_FREE do palptr := (palptr + 1) mod option.palsize;
   pe[palptr].colog := wgram[offenders[i].who].color;
   pe[palptr].colo := mcg_GammaOutput(wgram[offenders[i].who].color);
   pe[palptr].status := PE_ALLOCATED;
   inc(palusize);
  end;

  // Shake the new palette to represent colors optimally.
  wassup := 'Mean relocation... (' + strdec(palusize) + ')';
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
  wassup := 'Optimising...';
  SendMessageA(funstatus, WM_SETTEXT, 0, ptrint(@wassup[1]));

  // Remember the current palette and its total error.
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

   // Try this for all non-preset palette entries.
   i := option.palsize;
   while (i <> 0) and (palumiss = FALSE) do begin
    dec(i);
    if k = i then palumiss := TRUE else
    if pe[i].status = 1 then begin

     // Release the palette entry.
     pe[i].status := 0;
     mean_reloc;

     // Reallocate it!
     error_calc;
     pe[i].colog := wgram[offenders[0].who].color;
     pe[i].colo := mcg_GammaOutput(wgram[offenders[0].who].color);
     pe[i].status := 1;
     mean_reloc;

     // Was it an improvement?
     if totalerror < lasttotalerror then begin
      writeln(totalerror);
      // Yes! Save the new palette.
      lasttotalerror := totalerror;
      for j := high(pe) downto 0 do begin
       palu[j] := dword(pe[j].colo);
       palug[j] := pe[j].colog;
      end;
      k := i;
     end else begin
      // No! Restore the old palette.
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
 // The source image is in viewdata[0].bmpdata.
 // The compressed palette is in pe[].
 // The dithered result goes into rendimu.
 // Lots of useful information on this at Libcaca: http://caca.zoy.org/study/
 JustRender:
 wassup := 'Rendering...';
 SendMessageA(funstatus, WM_SETTEXT, 0, ptrint(@wassup[1]));
 {$note todo: the whole dithering shebang needs a rewrite and modularisation}

 // Set up a bitmap to render the result in...
 mcg_ForgetImage(@rendimu);
 rendimu.sizex := viewdata[0].bmpdata.sizex;
 rendimu.sizey := viewdata[0].bmpdata.sizey;
 rendimu.memformat := viewdata[0].alpha - 3;
 rendimu.bitdepth := 8;
 getmem(rendimu.image, rendimu.sizex * rendimu.sizey * viewdata[0].alpha);

 if option.dithering = 4 then begin
  // Error-diffusive dithering - calculate best dither match per pixel.
  // This uses the Sierra Lite algorithm, in serpentine order.

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
  for loopx := viewdata[0].bmpdata.sizex - 1 downto 0 do
   diffuselist[loopx] := loopx;
  // Process the image, top-down, alternating L-to-R and R-to-L.
  for loopy := 0 to viewdata[0].bmpdata.sizey - 1 do begin

   if loopy and 7 = 0 then begin
    wassup := 'Rendering... ' + strdec(dword(viewdata[0].bmpdata.sizey - loopy));
    SendMessageA(funstatus, WM_SETTEXT, 0, ptrint(@wassup[1]));
   end;

   // Rearrange the horizontal processing order.
   if diffuselist[0] = 0 then begin
    for loopx := viewdata[0].bmpdata.sizex - 1 downto 0 do
     diffuselist[loopx] := viewdata[0].bmpdata.sizex - 1 - loopx;
   end else
    for loopx := viewdata[0].bmpdata.sizex - 1 downto 0 do
     diffuselist[loopx] := loopx;

   for loopx := 0 to viewdata[0].bmpdata.sizex - 1 do begin
    // Apply diffusion mods to current pixel...
    i := (diffusecount + diffuselist[loopx] * 4 + 8) and k;
    wptr := loopy * viewdata[0].bmpdata.sizex + diffuselist[loopx];
    if viewdata[0].alpha = 3 then begin
     // 24-bit
     x := round(longint(palu[i + 0]) / 4) + mcg_GammaTab[RGBarray(viewdata[0].bmpdata.image^)[wptr].b];
     if x < 0 then tempcolor.b := 0 else if x > 65535 then tempcolor.b := 65535 else tempcolor.b := word(x);
     x := round(longint(palu[i + 1]) / 4) + mcg_GammaTab[RGBarray(viewdata[0].bmpdata.image^)[wptr].g];
     if x < 0 then tempcolor.g := 0 else if x > 65535 then tempcolor.g := 65535 else tempcolor.g := word(x);
     x := round(longint(palu[i + 2]) / 4) + mcg_GammaTab[RGBarray(viewdata[0].bmpdata.image^)[wptr].r];
     if x < 0 then tempcolor.r := 0 else if x > 65535 then tempcolor.r := 65535 else tempcolor.r := word(x);
     tempcolor.a := $FFFF;
    end else begin
     // 32-bit
     tempcolor := mcg_GammaInput(RGBAarray(viewdata[0].bmpdata.image^)[wptr]);
     x := round(longint(palu[i + 0]) / 4) + tempcolor.b;
     if x < 0 then tempcolor.b := 0 else if x > 65535 then tempcolor.b := 65535 else tempcolor.b := word(x);
     x := round(longint(palu[i + 1]) / 4) + tempcolor.g;
     if x < 0 then tempcolor.g := 0 else if x > 65535 then tempcolor.g := 65535 else tempcolor.g := word(x);
     x := round(longint(palu[i + 2]) / 4) + tempcolor.r;
     if x < 0 then tempcolor.r := 0 else if x > 65535 then tempcolor.r := 65535 else tempcolor.r := word(x);
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
     i := diff(tempcolor, pe[palptr].colog);
     if i < offenders[0].what then begin
      offenders[0].who := palptr; offenders[0].what := i;
     end;
    end;
    palptr := offenders[0].who;
    // Plot the pixel with the matched palette color.
    if viewdata[0].alpha = 3 then begin
     RGBarray(rendimu.image^)[wptr].b := pe[palptr].colo.b;
     RGBarray(rendimu.image^)[wptr].g := pe[palptr].colo.g;
     RGBarray(rendimu.image^)[wptr].r := pe[palptr].colo.r;
    end else
     dword((rendimu.image + wptr * 4)^) := dword(pe[palptr].colo);
    // Calculate the per-channel error.
    x := tempcolor.b - pe[palptr].colog.b;
    y := tempcolor.g - pe[palptr].colog.g;
    z := tempcolor.r - pe[palptr].colog.r;
    alf := tempcolor.a - pe[palptr].colog.a;
    // Stuff the error into PALU to diffuse it.
    i := (diffusecount + diffuselist[loopx] * 4 + 4) and k; // -1x
    if diffuselist[0] = 0 then i := (i + 8) and k; // or +1x
    longint(palu[i]) := longint(palu[i]) + x * 2; inc(i);
    longint(palu[i]) := longint(palu[i]) + y * 2; inc(i);
    longint(palu[i]) := longint(palu[i]) + z * 2; inc(i);
    longint(palu[i]) := longint(palu[i]) + alf * 2; inc(i);
    if diffuselist[0] <> 0 then i := (i + 12) and k;
    // -1x, +1y (or +0x, +1y if in reverse mode)
    j := (i + dword(viewdata[0].bmpdata.sizex * 4) + 4) and k;
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
   diffusecount := (diffusecount + dword(viewdata[0].bmpdata.sizex * 4) + 16) and k;
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
    if pe[palptr].status <> PE_FREE then begin
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
    if pe[palptr].status <> PE_FREE then begin
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
    // Calculate 50-50 diff from the real color.
    tempcolor.r := (pe[dithertab[wptr].pal1].colog.r + pe[dithertab[wptr].pal2].colog.r + 1) shr 1;
    tempcolor.g := (pe[dithertab[wptr].pal1].colog.g + pe[dithertab[wptr].pal2].colog.g + 1) shr 1;
    tempcolor.b := (pe[dithertab[wptr].pal1].colog.b + pe[dithertab[wptr].pal2].colog.b + 1) shr 1;
    tempcolor.a := (pe[dithertab[wptr].pal1].colog.a + pe[dithertab[wptr].pal2].colog.a + 1) shr 1;
    i := diff(mcg_GammaInput(viewdata[0].bmpdata.palette[wptr]), tempcolor);
    case option.dithering of
      1,5: if i < j then dithertab[wptr].mix := option.dithering;

      2:
      begin
       // Calculate 75-25 diff from the real color.
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
       // Linear weight calculation, scaled to 0..8.
       k := (8 * j + (i + j) div 2) div (i + j);
       dithertab[wptr].mix := 32 + k;
      end;

      6:
      begin
       // Linear weight calculation, scaled to 0..2.5 (x2 for fraction).
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
  loopx := viewdata[0].bmpdata.sizex;
  loopy := viewdata[0].bmpdata.sizey;
  wptr := loopx * loopy;
  // 1. get the next pixel from source image
  // 2. find the color in the hash table
  // 3. get palette indexes from the dithering table
  // 4. decide which palette color to use based on dithering
  {$note todo: use direct ptr access for speed}
  if viewdata[0].alpha = 4 then begin
   // 32-bit image rendering
   while wptr <> 0 do begin
    dec(wptr);

    if loopx = 0 then begin
     dec(loopy);
     loopx := viewdata[0].bmpdata.sizex;
    end;
    dec(loopx);

    i := dword((viewdata[0].bmpdata.image + wptr * 4)^);
    j := i mod diffusecount;
    while (palu[j] = $FFFFFFFF) or (dword(viewdata[0].bmpdata.palette[palu[j]]) <> i)
    do j := (j + 1) mod diffusecount;
    j := palu[j];
    dword((rendimu.image + wptr * 4)^) := dword(pe[dithertab[j].pal1].colo);
    case dithertab[j].mix of
      1:
      if (loopy + loopx) and 1 <> 0 then
       dword((rendimu.image + wptr * 4)^) := dword(pe[dithertab[j].pal2].colo);

      2:
      if ((loopy shl 1) + loopx) and 3 = 0 then
       dword((rendimu.image + wptr * 4)^) := dword(pe[dithertab[j].pal2].colo);

      255:
      if ((loopy shl 1) + loopx) and 3 <> 0 then
       dword((rendimu.image + wptr * 4)^) := dword(pe[dithertab[j].pal2].colo);

      5:
      if loopy and 1 <> 0 then
       dword((rendimu.image + wptr * 4)^) := dword(pe[dithertab[j].pal2].colo);

      32..48:
      if octadtab[loopy and 3, loopx and 3] <= dithertab[j].mix - 32 then
       dword((rendimu.image + wptr * 4)^) := dword(pe[dithertab[j].pal2].colo);

      64..75:
      if plusdtab[loopy mod 5, loopx mod 5] <= (dithertab[j].mix - 64) shr 1 then
       dword((rendimu.image + wptr * 4)^) := dword(pe[dithertab[j].pal2].colo);
    end;
   end;
  end else begin
   // 24-bit image rendering
   while wptr <> 0 do begin
    dec(wptr);
    if loopx = 0 then begin
     dec(loopy);
     loopx := viewdata[0].bmpdata.sizex;
    end;
    dec(loopx);
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
      if (loopy + loopx) and 1 <> 0 then
       k := dithertab[j].pal2;

      2:
      if ((loopy shl 1) + loopx) and 3 = 0 then
       k := dithertab[j].pal2;

      255:
      if ((loopy shl 1) + loopx) and 3 <> 0 then
       k := dithertab[j].pal2;

      5:
      if loopy and 1 <> 0 then
       k := dithertab[j].pal2;

      32..48:
      if octadtab[loopy and 3, loopx and 3] <= dithertab[j].mix - 32 then
       k := dithertab[j].pal2;

      64..75:
      if plusdtab[loopy mod 5, loopx mod 5] <= (dithertab[j].mix - 64) shr 1 then
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
  if pe[palptr].status <> PE_FREE then begin
   rendimu.palette[wptr] := pe[palptr].colo;
   inc(wptr);
  end;
  if pe[palptr].status <> PE_FIXED then ClearPE(palptr, palptr);
 end;
 setlength(rendimu.palette, wptr);

 // Let the user know we're done.
 SendMessageA(funwinhandle, WM_CLOSE, 0, 0);
end;
