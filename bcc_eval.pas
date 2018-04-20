procedure DetectFlats;
// Looks for blocks of 3x3 or 4x4 pixels of the same color in bmpdata.image^
// of view 0. Each match adds points to flats[color].weight, and at the end
// the array is sorted in order of descending weights.
var ofsx, ofsy, cmpw1 : word;
    poku, poku2, poku3, poku4 : pointer;
    refcolor, cmpd1, cmpd2, cmpd3 : dword;
    match : byte;

  procedure addflat(cola : dword; weight : byte);
  // Adds a new color to the flats[] list, or adds weight to it if the given
  // color is already listed.
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
    hash : array[0..hgram_bucket_count - 1] of array of dword;
    bucketitems : array[0..hgram_bucket_count - 1] of dword;
    bitmask : dword;
    existence : boolean;
begin
 if (sr > high(viewdata)) or (viewdata[sr].bmpdata.image = NIL) then exit;
 // If a palette already exists, this proc will not recalculate it. If you
 // want to force a recalculation, SetLength(.bmpdata.palette, 0) first.
 if length(viewdata[sr].bmpdata.palette) <> 0 then exit;

 gramsize := 0;
 filldword(bucketitems, length(bucketitems), 0);
 setlength(hash[0], 0); // silence a compiler warning

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
 hvar := 0;
 for iofs := high(bucketitems) downto 0 do begin
  if bucketitems[iofs] <> 0 then begin
   for i := 0 to bucketitems[iofs] - 1 do begin
    dword(viewdata[sr].bmpdata.palette[hvar]) := hash[iofs][i];
    inc(hvar);
   end;
  end;
 end;
end;
