{$define !difftest} // <-- use this to check that color diffs remain sane

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

{$define newdiffrgb}
{$ifdef newdiffrgb}
function diffRGB(c1, c2 : RGBA64) : dword;
// Returns the squared difference between the two RGBA64 colors.
// Apparently the best way to do this is actually in sRGB space, not linear,
// and with weighings of 3:4:2, plus whatever for alpha?
// See https://www.compuphase.com/cmetric.htm
// The output will be within [0..$9EC0A]
var b, g, r, a : dword;
begin
 b := abs(mcg_RevGammaTab[c1.b] * c1.a - mcg_RevGammaTab[c2.b] * c2.a);
 g := abs(mcg_RevGammaTab[c1.g] * c1.a - mcg_RevGammaTab[c2.g] * c2.a);
 r := abs(mcg_RevGammaTab[c1.r] * c1.a - mcg_RevGammaTab[c2.r] * c2.a);
 a := abs(c1.a - c2.a) * 255;
 diffRGB := b * 2 + g * 4 + r * 3 + a;
 r := r shr 11;
 g := g shr 11;
 b := b shr 11;
 a := a shr 11;
 inc(diffRGB, b * b * 2 + g * g * 4 + r * r * 3 + a * a);
end;
{$else}
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
{$endif}

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
 diffYCC := dword(Y) + Cr + Cb + aeon; // nominal range of sum = [0..360443]
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

{$ifdef difftest}
procedure DiffTest;
var testcount, timespent, numdiffs : dword;
    i, j, l : dword;
    timeovercount : double;
begin
 // Tiny debug segment to confirm any changes to diff routines aren't broken.
 writeln('=== Testing ===');
 diff := @diffRGB;
 for i := 0 to 5 do begin
  pe[i].colog.r := 0; pe[i].colog.g := 0; pe[i].colog.b := 0; pe[i].colog.a := $FFFF;
 end;
 pe[0].colog.a := 0;
 pe[1].colog.r := $FFFF; pe[2].colog.r := $FFFF; pe[4].colog.r := $8000;
 pe[1].colog.g := $FFFF; pe[4].colog.g := $8000; pe[5].colog.g := $FFFF;
 pe[1].colog.b := $FFFF; pe[3].colog.b := $FFFF; pe[4].colog.b := $8000;

 writeln(strhex(diff(pe[0].colog, pe[1].colog)));
 writeln(strhex(diff(pe[2].colog, pe[3].colog)));
 writeln(strhex(diff(pe[4].colog, pe[5].colog)));
 writeln(strhex(diff(pe[0].colog, pe[3].colog)));
 //exit;

 // Tiny speed test.
 testcount := 8;
 numdiffs := 1 shl 22;
 timespent := 0;
 for l := testcount - 1 downto 0 do begin
  i := GetTickCount;
  for j := numdiffs downto 0 do begin
   pe_used := diff(pe[0].colog, pe[1].colog);
   pe_used := diff(pe[2].colog, pe[3].colog);
   pe_used := diff(pe[4].colog, pe[5].colog);
   pe_used := diff(pe[0].colog, pe[5].colog);
  end;
  i := GetTickCount - i;
  inc(timespent, i);
  write(i, ',');
  sleep(130);
 end;
 writeln;
 writeln('Attempts: ', testcount);
 writeln('Diffs / attempt: ', numdiffs);
 timeovercount := timespent / testcount;
 writeln('Average ', timeovercount:1:1, ' msec / attempt');
 timeovercount := timeovercount / numdiffs;
 writeln('Average ', (1000 * timeovercount):3:3, ' usec / diff');
 writeln((1000 / timeovercount):1:1, ' diffs / second');
end;
{$endif difftest}
