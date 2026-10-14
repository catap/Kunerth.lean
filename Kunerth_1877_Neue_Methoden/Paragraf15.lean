/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf15

/-
Seite 55

§. 15.
Auflösung von Gleichungen anderer Form.
-/

namespace Beispiel01

/-
1. Erstes Exempel.
5x²−7xy ⟦Vorzeichen unklar⟧ 3y²−17x+8y−28 = 0,
daraus
y = (7x−8)/6 ± (1/6)√(−11x²+92x+400),
z² = −11x²+92x+400 = (20−px)²,
hieraus
x = 4(10p+23)/(p²+11), S = 4.9.181
-/

/-
Redaktionelle Rekonstruktion: Die anschliessende Formel für y
entspricht dem Term +3y² in der Ausgangsgleichung. Dies ist aus
der Rechnung erschlossen; das beschädigte Vorzeichen vor 3y²
bleibt als Lesart unklar. Die folgende quadratische Ergänzung
prüft diese mathematische Zuordnung, nicht die Lesart.
-/

example (x y : ℚ) :
    (6 * y - (7 * x - 8)) ^ 2 - (-11 * x ^ 2 + 92 * x + 400) =
      12 * (5 * x ^ 2 - 7 * x * y + 3 * y ^ 2 - 17 * x + 8 * y - 28) := by
  ring

example (x p : ℚ) :
    (20 - p * x) ^ 2 - (-11 * x ^ 2 + 92 * x + 400) =
      x * ((p ^ 2 + 11) * x - 4 * (10 * p + 23)) := by ring

example : (4 * 9 * 181 : ℤ) % (1 ^ 2 + 11) = 0 ∧
    (4 * 9 * 181 : ℤ) % ((-5) ^ 2 + 11) = 0 := by norm_num

/-
p =    1    −5    ∞
x =   11    −3    0
z =    9     5   20
y = 10, 13  −4    2
-/

example : (4 : ℚ) * (10 * 1 + 23) / (1 ^ 2 + 11) = 11 ∧
    (4 : ℚ) * (10 * (-5) + 23) / ((-5) ^ 2 + 11) = -3 := by norm_num

example : (9 : ℚ) ^ 2 = -11 * 11 ^ 2 + 92 * 11 + 400 ∧
    (5 : ℚ) ^ 2 = -11 * (-3) ^ 2 + 92 * (-3) + 400 ∧
    (20 : ℚ) ^ 2 = -11 * 0 ^ 2 + 92 * 0 + 400 := by norm_num

example : ((7 : ℚ) * 11 - 8 - 9) / 6 = 10 ∧
    ((7 : ℚ) * 11 - 8 + 9) / 6 = 13 ∧
    ((7 : ℚ) * (-3) - 8 + 5) / 6 = -4 ∧
    ((7 : ℚ) * 0 - 8 + 20) / 6 = 2 := by norm_num

end Beispiel01

namespace Beispiel02

/-
2. Zweites Exempel.
2x²−6xy+y²−14x+10y+4 = 0.
y = 3x−5±√(7x²−16x+21)
z² = 7x²−16x+21 = 4x²+(3x−7)(x−3) = [2x+p(x−3)]²,
-/

example (x y : ℚ) : 2 * x ^ 2 - 6 * x * y + y ^ 2 - 14 * x + 10 * y + 4 =
    (y - (3 * x - 5)) ^ 2 - (7 * x ^ 2 - 16 * x + 21) := by ring

example (x : ℚ) : 7 * x ^ 2 - 16 * x + 21 =
    4 * x ^ 2 + (3 * x - 7) * (x - 3) := by ring

example (x p : ℚ) : (2 * x + p * (x - 3)) ^ 2 - (7 * x ^ 2 - 16 * x + 21) =
    (x - 3) * ((p ^ 2 + 4 * p - 3) * (x - 3) + 12 * p - 2) := by ring

/-
somit
x = 3−(12p−2)/(p²+4p−3),
für p = q−2 wird
x = 3−2(6q−13)/(q²−7), S = 2×83;
-/

example (q : ℚ) :
    3 - (12 * (q - 2) - 2) / ((q - 2) ^ 2 + 4 * (q - 2) - 3) =
      3 - 2 * (6 * q - 13) / (q ^ 2 - 7) := by
  have h : (q - 2) ^ 2 + 4 * (q - 2) - 3 = q ^ 2 - 7 := by ring
  rw [h]
  ring

example : (2 * 83 : ℤ) % (3 ^ 2 - 7) = 0 := by norm_num

/-
für q =     ∞           3                 (−2+34)/(2+10) = 8/3
    x =     3      −2       34             −51         525
    z =    ±6      ±9      ±87            ±138       ±1386
    y = −2, 10  −2, −20  10, 184        −20, −296   184, 2956
-/

example : ((-2 : ℚ) + 34) / (2 + 10) = 8 / 3 := by norm_num

example : ([3, -3, 8 / 3, -8 / 3] : List ℚ).map
    (fun q => 3 - 2 * (6 * q - 13) / (q ^ 2 - 7)) =
      [-2, 34, -51, 525] := by norm_num

example : ([(3, 6), (-2, 9), (34, 87), (-51, 138), (525, 1386)] : List (ℤ × ℤ)).all
    (fun (x, z) => decide (z ^ 2 = 7 * x ^ 2 - 16 * x + 21)) = true := by decide

example : ([(3, 6), (-2, 9), (34, 87), (-51, 138), (525, 1386)] : List (ℤ × ℤ)).map
    (fun (x, z) => (3 * x - 5 - z, 3 * x - 5 + z)) =
      [(-2, 10), (-20, -2), (10, 184), (-296, -20), (184, 2956)] := by decide

example : ([(3, -2), (3, 10), (-2, -2), (-2, -20), (34, 10), (34, 184),
    (-51, -20), (-51, -296), (525, 184), (525, 2956)] : List (ℤ × ℤ)).all
      (fun (x, y) => decide (2 * x ^ 2 - 6 * x * y + y ^ 2 - 14 * x + 10 * y + 4 = 0)) =
        true := by decide

end Beispiel02

namespace Beispiel03

/-
3. Drittes Exempel.
42x²+62xy+21y² = 585
-/

/-
Seite 56

y = −31x/21 ± (1/21)√(79x²+12285);
v² = 79x²+12285; v = 79z+r;
x² = 79z²+2rz−155+(r²−40)/79,
für r = 35 wird der Bruch = 15 somit
x² = 79z²+70z−140;
-/

example (x y : ℚ) :
    (21 * y + 31 * x) ^ 2 - (79 * x ^ 2 + 12285) =
      21 * (42 * x ^ 2 + 62 * x * y + 21 * y ^ 2 - 585) := by ring

example (z r : ℚ) : ((79 * z + r) ^ 2 - 12285) / 79 =
    79 * z ^ 2 + 2 * r * z - 155 + (r ^ 2 - 40) / 79 := by ring

example : ((35 : ℚ) ^ 2 - 40) / 79 = 15 := by norm_num

example (z : ℚ) : ((79 * z + 35) ^ 2 - 12285) / 79 =
    79 * z ^ 2 + 70 * z - 140 := by ring

/-
für z = 1 wird
x = 3, v = 114 und v² = 79(x²−9)+114²
hieraus
x = 3−6(38p−79)/(p²−79), S = 2.3³.5.7.13.79
-/

example : (3 : ℤ) ^ 2 = 79 * 1 ^ 2 + 70 * 1 - 140 ∧
    (79 : ℤ) * 1 + 35 = 114 := by norm_num

example (x : ℚ) : 79 * x ^ 2 + 12285 = 79 * (x ^ 2 - 9) + 114 ^ 2 := by ring

example (p : ℚ) :
    3 - 2 * (114 * p - 79 * 3) / (p ^ 2 - 79) =
      3 - 6 * (38 * p - 79) / (p ^ 2 - 79) := by ring

/-
p =   0    8   7  5   4   3  1       9         10   11...
x =  −3   93  66  *  19   6  *   1266, 786     83   74
v = 114  834 597    202 123      11253, 6987    746  667
−y =  1  177  69      *   3       1333, 1493     87  141.
-/

example : ([0, 8, -7, -4, 3, -9, 9, 10, -11] : List ℚ).map
    (fun p => 3 - 6 * (38 * p - 79) / (p ^ 2 - 79)) =
      [-3, 93, -66, -19, 6, 1266, -786, -83, 74] := by norm_num

example : ([(0, -3), (8, 93), (-7, -66), (-4, -19), (3, 6),
    (-9, 1266), (9, -786), (10, -83), (-11, 74)] : List (ℚ × ℚ)).map
      (fun (p, x) => |114 + p * (x - 3)|) =
        [114, 834, 597, 202, 123, 11253, 6987, 746, 667] := by norm_num

example : ([(3, 114), (93, 834), (66, 597), (19, 202), (6, 123),
    (1266, 11253), (786, 6987), (83, 746), (74, 667)] : List (ℤ × ℤ)).all
      (fun (x, v) => decide (v ^ 2 = 79 * x ^ 2 + 12285)) = true := by decide

example : (((31 : ℚ) * (-3) + 114) / 21,
    ((31 : ℚ) * 93 + 834) / 21,
    ((31 : ℚ) * 66 - 597) / 21,
    ((31 : ℚ) * 6 - 123) / 21,
    ((31 : ℚ) * 1266 - 11253) / 21,
    ((31 : ℚ) * 786 + 6987) / 21,
    ((31 : ℚ) * 83 - 746) / 21,
    ((31 : ℚ) * 74 + 667) / 21) =
      (1, 177, 69, 3, 1333, 1493, 87, 141) := by norm_num

example : ([(5 : ℚ), -5, 1] : List ℚ).all
    (fun p => decide ((3 - 6 * (38 * p - 79) / (p ^ 2 - 79)).den ≠ 1)) = true := by
  native_decide

example : |(3 : ℚ) - 6 * (38 * (-1) - 79) / ((-1) ^ 2 - 79)| = 6 ∧
    (((31 : ℚ) * 19 + 202) / 21).den ≠ 1 ∧
    (((31 : ℚ) * 19 - 202) / 21).den ≠ 1 := by norm_num

example : ([(-3, -1), (93, -177), (66, -69), (6, -3), (1266, -1333),
    (786, -1493), (83, -87), (74, -141)] : List (ℤ × ℤ)).all
      (fun (x, y) => decide (42 * x ^ 2 + 62 * x * y + 21 * y ^ 2 = 585)) = true := by
  decide

/-
Die ferneren p liefern nichts oder Wiederholungen.
-/

example : ((List.range (Nat.sqrt (2 * 3 ^ 3 * 5 * 7 * 13 * 79 + 79) + 1)).drop 12).all
    (fun k => ([k, -(k : ℤ)] : List ℤ).all (fun p =>
      let x : ℚ := 3 - 6 * (38 * p - 79) / ((p : ℚ) ^ 2 - 79)
      let v : ℚ := 114 + p * (x - 3)
      decide (x.den = 1 ∧ (((-31 * x + v) / 21).den = 1 ∨
        ((-31 * x - v) / 21).den = 1) → |x| = 3 ∨ |x| = 6))) = true := by
  native_decide

end Beispiel03

end Kunerth1877.Paragraf15
