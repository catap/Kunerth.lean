/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf11

/-
Seite 42

§. 11.
Auflösung einiger Gleichungen von der Form
y² = ax²+b für positive Werthe von a.
-/

#guard (637 : ℤ) > 0 && (52 : ℤ) > 0 && (397 : ℤ) > 0

namespace Beispiel01

/-
1. Erstes Exempel.
y² = 637x²+575;    I
für y = 5y₁ und 7x = x₁ = 5x₁₁ geht diese Gleichung über in
y₁² = 13x₁₁²+23    II
-/

example (x₁₁ y₁ : ℚ) :
    (5 * y₁) ^ 2 - (637 * (5 * x₁₁ / 7) ^ 2 + 575) =
      25 * (y₁ ^ 2 - (13 * x₁₁ ^ 2 + 23)) := by ring

/-
für x₁₁ = 1 wird y₁ = 6; also ist
x₁₁ = 1−2(6p−13)/(p²−13),
-/

#guard (6 : ℤ) ^ 2 = 13 * 1 ^ 2 + 23

def x₁₁ (p : ℚ) : ℚ := 1 - 2 * (6 * p - 13) / (p ^ 2 - 13)

/-
S = 26.23 liefert nichts; also v² = 13w²−1, hier ist w = 5
v = 18; für p = +18/5 wird x₁₁ = 431, ein durch 7 nicht theilbarer,
somit unbrauchbarer Werth; dagegen liefert
p = −18/5 ... x₁₁ = 1729, y₁ = 6234,
somit ist x = 1235, y = 31170.
-/

#guard (26 * 23 : ℤ) = 598

#guard (18 : ℤ) ^ 2 = 13 * 5 ^ 2 - 1

#guard x₁₁ (18 / 5) = 431

#guard (431 : ℤ) % 7 != 0

#guard (x₁₁ (-18 / 5)) ^ 2 = 1729 ^ 2

#guard (6234 : ℤ) ^ 2 = 13 * 1729 ^ 2 + 23

#guard (5 * 1729 / 7 : ℚ) = 1235

#guard (5 * 6234 : ℤ) = 31170

#guard (31170 : ℤ) ^ 2 = 637 * 1235 ^ 2 + 575

/-
Auf andere Art. Hätte man die Gleichung I nicht
abgekürzt, so wäre zu setzen:
y² = d²x²+(637−d²)x²+575
hieraus
d² = 23γ²+637;
-/

example (x d : ℚ) : d ^ 2 * x ^ 2 + (637 - d ^ 2) * x ^ 2 + 575 =
    637 * x ^ 2 + 575 := by ring

/-
setzt man d = 7δ und γ = 7ε, so wird δ² = 23ε²+13 und für
ε = 1, δ = 6 und d = 42, somit
y² = (42x)²−23(49x²−25)
-/

example (δ ε : ℚ) : (7 * δ) ^ 2 - 23 * (7 * ε) ^ 2 - 637 =
    49 * (δ ^ 2 - 23 * ε ^ 2 - 13) := by ring

#guard (6 : ℤ) ^ 2 = 23 * 1 ^ 2 + 13

#guard (7 * 6 : ℤ) = 42

example (x : ℚ) : 637 * x ^ 2 + 575 = (42 * x) ^ 2 - 23 * (49 * x ^ 2 - 25) := by
  ring

/-
und
7x = 5−10(42p−637)/(p²−637)
oder
7x = 5−10(6q−13)/(q²−13), S = 130×23;
-/

def x (p : ℚ) : ℚ := (5 - 10 * (42 * p - 637) / (p ^ 2 - 637)) / 7

example (q : ℚ) : 7 * x (7 * q) = 5 - 10 * (6 * q - 13) / (q ^ 2 - 13) := by
  unfold x
  rw [show (7 * q) ^ 2 - 637 = 49 * (q ^ 2 - 13) by ring]
  rw [div_mul_eq_div_div]
  ring

#guard (130 * 23 : ℤ) % 7 != 0

/-
Seite 43

da S nichts liefert und den Factor 7 nicht enthält, so kann gesetzt
werden: v² = 13w²−1; für w = 5 wird v = 18 und für
q = −18/5 folgt x = −1235
wie oben.
-/

#guard x (7 * (-18 / 5)) = -1235

end Beispiel01

namespace Beispiel02

/-
2. Zweites Exempel.
y² = 52x²−139..... = 52x²−(139+d²)+d²
daraus
d² = 13γ²−139;
-/

example (x d : ℚ) : 52 * x ^ 2 - (139 + d ^ 2) + d ^ 2 = 52 * x ^ 2 - 139 := by ring

/-
für d = 13z+r wird
γ² = 13z²+2rz+(r²+139)/13;
für r = 2 wird
γ² = 13z²+4z+11
oder
γ² = 49z²−(18z−11)(2z+1)
-/

example (z r : ℚ) : ((13 * z + r) ^ 2 + 139) / 13 =
    13 * z ^ 2 + 2 * r * z + (r ^ 2 + 139) / 13 := by ring

#guard ((2 ^ 2 + 139) / 13 : ℚ) = 11

example (z : ℚ) : 13 * z ^ 2 + 4 * z + 11 = 49 * z ^ 2 - (18 * z - 11) * (2 * z + 1) := by
  ring

/-
und
2z = −1−2(7p+9)/(p²−13), S = 1112;
-/

def z (p : ℚ) : ℚ := (-1 - 2 * (7 * p + 9) / (p ^ 2 - 13)) / 2

#guard (8 * 139 : ℤ) = 1112

/-
für p = 3 ist z = 7, γ = 26, d = 93 somit
y² = 52x²−8788+93² = 52(x²−13²)+93²
-/

#guard z 3 = 7

#guard (26 : ℤ) ^ 2 = 13 * 7 ^ 2 + 4 * 7 + 11

#guard (13 * 7 + 2 : ℤ) = 93

example (x : ℚ) : 52 * x ^ 2 - 8788 + 93 ^ 2 = 52 * (x ^ 2 - 13 ^ 2) + 93 ^ 2 := by ring

/-
und
x = 13−2(93p−676)/(p²−52)
oder
x = 13−(93q−338)/(q²−13), S = 13×139;
-/

def x (q : ℚ) : ℚ := 13 - (93 * q - 338) / (q ^ 2 - 13)

example (q : ℚ) :
    13 - 2 * (93 * (2 * q) - 676) / ((2 * q) ^ 2 - 52) = x q := by
  unfold x
  rw [show (2 * q) ^ 2 - 52 = 4 * (q ^ 2 - 13) by ring, div_mul_eq_div_div]
  ring

#guard (13 * 139 : ℤ) = 1807

/-
da die Stammzahl kein x finden lässt, so setzen wir v² = 13w²−1
hier ist w = 5, v = 18 und für q = 18/5 kommt als zweiter Werth
x = 67, y = 483.
-/

#guard (18 : ℤ) ^ 2 = 13 * 5 ^ 2 - 1

#guard (x (18 / 5)) ^ 2 = 67 ^ 2

#guard (483 : ℤ) ^ 2 = 52 * 67 ^ 2 - 139

end Beispiel02

namespace Beispiel03

/-
3. Drittes Exempel.
y² = 397x²+9007, y = 397z+r,
x² = 397z²+2rz−22+(r²−273)/397;
-/

example (z r : ℚ) : ((397 * z + r) ^ 2 - 9007) / 397 =
    397 * z ^ 2 + 2 * r * z - 22 + (r ^ 2 - 273) / 397 := by ring

/-
Seite 44

dieser Bruch wird gleich 24 für r = 99, also ist
x² = 397z²+198z+2
oder
x² = (dz)²+(397−d²)z²+198z+2,
hieraus
2d²+9007 = γ²;
-/

#guard ((99 ^ 2 - 273) / 397 : ℚ) = 24

example (z d : ℚ) : (d * z) ^ 2 + (397 - d ^ 2) * z ^ 2 + 198 * z + 2 =
    397 * z ^ 2 + 198 * z + 2 := by ring

/-
für d = 3 ist γ = 95 und
x² = 9z²+(194z+2)(2z+1) = [3z+p(2z+1)]²
-/

#guard (2 * 3 ^ 2 + 9007 : ℤ) = 95 ^ 2

example (z : ℚ) : 397 * z ^ 2 + 198 * z + 2 = 9 * z ^ 2 + (194 * z + 2) * (2 * z + 1) := by
  ring

/-
und
2z = −1+(3p−95)/(p²+3p−97)
oder
2z = −1+2(3q−199)/(q²−397),
-/

def z (q : ℚ) : ℚ := (-1 + 2 * (3 * q - 199) / (q ^ 2 - 397)) / 2

example (p : ℚ) : 2 * z (2 * p + 3) = -1 + (3 * p - 95) / (p ^ 2 + 3 * p - 97) := by
  unfold z
  rw [show (2 * p + 3) ^ 2 - 397 = 4 * (p ^ 2 + 3 * p - 97) by ring,
    div_mul_eq_div_div]
  ring

/-
S = 8×9007 liefert nichts. Also setzen wir
v² = 397w²−4 = (19w)²+4(3w+1)(3w−1)
und
3w = 1−2(19r₁−397)/(r₁²−397), S₁ = 72;
-/

#guard (8 * 9007 : ℤ) = 72056

example (w : ℚ) : 397 * w ^ 2 - 4 = (19 * w) ^ 2 + 4 * (3 * w + 1) * (3 * w - 1) := by ring

def w (r₁ : ℚ) : ℚ := (1 - 2 * (19 * r₁ - 397) / (r₁ ^ 2 - 397)) / 3

#guard (2 * (397 - 19 ^ 2) : ℤ) = 72

/-
für r₁ = −20 wird w = 173, v = 3447; und für q = +3447/173 wird
z = +1041719, x = 20756109 und y = 413562542.
-/

#guard w (-20) = 173

#guard (3447 : ℤ) ^ 2 = 397 * 173 ^ 2 - 4

#guard z (3447 / 173) = 1041719

#guard (20756109 : ℤ) ^ 2 = 397 * 1041719 ^ 2 + 198 * 1041719 + 2

#guard (397 * 1041719 + 99 : ℤ) = 413562542

#guard (413562542 : ℤ) ^ 2 = 397 * 20756109 ^ 2 + 9007

end Beispiel03

end Kunerth1877.Paragraf11
