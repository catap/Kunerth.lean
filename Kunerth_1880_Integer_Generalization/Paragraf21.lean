/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf21

/-
Seite 365
§. 21.

Ist x = m/n und kommen in der VI. Spalte weder n, noch ein
Multiplum, noch die Factoren von n vor, so suche man für x
einen Bruch, dessen Nenner auf eine dieser Arten in der VI. Reihe
repräsentirt ist.

Nach IV ist α = −np + α₁, β = mp + β₁ und nach VI:

x = [(β² − c) : m]/[(α² − a) : n]
  = (mp² + 2β₁p + δ)/(np² − 2α₁p + γ);
-/

example (m n α₁ β₁ γ δ p : ℚ) (hm : m ≠ 0) (hn : n ≠ 0)
    (_hN : n * p ^ 2 - 2 * α₁ * p + γ ≠ 0) :
    (((m * p + β₁) ^ 2 - (β₁ ^ 2 - m * δ)) / m) /
      (((-n * p + α₁) ^ 2 - (α₁ ^ 2 - n * γ)) / n) =
      (m * p ^ 2 + 2 * β₁ * p + δ) / (n * p ^ 2 - 2 * α₁ * p + γ) := by
  have hnum : ((m * p + β₁) ^ 2 - (β₁ ^ 2 - m * δ)) / m =
      m * p ^ 2 + 2 * β₁ * p + δ := by
    apply (div_eq_iff hm).2
    ring
  have hden : ((-n * p + α₁) ^ 2 - (α₁ ^ 2 - n * γ)) / n =
      n * p ^ 2 - 2 * α₁ * p + γ := by
    apply (div_eq_iff hn).2
    ring
  rw [hnum, hden]

/-
lässt man hier p die ersten Glieder der natürlichen Zahlenreihe,
eventuell auch die der harmonischen Reihe (Schluss des §. 2)
mit beiden Vorzeichen durchlaufen, so kommt man häufig auf
einen solchen Werth von

x (= fm₁/(fn₁) = m₁/n₁),

dass der Nenner n₁ in einer der oben bezeichneten Weisen in der
VI. Colonne vertreten ist.
-/

namespace Beispiel12

/-
12. Exempel:
y² = 294x²+371x+120 = 25+(14x+5)(21x+19),
-/

example (x : ℚ) : 294 * x ^ 2 + 371 * x + 120 = 25 + (14 * x + 5) * (21 * x + 19) := by ring

/-
D = −49.71, x = −5/14, α = −14p, β = −5p+5,
x = −(5p²−10p−19)/(14p²−21);
-/

example : (371 ^ 2 - 4 * 294 * 120 : ℤ) = -49 * 71 := by norm_num

/-
I   294   VI
17 ...  5
 6 ... 25
-/

example :
    let step := fun (s : ℤ × ℤ × List (ℤ × Bool)) (q : ℤ) =>
      let m := q * s.2.1 - s.1
      let d := (294 - m ^ 2) / s.2.1
      (m, d, s.2.2 ++ [(d, (294 - m ^ 2) % s.2.1 == 0)])
    (([17, 6] : List ℤ).foldl step (0, 1, [])).2.2 = [(5, true), (25, true)] := by norm_num

/-
Seite 366

für p = −2 wird
x = −21/35 = −3/5, α = 28, β = 15 und
y = (−3.28+5.15)/5 = −9/5;
-/

example : (-(5 * (-2) ^ 2 - 10 * (-2) - 19) / (14 * (-2) ^ 2 - 21) : ℚ) = -21 / 35 := by norm_num

example : (-21 / 35 : ℚ) = -3 / 5 := by norm_num

example : (-14 * (-2) : ℤ) = 28 := by norm_num

example : (-5 * (-2) + 5 : ℤ) = 15 := by norm_num

example : ((-3 * 28 + 5 * 15) / 5 : ℚ) = -9 / 5 := by norm_num

example : (-9 / 5 : ℚ) ^ 2 = 294 * (-3 / 5) ^ 2 + (371) * (-3 / 5) + (120) := by norm_num

/-
somit 5x = −3+(−18p₁+91)/(p₁²−294)
-/

example (p : ℚ) : (-3) + (2 * (-9) * p + (2 * 294 * (-3) + (371) * 5)) / (p ^ 2 - 294) = (-3) + 1 * ((-18) * p + (91)) / (p ^ 2 - 294) := by ring

/-
für p₁ = 17 (der erste Näherungsbruch) wird x = 8, y = 148.
-/

example : (-3 + (-18 * 17 + 91) / (17 ^ 2 - 294) : ℚ) = 5 * 8 := by norm_num

example : (148 : ℚ) ^ 2 = 294 * (8) ^ 2 + (371) * (8) + (120) := by norm_num

/-
Oder: x = −5/14, y = 70/14,
14x = −5+14(10p+161)/(p²−294)
= −5+2(10p₁+23)/(p₁²−6), S¹,, = −2.71
-/

example : (70 / 14 : ℚ) ^ 2 = 294 * (-5 / 14) ^ 2 + (371) * (-5 / 14) + (120) := by norm_num

example (p : ℚ) : 14 * (10 * (7 * p) + 161) * (p ^ 2 - 6) = 2 * (10 * p + 23) * ((7 * p) ^ 2 - 294) := by ring

example : (14 ^ 2 * (-49 * 71) / (2 * 7 ^ 4) : ℚ) = -2 * 71 := by norm_num

/-
I   6   VI
2 ... 2
2 ... 1
4 ... 2
-/

example :
    let step := fun (s : ℤ × ℤ × List (ℤ × Bool)) (q : ℤ) =>
      let m := q * s.2.1 - s.1
      let d := (6 - m ^ 2) / s.2.1
      (m, d, s.2.2 ++ [(d, (6 - m ^ 2) % s.2.1 == 0)])
    (([2, 2, 4] : List ℤ).foldl step (0, 1, [])).2.2 = [(2, true), (1, true), (2, true)] := by norm_num

/-
p₁ = −22/9 (der dritte Näherungsbruch)
aus der zweiten Periode) macht x = 8.
-/

example : (-5 + 2 * (10 * (-22 / 9) + 23) / ((-22 / 9) ^ 2 - 6) : ℚ) = 14 * 8 := by norm_num

end Beispiel12

namespace Beispiel13

/-
13. Exempel:
y² = 637x²+575 = (25x+5)²+2(3x−55)(2x−5),
-/

example (x : ℚ) : 637 * x ^ 2 + 575 = (25 * x + 5) ^ 2 + 2 * (3 * x - 55) * (2 * x - 5) := by ring

/-
D = −4.5².7².13.23, x = 55/3, α = −3p+25, β = 55p+5,
-/

example : (-4 * 637 * 575 : ℤ) = -4 * 5 ^ 2 * 7 ^ 2 * 13 * 23 := by norm_num

/-
x = (55p²+10p−10)/(3p²−50p−4), p = −1/3, x = −65/117 = −5/9
α = 26, β = −40/3, y = −250/9 und
-/

example : ((55 * (-1 / 3) ^ 2 + 10 * (-1 / 3) - 10) / (3 * (-1 / 3) ^ 2 - 50 * (-1 / 3) - 4) : ℚ) = -65 / 117 := by norm_num

example : (-65 / 117 : ℚ) = -5 / 9 := by norm_num

example : (-3 * (-1 / 3) + 25 : ℚ) = 26 := by norm_num

example : (55 * (-1 / 3) + 5 : ℚ) = -40 / 3 := by norm_num

example : (-250 / 9 : ℚ) ^ 2 = 637 * (-5 / 9) ^ 2 + (0) * (-5 / 9) + (575) := by norm_num

/-
9x = −5+10(−50p₁−637)/(p₁²−637);
-/

example (p : ℚ) : (-5) + (2 * (-250) * p + (2 * 637 * (-5) + (0) * 9)) / (p ^ 2 - 637) = (-5) + 10 * ((-50) * p + (-637)) / (p ^ 2 - 637) := by ring

/-
I   637   VI
25 ... 12
 4 ...  9
 5 ... 17
-/

example :
    let step := fun (s : ℤ × ℤ × List (ℤ × Bool)) (q : ℤ) =>
      let m := q * s.2.1 - s.1
      let d := (637 - m ^ 2) / s.2.1
      (m, d, s.2.2 ++ [(d, (637 - m ^ 2) % s.2.1 == 0)])
    (([25, 4, 5] : List ℤ).foldl step (0, 1, [])).2.2 = [(12, true), (9, true), (17, true)] := by norm_num

/-
für p₁ = −101/4 (der zweite Näherungsbruch) wird x = 1235,
y = 31170.
-/

example : (-5 + 10 * (-50 * (-101 / 4) - 637) / ((-101 / 4) ^ 2 - 637) : ℚ) = 9 * 1235 := by norm_num

example : (31170 : ℚ) ^ 2 = 637 * (1235) ^ 2 + (0) * (1235) + (575) := by norm_num

end Beispiel13

end Kunerth1880.Paragraf21
