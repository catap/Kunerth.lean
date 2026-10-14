/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf20

/-
Seite 364
§. 20.

Ist a = μ²a₁ und der Bruch in VIII durch μ² gehoben; so
hat man √a₁ in einen Kettenbruch zu entwickeln und diesen mit
Rücksicht auf S,, zu benützen.
-/

example (μ a₁ v₁ w : ℤ) :
    (μ * v₁) ^ 2 - (μ ^ 2 * a₁) * w ^ 2 = μ ^ 2 * (v₁ ^ 2 - a₁ * w ^ 2) := by ring

namespace Beispiel11

/-
11. Exempel:
y² = 351x²+358x−697 = (27x+43)²−2(7x+19)(27x+67),
-/

example (x : ℚ) : 351 * x ^ 2 + 358 * x - 697 = (27 * x + 43) ^ 2 - 2 * (7 * x + 19) * (27 * x + 67) := by ring

/-
D = 64.17293, x = −67/27, y = −648/27,
27x = −67+216(−6p−173)/(p²−351), S₁ = 27D/8;
-/

example : (358 ^ 2 - 4 * 351 * (-697) : ℤ) = 64 * 17293 := by norm_num

example : (-648 / 27 : ℚ) ^ 2 = 351 * (-67 / 27) ^ 2 + (358) * (-67 / 27) + (-697) := by norm_num

example (p : ℚ) : (-67) + (2 * (-648) * p + (2 * 351 * (-67) + (358) * 27)) / (p ^ 2 - 351) = (-67) + 216 * ((-6) * p + (-173)) / (p ^ 2 - 351) := by ring

example : (27 ^ 2 * (64 * 17293) / 216 : ℚ) = 27 * (64 * 17293) / 8 := by norm_num

/-
I   351   VI
18 ... 27
-/

example :
    let step := fun (s : ℤ × ℤ × List (ℤ × Bool)) (q : ℤ) =>
      let m := q * s.2.1 - s.1
      let d := (351 - m ^ 2) / s.2.1
      (m, d, s.2.2 ++ [(d, (351 - m ^ 2) % s.2.1 == 0)])
    (([18] : List ℤ).foldl step (0, 1, [])).2.2 = [(27, true)] := by norm_num

/-
p = 18 entspricht nicht; ebenso wenig der eilfte Näherungsbruch
(an der eilften Stelle in VI steht auch 27).
-/

example : ((-67 + 216 * (-6 * 18 - 173) / (18 ^ 2 - 351)) / 27 : ℚ).den ≠ 1 := by norm_num

example :
    let step := fun (s : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × Bool) =>
      let (m, d, v₁, v₂, w₁, w₂, exactDivision) := s
      let q := (18 + m) / d
      let m' := q * d - m
      (m', (351 - m' ^ 2) / d, q * v₁ + v₂, v₁, q * w₁ + w₂, w₁,
        exactDivision && (351 - m' ^ 2) % d == 0)
    let (_, _, v, _, w, _, exactDivision) := (step^[11]) (0, 1, 1, 0, 0, 1, true)
    let p : ℚ := v / w
    ((-67 + 216 * (-6 * p - 173) / (p ^ 2 - 351)) / 27).den ≠ 1 ∧
      exactDivision = true := by
  norm_num [Function.iterate_succ_apply]

/-
Für p = 3p₁ wird 27x = −67+24(−18p₁−173)/(p₁²−39);
S¹,, = 3.8.17293,
-/

example (p : ℚ) : 216 * (-6 * (3 * p) - 173) * (p ^ 2 - 39) = 24 * (-18 * p - 173) * ((3 * p) ^ 2 - 351) := by ring

example : (27 ^ 2 * (64 * 17293) / (24 * 3 ^ 4) : ℚ) = 3 * 8 * 17293 := by norm_num

/-
Seite 365

I   39   VI
 6 ... 3
 4 ... 1
12 ... 3
 4 ... 1
-/

example :
    let step := fun (s : ℤ × ℤ × List (ℤ × Bool)) (q : ℤ) =>
      let m := q * s.2.1 - s.1
      let d := (39 - m ^ 2) / s.2.1
      (m, d, s.2.2 ++ [(d, (39 - m ^ 2) % s.2.1 == 0)])
    (([6, 4, 12, 4] : List ℤ).foldl step (0, 1, [])).2.2 = [(3, true), (1, true), (3, true), (1, true)] := by norm_num

/-
für p₁ = −306/49 ... +306/49 (der dritte Näherungsbruch) wird
x = 43103       203039
y = 807544      3803944 = (3.306/49)(203039+67/27)+648/27
nach IX in §. 5.
-/

example : (6 + 1 / (4 + 1 / (12)) : ℚ) = 306 / 49 := by norm_num

example : (-67 + 24 * (-18 * (-306 / 49) - 173) / ((-306 / 49) ^ 2 - 39) : ℚ) = 27 * 43103 := by norm_num

example : (807544 : ℚ) ^ 2 = 351 * (43103) ^ 2 + (358) * (43103) + (-697) := by norm_num

example : (-67 + 24 * (-18 * (306 / 49) - 173) / ((306 / 49) ^ 2 - 39) : ℚ) = 27 * 203039 := by norm_num

example : (3803944 : ℚ) ^ 2 = 351 * (203039) ^ 2 + (358) * (203039) + (-697) := by norm_num

example : ((3 * 306 / 49) * (203039 + 67 / 27) + 648 / 27 : ℚ) = 3803944 := by norm_num

end Beispiel11

end Kunerth1880.Paragraf20
