/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf22

/-
Seite 366
§. 22.

Wenn a = μ²a₁, x = m/n und n prim gegen μ ist, in Folge
dessen der Bruch in VIII durch μ² nicht gehoben werden kann
(§. 9), so lässt sich die Theilbarkeit dadurch herbeiführen,
dass man die Congruenz −np + α₁ ≡ 0 (mod μ) nach p auflöst,
-/

example (n μ α₁ : ℤ) (hcop : Int.gcd n μ = 1) :
    ∃ p : ℤ, μ ∣ -n * p + α₁ := by
  have h := Int.gcd_eq_gcd_ab n μ
  rw [hcop] at h
  norm_num at h
  refine ⟨α₁ * Int.gcdA n μ, α₁ * Int.gcdB n μ, ?_⟩
  linear_combination α₁ * h

/-
hierauf α = −np + α₁ möglichst nahe an √a bestimmt,
dessgleichen β = mp + β₁, die Differenz (αx + β)² − (ax² + bx + c)
durch nx − m dividirt und aus dem Quotienten die neue p-Function
bildet.
-/

/-
Seite 367

Im letzten Exempel ist 637 = 7².13, x = 5/2, α = −2p+25,
β = 5p+5; also −2p+25 ≡ 0 (mod 7), daraus p = 7q+2,
α = −14q+21, β = 35q+15, für q = 0 wird α = 21, β = 15,
-/

example : (637 : ℤ) = 7 ^ 2 * 13 := by norm_num

example (q : ℚ) : -2 * (7 * q + 2) + 25 = -14 * q + 21 := by ring

example (q : ℚ) : 5 * (7 * q + 2) + 5 = 35 * q + 15 := by ring

/-
(21x+15)²−(637x²+575) = −14(14x²−45x+25); dividirt
man dieses Trinom durch 2x−5, so ist 7x−5 der Quotus,
-/

example (x : ℚ) : (21 * x + 15) ^ 2 - (637 * x ^ 2 + 575) = -14 * (14 * x ^ 2 - 45 * x + 25) := by ring

example (x : ℚ) : 14 * x ^ 2 - 45 * x + 25 = (2 * x - 5) * (7 * x - 5) := by ring

/-
x = 5/7, y = 210/7 und 7x = 5+10(42p+637)/(p²−637)
= 5+10(6p₁+13)/(p₁²−13), S¹,, = −10.13.23
-/

example : (210 / 7 : ℚ) ^ 2 = 637 * (5 / 7) ^ 2 + (0) * (5 / 7) + (575) := by norm_num

example (p : ℚ) : 10 * (42 * (7 * p) + 637) * (p ^ 2 - 13) = 10 * (6 * p + 13) * ((7 * p) ^ 2 - 637) := by ring

example : (7 ^ 2 * (-4 * 637 * 575) / (10 * 7 ^ 4) : ℚ) = -10 * 13 * 23 := by norm_num

/-
I   13   VI
3 ... 4
1 ... 3
1 ... 3
1     4
1 ... 1
-/

example :
    let step := fun (s : ℤ × ℤ × List (ℤ × Bool)) (q : ℤ) =>
      let m := q * s.2.1 - s.1
      let d := (13 - m ^ 2) / s.2.1
      (m, d, s.2.2 ++ [(d, (13 - m ^ 2) % s.2.1 == 0)])
    (([3, 1, 1, 1, 1] : List ℤ).foldl step (0, 1, [])).2.2 = [(4, true), (3, true), (3, true), (4, true), (1, true)] := by norm_num

/-
für p₁ = 18/5 (der fünfte Näherungsbruch)
wird x = −1235.
-/

example : (3 + 1 / (1 + 1 / (1 + 1 / (1 + 1 / (1)))) : ℚ) = 18 / 5 := by norm_num

example : (5 + 10 * (6 * (18 / 5) + 13) / ((18 / 5) ^ 2 - 13) : ℚ) = 7 * (-1235) := by norm_num

end Kunerth1880.Paragraf22
