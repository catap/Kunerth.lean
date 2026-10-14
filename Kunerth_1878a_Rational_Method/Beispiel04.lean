/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1878a.Beispiel04

/-
Seite 335.

4. Exempel. y² = −11x² − 63x + 131 (1)

Die Determinante D = 9733 ist eine Primzahl.
-/
example : (-63 : ℤ) ^ 2 - 4 * (-11) * 131 = 9733 := by norm_num

example : Nat.Prime 9733 := by norm_num

/-
Nach (V): K² = −11Δ² + 9733(α² + 11); für α = 1, K = 2k, Δ = 2d wird:

k² = −11d² + 29199; k = 11z + r, K = 11(−2β) + 1·63 = 11·2z + 8 = 2k,
also k = 11z + 4, eingesetzt: d² = −11z² − 8z + 2653;
-/
example (d : ℚ) :
    (-11 * (2 * d) ^ 2 + 9733 * (1 ^ 2 + 11)) / 4 = -11 * d ^ 2 + 29199 := by ring

example (β : ℚ) : 2 * (-11) * β - (-63) * 1 = 11 * (-2 * β) + 1 * 63 := by ring

example (z : ℚ) : 11 * 2 * z + 8 = 2 * (11 * z + 4) := by ring

example (z : ℚ) :
    (29199 - (11 * z + 4) ^ 2) / 11 = -11 * z ^ 2 - 8 * z + 2653 := by ring

/-
z = 4n + 2, für z = +6 wird d = 47, k = 70, K = 140,

β = (140 − 1·63)/(2(−11)) = −7/2 und

4y² = (2x − 7)² − (4x + 25)(12x − 19).
-/
example : ∀ z d : ZMod 8,
    d ^ 2 = -11 * z ^ 2 - 8 * z + 2653 → z.val % 4 = 2 := by decide

example : (6 : ℤ) % 4 = 2 := by norm_num

example : (47 : ℚ) ^ 2 = -11 * 6 ^ 2 - 8 * 6 + 2653 := by norm_num

example : (11 : ℚ) * 6 + 4 = 70 := by norm_num

example : (2 : ℚ) * 70 = 140 := by norm_num

example : ((140 : ℚ) - 1 * 63) / (2 * (-11)) = -7 / 2 := by norm_num

example (x : ℚ) :
    4 * (-11 * x ^ 2 - 63 * x + 131) =
      (2 * x - 7) ^ 2 - (4 * x + 25) * (12 * x - 19) := by ring

/-
Hätte man oben α² + 11 = γ² gesetzt, so wäre α = 5, γ = 6, also K = 6k,
Δ = 6d, durch 36 dividirt:

k² = −11d² + 9733 (2)

k = 11z + r, K = 11(−2β) + 5·63 = 11·6z + 18 = 6k also k = 11z + 3,
eingesetzt: d² = −11z² − 6z + 884;
-/
example : (5 : ℚ) ^ 2 + 11 = 6 ^ 2 := by norm_num

example (d : ℚ) :
    (-11 * (6 * d) ^ 2 + 9733 * (5 ^ 2 + 11)) / 36 = -11 * d ^ 2 + 9733 := by ring

example (β : ℚ) : 2 * (-11) * β - (-63) * 5 = 11 * (-2 * β) + 5 * 63 := by ring

example (z : ℚ) : 11 * 6 * z + 18 = 6 * (11 * z + 3) := by ring

example (z : ℚ) :
    (9733 - (11 * z + 3) ^ 2) / 11 = -11 * z ^ 2 - 6 * z + 884 := by ring

/-
hier darf z keine ungerade Zahl sein; somit d = 2δ, z = 2ζ und durch 4
dividirt: δ² = −11ζ² − 3ζ + 221 eine in ganzen Zahlen unmögliche
Gleichung; also nach (VI):
-/
example : ∀ z d : ZMod 8,
    d ^ 2 = -11 * z ^ 2 - 6 * z + 884 → z.val % 2 = 0 := by decide

example (ζ : ℚ) :
    (-11 * (2 * ζ) ^ 2 - 6 * (2 * ζ) + 884) / 4 = -11 * ζ ^ 2 - 3 * ζ + 221 := by ring

example : ¬ ∃ ζ δ : ℤ, δ ^ 2 = -11 * ζ ^ 2 - 3 * ζ + 221 := by
  rintro ⟨ζ, δ, h⟩
  have hζ : -5 < ζ ∧ ζ < 5 := by
    constructor <;> nlinarith [sq_nonneg δ, sq_nonneg (ζ - 5), sq_nonneg (ζ + 5)]
  have hδ : -15 < δ ∧ δ < 15 := by
    constructor <;> nlinarith [sq_nonneg (22 * ζ + 3), sq_nonneg (δ - 15), sq_nonneg (δ + 15)]
  obtain ⟨hζlo, hζhi⟩ := hζ
  obtain ⟨hδlo, hδhi⟩ := hδ
  interval_cases ζ <;> interval_cases δ <;> norm_num at h

/-
Seite 336.

L₁² = 221Δ₁² + 9733(β₁² − 221); β₁ = 15, L₁ = 2l₁, Δ₁ = 2d₁, durch 4
dividirt: l₁² = 221d₁² + 9733, l₁ = 221z₁ + r₁

d₁² = 221z₁² + 2r₁z₁ − 44 + (r₁² − 9)/221;

r₁ = 3, 88
B = 0, 35

somit d₁² = 221z₁² + 6z₁ − 44

und

d₁² = 221z₁² + 176z₁ − 9;
-/
example : (-3 : ℤ) ^ 2 - 4 * (-11) * 221 = 9733 := by norm_num

example (d₁ : ℚ) :
    (221 * (2 * d₁) ^ 2 + 9733 * (15 ^ 2 - 221)) / 4 = 221 * d₁ ^ 2 + 9733 := by ring

example (z₁ r₁ : ℚ) :
    ((221 * z₁ + r₁) ^ 2 - 9733) / 221 =
      221 * z₁ ^ 2 + 2 * r₁ * z₁ - 44 + (r₁ ^ 2 - 9) / 221 := by ring

example : ((3 : ℚ) ^ 2 - 9) / 221 = 0 := by norm_num

example : ((88 : ℚ) ^ 2 - 9) / 221 = 35 := by norm_num

example (z₁ : ℚ) :
    221 * z₁ ^ 2 + 2 * 3 * z₁ - 44 + ((3 : ℚ) ^ 2 - 9) / 221 =
      221 * z₁ ^ 2 + 6 * z₁ - 44 := by ring

example (z₁ : ℚ) :
    221 * z₁ ^ 2 + 2 * 88 * z₁ - 44 + ((88 : ℚ) ^ 2 - 9) / 221 =
      221 * z₁ ^ 2 + 176 * z₁ - 9 := by ring

/-
in dieser Gleichung wird für z₁ = −1, d₁ = 6, l₁ = 133, L₁ = 266, α₁ =
1/2 und 4δ² = (ζ + 30)² − (15ζ + 4)(3ζ + 4), also ζ = −4/3, z = −8/3, k
= −79/3 und d = 86/3 = 2y,
-/
/-
Vorzeichenwahl: Aus l₁ = 221z₁ + r₁ mit z₁ = −1 und r₁ = 88 folgt
l₁ = −133. Der Text verwendet anschliessend die positive Wurzel 133
und damit L₁ = 266. Die Quadratgleichung lässt beide Vorzeichen zu;
die folgenden Rechnungen prüfen die gewählte positive Wurzel, keine
unveränderte Fortsetzung der vorzeichenbehafteten Substitution.
-/
example : (221 : ℚ) * (-1) + 88 = -133 := by norm_num

example : (-133 : ℚ) ^ 2 = 133 ^ 2 := by norm_num

example : (6 : ℚ) ^ 2 = 221 * (-1) ^ 2 + 176 * (-1) - 9 := by norm_num

example : (133 : ℚ) ^ 2 = 221 * 6 ^ 2 + 9733 := by norm_num

example : (2 : ℚ) * 133 = 266 := by norm_num

example : ((266 : ℚ) + (-3) * 15) / (2 * 221) = 1 / 2 := by norm_num

example (ζ : ℚ) :
    4 * (-11 * ζ ^ 2 - 3 * ζ + 221) =
      (ζ + 30) ^ 2 - (15 * ζ + 4) * (3 * ζ + 4) := by ring

example : (3 : ℚ) * (-4 / 3) + 4 = 0 := by norm_num

example : (2 : ℚ) * (-4 / 3) = -8 / 3 := by norm_num

example : (11 : ℚ) * (-8 / 3) + 3 = -79 / 3 := by norm_num

example : (86 / 3 : ℚ) ^ 2 = -11 * (-8 / 3) ^ 2 - 6 * (-8 / 3) + 884 := by norm_num

example : (86 / 3 : ℚ) = 2 * (43 / 3) := by norm_num

/-
weil für x = (k − 63)/22 die Gleichung (1) in k² = −11(2y)² + 9733
übergeht, die mit (2) identisch ist; somit y = 43/3, x = −134/3; für k =
+79/3 wird x = −5/3.
-/
example (k : ℚ) :
    -11 * ((k - 63) / 22) ^ 2 - 63 * ((k - 63) / 22) + 131 =
      (9733 - k ^ 2) / 44 := by ring

/-
Vermutlicher Druckfehler: Bei x = −134/3 fehlt eine 3 im Nenner.
Aus k = −79/3 und x = (k − 63)/22 folgt x = −134/33.
Die Abweichungen und das berichtigte Wurzelpaar werden getrennt geprüft.
-/
example : ((-79 / 3 : ℚ) - 63) / 22 ≠ -134 / 3 := by norm_num

example : (43 / 3 : ℚ) ^ 2 ≠ -11 * (-134 / 3) ^ 2 - 63 * (-134 / 3) + 131 := by
  norm_num

example : ((-79 / 3 : ℚ) - 63) / 22 = -134 / 33 := by norm_num

example : (43 / 3 : ℚ) ^ 2 = -11 * (-134 / 33) ^ 2 - 63 * (-134 / 33) + 131 := by norm_num

example : ((79 / 3 : ℚ) - 63) / 22 = -5 / 3 := by norm_num

example : (43 / 3 : ℚ) ^ 2 = -11 * (-5 / 3) ^ 2 - 63 * (-5 / 3) + 131 := by norm_num

end Kunerth1878a.Beispiel04
