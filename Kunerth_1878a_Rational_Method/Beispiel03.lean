/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1878a.Beispiel03

/-
Seite 334.

3. Exempel. y² = 199x² − 229x + 434.

Nach (V): K² = 199Δ² − 293023(α² − 199); für α = 13 folgt:

K² = 199Δ² + 8790690; K = 199z + r;

Δ² = 199z² + 2rz − 44174 + (r² − 64)/199; r = 8,
-/
example : (-229 : ℤ) ^ 2 - 4 * 199 * 434 = -293023 := by norm_num

example : (-293023 : ℚ) * (13 ^ 2 - 199) = 8790690 := by norm_num

example (z r : ℚ) :
    ((199 * z + r) ^ 2 - 8790690) / 199 =
      199 * z ^ 2 + 2 * r * z - 44174 + (r ^ 2 - 64) / 199 := by ring

example : ((8 : ℚ) ^ 2 - 64) / 199 = 0 := by norm_num

/-
Seite 335.

somit Δ² = 199z² + 16z − 44174; z = 2n + 1 und z > 14; für z = −15 wird
Δ = 19, K = 2977, β = 0 und

y² = 169x² + (2x − 7)(15x − 62).
-/
/-
Abweichungen im Druck: Der eingesetzte Werth z = −15 erfüllt die
angegebene Grenze z > 14 nicht. Diese wird nicht stillschweigend
als Grenze für |z| gelesen. Aus K = 199z + 8 folgt K = −2977;
der folgende Werth K = +2977 ist die andere Quadratwurzel, mit
welcher die Rechnung β = 0 ergibt. Dieser Vorzeichenwechsel wird
im Wortlaut nicht erläutert.
-/
example : ¬ (-15 : ℤ) > 14 ∧ (199 : ℤ) * (-15) + 8 = -2977 := by
  norm_num

example (z : ℚ) :
    199 * z ^ 2 + 2 * 8 * z - 44174 + ((8 : ℚ) ^ 2 - 64) / 199 =
      199 * z ^ 2 + 16 * z - 44174 := by ring

example : ∀ z Δ : ZMod 8,
    Δ ^ 2 = 199 * z ^ 2 + 16 * z - 44174 → z.val % 2 = 1 := by decide

example : (-15 : ℤ) % 2 = 1 := by norm_num

example : (19 : ℚ) ^ 2 = 199 * (-15) ^ 2 + 16 * (-15) - 44174 := by norm_num

example : (2977 : ℚ) ^ 2 = 199 * 19 ^ 2 + 8790690 := by norm_num

example : ((2977 : ℚ) + (-229) * 13) / (2 * 199) = 0 := by norm_num

example (x : ℚ) :
    199 * x ^ 2 - 229 * x + 434 = 169 * x ^ 2 + (2 * x - 7) * (15 * x - 62) := by ring

/-
Für α = 14 wird K² = 199Δ² + 879069; K = 199z + r,

Δ² = 199z² + 2rz − 4417 + (r² − 86)/199;

K = 199(2β) + 14·229 = 199(2β + 16) + 22,

somit r = 22, 2β + 16 = z und Δ² = 199z² + 44z − 4415;
-/
example : (-293023 : ℚ) * (14 ^ 2 - 199) = 879069 := by norm_num

example (z r : ℚ) :
    ((199 * z + r) ^ 2 - 879069) / 199 =
      199 * z ^ 2 + 2 * r * z - 4417 + (r ^ 2 - 86) / 199 := by ring

example (β : ℚ) : 199 * (2 * β) + 14 * 229 = 199 * (2 * β + 16) + 22 := by ring

example : ((22 : ℚ) ^ 2 - 86) / 199 = 2 := by norm_num

example (z : ℚ) :
    199 * z ^ 2 + 2 * 22 * z - 4417 + ((22 : ℚ) ^ 2 - 86) / 199 =
      199 * z ^ 2 + 44 * z - 4415 := by ring

/-
z = 4n + 2 ist unbrauchbar; z > 4, für z = +9 wird Δ = 110, β = −7/2 und
4y² = (28x − 7)² + (6x − 241)(2x − 7).
-/
example : ∀ z Δ : ZMod 8,
    Δ ^ 2 = 199 * z ^ 2 + 44 * z - 4415 → z.val % 4 ≠ 2 := by decide

example : (9 : ℤ) % 4 ≠ 2 ∧ (9 : ℤ) > 4 := by norm_num

example : (110 : ℚ) ^ 2 = 199 * 9 ^ 2 + 44 * 9 - 4415 := by norm_num

example : (2 : ℚ) * (-7 / 2) + 16 = 9 := by norm_num

example (x : ℚ) :
    4 * (199 * x ^ 2 - 229 * x + 434) =
      (28 * x - 7) ^ 2 + (6 * x - 241) * (2 * x - 7) := by ring

end Kunerth1878a.Beispiel03
