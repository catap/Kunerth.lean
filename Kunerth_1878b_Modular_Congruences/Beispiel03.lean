/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1878b.Beispiel03

/-
Seite 343.

3. Exempel. y² ≡ 127 (mod 239).

Der Modul ist kein quadratischer Rest von 127, wohl aber ist −239 ein
quadratischer Rest von 127 + 239 = 366 = 2·3·61; also dient als
Ausgangspunkt die Gleichung

y² = 239x + 366 und α = −239w(v + βw)/(v² − 366w²);
-/
example : ∀ r : Fin 127, (r.val : ℤ) ^ 2 % 127 ≠ 239 % 127 := by
  decide

example : (127 : ℤ) + 239 = 366 ∧ (366 : ℤ) = 2 * 3 * 61 := by
  norm_num

example : (35 : ℤ) ^ 2 % 366 = (-239) % 366 := by norm_num

/-
v² = 366w² − 239; v = 366z + r,

w² = 366z² + 2rz + (r² + 239)/366; r = 35, B = 4

w² = 366z² + 70z + 4,
-/
example (z r : ℚ) : ((366 * z + r) ^ 2 + 239) / 366 =
    366 * z ^ 2 + 2 * r * z + (r ^ 2 + 239) / 366 := by ring

example : ((35 : ℚ) ^ 2 + 239) / 366 = 4 := by norm_num

example (z : ℚ) : 366 * z ^ 2 + 2 * 35 * z +
    (35 ^ 2 + 239) / 366 = 366 * z ^ 2 + 70 * z + 4 := by ring

/-
für z = 0 wird w = 2, v = 35

α = 2(35 + 2β), β = −17, α = 2,
-/
example : (2 : ℚ) ^ 2 = 366 * 0 ^ 2 + 70 * 0 + 4 ∧
    (35 : ℚ) = 366 * 0 + 35 ∧
    (35 : ℚ) ^ 2 = 366 * 2 ^ 2 - 239 := by norm_num

example (β : ℚ) : -239 * 2 * (35 + β * 2) /
    (35 ^ 2 - 366 * 2 ^ 2) = 2 * (35 + 2 * β) := by ring

example : (2 : ℚ) * (35 + 2 * (-17)) = 2 := by norm_num

/-
y² = (2x − 17)² − (x − 77)(4x + 1) und x = 77, y = 137.
-/
example (x : ℚ) : 239 * x + 366 =
    (2 * x - 17) ^ 2 - (x - 77) * (4 * x + 1) := by ring

example : (77 : ℚ) - 77 = 0 ∧ (2 : ℚ) * 77 - 17 = 137 := by
  norm_num

example : (137 : ℤ) ^ 2 = 239 * 77 + 366 ∧
    (137 : ℤ) ^ 2 % 239 = 127 := by norm_num

end Kunerth1878b.Beispiel03
