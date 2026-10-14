/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1878a.Beispiel02

/-
Seite 333.

2. Exempel. y² = −2266x² + 21521. (1)

Das Zahlenglied ist eine Primzahl von der Form 8n + 1.
-/
example : Nat.Prime 21521 := by norm_num

example : (21521 : ℤ) % 8 = 1 := by norm_num

/-
Seite 334.

Nach (IV₁): Δ² = −2266β² + 21521(α² + 2266); α² + 2266 = γ², γ + α =
103, γ − α = 22, somit α = 81/2, γ = 125/2, Δ = (125/2)d, β = (125/2)β₀;
setzt man diese Werthe ein und dividirt durch γ², so wird d² = −2266β₀²
+ 21521 ... (2)
-/
example : (125 / 2 : ℚ) + 81 / 2 = 103 := by norm_num

example : (125 / 2 : ℚ) - 81 / 2 = 22 := by norm_num

example : (81 / 2 : ℚ) ^ 2 + 2266 = (125 / 2) ^ 2 := by norm_num

example (β₀ : ℚ) :
    (-2266 * ((125 / 2) * β₀) ^ 2 + 21521 * ((81 / 2) ^ 2 + 2266)) /
      (125 / 2) ^ 2 = -2266 * β₀ ^ 2 + 21521 := by ring

/-
d = 2266z + r, β₀² = −2266z² − 2rz + 9 − (r² − 1127)/2266;

r = 689 ... 895
B = 209 ... 353

einsetzen:

β₀² = −2266z² − 1378z − 200 ... (3)

und

β₀² = −2266z² − 1790z − 344 ... (4);
-/
example (z r : ℚ) :
    (21521 - (2266 * z + r) ^ 2) / 2266 =
      -2266 * z ^ 2 - 2 * r * z + 9 - (r ^ 2 - 1127) / 2266 := by ring

example : ((689 : ℚ) ^ 2 - 1127) / 2266 = 209 := by norm_num

example : ((895 : ℚ) ^ 2 - 1127) / 2266 = 353 := by norm_num

example (z : ℚ) :
    -2266 * z ^ 2 - 2 * 689 * z + 9 - 209 = -2266 * z ^ 2 - 1378 * z - 200 := by
  ring

example (z : ℚ) :
    -2266 * z ^ 2 - 2 * 895 * z + 9 - 353 = -2266 * z ^ 2 - 1790 * z - 344 := by
  ring

/-
hier kann z keine ganze Zahl sein.
-/
example : ¬ ∃ z β₀ : ℤ, β₀ ^ 2 = -2266 * z ^ 2 - 1378 * z - 200 := by
  rintro ⟨z, β₀, h⟩
  have hz : z = 0 := by
    have hbounds : -1 < z ∧ z < 1 := by
      constructor <;> nlinarith [sq_nonneg β₀, sq_nonneg (z - 1), sq_nonneg (z + 1)]
    omega
  subst z
  nlinarith [sq_nonneg β₀]

example : ¬ ∃ z β₀ : ℤ, β₀ ^ 2 = -2266 * z ^ 2 - 1790 * z - 344 := by
  rintro ⟨z, β₀, h⟩
  have hz : z = 0 := by
    have hbounds : -1 < z ∧ z < 1 := by
      constructor <;> nlinarith [sq_nonneg β₀, sq_nonneg (z - 1), sq_nonneg (z + 1)]
    omega
  subst z
  nlinarith [sq_nonneg β₀]

/-
Aus (3) folgt nach (VI): L₁² = −200Δ₁² + 4·21521(β₁² + 200); β₁ = 5, β₁²
+ 200 = 15², L₁ = 30l₁, Δ₁ = 3d₁; einsetzen und durch 30² dividiren:

l₁² = −2d₁² + 21521; l₁ = 2z₁ + r₁; L₁ = 200(−2α₁) + 5·1378 = 2·30z₁ +
30·1 = 30l₁, somit l₁ = 2z₁ + 1 und d₁² = −2z₁² − 2z₁ + 10760; d₁ = 2d,,
, z₁ = 2z,, , durch 4 dividiren: d,,² = −2z,,² − z,, + 2690;
-/
example : (-1378 : ℤ) ^ 2 - 4 * (-2266) * (-200) = 4 * 21521 := by norm_num

example : (5 : ℚ) ^ 2 + 200 = 15 ^ 2 := by norm_num

example (d₁ : ℚ) :
    (-200 * (3 * d₁) ^ 2 + 4 * 21521 * (5 ^ 2 + 200)) / 30 ^ 2 =
      -2 * d₁ ^ 2 + 21521 := by ring

example (α₁ : ℚ) : 2 * (-200) * α₁ - (-1378) * 5 = 200 * (-2 * α₁) + 5 * 1378 := by
  ring

example (z₁ : ℚ) : 2 * 30 * z₁ + 30 * 1 = 30 * (2 * z₁ + 1) := by ring

example (z₁ : ℚ) :
    (21521 - (2 * z₁ + 1) ^ 2) / 2 = -2 * z₁ ^ 2 - 2 * z₁ + 10760 := by ring

example (z₂ : ℚ) :
    (-2 * (2 * z₂) ^ 2 - 2 * (2 * z₂) + 10760) / 4 =
      -2 * z₂ ^ 2 - z₂ + 2690 := by ring

/-
z,, = 4n und z,, = 3n sind auszuschliessen; für z,, = −10 wird d,, = 50,
z₁ = −20, l₁ = −39, L₁ = −1170, α₁ = 403/20; nimmt man aber β₁ = −5, so
wird α₁ = −143/10;
-/
example : ∀ z₂ d₂ : ZMod 8,
    d₂ ^ 2 = -2 * z₂ ^ 2 - z₂ + 2690 → z₂.val % 4 ≠ 0 := by decide

example : ∀ z₂ d₂ : ZMod 3,
    d₂ ^ 2 = -2 * z₂ ^ 2 - z₂ + 2690 → z₂ ≠ 0 := by decide

example : (-10 : ℤ) % 4 ≠ 0 ∧ (-10 : ℤ) % 3 ≠ 0 := by norm_num

example : (50 : ℚ) ^ 2 = -2 * (-10) ^ 2 - (-10) + 2690 := by norm_num

example : (2 : ℚ) * (-10) = -20 := by norm_num

example : (2 : ℚ) * (-20) + 1 = -39 := by norm_num

example : (30 : ℚ) * (-39) = -1170 := by norm_num

example : ((-1170 : ℚ) + (-1378) * 5) / (2 * (-200)) = 403 / 20 := by norm_num

example : ((-1170 : ℚ) + (-1378) * (-5)) / (2 * (-200)) = -143 / 10 := by norm_num

/-
also folgt aus (3): 100β₀² = (143z + 50)² − (607z + 150)(407z + 150) und
z = −150/407, daher β₀ = −110/407 = x, weil (2) mit (1) identisch ist.
-/
example (z : ℚ) :
    100 * (-2266 * z ^ 2 - 1378 * z - 200) =
      (143 * z + 50) ^ 2 - (607 * z + 150) * (407 * z + 150) := by ring

example : (407 : ℚ) * (-150 / 407) + 150 = 0 := by norm_num

example : ((143 : ℚ) * (-150 / 407) + 50) / 10 = -110 / 407 := by norm_num

example : (-110 / 407 : ℚ) ^ 2 =
    -2266 * (-150 / 407) ^ 2 - 1378 * (-150 / 407) - 200 := by norm_num

example : ((2266 : ℚ) * (-150 / 407) + 689) ^ 2 =
    -2266 * (-110 / 407) ^ 2 + 21521 := by norm_num

end Kunerth1878a.Beispiel02
