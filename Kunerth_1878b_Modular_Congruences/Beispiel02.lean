/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1878b.Beispiel02

/-
Seite 343.

2. Exempel. y² ≡ 16315 (mod 21433)

Der Modul 21433 ist ein quadratischer Rest von 16315 − 21433 = −5118 =
−2·3·853, daher bildet die Gleichung y² = 21433x − 5118 die Grundlage
der Rechnung und

α = −21433w(v + βw)/(v + 5118w²)
-/
example : (16315 : ℤ) - 21433 = -5118 ∧
    (-5118 : ℤ) = -2 * 3 * 853 := by norm_num

example : (31 : ℤ) ^ 2 % 5118 = 21433 % 5118 := by norm_num

/-
v² = −5118w² + 21433; für w = 2 wird v = 31,

α = −2(31 + 2β); β = −16, α = 2 und
-/
example : (31 : ℚ) ^ 2 = -5118 * 2 ^ 2 + 21433 := by norm_num

/-
Vermutlicher Druckfehler: Im Nenner der ersten Formel fehlt das Quadrat
bei v. Mit v = 31, w = 2 und β = −16 ergibt der angegebene Nenner
v + 5118w² nicht α = 2.
-/
example : -(21433 : ℚ) * 2 * (31 + (-16) * 2) /
    (31 + 5118 * 2 ^ 2) ≠ 2 := by norm_num

/- Nachrechnung der vermuteten Berichtigung mit v² + 5118w². -/
example : -(21433 : ℚ) * 2 * (31 + (-16) * 2) /
    (31 ^ 2 + 5118 * 2 ^ 2) = 2 := by norm_num

example : -(2 : ℚ) * (31 + 2 * (-16)) = 2 := by norm_num

/-
y² = (2x − 16)² − (x − 5374)(4x − 1), somit x = 5374, y = 10732.
-/
example (x : ℚ) : 21433 * x - 5118 =
    (2 * x - 16) ^ 2 - (x - 5374) * (4 * x - 1) := by ring

example : (5374 : ℚ) - 5374 = 0 ∧
    (2 : ℚ) * 5374 - 16 = 10732 := by norm_num

example : (10732 : ℤ) ^ 2 = 21433 * 5374 - 5118 := by norm_num

example : (10732 : ℤ) ^ 2 % 21433 = 16315 := by norm_num

end Kunerth1878b.Beispiel02
