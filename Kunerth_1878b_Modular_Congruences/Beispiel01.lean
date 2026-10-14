/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1878b.Beispiel01

/-
Seite 341.

1. Exempel. y² ≡ 1124 (mod 20521)

Der Modul ist ein quadratischer Rest von 1124 = 4·281, somit liegt der
Rechnung die Gleichung y² = 20521x + 1124 zu Grunde und es ist

α = −20521w(v + βw)/(v² − 1124w²);
-/
example : (1124 : ℤ) = 4 * 281 ∧
    (17 : ℤ) ^ 2 % 1124 = 20521 % 1124 := by norm_num

/-
v² = 1124w² + 20521, v = 1124z + r

w² = 1124z² + 2rz − 18 + (r² − 289)/1124;

r = 17, 579       w² = 1124z² + 34z − 18 (1)
B = 0, 298        w² = 1224z² + 1158z + 280 (2)
-/
example (z r : ℚ) : ((1124 * z + r) ^ 2 - 20521) / 1124 =
    1124 * z ^ 2 + 2 * r * z - 18 + (r ^ 2 - 289) / 1124 := by
  ring

example : ((17 : ℚ) ^ 2 - 289) / 1124 = 0 ∧
    ((579 : ℚ) ^ 2 - 289) / 1124 = 298 := by norm_num

example (z : ℚ) : ((1124 * z + 17) ^ 2 - 20521) / 1124 =
    1124 * z ^ 2 + 34 * z - 18 := by ring

/-
Vermutlicher Druckfehler: In (2) steht 1224 statt 1124. Die Einsetzung
von r = 579 in die vorstehende Gleichung ergibt 1124z² + 1158z + 280.
Die folgende Nachrechnung hält die Abweichung −100z² fest; für z = 0
stimmen beide Ausdrücke überein.
-/
example (z : ℚ) : ((1124 * z + 579) ^ 2 - 20521) / 1124 -
    (1224 * z ^ 2 + 1158 * z + 280) = -100 * z ^ 2 := by ring

/- Nachrechnung der vermuteten Berichtigung mit 1124. -/
example (z : ℚ) : ((1124 * z + 579) ^ 2 - 20521) / 1124 =
    1124 * z ^ 2 + 1158 * z + 280 := by ring

/-
Setzt man in (1) 2z = z₀, so folgt w² = 281z₀² + 17z₀ − 18; da sich hier
ein ganzzahliges z₀ nicht sofort finden lässt, so bilde man aus dieser
Gleichung nach (IV) für β₁ = 0 die derivirte Δ² = −72α₁² + 20521, Δ =
72z₁ + r₁,
-/
example (z₀ : ℚ) : 1124 * (z₀ / 2) ^ 2 + 34 * (z₀ / 2) - 18 =
    281 * z₀ ^ 2 + 17 * z₀ - 18 := by ring

example (α₁ : ℚ) : 4 * (0 ^ 2 + 18) * (281 - α₁ ^ 2) +
    (17 - 2 * α₁ * 0) ^ 2 = -72 * α₁ ^ 2 + 20521 := by ring

/-
Seite 342.

α₁² = −72z₁² − 2r₁z₁ + 285 − (r₁² − 1)/72;

r₁ = 1, 17, 19, 35
B = 0, 4, 5, 17;

man erhält nun das System der Gleichungen

α₁² = −72z₁² − 2z₁ + 285
  „ =      „ − 34z₁ + 281
  „ =      „ − 38z₁ + 280
  „ =      „ − 70z₁ + 268.
-/
example (z₁ r₁ : ℚ) : (20521 - (72 * z₁ + r₁) ^ 2) / 72 =
    -72 * z₁ ^ 2 - 2 * r₁ * z₁ + 285 - (r₁ ^ 2 - 1) / 72 := by
  ring

example : ((1 : ℚ) ^ 2 - 1) / 72 = 0 ∧
    ((17 : ℚ) ^ 2 - 1) / 72 = 4 ∧
    ((19 : ℚ) ^ 2 - 1) / 72 = 5 ∧
    ((35 : ℚ) ^ 2 - 1) / 72 = 17 := by norm_num

example (z₁ : ℚ) :
    (20521 - (72 * z₁ + 1) ^ 2) / 72 =
      -72 * z₁ ^ 2 - 2 * z₁ + 285 ∧
    (20521 - (72 * z₁ + 17) ^ 2) / 72 =
      -72 * z₁ ^ 2 - 34 * z₁ + 281 ∧
    (20521 - (72 * z₁ + 19) ^ 2) / 72 =
      -72 * z₁ ^ 2 - 38 * z₁ + 280 ∧
    (20521 - (72 * z₁ + 35) ^ 2) / 72 =
      -72 * z₁ ^ 2 - 70 * z₁ + 268 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-
Für z₁ = −2 wird in der ersten Gleichung α₁ = 1, somit ist w² = z₀² +
(40z₀ − 9)(7z₀ + 2) und z₀ = −2/7 = w, z = −1/7, v = 1005/7; nun wird α
= −2(1005 + 2β)/49 und aus der Congruenz 1005 + 2β ≡ 0 (mod 49) findet
man β = 12, somit α = −42 und y² = (42x − 12)² − (441x + 20)(4x − 49);
-/
example : (1 : ℚ) ^ 2 = -72 * (-2) ^ 2 - 2 * (-2) + 285 := by
  norm_num

example (z₀ : ℚ) : 281 * z₀ ^ 2 + 17 * z₀ - 18 =
    z₀ ^ 2 + (40 * z₀ - 9) * (7 * z₀ + 2) := by ring

example : (7 : ℚ) * (-2 / 7) + 2 = 0 ∧
    ((-2 : ℚ) / 7) ^ 2 = 281 * (-2 / 7) ^ 2 + 17 * (-2 / 7) - 18 ∧
    ((-2 : ℚ) / 7) / 2 = -1 / 7 ∧
    |1124 * ((-1 : ℚ) / 7) + 17| = 1005 / 7 := by norm_num

example (β : ℚ) : -20521 * (2 / 7) * (1005 / 7 + β * (2 / 7)) /
    ((1005 / 7) ^ 2 - 1124 * (2 / 7) ^ 2) =
      -2 / 49 * (1005 + 2 * β) := by ring

example : ((1005 : ℤ) + 2 * 12) % 49 = 0 ∧
    -(2 : ℚ) / 49 * (1005 + 2 * 12) = -42 := by norm_num

example (x : ℚ) : 20521 * x + 1124 =
    (42 * x - 12) ^ 2 - (441 * x + 20) * (4 * x - 49) := by ring

/-
es ist daher

x = 49/4, y = 1005/2 und nach [7] 4x = 20521q² − 2010q + 49,

da das letzte Trinom durch 4 theilbar sein muss, so besteht nach
Weglassung der Vielfachen von 4 die Congruenz q² − 2q + 1 ≡ 0 (mod 4);
somit ist q = 1, x = 4640, y = 9758.
-/
example : (4 : ℚ) * (49 / 4) - 49 = 0 ∧
    (42 : ℚ) * (49 / 4) - 12 = 1005 / 2 ∧
    ((1005 : ℚ) / 2) ^ 2 = 20521 * (49 / 4) + 1124 := by norm_num

example (q : ℚ) : 4 * ((20521 * q ^ 2 - 2010 * q + 49) / 4) =
    20521 * q ^ 2 - 2 * 1005 * q - (-49) := by ring

example (q : ℤ) : (20521 * q ^ 2 - 2010 * q + 49) % 4 =
    (q ^ 2 - 2 * q + 1) % 4 := by omega

example : ((1 : ℤ) ^ 2 - 2 * 1 + 1) % 4 = 0 ∧
    ((20521 : ℚ) * 1 ^ 2 - 2010 * 1 + 49) / 4 = 4640 ∧
    ((20521 : ℚ) * 1 - 1005) / 2 = 9758 := by norm_num

example : (9758 : ℤ) ^ 2 = 20521 * 4640 + 1124 ∧
    (9758 : ℤ) ^ 2 % 20521 = 1124 := by norm_num

/-
Hätte man die Gleichung (2) benützt, welche für z = 2z₀, w = 2w₀ und
nach Kürzung durch 4 in w₀² = 1124z₀² + 579z₀ + 70 übergeht, so stösst
man auch hier auf kein ganzzahliges z₀; daher nach (VI) L² = 70Δ² +
20521(β₁² − 70); für β₁ = 4, L = 3l, Δ = 3d wird nach Division durch 9:
l² = 70d² − 123126;

l = 70z₁ + r₁;

d² = 70z₁² + 2r₁z₁ + 1759 + (r₁² − 4)/70;

r₁ = 2, 12
B = 0, 2

also d² = 70z₁² + 4z₁ + 1759 und d² = 70z₁² + 24z₁ + 1761,
-/
/-
Zuordnung: Die angegebene Gleichung folgt aus (2), wenn dort der
vermutliche Druckfehler 1224 zu 1124 berichtigt wird. Mit dem
angegebenen Coefficienten 1224 verbleibt die Abweichung 100z₀².
-/
example (z₀ : ℚ) : (1224 * (2 * z₀) ^ 2 + 1158 * (2 * z₀) + 280) / 4 -
    (1124 * z₀ ^ 2 + 579 * z₀ + 70) = 100 * z₀ ^ 2 := by ring

/- Nachrechnung der vermuteten Berichtigung mit 1124. -/
example (z₀ : ℚ) : (1124 * (2 * z₀) ^ 2 + 1158 * (2 * z₀) + 280) / 4 =
    1124 * z₀ ^ 2 + 579 * z₀ + 70 := by ring

example : (579 : ℤ) ^ 2 - 4 * 1124 * 70 = 20521 := by norm_num

example (d : ℚ) : (70 * (3 * d) ^ 2 + 20521 * (4 ^ 2 - 70)) / 9 =
    70 * d ^ 2 - 123126 := by ring

example (z₁ r₁ : ℚ) : ((70 * z₁ + r₁) ^ 2 + 123126) / 70 =
    70 * z₁ ^ 2 + 2 * r₁ * z₁ + 1759 + (r₁ ^ 2 - 4) / 70 := by ring

example : ((2 : ℚ) ^ 2 - 4) / 70 = 0 ∧
    ((12 : ℚ) ^ 2 - 4) / 70 = 2 := by norm_num

example (z₁ : ℚ) :
    ((70 * z₁ + 2) ^ 2 + 123126) / 70 =
      70 * z₁ ^ 2 + 4 * z₁ + 1759 ∧
    ((70 * z₁ + 12) ^ 2 + 123126) / 70 =
      70 * z₁ ^ 2 + 24 * z₁ + 1761 := by constructor <;> ring

/-
die erste dieser Gleichungen, gibt für z₁ = 3: d = 49, l = 212, L = 636;
für β₁ = −4 wird α₁ = −12,

w₀² = (12z₀ + 4)² + (28z₀ + 9)(35z₀ + 6); also z₀ = −9/28,

w₀ = 1/7; z = −9/14, w = 2/7, v = 1005/7, wie oben.
-/
example : (49 : ℚ) ^ 2 = 70 * 3 ^ 2 + 4 * 3 + 1759 ∧
    (70 : ℚ) * 3 + 2 = 212 ∧ (3 : ℚ) * 212 = 636 ∧
    ((579 : ℚ) * (-4) + 636) / (2 * 70) = -12 := by norm_num

example (z₀ : ℚ) : 1124 * z₀ ^ 2 + 579 * z₀ + 70 =
    (12 * z₀ + 4) ^ 2 + (28 * z₀ + 9) * (35 * z₀ + 6) := by ring

example : (28 : ℚ) * (-9 / 28) + 9 = 0 ∧
    (12 : ℚ) * (-9 / 28) + 4 = 1 / 7 ∧
    (2 : ℚ) * (-9 / 28) = -9 / 14 ∧
    (2 : ℚ) * (1 / 7) = 2 / 7 ∧
    |1124 * ((-9 : ℚ) / 14) + 579| = 1005 / 7 := by norm_num

example : ((1005 : ℚ) / 7) ^ 2 = 1124 * (2 / 7) ^ 2 + 20521 := by
  norm_num

end Kunerth1878b.Beispiel01
