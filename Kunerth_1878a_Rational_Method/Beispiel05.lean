/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1878a.Beispiel05

/-
Seite 336.

5. Exempel. y² = 7499x² + 8501x + 2661 (1)

Die Determinante D = −7552355 = −5·1510471; der zweite Factor dürfte
eine Primzahl sein.
-/
example : (8501 : ℤ) ^ 2 - 4 * 7499 * 2661 = -7552355 := by norm_num

example : (-7552355 : ℤ) = -5 * 1510471 := by norm_num

/-
Für α = 0 ist nach (IV):

Δ² = 7499(2β)² − 7552355; Δ = 7499z + r,

eingesetzt:

(2β)² = 7499z² + 2rz + 1007 + (r² + 862)/7499;

durch Lösung der Congruenz r² + 862 ≡ 0 (mod 7499), deren Modul eine
Primzahl ist, findet man r = 1002 und B = 134; somit (2β)² = 7499z² +
2004z + 1141;
-/
example (β : ℚ) :
    4 * (7499 * β ^ 2 - 8501 * 0 * β + 2661 * 0 ^ 2) + 8501 ^ 2 - 4 * 7499 * 2661 =
      7499 * (2 * β) ^ 2 - 7552355 := by ring

example (z r : ℚ) :
    ((7499 * z + r) ^ 2 + 7552355) / 7499 =
      7499 * z ^ 2 + 2 * r * z + 1007 + (r ^ 2 + 862) / 7499 := by ring

example : Nat.Prime 7499 := by norm_num

example : ((1002 : ℤ) ^ 2 + 862) % 7499 = 0 := by norm_num

example : ((1002 : ℚ) ^ 2 + 862) / 7499 = 134 := by norm_num

example (z : ℚ) :
    7499 * z ^ 2 + 2 * 1002 * z + 1007 + ((1002 : ℚ) ^ 2 + 862) / 7499 =
      7499 * z ^ 2 + 2004 * z + 1141 := by ring

/-
z = 4n ist auszuschliessen; für z = −6 wird 2β = 509 und β = 509/2 = y.
-/
example : ∀ z v : ZMod 8,
    v ^ 2 = 7499 * z ^ 2 + 2004 * z + 1141 → z.val % 4 ≠ 0 := by decide

example : (-6 : ℤ) % 4 ≠ 0 := by norm_num

example : (509 : ℚ) ^ 2 = 7499 * (-6) ^ 2 + 2004 * (-6) + 1141 := by norm_num

example : (2 : ℚ) * (509 / 2) = 509 := by norm_num

/-
Führt man hier, obschon es nicht mehr nöthig ist, die Transformation
aus, so folgt:

4y² = 509² + (2x + 7)(14998x − 35491).
-/
example (x : ℚ) :
    4 * (7499 * x ^ 2 + 8501 * x + 2661) =
      509 ^ 2 + (2 * x + 7) * (14998 * x - 35491) := by ring

/-
Seite 337.

Leichter geht die Rechnung, wenn man in der nach (V) gebildeten
Gleichung K² = 7499Δ² − 7552355(α² − 7499) α = 87 setzt; da ist α² −
7499 = 70; für K = 5k, Δ = 5d folgt nach Kürzung durch 25:

k² = 7499d² − 21146594; k = 7499z + r,

d² = 7499z² + 2rz + 2820 + (r² − 586)/7499,

K = 7499(2β) − 87·8501 = 7499·5z − 5·937 = 5k,

also r = −937, eingesetzt:

d² = 7499z² − 1874z + 2937;
-/
example : (87 : ℚ) ^ 2 - 7499 = 70 := by norm_num

example (d : ℚ) :
    (7499 * (5 * d) ^ 2 - 7552355 * (87 ^ 2 - 7499)) / 25 =
      7499 * d ^ 2 - 21146594 := by ring

example (z r : ℚ) :
    ((7499 * z + r) ^ 2 + 21146594) / 7499 =
      7499 * z ^ 2 + 2 * r * z + 2820 + (r ^ 2 - 586) / 7499 := by ring

example (z : ℚ) : 7499 * 5 * z - 5 * 937 = 5 * (7499 * z - 937) := by ring

example : (((-937 : ℚ) ^ 2 - 586) / 7499) = 117 := by norm_num

example (z : ℚ) :
    7499 * z ^ 2 + 2 * (-937) * z + 2820 + ((-937 : ℚ) ^ 2 - 586) / 7499 =
      7499 * z ^ 2 - 1874 * z + 2937 := by ring

/-
z = 2n + 1, 5n, 9n sind unbrauchbar; bis 10 findet sich keine Zahl für
z.
-/
example : ∀ z d : ZMod 8,
    d ^ 2 = 7499 * z ^ 2 - 1874 * z + 2937 → z.val % 2 = 0 := by decide

example : ∀ z d : ZMod 5,
    d ^ 2 = 7499 * z ^ 2 - 1874 * z + 2937 → z ≠ 0 := by decide

example : ∀ z d : ZMod 9,
    d ^ 2 = 7499 * z ^ 2 - 1874 * z + 2937 → z ≠ 0 := by decide

example : (((List.range 21).map fun i => (i : ℤ) - 10).filter fun z =>
    let v := 7499 * z ^ 2 - 1874 * z + 2937
    (Nat.sqrt v.natAbs : ℤ) ^ 2 == v) =
    [] := by native_decide

/-
Also nach (V)
K₁² = 7499Δ₁² − 4·14·1510471(α₁² − 7499); für α₁ = 87 befindet sich im
Zahlengliede der Factor 28²; also K₁ = 28k₁, Δ₁ = 28d₁ und durch 28²
dividirt:

k₁² = 7499d₁² − 7552355 (2)

k₁ = 7499z₁ + r₁, K₁ = 7499(2β₁) − 87·1874 = 7499·28z₁ − 28·1002 = 28k₁,

somit k₁ = 7499z₁ − 1002; eingesetzt:

d₁² = 7499z₁² − 2004z₁ + 1141;

z₁ darf durch 4 nicht theilbar sein; für z₁ = +6 wird d₁ = 509 = 2y,
-/
/-
Vorzeichenfrage: In der vorangehenden Gleichung ist b = −1874.
Die Formel K₁ = 2aβ₁ − bα₁ ergibt daher für α₁ = 87 den Ausdruck
7499(2β₁) + 87·1874. Der gedruckte Ausdruck mit −87·1874 entspricht
dagegen α₁ = −87, wie es unten bei der Rückrechnung ausdrücklich
steht. Die Gleichung für K₁² enthält nur α₁² und unterscheidet diese
Vorzeichen nicht. Die drei gedruckten Angaben bleiben erhalten;
eine eindeutige Berichtigung wird daraus nicht abgeleitet.
-/
example (β₁ : ℚ) :
    2 * 7499 * β₁ - (-1874) * 87 = 7499 * (2 * β₁) + 87 * 1874 := by ring

example (β₁ : ℚ) :
    2 * 7499 * β₁ - (-1874) * (-87) = 7499 * (2 * β₁) - 87 * 1874 := by ring

example : (-1874 : ℤ) ^ 2 - 4 * 7499 * 2937 = -4 * 14 * 1510471 := by norm_num

example (d₁ : ℚ) :
    (7499 * (28 * d₁) ^ 2 - 4 * 14 * 1510471 * (87 ^ 2 - 7499)) / 28 ^ 2 =
      7499 * d₁ ^ 2 - 7552355 := by ring

example (z₁ : ℚ) : 7499 * 28 * z₁ - 28 * 1002 = 28 * (7499 * z₁ - 1002) := by ring

example (z₁ : ℚ) :
    ((7499 * z₁ - 1002) ^ 2 + 7552355) / 7499 =
      7499 * z₁ ^ 2 - 2004 * z₁ + 1141 := by ring

example : ∀ z₁ d₁ : ZMod 8,
    d₁ ^ 2 = 7499 * z₁ ^ 2 - 2004 * z₁ + 1141 → z₁.val % 4 ≠ 0 := by decide

example : (6 : ℤ) % 4 ≠ 0 := by norm_num

example : (509 : ℚ) ^ 2 = 7499 * 6 ^ 2 - 2004 * 6 + 1141 := by norm_num

/-
weil die Gleichung (2) aus (1) entsteht, wenn dort x = (k₁ −
8501)/(2·7499) gesetzt wird.
-/
example (k₁ : ℚ) :
    4 * 7499 * (7499 * ((k₁ - 8501) / (2 * 7499)) ^ 2 +
      8501 * ((k₁ - 8501) / (2 * 7499)) + 2661) = k₁ ^ 2 + 7552355 := by ring

/-
Würde davon abgesehen die Rechnung fortgesetzt werden, so fände man k₁ =
43992, K₁ = 1231776 und für α₁ = −87 ist β₁ = 93, also d² = (87z − 93)²
− 14(z − 204)(5z − 2); z = 2/5, k = 10313/5, K = 10313, β = 50 und

y² = (87x + 50)² − (35x − 23)(2x + 7).
-/
example : (7499 : ℚ) * 6 - 1002 = 43992 := by norm_num

example : (28 : ℚ) * 43992 = 1231776 := by norm_num

example : ((1231776 : ℚ) + (-1874) * (-87)) / (2 * 7499) = 93 := by norm_num

example : (7499 : ℚ) * (2 * 93) - 87 * 1874 =
    7499 * 28 * 6 - 28 * 1002 := by norm_num

example (z : ℚ) :
    7499 * z ^ 2 - 1874 * z + 2937 =
      (87 * z - 93) ^ 2 - 14 * (z - 204) * (5 * z - 2) := by ring

example : (5 : ℚ) * (2 / 5) - 2 = 0 := by norm_num

example : (7499 : ℚ) * (2 / 5) - 937 = 10313 / 5 := by norm_num

example : (5 : ℚ) * (10313 / 5) = 10313 := by norm_num

example : ((10313 : ℚ) + 87 * 8501) / (2 * 7499) = 50 := by norm_num

example (x : ℚ) :
    7499 * x ^ 2 + 8501 * x + 2661 =
      (87 * x + 50) ^ 2 - (35 * x - 23) * (2 * x + 7) := by ring

end Kunerth1878a.Beispiel05
