/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1878a.Beispiel01

/-
Seite 333.

1 Exempel. y² = 331x² + 21193.

Das Zahlenglied ist eine Primzahl von der Form 8n + 1.
-/
example : Nat.Prime 21193 := by norm_num

example : (21193 : ℤ) % 8 = 1 := by norm_num

/-
Nach (IV₁): Δ² = 331β² + 21193(α² − 331); für α = 18 wird Δ² = 331β² −
148351; Δ = 331z + r, β² = 331z² + 2rz + 448 + (r² + 63)/331, r = 54,
der Bruch B = 9, somit β² = 331z² + 108z + 457;
-/
example : (18 : ℚ) ^ 2 - 331 = -7 := by norm_num

example : (21193 : ℚ) * (18 ^ 2 - 331) = -148351 := by norm_num

example (z r : ℚ) :
    ((331 * z + r) ^ 2 + 148351) / 331 =
      331 * z ^ 2 + 2 * r * z + 448 + (r ^ 2 + 63) / 331 := by ring

example : ((54 : ℚ) ^ 2 + 63) / 331 = 9 := by norm_num

example (z : ℚ) :
    331 * z ^ 2 + 2 * 54 * z + 448 + ((54 : ℚ) ^ 2 + 63) / 331 =
      331 * z ^ 2 + 108 * z + 457 := by ring

/-
die Formen z = 4n + 2, 5n, 11n sind unbrauchbar; bis 11 gibt es für z
keine Zahl.
-/
example : ∀ z β : ZMod 8,
    β ^ 2 = 331 * z ^ 2 + 108 * z + 457 → z.val % 4 ≠ 2 := by decide

example : ∀ z β : ZMod 5,
    β ^ 2 = 331 * z ^ 2 + 108 * z + 457 → z ≠ 0 := by decide

example : ∀ z β : ZMod 11,
    β ^ 2 = 331 * z ^ 2 + 108 * z + 457 → z ≠ 0 := by decide

example : (((List.range 23).map fun i => (i : ℤ) - 11).filter fun z =>
    let v := 331 * z ^ 2 + 108 * z + 457
    (Nat.sqrt v.natAbs : ℤ) ^ 2 == v) =
    [] := by native_decide

/-
Aus der letzten Gleichung folgt nach (V): K₁² = 331Δ₁² − 593404(α₁² −
331); α₁ = 19, K₁ = 2k₁, Δ₁ = 2d₁, durch 4 dividirt: k₁² = 331d₁² −
4450530; k₁ = 331z₁ + r₁; K₁ = 331(2β₁) − 19·108 = 331(2β₁ − 6) − 66 =
2k₁; somit k₁ = 331z₁ − 33, β₁ − 3 = z₁ und d₁² = 331z₁² − 66z₁ + 13449;
-/
example : (108 : ℤ) ^ 2 - 4 * 331 * 457 = -593404 := by norm_num

example : ((-593404 : ℚ) * (19 ^ 2 - 331)) / 4 = -4450530 := by norm_num

example (d₁ : ℚ) :
    (331 * (2 * d₁) ^ 2 - 593404 * (19 ^ 2 - 331)) / 4 =
      331 * d₁ ^ 2 - 4450530 := by ring

example (β₁ : ℚ) :
    331 * (2 * β₁) - 19 * 108 = 331 * (2 * β₁ - 6) - 66 := by ring

example (z₁ : ℚ) :
    ((331 * z₁ - 33) ^ 2 + 4450530) / 331 =
      331 * z₁ ^ 2 - 66 * z₁ + 13449 := by ring

/-
hier ist z₁ = 2n, für z₁ = +2 wird d₁ = 121, β₁ = 5 und β² = (19z + 5)²
− (10z + 54)(3z − 8),
-/
example : ∀ z₁ d₁ : ZMod 8,
    d₁ ^ 2 = 331 * z₁ ^ 2 - 66 * z₁ + 13449 → z₁.val % 2 = 0 := by decide

example : (2 : ℤ) % 2 = 0 := by norm_num

example : (121 : ℚ) ^ 2 = 331 * 2 ^ 2 - 66 * 2 + 13449 := by norm_num

example : (5 : ℚ) - 3 = 2 := by norm_num

example (z : ℚ) :
    331 * z ^ 2 + 108 * z + 457 =
      (19 * z + 5) ^ 2 - (10 * z + 54) * (3 * z - 8) := by ring

/-
daher z = +8/3, β = ±167/3 und 9y² = (54x − 167)² + (21x + 5816)(3x +
28)¹.
-/
example : (3 : ℚ) * (8 / 3) - 8 = 0 := by norm_num

example : (19 : ℚ) * (8 / 3) + 5 = 167 / 3 := by norm_num

example : (167 / 3 : ℚ) ^ 2 = 331 * (8 / 3) ^ 2 + 108 * (8 / 3) + 457 := by
  norm_num

example : (-167 / 3 : ℚ) ^ 2 = 331 * (8 / 3) ^ 2 + 108 * (8 / 3) + 457 := by
  norm_num

example (x : ℚ) :
    9 * (331 * x ^ 2 + 21193) =
      (54 * x - 167) ^ 2 + (21 * x + 5816) * (3 * x + 28) := by ring

/-
¹ Diese Transformation geschieht derart, dass man nach Bestimmung der
Grössen α und β das Trinom (a − α²)x² + (b − 2αβ)x + (c − β²) in das
Product (γx + δ)(εx + ζ) verwandelt. Ist η² die Determinante des
Trinoms, die hier immer ein Quadrat sein muss, so setze man b − 2αβ + η
= 2p, b − 2αβ − η = 2q und px + qx anstatt (b − 2αβ)x, worauf die
Verwandlung des Trinoms in ein Product sofort ausgeführt werden kann.
-/

example (b α β η x : ℚ) :
    ((b - 2 * α * β + η) / 2) * x + ((b - 2 * α * β - η) / 2) * x =
      (b - 2 * α * β) * x := by ring

example (a b c α β η : ℚ)
    (hη : η ^ 2 = (b - 2 * α * β) ^ 2 - 4 * (a - α ^ 2) * (c - β ^ 2)) :
    ((b - 2 * α * β + η) / 2) * ((b - 2 * α * β - η) / 2) =
      (a - α ^ 2) * (c - β ^ 2) := by nlinarith [hη]

end Kunerth1878a.Beispiel01
