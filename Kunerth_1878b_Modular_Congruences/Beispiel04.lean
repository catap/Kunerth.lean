/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1878b.Beispiel04

/-
Seite 343.

4. Exempel. y² ≡ 4163 (mod 19139)
                 d          b

Der Modul ist ein quadratischer Rest von d − 2b = −34115 = −5·6823,
somit ist y² = 19139x − 34115 die erste Grundgleichung und
-/
example : (4163 : ℤ) - 2 * 19139 = -34115 ∧
    (-34115 : ℤ) = -5 * 6823 := by norm_num

/-
α = −19139w(v + βw)/(v² + 34115w²); v² = −34115w² + 19139,

v = 34115z + r, w² = −34115z² − 2rz − (r² − 19139)/34115;
-/
example (z r : ℚ) : (19139 - (34115 * z + r) ^ 2) / 34115 =
    -34115 * z ^ 2 - 2 * r * z - (r ^ 2 - 19139) / 34115 := by ring

/-
Seite 344.

r² ≡ 19139 (mod 6823·5), r² ≡ 19139 (mod 6823);

der Modul 6823 ist ein quadratischer Rest von

19139 − 2·6823 = 5493, somit r² = 6823ρ + 5493

die zweite Grundgleichung und

α₁ = −6823w₁(v₁ + β₁w₁)/(v₁² − 5493w₁²); v₁² = 5493w₁² + 6823,

v₁ = 5493z₁ + r₁, w₁² = 5493z₁² + 2r₁z₁ − 1 + (r₁² − 1330)/5493;
-/
example : (19139 : ℤ) - 2 * 6823 = 5493 ∧ (5493 : ℤ) = 1831 * 3 := by
  norm_num

example (z₁ r₁ : ℚ) : ((5493 * z₁ + r₁) ^ 2 - 6823) / 5493 =
    5493 * z₁ ^ 2 + 2 * r₁ * z₁ - 1 + (r₁ ^ 2 - 1330) / 5493 := by ring

/-
r₁² ≡ 1330 (mod 1831·3); hier ist r₁² = 1831ρ₁ + 1330 die dritte
Grundgleichung und

α,, = −1831w,,(v,, + β,,w,,)/(v,,² − 1330w,,²); v,,² = 1330w,,² + 1831,

v,,² = 1330z,, + r,, ,
-/
/-
Vermutlicher Druckfehler: Bei der Einsetzung steht v,,² statt v,,.
Die später angegebenen Werthe z,, = 0 und v,, = r,, = 331 erfüllen
die angegebene Gleichung mit v,,² nicht.
-/
example : (331 : ℚ) ^ 2 ≠ 1330 * 0 + 331 := by norm_num

/- Nachrechnung der vermuteten Berichtigung v,, = 1330z,, + r,,. -/
example : (331 : ℚ) = 1330 * 0 + 331 := by norm_num

/-
w,,² = 1330z,,² + 2r,,z,, − 1 + (r,,² − 501)/1330; r,,² ≡ 501 (mod
2·5·7·19)

somit r,, = 201, 331, 369, 429
B = 30, 82, 102, 138

und w,,² = 1330z,,² + 662z,, + 81;
-/
example : (1330 : ℤ) = 2 * 5 * 7 * 19 := by norm_num

example (z₂ r₂ : ℚ) : ((1330 * z₂ + r₂) ^ 2 - 1831) / 1330 =
    1330 * z₂ ^ 2 + 2 * r₂ * z₂ - 1 + (r₂ ^ 2 - 501) / 1330 := by ring

example : ((201 : ℚ) ^ 2 - 501) / 1330 = 30 ∧
    ((331 : ℚ) ^ 2 - 501) / 1330 = 82 ∧
    ((369 : ℚ) ^ 2 - 501) / 1330 = 102 ∧
    ((429 : ℚ) ^ 2 - 501) / 1330 = 138 := by norm_num

example (z₂ : ℚ) : ((1330 * z₂ + 331) ^ 2 - 1831) / 1330 =
    1330 * z₂ ^ 2 + 662 * z₂ + 81 := by ring

/-
für z,, = 0 wird w,, = 9, v,, = 331, α,, = −9(331 + 9β,,); β,, = −36,
α,, = −63 und

r₁² = (63ρ₁ + 36)² − (49ρ₁ + 34)(81ρ₁ − 1), somit ρ₁ = −34/49, r₁ = 54/7
-/
example : (9 : ℚ) ^ 2 = 1330 * 0 ^ 2 + 662 * 0 + 81 ∧
    (331 : ℚ) ^ 2 = 1330 * 9 ^ 2 + 1831 := by norm_num

example (β₂ : ℚ) : -1831 * 9 * (331 + β₂ * 9) /
    (331 ^ 2 - 1330 * 9 ^ 2) = -9 * (331 + 9 * β₂) := by ring

example : -(9 : ℚ) * (331 + 9 * (-36)) = -63 := by norm_num

example (ρ₁ : ℚ) : 1831 * ρ₁ + 1330 =
    (63 * ρ₁ + 36) ^ 2 - (49 * ρ₁ + 34) * (81 * ρ₁ - 1) := by ring

example : (49 : ℚ) * (-34 / 49) + 34 = 0 ∧
    |63 * ((-34 : ℚ) / 49) + 36| = 54 / 7 ∧
    ((54 : ℚ) / 7) ^ 2 = 1831 * (-34 / 49) + 1330 := by norm_num

/-
und 49ρ₁ = 1831p² − 108p − 34 ≡ 0 (mod 49) oder (p − 3)² ≡ 0 (mod 49),
also p = 3, ρ₁ = 329 und r₁ ≡ 777 (mod 5493);

daher r₁ = 1054, 2608
B = 202, 1238

und w₁² = 5493z₁² + 2108z₁ + 201 (1),
w₁² = 5493z₁² + 5216z₁ + 1237 (2),
-/
example : ∀ p : ZMod 49,
    1831 * p ^ 2 - 108 * p - 34 = 0 ↔ (p - 3) ^ 2 = 0 := by decide

example : ((3 : ℤ) - 3) ^ 2 % 49 = 0 ∧
    ((1831 : ℚ) * 3 ^ 2 - 108 * 3 - 34) / 49 = 329 ∧
    ((1831 : ℚ) * 3 - 54) / 7 = 777 ∧
    (777 : ℚ) ^ 2 = 1831 * 329 + 1330 := by norm_num

/-
Vermutlicher Druckfehler: Beim Werthe 777 steht der Modul 5493 statt
1831. Aus der dritten Grundgleichung folgt die Congruenz mit dem
Modul 1831; für den angegebenen Modul 5493 ist 777 keine Wurzel.
-/
example : (777 : ℤ) ^ 2 % 5493 ≠ 1330 := by norm_num

/-
Nachrechnung mit dem Modul 1831. Die anschließend angegebenen Werthe
1054 und 2608 sind 1831 − 777 und 1831 + 777; ihre Quadrate werden
danach beim Modul 5493 geprüft.
-/
example : (777 : ℤ) ^ 2 % 1831 = 1330 ∧
    (1054 : ℤ) = 1831 - 777 ∧ (2608 : ℤ) = 1831 + 777 := by norm_num

example : (1054 : ℤ) ^ 2 % 5493 = 1330 ∧
    (2608 : ℤ) ^ 2 % 5493 = 1330 ∧
    ((1054 : ℚ) ^ 2 - 1330) / 5493 = 202 ∧
    ((2608 : ℚ) ^ 2 - 1330) / 5493 = 1238 := by norm_num

example (z₁ : ℚ) :
    ((5493 * z₁ + 1054) ^ 2 - 6823) / 5493 =
      5493 * z₁ ^ 2 + 2108 * z₁ + 201 ∧
    ((5493 * z₁ + 2608) ^ 2 - 6823) / 5493 =
      5493 * z₁ ^ 2 + 5216 * z₁ + 1237 := by constructor <;> ring

/-
in (1) ist z₁ = 4n, bis z₁ = 20 findet sich nichts! (2) ist in ganzen
Zahlen unmöglich.
-/
example (z₁ w₁ : ℤ) (h : w₁ ^ 2 = 5493 * z₁ ^ 2 + 2108 * z₁ + 201) :
    ∃ n : ℤ, z₁ = 4 * n := by
  have hz₀ : 0 ≤ z₁ % 8 := Int.emod_nonneg _ (by norm_num)
  have hz₈ : z₁ % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
  have hw₀ : 0 ≤ w₁ % 8 := Int.emod_nonneg _ (by norm_num)
  have hw₈ : w₁ % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
  have hm := congrArg (fun t : ℤ => t % 8) h
  have hm' : (w₁ % 8) ^ 2 % 8 =
      (5493 * (z₁ % 8) ^ 2 + 2108 * (z₁ % 8) + 201) % 8 := by
    simpa only [pow_two, Int.add_emod, Int.mul_emod, Int.emod_emod] using hm
  have hz : z₁ % 4 = 0 := by
    interval_cases hz : z₁ % 8 <;> interval_cases hw : w₁ % 8 <;>
      norm_num at hm' <;> omega
  exact Int.dvd_of_emod_eq_zero hz

example : ([-20, -16, -12, -8, -4, 0, 4, 8, 12, 16, 20] : List ℤ).all
    (fun z₁ => let n := 5493 * z₁ ^ 2 + 2108 * z₁ + 201
      decide ((Nat.sqrt n.toNat : ℤ) ^ 2 ≠ n)) = true := by native_decide

example : ∀ z₁ w₁ : ZMod 8,
    w₁ ^ 2 = 5493 * z₁ ^ 2 + 5216 * z₁ + 1237 → z₁ = 2 ∨ z₁ = 6 := by decide

/-
Auf Seite 339 sollen gefundene v₀ und w₀ beim Einsetzen positiv
genommen werden; im obigen Satz ist jedoch keine Beschränkung auf
nichtnegative z₁ angegeben. Eine solche wird hier nicht hinzugefügt.
-/
example : Prop :=
  ¬ ∃ z₁ w₁ : ℤ, w₁ ^ 2 = 5493 * z₁ ^ 2 + 5216 * z₁ + 1237

/-
Aus (1) folgt: L² = 201Δ² + 4·6823(β₀² − 201); β₀ = 15, L = 4l, Δ = 4d,
durch 16 dividirt:

l² = 201d² + 40938; l = 201z₀ + r₀;

d² = 201z₀² + 2r₀z₀ − 203 + (r₀² − 135)/201; r₀ = 66, B = 21
-/
example : (2108 : ℤ) ^ 2 - 4 * 5493 * 201 = 4 * 6823 := by norm_num

example (d : ℚ) : (201 * (4 * d) ^ 2 + 4 * 6823 * (15 ^ 2 - 201)) / 16 =
    201 * d ^ 2 + 40938 := by ring

example (z₀ r₀ : ℚ) : ((201 * z₀ + r₀) ^ 2 - 40938) / 201 =
    201 * z₀ ^ 2 + 2 * r₀ * z₀ - 203 + (r₀ ^ 2 - 135) / 201 := by ring

example : ((66 : ℚ) ^ 2 - 135) / 201 = 21 := by norm_num

/-
Seite 345.

d² = 201z₀² + 132z₀ − 182; in ganzen Zahlen unmöglich;
-/
example (z₀ : ℚ) : ((201 * z₀ + 66) ^ 2 - 40938) / 201 =
    201 * z₀ ^ 2 + 132 * z₀ - 182 := by ring

example : ¬ ∃ z₀ d : ℤ, d ^ 2 = 201 * z₀ ^ 2 + 132 * z₀ - 182 := by
  rintro ⟨z₀, d, h⟩
  have hm := congrArg (fun t : ℤ => (t : ZMod 8)) h
  push_cast at hm
  have residues : ∀ z d : ZMod 8, d ^ 2 ≠ 201 * z ^ 2 + 132 * z - 182 := by decide
  exact residues _ _ hm

/-
somit L₁² = −182Δ₁² + 24·6823(β₂² + 182), β₂ = 2, L₁ = 4l,, , Δ₁ = 4d₁
durch 16 dividirt:

l₁² = −182d₁² + 1903617; l₁ = 182z₂ + r₂;

d₁² = −182z₂² − 2r₂z₂ + 10459 − (r₂² − 79)/182;
r₂ = 25, 53
B = 3, 15

hiemit d₁² = −182z₂² − 50z₂ + 10456 und
d₁² = −182z₂² − 106z₂ + 10444
-/
/-
Lesart und Zuordnung: Bei L₁ = 4l,, stehen zwei tiefgestellte
Kommata; die nächste Gleichung verwendet dagegen l₁. Die folgende
Nachrechnung folgt diesem l₁ und der Zuordnung L₁ = 4l₁.
-/
example : (132 : ℤ) ^ 2 - 4 * 201 * (-182) = 24 * 6823 := by norm_num

example (d₁ : ℚ) :
    (-182 * (4 * d₁) ^ 2 + 24 * 6823 * (2 ^ 2 + 182)) / 16 =
      -182 * d₁ ^ 2 + 1903617 := by ring

example (z₂ r₂ : ℚ) : (1903617 - (182 * z₂ + r₂) ^ 2) / 182 =
    -182 * z₂ ^ 2 - 2 * r₂ * z₂ + 10459 - (r₂ ^ 2 - 79) / 182 := by ring

example : ((25 : ℚ) ^ 2 - 79) / 182 = 3 ∧
    ((53 : ℚ) ^ 2 - 79) / 182 = 15 := by norm_num

example (z₂ : ℚ) :
    (1903617 - (182 * z₂ + 25) ^ 2) / 182 =
      -182 * z₂ ^ 2 - 50 * z₂ + 10456 ∧
    (1903617 - (182 * z₂ + 53) ^ 2) / 182 =
      -182 * z₂ ^ 2 - 106 * z₂ + 10444 := by constructor <;> ring

/-
die erste dieser Gleichungen liefert für z₂ = −4, d₁ = 88, l₁ = −703, L₁
= −2812, α₂ = 7 und

d² = (7z₀ + 2)² + 2(2z₀ + 3)(38z₀ − 31);

z₀ = −3/2, d = −19/2, l = −471/2, L = −942;

für β₀ = −15 wird α₀ = −81,
-/
example : (88 : ℚ) ^ 2 = -182 * (-4) ^ 2 - 50 * (-4) + 10456 ∧
    (182 : ℚ) * (-4) + 25 = -703 ∧
    (4 : ℚ) * (-703) = -2812 ∧
    ((132 : ℚ) * 2 + (-2812)) / (2 * (-182)) = 7 := by norm_num

example (z₀ : ℚ) : 201 * z₀ ^ 2 + 132 * z₀ - 182 =
    (7 * z₀ + 2) ^ 2 + 2 * (2 * z₀ + 3) * (38 * z₀ - 31) := by ring

example : (2 : ℚ) * (-3 / 2) + 3 = 0 := by norm_num

/-
Vermutlicher Druckfehler: Für z₀ = −3/2 gibt der Factor 7z₀ + 2
den Werth −17/2 statt des angegebenen −19/2. Das Quadrat von −19/2
erfüllt die vorstehende Gleichung nicht.
-/
example : ((-19 : ℚ) / 2) ^ 2 ≠ 201 * (-3 / 2) ^ 2 + 132 * (-3 / 2) - 182 := by
  norm_num

/- Nachrechnung der vermuteten Berichtigung d = −17/2. -/
example : (7 : ℚ) * (-3 / 2) + 2 = -17 / 2 ∧
    ((-17 : ℚ) / 2) ^ 2 = 201 * (-3 / 2) ^ 2 + 132 * (-3 / 2) - 182 := by norm_num

example : (201 : ℚ) * (-3 / 2) + 66 = -471 / 2 ∧
    (4 : ℚ) * (-471 / 2) = -942 ∧
    ((2108 : ℚ) * (-15) + (-942)) / (2 * 201) = -81 := by norm_num

/-
w₁² = (81z₁ + 15)² − 2(89z₁ + 12)(6z₁ + 1); somit z₁ = −1/6,

w₁ = 3/2, v₁ = 277/2, α₁ = −3(277 + 3β₁)/4, β₁ = −91, α₁ = −3

und r² = (3ρ + 91)² − (ρ − 697)(9ρ − 4); ρ = 697, und r ≡ 2182 (mod
6823), somit
-/
example (z₁ : ℚ) : 5493 * z₁ ^ 2 + 2108 * z₁ + 201 =
    (81 * z₁ + 15) ^ 2 - 2 * (89 * z₁ + 12) * (6 * z₁ + 1) := by ring

example : (6 : ℚ) * (-1 / 6) + 1 = 0 ∧
    (81 : ℚ) * (-1 / 6) + 15 = 3 / 2 ∧
    (5493 : ℚ) * (-1 / 6) + 1054 = 277 / 2 ∧
    ((277 : ℚ) / 2) ^ 2 = 5493 * (3 / 2) ^ 2 + 6823 := by norm_num

example (β₁ : ℚ) :
    -6823 * (3 / 2) * (277 / 2 + β₁ * (3 / 2)) /
      ((277 / 2) ^ 2 - 5493 * (3 / 2) ^ 2) = -3 / 4 * (277 + 3 * β₁) := by
  ring

example : -(3 : ℚ) / 4 * (277 + 3 * (-91)) = -3 := by norm_num

example (ρ : ℚ) : 6823 * ρ + 5493 =
    (3 * ρ + 91) ^ 2 - (ρ - 697) * (9 * ρ - 4) := by ring

example : (3 : ℚ) * 697 + 91 = 2182 ∧
    (2182 : ℤ) ^ 2 % 6823 = 19139 % 6823 := by norm_num

/-
r = 2182, 15828
B = 139, 7343;

w² = −34115z² − 4364z − 139 (1)
w² = −34115z² − 31656z − 7343 (2)

in ganzen Zahlen unmöglich.
-/
example : (2182 : ℤ) ^ 2 % 34115 = 19139 ∧
    (15828 : ℤ) ^ 2 % 34115 = 19139 ∧
    ((2182 : ℚ) ^ 2 - 19139) / 34115 = 139 ∧
    ((15828 : ℚ) ^ 2 - 19139) / 34115 = 7343 := by norm_num

example (z : ℚ) :
    (19139 - (34115 * z + 2182) ^ 2) / 34115 =
      -34115 * z ^ 2 - 4364 * z - 139 ∧
    (19139 - (34115 * z + 15828) ^ 2) / 34115 =
      -34115 * z ^ 2 - 31656 * z - 7343 := by constructor <;> ring

example : ¬ ∃ z w : ℤ, w ^ 2 = -34115 * z ^ 2 - 4364 * z - 139 := by
  rintro ⟨z, w, h⟩
  rcases (show 0 ≤ z ∨ z ≤ -1 by omega) with hz | hz
  · nlinarith [sq_nonneg z, sq_nonneg w]
  · have hsq : -z ≤ z ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ -z by omega) (show 0 ≤ -z - 1 by omega)]
    nlinarith [sq_nonneg w]

example : ¬ ∃ z w : ℤ, w ^ 2 = -34115 * z ^ 2 - 31656 * z - 7343 := by
  rintro ⟨z, w, h⟩
  rcases (show 0 ≤ z ∨ z ≤ -1 by omega) with hz | hz
  · nlinarith [sq_nonneg z, sq_nonneg w]
  · have hsq : -z ≤ z ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ -z by omega) (show 0 ≤ -z - 1 by omega)]
    nlinarith [sq_nonneg w]

/-
Somit aus (1) L,,² = −139Δ,,² + 4·19139(β₃² + 139); β₃ = 1, L,, = 4l,, ,
Δ,, = 4d,, und durch 16 abgekürzt,

l,,² = −139d,,² + 669865; l,, = 139z₃ + r₃,

d,,² = −139z₃² − 2r₃z₃ + 4819 − (r₃² − 24)/139; r₃ = 21, B = 3,

d,,² = −139z₃² − 42z₃ + 4816;

da hier z₃ gerade sein muss, so setze man d,, = 2d,,, , z₃ = 2z₄ und
dividire durch 4 d,,,² = −139z₄² − 21z₄ + 1204;
-/
example : (-4364 : ℤ) ^ 2 - 4 * (-34115) * (-139) = 4 * 19139 := by
  norm_num

example (d₂ : ℚ) :
    (-139 * (4 * d₂) ^ 2 + 4 * 19139 * (1 ^ 2 + 139)) / 16 =
      -139 * d₂ ^ 2 + 669865 := by ring

example (z₃ r₃ : ℚ) : (669865 - (139 * z₃ + r₃) ^ 2) / 139 =
    -139 * z₃ ^ 2 - 2 * r₃ * z₃ + 4819 - (r₃ ^ 2 - 24) / 139 := by ring

example : ((21 : ℚ) ^ 2 - 24) / 139 = 3 := by norm_num

example (z₃ : ℚ) : (669865 - (139 * z₃ + 21) ^ 2) / 139 =
    -139 * z₃ ^ 2 - 42 * z₃ + 4816 := by ring

example (z₃ d₂ : ℤ) (h : d₂ ^ 2 = -139 * z₃ ^ 2 - 42 * z₃ + 4816) :
    Even z₃ := by
  have hz₀ : 0 ≤ z₃ % 8 := Int.emod_nonneg _ (by norm_num)
  have hz₈ : z₃ % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
  have hd₀ : 0 ≤ d₂ % 8 := Int.emod_nonneg _ (by norm_num)
  have hd₈ : d₂ % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
  have hm := congrArg (fun t : ℤ => t % 8) h
  have hm' : (d₂ % 8) ^ 2 % 8 =
      (-139 * (z₃ % 8) ^ 2 - 42 * (z₃ % 8) + 4816) % 8 := by
    simpa only [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, Int.emod_emod] using hm
  have hz : z₃ % 2 = 0 := by
    interval_cases hz : z₃ % 8 <;> interval_cases hd : d₂ % 8 <;>
      norm_num at hm' <;> omega
  exact even_iff_two_dvd.mpr (Int.dvd_of_emod_eq_zero hz)

example (z₄ : ℚ) : (-139 * (2 * z₄) ^ 2 - 42 * (2 * z₄) + 4816) / 4 =
    -139 * z₄ ^ 2 - 21 * z₄ + 1204 := by ring

/-
für z₄ = −3

Seite 346.

wird d,,, = 4, z₃ = −6, l,, = −813, L,, = −3252, für β₁ = −1 wird α₁ =
−4, somit

w² = (4z + 1)² − (1101z + 70)(31z + 2) und z = −2/31,

w = 23/31, v = 588/31,
-/
example : (4 : ℚ) ^ 2 = -139 * (-3) ^ 2 - 21 * (-3) + 1204 ∧
    (2 : ℚ) * (-3) = -6 ∧ (139 : ℚ) * (-6) + 21 = -813 ∧
    (4 : ℚ) * (-813) = -3252 ∧
    ((-4364 : ℚ) * (-1) + (-3252)) / (2 * (-139)) = -4 := by norm_num

example (z : ℚ) : -34115 * z ^ 2 - 4364 * z - 139 =
    (4 * z + 1) ^ 2 - (1101 * z + 70) * (31 * z + 2) := by ring

example : (31 : ℚ) * (-2 / 31) + 2 = 0 ∧
    (4 : ℚ) * (-2 / 31) + 1 = 23 / 31 ∧
    |34115 * ((-2 : ℚ) / 31) + 2182| = 588 / 31 ∧
    ((588 : ℚ) / 31) ^ 2 = -34115 * (23 / 31) ^ 2 + 19139 := by norm_num

/-
α = −23(588 + 23β)/31²; für β = 58 ist α = −46 und y² = (46x − 58)² −
(4x − 39)(529x − 961), also

x = 39/4, y = 781/2 und 4x = 19139q² − 1562q + 39 ≡ 0 (mod 4),

oder (q + 1)² ≡ 0 (mod 4), somit s = +1, x = 4404, y = 9179.
-/
example (β : ℚ) :
    -19139 * (23 / 31) * (588 / 31 + β * (23 / 31)) /
      ((588 / 31) ^ 2 + 34115 * (23 / 31) ^ 2) =
        -23 / 31 ^ 2 * (588 + 23 * β) := by ring

example : -(23 : ℚ) / 31 ^ 2 * (588 + 23 * 58) = -46 := by norm_num

example (x : ℚ) : 19139 * x - 34115 =
    (46 * x - 58) ^ 2 - (4 * x - 39) * (529 * x - 961) := by ring

example : (4 : ℚ) * (39 / 4) - 39 = 0 ∧
    (46 : ℚ) * (39 / 4) - 58 = 781 / 2 ∧
    ((781 : ℚ) / 2) ^ 2 = 19139 * (39 / 4) - 34115 := by norm_num

example : ∀ q : ZMod 4,
    19139 * q ^ 2 - 1562 * q + 39 = 0 ↔ (q + 1) ^ 2 = 0 := by decide

/-
Zuordnung: Die folgende Rechnung setzt q = 1; im Wortlaut steht s = +1.
-/
example : ((1 : ℤ) + 1) ^ 2 % 4 = 0 ∧
    ((19139 : ℚ) * 1 ^ 2 - 1562 * 1 + 39) / 4 = 4404 ∧
    ((19139 : ℚ) * 1 - 781) / 2 = 9179 := by norm_num

example : (9179 : ℤ) ^ 2 = 19139 * 4404 - 34115 ∧
    (9179 : ℤ) ^ 2 % 19139 = 4163 := by norm_num

end Kunerth1878b.Beispiel04
