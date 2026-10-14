/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf08

/-
Seite 33.

§. 8.
Auffindung neuer Werthe der Unbekannten.

1. Kennt man für die Gleichung y² = ax² + b zwei Werthe von x, deren
einer auch Null sein kann, so lassen sich mit denselben oft neue Werthe
von x, und wenn b eine Primzahl und a positiv ist, in beliebiger Anzahl
finden.
-/

example : Prop :=
  ∀ (a : ℤ) (b : ℕ) (x₁ y₁ x₂ y₂ : ℤ),
    0 < a → b.Prime → x₁ ≠ x₂ →
    y₁ ^ 2 = a * x₁ ^ 2 + b → y₂ ^ 2 = a * x₂ ^ 2 + b →
    Set.Infinite {x : ℤ | ∃ y : ℤ, y ^ 2 = a * x ^ 2 + b}

/-
Es seien x₁, y₁ und x₁₁, y₁₁ zwei Paare bekannter Wurzeln dieser
Gleichung, so ist die p-Function für

x = x₁ − 2(y₁p − ax₁)/(p² − a) ... (ρ);
-/

example (a x x₁ y₁ p : ℚ) :
    (p * (x - x₁) + y₁) ^ 2 - (a * (x ^ 2 - x₁ ^ 2) + y₁ ^ 2) =
      (x - x₁) * ((p ^ 2 - a) * (x - x₁) + 2 * (y₁ * p - a * x₁)) := by ring

/-
setzt man p = y₁₁/x₁₁, so geht (ρ) über in

x = x₁ − 2(y₁y₁₁ − ax₁x₁₁)x₁₁/b. (A)
-/

example (a b x₁ y₁ x₂ y₂ : ℚ) (hx₂ : x₂ ≠ 0) (hb : b ≠ 0)
    (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) :
    x₁ - 2 * (y₁ * (y₂ / x₂) - a * x₁) / ((y₂ / x₂) ^ 2 - a) =
      x₁ - 2 * (y₁ * y₂ - a * x₁ * x₂) / b * x₂ := by
  have hd : (y₂ / x₂) ^ 2 - a = b / x₂ ^ 2 := by
    field_simp
    nlinarith [h₂]
  rw [hd]
  field_simp

/-
Der Annahme zufolge ist:

y₁² = ax₁² + b, y₁₁² = ax₁₁² + b,

und nach vollzogener Multiplication beider Gleichungen ist

y₁²y₁₁² − a²x₁²x₁₁² = ab(x₁² + x₁₁²) + b²
-/

example (a b x₁ y₁ x₂ y₂ : ℚ)
    (h₁ : y₁ ^ 2 = a * x₁ ^ 2 + b) (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) :
    y₁ ^ 2 * y₂ ^ 2 - a ^ 2 * x₁ ^ 2 * x₂ ^ 2 =
      a * b * (x₁ ^ 2 + x₂ ^ 2) + b ^ 2 := by
  rw [h₁, h₂]
  ring

/-
oder

(y₁y₁₁ + ax₁x₁₁)(y₁y₁₁ − ax₁x₁₁) = b[a(x₁² + x₁₁²) + b];
-/

example (a b x₁ y₁ x₂ y₂ : ℚ)
    (h₁ : y₁ ^ 2 = a * x₁ ^ 2 + b) (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) :
    (y₁ * y₂ + a * x₁ * x₂) * (y₁ * y₂ - a * x₁ * x₂) =
      b * (a * (x₁ ^ 2 + x₂ ^ 2) + b) := by
  calc
    _ = y₁ ^ 2 * y₂ ^ 2 - a ^ 2 * x₁ ^ 2 * x₂ ^ 2 := by ring
    _ = _ := by rw [h₁, h₂]; ring

/-
ist b eine Primzahl, so muss einer der linksstehenden binomischen
Factoren und somit auch der Zähler des Bruches in (A), welcher

Seite 34.

diese zwei Binome repräsentirt, je nachdem man

p = +y₁₁/x₁₁ oder = −y₁₁/x₁₁

gesetzt hat, durch b theilbar sein; in diesem Falle wird für x stets
eine ganze Zahl und zugleich ein neuer Werth erhalten.
-/

example (a b x₁ x₂ y₁ y₂ : ℤ)
    (hb : b.natAbs.Prime) (_hbpos : 0 < b) (h₁ : y₁ ^ 2 = a * x₁ ^ 2 + b)
    (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) :
    b ∣ y₁ * y₂ + a * x₁ * x₂ ∨ b ∣ y₁ * y₂ - a * x₁ * x₂ := by
  apply (Int.prime_iff_natAbs_prime.mpr hb).dvd_or_dvd
  refine ⟨a * (x₁ ^ 2 + x₂ ^ 2) + b, ?_⟩
  calc
    _ = y₁ ^ 2 * y₂ ^ 2 - a ^ 2 * x₁ ^ 2 * x₂ ^ 2 := by ring
    _ = _ := by rw [h₁, h₂]; ring

example (b x₁ x₂ t : ℤ) (hb : b ≠ 0) (ht : b ∣ t) :
    ∃ x : ℤ, (x : ℚ) = x₁ - 2 * (t : ℚ) / b * x₂ := by
  obtain ⟨k, hk⟩ := ht
  refine ⟨x₁ - 2 * k * x₂, ?_⟩
  rw [hk]
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  push_cast
  field_simp

/-
Wäre b jedoch ein Product, so kann es vorkommen, dass ein Factor von b
in y₁y₁₁ + ax₁x₁₁, der zweite aber in y₁y₁₁ − ax₁x₁₁ enthalten ist, und
dann liefert jene Substitution keinen ganzzahligen Werth für x.

In dieser Rechnung muss das zweite Glied des Nenners p² − a, d. i. die
Zahl a der Coëfficient von x² sein; wäre jedoch die p-Function durch ν²
abgekürzt worden, so müsste der Bruch y₁₁/x₁₁ durch ν dividirt werden,
damit der obige Satz Geltung habe.
-/

example (ν x₂ y₂ : ℚ) (_hν : ν ≠ 0) (_hx₂ : x₂ ≠ 0) : (y₂ / x₂) / ν = y₂ / (ν * x₂) := by ring

namespace Beispiel01

/-
3. Erstes Exempel.

y² = 11x² + 1,

da x₁ = 0, so ist

x = −2p/(p² − 11), S = 2,
-/

example : (1 : ℤ) ^ 2 = 11 * (0) ^ 2 + (1) := by norm_num

private def xOf (p : ℚ) : ℚ := -2 * p / (p ^ 2 - 11)

/-
und für p = 3 wird x₁₁ = 3, y₁₁ = 10;
-/

example : (2 : ℤ) % (3 ^ 2 - 11) = 0 := by norm_num

example : |xOf (3)| = 3 := by norm_num [xOf]

example : (3 : ℚ) * xOf 3 + 1 = 10 := by norm_num [xOf]

example : (10 : ℤ) ^ 2 = 11 * (3) ^ 2 + (1) := by norm_num

/-
für p = 10/3 wird x₁₁₁ = 60 und y₁₁₁ = 199.
-/

example : |xOf (10 / 3)| = 60 := by norm_num [xOf]

example : |((10 : ℚ) / 3) * xOf (10 / 3) + 1| = 199 := by norm_num [xOf]

example : (199 : ℤ) ^ 2 = 11 * (60) ^ 2 + (1) := by norm_num

end Beispiel01

namespace Beispiel02

/-
4. Zweites Exempel.

y² = 30x² + 91;

hier ist x₁ = 3, y₁ = 19, somit

x = 3 − 2(19p − 90)/(p² − 30), S = 60·91;
-/

example : (19 : ℤ) ^ 2 = 30 * (3) ^ 2 + (91) := by norm_num

private def xOf (p : ℚ) : ℚ := 3 - 2 * (19 * p - 90) / (p ^ 2 - 30)

/-
daraus findet man für

p = −3   4   5      6      −10   15
x = 11   1   5,71   5,71   11    1
y = 61   11  29,389.
-/

example : ([-3, 4, 5, -5, 6, -6, -10, 15] : List ℤ).all (fun p => decide ((60 * 91 : ℤ) % (p ^ 2 - 30) = 0)) = true := by decide

example : ([-3, 4, 5, -5, 6, -6, -10, 15] : List ℚ).map (fun p => |xOf p|) =
    [11, 1, 5, 71, 5, 71, 11, 1] := by norm_num [xOf]

example : ([-3, 4, 5, -5, 6, -6, -10, 15] : List ℚ).map (fun p => |19 + p * (xOf p - 3)|) =
    [61, 11, 29, 389, 29, 389, 61, 11] := by norm_num [xOf]

/-
Setzt man nun mit entsprechendem Vorzeichen

p = 11/1   29/5   61/11 ...

so kömmt

x = *      +113   *
-/

example : ([11, -11, 61 / 11, -61 / 11] : List ℚ).all
    (fun p => decide ((xOf p).den ≠ 1)) = true := by native_decide

example : xOf (-29 / 5) = 113 := by norm_num [xOf]

/-
Seite 35.

für p = 11/1 wird

y₁y₁₁ − ax₁x₁₁ = 19 × 11 − 30·3·1 = 119 durch 7 theilbar;
y₁y₁₁ + ax₁x₁₁ = 19 × 11 + 30·3·1 = 299 durch 13 theilbar;

aber es ist weder 119 noch 299 durch 91 theilbar.
-/

example : (19 : ℤ) * 11 - 30 * 3 * 1 = 119 ∧
    (19 : ℤ) * 11 + 30 * 3 * 1 = 299 ∧
    (119 : ℤ) % 7 = 0 ∧ (299 : ℤ) % 13 = 0 ∧
    (119 : ℤ) % 91 ≠ 0 ∧ (299 : ℤ) % 91 ≠ 0 := by norm_num

end Beispiel02

end Kunerth1877.Paragraf08
