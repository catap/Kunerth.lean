/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf15

/-
Seite 354
§. 15.

Ist in I b = 0, also y² = ax² + c, so kann jeder Werth von x
mit beiden Vorzeichen genommen werden, daher nach VIII

nx = m + 2(rp₁ + am)/(p₁² − a)

und

nx = −m − 2(rp₁ + am)/(p₁² − a) = m + 2(rpⅢ + am)/(pⅢ² − a).
-/

example (a c x : ℚ) : a * (-x) ^ 2 + c = a * x ^ 2 + c := by ring

/-
Seite 355

Es ist somit

(rpⅢ + am)/(pⅢ² − a) = −(mp₁² + rp₁)/(p₁² − a),

und nach pⅢ aufgelöst:

pⅢ = a/p₁ und = −(rp₁ + am)/(mp₁ + r);

lässt man hier für p₁ auch den äquivalenten Werth

pⅡ (= −a(mp₁ + r)/(rp₁ + am))

aus §. 12 eintreten, so ergeben sich die vier äquivalenten
Substitutionen: p₁ und

pⅡ = −a(mp₁ + r)/(rp₁ + am)

bezüglich +x und

pⅢ = a/p₁ nebst pⅣ = −(rp₁ + am)/(mp₁ + r)

bezüglich −x, wobei

pⅠpⅢ = pⅡpⅣ = a.
-/

example (a p : ℚ) (hp : p ≠ 0) : p * (a / p) = a := by field_simp

example (a m r p : ℚ) (h₁ : r * p + a * m ≠ 0) (h₂ : m * p + r ≠ 0) :
    (-(a * (m * p + r)) / (r * p + a * m)) *
      (-(r * p + a * m) / (m * p + r)) = a := by
  calc
    _ = a * ((r * p + a * m) / (r * p + a * m)) *
      ((m * p + r) / (m * p + r)) := by ring
    _ = a := by rw [div_self h₁, div_self h₂]; ring

example (a m r p q : ℚ) (hp : p ^ 2 - a ≠ 0) (hq : q ^ 2 - a ≠ 0)
    (hd : r * p + a * m ≠ 0)
    (heq : q = -(a * (m * p + r)) / (r * p + a * m)) :
    m + 2 * (r * q + a * m) / (q ^ 2 - a) =
      m + 2 * (r * p + a * m) / (p ^ 2 - a) := by
  have h := (eq_div_iff hd).1 heq
  field_simp [hp, hq]
  linear_combination 2 * (p - q) * h

example (a m r p q : ℚ) (hp : p ^ 2 - a ≠ 0) (hq : q ^ 2 - a ≠ 0)
    (hp₀ : p ≠ 0) (heq : q = a / p) :
    m + 2 * (r * q + a * m) / (q ^ 2 - a) =
      -(m + 2 * (r * p + a * m) / (p ^ 2 - a)) := by
  have h := (eq_div_iff hp₀).1 heq
  field_simp [hp, hq]
  linear_combination 2 * (m * (p * q + a) + r * (p + q)) * h

example (a m r p q : ℚ) (hp : p ^ 2 - a ≠ 0) (hq : q ^ 2 - a ≠ 0)
    (hd : m * p + r ≠ 0)
    (heq : q = -(r * p + a * m) / (m * p + r)) :
    m + 2 * (r * q + a * m) / (q ^ 2 - a) =
      -(m + 2 * (r * p + a * m) / (p ^ 2 - a)) := by
  have h := (eq_div_iff hd).1 heq
  field_simp [hp, hq]
  linear_combination 2 * (p * q - a) * h

/-
vⅠ² − awⅠ² (= NⅠ), −ac(vⅠ² − awⅠ²)/ρ₂² (= NⅡ),
−a(vⅠ² − awⅠ²)/ρ₃² (= NⅢ) und c(vⅠ² − awⅠ²)/ρ₄² (= NⅣ)

sind die zugehörigen äquivalenten Nenner.
-/

example (a c m n r v w : ℚ) (hr : r ^ 2 = a * m ^ 2 + c * n ^ 2) :
    (-a * (m * v + r * w)) ^ 2 - a * (r * v + a * m * w) ^ 2 =
      -a * c * n ^ 2 * (v ^ 2 - a * w ^ 2) := by
  linear_combination -a * (v ^ 2 - a * w ^ 2) * hr

example (a v w : ℚ) :
    (a * w) ^ 2 - a * v ^ 2 = -a * (v ^ 2 - a * w ^ 2) := by ring

example (a c m n r v w : ℚ) (hr : r ^ 2 = a * m ^ 2 + c * n ^ 2) :
    (-(r * v + a * m * w)) ^ 2 - a * (m * v + r * w) ^ 2 =
      c * n ^ 2 * (v ^ 2 - a * w ^ 2) := by
  linear_combination (v ^ 2 - a * w ^ 2) * hr

example (a c n N₁ N₂ ρ₂ v₂ w₂ : ℚ) (_hρ : ρ₂ ≠ 0) (hn : n ≠ 0)
    (hN₂ : N₂ = v₂ ^ 2 - a * w₂ ^ 2)
    (h : (n * ρ₂ * v₂) ^ 2 - a * (n * ρ₂ * w₂) ^ 2 = -a * c * n ^ 2 * N₁) :
    N₂ * ρ₂ ^ 2 = -a * c * N₁ := by
  have he : n ^ 2 * (N₂ * ρ₂ ^ 2 + a * c * N₁) = 0 := by
    rw [hN₂]
    linear_combination h
  have hz := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hn)
  linarith

example (a N₁ N₃ ρ₃ v₃ w₃ : ℚ) (_hρ : ρ₃ ≠ 0) (hN₃ : N₃ = v₃ ^ 2 - a * w₃ ^ 2)
    (h : (ρ₃ * v₃) ^ 2 - a * (ρ₃ * w₃) ^ 2 = -a * N₁) :
    N₃ * ρ₃ ^ 2 = -a * N₁ := by
  rw [hN₃]
  linear_combination h

example (a c n N₁ N₄ ρ₄ v₄ w₄ : ℚ) (_hρ : ρ₄ ≠ 0) (hn : n ≠ 0)
    (hN₄ : N₄ = v₄ ^ 2 - a * w₄ ^ 2)
    (h : (n * ρ₄ * v₄) ^ 2 - a * (n * ρ₄ * w₄) ^ 2 = c * n ^ 2 * N₁) :
    N₄ * ρ₄ ^ 2 = c * N₁ := by
  have he : n ^ 2 * (N₄ * ρ₄ ^ 2 - c * N₁) = 0 := by
    rw [hN₄]
    linear_combination h
  have hz := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hn)
  linarith

/-
Die Divisoren ρ₂², ρ₃², ρ₄² finden ihre Erklärung in dem auch hier
geltenden Gesetze:

NⅠNⅡ = −4acn²/ρⅠ² und NⅢNⅣ = −4acn²/ρⅢ² ... XIIb.
-/

/-
Rechenschritt: Einsetzen von D = −4ac in die vorausgesetzten
Productgleichungen.
-/

example (a c n N₁ N₂ N₃ N₄ ρ₁ ρ₃ D : ℚ) (_hρ₁ : ρ₁ ≠ 0) (_hρ₃ : ρ₃ ≠ 0) (hD : D = -4 * a * c)
    (h₁ : N₁ * N₂ * ρ₁ ^ 2 = n ^ 2 * D)
    (h₃ : N₃ * N₄ * ρ₃ ^ 2 = n ^ 2 * D) :
    N₁ * N₂ * ρ₁ ^ 2 = -4 * a * c * n ^ 2 ∧
      N₃ * N₄ * ρ₃ ^ 2 = -4 * a * c * n ^ 2 := by
  rw [hD] at h₁ h₃
  constructor <;> nlinarith

end Kunerth1880.Paragraf15
