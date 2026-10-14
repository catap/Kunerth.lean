/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf09

/-
Seite 350
§. 9.

Ist a = μ²a₁, 2r = μd und 2am + bn = μ²f, so lässt sich,
wenn man in XI v = μv₁ setzt, der erste Bruch daselbst durch μ²
heben und überdies jede Seite der Gleichung durch μ² dividiren.
Dadurch verliert die Stammzahl den Factor μ⁴ und der Nenner
v² − aw² den Factor μ²; hierauf findet man

nx = m + (dv₁ + fw)w/(v₁² − a₁w²) ... [2]
und S/μ⁴ = S,, = −a₁d² + f²,

der Rückstand im ersten Zähler. Auf die Formel [2] kommt man
auch, wenn man in VIII oder X μpⅡ für p₁ resp. μv₁ für v setzt
und den Bruch durch μ² hebt. Haben d und f ein gemeinschaftliches
Mass, so ist dieses herauszuheben.
-/

example (μ a₁ d f v₁ w : ℚ) (hμ : μ ≠ 0)
    (_hN : v₁ ^ 2 - a₁ * w ^ 2 ≠ 0) :
    ((μ * d * (μ * v₁) + μ ^ 2 * f * w) / ((μ * v₁) ^ 2 - μ ^ 2 * a₁ * w ^ 2)) * w =
      ((d * v₁ + f * w) / (v₁ ^ 2 - a₁ * w ^ 2)) * w := by
  field_simp

example (μ a₁ d f : ℚ) :
    -(μ ^ 2 * a₁) * (μ * d) ^ 2 + (μ ^ 2 * f) ^ 2 =
      μ ^ 4 * (-a₁ * d ^ 2 + f ^ 2) := by
  ring

/-
Diese Reduction kann nur dann stattfinden, wenn n ein
Dividuum von μ oder μ/2 ist, denn nur in diesem Falle können 2r
durch μ, und bn durch μ² theilbar und die Coëfficienten in I frei
von gemeinen quadratischen Factoren sein, wie sich aus der
Gleichung r² = am² + bmn + cn² ... [3] ersehen lässt, in welcher
der obigen Annahme zufolge jedes Glied durch μ² oder (μ/2)²
theilbar sein soll.
-/

example (a a₁ b c m n r μ d f : ℤ)
    (hμ : 0 < μ) (_hn : 0 < n) (ha : a = μ ^ 2 * a₁)
    (hr : 2 * r = μ * d) (hg : 2 * a * m + b * n = μ ^ 2 * f)
    (hroot : r ^ 2 = a * m ^ 2 + b * m * n + c * n ^ 2)
    (hprim : ∀ k : ℤ, 1 < k → ¬ (k ^ 2 ∣ a ∧ k ^ 2 ∣ b ∧ k ^ 2 ∣ c))
    (_hmn : Int.gcd m n = 1) :
    μ ∣ n ∨ μ ∣ 2 * n := by
  let h : ℤ := Int.gcd μ (2 * n)
  obtain ⟨u, hu⟩ := Int.gcd_dvd_left μ (2 * n)
  obtain ⟨v, hv⟩ := Int.gcd_dvd_right μ (2 * n)
  change μ = h * u at hu
  change 2 * n = h * v at hv
  have hh : h ≠ 0 := by
    intro hz
    rw [hz] at hu
    norm_num at hu
    omega
  have hh_nonneg : 0 ≤ h := by dsimp [h]; positivity
  have hu_pos : 0 < u := by
    by_contra hn
    have hu_nonpos : u ≤ 0 := by omega
    have hz := mul_nonpos_of_nonneg_of_nonpos hh_nonneg hu_nonpos
    rw [← hu] at hz
    omega
  have hcop : IsCoprime u v := by
    refine ⟨Int.gcdA μ (2 * n), Int.gcdB μ (2 * n), ?_⟩
    have hb := Int.gcd_eq_gcd_ab μ (2 * n)
    change h = _ at hb
    apply mul_left_cancel₀ hh
    linear_combination -hb - Int.gcdA μ (2 * n) * hu - Int.gcdB μ (2 * n) * hv
  have hbn : μ ^ 2 ∣ b * n := by
    refine ⟨f - 2 * a₁ * m, ?_⟩
    linear_combination hg - 2 * m * ha
  obtain ⟨t, ht⟩ := hbn
  have hua : u ^ 2 ∣ a := by
    refine ⟨h ^ 2 * a₁, ?_⟩
    rw [ha, hu]
    ring
  have hub : u ^ 2 ∣ b := by
    apply (hcop.pow_left (m := 2)).dvd_of_dvd_mul_left
    refine ⟨2 * h * t, ?_⟩
    apply mul_left_cancel₀ hh
    rw [hu] at ht
    linear_combination 2 * ht - b * hv
  have hc : c * (2 * n) ^ 2 = μ ^ 2 * (d ^ 2 - 4 * a₁ * m ^ 2 - 4 * t * m) := by
    linear_combination -4 * hroot + (2 * r + μ * d) * hr -
      4 * m ^ 2 * ha - 4 * m * ht
  have huc : u ^ 2 ∣ c := by
    apply ((hcop.pow_left (m := 2)).pow_right (n := 2)).dvd_of_dvd_mul_left
    refine ⟨d ^ 2 - 4 * a₁ * m ^ 2 - 4 * t * m, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 2 hh)
    rw [hu, hv] at hc
    linear_combination hc
  have hu_one : u = 1 := by
    by_contra hne
    have hgt : 1 < u := by omega
    exact hprim u hgt ⟨hua, hub, huc⟩
  right
  refine ⟨v, ?_⟩
  rw [hu, hu_one]
  simpa using hv

end Kunerth1880.Paragraf09
