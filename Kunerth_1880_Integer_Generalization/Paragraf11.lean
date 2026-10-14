/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf11

/-
Seite 351
§. 11.

Endlich lässt sich, wenn a = μ²a₁ und 2am + bn = μf ist, der
erste Bruch in XI für v = μv₁ durch μ² heben, wodurch in S und
im Nenner der Factor μ² getilgt wird; dann ist

μnx = μm + (2rv₁ + fw)w/(v₁² − a₁w²) ... [4]
und S/μ² = S,,, = −4a₁r² + f².
-/

example (μ a₁ r f v₁ w m : ℚ) (hμ : μ ≠ 0)
    (_hN : v₁ ^ 2 - a₁ * w ^ 2 ≠ 0) :
    μ * (m + ((2 * r * (μ * v₁) + μ * f * w) /
      ((μ * v₁) ^ 2 - μ ^ 2 * a₁ * w ^ 2)) * w) =
      μ * m + ((2 * r * v₁ + f * w) / (v₁ ^ 2 - a₁ * w ^ 2)) * w := by
  field_simp

example (μ a₁ r f : ℚ) :
    -4 * (μ ^ 2 * a₁) * r ^ 2 + (μ * f) ^ 2 =
      μ ^ 2 * (-4 * a₁ * r ^ 2 + f ^ 2) := by
  ring

/-
Dieselbe Formel wird erhalten, wenn man in VIII oder X
beide Seiten mit μ multiplicirt und den Bruch durch μ² abkürzt;
doch ist diese Reduction wegen Vergrösserung des Coëfficienten
von x minder vortheilhaft.

In [4] muss n prim gegen μ sein; denn angenommen n = μn₁,
so würde die obige Gleichung [3] lauten:

r² = μ²a₁m² + bmμn₁ + cμ²n₁²,

und könnte nur dann bestehen, wenn bμn₁, d. i. bn durch μ²,
somit r durch μ theilbar wären, was der Annahme widerspricht
und eine unmittelbare Abkürzung durch μ² ermöglichen würde.
Daher bleibt v₁² − a₁w² ein Vielfaches von n und w ist gemeiniglich
durch μ theilbar.
-/

example (a₁ b c m n₁ r q : ℤ) (hq : Prime q)
    (hcop : Int.gcd q m = 1)
    (hr : r ^ 2 = q ^ 2 * a₁ * m ^ 2 + b * m * (q * n₁) + c * (q * n₁) ^ 2) :
    q ∣ r ∧ q ^ 2 ∣ b * (q * n₁) := by
  have hrq : q ∣ r ^ 2 := by
    refine ⟨q * a₁ * m ^ 2 + b * m * n₁ + c * q * n₁ ^ 2, ?_⟩
    linear_combination hr
  have hd : q ∣ r := hq.dvd_of_dvd_pow hrq
  refine ⟨hd, ?_⟩
  rcases hd with ⟨t, ht⟩
  apply (Int.isCoprime_iff_gcd_eq_one.mpr hcop).pow_left.dvd_of_dvd_mul_left
  refine ⟨t ^ 2 - a₁ * m ^ 2 - c * n₁ ^ 2, ?_⟩
  rw [ht] at hr
  linear_combination -hr

example (a a₁ b c m n r μ : ℤ) (ha : a = μ ^ 2 * a₁)
    (hmn : Int.gcd m n = 1)
    (hr : r ^ 2 = a * m ^ 2 + b * m * n + c * n ^ 2)
    (hremaining : ∀ q : ℤ, Prime q → q ∣ μ →
      ¬ (q ∣ 2 * r ∧ q ^ 2 ∣ 2 * a * m + b * n)) :
    ¬ ∃ q : ℤ, Prime q ∧ q ∣ μ ∧ q ∣ n := by
  rintro ⟨q, hq, hqμ, hqn⟩
  rcases hqμ with ⟨u, hu⟩
  rcases hqn with ⟨n₁, hn₁⟩
  have hrq : q ∣ r ^ 2 := by
    refine ⟨q * u ^ 2 * a₁ * m ^ 2 + b * m * n₁ + c * q * n₁ ^ 2, ?_⟩
    rw [ha, hu, hn₁] at hr
    linear_combination hr
  have hd : q ∣ r := hq.dvd_of_dvd_pow hrq
  have hcop : IsCoprime q m := by
    have h := Int.gcd_eq_gcd_ab m n
    rw [hmn] at h
    norm_num at h
    refine ⟨n₁ * Int.gcdB m n, Int.gcdA m n, ?_⟩
    linear_combination -h - Int.gcdB m n * hn₁
  have hbn : q ^ 2 ∣ b * n := by
    rcases hd with ⟨t, ht⟩
    apply hcop.pow_left.dvd_of_dvd_mul_left
    refine ⟨t ^ 2 - u ^ 2 * a₁ * m ^ 2 - c * n₁ ^ 2, ?_⟩
    rw [ha, hu, hn₁, ht] at hr
    rw [hn₁]
    linear_combination -hr
  apply hremaining q hq ⟨u, hu⟩
  refine ⟨dvd_mul_of_dvd_right hd 2, dvd_add ?_ hbn⟩
  refine ⟨2 * u ^ 2 * a₁ * m, ?_⟩
  rw [ha, hu]
  ring

/-
Alle diese Abkürzungen sind schon in der Hauptformel VIII
auszuführen, da XI zur Rechnung nicht nöthig ist.
-/

end Kunerth1880.Paragraf11
