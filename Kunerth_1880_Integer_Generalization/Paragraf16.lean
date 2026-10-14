/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf16

/-
Seite 355
§. 16.

Kommen in D die Primfactoren 𝔞 und 𝔠 singulär vor, und ist
jener ein Theiler von a, dieser aber ein Theiler von c, so kann
man jene zwei Primzahlen streichen und bloss den Nenner NⅠ
suchen und benützen, in welchem, der obigen Darstellung gemäss
𝔞 und 𝔠 nicht vorzukommen brauchen; dadurch wird die Zahl der
Versuche viermal kleiner.
-/

def singularPrimeSelection : Prop :=
  ∀ (a c m n r x α₁ β₁ γ k qₐ q_c : ℤ) (p : ℚ)
    (_hn : 0 < n) (_hmn : Int.gcd m n = 1)
    (_hr : r ^ 2 = a * m ^ 2 + c * n ^ 2)
    (_hline : r = m * α₁ + n * β₁) (_hA : α₁ ^ 2 - a = n * γ)
    (_hprep : p.num = n * k - α₁ * (p.den : ℤ))
    (_hp₀ : p ≠ 0) (_hp : p ^ 2 - a ≠ 0)
    (_h₁ : (r : ℚ) * p + a * m ≠ 0) (_h₂ : (m : ℚ) * p + r ≠ 0)
    (_hX : (n : ℚ) * x = m + 2 * (r * p + a * m) / (p ^ 2 - a))
    (_hpₐ : Prime qₐ) (_hp_c : Prime q_c) (_hdₐ : qₐ ∣ a) (_hd_c : q_c ∣ c)
    (_hsₐ : ¬ qₐ ^ 2 ∣ -4 * a * c) (_hs_c : ¬ q_c ^ 2 ∣ -4 * a * c),
    let p₂ := -((a : ℚ) * (m * p + r)) / (r * p + a * m)
    let p₃ := (a : ℚ) / p
    let p₄ := -((r : ℚ) * p + a * m) / (m * p + r)
    p₂ ^ 2 - a ≠ 0 → p₃ ^ 2 - a ≠ 0 → p₄ ^ 2 - a ≠ 0 →
      ∃ q : ℚ, (q = p ∨ q = p₂ ∨ q = p₃ ∨ q = p₄) ∧
        q ^ 2 - a ≠ 0 ∧
        (∃ z : ℤ, (n : ℚ) * z = m + 2 * (r * q + a * m) / (q ^ 2 - a)) ∧
        n ∣ q.num ^ 2 - a * (q.den : ℤ) ^ 2 ∧
        ¬ qₐ ∣ q.num ^ 2 - a * (q.den : ℤ) ^ 2 ∧
        ¬ q_c ∣ q.num ^ 2 - a * (q.den : ℤ) ^ 2

/-
Wäre v² − aw² = NⅠ in ganzen theilfremden Zahlen möglich,
eine der drei andern äquivalenten Gleichungen mit den
Zahlengliedern NⅡ, NⅢ, NⅣ jedoch unmöglich, so wäre die erste
Gleichung

Seite 356

unbrauchbar; und wenn sich vier derartige Gleichungen,
wie es die erste ist, nicht bilden lassen, so ist die Gleichung I
unmöglich; doch darf man aus dem Bestehen jener vier Gleichungen
auf die Möglichkeit von I nicht schliessen. ¹
-/

private theorem four_equations (a c m n r x α₁ β₁ γ k : ℤ) (p : ℚ) (hn : 0 < n)
    (hmn : Int.gcd m n = 1) (hr : r ^ 2 = a * m ^ 2 + c * n ^ 2)
    (hline : r = m * α₁ + n * β₁) (hA : α₁ ^ 2 - a = n * γ)
    (hprep : p.num = n * k - α₁ * (p.den : ℤ))
    (hp₀ : p ≠ 0) (hp : p ^ 2 - a ≠ 0)
    (h₁ : (r : ℚ) * p + a * m ≠ 0) (h₂ : (m : ℚ) * p + r ≠ 0)
    (hX : (n : ℚ) * x = m + 2 * (r * p + a * m) / (p ^ 2 - a)) :
    let p₂ := -((a : ℚ) * (m * p + r)) / (r * p + a * m)
    let p₃ := (a : ℚ) / p
    let p₄ := -((r : ℚ) * p + a * m) / (m * p + r)
    let N := fun q : ℚ => q.num ^ 2 - a * (q.den : ℤ) ^ 2
    p₂ ^ 2 - a ≠ 0 → p₃ ^ 2 - a ≠ 0 → p₄ ^ 2 - a ≠ 0 →
      ∃ ρ₁ ρ₂ ρ₃ ρ₄ ρIII : ℤ,
        ρ₁ ≠ 0 ∧ ρ₂ ≠ 0 ∧ ρ₃ ≠ 0 ∧ ρ₄ ≠ 0 ∧ ρIII ≠ 0 ∧
        N p₂ * ρ₂ ^ 2 = -a * c * N p ∧
        N p₃ * ρ₃ ^ 2 = -a * N p ∧
        N p₄ * ρ₄ ^ 2 = c * N p ∧
        N p * N p₂ * ρ₁ ^ 2 = -4 * a * c * n ^ 2 ∧
        N p₃ * N p₄ * ρIII ^ 2 = -4 * a * c * n ^ 2 := by
  have denominator_product (s d C v₁ w₁ v₂ w₂ : ℤ)
      (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0)
      (hcop₁ : IsCoprime v₁ w₁) (hcop₂ : IsCoprime v₂ w₂)
      (hsum : s * (v₁ * w₂ + v₂ * w₁) = d * w₁ * w₂)
      (hprod : s * v₁ * v₂ = -C * w₁ * w₂) :
      ∃ ρ : ℤ, s = ρ * w₁ * w₂ := by
    have hroot : s * v₁ ^ 2 = w₁ * (d * v₁ + C * w₁) := by
      apply mul_right_cancel₀ hw₂
      linear_combination v₁ * hsum - w₁ * hprod
    have hw₁s : w₁ ∣ s := by
      apply (hcop₁.symm.pow_right (n := 2)).dvd_of_dvd_mul_left
      exact ⟨d * v₁ + C * w₁, by linear_combination hroot⟩
    obtain ⟨t, ht⟩ := hw₁s
    have hsumt : t * (v₁ * w₂ + v₂ * w₁) = d * w₂ := by
      apply mul_left_cancel₀ hw₁
      rw [ht] at hsum
      linear_combination hsum
    have hprodt : t * v₁ * v₂ = -C * w₂ := by
      apply mul_left_cancel₀ hw₁
      rw [ht] at hprod
      linear_combination hprod
    have h₁ : w₂ ∣ t * v₁ := by
      apply hcop₂.symm.dvd_of_dvd_mul_right
      exact ⟨-C, by linear_combination hprodt⟩
    have h₂ : w₂ ∣ t * w₁ := by
      apply hcop₂.symm.dvd_of_dvd_mul_left
      exact ⟨d - t * v₁, by linear_combination hsumt⟩
    have hwt : w₂ ∣ t := by
      obtain ⟨A, B, hBez⟩ := hcop₁
      obtain ⟨u, hu⟩ := h₁
      obtain ⟨v, hv⟩ := h₂
      refine ⟨A * u + B * v, ?_⟩
      linear_combination A * hu + B * hv - t * hBez
    obtain ⟨ρ, hρ⟩ := hwt
    refine ⟨ρ, ?_⟩
    rw [ht, hρ]
    ring

  have fraction_reduction (A B : ℤ) (q : ℚ) (hB : B ≠ 0)
      (hq : q = (A : ℚ) / B) :
      ∃ ρ : ℤ, ρ ≠ 0 ∧ A = ρ * q.num ∧ B = ρ * (q.den : ℤ) := by
    have hw : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
    have hwQ : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have hBQ : (B : ℚ) ≠ 0 := by exact_mod_cast hB
    have hcop : IsCoprime q.num (q.den : ℤ) := by
      apply Int.isCoprime_iff_nat_coprime.mpr
      simpa using q.reduced
    have hcQ : (q.num : ℚ) * B = (A : ℚ) * q.den := by
      apply (div_eq_div_iff hwQ hBQ).mp
      rw [Rat.num_div_den, hq]
    have hc : q.num * B = A * (q.den : ℤ) := by exact_mod_cast hcQ
    have hd : (q.den : ℤ) ∣ B := by
      apply hcop.symm.dvd_of_dvd_mul_left
      exact ⟨A, by linear_combination hc⟩
    obtain ⟨ρ, hρ⟩ := hd
    refine ⟨ρ, ?_, ?_, by rw [hρ]; ring⟩
    · intro h
      apply hB
      rw [hρ, h]
      ring
    · apply mul_right_cancel₀ hw
      rw [hρ] at hc
      linear_combination -hc

  have equivalent_denominators (a m n r g D x : ℤ) (p q : ℚ)
      (hmn : Int.gcd m n = 1)
      (hS : g ^ 2 - 4 * a * r ^ 2 = n ^ 2 * D)
      (hp : p ^ 2 - a ≠ 0) (hg : 2 * (r : ℚ) * p + g ≠ 0)
      (hX : (n : ℚ) * x = m + (2 * r * p + g) / (p ^ 2 - a))
      (heq : q = -((g : ℚ) * p + 2 * a * r) / (2 * r * p + g)) :
      ∃ ρ : ℤ, ρ ≠ 0 ∧ Int.gcd ρ n = 1 ∧
        (p.num ^ 2 - a * (p.den : ℤ) ^ 2) *
          (q.num ^ 2 - a * (q.den : ℤ) ^ 2) * ρ ^ 2 = n ^ 2 * D := by
    let s : ℤ := n * x - m
    let v₁ := p.num
    let w₁ : ℤ := p.den
    let v₂ := q.num
    let w₂ : ℤ := q.den
    have hw₁ : w₁ ≠ 0 := by dsimp [w₁]; exact_mod_cast p.den_nz
    have hw₂ : w₂ ≠ 0 := by dsimp [w₂]; exact_mod_cast q.den_nz
    have hw₁Q : (w₁ : ℚ) ≠ 0 := by exact_mod_cast hw₁
    have hw₂Q : (w₂ : ℚ) ≠ 0 := by exact_mod_cast hw₂
    have hpv : p = (v₁ : ℚ) / w₁ := by simpa [v₁, w₁] using (Rat.num_div_den p).symm
    have hqv : q = (v₂ : ℚ) / w₂ := by simpa [v₂, w₂] using (Rat.num_div_den q).symm
    have hcop₁ : IsCoprime v₁ w₁ := by
      apply Int.isCoprime_iff_nat_coprime.mpr
      simpa [v₁, w₁] using p.reduced
    have hcop₂ : IsCoprime v₂ w₂ := by
      apply Int.isCoprime_iff_nat_coprime.mpr
      simpa [v₂, w₂] using q.reduced
    have hsX : (s : ℚ) = (2 * r * p + g) / (p ^ 2 - a) := by
      dsimp [s]
      push_cast
      linear_combination hX
    have hcross := (eq_div_iff hp).mp hsX
    have hqcross := (eq_div_iff hg).mp heq
    have hsumQ : (s : ℚ) * (p + q) = 2 * r := by
      have h : (p ^ 2 - a) * ((s : ℚ) * (p + q) - 2 * r) = 0 := by
        linear_combination (p + q) * hcross + hqcross
      have h' := (mul_eq_zero.mp h).resolve_left hp
      linarith
    have hprodQ : (s : ℚ) * p * q = -((a : ℚ) * s + g) := by
      linear_combination p * hsumQ - hcross
    have hsum : s * (v₁ * w₂ + v₂ * w₁) = 2 * r * w₁ * w₂ := by
      rw [hpv, hqv] at hsumQ
      field_simp [hw₁Q, hw₂Q] at hsumQ
      have hQ : (s : ℚ) * (v₁ * w₂ + v₂ * w₁) = 2 * r * w₁ * w₂ := by
        linear_combination hsumQ
      exact_mod_cast hQ
    have hprod : s * v₁ * v₂ = -(a * s + g) * w₁ * w₂ := by
      rw [hpv, hqv] at hprodQ
      field_simp [hw₁Q, hw₂Q] at hprodQ
      have hQ : (s : ℚ) * v₁ * v₂ = -((a : ℚ) * s + g) * w₁ * w₂ := by
        linear_combination hprodQ
      exact_mod_cast hQ
    obtain ⟨ρ, hρ⟩ := denominator_product s (2 * r) (a * s + g)
      v₁ w₁ v₂ w₂ hw₁ hw₂ hcop₁ hcop₂ hsum hprod
    have hs₀ : (s : ℚ) ≠ 0 := by
      intro hs
      apply hg
      linear_combination -hcross + (p ^ 2 - a) * hs
    refine ⟨ρ, ?_, ?_, ?_⟩
    · intro h
      apply hs₀
      have hs : s = 0 := by rw [hρ, h]; ring
      exact_mod_cast hs
    · apply Int.isCoprime_iff_gcd_eq_one.mp
      have h := Int.gcd_eq_gcd_ab m n
      rw [hmn] at h
      norm_num at h
      refine ⟨-w₁ * w₂ * Int.gcdA m n, x * Int.gcdA m n + Int.gcdB m n, ?_⟩
      dsimp [s] at hρ
      linear_combination -h + Int.gcdA m n * hρ
    · have hnormQ : (s : ℚ) ^ 2 * (p ^ 2 - a) * (q ^ 2 - a) =
          (g : ℚ) ^ 2 - 4 * a * r ^ 2 := by
        linear_combination ((s : ℚ) * p * q + a * s - g) * hprodQ -
          a * ((s : ℚ) * (p + q) + 2 * r) * hsumQ
      have hSQ : (g : ℚ) ^ 2 - 4 * a * r ^ 2 = (n : ℚ) ^ 2 * D := by exact_mod_cast hS
      rw [hSQ, hpv, hqv] at hnormQ
      have hρQ : (s : ℚ) = (ρ : ℚ) * w₁ * w₂ := by exact_mod_cast hρ
      rw [hρQ] at hnormQ
      field_simp [hw₁Q, hw₂Q] at hnormQ
      have hQ : ((v₁ : ℚ) ^ 2 - a * w₁ ^ 2) *
          ((v₂ : ℚ) ^ 2 - a * w₂ ^ 2) * ρ ^ 2 = (n : ℚ) ^ 2 * D := by
        linear_combination hnormQ
      dsimp [v₁, w₁, v₂, w₂] at hQ
      exact_mod_cast hQ

  have transformed_denominators (a c m n r α₁ β₁ γ k : ℤ) (p : ℚ) (hn : n ≠ 0)
      (hr : r ^ 2 = a * m ^ 2 + c * n ^ 2)
      (hline : r = m * α₁ + n * β₁) (hA : α₁ ^ 2 - a = n * γ)
      (hprep : p.num = n * k - α₁ * (p.den : ℤ))
      (hp₀ : p ≠ 0)
      (h₁ : (r : ℚ) * p + a * m ≠ 0) (h₂ : (m : ℚ) * p + r ≠ 0) :
      let p₂ := -((a : ℚ) * (m * p + r)) / (r * p + a * m)
      let p₃ := (a : ℚ) / p
      let p₄ := -((r : ℚ) * p + a * m) / (m * p + r)
      let N := fun q : ℚ => q.num ^ 2 - a * (q.den : ℤ) ^ 2
      ∃ ρ₂ ρ₃ ρ₄ : ℤ, ρ₂ ≠ 0 ∧ ρ₃ ≠ 0 ∧ ρ₄ ≠ 0 ∧
        N p₂ * ρ₂ ^ 2 = -a * c * N p ∧
        N p₃ * ρ₃ ^ 2 = -a * N p ∧ N p₄ * ρ₄ ^ 2 = c * N p := by
    let v := p.num
    let w : ℤ := p.den
    have hw : w ≠ 0 := by dsimp [w]; exact_mod_cast p.den_nz
    have hwQ : (w : ℚ) ≠ 0 := by exact_mod_cast hw
    have hpv : p = (v : ℚ) / w := by simpa [v, w] using (Rat.num_div_den p).symm
    have hv : v ≠ 0 := by
      intro h
      apply hp₀
      rw [hpv]
      simp [h]
    have hvQ : (v : ℚ) ≠ 0 := by exact_mod_cast hv
    let U := m * k + β₁ * w
    let B := r * k - (m * γ + α₁ * β₁) * w
    have hvprep : v = n * k - α₁ * w := hprep
    have hU : m * v + r * w = n * U := by
      rw [hvprep, hline]
      dsimp [U]
      ring
    have hB : r * v + a * m * w = n * B := by
      rw [hvprep]
      dsimp [B]
      linear_combination -α₁ * w * hline - m * w * hA
    have hUQ : (m : ℚ) * v + r * w = (n : ℚ) * U := by exact_mod_cast hU
    have hBQ : (r : ℚ) * v + a * m * w = (n : ℚ) * B := by exact_mod_cast hB
    have hU₀ : U ≠ 0 := by
      intro h
      apply h₂
      rw [hpv]
      field_simp [hwQ]
      rw [h] at hUQ
      linear_combination hUQ
    have hB₀ : B ≠ 0 := by
      intro h
      apply h₁
      rw [hpv]
      field_simp [hwQ]
      rw [h] at hBQ
      linear_combination hBQ
    have hU₀Q : (U : ℚ) ≠ 0 := by exact_mod_cast hU₀
    have hB₀Q : (B : ℚ) ≠ 0 := by exact_mod_cast hB₀
    let p₂ := -((a : ℚ) * (m * p + r)) / (r * p + a * m)
    let p₃ := (a : ℚ) / p
    let p₄ := -((r : ℚ) * p + a * m) / (m * p + r)
    change ∃ ρ₂ ρ₃ ρ₄ : ℤ, ρ₂ ≠ 0 ∧ ρ₃ ≠ 0 ∧ ρ₄ ≠ 0 ∧ _
    have hp₂ : p₂ = ((-a * U : ℤ) : ℚ) / B := by
      dsimp [p₂]
      apply (div_eq_div_iff h₁ hB₀Q).2
      rw [hpv]
      push_cast
      field_simp [hwQ]
      linear_combination -(a : ℚ) * B * hUQ + a * U * hBQ
    have hp₃ : p₃ = ((a * w : ℤ) : ℚ) / v := by
      dsimp [p₃]
      rw [hpv]
      push_cast
      field_simp [hwQ, hvQ]
    have hp₄ : p₄ = ((-B : ℤ) : ℚ) / U := by
      dsimp [p₄]
      apply (div_eq_div_iff h₂ hU₀Q).2
      rw [hpv]
      field_simp [hwQ]
      linear_combination -(U : ℚ) * hBQ + B * hUQ
    obtain ⟨ρ₂, hρ₂, hv₂, hw₂⟩ := fraction_reduction (-a * U) B p₂ hB₀ hp₂
    obtain ⟨ρ₃, hρ₃, hv₃, hw₃⟩ := fraction_reduction (a * w) v p₃ hv hp₃
    obtain ⟨ρ₄, hρ₄, hv₄, hw₄⟩ := fraction_reduction (-B) U p₄ hU₀ hp₄
    have hnorm₂ : (-a * U) ^ 2 - a * B ^ 2 = -a * c * (v ^ 2 - a * w ^ 2) := by
      have h : (-a * (m * v + r * w)) ^ 2 - a * (r * v + a * m * w) ^ 2 =
          -a * c * n ^ 2 * (v ^ 2 - a * w ^ 2) := by
        linear_combination -a * (v ^ 2 - a * w ^ 2) * hr
      rw [hU, hB] at h
      apply mul_left_cancel₀ (pow_ne_zero 2 hn)
      linear_combination h
    have hnorm₃ : (a * w) ^ 2 - a * v ^ 2 = -a * (v ^ 2 - a * w ^ 2) := by ring
    have hnorm₄ : (-B) ^ 2 - a * U ^ 2 = c * (v ^ 2 - a * w ^ 2) := by
      have h : (-(r * v + a * m * w)) ^ 2 - a * (m * v + r * w) ^ 2 =
          c * n ^ 2 * (v ^ 2 - a * w ^ 2) := by
        linear_combination (v ^ 2 - a * w ^ 2) * hr
      rw [hU, hB] at h
      apply mul_left_cancel₀ (pow_ne_zero 2 hn)
      linear_combination h
    refine ⟨ρ₂, ρ₃, ρ₄, hρ₂, hρ₃, hρ₄, ?_, ?_, ?_⟩
    · rw [hv₂, hw₂] at hnorm₂
      change (p₂.num ^ 2 - a * (p₂.den : ℤ) ^ 2) * ρ₂ ^ 2 = _
      change _ = -a * c * (v ^ 2 - a * w ^ 2)
      linear_combination hnorm₂
    · rw [hv₃] at hnorm₃
      nth_rw 1 [hw₃] at hnorm₃
      change (p₃.num ^ 2 - a * (p₃.den : ℤ) ^ 2) * ρ₃ ^ 2 = _
      change _ = -a * (v ^ 2 - a * w ^ 2)
      linear_combination hnorm₃
    · rw [hv₄, hw₄] at hnorm₄
      change (p₄.num ^ 2 - a * (p₄.den : ℤ) ^ 2) * ρ₄ ^ 2 = _
      change _ = c * (v ^ 2 - a * w ^ 2)
      linear_combination hnorm₄
  let p₂ := -((a : ℚ) * (m * p + r)) / (r * p + a * m)
  let p₃ := (a : ℚ) / p
  let p₄ := -((r : ℚ) * p + a * m) / (m * p + r)
  change p₂ ^ 2 - a ≠ 0 → p₃ ^ 2 - a ≠ 0 → p₄ ^ 2 - a ≠ 0 → _
  intro _hp₂ hp₃ _hp₄
  obtain ⟨ρ₂, ρ₃, ρ₄, hρ₂, hρ₃, hρ₄, hN₂, hN₃, hN₄⟩ :=
    transformed_denominators a c m n r α₁ β₁ γ k p (ne_of_gt hn) hr hline hA hprep hp₀ h₁ h₂
  have hS : (2 * a * m) ^ 2 - 4 * a * r ^ 2 = n ^ 2 * (-4 * a * c) := by
    linear_combination -4 * a * hr
  have hg : 2 * (r : ℚ) * p + 2 * a * m ≠ 0 := by
    intro h
    apply h₁
    linear_combination (1 / 2 : ℚ) * h
  have hX₁ : (n : ℚ) * x = m + (2 * r * p + 2 * a * m) / (p ^ 2 - a) := by
    linear_combination hX
  have heq₁ : p₂ = -(((2 * a * m : ℤ) : ℚ) * p + 2 * a * r) /
      (2 * r * p + (2 * a * m : ℤ)) := by
    dsimp [p₂]
    push_cast
    apply (div_eq_div_iff h₁ hg).2
    ring
  obtain ⟨ρ₁, hρ₁, _hcop₁, hpair₁⟩ := equivalent_denominators a m n r (2 * a * m)
    (-4 * a * c) x p p₂ hmn hS hp
    (by simpa only [Int.cast_mul, Int.cast_ofNat] using hg)
    (by simpa only [Int.cast_mul, Int.cast_ofNat] using hX₁) heq₁
  have hpp₃ : p * p₃ = a := by
    dsimp [p₃]
    field_simp [hp₀]
  have hsign : (m : ℚ) + 2 * (r * p₃ + a * m) / (p₃ ^ 2 - a) =
      -(m + 2 * (r * p + a * m) / (p ^ 2 - a)) := by
    field_simp [hp, hp₃]
    linear_combination 2 * (m * (p * p₃ + a) + r * (p + p₃)) * hpp₃
  have hX₃ : (n : ℚ) * (-x) = m + (2 * r * p₃ + 2 * a * m) / (p₃ ^ 2 - a) := by
    linear_combination -hX - hsign
  have ha : (a : ℚ) ≠ 0 := by
    intro h
    apply hp₃
    dsimp [p₃]
    rw [h]
    norm_num
  have hmul : p * (2 * r * p₃ + 2 * a * m) = 2 * a * (m * p + r) := by
    linear_combination 2 * r * hpp₃
  have hg₃ : 2 * (r : ℚ) * p₃ + 2 * a * m ≠ 0 := by
    intro h
    apply mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) ha) h₂
    linear_combination -hmul + p * h
  have hp₄ : p₄ * (m * p + r) = -(r * p + a * m) := by
    dsimp [p₄]
    exact div_mul_cancel₀ _ h₂
  have heq₃ : p₄ = -(((2 * a * m : ℤ) : ℚ) * p₃ + 2 * a * r) /
      (2 * r * p₃ + (2 * a * m : ℤ)) := by
    push_cast
    apply (eq_div_iff hg₃).2
    apply mul_left_cancel₀ hp₀
    linear_combination 2 * a * hp₄ + (2 * r * p₄ + 2 * a * m) * hpp₃
  obtain ⟨ρIII, hρIII, _hcopIII, hpairIII⟩ := equivalent_denominators a m n r (2 * a * m)
    (-4 * a * c) (-x) p₃ p₄ hmn hS hp₃
    (by simpa only [Int.cast_mul, Int.cast_ofNat] using hg₃)
    (by simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_neg] using hX₃) heq₃
  refine ⟨ρ₁, ρ₂, ρ₃, ρ₄, ρIII, hρ₁, hρ₂, hρ₃, hρ₄, hρIII, hN₂, hN₃, hN₄, ?_, ?_⟩
  · linear_combination hpair₁
  · linear_combination hpairIII

/-
Hätte man den Bruch in VIII durch μ² gehoben, so müsste
in XIIb die Stammzahl −4acn² durch μ⁴ dividirt werden.

Wird die Lösung einer der äquivalenten Gleichungen dadurch
erschwert, dass das Zahlenglied ein Product mehrerer Primzahlen
ist, so zerlege man dieses Glied in zwei Factoren (N = nⅠnⅡ),
für welche vⅠ² = awⅠ² + nⅠ und vⅡ² = awⅡ² + nⅡ in
Rationalzahlen möglich sind, bestimme aus den Auflösungen
dieser Gleichungen die Unbekannten der Gleichung v² = aw² + N
mittelst der Formeln

w = vⅠwⅡ ∓ vⅡwⅠ und v = vⅠvⅡ ∓ awⅠwⅡ
-/

example (a v₁ v₂ w₁ w₂ : ℚ) :
    (v₁ * v₂ + a * w₁ * w₂) ^ 2 - a * (v₁ * w₂ + v₂ * w₁) ^ 2 =
      (v₁ ^ 2 - a * w₁ ^ 2) * (v₂ ^ 2 - a * w₂ ^ 2) := by ring

example (a v₁ v₂ w₁ w₂ : ℚ) :
    (v₁ * v₂ - a * w₁ * w₂) ^ 2 - a * (v₁ * w₂ - v₂ * w₁) ^ 2 =
      (v₁ ^ 2 - a * w₁ ^ 2) * (v₂ ^ 2 - a * w₂ ^ 2) := by ring

/-
und finde, wenn dies Brüche sein sollten, mittelst der p-Function
ganze Zahlen für w und v oder ein Kriterium der Unmöglichkeit
einer solchen Lösung.

Ist −ac ein Quadrat, so gibt es für x = ±√(−c/a) nur zwei
äquivalente Substitutionen.
-/

example (a m r p : ℚ) (hp : p ≠ 0)
    (h₁ : r * p + a * m ≠ 0) (h₂ : m * p + r ≠ 0)
    (hy₀ : r * p ^ 2 + 2 * a * m * p + a * r = 0) :
    -(a * (m * p + r)) / (r * p + a * m) = p ∧
      -(r * p + a * m) / (m * p + r) = a / p := by
  constructor
  · apply (div_eq_iff h₁).2
    linear_combination -hy₀
  · apply (div_eq_div_iff h₂ hp).2
    linear_combination -hy₀

/-
¹ Weil die Gleichungen mit den Zahlengliedern NⅠ und NⅢ zugleich
möglich oder zugleich unmöglich sind, und weil für NⅡ und NⅣ
dasselbe gilt, so braucht man blos NⅠ und NⅡ eventuell NⅠ und NⅣ
nebst XIIb in Betracht zu ziehen.
-/

end Kunerth1880.Paragraf16
