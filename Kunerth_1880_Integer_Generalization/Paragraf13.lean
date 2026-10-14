/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf13

/-
Seite 352
§. 13.

Nach XI ist
(nx − m)(2rpⅠ − g) − 4r² = −n²D/(pⅠ² − a)
und ebenso
(nx − m)(2rpⅡ − g) − 4r² = −n²D/(pⅡ² − a) ... [7]
-/

example (a r g p : ℚ) :
    (g * p + 2 * a * r) ^ 2 - a * (2 * r * p + g) ^ 2 =
      (g ^ 2 - 4 * a * r ^ 2) * (p ^ 2 - a) := by
  ring

/-
Seite 353

hier stellen pⅠ und pⅡ reducirte Brüche vor. Subtrahirt man die
untere Gleichung von der oberen und dividirt hierauf beiderseits
durch pⅠ − pⅡ, so kommt

2rs = n²D(pⅠ + pⅡ)/[(pⅠ² − a)(pⅡ² − a)];

da nach [6] pⅠ + pⅡ = 2r/s ist, so geht die letzte Formel über in

s² = n²D/[(pⅠ² − a)(pⅡ² − a)]
   = n²DwⅠ²wⅡ²/[(vⅠ² − awⅠ²)(vⅡ² − awⅡ²)];
-/

example (a r g s p₁ p₂ : ℚ)
    (hsum : s * (p₁ + p₂) = 2 * r)
    (hprod : s * p₁ * p₂ = -(a * s + g)) :
    s ^ 2 * (p₁ ^ 2 - a) * (p₂ ^ 2 - a) = g ^ 2 - 4 * a * r ^ 2 := by
  linear_combination (s * p₁ * p₂ + a * s - g) * hprod -
    a * (s * (p₁ + p₂) + 2 * r) * hsum

example (a n D s p₁ p₂ : ℚ) (h₁ : p₁ ^ 2 - a ≠ 0)
    (h₂ : p₂ ^ 2 - a ≠ 0)
    (h : s ^ 2 * (p₁ ^ 2 - a) * (p₂ ^ 2 - a) = n ^ 2 * D) :
    s ^ 2 = n ^ 2 * D / ((p₁ ^ 2 - a) * (p₂ ^ 2 - a)) := by
  apply (eq_div_iff (mul_ne_zero h₁ h₂)).2
  linear_combination h

/-
weil ferner in [5] das grösste gemeinschaftliche Mass h von 2r und g
nicht für jeden entsprechenden Werth von p₁ gegen den Nenner
p₁² − a ganz hinausfallen muss, da h überdies einen Theiler
enthalten kann, der im Nenner gar nicht vorkommen darf; so können,
wenn h nicht Eins ist, die Zahlen 2r, g und s für verschiedene
Werthe von p₁ einen oder den andern Factor von h als gemeinsch.
Mass besitzen, und es wird demzufolge der Nenner s der zwei
Brüche in [6] nicht immer der kleinste sein. Da nun laut [6] die
Summe der reducirten Brüche vⅠ/wⅠ und vⅡ/wⅡ gleich 2r/s und ihr
Product vⅠvⅡ/(wⅠwⅡ) gleich −(as + g)/s ist, so können die Glieder
des letzten Bruches auch grösser sein als die des ihm
vorangehenden, so dass man im Allgemeinen annehmen kann:
s = ρⅠwⅠwⅡ und g = ρⅠgⅠ, also wⅠ²wⅡ² = s²/ρⅠ²;
-/

example (a r g s v₁ w₁ v₂ w₂ : ℤ)
    (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0)
    (hcop₁ : IsCoprime v₁ w₁) (hcop₂ : IsCoprime v₂ w₂)
    (hsum : s * (v₁ * w₂ + v₂ * w₁) = (2 * r) * w₁ * w₂)
    (hprod : s * v₁ * v₂ = -(a * s + g) * w₁ * w₂) :
    ∃ ρ : ℤ, s = ρ * w₁ * w₂ := by
  have hroot : s * v₁ ^ 2 = w₁ * ((2 * r) * v₁ + (a * s + g) * w₁) := by
    apply mul_right_cancel₀ hw₂
    linear_combination v₁ * hsum - w₁ * hprod
  have hw₁s : w₁ ∣ s := by
    apply (hcop₁.symm.pow_right (n := 2)).dvd_of_dvd_mul_left
    exact ⟨(2 * r) * v₁ + (a * s + g) * w₁, by linear_combination hroot⟩
  obtain ⟨t, ht⟩ := hw₁s
  have hsumt : t * (v₁ * w₂ + v₂ * w₁) = (2 * r) * w₂ := by
    apply mul_left_cancel₀ hw₁
    rw [ht] at hsum
    linear_combination hsum
  have hprodt : t * v₁ * v₂ = -(a * s + g) * w₂ := by
    apply mul_left_cancel₀ hw₁
    nth_rw 1 [ht] at hprod
    linear_combination hprod
  have h₁ : w₂ ∣ t * v₁ := by
    apply hcop₂.symm.dvd_of_dvd_mul_right
    exact ⟨-(a * s + g), by linear_combination hprodt⟩
  have h₂ : w₂ ∣ t * w₁ := by
    apply hcop₂.symm.dvd_of_dvd_mul_left
    exact ⟨(2 * r) - t * v₁, by linear_combination hsumt⟩
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

/-
oben eingesetzt und reducirt, wird

NⅠNⅡ = n²D/ρⅠ² ... XIIa.
-/

example (a n D s ρ v₁ w₁ v₂ w₂ : ℚ) (_hρ : ρ ≠ 0) (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0)
    (hs : s = ρ * w₁ * w₂)
    (h : s ^ 2 * ((v₁ / w₁) ^ 2 - a) * ((v₂ / w₂) ^ 2 - a) = n ^ 2 * D) :
    (v₁ ^ 2 - a * w₁ ^ 2) * (v₂ ^ 2 - a * w₂ ^ 2) * ρ ^ 2 = n ^ 2 * D := by
  rw [hs] at h
  field_simp [hw₁, hw₂] at h
  linear_combination h

/-
Da NⅠ und NⅡ Dividuen von n sind, so muss D durch ρⅠ²
theilbar und jeder dieser zwei Nenner ein Divisor von nD/ρⅠ² sein;
-/

example (n N₁ N₂ k₁ k₂ ρ D : ℤ) (hn : n ≠ 0)
    (hN₁ : N₁ = n * k₁) (hN₂ : N₂ = n * k₂)
    (hXII : N₁ * N₂ * ρ ^ 2 = n ^ 2 * D) :
    ρ ^ 2 ∣ D := by
  refine ⟨k₁ * k₂, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hn)
  rw [hN₁, hN₂] at hXII
  linear_combination -hXII

/-
für manche Werthe von p₁ fällt daher ρⅠ² als ein zur Bildung von N
eben unnöthiger Factor aus D und aus beiden Seiten der
Gleichungen [7] hinaus; ist ρⅠ eine Primzahl und a ein Nichtrest von
ρⅠ, so muss ρⅠ² immer hinausfallen. Zerlegt man das grösste
gemeinschaftliche Mass h von 2r und g in zwei solche Factoren hⅡ
und ρⅡ, dass alle einfachen Divisoren von hⅡ in n aufgehen,
ρⅡ dagegen

Seite 354

prim gegen n ist, so kann nx − m, d. i. s durch ρⅡ theilbar sein,
und ρⅡ² ist der grösste Divisor von h², durch welchen in besonderen
Fällen beide Seiten in [7] theilbar sein können. Die obige Zahl
ρⅠ ist somit ein Theiler von ρⅡ und dieses wieder ein Theiler von
ρ (§. 8); daher können aus D gelegentlich nur solche quadratische
Factoren hinausfallen, welche Divisoren von h² und prim gegen
n sind.
-/

example (m n x ρ w₁ w₂ : ℤ) (hmn : Int.gcd m n = 1)
    (hs : n * x - m = ρ * w₁ * w₂) : Int.gcd ρ n = 1 := by
  apply Int.isCoprime_iff_gcd_eq_one.mp
  have h := Int.gcd_eq_gcd_ab m n
  rw [hmn] at h
  norm_num at h
  refine ⟨-w₁ * w₂ * Int.gcdA m n, x * Int.gcdA m n + Int.gcdB m n, ?_⟩
  linear_combination -h + Int.gcdA m n * hs

example (r g a ρ v₁ w₁ v₂ w₂ : ℤ)
    (hsum : 2 * r = ρ * (v₁ * w₂ + v₂ * w₁))
    (hprod : g = -ρ * (a * w₁ * w₂ + v₁ * v₂)) :
    ρ ∣ (Int.gcd (2 * r) g : ℤ) := by
  rw [Int.coe_gcd]
  apply dvd_gcd
  · exact ⟨v₁ * w₂ + v₂ * w₁, hsum⟩
  · exact ⟨-(a * w₁ * w₂ + v₁ * v₂), by linear_combination hprod⟩

/- Hilfsschritt: XIIa für die reducirten äquivalenten Brüche. -/

theorem pairedNorms (a b c m n r x : ℤ) (p : ℚ) (_hn : 0 < n)
    (hmn : Int.gcd m n = 1)
    (hroot : r ^ 2 = a * m ^ 2 + b * m * n + c * n ^ 2)
    (hp : p ^ 2 - a ≠ 0)
    (hg : 2 * (r : ℚ) * p + (2 * a * m + b * n) ≠ 0)
    (hX : (n : ℚ) * x = m + (2 * r * p + (2 * a * m + b * n)) / (p ^ 2 - a)) :
    let q := -(((2 * a * m + b * n : ℤ) : ℚ) * p + 2 * a * r) /
      (2 * r * p + (2 * a * m + b * n))
    q ^ 2 - a ≠ 0 →
      ∃ ρ : ℤ, ρ ≠ 0 ∧ Int.gcd ρ n = 1 ∧
        (p.num ^ 2 - a * (p.den : ℤ) ^ 2) *
          (q.num ^ 2 - a * (q.den : ℤ) ^ 2) * ρ ^ 2 =
            n ^ 2 * (b ^ 2 - 4 * a * c) := by
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
  let q : ℚ := -(((2 * a * m + b * n : ℤ) : ℚ) * p + 2 * a * r) /
    (2 * r * p + (2 * a * m + b * n))
  change q ^ 2 - a ≠ 0 → _
  intro _hq
  have hS : (2 * a * m + b * n) ^ 2 - 4 * a * r ^ 2 =
      n ^ 2 * (b ^ 2 - 4 * a * c) := by
    linear_combination -4 * a * hroot
  refine equivalent_denominators a m n r (2 * a * m + b * n)
    (b ^ 2 - 4 * a * c) x p q hmn hS hp ?_ ?_ ?_
  · simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hg
  · simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hX
  · dsimp [q]
    push_cast
    rfl

/-
Dies ist bei den zur Ermittlung von N anzustellenden
Versuchen zu benützen. Ist α ein Nichtrest der Primzahl π und die
ganze Zahl D/π²ᵛ prim gegen π, so ist π²ᵛ in D zu löschen.
-/

/-
Lesart: Im Druck steht das griechische α. Ob hier der Coëfficient
a gemeint ist, bleibt eine Frage der mathematischen Zuordnung.
-/

/-
Formale Zuordnung: α wird in der Nichtrestbedingung durch seine
Restclasse modulo π dargestellt. Diese wird nicht mit der Restclasse
des Coëfficienten a gleichgesetzt; auch ihr Zusammenhang mit dem
früheren rationalen Parameter α bleibt offen.

D = b² − 4ac und h ist das grösste gemeinschaftliche Mass von 2r
und 2am + bn. Der quadratische Factor F = π²ᵛ muss nach dem
vorhergehenden Absatz D und h² theilen und prim gegen n sein.
Die Bedingung F ∣ D hält fest, dass D/F eine ganze Zahl ist.

Das Streichen wird als Einschränkung der Nennerprobe aus §. 6
und §. 7 erfasst: Ein Nenner N = v² − aw² aus theilfremden v, w,
der durch n theilbar ist und nD theilt, soll auch n(D/F) theilen.
Die Voraussetzungen für die Coëfficienten und den bekannten Bruch
m/n stammen aus §. 1; die Nenner w und N sind ungleich Null.
Die folgende Proposition hält diese Deutung ohne Beweis fest.
-/

example : Prop :=
  ∀ (π ν : ℕ) (α : ZMod π) (a b c m n r v w : ℤ),
    0 < a → (¬ ∃ q : ℤ, q ^ 2 = a) →
    0 < n → Int.gcd m n = 1 →
    r ^ 2 = a * m ^ 2 + b * m * n + c * n ^ 2 →
    π.Prime → 0 < ν → (¬ ∃ t : ZMod π, t ^ 2 = α) →
    let D := b ^ 2 - 4 * a * c
    let h : ℤ := Int.gcd (2 * r) (2 * a * m + b * n)
    let N := v ^ 2 - a * w ^ 2
    let F := (π : ℤ) ^ (2 * ν)
    F ∣ D → F ∣ h ^ 2 → Int.gcd F n = 1 →
    Int.gcd (D / F) (π : ℤ) = 1 →
    w ≠ 0 → Int.gcd v w = 1 → N ≠ 0 →
    n ∣ N → N ∣ n * D → N ∣ n * (D / F)

end Kunerth1880.Paragraf13
