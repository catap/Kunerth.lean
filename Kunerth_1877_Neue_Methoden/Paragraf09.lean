/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf09

/-
Seite 35

§. 9.
Fortsetzung.

1. Sind in der Gleichung y² = ax²+b drei Werthe von x
bekannt, so lassen sich durch Addition und Subtraction der
gefundenen Wurzeln neue Wurzeln, und wenn a positiv ist, in
beliebiger Anzahl finden. Sind x₁, y₁, x₂, y₂, x₃, y₃ diese bekannten
Werthe, so setze man
p = (y₂+y₃)/(x₂+x₃)
in die Gleichung
x = x₁−2(y₁p−ax₁)/(p²−a),
da folgt
x = x₁−2[y₁(y₂+y₃)−ax₁(x₂+x₃)](x₂+x₃)/[(y₂+y₃)²−a(x₂+x₃)²]
oder
x = x₁−[y₁(y₂+y₃)−ax₁(x₂+x₃)](x₂+x₃)/(y₂y₃−ax₂x₃+b). (A)
-/

example : Prop :=
  ∀ a b x₁ y₁ x₂ y₂ x₃ y₃ : ℤ,
    0 < a → y₁ ^ 2 = a * x₁ ^ 2 + b →
    y₂ ^ 2 = a * x₂ ^ 2 + b → y₃ ^ 2 = a * x₃ ^ 2 + b →
    (x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃) →
    Set.Infinite {x : ℤ | ∃ y : ℤ, y ^ 2 = a * x ^ 2 + b}

example (a x₁ y₁ x₂ y₂ x₃ y₃ : ℚ) (hs : x₂ + x₃ ≠ 0)
    (_hd : (y₂ + y₃) ^ 2 - a * (x₂ + x₃) ^ 2 ≠ 0) :
    x₁ - 2 * (y₁ * ((y₂ + y₃) / (x₂ + x₃)) - a * x₁) /
      (((y₂ + y₃) / (x₂ + x₃)) ^ 2 - a) =
    x₁ - 2 * (y₁ * (y₂ + y₃) - a * x₁ * (x₂ + x₃)) /
      ((y₂ + y₃) ^ 2 - a * (x₂ + x₃) ^ 2) * (x₂ + x₃) := by
  have he : ((y₂ + y₃) / (x₂ + x₃)) ^ 2 - a =
      ((y₂ + y₃) ^ 2 - a * (x₂ + x₃) ^ 2) / (x₂ + x₃) ^ 2 := by field_simp
  rw [he]
  field_simp

example (a b x₂ y₂ x₃ y₃ : ℚ)
    (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) (h₃ : y₃ ^ 2 = a * x₃ ^ 2 + b) :
    (y₂ + y₃) ^ 2 - a * (x₂ + x₃) ^ 2 = 2 * (y₂ * y₃ - a * x₂ * x₃ + b) := by
  linear_combination h₂ + h₃

/-
Aus den Gleichungen
y₂² = ax₂²+b
 y₃² = ax₃²+b } (z)
folgt durch Multiplication
(y₂y₃−ax₂x₃)(y₂y₃+ax₂x₃) = ab(x₂²+x₃²)+b² ... (λ)
-/

example (a b x₂ y₂ x₃ y₃ : ℚ)
    (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) (h₃ : y₃ ^ 2 = a * x₃ ^ 2 + b) :
    (y₂ * y₃ - a * x₂ * x₃) * (y₂ * y₃ + a * x₂ * x₃) =
      a * b * (x₂ ^ 2 + x₃ ^ 2) + b ^ 2 := by
  linear_combination y₃ ^ 2 * h₂ + (a * x₂ ^ 2 + b) * h₃

/-
und wenn man die linksstehenden Binome mit u respective v und
das rechtsstehende mit w bezeichnet, so ist
uv = w und u+b = (w+bv)/v,
also v(u+b) = w+bv, d. i.
-/

example (u v w b : ℚ) (hv : v ≠ 0) (h : u * v = w) : u + b = (w + b * v) / v := by
  apply (eq_div_iff hv).mpr
  linear_combination h

/-
Seite 36

v(u+b) = ab(x₂²+x₃²)+b²+by₂y₃+abx₂x₃ =
= ab(x₂+x₃)²+b(u+b)
und hieraus
(u+b)(v−b) = ab(x₂+x₃)²,
das ist
(y₂y₃−ax₂x₃+b)(y₂y₃+ax₂x₃−b) = ab(x₂+x₃)² (B)
-/

example (a b x₂ y₂ x₃ y₃ : ℚ) :
    a * b * (x₂ ^ 2 + x₃ ^ 2) + b ^ 2 + b * y₂ * y₃ + a * b * x₂ * x₃ =
    a * b * (x₂ + x₃) ^ 2 + b * (y₂ * y₃ - a * x₂ * x₃ + b) := by ring

theorem equationB (a b x₂ y₂ x₃ y₃ : ℚ)
    (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) (h₃ : y₃ ^ 2 = a * x₃ ^ 2 + b) :
    (y₂ * y₃ - a * x₂ * x₃ + b) * (y₂ * y₃ + a * x₂ * x₃ - b) =
      a * b * (x₂ + x₃) ^ 2 := by
  linear_combination y₃ ^ 2 * h₂ + (a * x₂ ^ 2 + b) * h₃

/-
somit
y₂y₃−ax₂x₃+b = ab(x₂+x₃)²/(y₂y₃+ax₂x₃−b)
in (A) substituirt:
x = x₁−[y₁(y₂+y₃)−ax₁(x₂+x₃)](y₂y₃+ax₂x₃−b)/[ab(x₂+x₃)]. (C)
-/

example (a b x₁ y₁ x₂ y₂ x₃ y₃ : ℚ)
    (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) (h₃ : y₃ ^ 2 = a * x₃ ^ 2 + b)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : x₂ + x₃ ≠ 0)
    (hu : y₂ * y₃ - a * x₂ * x₃ + b ≠ 0) :
    x₁ - (y₁ * (y₂ + y₃) - a * x₁ * (x₂ + x₃)) /
      (y₂ * y₃ - a * x₂ * x₃ + b) * (x₂ + x₃) =
    x₁ - ((y₁ * (y₂ + y₃) - a * x₁ * (x₂ + x₃)) *
      (y₂ * y₃ + a * x₂ * x₃ - b)) / (a * b * (x₂ + x₃)) := by
  have hB := equationB a b x₂ y₂ x₃ y₃ h₂ h₃
  field_simp
  linear_combination (y₁ * (y₂ + y₃) - a * x₁ * (x₂ + x₃)) * hB

/-
Aus (λ) und (z) folgt bei obiger Bezeichnung
uv = b(y₂²+y₃²−b),
somit
v(u+b) = b(y₂²+y₃²)−b²+by₂y₃+abx₂x₃ =
= b(y₂+y₃)²−b(y₂y₃−ax₂x₃+b) = b(y₂+y₃)²−b(u+b)
und hieraus
(u+b)(v+b) = b(y₂+y₃)²,
somit
y₂y₃−ax₂x₃+b = b(y₂+y₃)²/(y₂y₃+ax₂x₃+b)
in A) substituirt:
x = x₁−[y₁(y₂+y₃)−ax₁(x₂+x₃)](y₂y₃+ax₂x₃+b)(x₂+x₃)/[b(y₂+y₃)²]. (D)
-/

example (a b x₂ y₂ x₃ y₃ : ℚ)
    (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) (h₃ : y₃ ^ 2 = a * x₃ ^ 2 + b) :
    (y₂ * y₃ - a * x₂ * x₃) * (y₂ * y₃ + a * x₂ * x₃) =
      b * (y₂ ^ 2 + y₃ ^ 2 - b) := by
  linear_combination (y₃ ^ 2 - b) * h₂ + a * x₂ ^ 2 * h₃

example (a b x₂ y₂ x₃ y₃ : ℚ) :
    b * (y₂ ^ 2 + y₃ ^ 2) - b ^ 2 + b * y₂ * y₃ + a * b * x₂ * x₃ =
      b * (y₂ + y₃) ^ 2 - b * (y₂ * y₃ - a * x₂ * x₃ + b) := by ring

theorem equationD (a b x₂ y₂ x₃ y₃ : ℚ)
    (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) (h₃ : y₃ ^ 2 = a * x₃ ^ 2 + b) :
    (y₂ * y₃ - a * x₂ * x₃ + b) * (y₂ * y₃ + a * x₂ * x₃ + b) =
      b * (y₂ + y₃) ^ 2 := by
  linear_combination (y₃ ^ 2 - b) * h₂ + a * x₂ ^ 2 * h₃

example (a b x₁ y₁ x₂ y₂ x₃ y₃ : ℚ)
    (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) (h₃ : y₃ ^ 2 = a * x₃ ^ 2 + b)
    (hb : b ≠ 0) (ht : y₂ + y₃ ≠ 0)
    (hu : y₂ * y₃ - a * x₂ * x₃ + b ≠ 0) :
    x₁ - (y₁ * (y₂ + y₃) - a * x₁ * (x₂ + x₃)) /
      (y₂ * y₃ - a * x₂ * x₃ + b) * (x₂ + x₃) =
    x₁ - ((y₁ * (y₂ + y₃) - a * x₁ * (x₂ + x₃)) *
      (y₂ * y₃ + a * x₂ * x₃ + b) * (x₂ + x₃)) / (b * (y₂ + y₃) ^ 2) := by
  have hD := equationD a b x₂ y₂ x₃ y₃ h₂ h₃
  field_simp
  linear_combination (y₁ * (y₂ + y₃) - a * x₁ * (x₂ + x₃)) * (x₂ + x₃) * hD

/-
Vergleicht man diesen Werth von x mit dem obigen in (C)
stehenden, so zeigen sich verschiedene Zähler und Nenner; dieser
Unterschied muss aber nach vollzogener Reduction verschwinden.
Zuvörderst hebt sich in beiden Brüchen der grösste
gemeinschaftliche Theiler m von x₂+x₃ und y₂+y₃, so dass für
x₂+x₃ = mk und y₂+y₃ = ml, die Nenner dieser Brüche in ak
und l² übergehen, wenn man vorläufig von b absieht; weil aber
k prim gegen l ist, so muss k hinausfallen und es bleibt a und l².
-/

example (d a k l : ℤ) (_hkl : IsCoprime k l) (hak : d ∣ a * k) (hl : d ∣ l ^ 2) : d ∣ a := by
  obtain ⟨u, v, h⟩ := _hkl.pow_right (n := 2)
  obtain ⟨c, hc⟩ := hak
  obtain ⟨e, he⟩ := hl
  exact ⟨u * c + a * v * e, by linear_combination -a * h + u * hc + (a * v) * he⟩

/-
Seite 37

Nun sei a = μα, l² = μλ und α prim gegen λ; dann müssen α
und λ sich heben und beide Nenner gehen in μ über.
-/

example (d μ α lam : ℤ) (hcop : IsCoprime α lam) (hα : d ∣ μ * α) (hlam : d ∣ μ * lam) : d ∣ μ := by
  obtain ⟨u, v, h⟩ := hcop
  obtain ⟨c, hc⟩ := hα
  obtain ⟨e, he⟩ := hlam
  exact ⟨u * c + v * e, by linear_combination -μ * h + u * hc + v * he⟩

/-
Enthält μ keinen quadratischen Factor, so ist l durch μ
theilbar; wäre aber μ ein Vielfaches von ν² — wobei ν eine ungerade
Primzahl bezeichnen soll — so müsste ν² wegen der
Gleichung
y₂²−y₃² = a(x₂²−x₃²). (π)
auch ein Theiler von y₂+y₃ sein; denn wäre letzteres Binom nur
durch ν theilbar, so müsste auch y₂−y₃ und demzufolge y₂ und y₃
durch ν theilbar sein; dann aber wären b und a Vielfache von ν²
und man könnte die gegebene Gleichung durch ν² abkürzen; somit
muss y₂+y₃ den Factor ν² enthalten.
-/

example (μ l : ℤ) (hμ : Squarefree μ) (h : μ ∣ l ^ 2) : μ ∣ l := by
  exact (hμ.dvd_pow_iff_dvd (n := 2) (by decide)).mp h

example (a b x₂ y₂ x₃ y₃ : ℤ)
    (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) (h₃ : y₃ ^ 2 = a * x₃ ^ 2 + b) :
    y₂ ^ 2 - y₃ ^ 2 = a * (x₂ ^ 2 - x₃ ^ 2) := by linear_combination h₂ - h₃

example (a b x₂ y₂ x₃ y₃ ν : ℤ) (hν : Prime ν) (_hνpos : 0 < ν) (hodd : IsCoprime ν 2)
    (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) (h₃ : y₃ ^ 2 = a * x₃ ^ 2 + b)
    (ha : ν ^ 2 ∣ a) (hb : ¬ ν ^ 2 ∣ b) (hs : ν ∣ y₂ + y₃) : ν ^ 2 ∣ y₂ + y₃ := by
  by_contra hnot
  obtain ⟨t, ht⟩ := hs
  have hnt : ¬ ν ∣ t := by
    rintro ⟨q, hq⟩
    apply hnot
    exact ⟨q, by rw [ht, hq]; ring⟩
  have hprod : ν ^ 2 ∣ (y₂ + y₃) * (y₂ - y₃) := by
    obtain ⟨A, hA⟩ := ha
    exact ⟨A * (x₂ ^ 2 - x₃ ^ 2), by nlinarith [h₂, h₃]⟩
  have htprod : ν ∣ t * (y₂ - y₃) := by
    apply (mul_dvd_mul_iff_left hν.ne_zero).mp
    simpa only [pow_two, ht, mul_assoc] using hprod
  have hdiff : ν ∣ y₂ - y₃ := (hν.dvd_mul.mp htprod).resolve_left hnt
  have hsum : ν ∣ y₂ + y₃ := ⟨t, ht⟩
  have htwoy : ν ∣ 2 * y₂ := by
    convert dvd_add hsum hdiff using 1
    ring
  have hy : ν ∣ y₂ := hodd.dvd_of_dvd_mul_left htwoy
  apply hb
  have hysq : ν ^ 2 ∣ y₂ ^ 2 := by
    obtain ⟨t, ht⟩ := hy
    exact ⟨t ^ 2, by rw [ht]; ring⟩
  convert dvd_sub hysq (dvd_mul_of_dvd_left ha (x₂ ^ 2)) using 1
  nlinarith [h₂]

/-
Zwar könnte beim Abkürzen von y₂+y₃ und x₂+x₃ der Factor ν oder ν²
sich in diesen Binomen heben, dann aber wäre die rechte Seite der
Gleichung π durch ν³ respective ν⁴ theilbar, und y₂+y₃ müsste den
Factor ν³ respective ν⁴ ebenfalls enthalten, so dass nach erfolgter
Abkürzung in l der Factor ν² zurückbleiben würde. Es muss somit
l durch jedes μ, welches keine geradgerade Zahl ist, theilbar sein.
-/

example (ν l : ℤ) (hν : ν ≠ 0) (h : ν ^ 3 ∣ ν * l) : ν ^ 2 ∣ l := by
  rw [show ν ^ 3 = ν * ν ^ 2 by ring] at h
  exact (mul_dvd_mul_iff_left hν).mp h

example (ν l : ℤ) (hν : ν ≠ 0) (h : ν ^ 4 ∣ ν ^ 2 * l) : ν ^ 2 ∣ l := by
  rw [show ν ^ 4 = ν ^ 2 * ν ^ 2 by ring] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hν)).mp h

example (a b μ α lam m k l x₂ y₂ x₃ y₃ ν : ℤ)
    (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) (h₃ : y₃ ^ 2 = a * x₃ ^ 2 + b)
    (hm : 0 < m) (hx : x₂ + x₃ = m * k) (hy : y₂ + y₃ = m * l)
    (_hkl : IsCoprime k l) (ha : a = μ * α) (hl : l ^ 2 = μ * lam)
    (_hαlam : IsCoprime α lam) (hν : Prime ν) (_hνpos : 0 < ν)
    (hνodd : IsCoprime ν 2) (hμ : ν ^ 2 ∣ μ)
    (hreduced : ¬ (ν ^ 2 ∣ a ∧ ν ^ 2 ∣ b)) : ν ^ 2 ∣ l := by
  have hνa : ν ^ 2 ∣ a := ha ▸ dvd_mul_of_dvd_left hμ α
  have hνb : ¬ ν ^ 2 ∣ b := fun hb => hreduced ⟨hνa, hb⟩
  have hlsq : ν ^ 2 ∣ l ^ 2 := hl ▸ dvd_mul_of_dvd_left hμ lam
  have hnusq : ν ∣ ν ^ 2 := ⟨ν, by ring⟩
  have hνl : ν ∣ l := by
    have hh := hnusq.trans hlsq
    rw [pow_two] at hh
    exact (hν.dvd_mul.mp hh).elim id id
  have hsum : ν ∣ y₂ + y₃ := by
    rw [hy]
    exact dvd_mul_of_dvd_right hνl m
  have hdiff : ¬ ν ∣ y₂ - y₃ := by
    intro hdiff
    have htwoy : ν ∣ 2 * y₂ := by
      convert dvd_add hsum hdiff using 1
      ring
    have hy₂ : ν ∣ y₂ := hνodd.dvd_of_dvd_mul_left htwoy
    apply hνb
    convert dvd_sub (pow_dvd_pow_of_dvd hy₂ 2) (dvd_mul_of_dvd_left hνa (x₂ ^ 2)) using 1
    nlinarith [h₂]
  have he : m * (l * (y₂ - y₃) - a * k * (x₂ - x₃)) = 0 := by
    linear_combination h₂ - h₃ - (y₂ - y₃) * hy + a * (x₂ - x₃) * hx
  have hcancel : l * (y₂ - y₃) = a * k * (x₂ - x₃) := by
    have hh := (mul_eq_zero.mp he).resolve_left (ne_of_gt hm)
    linarith
  have hprod : ν ^ 2 ∣ l * (y₂ - y₃) := by
    rw [hcancel]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hνa k) (x₂ - x₃)
  obtain ⟨t, ht⟩ := hνl
  have htprod : ν ∣ t * (y₂ - y₃) := by
    apply (mul_dvd_mul_iff_left hν.ne_zero).mp
    simpa only [pow_two, ht, mul_assoc] using hprod
  obtain ⟨v, hv⟩ := (hν.dvd_mul.mp htprod).resolve_right hdiff
  exact ⟨v, by rw [ht, hv]; ring⟩

/-
Würde jedoch μ den Factor 2²ⁿ enthalten, so müssten b und
sämmtliche y ungerade Zahlen sein; y₂+y₃ wäre dann durch
2²ⁿ⁻¹ und y₂−y₃ durch 2 theilbar; käme überdies in x₂+x₃ der
Factor 2ᵐ vor, so müsste y₂+y₃ ein Vielfaches von 2²ⁿ⁺ᵐ⁻¹ sein,
so dass nach erfolgter Abkürzung der Binome y₂+y₃ und x₂+x₃
in l noch immer 2²ⁿ⁻¹ verbliebe, und weil der zweite Factor im
Zähler des Bruches in (C) wegen der Beschaffenheit der Zahlen
a, b, y₂, y₃ ebenfalls geradzahlig sein muss, so ist der Zähler des
Bruches in (C) durch 2²ⁿ theilbar.
-/

example (l : ℤ) (n m : ℕ) (hn : 1 ≤ n)
    (h : (2 : ℤ) ^ (2 * n + m - 1) ∣ 2 ^ m * l) : (2 : ℤ) ^ (2 * n - 1) ∣ l := by
  have he : 2 * n + m - 1 = m + (2 * n - 1) := by omega
  rw [he, pow_add] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero m (by norm_num : (2 : ℤ) ≠ 0))).mp h

example (A B U V x₂ x₃ : ℤ) :
    Even ((2 * U + 1) * (2 * V + 1) + 2 * A * x₂ * x₃ - (2 * B + 1)) := by
  exact ⟨2 * U * V + U + V + A * x₂ * x₃ - B, by ring⟩

example (a b μ α lam m k l x₁ y₁ x₂ y₂ x₃ y₃ : ℤ) (n : ℕ)
    (hn : 1 ≤ n) (h₁ : y₁ ^ 2 = a * x₁ ^ 2 + b)
    (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) (h₃ : y₃ ^ 2 = a * x₃ ^ 2 + b)
    (hm : 0 < m) (hx : x₂ + x₃ = m * k) (hy : y₂ + y₃ = m * l)
    (_hkl : IsCoprime k l) (ha : a = μ * α) (hl : l ^ 2 = μ * lam)
    (_hαlam : IsCoprime α lam) (hμ : (2 : ℤ) ^ (2 * n) ∣ μ)
    (hreduced : ¬ ((4 : ℤ) ∣ a ∧ (4 : ℤ) ∣ b)) :
    Odd b ∧ Odd y₁ ∧ Odd y₂ ∧ Odd y₃ ∧ (2 : ℤ) ^ (2 * n - 1) ∣ l := by
  have hpower : (2 : ℤ) ^ (2 * n) ∣ a := ha ▸ dvd_mul_of_dvd_left hμ α
  have hlsq : (2 : ℤ) ^ (2 * n) ∣ l ^ 2 := hl ▸ dvd_mul_of_dvd_left hμ lam
  have hfour : (4 : ℤ) ∣ (2 : ℤ) ^ (2 * n) := by
    have hh := pow_dvd_pow (2 : ℤ) (show 2 ≤ 2 * n by omega)
    norm_num at hh
    exact hh
  have ha4 : (4 : ℤ) ∣ a := hfour.trans hpower
  have hb4 : ¬ (4 : ℤ) ∣ b := fun hb => hreduced ⟨ha4, hb⟩
  have odd_solution (X Y : ℤ) (hY : Y ^ 2 = a * X ^ 2 + b) : Odd Y := by
    rcases Int.even_or_odd Y with hEven | hOdd
    · exfalso
      apply hb4
      obtain ⟨t, ht⟩ := hEven
      obtain ⟨A, hA⟩ := ha4
      refine ⟨t ^ 2 - A * X ^ 2, ?_⟩
      rw [ht, hA] at hY
      nlinarith [hY]
    · exact hOdd
  have hy₁ := odd_solution x₁ y₁ h₁
  have hy₂ := odd_solution x₂ y₂ h₂
  have hy₃ := odd_solution x₃ y₃ h₃
  have hbOdd : Odd b := by
    obtain ⟨t, ht⟩ := hy₁
    obtain ⟨A, hA⟩ := ha4
    refine ⟨2 * t ^ 2 + 2 * t - 2 * A * x₁ ^ 2, ?_⟩
    rw [ht, hA] at h₁
    nlinarith [h₁]
  refine ⟨hbOdd, hy₁, hy₂, hy₃, ?_⟩
  have hprime2 : Prime (2 : ℤ) := by norm_num
  have h2l : (2 : ℤ) ∣ l := by
    exact hprime2.dvd_of_dvd_pow ((show (2 : ℤ) ∣ 4 by norm_num).trans (hfour.trans hlsq))
  by_cases hn1 : n = 1
  · simpa [hn1] using h2l
  have h16lsq : (16 : ℤ) ∣ l ^ 2 := by
    have hh := pow_dvd_pow (2 : ℤ) (show 4 ≤ 2 * n by omega)
    norm_num at hh
    exact hh.trans hlsq
  have h4l : (4 : ℤ) ∣ l := by
    obtain ⟨t, ht⟩ := h2l
    have heq : l ^ 2 = 4 * t ^ 2 := by rw [ht]; ring
    rw [heq] at h16lsq
    have h4tsq : (4 : ℤ) ∣ t ^ 2 :=
      (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h16lsq
    obtain ⟨u, hu⟩ := hprime2.dvd_of_dvd_pow ((show (2 : ℤ) ∣ 4 by norm_num).trans h4tsq)
    exact ⟨u, by rw [ht, hu]; ring⟩
  have h4sum : (4 : ℤ) ∣ y₂ + y₃ := by
    rw [hy]
    exact dvd_mul_of_dvd_right h4l m
  have h2diff : (2 : ℤ) ∣ y₂ - y₃ := by
    obtain ⟨u, hu⟩ := hy₂
    obtain ⟨v, hv⟩ := hy₃
    exact ⟨u - v, by rw [hu, hv]; ring⟩
  have hnot4diff : ¬ (4 : ℤ) ∣ y₂ - y₃ := by
    intro hh
    have h4two : (4 : ℤ) ∣ 2 * y₂ := by
      convert dvd_add h4sum hh using 1
      ring
    have h2y : (2 : ℤ) ∣ y₂ :=
      (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h4two
    have hoddmod := Int.odd_iff.mp hy₂
    have hevenmod := Int.emod_eq_zero_of_dvd h2y
    omega
  obtain ⟨v, hv⟩ := h2diff
  have hvOdd : Odd v := by
    rcases Int.even_or_odd v with hEven | hOdd
    · exfalso
      apply hnot4diff
      obtain ⟨t, ht⟩ := hEven
      exact ⟨t, by rw [hv, ht]; ring⟩
    · exact hOdd
  have hcop : IsCoprime (2 : ℤ) v := by
    obtain ⟨t, ht⟩ := hvOdd
    exact ⟨-t, 1, by rw [ht]; ring⟩
  have he : m * (l * (y₂ - y₃) - a * k * (x₂ - x₃)) = 0 := by
    linear_combination h₂ - h₃ - (y₂ - y₃) * hy + a * (x₂ - x₃) * hx
  have hcancel : l * (y₂ - y₃) = a * k * (x₂ - x₃) := by
    have hh := (mul_eq_zero.mp he).resolve_left (ne_of_gt hm)
    linarith
  have hprod : (2 : ℤ) ^ (2 * n) ∣ l * (y₂ - y₃) := by
    rw [hcancel]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpower k) (x₂ - x₃)
  have hpow : (2 : ℤ) ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
    calc
      _ = (2 : ℤ) ^ (1 + (2 * n - 1)) := congrArg (fun e => (2 : ℤ) ^ e) (by omega)
      _ = _ := by rw [pow_add]; norm_num
  have hlv : (2 : ℤ) ^ (2 * n - 1) ∣ l * v := by
    apply (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp
    rw [hpow, hv] at hprod
    convert hprod using 1
    ring
  exact hcop.pow_left.dvd_of_dvd_mul_right hlv

example (a k l x₁ y₁ V : ℤ) (n : ℕ) (hn : 1 ≤ n)
    (ha : (2 : ℤ) ^ (2 * n) ∣ a) (hl : (2 : ℤ) ^ (2 * n - 1) ∣ l)
    (hV : Even V) : (2 : ℤ) ^ (2 * n) ∣ (y₁ * l - a * x₁ * k) * V := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨L, hL⟩ := hl
  obtain ⟨v, hv⟩ := hV
  have he : 2 * n = (2 * n - 1) + 1 := by omega
  refine ⟨(y₁ * L - 2 * A * x₁ * k) * v, ?_⟩
  have hp : (2 : ℤ) ^ (2 * n) = 2 ^ (2 * n - 1) * 2 := by
    calc
      _ = (2 : ℤ) ^ ((2 * n - 1) + 1) := congrArg (fun e => (2 : ℤ) ^ e) he
      _ = _ := by rw [pow_add]; norm_num
  rw [hA, hL, hv, hp]
  ring

/-
Die Brüche in (C) und (D) können somit nach erfolgter
Reduction keinen grösseren Nenner haben als b.
-/

example (a b x₁ y₁ x₂ y₂ x₃ y₃ : ℤ)
    (_hb : b ≠ 0) (_h₁ : y₁ ^ 2 = a * x₁ ^ 2 + b)
    (h₂ : y₂ ^ 2 = a * x₂ ^ 2 + b) (h₃ : y₃ ^ 2 = a * x₃ ^ 2 + b)
    (hu : (y₂ : ℚ) * y₃ - a * x₂ * x₃ + b ≠ 0) :
    ∃ n : ℤ, (b : ℚ) * (x₁ - (y₁ * ((y₂ : ℚ) + y₃) - a * x₁ * (x₂ + x₃)) /
      ((y₂ : ℚ) * y₃ - a * x₂ * x₃ + b) * (x₂ + x₃)) = n := by
  refine ⟨x₁ * (y₂ * y₃ + a * x₂ * x₃) - y₁ * (x₂ * y₃ + x₃ * y₂), ?_⟩
  have h₂q : (y₂ : ℚ) ^ 2 = a * (x₂ : ℚ) ^ 2 + b := by exact_mod_cast h₂
  have h₃q : (y₃ : ℚ) ^ 2 = a * (x₃ : ℚ) ^ 2 + b := by exact_mod_cast h₃
  push_cast
  field_simp
  linear_combination
    (-(x₁ : ℚ) * (y₃ : ℚ) ^ 2 + x₃ * y₁ * (y₃ : ℚ)) * h₂q +
    (-(a : ℚ) * x₁ * (x₂ : ℚ) ^ 2 - b * x₁ + x₂ * y₁ * (y₂ : ℚ)) * h₃q

/-
Ist b eine Primzahl, so wird wegen der Gleichung (B) x stets
eine ganze Zahl; ist b aber ein Product, so kann ein Factor von
b im Nenner zurückbleiben, und dann ist x ein Bruch.

2. Da wegen der Form der gegebenen Gleichung die Werthe
der Unbekannten positiv und negativ genommen werden können,
so repräsentirt das Binom x₂+x₃ folgende vier Verbindungen:
x₂+x₃, x₂−x₃, −x₂+x₃, −x₂−x₃,
und da ein Gleiches auch für y₂+y₃ gilt, so ergeben sich für d
-/

/-
Seite 38

folgende acht Brüche:
±(y₂+y₃)/(x₂+x₃), ±(y₂−y₃)/(x₂−x₃),
±(y₂+y₃)/(x₂−x₃), ±(y₂−y₃)/(x₂+x₃),
mit denen der Versuch, einen oder mehrere neue ganzzahlige
Werthe für x zu finden, zu machen ist.
-/

example (x₂ x₃ y₂ y₃ : ℚ) :
    (-y₂ - y₃) / (-x₂ - x₃) = (y₂ + y₃) / (x₂ + x₃) := by
  calc
    _ = (-(y₂ + y₃)) / (-(x₂ + x₃)) := by congr 1 <;> ring
    _ = _ := neg_div_neg_eq _ _

/-
3. Das Einsetzen dieser Brüche kann aber nur dann Erfolg
haben, wenn der Coëfficient von x², nämlich die Zahl a im
Nenner der p-Function intact vorkömmt; wäre jedoch dieser
Bruch durch einen quadratischen Factor von a, etwa durch ν²
abgekürzt worden, so müsste auch jeder für p einzusetzende
Bruch durch ν dividirt werden.
-/

example (a p ν : ℚ) (hν : ν ≠ 0) :
    (p / ν) ^ 2 - a / ν ^ 2 = (p ^ 2 - a) / ν ^ 2 := by field_simp

example (a x₁ y₁ p ν : ℚ) (hν : ν ≠ 0) (_hd : p ^ 2 - a ≠ 0) :
    x₁ - 2 * ((y₁ / ν) * (p / ν) - (a / ν ^ 2) * x₁) /
      ((p / ν) ^ 2 - a / ν ^ 2) =
    x₁ - 2 * (y₁ * p - a * x₁) / (p ^ 2 - a) := by
  have he : (p / ν) ^ 2 - a / ν ^ 2 = (p ^ 2 - a) / ν ^ 2 := by field_simp
  rw [he]
  field_simp

/-
4. Da in dieser Rechnung x₁, y₁ für x₃, y₃ gesetzt werden
kann, so gilt dieser Satz auch dann, wenn für x blos zwei
Werthe bekannt sind, und häufig lassen sich schon mit x₁ und x₂
neue Wurzeln finden; in Peel's Problem jedoch sind, wenn x = 0
gezählt wird, noch zwei Werthe erforderlich.

5. Sollten die zwei Wurzeln x₁ und x₂ nicht genügen, so
suche man mittelst der Substitution p = y₂/x₂ eine dritte Wurzel,
oder was noch sicherer ist, man finde für x₂ die äquivalenten
Substitutionen (§. 3, 10) und setze dieselben mit entgegengesetzten
Vorzeichen in die p-Function; besonders dann, wenn vier Äquivalente
gefunden wurden, dürfte eines derselben ein ganzzahliges
neues x liefern.
-/

/-
6. Bei Anwendung dieser Additionsmethode kommt man
auf alle innerhalb eines beliebig bestimmten Zahlenraumes
liegenden Werthe von x. Auch wenn a negativ und das Zahlenglied
gross ist, kann dieses Verfahren zur Auffindung solcher
Wurzeln, welche die p-Function nicht liefert, mit Vortheil benützt
werden; sonst müsste man aus einem der gefundenen Wurzelpaare
— etwa aus x₂, y₂ — eine neue p-Function bilden, und
mit dieser die etwa noch unbekannten Werthe suchen, was eine
mühsamere Rechnung ist (§. 13, 2).
-/

/-
Formalisierungsschema der Vollständigkeitsbehauptung: Das Prädikat
durchAdditionErreichbar bezeichnet die mit der beschriebenen
Additionsmethode erreichbaren ganzzahligen Werthe von x. Es bleibt
hier ein ausdrücklicher Parameter, weil der allgemeine Satz weder
die Anfangswurzeln noch die Ausführung der Ersatzsubstitutionen
vollständig festlegt. Im zweiten Exempel werden kleinste Anfangswurzeln
verwendet. Eine Aussage für beliebige Anfangswurzeln wird daraus nicht
abgeleitet; auch a wird hier nicht auf positive Zahlen beschränkt.

Die folgende Proposition hält das behauptete Erreichen aller Lösungen
in jedem vorgegebenen Zahlenintervall fest, ohne es zu beweisen.
Sie legt die Bedeutung von durchAdditionErreichbar nicht selbst fest
und ist daher noch keine vollständige Formalisierung des Verfahrens.
-/

example (a b : ℤ) (durchAdditionErreichbar : ℤ → Prop) : Prop :=
  ∀ untere obere x : ℤ,
    untere ≤ x → x ≤ obere →
    (∃ y : ℤ, y ^ 2 = a * x ^ 2 + b) → durchAdditionErreichbar x

namespace Beispiel01

/-
7. Erstes Exempel.
y² = 30x²+91, x = 1−2(11p−30)/(p²−30), S = 60.91
-/

def x (p : ℚ) : ℚ := 1 - 2 * (11 * p - 30) / (p ^ 2 - 30)

#guard (60 * 91 : ℤ) = 5460

/-
Seite 39

x =  1   3   5  11   71..., für p = (29+19)/(5+3) = 6 wird x = 11
y = 11  19  29  61  389..., für p = (29−19)/(5−3) = 5 wird x = 11
für p = −6 kommt x = 33
 „  p = −5   „   x = 33;
-/

#guard ([(1, 11), (3, 19), (5, 29), (11, 61), (71, 389)] : List (ℤ × ℤ)).all
  fun (x, y) => y ^ 2 == 30 * x ^ 2 + 91

#guard ((29 + 19) / (5 + 3) : ℚ) = 6

#guard ((29 - 19) / (5 - 3) : ℚ) = 5

#guard ([(6, 11), (5, 11), (-6, 33), (-5, 33)] : List (ℚ × ℚ)).all
  fun (p, v) => (x p) ^ 2 == v ^ 2

/-
die übrigen vier Werthe von p nämlich
p = ±(29+19)/(5−3) und p = ±(29−19)/(5+3)
liefern kein ganzzahliges x.
-/

#guard ([24, -24, 5/4, -5/4] : List ℚ).all fun p => (x p).den != 1

/-
Für p = −(389+19)/(71+3) = −204/37 und für
−(389−19)/(71−3) = −185/34 wird x = 3189/7,
weil für diese Werthe von p keines der in (B)
rechtsstehenden Binome durch 91 theilbar ist (§. 9, 1).
-/

#guard (-(389 + 19) / (71 + 3) : ℚ) = -204 / 37

#guard (-(389 - 19) / (71 - 3) : ℚ) = -185 / 34

#guard x (-204 / 37) = 3189 / 7

#guard (x (-185 / 34)) ^ 2 = (3189 / 7) ^ 2

/-
Dagegen
wird für p = (389+19)/(71−3) = 6 und ebenso für p = (389−19)/(71+3) = 5
x = 11 wie zuvor.
-/

#guard ((389 + 19) / (71 - 3) : ℚ) = 6

#guard ((389 - 19) / (71 + 3) : ℚ) = 5

end Beispiel01

namespace Beispiel02

/-
8. Zweites Exempel. Um die aufeinander folgenden
Wurzeln der Gleichung y² = 7x²+1 aus den kleinsten Werthen
x₂ = 3, y₂ = 8 zu finden, setze man in der Gleichung
x = −2p/(p²−7) ... p = 8/3
-/

def x (p : ℚ) : ℚ := -2 * p / (p ^ 2 - 7)

#guard (8 : ℤ) ^ 2 = 7 * 3 ^ 2 + 1

/-
da kommt x₃ = −48, und aus der Gleichung y = px+1 folgt
y₃ = −127.
-/

def y (p : ℚ) : ℚ := p * x p + 1

#guard x (8 / 3) = -48

#guard y (8 / 3) = -127

/-
Für p = (127+8)/(48+3) = 45/17 und für
p = (127−8)/(48−3) = 119/45 kommt
— vom Vorzeichen abgesehen — x₄ = 765 und y₄ = 2024; die
anderen Werthe von p liefern x = 3; und so lassen sich noch
fernere Werthe für x finden.
-/

#guard ((127 + 8) / (48 + 3) : ℚ) = 45 / 17

#guard ((127 - 8) / (48 - 3) : ℚ) = 119 / 45

#guard ([45/17, 119/45] : List ℚ).all
  fun p => (x p) ^ 2 == 765 ^ 2 && (y p) ^ 2 == 2024 ^ 2

#guard ([3, -3, 7/3, -7/3] : List ℚ).all fun p => (x p) ^ 2 == 3 ^ 2

#guard (2024 : ℤ) ^ 2 = 7 * 765 ^ 2 + 1

end Beispiel02

end Kunerth1877.Paragraf09
