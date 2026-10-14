/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1878b.AllgemeinerTeil

/-
Seite 338.

Numerische Auflösung quadratischer Congruenzen für jeden einfachen
Modul.

Die im Vorangehenden dargestellte Methode lässt sich mit einigen
Modificationen auch zur Lösung quadratischer Congruenzen benützen.

Ist in der Congruenz y² ≡ d (mod b) der Modul b eine einfache und d eine
unter ihm liegende positive oder negative Zahl, so untersuche man
zuförderst, ob +b oder −b ein quadratischer Rest von d ist. Im
bejahenden Falle hat man die, jene Congruenz vertretende Gleichung y² =
bx + d auf die unter (II) im vorigen Abschnitte vorgeschriebene Form zu
bringen; im verneinenden, zumeist vorkommenden Falle hingegen, bilde man
aus d durch successives Hinzuaddiren von +b wie auch nebenbei von −b
eine solche kleinste Zahl c = d ± nb, dass +b oder −b ein quadratischer
Rest von c, und dabei der grösste Divisor von c kleiner als b werde;
doch dürfen diese Zahlen nicht beide zugleich negativ sein, weil sonst
die spätere Gleichung [4] unmöglich wäre.
-/
example (b d n x : ℤ) : b * x + (d + n * b) = b * (x + n) + d := by
  ring

/-
Hierauf gebe man der mit der Congruenz y² ≡ c (mod b) äquivalenten
Gleichung

y² = bx + c [1]
-/
example (b c y : ℤ) : y ^ 2 % b = c % b ↔
    ∃ x : ℤ, y ^ 2 = b * x + c := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by omega⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by omega⟩

/-
die Form

y² = (αx + β)² − (γx + δ)(εx + ζ), [2]

was dadurch bewerkstelligt wird, dass man zu [1] die identische
Gleichung 0 = (αx + β)² − α²x² − 2αβx − β² hinzuaddirt, in welcher α und
β noch unbestimmte Zahlen bezeichnen.
-/
example (α β x : ℚ) :
    0 = (α * x + β) ^ 2 - α ^ 2 * x ^ 2 - 2 * α * β * x - β ^ 2 := by
  ring

/-
Damit in der so erhaltenen Gleichung

y² = (αx + β)² − [α²x² + (2αβ − b)x + (β² − c)]

das eckig eingeklammerte Trinom ein Product zweier linearen Factoren
werde, muss seine Determinante ein Quadrat sein; also

(2αβ − b)² − 4α²(β² − c) = Δ² oder Δ² = 4cα² − 4bαβ + b²;
-/
example (b c α β x : ℚ) : b * x + c = (α * x + β) ^ 2 -
    (α ^ 2 * x ^ 2 + (2 * α * β - b) * x + (β ^ 2 - c)) := by ring

example (b c α β γ δ ε ζ : ℚ)
    (h : ∀ x : ℚ, α ^ 2 * x ^ 2 + (2 * α * β - b) * x +
      (β ^ 2 - c) = (γ * x + δ) * (ε * x + ζ)) :
    ∃ Δ : ℚ, (2 * α * β - b) ^ 2 - 4 * α ^ 2 * (β ^ 2 - c) = Δ ^ 2 := by
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h (-1)
  have hA : α ^ 2 = γ * ε := by nlinarith [h₀, h₁, h₂]
  have hB : 2 * α * β - b = γ * ζ + δ * ε := by nlinarith [h₁, h₂]
  have hC : β ^ 2 - c = δ * ζ := by simpa using h₀
  refine ⟨γ * ζ - δ * ε, ?_⟩
  rw [hA, hB, hC]
  ring

example (b c α β : ℚ) :
    (2 * α * β - b) ^ 2 - 4 * α ^ 2 * (β ^ 2 - c) =
      4 * c * α ^ 2 - 4 * b * α * β + b ^ 2 := by ring

/-
Seite 339.

setzt man hier Δ = 2pα + b, so wird α = −b(p + β)/(p² − c) und für p =
v/w:

α = −bw(v + βw)/(v² − cw²) [3]
-/
example (b c p β : ℚ) (h : p ^ 2 - c ≠ 0) :
    (2 * p * (-b * (p + β) / (p ^ 2 - c)) + b) ^ 2 =
      4 * c * (-b * (p + β) / (p ^ 2 - c)) ^ 2 -
      4 * b * (-b * (p + β) / (p ^ 2 - c)) * β + b ^ 2 := by
  field_simp
  ring

example (b c v w β : ℚ) (hw : w ≠ 0)
    (_h : v ^ 2 - c * w ^ 2 ≠ 0) :
    -b * (v / w + β) / ((v / w) ^ 2 - c) =
      -b * w * (v + β * w) / (v ^ 2 - c * w ^ 2) := by
  field_simp

/-
Bestimmt man aus der, wegen der oben herbeigeführten Beschaffenheit von
b und c, in Rationalzahlen möglichen Gleichung

v² − cw² = ±b [4]

die Grössen v und w nach der im ersten Abschnitte angegebenen Methode,
und setzt die gefundenen positiv zu nehmenden Werthe v₀ und w₀ in die
Gleichung [3] ein, so wird

α = ∓w₀(v₀ + w₀β) [5]
-/
example (b c v w β : ℚ) (hb : b ≠ 0)
    (h : v ^ 2 - c * w ^ 2 = b) :
    -b * w * (v + β * w) / (v ^ 2 - c * w ^ 2) = -w * (v + w * β) := by
  rw [h]
  field_simp

example (b c v w β : ℚ) (hb : b ≠ 0)
    (h : v ^ 2 - c * w ^ 2 = -b) :
    -b * w * (v + β * w) / (v ^ 2 - c * w ^ 2) = w * (v + w * β) := by
  rw [h]
  field_simp

/-
Nun ist der Unbestimmten β ein solcher Werth zu ertheilen, dass α eine
möglichst kleine ganze Zahl werde, was bei einem ganzzahligen w₀
sogleich erreicht wird, wenn man für β die dem Quotienten −v₀/w₀ nächst
liegende negative ganze Zahl setzt, sonst aber durch Lösung einer
unbestimmten einfachen Gleichung zu Stande kömmt.
-/
example (b : ℕ) (c w : ℤ) (v : ℚ) (hb : b.Prime)
    (_hv : 0 < v) (hw : 0 < w)
    (hnorm : v ^ 2 - c * (w : ℚ) ^ 2 = b ∨
      v ^ 2 - c * (w : ℚ) ^ 2 = -(b : ℚ))
    (β : ℤ) (_hneg : β < 0)
    (hβ : ∀ k : ℤ, k < 0 → |(β : ℚ) + v / w| ≤ |(k : ℚ) + v / w|) :
    ∃ α : ℤ, (α : ℚ) = -(b : ℚ) * w * (v + w * β) /
        (v ^ 2 - c * (w : ℚ) ^ 2) ∧
      ∀ k : ℤ, k < 0 → |(α : ℚ)| ≤
        |-(b : ℚ) * w * (v + w * k) / (v ^ 2 - c * (w : ℚ) ^ 2)| := by
  obtain ⟨α, hα⟩ : ∃ α : ℤ, (α : ℚ) = -(b : ℚ) * w * (v + w * β) /
      (v ^ 2 - c * (w : ℚ) ^ 2) := by
    obtain ⟨N, hN⟩ : ∃ N : ℤ, v ^ 2 = (N : ℚ) := by
      rcases hnorm with h | h
      · refine ⟨c * w ^ 2 + b, ?_⟩
        push_cast
        linarith
      · refine ⟨c * w ^ 2 - b, ?_⟩
        push_cast
        linarith
    have hSquare : IsSquare (N : ℚ) := ⟨v, by nlinarith [hN]⟩
    obtain ⟨V, hV⟩ := Rat.isSquare_intCast_iff.mp hSquare
    have hVq : v ^ 2 = (V : ℚ) ^ 2 := by
      rw [hN, hV]
      push_cast
      ring
    obtain ⟨v₀, rfl⟩ : ∃ v₀ : ℤ, (v₀ : ℚ) = v := by
      rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hVq) with h | h
      · exact ⟨V, h.symm⟩
      · exact ⟨-V, by simpa using h.symm⟩
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne_zero
    rcases hnorm with h | h
    · refine ⟨-w * (v₀ + w * β), ?_⟩
      push_cast
      rw [h]
      field_simp
    · refine ⟨w * (v₀ + w * β), ?_⟩
      push_cast
      rw [h]
      field_simp
  refine ⟨α, hα, ?_⟩
  intro k hk
  have hwq : (w : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hw)
  have hscale (j : ℤ) :
      -(b : ℚ) * w * (v + w * j) / (v ^ 2 - c * (w : ℚ) ^ 2) =
        (-(b : ℚ) * (w : ℚ) ^ 2 / (v ^ 2 - c * (w : ℚ) ^ 2)) *
          ((j : ℚ) + v / w) := by
    have hlinear : v + (w : ℚ) * j = (w : ℚ) * ((j : ℚ) + v / w) := by
      field_simp
      ring
    rw [hlinear]
    ring
  rw [hα, hscale β, hscale k, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hβ k hk) (abs_nonneg _)

/-
Ist nämlich w = λ/ν und v = μ/ν, so wird α = −λ(μ + λβ)/ν² sein, und man
hat aus der Gleichung μ + λβ = ν²s, in welcher β und s unbekannt sind,
für s die kleinste ganze Zahl zu finden; oder man löse die Congruenz λβ
+ μ ≡ 0 (mod ν²) und benütze einen kleinen Werth von β.
-/
example («λ» μ ν β : ℤ) (_hν : ν ≠ 0) :
    -((«λ» : ℚ) / ν) * ((μ : ℚ) / ν + ((«λ» : ℚ) / ν) * β) =
      -(«λ» : ℚ) / (ν : ℚ) ^ 2 * ((μ : ℚ) + «λ» * β) := by ring

example («λ» μ ν β s : ℤ) (hν : ν ≠ 0) (h : μ + «λ» * β = ν ^ 2 * s) :
    -(«λ» : ℚ) / (ν : ℚ) ^ 2 * ((μ : ℚ) + «λ» * β) = -(«λ» : ℚ) * s := by
  have hνq : (ν : ℚ) ≠ 0 := by exact_mod_cast hν
  have hq : (μ : ℚ) + «λ» * β = (ν : ℚ) ^ 2 * s := by exact_mod_cast h
  rw [hq]
  field_simp

example («λ» μ ν β : ℤ) (_hν : ν ≠ 0) : («λ» * β + μ) % ν ^ 2 = 0 ↔
    ∃ s : ℤ, μ + «λ» * β = ν ^ 2 * s := by
  rw [← Int.dvd_iff_emod_eq_zero]
  simpa only [add_comm] using
    (dvd_iff_exists_eq_mul_right : ν ^ 2 ∣ «λ» * β + μ ↔ _)

example (σ «λ» μ ν β s : ℤ) (hν : ν ≠ 0)
    (hprep : μ + «λ» * β = ν ^ 2 * s) :
    -(σ : ℚ) * ((«λ» : ℚ) / ν) * ((μ : ℚ) / ν + ((«λ» : ℚ) / ν) * β) =
      ((-σ * «λ» * s : ℤ) : ℚ) := by
  have hνq : (ν : ℚ) ≠ 0 := by exact_mod_cast hν
  have hq : (μ : ℚ) + «λ» * β = (ν : ℚ) ^ 2 * s := by exact_mod_cast hprep
  have he : -(σ : ℚ) * ((«λ» : ℚ) / ν) *
      ((μ : ℚ) / ν + ((«λ» : ℚ) / ν) * β) =
      -(σ : ℚ) * «λ» / (ν : ℚ) ^ 2 * ((μ : ℚ) + «λ» * β) := by ring
  rw [he, hq]
  push_cast
  field_simp

/-
Sind α und β bestimmt, so kann die Transformation [2] ausgeführt werden,
wobei jedoch zu bemerken ist, dass in dieser Gleichung bei dem hier
eingeschlagenen Gange der Rechnung die Coefficienten γ und ε stets
Quadratzahlen sein müssen, daher [2] eigentlich so zu schreiben ist:

y² = (αx + β)² − (γ²x + δ)(ε²x + ζ) [6]
-/
example (b : ℕ) (c σ «λ» μ ν β s : ℤ) (_hb : b.Prime)
    (_hc : c ≠ 0) (_hf : ∀ p : ℕ, p.Prime → p ∣ c.natAbs → p < b)
    (hσ : σ = 1 ∨ σ = -1) (_hsign : 0 < c ∨ 0 < σ * b) (hν : ν ≠ 0)
    (_hv : 0 < (μ : ℚ) / ν) (_hw : 0 < («λ» : ℚ) / ν)
    (hnorm : ((μ : ℚ) / ν) ^ 2 - c * ((«λ» : ℚ) / ν) ^ 2 = σ * b)
    (hprep : μ + «λ» * β = ν ^ 2 * s) :
    let α : ℤ := -σ * «λ» * s
    ∃ γ δ ε ζ : ℤ, ∀ x : ℚ,
      b * x + c = ((α : ℚ) * x + β) ^ 2 -
        ((γ : ℚ) ^ 2 * x + δ) * ((ε : ℚ) ^ 2 * x + ζ) := by
  let w : ℚ := («λ» : ℚ) / ν
  let P : ℤ := w.num
  let Q : ℤ := w.den
  have hQ : Q ≠ 0 := by dsimp [Q]; exact_mod_cast w.den_ne_zero
  have hQq : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ
  have hνq : (ν : ℚ) ≠ 0 := by exact_mod_cast hν
  have hdiv : Q ∣ ν := by
    simpa only [Q, w, Rat.divInt_eq_div] using Rat.den_dvd «λ» ν
  obtain ⟨t, ht⟩ := hdiv
  have ht₀ : t ≠ 0 := by intro hz; rw [hz, mul_zero] at ht; exact hν ht
  have hnum : (P : ℚ) / Q = («λ» : ℚ) / ν := by
    exact Rat.num_div_den w
  have hLamq : («λ» : ℚ) = P * t := by
    have htq : (ν : ℚ) = Q * t := by exact_mod_cast ht
    field_simp at hnum
    rw [htq] at hnum
    apply (mul_right_cancel₀ hQq)
    nlinarith [hnum]
  have hLam : «λ» = P * t := by exact_mod_cast hLamq
  have hμ : μ = t * (Q ^ 2 * t * s - P * β) := by
    rw [ht, hLam] at hprep
    nlinarith [hprep]
  have hnormI : μ ^ 2 - c * «λ» ^ 2 = σ * b * ν ^ 2 := by
    field_simp at hnorm
    have hn : μ ^ 2 - c * «λ» ^ 2 = ν ^ 2 * σ * b := by exact_mod_cast hnorm
    nlinarith [hn]
  rw [hμ, hLam, ht] at hnormI
  have hnormReduced : (Q ^ 2 * t * s - P * β) ^ 2 - c * P ^ 2 = σ * b * Q ^ 2 := by
    apply (mul_left_cancel₀ (pow_ne_zero 2 ht₀))
    linear_combination hnormI
  have hcop : IsCoprime P Q := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa [P, Q, Int.gcd] using w.reduced
  have hd : Q ^ 2 ∣ β ^ 2 - c := by
    have hcop₂ : IsCoprime (Q ^ 2) (P ^ 2) := hcop.symm.pow_left.pow_right
    apply hcop₂.dvd_of_dvd_mul_left
    refine ⟨σ * b - Q ^ 2 * t ^ 2 * s ^ 2 + 2 * P * t * s * β, ?_⟩
    linear_combination hnormReduced
  obtain ⟨k, hk⟩ := hd
  refine ⟨P, -σ * Q ^ 2, t * s, -σ * k, ?_⟩
  intro x
  have hσq : (σ : ℚ) ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hkq : (β : ℚ) ^ 2 - c = (Q : ℚ) ^ 2 * k := by exact_mod_cast hk
  have hNq : ((Q : ℚ) ^ 2 * t * s - P * β) ^ 2 - c * P ^ 2 = σ * b * Q ^ 2 := by
    exact_mod_cast hnormReduced
  have hmiddle : (b : ℚ) = (σ : ℚ) *
      (-2 * P * t * s * β + P ^ 2 * k + Q ^ 2 * t ^ 2 * s ^ 2) := by
    apply (mul_right_cancel₀ (pow_ne_zero 2 hQq))
    linear_combination -σ * hNq + σ * P ^ 2 * hkq - b * Q ^ 2 * hσq
  push_cast
  rw [hLamq, hmiddle]
  linear_combination
    (-(P : ℚ) ^ 2 * t ^ 2 * s ^ 2 * x ^ 2 + Q ^ 2 * k) * hσq - hkq

/-
Es kann nämlich, da b eine Primzahl bedeutet, der rechte Flügel in [1]
d. i. bx + c nur dann ein Quadrat werden, wenn für x ein Bruch gesetzt
wird, dessen Nenner eine Quadratzahl

Seite 340.

(also auch 1) oder b oder endlich ein Product dieser beiden Zahlen ist.
Brüche der zwei letzten Arten können aus [1] in beliebiger Anzahl zwar
augenblicklich gewonnen, für den vorliegenden Zweck aber desshalb nicht
verwendet werden, weil sie die Ermittlung eines ganzzahligen Werthes für
x von der Lösung einer quadratischen Congruenz nach dem Modul b abhängig
machen würden, wie aus dem weiteren Verlaufe dieses Calculs zu ersehen
ist. Um daher solche Werthe für x aus [2] nicht zu erhalten, wurde in
dem Ausdrucke von α unter [3] der Factor b eliminirt und es bleiben
somit für x nur Brüche mit quadratischem Nenner übrig; desshalb stehen
in [6] die Coefficienten γ² und ε².
-/
example (b : ℕ) (c : ℤ) (x y : ℚ) (hb : b.Prime)
    (h : y ^ 2 = b * x + c) :
    IsSquare x.den ∨ x.den = b ∨ ∃ n : ℕ, IsSquare n ∧ x.den = b * n := by
  have hbx : (b : ℚ) * x = y ^ 2 - c := by linarith
  have hden : x.den = (y.den * y.den) * Nat.gcd (b * x.num.natAbs) x.den := by
    simpa [hbx, pow_two, Rat.mul_self_den, Int.natAbs_mul] using
      Rat.den_mul_den_eq_den_mul_gcd (b : ℚ) x
  have hg : Nat.gcd (b * x.num.natAbs) x.den ∣ b := by
    have hcop := Nat.Coprime.of_dvd_left (Nat.gcd_dvd_right (b * x.num.natAbs) x.den)
      x.reduced.symm
    exact hcop.dvd_of_dvd_mul_right (Nat.gcd_dvd_left _ _)
  rcases hb.eq_one_or_self_of_dvd _ hg with hg | hg
  · left
    exact ⟨y.den, by simpa [hg] using hden⟩
  · right; right
    exact ⟨y.den * y.den, ⟨y.den, rfl⟩, by simpa [hg, Nat.mul_comm] using hden⟩

/-
Weil ferner die rechte Seite dieser Gleichung sich auf bx + c reduciren
muss, so ist α²x² = γ²ε²x², also α = γε und α/γ = ε.
-/
example (α β γ δ ε ζ x : ℚ) :
    (α * x + β) ^ 2 - (γ ^ 2 * x + δ) * (ε ^ 2 * x + ζ) =
      (α ^ 2 - γ ^ 2 * ε ^ 2) * x ^ 2 +
      (2 * α * β - γ ^ 2 * ζ - δ * ε ^ 2) * x + β ^ 2 - δ * ζ := by ring

/-
Aus der jetzt fertigen Gleichung [6] fliesst sofort

x = −δ/γ², y = −αδ/γ² + β = (−δε + βγ)/γ;
-/
example (α β γ δ ε : ℚ) (hγ : γ ≠ 0) (hα : α = γ * ε) :
    -α * δ / γ ^ 2 + β = (-δ * ε + β * γ) / γ := by
  rw [hα]
  field_simp

example (α β γ δ ε ζ : ℚ) (hγ : γ ≠ 0) :
    (α * (-δ / γ ^ 2) + β) ^ 2 -
      (γ ^ 2 * (-δ / γ ^ 2) + δ) * (ε ^ 2 * (-δ / γ ^ 2) + ζ) =
        (-α * δ / γ ^ 2 + β) ^ 2 := by
  field_simp
  ring

/-
und wenn man den Zähler dieses Bruches mit κ bezeichnet, so ist y = κ/γ;
setzt man diese Werthe in [1], so entsteht die identische Gleichung
κ²/γ² = b(−δ/γ²) + c, und zieht man diese von [1] ab, so kömmt die
unbestimmte Gleichung

y² − κ²/γ² = b(x + δ/γ²) oder γ²y² = b(γ²x + δ) + κ².
-/
example (b c γ δ κ x y : ℚ) (_hγ : γ ≠ 0)
    (h₀ : κ ^ 2 / γ ^ 2 = b * (-δ / γ ^ 2) + c)
    (h : y ^ 2 = b * x + c) :
    y ^ 2 - κ ^ 2 / γ ^ 2 = b * (x + δ / γ ^ 2) := by
  rw [h, h₀]
  ring

example (b c γ δ κ x y : ℚ)
    (h₀ : κ ^ 2 = -b * δ + c * γ ^ 2) (h : y ^ 2 = b * x + c) :
    γ ^ 2 * y ^ 2 = b * (γ ^ 2 * x + δ) + κ ^ 2 := by
  rw [h, h₀]
  ring

/-
Lässt man b(γ²x + δ) + κ² = ((γ²x + δ)/q + κ)² sein, so folgt nach
bewirkter Reduction b = (γ²x + δ)/q² + 2κ/q und hieraus:

γ²x = bq² − 2κq − δ; [7]

diese Gleichung mit den Unbestimmten q und x kann fortan aus den für x
und y gefundenen Brüchen unmittelbar gebildet werden.
-/
/-
Redaktionelle Einordnung: κ bezeichnet weiterhin den zuvor bestimmten
Zähler −δε + βγ. Der folgende Ausdruck vom Typ Prop hält die behauptete
Folgerung vom Quadratansatz zur reducirten Gleichung und zu [7] fest;
er ist kein Beweis dieser Folgerung. Die Voraussetzung q ≠ 0 hält die
Definitionsbedingung der gedruckten Brüche fest.

Setzt man zur Erläuterung U = γ²x + δ, so ergibt das Beseitigen der
Nenner aus dem Quadratansatz U(U + 2κq − bq²) = 0. Die Kürzung durch U
setzt U ≠ 0 voraus. Für U = 0 ist der Quadratansatz stets erfüllt; die
reducirte Gleichung folgt daraus nicht. Dieser Fall enthält bei γ ≠ 0
den zuvor verwendeten Werth x = −δ/γ². Der Druck behandelt ihn hier
nicht gesondert. Die zusätzliche Voraussetzung U ≠ 0 wird deshalb nicht
in die aufgezeichnete Behauptung aufgenommen.
-/
example (b γ δ κ x q : ℚ) : Prop :=
  q ≠ 0 →
    b * (γ ^ 2 * x + δ) + κ ^ 2 =
      ((γ ^ 2 * x + δ) / q + κ) ^ 2 →
    b = (γ ^ 2 * x + δ) / q ^ 2 + 2 * κ / q ∧
      γ ^ 2 * x = b * q ^ 2 - 2 * κ * q - δ

/-
Formale Unterstützung: Die folgende Aussage prüft [7] durch Einsetzen
in den Quadratansatz, also in der umgekehrten Richtung.
-/
example (b γ δ κ x q : ℚ) (hq : q ≠ 0)
    (h : γ ^ 2 * x + δ = b * q ^ 2 - 2 * κ * q) :
    b * (γ ^ 2 * x + δ) + κ ^ 2 =
      ((γ ^ 2 * x + δ) / q + κ) ^ 2 := by
  rw [h]
  field_simp
  ring

/-
Formale Unterstützung: Die folgende Folgerung zu [7] setzt die bereits
reducirte Gleichung voraus.
-/
example (b γ δ κ x q : ℚ) (hq : q ≠ 0)
    (h : b = (γ ^ 2 * x + δ) / q ^ 2 + 2 * κ / q) :
    γ ^ 2 * x = b * q ^ 2 - 2 * κ * q - δ := by
  field_simp at h
  nlinarith [h]

/-
Seite 341.

Soll für x eine ganze Zahl resultiren, so muss in [7] die rechte Seite
durch γ² theilbar sein, und der dies vermittelnde Werth von q ergibt
sich aus der Congruenz

bq² − 2κq − δ ≡ 0 (mod γ²) [8]

und liefert schliesslich, in [7] eingesetzt, den gesuchten ganzzahligen
Werth von x.
-/
example (b γ δ κ q : ℤ) :
    (b * q ^ 2 - 2 * κ * q - δ) % γ ^ 2 = 0 ↔
      ∃ x : ℤ, γ ^ 2 * x = b * q ^ 2 - 2 * κ * q - δ := by
  rw [← Int.dvd_iff_emod_eq_zero]
  simpa only [eq_comm] using
    (dvd_iff_exists_eq_mul_right : γ ^ 2 ∣ b * q ^ 2 - 2 * κ * q - δ ↔ _)

/-
Wären v₀ und w₀ vielziffrige Zahlen, wodurch die weitere Rechnung
beschwerlich würde, so kann man mit diesen Werthen kleinere Zahlen für v
und w aus der Gleichung [4] finden, wenn man ihr die Gestalt (II) im
ersten Abschnitte verschafft und sich zu diesem Behufe der dortigen
Gleichung (III) bedient. Dieser zufolge ist w₀α₁ + β₁ = v₀ und α₁, β₁
sind die Unbekannten; bestimmt man diese in den kleinsten Zahlen und
transformirt [4] so wird

v² = (α₁w + β₁)² + (γ₁w + δ₁)(ε₁w + ζ₁);

und dieser Gleichung können für w und v mit weniger Ziffern geschriebene
Werthe entnommen werden, die hierauf in [5] einzustellen sind.
-/
example (c s v₀ w₀ α₁ β₁ w : ℚ)
    (h₀ : v₀ ^ 2 = c * w₀ ^ 2 + s)
    (hline : w₀ * α₁ + β₁ = v₀) :
    c * w ^ 2 + s = (α₁ * w + β₁) ^ 2 +
      (w - w₀) * ((c - α₁ ^ 2) * w + (c - α₁ ^ 2) * w₀ - 2 * α₁ * β₁) := by
  rw [← hline] at h₀
  nlinarith [h₀]

end Kunerth1878b.AllgemeinerTeil
