/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf17

/-
Seite 356
§. 17.

Kommen in D quadratische Factoren vor, deren Product wir
mit ν² bezeichnen, so dass D = ν²D₁ ist, so lässt sich meistens eine
p-Function finden, deren Nenner v² − aw² lediglich ein Theiler
von n₁νD₁ sein darf.

Um auf diese p-Function zu kommen, setze man in der
Gleichung K² = aΔ² + D(α² − a) ... (V im Eingangs erwähnten
Hefte ex 1878) α = ν, K = νk, Δ = νd und dividire, wenn a und ν²
keinen quadratischen Factor gemein haben, beiderseits durch ν²:
da wird

k² = ad² + D₁(ν² − a) ... (1)
-/

example (ν a D₁ k d : ℚ) :
    (ν * k) ^ 2 - (a * (ν * d) ^ 2 + ν ^ 2 * D₁ * (ν ^ 2 - a)) =
      ν ^ 2 * (k ^ 2 - (a * d ^ 2 + D₁ * (ν ^ 2 - a))) := by ring

/-
wo d und k die Unbekannten sind. Nach Bestimmung derselben

Seite 357

erhält man

β = ν(±k + b)/(2a) = νη oder (ν/2)η.

Ist η ein reducirter Bruch, so muss sein Nenner ein Theiler von a
und prim gegen ν sein; wären nämlich a und ν durch μ theilbar,
so müssten b wegen D = ν²D₁, und k wegen (1) es auch sein,
und in dem obigen Ausdrucke für β bliebe, beim Abkürzen durch μ
der Factor ν im Zähler intact. η kann auch Null sein.
-/

example (a b c ν D₁ k d ε : ℤ) (_hε : ε = 1 ∨ ε = -1)
    (ha : a ≠ 0) (_hν : 0 < ν) (hD : b ^ 2 - 4 * a * c = ν ^ 2 * D₁)
    (hk : k ^ 2 = a * d ^ 2 + D₁ * (ν ^ 2 - a))
    (hfree : ∀ q : ℤ, 1 < q → ¬ (q ^ 2 ∣ a ∧ q ^ 2 ∣ ν ^ 2)) :
    let η₁ : ℚ := ((ε * k : ℤ) + (b : ℚ)) / (2 * a)
    let η₂ : ℚ := ((ε * k : ℤ) + (b : ℚ)) / a
    ((η₁.den : ℤ) ∣ a ∧ Int.gcd (η₁.den : ℤ) ν = 1) ∨
      ((η₂.den : ℤ) ∣ a ∧ Int.gcd (η₂.den : ℤ) ν = 1) := by
  dsimp only
  let η : ℚ := ((ε * k : ℤ) + (b : ℚ)) / a
  have hη : η = Rat.divInt (ε * k + b) a := by
    rw [← Rat.intCast_div_eq_divInt]
    simp only [η, Int.cast_add]
  have hden : (η.den : ℤ) ∣ a := by
    rw [hη]
    exact Rat.den_dvd (ε * k + b) a
  refine Or.inr ⟨hden, ?_⟩
  change Int.gcd (η.den : ℤ) ν = 1
  by_contra hcommon
  obtain ⟨p, hp, hpcommon⟩ := Nat.exists_prime_and_dvd hcommon
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpgcd : (p : ℤ) ∣ (Int.gcd (η.den : ℤ) ν : ℤ) :=
    Int.natCast_dvd_natCast.mpr hpcommon
  have hpden : (p : ℤ) ∣ (η.den : ℤ) :=
    dvd_trans hpgcd (Int.gcd_dvd_left _ _)
  have hpν : (p : ℤ) ∣ ν := dvd_trans hpgcd (Int.gcd_dvd_right _ _)
  have hpa : (p : ℤ) ∣ a := dvd_trans hpden hden
  have hpν₂ : (p : ℤ) ∣ ν ^ 2 := dvd_pow hpν (by decide)
  have hpb : (p : ℤ) ∣ b := by
    apply hp'.dvd_of_dvd_pow (n := 2)
    rw [show b ^ 2 = ν ^ 2 * D₁ + 4 * (a * c) by nlinarith [hD]]
    exact dvd_add (dvd_mul_of_dvd_left hpν₂ D₁)
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hpa c) 4)
  have hpk : (p : ℤ) ∣ k := by
    apply hp'.dvd_of_dvd_pow (n := 2)
    rw [hk]
    exact dvd_add (dvd_mul_of_dvd_left hpa (d ^ 2))
      (dvd_mul_of_dvd_right (dvd_sub hpν₂ hpa) D₁)
  have hpnumerator : (p : ℤ) ∣ ε * k + b :=
    dvd_add (dvd_mul_of_dvd_right hpk ε) hpb
  have heq : (ε * k + b) * (η.den : ℤ) = η.num * a := by
    apply (Rat.divInt_eq_divInt_iff ha (by exact_mod_cast η.den_ne_zero)).mp
    rw [← hη, ← Rat.intCast_div_eq_divInt]
    simpa only [Int.cast_natCast] using (Rat.num_div_den η).symm
  have hreduced : IsCoprime (η.den : ℤ) η.num := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa using η.reduced.symm
  have hpcoprime : IsCoprime (p : ℤ) η.num :=
    hreduced.of_isCoprime_of_dvd_left hpden
  have hpsquare : (p : ℤ) ^ 2 ∣ a := by
    apply hpcoprime.pow_left.dvd_of_dvd_mul_left
    rw [← heq]
    simpa [pow_two] using mul_dvd_mul hpnumerator hpden
  apply hfree p (by exact_mod_cast hp.one_lt)
  exact ⟨hpsquare, by simpa only [pow_two] using mul_dvd_mul hpν hpν⟩

/-
Es wird also

y² = (νx + νη)² + (γx − δ)(n₁x − m₁) ... (2),
x = m₁/n₁, y = νr₁/n₁

und

n₁x = m₁ + (2νr₁p₁ + l)/(p₁² − a);

weil hier S = n₁²ν²D₁ ist, so muss l = νl₁ sein, somit

n₁x = m₁ + ν(2r₁p₁ + l₁)/(p₁² − a).
-/

example (ν r₁ l₁ m₁ a p : ℚ) (_hp : p ^ 2 - a ≠ 0) :
    m₁ + (2 * ν * r₁ * p + ν * l₁) / (p ^ 2 - a) =
      m₁ + ν * ((2 * r₁ * p + l₁) / (p ^ 2 - a)) := by ring

/-
Hier ist die reducirte Stz. S₁ = n₁²νD₁ und, wie sogleich bewiesen
wird, ν prim gegen n₁, daher nach §. 8 n₁νD₁ ein Vielfaches
aller brauchbaren Werthe von v² − aw².

Die Zahlen ν und n₁ können desshalb als theilfremd angesehen
werden, weil sonst ihr gemeinschaftliches Mass μ wegen der
Determinante ν²D₁ des auf die Form I gebrachten rechten Flügels
in (2) auch ein Mass von m₁ sein müsste und daselbst im Binome
n₁x − m₁ herausgehoben werden könnte.

Wäre aber a = π²a₁ und λ das grösste gemeinschaftliche Mass
von π und ν, so ist α = πν/λ zu setzen und die obige Gleichung V
durch (πν)² zu kürzen; in der transformirten Gleichung II wird ein
Werth von x ein Bruch sein, dessen Nenner durch π oder π/2
theilbar ist, und die aus diesem Bruche gebildete p-Function wird
im Zähler den gemeinschaftlichen Factor ν haben und durch π²
oder (π/2)² gekürzt werden können.
-/

example (π ν «λ» a₁ D₁ k d : ℚ) (hπ : π ≠ 0) (hν : ν ≠ 0)
    (hlam : «λ» ≠ 0) :
    ((π * ν * k) ^ 2 -
        (π ^ 2 * a₁ * (π * ν * d) ^ 2 +
          ν ^ 2 * D₁ * ((π * ν / «λ») ^ 2 - π ^ 2 * a₁))) /
        (π * ν) ^ 2 =
      k ^ 2 - (π ^ 2 * a₁ * d ^ 2 + D₁ * ((ν / «λ») ^ 2 - a₁)) := by
  field_simp

example (π ν «λ» a₁ b k ε : ℚ) (hπ : π ≠ 0) (hlam : «λ» ≠ 0)
    (ha₁ : a₁ ≠ 0) (_hε : ε = 1 ∨ ε = -1) :
    (ε * π * ν * k + (π * ν / «λ») * b) / (2 * (π ^ 2 * a₁)) =
      ν * (ε * «λ» * k + b) / (2 * π * «λ» * a₁) := by
  field_simp

example (a a₁ b m n r π d₀ f : ℚ) (q : ℚ) (hπ : π ≠ 0)
    (ha : a = π ^ 2 * a₁) (hr : 2 * r = π * d₀)
    (hg : 2 * a * m + b * n = π ^ 2 * f) (_hq : q ^ 2 - a₁ ≠ 0) :
    m + (2 * r * (π * q) + (2 * a * m + b * n)) / ((π * q) ^ 2 - a) =
      m + (d₀ * q + f) / (q ^ 2 - a₁) := by
  rw [hg, ha, hr]
  have hnum : π * d₀ * (π * q) + π ^ 2 * f = π ^ 2 * (d₀ * q + f) := by ring
  have hden : (π * q) ^ 2 - π ^ 2 * a₁ = π ^ 2 * (q ^ 2 - a₁) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 2 hπ)]

example (a a₁ b m n r π μ d₀ f : ℚ) (q : ℚ) (hμ : μ ≠ 0)
    (hπ : 2 * μ = π) (ha : a = π ^ 2 * a₁) (hr : 2 * r = μ * d₀)
    (hg : 2 * a * m + b * n = μ ^ 2 * f) (_hq : q ^ 2 - 4 * a₁ ≠ 0) :
    m + (2 * r * (μ * q) + (2 * a * m + b * n)) / ((μ * q) ^ 2 - a) =
      m + (d₀ * q + f) / (q ^ 2 - 4 * a₁) := by
  rw [hg, ha, ← hπ, hr]
  have hnum : μ * d₀ * (μ * q) + μ ^ 2 * f = μ ^ 2 * (d₀ * q + f) := by ring
  have hden : (μ * q) ^ 2 - (2 * μ) ^ 2 * a₁ = μ ^ 2 * (q ^ 2 - 4 * a₁) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 2 hμ)]

/-
Diese Transformationen können das Auffinden eines
Kennzeichens für die Unmöglichkeit der Lösung in ganzen Zahlen

Seite 358

erleichtern, weil dadurch die Menge der Factoren von S in der
reducirten Stammzahl S₁ vermindert wird. ¹

¹ Die bisherigen Sätze haben auch dann Geltung, wenn a negativ
oder ein Quadrat ist.
-/

/-
Die folgende Formalisierung wendet die Fussnote auf die Behauptung
über VIa aus §. 3 für die genannten Werthe von a an. Ob der Fall D = 0
stillschweigend ausgenommen war, entscheidet die Fussnote nicht; eine
solche Voraussetzung wird hier nicht hinzugefügt.
-/

example : Prop := ∀ (a b c m n α₁ β₁ : ℤ) (γ δ : ℚ), n ≠ 0 →
    (a < 0 ∨ ∃ q : ℤ, q ^ 2 = a) →
    (α₁ : ℚ) ^ 2 - n * γ = a →
    2 * (α₁ : ℚ) * β₁ + m * γ + n * δ = b →
    (β₁ : ℚ) ^ 2 - m * δ = c →
    ∀ x y : ℚ, y ^ 2 = a * x ^ 2 + b * x + c →
      ∃ p : ℚ, n * p ^ 2 - 2 * α₁ * p + γ ≠ 0 ∧
        x = (m * p ^ 2 + 2 * β₁ * p + δ) / (n * p ^ 2 - 2 * α₁ * p + γ)

end Kunerth1880.Paragraf17
