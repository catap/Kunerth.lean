/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Kunerth_1880_Integer_Generalization.Paragraf13

namespace Kunerth1880.Paragraf14

/-
Seite 354
§. 14.

Enthält D einen Primfactor blos in der ersten Potenz, so
kann derselbe nur in Einem Nenner vorkommen (XIIa), und da zur
Berechnung von x der diesem äquivalente Nenner genügt, so darf
ein singulärer Factor in D gelöscht werden, wodurch sich die
Zahl der zur Ergründung von N nöthigen Versuche auf die Hälfte
reducirt.
-/

/-
Zur Reichweite der Übersetzung: Die folgende Proposition deutet
„Nenner“ als die unveränderten N₁ und N₂ in XIIa, nicht als N₁/n
und N₂/n. Ihre Voraussetzungen schliessen q ∣ n nicht aus; dann
kann der Factor n beide Nenner durch q theilbar machen. Ob die
gedruckte Behauptung gekürzte Nenner oder eine weitere Einschränkung
betrifft, bleibt ungeklärt. Weder eine Kürzung durch n noch die
Zusatzvoraussetzung q ∤ n wird hier in den Wortlaut hineingelesen.
Die Proposition hält diese vorläufige Deutung ohne Beweis fest.
-/

def singularPrimeNotBoth : Prop :=
  ∀ (D n N₁ N₂ ρ q : ℤ) (_hn : n ≠ 0)
    (_hN₁ : n ∣ N₁) (_hN₂ : n ∣ N₂) (_hρn : Int.gcd ρ n = 1)
    (_hq : Prime q) (_hqD : q ∣ D) (_hqD₂ : ¬ q ^ 2 ∣ D) (_hXII : N₁ * N₂ * ρ ^ 2 = n ^ 2 * D),
    ¬ (q ∣ N₁ ∧ q ∣ N₂)

/-
Wäre v² − aw² = NⅠ in ganzen Zahlen möglich, nicht aber
v² − aw² = NⅡ, so wäre die erste Gleichung zur Bestimmung von
x unbrauchbar, und wenn sich zwei solche in ganzen und
theilfremden Zahlen auflösliche Gleichungen nicht bilden lassen,
so ist auch I in ganzen Zahlen unmöglich; doch ist dieser Satz
positiv aufgestellt, nicht allgemein giltig.
-/

/- Hilfsschritt: Anwendung von XIIa auf die äquivalenten Nenner. -/

example (a b c m n r x : ℤ) (p : ℚ) (_hn : 0 < n)
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
  exact Kunerth1880.Paragraf13.pairedNorms a b c m n r x p _hn hmn hroot hp hg hX

/-
Wurde der Bruch in VIII durch μ² gehoben, so hat man
in XIIa S/μ⁴ für S zu setzen.

Wenn die Determinante in I ein Quadrat ist, so lassen sich
durch unmittelbare Zerlegung des dortigen Trinoms zwei Werthe
von x finden und für jeden derselben hat p₁ nur Einen Werth.
-/

example (a b c t : ℚ) (ha : a ≠ 0) (hD : b ^ 2 - 4 * a * c = t ^ 2) :
    a * ((-b + t) / (2*a)) ^ 2 + b * ((-b+t)/(2*a)) + c = 0 ∧
    a * ((-b - t) / (2*a)) ^ 2 + b * ((-b-t)/(2*a)) + c = 0 := by
  constructor <;> field_simp <;> linear_combination -hD

example (a r g s : ℚ) (hs : s ≠ 0)
    (hz : a * s ^ 2 + g * s + r ^ 2 = 0)
    (hN : (r/s)^2-a ≠0) :
    ∃! p : ℚ, p^2-a ≠0 ∧ s = (2*r*p+g)/(p^2-a) := by
  refine ⟨r/s, ⟨hN, ?_⟩, ?_⟩
  · apply (eq_div_iff hN).2
    field_simp [hs]
    linear_combination -hz
  · intro p ⟨hp, he⟩
    have he' := (eq_div_iff hp).1 he
    have hz' : (s*p-r)^2 = 0 := by
      linear_combination s*he' + hz
    have he'' : s*p-r=0 := sq_eq_zero_iff.mp hz'
    apply (eq_div_iff hs).2
    linarith

example (a b c m n r x : ℚ)
    (hr : r^2=a*m^2+b*m*n+c*n^2) (hx : a*x^2+b*x+c=0) :
    a*(n*x-m)^2+(2*a*m+b*n)*(n*x-m)+r^2=0 := by
  linear_combination hr+n^2*hx

end Kunerth1880.Paragraf14
