/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf03

/-
Seite 344
§. 3.

Lässt sich für p eine rationale Zahl finden, die den Bruch in
VIa zu einer ganzen Zahl macht, so ist die Aufgabe gelöst; ob
dies aber nicht auch dann möglich wäre, wenn für p kein solcher
Werth existirt, muss zuvörderst untersucht werden. Denn vielleicht
lassen sich, wenn auch nicht mit m/n, so doch mit andern, die
Gleichung I befriedigenden Brüchen p-Functionen bilden, aus
denen ganze Zahlen für x gewonnen werden können. Darauf geben
folgende Betrachtungen die entscheidende Antwort.

Seite 345

Für x = m/n und y = r/n besteht nach III die Gleichung

mα + nβ = r ... (1)

und ebenso für ein anderes Paar von Werthen, etwa für x = m₁/n₁
und y = r₁/n₁ die Gleichung m₁α + n₁β = r₁ ... (2).

Alle aus (1) entwickelten Werthe von α und β geben solche
Formen von II, in denen der Wurzelfactor nx − m vorkommt,
wogegen die aus (2) gefundenen Werthe von α und β Formen liefern,
die den Wurzelfactor n₁x − m₁ enthalten. Lässt man jedoch (1)
und (2) als zusammengehörige Gleichungen gelten, und bestimmt
aus ihnen α und β, die in diesem Falle gemeiniglich Brüche sind,
so befriedigt das gefundene Zahlenpaar jede dieser zwei
Gleichungen,
-/

example (m n r m₁ n₁ r₁ : ℚ) (hd : m * n₁ - m₁ * n ≠ 0) :
    let α := (r * n₁ - r₁ * n) / (m * n₁ - m₁ * n)
    let β := (m * r₁ - m₁ * r) / (m * n₁ - m₁ * n)
    m * α + n * β = r ∧ m₁ * α + n₁ * β = r₁ := by
  dsimp
  have h := mul_inv_cancel₀ hd
  constructor
  · linear_combination r * h
  · linear_combination r₁ * h

/-
und es muss daher in der mit diesen Werthen gebildeten
Form II sowohl nx − m als auch n₁x − m₁ erscheinen.
-/

example (a b c α β x x₀ x₁ : ℚ) (hd : x₀ ≠ x₁)
    (h₀ : (α * x₀ + β) ^ 2 = a * x₀ ^ 2 + b * x₀ + c)
    (h₁ : (α * x₁ + β) ^ 2 = a * x₁ ^ 2 + b * x₁ + c) :
    (α * x + β) ^ 2 - (a * x ^ 2 + b * x + c) =
      (α ^ 2 - a) * (x - x₀) * (x - x₁) := by
  have hl : (x₀-x₁)*((α^2-a)*(x₀+x₁)+2*α*β-b)=0 := by
    linear_combination h₀-h₁
  have hl' := (mul_eq_zero.mp hl).resolve_left (sub_ne_zero.mpr hd)
  linear_combination h₀ + (x-x₀)*hl'

/-
Da nun das letztere Binom alle möglichen Wurzelfactoren vorstellt,
so kann in der Gleichung II mit dem speciellen Factor nx − m
dieser selbst und jeder andere der Gleichung I zukommende
Wurzelfactor in Verbindung treten. Der rechtsstehende Ausdruck in V
repräsentirt somit alle Wurzelfactoren der Gleichung I und der
Bruch in VI, wie überhaupt jede p-Function, alle möglichen
Werthe von x.

Die Gleichung I kann daher nur dann in ganzen Zahlen
gelöst werden, wenn für p solche Werthe bestehen, die den Bruch
in VIa in eine ganze Zahl verwandeln; wird aber nachgewiesen,
dass ein solcher Werthe für p nicht möglich ist, so ist auch die
gestellte Aufgabe unmöglich.
-/

example : Prop := ∀ (a b c m n α₁ β₁ : ℤ) (γ δ : ℚ), n ≠ 0 →
    0 < a →
    (¬ ∃ q : ℚ, q ^ 2 = a) →
    (α₁ : ℚ) ^ 2 - n * γ = a →
    2 * (α₁ : ℚ) * β₁ + m * γ + n * δ = b →
    (β₁ : ℚ) ^ 2 - m * δ = c →
    ∀ x y : ℚ, y ^ 2 = a * x ^ 2 + b * x + c →
      ∃ p : ℚ, n * p ^ 2 - 2 * α₁ * p + γ ≠ 0 ∧
        x = (m * p ^ 2 + 2 * β₁ * p + δ) / (n * p ^ 2 - 2 * α₁ * p + γ)

end Kunerth1880.Paragraf03
