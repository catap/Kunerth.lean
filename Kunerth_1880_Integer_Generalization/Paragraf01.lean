/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf01

/-
Seite 342
Berechnung der ganzzahligen Wurzeln unbestimmter
quadratischer Gleichungen mit zwei Unbekannten
aus den für letztere gefundenen Brüchen, nebst den
Kriterien der Unmöglichkeit einer solchen Lösung.

Von Prof. Adolf Kunerth.

(Vorgelegt in der Sitzung am 1. Juli 1880.)

§. 1.

Jeder vollständigen Gleichung dieser Art lässt sich durch
eine lineare Substitution für eine ihrer Unbekannten die Gestalt
y² = ax² + bx + c ... I ertheilen, wo die Coëfficienten ganze
Zahlen sind; dabei soll a positiv und ein Nichtquadrat sein.

In der Abhandlung: „Praktische Methode zur numerischen
Auflösung unbestimmter quadratischer Gleichungen in rationalen
Zahlen“, publicirt im LXXVIII. Bande der Sitzungsberichte der
k. A. d. W. II. Abth., Juli-Heft 1878, wurde ein Verfahren
angegeben, jede in rationalen Zahlen mögliche Gleichung von der
Form I auf die Form

y² = (αx + β)² ± (γx − δ)(εx − ζ)

zu bringen, in welcher die griechischen Buchstaben bestimmte
Rationalzahlen bedeuten. Aus dieser Gleichung ergeben sich für
x die zwei Werthe δ/γ und ζ/ε, welche im Allgemeinen echte Brüche
sind; und da entsteht die Frage, ob nicht aus einem dieser Brüche
die etwa bestehenden ganzzahligen Werthe von x gefunden
werden könnten?

Angenommen, es wäre ein Bruch m/n bekannt, welcher für x
in die Gleichung I gesetzt, derselben Genüge leistet, so kann die
rechte Seite derselben auf die Form

(αx + β)² − (γx − δ)(nx − m) = ax² + bx + c ... II

gebracht werden, sobald die mit griechischen Lettern bezeichneten

Seite 343

Zahlen bestimmt sind.
-/

example (α β γ δ m n x : ℚ) :
    (α * x + β) ^ 2 - (γ * x - δ) * (n * x - m) =
      (α ^ 2 - n * γ) * x ^ 2 + (2 * α * β + m * γ + n * δ) * x +
        (β ^ 2 - m * δ) := by
  ring

/-
Für

x = m/n wird y = α m/n + β = r/n, also mα + nβ = r ... III,
-/

example (α β m n : ℚ) (hn : n ≠ 0) :
    α * (m / n) + β = (m * α + n * β) / n := by
  field_simp

/-
und aus dieser unbestimmten Gleichung findet man

[α = −np + α₁, β = mp + β₁] ... IV;

hier stellen α₁ und β₁ bekannte ganze Zahlen vor, während p
jeden rationalen Werth erhalten kann. Es lässt sich daher diese
Transformation auf beliebig viele Arten ausführen, indem bei
jeder Änderung von p die Zahlen α, β, γ, δ andere werden. Für
ein specielles Paar von α und β findet man den Factor γx − δ aus
der Gleichung II durch einfache Rechnung.
-/

example (m n α₁ β₁ p : ℚ) :
    m * (-n * p + α₁) + n * (m * p + β₁) = m * α₁ + n * β₁ := by
  ring

end Kunerth1880.Paragraf01
