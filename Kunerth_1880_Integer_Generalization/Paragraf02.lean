/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf02

/-
Seite 343
§. 2.

Setzt man aus IV die allgemeinen Ausdrücke für α und β
in die Gleichung II und verbindet die Glieder des entwickelten
Quadrates mit den gleichartigen Gliedern des transponirten
rechten Flügels, so wird

(γx − δ)(nx − m) = [n²p² − 2nα₁p + α₁² − a]x² −
[2mnp² − 2(mα₁ − nβ₁)p − (2α₁β₁ − b)]x +
[m²p² + 2mβ₁p + β₁² − c]

Aus II folgt:
α₁² − nγ = a, 2α₁β₁ + mγ + nδ = b, β₁² − mδ = c;
somit
α₁² − a = nγ, 2α₁β₁ − b = −mγ − nδ, β₁² − c = mδ;

nach Einsetzen dieser Werthe in die letzte Gleichung erhält man:

(γx − δ)(nx − m) = [n²p² − 2nα₁p + nγ]x² −
[2mnp² − 2(mα₁ − nβ₁)p + (mγ + nδ)]x +
[m²p² + 2mβ₁p + mδ],

und durch Division beider Seiten mit nx − m:

γx − δ = (np² − 2α₁p + γ)x − (mp² + 2β₁p + δ) ... V.
-/

example (n m α₁ β₁ γ δ p x : ℚ) :
    ((-n * p + α₁) * x + (m * p + β₁)) ^ 2 -
      ((α₁ ^ 2 - n * γ) * x ^ 2 +
        (2 * α₁ * β₁ + m * γ + n * δ) * x + β₁ ^ 2 - m * δ) =
    ((n * p ^ 2 - 2 * α₁ * p + γ) * x -
      (m * p ^ 2 + 2 * β₁ * p + δ)) * (n * x - m) := by
  ring

/-
Der rechte Flügel dieser Gleichung ist der allgemeine
Ausdruck für den Wurzelfactor γx − δ, der für jeden neuen Werth von
p ein anderer wird. Für p = 0 wird x = δ/γ; allgemein aber ist

Seite 344

x = (mp² + 2β₁p + δ)/(np² − 2α₁p + γ) ... VIa,

die Gleichung der p-Function für m/n.

Diese Formel kann zufolge der Entstehung ihrer Bruchglieder
concis auch so dargestellt werden:

x = [(β² − c) : m]/[(α² − a) : n] ... VIb,

wo für α und β die in IV stehenden Binome zu nehmen sind. Ist
m/n negativ, so hat man den Brüchen in VIa und VIb das Zeichen −
vorzusetzen, dann ist in IV: α = −np + α₁ und β = −mp + β₁.
-/

example (m n α₁ β₁ p : ℚ) :
    (-m) * (-n * p + α₁) + n * (-m * p + β₁) = -m * α₁ + n * β₁ := by ring

/-
Setzen wir in VIa 1/P für p, so wird

x = (δP² + 2β₁P + m)/(γP² − 2α₁P + n),

die Gleichung der p-Function für δ/γ.
-/

example (m n α₁ β₁ γ δ P : ℚ) (hP : P ≠ 0)
    (_h : γ * P ^ 2 - 2 * α₁ * P + n ≠ 0) :
    (m * (1 / P) ^ 2 + 2 * β₁ * (1 / P) + δ) /
      (n * (1 / P) ^ 2 - 2 * α₁ * (1 / P) + γ) =
    (δ * P ^ 2 + 2 * β₁ * P + m) / (γ * P ^ 2 - 2 * α₁ * P + n) := by
  field_simp
  ring

/-
Ertheilt man der Variablen P einen besonderen Werth, für welchen
x = M/N wird, so sind die zugehörigen Grössen:

α = −n/P + α₁, β = m/P + β₁ und y = (M/N)α + β.

Oft ermöglicht der neue Nenner N eine rasche Lösung der
Gleichung I.
-/

end Kunerth1880.Paragraf02
