/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf23

/-
Seite 367
§. 23.
III. Berechnung gebrochener Zahlen für p₁ mittelst Gleichungen.

Führt auch der Kettenbruch nicht zum Ziele, was bei
Anwendung der bisher gebotenen Mittel (darunter §. 21)
gemeiniglich nur dann eintritt, wenn a − 1 ein Quadrat, oder wenn die
Lösung der Gleichung I in ganzen Zahlen unmöglich ist, so muss
man zur Aufstellung von Gleichungen schreiten, welche die Form
v² = aw² + N ... (1) haben und in ganzen, theilfremden Zahlen
auflöslich sein sollen. Wäre a = μ²a₁ und der Bruch in VIII
durch μ² gehoben worden, so sind Gleichungen von der Form
v² = a₁w² + N¹ zu construiren.

Für N und N¹ dürfen versuchsweise nur jene Factoren von S
respective S,, in steigender Ordnung gesetzt werden, welche nach
den in §. 18 angegebenen Regeln gebildet sind. Auch darf für N
keine unter √a liegende Zahl genommen werden, welche unter
den Nenner der vollständigen Quotienten (VI. Verticalreihe, §. 19)
fehlt, weil sonst (1) in relativen Primzahlen unmöglich wäre.
Dasselbe gilt für N¹ bezüglich √a₁.
-/

example : Prop :=
  ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
    (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
    (_hM : M 0 = 0) (_hQ : Q 0 = 1)
    (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
      (Real.sqrt a + M k) / Q k < A k + 1)
    (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
    (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
    (_hN : (|N| : ℤ) < Real.sqrt a)
    (_habsent : ∀ k, Q (k + 1) ≠ |N|),
    ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N

/-
Jede in dieser Rechnung vorkommende unbestimmte
Gleichung des zweiten Grades ist hinsichtlich ihrer Möglichkeit in

Seite 368

ganzen Zahlen der Probe auf die quadratischen Achterreste ihrer
Seiten zu unterziehen, und bei Gleichungen von der Form I ist
im vorhinein zu untersuchen, ob das Zahlenglied ein quadratischer
Rest des grössten gemeinschaftlichen Masses der zwei andern
Coëfficienten ist.
-/

example (a b c x y : ℤ) (h : y ^ 2 = a * x ^ 2 + b * x + c) :
    ∃ t : ℤ, (Int.gcd a b : ℤ) ∣ t ^ 2 - c := by
  refine ⟨y, ?_⟩
  rw [show y ^ 2 - c = a * x ^ 2 + b * x by linarith [h]]
  exact dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left a b) (x ^ 2))
    (dvd_mul_of_dvd_left (Int.gcd_dvd_right a b) x)

/-
Ist in I b von Null verschieden und v² = aw² + N ... (1) in
relativen Primzahlen möglich, so muss v² = aw² + S/N es auch sein
(§. 14); ist aber b = 0 und (1) möglich, so müssen noch drei
ähnliche Gleichungen in relativen Primzahlen auflöslich sein, weil
sonst (1) unbrauchbar wäre (§. 16).

Die Auflösung der Gleichung (1) kann im Möglichkeitsfalle
auf zweierlei Art erfolgen.

1. Für v = az + r wird

w² = az² + 2rz + (r² − N)/a;
-/

example (a z r N : ℚ) (ha : a ≠ 0) :
    ((a * z + r) ^ 2 - N) / a = a * z ^ 2 + 2 * r * z + (r ^ 2 - N) / a := by
  field_simp
  ring

/-
von den 2μ incongruenten Wurzeln der Congruenz r² ≡ N (mod a)
setze man die ersten μ Wurzeln für r in die letzte Gleichung ein,
wodurch ein System von μ unbestimmten quadratischen
Gleichungen entsteht. Für jede der letzteren finde man mittelst der
Achterreste, welche von den Formen 8n ± (1, 3, 2, 4, 0) die
Unbekannte z haben kann, und ermittle hierauf durch Versuche
eine solche Zahl für z, welche einer dieser Gleichungen Genüge
leistet. Dabei versuche man für z nur solche Zahlen, von denen
das bekannte Glied ein quadratischer Rest ist, und meide
Substitutionen, bei denen eine Primzahl in zwei Gliedern potenzirt
im dritten aber singulär vorkäme.

2. Man berechne aus der unbestimmten Gleichung

Δ² = aβ² + N(α² − a) ... IV₁ ex 1878

für einen beliebigen Werth von α jenen von β mittelst des Satzes
Δ = az + r auf die eben angegebene Weise, bringe hierauf die
Gleichung (1) auf die Form II, und benütze, falls es noch nöthig
wäre, eine p-Function.

Ist die Gleichung I, in der b auch Null sein kann, in ganzen
Zahlen möglich, so entsprechen jedem ganzzahligen α unzählige
ebenso beschaffene β (wegen III), und ist a − α² eine Primzahl
und ein ganzzahliges β gefunden, so liefert die Form II für x

Seite 369

wenigstens Eine ganze Zahl.
-/

/-
Ein entarteter Fall mit D = 0 wird in der obigen Aussage nicht
ausdrücklich ausgeschlossen.
-/

example : Prop :=
  ∀ (a b c α : ℤ), 0 < a → (¬ ∃ q : ℤ, q ^ 2 = a) →
    (∃ x y : ℤ, y ^ 2 = a * x ^ 2 + b * x + c) →
    Set.Infinite {β : ℤ | ∃ x y : ℤ,
      y ^ 2 = a * x ^ 2 + b * x + c ∧ α * x + β = y}

/-
Um aber für β eine ganze Zahl zu finden, ist es rathsam, die
Gleichung

K² = aΔ² + D(α² − a) ... V ex 1878

beziehungsweise die obige unter IV₁ nicht auf Grund willkürlicher
Annahmen mittelst Division ihrer Glieder durch Quadrate
abzukürzen. Würde trotzdem eine dieser zwei Gleichungen in
ganzen Zahlen unmöglich, so ist auch I unauflöslich.
-/

example (a b c α : ℤ)
    (hno : ¬ ∃ K Δ : ℤ, K ^ 2 = a * Δ ^ 2 + (b ^ 2 - 4 * a * c) * (α ^ 2 - a)) :
    ¬ ∃ x y : ℤ, y ^ 2 = a * x ^ 2 + b * x + c := by
  rintro ⟨x, y, h⟩
  let β := y - α * x
  have hIII : y = α * x + β := by dsimp [β]; ring
  have hquadratic : (a - α ^ 2) * x ^ 2 + (b - 2 * α * β) * x +
      c - β ^ 2 = 0 := by
    rw [hIII] at h
    linear_combination -h
  let Δ := 2 * (a - α ^ 2) * x + b - 2 * α * β
  have hIV : Δ ^ 2 =
      4 * (a * β ^ 2 - b * α * β + c * α ^ 2) + b ^ 2 - 4 * a * c := by
    dsimp [Δ]
    linear_combination 4 * (a - α ^ 2) * hquadratic
  apply hno
  refine ⟨2 * a * β - b * α, Δ, ?_⟩
  linear_combination -a * hIV

example (a N α : ℤ)
    (hno : ¬ ∃ Δ β : ℤ, Δ ^ 2 = a * β ^ 2 + N * (α ^ 2 - a)) :
    ¬ ∃ v w : ℤ, v ^ 2 = a * w ^ 2 + N := by
  rintro ⟨v, w, h⟩
  let β := v - α * w
  have hIII : v = α * w + β := by dsimp [β]; ring
  have hquadratic : (a - α ^ 2) * w ^ 2 - 2 * α * β * w + N - β ^ 2 = 0 := by
    rw [hIII] at h
    linear_combination -h
  apply hno
  refine ⟨(a - α ^ 2) * w - α * β, β, ?_⟩
  linear_combination (a - α ^ 2) * hquadratic

/-
Dieser Vorgang wird mühsam und abschreckend, wenn der Werth von z
weitab vom Ausgangspunkte der Versuche liegt, daher man
letztere nicht ausdehne, sondern lieber mit Verzicht auf die Primzahl
für α eine andere, etwa solche Zahl setze, für welche α² − a eine
der ersten in der VI. Verticalreihe stehenden Zahlen oder ein
Multiplum einer solchen wird (§. 19).

Lässt sich ein Werth von β nicht leicht finden, so bediene
man sich, wenn b nicht Null und c nicht gross ist, der Gleichung

L² = cΔ² + D(β² − c) ... VI ex 1878

und setze hier für β nur Theiler von c. Hat man L bestimmt,
so wird α nach der Formel

α = (±L + bβ)/(2c)

berechnet.
-/

example (a b c α β : ℚ) :
    (2 * c * α - b * β) ^ 2 - (b ^ 2 - 4 * a * c) * (β ^ 2 - c) =
      c * ((2 * α * β - b) ^ 2 - 4 * (α ^ 2 - a) * (β ^ 2 - c)) := by ring

/-
Ist b = 0, so hat man die einfachere Formel

Δ² = cα² + a(β² − c) ... IV,, ex 1878

zu benützen und für β Divisoren von c zu nehmen.
-/

example (a c α β : ℚ) :
    a * β ^ 2 + c * (α ^ 2 - a) = c * α ^ 2 + a * (β ^ 2 - c) := by ring

/-
Endlich kann man versuchen, die Gleichungen V respective
IV₁ ex 1878 auf die im letzten Absatze des §. 16 angegebene
Weise in Rationalzahlen zu lösen.

Von den die Gleichung (1) befriedigenden Zahlen probire
man nicht nur Ein Paar in der Formel VIII oder X, sondern man
versuche einige innerhalb der ersten Periode liegenden Werthe
von w und v, ehe man weiter geht.

Die hier angegebenen Methoden führen überraschend schnell
zur Auflösung der Gleichungen oder zu einem Kennzeichen der
Unmöglichkeit einer Lösung in ganzen Zahlen.
-/

end Kunerth1880.Paragraf23
