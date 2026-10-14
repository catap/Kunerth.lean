/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf04

/-
Seite 21

§. 4.

1. Die in §. 1. 7. hinsichtlich des Factors a erörterte Eigenschaft des
Bruches in III bietet ein Mittel die Rechnung auf den Fall w = 1 zu
beschränken, wo q eine ganze Zahl ist.
Liefert die Stammzahl S keinen brauchbaren Werth für q und ist α der
grösste Factor von a, der im Nenner von III — und somit auch in S —
als Factor vorzukommen hat, so setze man mit Berücksichtigung der
quadratischen Reste den Nenner v²−gw² = ∓α eventuell = ∓2α und = ∓4α,
wofern S durch letztere zwei Zahlen theilbar ist. Wäre keine dieser
sechs Gleichungen möglich, so sind der Stammzahl in natürlicher Ordnung
Vielfache von α zu entnehmen und an die Stelle von α in jene sechs
Gleichungen zu setzen. Wäre αβ ein solches Vielfache, so dürfen 2αβ und
4αβ nur dann verwendet werden, wenn sie Theiler von S sind.
Für α = 1 sind die aufeinander folgenden Factoren von S als Zahlenglieder
jener sechs Gleichungen zu benützen.
Hat man auf diese Weise eine in ganzen Zahlen mögliche Gleichung
gefunden — sie heisse die erste derivirte Gleichung — so bestimme man
für dieselbe die p-Function und suche

Seite 22

aus dieser einen ganzzahligen Werth für w, dem ein ebenso beschaffener
für v entsprechen wird. Sollte sich aber auch aus der neuen Stammzahl
kein solcher Werth für w ergeben, so bilde man sich auf eine der oberen
ähnliche Art die zweite derivirte Gleichung v₁²−gw₁² = ∓α₁, ... und
setze dieses Verfahren so lange fort, bis man auf ein ganzzahliges wᵣ
und vᵣ kommt; durch Einsetzen dieser Zahlen in die p-Function der
vorhergehenden Derivirten findet man wᵣ₋₁ und vᵣ₋₁ und durch weitere
recurrente Substitutionen schliesslich ein ganzzahliges x₁.

2. Kann ein quadratischer Factor von S in eine derivirte Gleichung als
Zahlenglied eintreten, so wird dadurch die Auffindung der zugehörigen
p-Function erleichtert.

3. Käme man auf eine derivirte Gleichung, welche mit einer bereits
vorkommenden Gleichung identisch ist, so muss statt jener Derivirten
eine andere gesucht werden.

4. Ist man bei einer höheren, etwa der dritten Derivirten angelangt,
so sind behufs der unmittelbaren Auffindung von w₃ mindestens aus der
Gruppe (±α, ∓2α, ∓4α) alle zulässigen Gleichungen zu benützen und erst,
wenn keine derselben ein ganzzahliges w₃ liefert, ist von jeder der
zuletzt behandelten p-Functionen auf die nächste derivirte Gleichung
überzugehen, weil sich sonst in manchen Fällen (namentlich wenn g eine
grosse Zahl ist) die Rechnung in die Länge zieht, und man entweder für
x nicht den kleinsten Werth findet oder eines der w nicht ganzzahlig
ausfällt ¹.

5. Auch kann es vorkommen, dass sich für die gegebene Gleichung oder
für eine der Derivirten die p-Function nicht finden lässt. Wäre
y² = gx²+k eine solche Gleichung, so setze man y = gz+r; dann ist

x² = gz²+2rz+(r²−k)/g;
-/

example (g k z r : ℚ) (hg : g ≠ 0) :
    ((g * z + r) ^ 2 - k) / g =
      g * z ^ 2 + 2 * r * z + (r ^ 2 - k) / g := by
  field_simp
  ring

/-
wäre k > g, also k = gl+m, so ist

x² = gz²+2rz−l+(r²−m)/g ... (λ.);

¹ Für p-Functionen welche von Gleichungen abgeleitet sind, die keine
ganzzahligen Wurzeln besitzen, können auch die derivirten Gleichungen
nicht in ganzen Zahlen gelöst werden.
-/

example (g l m z r : ℚ) (hg : g ≠ 0) :
    g * z ^ 2 + 2 * r * z + (r ^ 2 - (g * l + m)) / g =
      g * z ^ 2 + 2 * r * z - l + (r ^ 2 - m) / g := by
  field_simp
  ring

/-
Seite 23

da dieser Bruch in eine ganze Zahl n übergehen muss, so suche man aus
der Gleichung r² = gn+m alle ganzzahligen Werthe für r, die kleiner als
g sind, d. h. man bestimme aus der Congruenz r² ≡ m (mod. g) sämmtliche
Wurzeln der ersten Periode und setze von diesen alle, die kleiner als
g/2 sind für r in die Gleichung (λ); dies gibt eine Reihe von
Gleichungen, von denen, wenn für x ein ganzzahliger Werth existirt,
wenigstens eine für z eine ganze Zahl liefert.
-/

example (g m n r : ℤ) (h : r ^ 2 = g * n + m) :
    Int.ModEq g (r ^ 2) m := by
  apply Int.modEq_iff_dvd.mpr
  exact ⟨-n, by nlinarith [h]⟩

/-
Wird für einen Werth von r das Binom n−l eine Quadratzahl e², so ist
für z = 0, x = e und y = r. Offenbar lassen sich aus diesen
Gleichungen, in denen z positiv und negativ zu nehmen ist, alle Werthe
von x finden, wenn die Anzahl derselben eine begrenzte ist, was für
ein negatives g eintritt.
-/

example (g l m n r e : ℤ) (hr : r ^ 2 = g * n + m)
    (he : e ^ 2 = n - l) :
    r ^ 2 = g * e ^ 2 + (g * l + m) := by rw [he]; nlinarith [hr]

/-
Ist g eine Primzahl, so erhält man für r zwei Werthe, und somit nur
eine Gleichung mit der Variablen z.
-/

example (g : ℕ) [Fact g.Prime] (m r s : ZMod g)
    (hr : r ^ 2 = m) :
    s ^ 2 = m ↔ s = r ∨ s = -r := by
  rw [← hr, sq_eq_sq_iff_eq_or_eq_neg]

example (g r z : ℚ) :
    g * (-z) ^ 2 + 2 * (-r) * (-z) = g * z ^ 2 + 2 * r * z := by ring

/-
Hat z einen grösseren Zahlenwerth, so suche man für z die p-Function
und aus derselben ein ganzzahliges z.
Die Gleichung (λ) nennen wir die der z-Function.
-/

end Kunerth1877.Paragraf04
