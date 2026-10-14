/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1878a.AllgemeinerTeil

/-
Seite 327.

Praktische Methode zur numerischen Auflösung unbestimmter quadratischer
Gleichungen in rationalen Zahlen.
Von Prof. Adolf Kunerth.

Setzt man in der vollständigen Gleichung Ax² + Bxz + Cz² + Dx + Ez + F =
0 die Unbestimmte z = (y − (Bx + E))/(2C), so nimmt sie nach vollzogener
Reduction die Form

y² = ax² + bx + c (I)
-/
example (A B C D E F x y : ℚ) (hC : C ≠ 0) :
    4 * C * (A * x ^ 2 + B * x * ((y - (B * x + E)) / (2 * C)) +
      C * ((y - (B * x + E)) / (2 * C)) ^ 2 + D * x +
      E * ((y - (B * x + E)) / (2 * C)) + F) =
    y ^ 2 - ((B ^ 2 - 4 * A * C) * x ^ 2 +
      (2 * B * E - 4 * C * D) * x + E ^ 2 - 4 * C * F) := by
  field_simp
  ring

/-
an, und geht für x = (u − b)/(2a) in die Gleichung u² = 4ay² + b² − 4ac
über, an welcher sich die Möglichkeit ihrer Auflösung in Rationalzahlen
auf die bekannte Weise untersuchen lässt.
-/
example (a b c u y : ℚ) (ha : a ≠ 0) :
    4 * a * (a * ((u - b) / (2 * a)) ^ 2 +
      b * ((u - b) / (2 * a)) + c - y ^ 2) =
    u ^ 2 - (4 * a * y ^ 2 + b ^ 2 - 4 * a * c) := by
  field_simp
  ring

/-
Ist eine solche Lösung möglich, so kann der rechte Flügel der Gleichung
I auf beliebig viele Arten in einen Ausdruck von nachstehender Form
verwandelt werden:

y² = ax² + bx + c = (αx + β)² + (γx + δ)(εx + ζ) (II)

und jede solche Transformation liefert zwei Werthe für x, aus denen sich
andere finden lassen. Die griechischen Buchstaben bezeichnen ganze oder
gebrochene Zahlen.
-/
example (a b c : ℤ) (h : ∃ x y : ℚ, y ^ 2 = a * x ^ 2 + b * x + c) :
    Set.Infinite {p : ℚ × ℚ × ℚ × ℚ × ℚ × ℚ | ∀ x : ℚ,
      a * x ^ 2 + b * x + c = (p.1 * x + p.2.1) ^ 2 +
        (p.2.2.1 * x + p.2.2.2.1) * (p.2.2.2.2.1 * x + p.2.2.2.2.2)} := by
  obtain ⟨x₀, y₀, h₀⟩ := h
  let f : ℚ → ℚ × ℚ × ℚ × ℚ × ℚ × ℚ := fun α =>
    (α, y₀ - α * x₀, 1, -x₀, a - α ^ 2,
      b - 2 * α * (y₀ - α * x₀) + (a - α ^ 2) * x₀)
  have hinj : Function.Injective f := by
    intro α β hαβ
    exact congrArg Prod.fst hαβ
  apply (Set.infinite_range_of_injective hinj).mono
  rintro p ⟨α, rfl⟩ x
  dsimp [f]
  linear_combination -h₀

/-
Sind x = m/n und y = r/n zwei bekannte, die Gleichung I befriedigende
Werthe, so gestaltet sich diese für γ = n und δ = −m nach Einsetzen
jener Brüche also:

r²/n² = (α·m/n + β)² oder r = mα + nβ (III)
-/
example (α β m n r : ℚ) (hn : n ≠ 0) (h : r = m * α + n * β) :
    r ^ 2 / n ^ 2 = (α * (m / n) + β) ^ 2 := by
  rw [h]
  field_simp

example (α β ε ζ m n : ℚ) (hn : n ≠ 0) :
    (α * (m / n) + β) ^ 2 + (n * (m / n) - m) * (ε * (m / n) + ζ) =
    (α * (m / n) + β) ^ 2 := by
  field_simp
  ring

/-
und aus dieser unbestimmten Gleichung können die Unbekannten α und β und
hierauf aus II ε und ζ bestimmt werden. Zu jedem rationalen α gehört ein
eben solches β und umgekehrt; weil aber für m, n und r unzählig viele
Gruppen von Zahlen existiren, so entsprechen, wenn man letztere drei
Grössen unbestimmt

Seite 328.

sein lässt, jeder für α oder β willkürlich gesetzten Zahl unzählige
Werthe von β respective α, und dieser Umstand ermöglicht die relativ
leichte Auffindung irgend eines solchen Werthes und damit die Lösung der
vorgelegten Gleichung.
-/
example (m n r α : ℚ) (hn : n ≠ 0) :
    r = m * α + n * ((r - m * α) / n) := by
  field_simp
  ring

example (m n r β : ℚ) (hm : m ≠ 0) :
    r = m * ((r - n * β) / m) + n * β := by
  field_simp
  ring

/-
Soll jedoch die in II vorschriebene Transformation ausgeführt werden,
ohne einen entsprechenden Werth von x zu kennen, so bringe man in II das
Glied (αx + β)² nach links, und weil in der so geformten Gleichung

(a − α²)x² + (b − 2αβ)x + (c − β²) = (γx + δ)(εx + ζ)
-/
example (a b c α β x : ℚ) :
    a * x ^ 2 + b * x + c - (α * x + β) ^ 2 =
    (a - α ^ 2) * x ^ 2 + (b - 2 * α * β) * x + (c - β ^ 2) := by
  ring

/-
die linke Seite ein Product zweier lineären Factoren werden soll, so
muss ihre Determinante ein Quadrat sein; also

(b − 2αβ)² − 4(a − α²)(c − β²) = Δ²,

oder

Δ² = 4(aβ² − bαβ + cα²) + b² − 4ac (IV)
-/
example (a b c α β : ℚ) :
    (b - 2 * α * β) ^ 2 - 4 * (a - α ^ 2) * (c - β ^ 2) =
    4 * (a * β ^ 2 - b * α * β + c * α ^ 2) + b ^ 2 - 4 * a * c := by
  ring

/-
eine in ganzen Zahlen mögliche Gleichung, weil (III) eine solche ist.
-/
example (a b c m n r : ℤ) (_hn : n ≠ 0)
    (h : r ^ 2 = a * m ^ 2 + b * m * n + c * n ^ 2) :
    ∃ α β : ℤ, r = m * α + n * β := by
  let g : ℤ := Int.gcd m n
  obtain ⟨u, hm⟩ := Int.gcd_dvd_left m n
  obtain ⟨v, hn⟩ := Int.gcd_dvd_right m n
  change m = g * u at hm
  change n = g * v at hn
  have hsq : g ^ 2 ∣ r ^ 2 := by
    refine ⟨a * u ^ 2 + b * u * v + c * v ^ 2, ?_⟩
    rw [h, hm, hn]
    ring
  obtain ⟨t, ht⟩ :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hsq
  refine ⟨Int.gcdA m n * t, Int.gcdB m n * t, ?_⟩
  change r = (Int.gcd m n : ℤ) * t at ht
  rw [ht, Int.gcd_eq_gcd_ab]
  ring

example (a b c m n r α β : ℤ) (hn : n ≠ 0)
    (h : r ^ 2 = a * m ^ 2 + b * m * n + c * n ^ 2)
    (hIII : r = m * α + n * β) :
    ∃ Δ : ℤ, Δ ^ 2 = 4 * (a * β ^ 2 - b * α * β + c * α ^ 2) + b ^ 2 - 4 * a * c := by
  have hroot : (a - α ^ 2) * m ^ 2 + (b - 2 * α * β) * m * n + (c - β ^ 2) * n ^ 2 = 0 := by
    rw [hIII] at h
    nlinarith [h]
  have hscaled : (2 * (a - α ^ 2) * m + (b - 2 * α * β) * n) ^ 2 =
      n ^ 2 * (4 * (a * β ^ 2 - b * α * β + c * α ^ 2) + b ^ 2 - 4 * a * c) := by
    linear_combination 4 * (a - α ^ 2) * hroot
  let δ : ℚ := (2 * ((a : ℚ) - (α : ℚ) ^ 2) * m + (b - 2 * (α : ℚ) * β) * n) / n
  have hδ : δ ^ 2 = (4 * (a * β ^ 2 - b * α * β + c * α ^ 2) + b ^ 2 - 4 * a * c : ℤ) := by
    dsimp [δ]
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    field_simp
    exact_mod_cast hscaled
  have hs : IsSquare ((4 * (a * β ^ 2 - b * α * β + c * α ^ 2) + b ^ 2 - 4 * a * c : ℤ) : ℚ) :=
    ⟨δ, by nlinarith [hδ]⟩
  obtain ⟨Δ, hΔ⟩ := Rat.isSquare_intCast_iff.mp hs
  exact ⟨Δ, by nlinarith [hΔ]⟩

/-
Seite 328.

Schreibt man hier D für b² − 4ac (die Determinante in I) und schafft das
zweite Glied −bαβ weg, was auf zweierlei Weise geschehen kann, so folgt

für β = (K + bα)/(2a) ... K² = aΔ² + D(α² − a) (V)
-/
example (a b c α β : ℚ) :
    (2 * a * β - b * α) ^ 2 =
    a * (4 * (a * β ^ 2 - b * α * β + c * α ^ 2) + b ^ 2 - 4 * a * c) +
      (b ^ 2 - 4 * a * c) * (α ^ 2 - a) := by
  ring

example (a b α K : ℚ) (ha : a ≠ 0) :
    2 * a * ((K + b * α) / (2 * a)) - b * α = K := by
  field_simp
  ring

/-
und

für α = (L + bβ)/(2c) ... L² = cΔ² + D(β² − c) (VI)
-/
example (a b c α β : ℚ) :
    (2 * c * α - b * β) ^ 2 =
    c * (4 * (a * β ^ 2 - b * α * β + c * α ^ 2) + b ^ 2 - 4 * a * c) +
      (b ^ 2 - 4 * a * c) * (β ^ 2 - c) := by
  ring

example (b c β L : ℚ) (hc : c ≠ 0) :
    2 * c * ((L + b * β) / (2 * c)) - b * β = L := by
  field_simp
  ring

/-
Diese zwei Gleichungen sind wegen der Beschaffenheit von (I) und (III)
für jeden rationalen Werth von α respective β in eben solchen Zahlen
möglich, was sich auch aus ihrer Form und den Beziehungen von a und c zu
D ergibt, welche aus der in ganzen Zahlen möglichen Gleichung (IV)
sogleich zu ersehen sind, wenn daselbst erst α und dann β gleich Null
gesetzt werden.
-/
/-
Zu jedem Werthe einer dieser Variablen gehören unzählige Werthe der in K
respective L steckenden zweiten, von denen man einen oder den andern, er
mag eine ganze oder eine gebrochene Zahl sein, mittels einiger Versuche
aus (V) oder (VI)

Seite 329.

oder aus einer der Gleichungen findet, die sich aus diesen zweien
ableiten lassen.
-/
/-
Ob entartete Fälle mit D = 0 stillschweigend ausgeschlossen waren, ist
im obigen Wortlaut nicht festgelegt; eine zusätzliche Voraussetzung wird
hier nicht eingeführt.
-/
/- Aussagen ohne Beweis; geprüft wird nur die Formulierung als Proposition. -/
example : Prop :=
  ∀ (a b c : ℤ) (α : ℚ), a ≠ 0 →
    (∃ x y : ℚ, y ^ 2 = a * x ^ 2 + b * x + c) →
    Set.Infinite {β : ℚ | ∃ Δ : ℚ,
      (2 * a * β - b * α) ^ 2 =
        a * Δ ^ 2 + (b ^ 2 - 4 * a * c) * (α ^ 2 - a)}

example : Prop :=
  ∀ (a b c : ℤ) (β : ℚ), c ≠ 0 →
    (∃ x y : ℚ, y ^ 2 = a * x ^ 2 + b * x + c) →
    Set.Infinite {α : ℚ | ∃ Δ : ℚ,
      (2 * c * α - b * β) ^ 2 =
        c * Δ ^ 2 + (b ^ 2 - 4 * a * c) * (β ^ 2 - c)}

/-
Wählt man zur Rechnung die Gleichung (V), so ist der Grösse α ein
solcher Werth zu ertheilen, dass α² − a möglichst klein, oder eine
Quadratzahl, die auch ein Bruch sein darf, oder ein Multiplum eines
Quadrates werde, zu dessen Bildung auch D beitragen kann; durch dieses
Quadrat, etwa λ², dividire man mit Einbeziehung von a beide Seiten der
Gleichung V, welche dadurch, wenn wir hier a von dieser Division
unberührt bleiben lassen und

K = λk, Δ = λd, D(α² − a) = λf setzen, in k² = ad² + f (VII)

übergeht.
-/
/-
Vermutlicher Druckfehler: Die angegebene Division durch λ² erfordert
D(α² − a) = λ²f statt λf. Mit λf bleibt der Rest f/λ.
Zuerst wird die Differenz zu VII, dann die Rechnung mit λ²f geprüft.
-/
example (a k d f lam : ℚ) (hlam : lam ≠ 0) :
    ((lam * k) ^ 2 - a * (lam * d) ^ 2 - lam * f) / lam ^ 2 -
      (k ^ 2 - a * d ^ 2 - f) = f - f / lam := by
  field_simp
  ring

example (a k d f lam : ℚ) (hlam : lam ≠ 0) :
    ((lam * k) ^ 2 - a * (lam * d) ^ 2 - lam ^ 2 * f) / lam ^ 2 =
      k ^ 2 - a * d ^ 2 - f := by
  field_simp

/-
Das Abkürzen durch λ² hat nur den Zweck, die Rechnung in kleineren
Zahlen zu führen; weil aber durch die Annahme des gemeinschaftlichen
Factors λ in den Grössen K oder L und Δ die Lösungen der Gleichungen (V)
oder (VI) in theilfremden Zahlen ausgeschlossen und dadurch die Chancen
der schnellen Auffindung eines entsprechenden Werthes vermindert werden,
so kann, falls die Achterreste eine Lösung in ganzen Zahlen als möglich
erscheinen lassen, D keine grosse Zahl und λ einziffrig ist, die
Division durch λ² auch unterbleiben, oder erst dann successive durch die
quadratischen Factoren von λ² erfolgen, wenn das Suchen nach relativen
Primzahlen fruchtlos sein sollte.

Dieses Verfahren empfiehlt sich besonders dann, wenn a oder c negativ
und daher die Anzahl der in ganzen Zahlen etwa möglichen Lösungen von
(V) oder (VI) eine begrenzte ist; in diesem Falle durchforsche man den
ganzen Zahlenraum, in welchem Wurzeln der Gleichung liegen können,
wofern dies nicht zu viele Versuche erfordert.
-/
example (a b c : ℤ) (α β : ℚ) :
    (a < 0 → Set.Finite {p : ℤ × ℤ |
      (p.1 : ℚ) ^ 2 = a * (p.2 : ℚ) ^ 2 + (b ^ 2 - 4 * a * c : ℤ) * (α ^ 2 - a)}) ∧
    (c < 0 → Set.Finite {p : ℤ × ℤ |
      (p.1 : ℚ) ^ 2 = c * (p.2 : ℚ) ^ 2 + (b ^ 2 - 4 * a * c : ℤ) * (β ^ 2 - c)}) := by
  have finiteNegative (A : ℤ) (F : ℚ) (hA : A < 0) :
      Set.Finite {p : ℤ × ℤ | (p.1 : ℚ) ^ 2 = A * (p.2 : ℚ) ^ 2 + F} := by
    let N : ℤ := ⌈|F|⌉
    have self_le_sq (z : ℤ) : z ≤ z ^ 2 := by
      rcases (show z ≤ 0 ∨ 1 ≤ z by omega) with hz | hz
      · nlinarith [sq_nonneg z]
      · nlinarith [mul_nonneg (show 0 ≤ z - 1 by omega) (show 0 ≤ z by omega)]
    apply ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)).subset
    rintro ⟨K, Δ⟩ h
    change (K : ℚ) ^ 2 = A * (Δ : ℚ) ^ 2 + F at h
    have hAq : (A : ℚ) + 1 ≤ 0 := by exact_mod_cast (show A + 1 ≤ 0 by omega)
    have hsumq : (K : ℚ) ^ 2 + (Δ : ℚ) ^ 2 ≤ F := by
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hAq (sq_nonneg (Δ : ℚ))]
    have hFN : F ≤ (N : ℚ) := (le_abs_self F).trans (Int.le_ceil |F|)
    have hsum : K ^ 2 + Δ ^ 2 ≤ N := by exact_mod_cast hsumq.trans hFN
    have hK : -N ≤ K ∧ K ≤ N := by
      constructor <;> nlinarith [self_le_sq K, self_le_sq (-K), sq_nonneg Δ]
    have hΔ : -N ≤ Δ ∧ Δ ≤ N := by
      constructor <;> nlinarith [self_le_sq Δ, self_le_sq (-Δ), sq_nonneg K]
    exact ⟨hK, hΔ⟩
  exact ⟨fun ha => finiteNegative a ((b ^ 2 - 4 * a * c : ℤ) * (α ^ 2 - a)) ha,
    fun hc => finiteNegative c ((b ^ 2 - 4 * a * c : ℤ) * (β ^ 2 - c)) hc⟩

/-
Bezüglich der Gleichungen (V) und (VI) ist noch zu bemerken, dass, wenn
die Gleichung, aus welcher sie gebildet wurden, in ganzen Zahlen möglich
ist, zu jedem ganzzahligen α unendlich viele eben solche β gehören, aber
nicht umgekehrt; denn alsdann ist

x = m/n = m/1, y = r/n = r/1
-/
/-
Der vorhergehende Absatz behandelt endliche Fälle, der folgende setzt
unendlich viele Paare voraus. Die weite Formulierung bleibt hier samt
dieser Unklarheit erhalten.
-/
/- Aussage ohne Beweis; geprüft wird nur die Formulierung als Proposition. -/
example : Prop :=
  ∀ (a b c α : ℤ), a ≠ 0 →
    (∃ m r : ℤ, r ^ 2 = a * m ^ 2 + b * m + c) →
    Set.Infinite {β : ℤ | ∃ m r : ℤ,
      r ^ 2 = a * m ^ 2 + b * m + c ∧ r = m * α + β}

/-
Seite 330.

und (III) geht in r = mα + β über;
-/
example (m r α : ℤ) : r = m * α + (r - m * α) := by ring

/-
da m und r unzählig viele Paare ganzer Zahlen bezeichnen und für jedes
solche Paar der Grösse α jeder Werth aus der natürlichen Zahlenreihe,
positiv oder negativ genommen, ertheilt werden kann, so entsprechen
jedem ganzzahligen α unendlich viele eben so beschaffene Werthe von β
und somit auch von K = 2aβ − bα; dagegen darf für ein besonderes Paar
vom m und r der Werth von β nicht willkührlich angenommen werden, wenn α
und dem zufolge auch L ganze Zahlen werden sollen. Es ist daher die
Wahrscheinlichkeit, mittels der Gleichung (V) eher auf ein ganzzahliges
K zu stossen, grösser als die, mittels (VI) auf ein ganzzahliges L, und
insofern gebührt der Gleichung (V) der Vorzug; doch kann in besonderen
Fällen, wenn (V) den Dienst versagt, wie auch wenn c negativ oder
kleiner als a ist, es vortheilhaft sein, sich der Gleichung (VI) zu
bedienen.
-/
/- Aussage ohne Beweis; geprüft wird nur die Formulierung als Proposition. -/
example : Prop :=
  ∀ (a b c α : ℤ), a ≠ 0 →
    Set.Infinite {p : ℤ × ℤ | p.2 ^ 2 = a * p.1 ^ 2 + b * p.1 + c} →
    Set.Infinite {β : ℤ | ∃ m r : ℤ,
      r ^ 2 = a * m ^ 2 + b * m + c ∧ r = m * α + β}

/-
Um die Lösungsversuche mit kleineren und passenden Zahlen zu machen,
setze man in (VII) k = az + r und bestimme für die so erhaltene
Gleichung

d² = az² + 2rz + g + (r² − h)/a

die Werthe von r aus der Congruenz r² ≡ h (mod a);
-/
example (a z r g h : ℚ) (ha : a ≠ 0) :
    ((a * z + r) ^ 2 - (h - a * g)) / a =
      a * z ^ 2 + 2 * r * z + g + (r ^ 2 - h) / a := by
  field_simp
  ring

/-
von den 2μ Wurzeln derselben setze man blos die erste Hälfte für r in
die letzte Gleichung ein, und untersuche in jeder der so entstandenen μ
Gleichungen, deren Repräsentant

d² = az² + 2rz + p (VIII)

ist, mittels der Achterreste, welche von den Zahlenformen 2n + 1, 4n +
2, 4n die Unbestimmte z annehmen dürfe, damit das letzte Trinom eine
Quadratzahl werden könne; dabei sind auch in Vorhinein jene Zahlen, als
für z ungeeignet, auszuscheiden, von denen das Zahlenglied p ein
quadratischer Nichtrest ist.
-/
example (a z r g h p : ℚ) (hp : p = g + (r ^ 2 - h) / a) :
    a * z ^ 2 + 2 * r * z + g + (r ^ 2 - h) / a =
      a * z ^ 2 + 2 * r * z + p := by rw [hp]; ring

/-
Hierauf gebe man der Variablen z in jeder der μ Gleichungen einige auf
einander folgende zulässige Werthe, und wenn keiner derselben ein
Quadrat erzeugen sollte, so behandle man irgend eine dieser μ
Gleichungen — die übrigen sind gemeiniglich nicht mehr nöthig — in der
eben dargestellten Weise, um sie

Seite 331.

auf die in (II) stehende Form zu bringen, d. h. man suche für z einen
Genüge leistenden Bruch.

Dieses Verfahren ist so lange fortzusetzen, bis man auf eine Gleichung
(VIII) kömmt, die sich mit einer durch Probiren zu findenden ganzen Zahl
lösen lässt, was selbst bei vierziffrigen Coefficienten, wenn nicht
früher, so nach dem dritten Transformations-Versuche eintreten dürfte.

Ein weiteres Fortschreiten in den abgeleiteten Gleichungen erweist sich
der etwas mühsamen Recursionsrechnung wegen nicht als vortheilhaft,
sondern es ist, wenn man auch für z,, nicht alsbald auf eine ganze Zahl
stossen sollte, der Grösse α respective β ein anderer Werth zu
ertheilen, oder die Gleichung (V) mit (VI) zu vertauschen, oder endlich
aus dem Systeme jener μ Gleichungen eine andere zu wählen. Jede dieser
Veränderungen wird von Erfolg sein, da sie neue Gleichungen schafft, von
denen eine oder die andere in ganzen Zahlen gelöst werden kann.

Eine solche Wendung in der Rechnung, die bei Gleichungen mit grossen
Constanten zuweilen nöthig ist, verursacht übrigens weit weniger Mühe,
als die Auflösung einer einzigen quadratischen Congruenz, deren Modul
eine grosse Primzahl enthält; in diesem Falle wird die directe Methode
von Lagrange praktisch unausführbar, während der hier angegebene Vorgang
auch bei siebenziffrigen Primzahlen bald zum Ziele führt.
-/

/-
Seite 331.

Bei diesem Verfahren ist man der Auflösung quadratischer Congruenzen
ganz überhoben, sobald α oder β einen von Null verschiedenen Werth
erhält. Anstatt nämlich den durch die Substitution K = az + r
entstandenen Bruch (r² − h)/a durch Lösung der Congruenz r² ≡ h (mod a)
in eine ganze Zahl zu verwandeln, kömmt man mittels der zu (V) gehörigen
Formel

β = (K + αb)/(2a) oder K = 2aβ − αb

auf die Gleichung az + r = 2aβ − αb, welche sofort die gelöste Congruenz
r ≡ −αb (mod a) liefert, und aus dieser einen Wurzel r findet man die
etwaigen andern durch Vereinigung lineärer Congruenzen.
-/
example (a b α β z r : ℤ) (h : a * z + r = 2 * a * β - α * b) :
    Int.ModEq a r (-α * b) := by
  apply Int.modEq_iff_dvd.mpr
  exact ⟨z - 2 * β, by linarith⟩

/-
Hat man aber K = λk und k = az + r gesetzt, so ist

Seite 332.

aλz + λr = 2aβ − αb, somit λr ≡ −αb (mod a).
-/
example (a b α β z r lam : ℤ)
    (h : a * lam * z + lam * r = 2 * a * β - α * b) :
    Int.ModEq a (lam * r) (-α * b) := by
  apply Int.modEq_iff_dvd.mpr
  exact ⟨lam * z - 2 * β, by linarith⟩

/-
Würde endlich bei der Abkürzung durch λ² der Coefficient a in die
Division einbezogen werden und in a₁ übergegangen sein, in Folge dessen
k = a₁z + r zu setzen käme, so hätte man aus der Congruenz λr ≡ −αb (mod
a₁) den Werth von r zu bestimmen. Überhaupt muss 2aβ − αb auf die Form
a₁λz + λr gebracht werden, und dabei r kleiner als a₁ sein; für die
Gleichung (VI) gelten analoge Regeln.

Nur wenn in (I) b = 0 ist, muss Eine quadratische Congruenz auf
gewöhnliche Art gelöst werden.
-/
example (a b α β z r lam a₁ : ℤ) (ha : a₁ ∣ a)
    (h : a₁ * lam * z + lam * r = 2 * a * β - α * b) :
    Int.ModEq a₁ (lam * r) (-α * b) := by
  obtain ⟨q, rfl⟩ := ha
  apply Int.modEq_iff_dvd.mpr
  exact ⟨lam * z - 2 * q * β, by linarith⟩

/-
Der Grund, warum von den 2μ Wurzeln der oben besprochenen Congruenz nur
die erste Hälfte in die betreffende Gleichung einzusetzen ist, liegt
darin, dass zu jeder Wurzel r in der ersten Hälfte sich eine Wurzel a −
r in der zweiten Hälfte findet; ist nun K = az + r und man setzt hier z₁
− 1 für z, so wird K = az₁ − (a − r); aus dieser Gleichung erhält man
für K denselben Werth, wie aus der vorhergehenden, wenn z₁ um Eins
grösser genommen wird als z, daher ist die zweite Hälfte der Wurzeln
überflüssig.
-/
example (a z₁ r : ℚ) : a * (z₁ - 1) + r = a * z₁ - (a - r) := by ring

/-
Die vorstehende Identität prüft den gedruckten Wechsel z = z₁ − 1.
Die folgende Aussage erfasst zusätzlich die Wurzelpaarung r, a − r
und die Abdeckung des jeweils ergänzenden Restzweiges. Die Abdeckung
betrifft die Quadratwerte, wie sie in (V) und (VII), k² = ad² + f,
auftreten. Sie behauptet keine Gleichheit der vorzeichenbehafteten
Familien az + r und az + (a − r); der gedruckte Ausdruck für denselben
Werth lautet az₁ − (a − r). Eine beliebige Halbierung der Wurzelmenge
wird damit nicht behauptet.
Aussage ohne Beweis; geprüft wird nur die Formulierung als Proposition.
-/
example (a h : ℤ) : Prop :=
  (∀ r : ℤ, Int.ModEq a (r ^ 2) h →
    Int.ModEq a ((a - r) ^ 2) h) ∧
  (∀ r K : ℤ, Int.ModEq a (r ^ 2) h →
    (∃ z : ℤ, K = a * z + (a - r)) →
    ∃ z : ℤ, K ^ 2 = (a * z + r) ^ 2)

/-
Mit dem gefundenen ganzzahligen Werthe von z ist die aus Substitutionen
und Transformationen bestehende rückläufige Rechnung durchzuführen,
wobei zuweilen für β oder α mit kleineren Zahlen geschriebene Werthe
erzielt werden können, wenn man die für eine dieser Grössen eingesetzte
Zahl negativ nimmt; Brüche sind für α und β eben so brauchbar, wie ganze
Zahlen.

Jede Abkürzung in (V) oder (VI), wie auch in den ferneren Gleichungen
ist in der recurrenten Rechnung wohl zu berücksichtigen.

Wenn in (I) b = 0 ist, wie auch dann, wenn α oder β gleich Null gesetzt
wird, so bediene man sich der einfacheren Gleichung (IV), denn in beiden
Fällen gehen (V) und (VI) nach vollzogener Abkürzung in (IV) über.
Letztere Gleichung hat für b = 0 die Form

Δ² = aβ² + c(α² − a) oder Δ² = cα² + a(β² − c). (IV₁)
-/
example (a c α β : ℚ) :
    (4 * (a * β ^ 2 + c * α ^ 2) - 4 * a * c) / 4 =
      a * β ^ 2 + c * (α ^ 2 - a) := by ring

example (a c α β : ℚ) :
    a * β ^ 2 + c * (α ^ 2 - a) = c * α ^ 2 + a * (β ^ 2 - c) := by ring

/-
Mit jedem bekannten Werthe von x, etwa mit m/n, lassen sich beliebig
viele andere finden, indem man aus (III) α und β bestimmt,

Seite 333.

hierauf in der Gleichung ax² + bx + c = (αx + β)² + (nx − m)(εx + ζ) das
Quadrat auf die linke Seite schafft und diese dann durch nx − m
dividirt; der Quotient εx + ζ liefert die Wurzel x = −ζ/ε und ändert
sich mit α und β. Setzt man in (III) ζ und −ε statt m respective n, so
ergeben sich neue Werthe von x.
-/
example (ε ζ : ℚ) (hε : ε ≠ 0) : ε * (-ζ / ε) + ζ = 0 := by
  field_simp
  ring

private theorem divisionNachIII (a b c m n r α β : ℚ) (hn : n ≠ 0)
    (hknown : r ^ 2 = a * m ^ 2 + b * m * n + c * n ^ 2)
    (hIII : r = m * α + n * β) :
    let ε := (a - α ^ 2) / n
    let ζ := (b - 2 * α * β + m * ε) / n
    ∀ x : ℚ, a * x ^ 2 + b * x + c - (α * x + β) ^ 2 =
      (n * x - m) * (ε * x + ζ) := by
  intro ε ζ x
  have hknown' : (m * α + n * β) ^ 2 =
      a * m ^ 2 + b * m * n + c * n ^ 2 := by
    rw [← hIII]
    exact hknown
  dsimp [ε, ζ]
  field_simp
  nlinarith [hknown']

private theorem wurzelNachDivision (a b c m n r α β : ℚ) (hn : n ≠ 0)
    (hknown : r ^ 2 = a * m ^ 2 + b * m * n + c * n ^ 2)
    (hIII : r = m * α + n * β) :
    let ε := (a - α ^ 2) / n
    let ζ := (b - 2 * α * β + m * ε) / n
    ε ≠ 0 →
      a * (-ζ / ε) ^ 2 + b * (-ζ / ε) + c =
        (α * (-ζ / ε) + β) ^ 2 ∧
      let r₁ := ζ * α - ε * β
      r₁ ^ 2 = a * ζ ^ 2 + b * ζ * (-ε) + c * (-ε) ^ 2 ∧
        r₁ = ζ * α + (-ε) * β := by
  intro ε ζ hε
  have hfactor := divisionNachIII a b c m n r α β hn hknown hIII (-ζ / ε)
  change a * (-ζ / ε) ^ 2 + b * (-ζ / ε) + c - (α * (-ζ / ε) + β) ^ 2 =
    (n * (-ζ / ε) - m) * (ε * (-ζ / ε) + ζ) at hfactor
  have hzero : ε * (-ζ / ε) + ζ = 0 := by
    field_simp
    ring
  rw [hzero, mul_zero] at hfactor
  have hroot : a * (-ζ / ε) ^ 2 + b * (-ζ / ε) + c =
      (α * (-ζ / ε) + β) ^ 2 := sub_eq_zero.mp hfactor
  constructor
  · exact hroot
  · constructor
    · field_simp at hroot
      nlinarith [hroot]
    · ring

example (a b c m n r α β α₁ : ℚ) (hn : n ≠ 0)
    (hknown : r ^ 2 = a * m ^ 2 + b * m * n + c * n ^ 2)
    (hIII : r = m * α + n * β) :
    let ε := (a - α ^ 2) / n
    let ζ := (b - 2 * α * β + m * ε) / n
    ε ≠ 0 →
      let r₁ := ζ * α - ε * β
      let β₁ := (r₁ - ζ * α₁) / (-ε)
      let ε₁ := (a - α₁ ^ 2) / (-ε)
      let ζ₁ := (b - 2 * α₁ * β₁ + ζ * ε₁) / (-ε)
      r₁ = ζ * α₁ + (-ε) * β₁ ∧
        ∀ x : ℚ, a * x ^ 2 + b * x + c - (α₁ * x + β₁) ^ 2 =
          ((-ε) * x - ζ) * (ε₁ * x + ζ₁) := by
  intro ε ζ hε r₁ β₁ ε₁ ζ₁
  have hI₁ : r₁ ^ 2 = a * ζ ^ 2 + b * ζ * (-ε) + c * (-ε) ^ 2 :=
    (wurzelNachDivision a b c m n r α β hn hknown hIII hε).2.1
  have hn₁ : -ε ≠ 0 := neg_ne_zero.mpr hε
  have hIII₁ : r₁ = ζ * α₁ + (-ε) * β₁ := by
    dsimp [β₁]
    field_simp
    ring
  exact ⟨hIII₁, divisionNachIII a b c ζ (-ε) r₁ α₁ β₁ hn₁ hI₁ hIII₁⟩

/-
Ein ausdrücklicher Ausschluss des Falles D = 0 steht nicht im obigen
Wortlaut und wird der Aussage hier nicht hinzugefügt.
-/
/- Aussage ohne Beweis; geprüft wird nur die Formulierung als Proposition. -/
example : Prop :=
  ∀ (a b c m n r : ℤ), n ≠ 0 →
    ((r : ℚ) / n) ^ 2 = a * ((m : ℚ) / n) ^ 2 + b * ((m : ℚ) / n) + c →
    Set.Infinite {x : ℚ | ∃ y : ℚ, y ^ 2 = a * x ^ 2 + b * x + c}

/-
Die Wirksamkeit dieser Methode und die dabei zu beobachtenden Vortheile
mögen an einigen Beispielen ersichtlich gemacht werden.
-/

end Kunerth1878a.AllgemeinerTeil
