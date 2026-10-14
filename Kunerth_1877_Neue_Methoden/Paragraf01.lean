/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf01

/-
Seite 7

Neue Methoden zur Auflösung unbestimmter quadratischer
Gleichungen in ganzen Zahlen.
Von Prof. Adolf Kunerth.

§. 1.

1. Hat man aus einer unbestimmten quadratischen Gleichung für x die
Gleichung

I    x = (Ap²+Bp+C)/(ap²+bp+c)

gefunden, so lassen sich aus derselben die ganzzahligen Werthe von x
ermitteln, falls solche vorhanden sind.
In diesem Bruche, welcher die p-Function heissen mag, bedeutet p eine
unbestimmte rationale Zahl, die anderen Buchstaben aber bezeichnen
gegebene ganze Zahlen. Hätten die Coëfficienten a, b, c einen
gemeinschaftlichen Factor m, so multiplicire man beide Seiten der
Gleichung mit m, worauf von den ganzzahligen Werthen, die für mx
gefunden werden, die durch m theilbaren die gesuchten sind. Es kann
daher angenommen werden, dass die Coëfficienten im Nenner keinen
gemeinschaftlichen Factor enthalten.
-/

/-
Formale Zuordnung: a₁, b₁, c₁ bezeichnen die durch m getheilten
Nennercoëfficienten, z einen ganzzahligen Werth von mx. Die
Theilbarkeitsbedingung wählt genau die ganzzahligen Lösungen der
ursprünglichen p-Function aus. Der Factor m und der Nenner sind
ungleich Null, damit die bezeichneten Brüche bestimmt sind.
Die Behauptung wird als Proposition festgehalten, nicht bewiesen.
-/

example : Prop :=
  ∀ A B C a b c m a₁ b₁ c₁ : ℤ, ∀ p : ℚ,
    m ≠ 0 → a = m * a₁ → b = m * b₁ → c = m * c₁ →
    (a : ℚ) * p ^ 2 + (b : ℚ) * p + (c : ℚ) ≠ 0 →
    ∀ z : ℤ,
      ((z : ℚ) =
        ((A : ℚ) * p ^ 2 + (B : ℚ) * p + (C : ℚ)) /
          ((a₁ : ℚ) * p ^ 2 + (b₁ : ℚ) * p + (c₁ : ℚ)) ∧
        m ∣ z) ↔
      ∃ x : ℤ,
        (x : ℚ) =
          ((A : ℚ) * p ^ 2 + (B : ℚ) * p + (C : ℚ)) /
            ((a : ℚ) * p ^ 2 + (b : ℚ) * p + (c : ℚ)) ∧
          z = m * x

example (a b c m p : ℚ) :
    m * (a * p ^ 2 + b * p + c) =
      m * a * p ^ 2 + m * b * p + m * c := by ring

/-
2. Hätten a und A den grössten gemeinschaftlichen Divisor n, so dass
a = na₁ und A = nA₁, so setze man

p = q/n;

dann wird

x = (A₁q²+Bq+Cn)/(a₁q²+bq+cn)

und a₁ ist prim gegen A₁.

Seite 8

Es können somit in der obigen Gleichung a und A als relative
Primzahlen angesehen werden.
-/

/-
Die folgende Proposition hält die behauptete relative Primheit nach
Division durch den grössten gemeinschaftlichen Divisor fest, ohne
sie zu beweisen. n ist der nichtnegative ganzzahlige ggT; n ≠ 0
ist für die Substitution p = q/n erforderlich.
-/

example : Prop :=
  ∀ a A n a₁ A₁ : ℤ,
    n = (Int.gcd a A : ℤ) → n ≠ 0 →
    a = n * a₁ → A = n * A₁ → Int.gcd a₁ A₁ = 1

example (A₁ B C n q : ℚ) (hn : n ≠ 0) :
    n * (n * A₁ * (q / n) ^ 2 + B * (q / n) + C) =
      A₁ * q ^ 2 + B * q + C * n := by field_simp

example (a₁ b c n q : ℚ) (hn : n ≠ 0) :
    n * (n * a₁ * (q / n) ^ 2 + b * (q / n) + c) =
      a₁ * q ^ 2 + b * q + c * n := by field_simp

example (A₁ B C a₁ b c n q : ℚ) (hn : n ≠ 0) :
    (n*A₁*(q/n)^2 + B*(q/n) + C) /
      (n*a₁*(q/n)^2 + b*(q/n) + c) =
      (A₁*q^2 + B*q + C*n) / (a₁*q^2 + b*q + c*n) := by
  field_simp

/-
3. Wäre c ein Theiler von C, oder würde nach vollzogener Abkürzung der
zwei Brüche A/a und C/c der letztere mit einem kleineren Nenner
geschrieben als der erstere, so setze man in der obigen Gleichung

p = 1/q

und es wird

x = (Cq²+Bq+A)/(cq²+bq+a),

wodurch die Rechnung in kleineren Zahlen geführt werden kann.
-/

example (A B C q : ℚ) (hq : q ≠ 0) :
    q ^ 2 * (A * (1 / q) ^ 2 + B / q + C) =
      C * q ^ 2 + B * q + A := by field_simp; ring

example (A B C a b c q : ℚ) (hq : q ≠ 0) :
    (A * (1/q)^2 + B / q + C) / (a * (1/q)^2 + b / q + c) =
      (C*q^2 + B*q + A) / (c*q^2 + b*q + a) := by
  field_simp
  ring

/-
4. Nun schaffe man mittelst der Substitution

p = (q−b)/(2a)

das zweite Glied des Nenners weg; dadurch geht dieser in

a(q²−b²+4ac)/(4a²)
-/

example (a b c q : ℚ) (ha : a ≠ 0) :
    a * ((q - b) / (2 * a)) ^ 2 +
      b * ((q - b) / (2 * a)) + c =
      a * (q ^ 2 - b ^ 2 + 4 * a * c) / (4 * a ^ 2) := by
  field_simp
  ring

/-
und der Zähler in

(1/(4a²))(Aq²−2Abq+2aBq+Ab²−2abB+4a²c)
-/

/-
Vermutlicher Druckfehler: Im letzten Gliede steht c statt C.
Die Differenz zum angegebenen Zähler ist C − c; mit C stimmt die
Substitution mit I und der folgenden Formel II überein.
-/

example (A B C a b c q : ℚ) (ha : a ≠ 0) :
    A * ((q - b) / (2 * a)) ^ 2 +
      B * ((q - b) / (2 * a)) + C -
      (A * q ^ 2 - 2 * A * b * q + 2 * a * B * q + A * b ^ 2 -
        2 * a * b * B + 4 * a ^ 2 * c) / (4 * a ^ 2) = C - c := by
  field_simp
  ring

example (A B C a b q : ℚ) (ha : a ≠ 0) :
    A * ((q - b) / (2 * a)) ^ 2 +
      B * ((q - b) / (2 * a)) + C =
      (A * q ^ 2 - 2 * A * b * q + 2 * a * B * q + A * b ^ 2 -
        2 * a * b * B + 4 * a ^ 2 * C) / (4 * a ^ 2) := by
  field_simp
  ring

/-
über, und setzt man 2Ab²−Ab² anstatt Ab², so folgt nach geschehener
Reduction

II    x = [A(q²−b²)+2(aB−Ab)(q−b)+4a²C]/[a((q²−b²)+4ac)]
-/

example (A B C a b q : ℚ) :
    A * q ^ 2 - 2 * A * b * q + 2 * a * B * q + A * b ^ 2 -
      2 * a * b * B + 4 * a ^ 2 * C =
      A * (q ^ 2 - b ^ 2) + 2 * (a * B - A * b) * (q - b) +
        4 * a ^ 2 * C := by ring

/-
5. Im Allgemeinen haben Zähler und Nenner dieses Bruches implicite
den gemeinschaftlichen Factor 4a² was sogleich hervortritt, wenn man
daselbst der obigen Substitution entsprechend q−b = 2ap und
q+b = 2(ap+b) setzt; da wird der Zähler

= 4a²(Ap²+Bp+C)
-/

example (A B C a b p : ℚ) :
    A * ((2 * a * p + b) ^ 2 - b ^ 2) +
      2 * (a * B - A * b) * (2 * a * p) + 4 * a ^ 2 * C =
      4 * a ^ 2 * (A * p ^ 2 + B * p + C) := by ring

/-
Seite 9

und der Nenner

= 4a²(ap²+bp+c).
-/

example (a b c p : ℚ) :
    a * ((2 * a * p + b) ^ 2 - b ^ 2 + 4 * a * c) =
      4 * a ^ 2 * (a * p ^ 2 + b * p + c) := by ring

/-
Multiplicirt man II mit a, so wird im Nenner der Factor 4a verbleiben,
und denkt man für q einen solchen Bruch v/w gesetzt, dass der Nenner
q²−b²+4ac sich in 4a/w² verwandelt, so wird aus dem Bruche in II eine
ganze durch a theilbare Zahl.
Es ist somit

ax = A + [2(aB−Ab)(q−b)+4a(aC−cA)]/[q²−(b²−4ac)]

oder

ax = A + [2(aB−Ab)q+4a(aC−cA)−2b(aB−bA)]/[q²−(b²−4ac)]

oder kurz:

III    ax = A + (dq+f)/(q²−g).
-/

example (A B C a b c q : ℚ)
    (h : q ^ 2 - (b ^ 2 - 4 * a * c) ≠ 0) :
    (A * (q ^ 2 - b ^ 2) + 2 * (a * B - A * b) * (q - b) +
      4 * a ^ 2 * C) / (q ^ 2 - (b ^ 2 - 4 * a * c)) =
      A + (2 * (a * B - A * b) * q + 4 * a * (a * C - c * A) -
        2 * b * (a * B - b * A)) /
        (q ^ 2 - (b ^ 2 - 4 * a * c)) := by
  ring_nf at h ⊢
  field_simp [h]
  ring

/-
6. Für jeden Werth von q, der q²−g = 4a/w² macht, wird der Bruch in III
eine ganze Zahl D, A+D wird ein Vielfaches von a und somit x eine ganze
Zahl. Letzteres wird oft erreicht, wenn sich für den Nenner q²−g ein
Bruch ak/w² finden lässt, dessen Bestandtheil k im Zähler von III als
Factor bereits vorkommt oder dann auftritt, nachdem daselbst für die
Variable q ein entsprechender specieller Werth eingesetzt wurde. Es
wird später gezeigt werden, wie sich aus d, f, g jene ganzen Zahlen
finden lassen, die für k versuchsweise zu setzen sind. Dabei ist aber
zu bemerken, dass nicht jeder Werth von q, welcher den Bruch in III zu
einer ganzen Zahl macht, auch x in eine solche verwandelt.
-/

example : Prop :=
  ∀ (A B C a b c v w : ℤ) (_ha : a ≠ 0) (_hw : w ≠ 0)
    (_hcop : Int.gcd a A = 1)
    (_hprimitive : Int.gcd (Int.gcd a b) c = 1)
    (_hden : ((v : ℚ) / w) ^ 2 - (b ^ 2 - 4 * (a : ℚ) * c) =
      4 * (a : ℚ) / w ^ 2),
    ∃ x : ℤ, (a : ℚ) * x = A +
      (2 * ((a : ℚ) * B - A * b) * ((v : ℚ) / w) +
        4 * (a : ℚ) * (a * C - c * A) -
        2 * (b : ℚ) * (a * B - b * A)) /
      (((v : ℚ) / w) ^ 2 - (b ^ 2 - 4 * (a : ℚ) * c))

/-
7. Für specielle Werthe von q kann der Nenner q²−b²+4ac in III den
Factor 4 verlieren und eine blos durch 2 theilbare oder auch eine
ungerade Zahl werden, was übrigens den Gang der Rechnung nicht ändert.
Der Factor a aber kann in diesem Nenner nicht verschwinden, einen
einzigen sogleich zu erörternden Fall ausgenommen. Denn würde sich für
einen speciellen

Seite 10

Werth von q der Factor a im Nenner q²−b²+4ac verlieren, so müsste dies
auch im Äquivalente dieses Nenners 4a(ap²+bp+c) geschehen, was hier
offenbar nur für p = r/(as) eintreten könnte.
Setzen wir für p diesen Bruch in I, so folgt nach Wegschaffung der
Nenner

x = (Ar²+Bars+Ca²s²)/(ar²+bars+ca²s²);

da hier der Nenner den Factor a enthält, der Zähler aber nicht, weil
a prim gegen A ist, so könnte x keine ganze Zahl werden, falls a im
Nenner des Bruches III verschwände.
-/

example (A B C a r s : ℚ) (ha : a ≠ 0) (hs : s ≠ 0) :
    (a * s) ^ 2 * (A * (r / (a * s)) ^ 2 + B * r / (a * s) + C) =
      A * r ^ 2 + B * a * r * s + C * a ^ 2 * s ^ 2 := by
  field_simp

example (a b c r s : ℚ) (ha : a ≠ 0) (hs : s ≠ 0) :
    (a * s) ^ 2 * (a * (r / (a * s)) ^ 2 + b * r / (a * s) + c) =
      a * r ^ 2 + b * a * r * s + c * a ^ 2 * s ^ 2 := by
  field_simp

/-
8. Enthält a aber einen quadratischen Factor n² und ist b durch n
theilbar, so wird sich für q = nr dieser Factor n² im Bruche III auch
für ein unbestimmt gelassenes r heben, wie aus III zu ersehen ist.
Wäre a = n² und b durch n theilbar, so wird a aus dem Nenner dieses
Bruches hinausfallen.
Dieses nothwendige Vorkommen des Factors a im Nenner des Bruches III
ist von besonderer Wichtigkeit.
-/

example (a₁ b₁ c n r : ℚ) :
    (n * r) ^ 2 - (n * b₁) ^ 2 + 4 * (n ^ 2 * a₁) * c =
      n ^ 2 * (r ^ 2 - b₁ ^ 2 + 4 * a₁ * c) := by ring

/-
9. Haben f und g den gemeinschaftlichen Factor n² und ist d durch n
theilbar, so lässt sich der Bruch in III für q = nr durch n² abkürzen;
denn für d = nδ, f = n²φ, g = n²γ wird

ax = A + (n²δr+n²φ)/(n²r²−n²γ),

also

ax = A + (δr+φ)/(r²−γ).
-/

example (δ φ γ n r : ℚ) (hn : n ≠ 0) :
    (n * δ * (n * r) + n ^ 2 * φ) / ((n * r) ^ 2 - n ^ 2 * γ) =
      (δ * r + φ) / (r ^ 2 - γ) := by
  rw [show n * δ * (n * r) + n ^ 2 * φ = n ^ 2 * (δ * r + φ) by ring,
    show (n * r) ^ 2 - n ^ 2 * γ = n ^ 2 * (r ^ 2 - γ) by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hn)

/-
10. Ja selbst in dem Falle, wenn d den Factor n nicht enthält, während
f durch n und g durch n² theilbar sind, kann die Abkürzung durch n²
stattfinden, nachdem man beide Seiten der Gleichung III mit n
multiplicirt hat; dann ist

anx = An + (dn²r+n²φ)/(n²r²−n²γ)

oder

anx = nA + (dr+φ)/(r²−γ).
-/

example (d φ γ n r : ℚ) (hn : n ≠ 0) :
    n * ((d * (n * r) + n * φ) / ((n * r) ^ 2 - n ^ 2 * γ)) =
      (d * r + φ) / (r ^ 2 - γ) := by
  rw [← mul_div_assoc,
    show n * (d * (n * r) + n * φ) = n ^ 2 * (d * r + φ) by ring,
    show (n * r) ^ 2 - n ^ 2 * γ = n ^ 2 * (r ^ 2 - γ) by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hn)

/-
Seite 11

Es lässt sich demnach die Gleichung III immer so gestalten, dass f und
g keinen gemeinschaftlichen Theiler besitzen, dessen Quadrat ein
Theiler von g ist.
Diese Abkürzungen haben auch dann zu geschehen, wenn d, f oder g gleich
Null sind.

11. Durch diese die weitere Rechnung bedeutend vereinfachenden
Reductionen wird der Factor a im Nenner von III nicht beseitigt; denn
für q = nr wird

p = (nr−b)/(2a) = s/(2a);

setzen wir diesen Bruch für p in das Äquivalent der rechten Seite der
Gleichung III, d. i. in den Ausdruck

a(Ap²+Bp+C)/(ap²+bp+c),

so kommt nach vollzogener Reduction

(As²+2aBs+4a²C)/(s²+2bs+4a),
-/

/-
Vermutlicher Druckfehler: Im Nenner fehlt c im Gliede 4ac.
Die erste Nachrechnung bestimmt die Differenz zum angegebenen Bruch;
die zweite prüft die Substitution mit dem Nenner s² + 2bs + 4ac.
-/

example (A B C a b c s : ℚ) (ha : a ≠ 0)
    (h₁ : a * (s / (2 * a)) ^ 2 + b * (s / (2 * a)) + c ≠ 0)
    (h₂ : s ^ 2 + 2 * b * s + 4 * a ≠ 0) :
    a * (A * (s / (2 * a)) ^ 2 + B * (s / (2 * a)) + C) /
      (a * (s / (2 * a)) ^ 2 + b * (s / (2 * a)) + c) -
      (A * s ^ 2 + 2 * a * B * s + 4 * a ^ 2 * C) /
        (s ^ 2 + 2 * b * s + 4 * a) =
      4 * a * (1 - c) * (A * s ^ 2 + 2 * a * B * s + 4 * a ^ 2 * C) /
        ((s ^ 2 + 2 * b * s + 4 * a * c) * (s ^ 2 + 2 * b * s + 4 * a)) := by
  have he : s ^ 2 + 2 * b * s + 4 * a * c =
      4 * a * (a * (s / (2 * a)) ^ 2 + b * (s / (2 * a)) + c) := by
    field_simp
    ring
  have hd : s ^ 2 + 2 * b * s + 4 * a * c ≠ 0 := by
    rw [he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) ha) h₁
  have hact :
      a * (A * (s / (2 * a)) ^ 2 + B * (s / (2 * a)) + C) /
        (a * (s / (2 * a)) ^ 2 + b * (s / (2 * a)) + c) =
        (A * s ^ 2 + 2 * a * B * s + 4 * a ^ 2 * C) /
          (s ^ 2 + 2 * b * s + 4 * a * c) := by
    field_simp [hd]
    ring
  rw [hact, div_sub_div _ _ hd h₂]
  congr 1
  ring

example (A B C a b c s : ℚ) (ha : a ≠ 0)
    (h₁ : a * (s / (2 * a)) ^ 2 + b * (s / (2 * a)) + c ≠ 0) :
    a * (A * (s / (2 * a)) ^ 2 + B * (s / (2 * a)) + C) /
      (a * (s / (2 * a)) ^ 2 + b * (s / (2 * a)) + c) =
      (A * s ^ 2 + 2 * a * B * s + 4 * a ^ 2 * C) /
        (s ^ 2 + 2 * b * s + 4 * a * c) := by
  have he : s ^ 2 + 2 * b * s + 4 * a * c =
      4 * a * (a * (s / (2 * a)) ^ 2 + b * (s / (2 * a)) + c) := by
    field_simp
    ring
  have hd : s ^ 2 + 2 * b * s + 4 * a * c ≠ 0 := by
    rw [he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) ha) h₁
  field_simp [hd]
  ring

/-
und weil s = 2ap, so enthält in diesem Bruche und daher auch im Bruche
III der Zähler den Factor 4a² und der Nenner den Factor 4a.
Auch die zur Gleichung III gemachte Bemerkung, dass für solche Werthe
von q, welche den Nenner in 4a/w², resp. in 2a/w², a/w² oder ak/w²
verwandeln, der Bruch in eine ganze Zahl D übergeht, die um A vermehrt
ein Vielfaches von a wird, behält ihre Giltigkeit, weil durch jene
Abkürzungen die Factoren a² im Zähler und a im Nenner des Bruches III
nicht verloren gehen; dabei aber muss k einen schicklichen Werth
erhalten.
-/

end Kunerth1877.Paragraf01
