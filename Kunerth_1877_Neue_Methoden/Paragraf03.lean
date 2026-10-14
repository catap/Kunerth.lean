/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf03

/-
Seite 15

§. 3.

1. Wäre jedoch g keine positive Quadratzahl, so multiplicire man beide
Seiten der Gleichung III, welche, wenn ax−A = x₁ gesetzt wird, in

x₁ = (dq+f)/(q²−g)

übergeht, mit q; dann ist

IV    qx₁ = (dq²+fq)/(q²−g)

und da zeigt sich, dass auch dieser Bruch für jene Werthe von q eine
ganze Zahl wird, welche den Bruch III in eine solche verwandeln.
-/

example (d f g q : ℚ) :
    q * ((d * q + f) / (q ^ 2 - g)) =
      (d * q ^ 2 + f * q) / (q ^ 2 - g) := by ring

/-
Ist nämlich q = v/w ein solcher Werth, so ist

x₁ = w(dv+fw)/(v²−gw²)
-/

example (d f g v w : ℚ) (hw : w ≠ 0)
    (_hd : v ^ 2 - g * w ^ 2 ≠ 0) :
    (d * (v / w) + f) / ((v / w) ^ 2 - g) =
      w * (d * v + f * w) / (v ^ 2 - g * w ^ 2) := by
  have he : (v / w) ^ 2 - g = (v ^ 2 - g * w ^ 2) / w ^ 2 := by
    field_simp
  rw [he]
  field_simp

/-
eine ganze Zahl, und weil v prim gegen w, so muss dv+fw durch v²−gw²
theilbar sein;
-/

example (g v w : ℤ) (hvw : Int.gcd v w = 1) :
    IsCoprime (v ^ 2 - g * w ^ 2) w := by
  obtain ⟨s, t, h⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hvw
  refine ⟨s ^ 2, g * w * s ^ 2 + 2 * s * t * v + t ^ 2 * w, ?_⟩
  calc
    _ = (s * v + t * w) ^ 2 := by ring
    _ = 1 := by rw [h]; norm_num

example (d f g v w x₁ : ℤ)
    (hcop : IsCoprime (v ^ 2 - g * w ^ 2) w)
    (hx : (v ^ 2 - g * w ^ 2) * x₁ = w * (d * v + f * w)) :
    v ^ 2 - g * w ^ 2 ∣ d * v + f * w ∧
      v ^ 2 - g * w ^ 2 ∣ v * (d * v + f * w) := by
  have h : v ^ 2 - g * w ^ 2 ∣ d * v + f * w := by
    apply hcop.dvd_of_dvd_mul_left
    exact ⟨x₁, hx.symm⟩
  exact ⟨h, dvd_mul_of_dvd_right h v⟩

/-
nun geht aber für q = v/w die Gleichung IV über in

qx₁ = v(dv+fw)/(v²−gw²),

somit ist auch dieser Bruch und ebenso qx₁ eine ganze Zahl.
-/

example (d f g v w : ℚ) (hw : w ≠ 0) :
    v / w * (w * (d * v + f * w) / (v ^ 2 - g * w ^ 2)) =
      v * (d * v + f * w) / (v ^ 2 - g * w ^ 2) := by
  field_simp

/-
Aus IV folgt

qx₁ = d+(fq−dg)/(q²−g),

Seite 16

und für qx₁−d = z, wird

V    z = (fq−dg)/(q²−g)

und dieser Bruch ist auch eine ganze Zahl, weil z eine solche ist.
-/

/-
Vermutlicher Vorzeichenfehler: Die Division in IV ergibt fq + dg
statt fq − dg. Die folgenden Nachrechnungen zeigen die Differenzen
und prüfen die Division mit dem Pluszeichen. Die danach angeführten
Formeln V bis VII behalten ihre angegebenen Vorzeichen; ihre
gegenseitigen Umformungen bestätigen nicht die fehlerhafte Division.
-/

example (d f g q : ℚ) :
    (d * q ^ 2 + f * q) - (d * (q ^ 2 - g) + (f * q - d * g)) =
      2 * d * g := by
  ring

example (d f g q : ℚ) (h : q ^ 2 - g ≠ 0) :
    (q * ((d * q + f) / (q ^ 2 - g)) - d) -
      (f * q - d * g) / (q ^ 2 - g) = 2 * d * g / (q ^ 2 - g) := by
  ring_nf at h ⊢
  field_simp [h]
  ring

example (d f g q : ℚ) :
    d * q ^ 2 + f * q = d * (q ^ 2 - g) + (f * q + d * g) := by ring

example (d f g q : ℚ) (h : q ^ 2 - g ≠ 0) :
    q * ((d * q + f) / (q ^ 2 - g)) - d =
      (f * q + d * g) / (q ^ 2 - g) := by
  field_simp [h]
  ring

/-
Multiplicirt man diese Gleichung mit d und die Gleichung III in ihrer
am Beginne dieses Paragraphen verkürzten Form mit f, so folgt:

dz = (dfq−d²g)/(q²−g) und fx₁ = (dfq+f²)/(q²−g);
-/

example (d f g q : ℚ) :
    d * ((f * q - d * g) / (q ^ 2 - g)) =
      (d * f * q - d ^ 2 * g) / (q ^ 2 - g) := by ring

example (d f g q : ℚ) :
    f * ((d * q + f) / (q ^ 2 - g)) =
      (d * f * q + f ^ 2) / (q ^ 2 - g) := by ring

/-
subtrahirt man die erste von der zweiten Gleichung, so ist

VI    fx₁−dz = (d²g+f²)/(q²−g)

Der Zähler dieses Bruches ist eine bestimmte Zahl, welche mit S
bezeichnet werden und Stammzahl heissen mag, weil ihr alle ganzzahligen
Werthe von x entstammen; es ist somit

VII    S = d²g+f²
-/

example (d f g q : ℚ) :
    (d * f * q + f ^ 2) / (q ^ 2 - g) -
      (d * f * q - d ^ 2 * g) / (q ^ 2 - g) =
      (d ^ 2 * g + f ^ 2) / (q ^ 2 - g) := by ring

/-
2. Haben d und f einen gemeinschaftlichen Factor, so kürze man die
Gleichung VI durch denselben ab; dieser Factor ist somit aus der
Stammzahl wegzulassen.
-/

example (d f g h : ℤ) (hd : h ∣ d) (hf : h ∣ f) :
    h ∣ d ^ 2 * g + f ^ 2 := by
  obtain ⟨d₁, rfl⟩ := hd
  obtain ⟨f₁, rfl⟩ := hf
  exact ⟨h * (d₁ ^ 2 * g + f₁ ^ 2), by ring⟩

/-
3. Enthalten ferner d, f, g, den Primfactor ν, und zwar f mindestens
in der zweiten, g wegen der bereits oben erwähnten Abkürzungen in der
ersten und d in irgend einer Potenz, so ist jedes ganzzahlige x₁ und z
durch ν oder eine Potenz von ν theilbar.
Denn es sei d = ν^pδ, f = ν^rφ, g = νγ, so ist

x₁ = (ν^pδq+ν^rφ)/(q²−νγ);

ist q prim gegen ν, so ist x₁ ein Vielfaches der niedrigeren der zwei
Potenzen ν^p und ν^r; für q = q₁ aber ist x₁ ein Vielfaches von jener
der zwei Potenzen ν^p und ν^(r−1), welche den kleineren Exponenten hat.
Weil ferner z = qx₁−d, so ist auch z ein Vielfaches von ν^p oder ν^r,
somit sind x₁ und z durch die kleinere der Zahlen νₚ und ν^(r−1)
theilbar.

Seite 17

Für d = 0 sind x₁ und z durch ν^(r−1) und für f = 0 durch ν^p theilbar.
Finden sich nun solche Potenzen der Primzahlen ν, ν′, ν″, ... vor,
durch welche x₁ und z theilbar sind, so kürze man beide Seiten der
Gleichung VI durch das Product dieser Potenzen ab und lasse dieses
Product auch aus der Stammzahl weg.
Durch diese Reductionen kommt man auf den kleinsten Werth der
Stammzahl, wodurch die weitere Rechnung bedeutend vereinfacht wird.
Weil aber derartige Abkürzungen nur mit numerischen Zahlen möglich
sind, so müssen die Gleichungen III und VI als Substrat des Folgenden
dienen.
-/

example (ν : ℕ) (hν : ν.Prime) (e j : ℕ)
    (_he : 0 < e) (hj : 2 ≤ j) (δ φ γ x₁ z : ℤ) (q : ℚ)
    (hg : ¬ (ν : ℤ) ∣ γ)
    (hx : (x₁ : ℚ) =
      ((ν : ℚ) ^ e * δ * q + (ν : ℚ) ^ j * φ) /
        (q ^ 2 - (ν : ℚ) * γ))
    (hz : (z : ℚ) = q * x₁ - (ν : ℚ) ^ e * δ)
    (hden : q ^ 2 - (ν : ℚ) * γ ≠ 0) :
    (ν : ℤ) ^ min e (j - 1) ∣ x₁ ∧
      (ν : ℤ) ^ min e (j - 1) ∣ z := by

  let p : ℤ := ν
  let v : ℤ := q.num
  let w : ℤ := q.den
  have hp : Prime p := Nat.prime_iff_prime_int.mp hν
  have hp₀ : p ≠ 0 := hp.ne_zero
  have hw : w ≠ 0 := by
    dsimp [w]
    exact_mod_cast q.den_nz
  have hwQ : (w : ℚ) ≠ 0 := by exact_mod_cast hw
  have hq : q = (v : ℚ) / (w : ℚ) := by
    simpa [v, w] using (Rat.num_div_den q).symm
  have hvw : IsCoprime v w := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa [v, w] using q.reduced
  have hX : (v ^ 2 - p * γ * w ^ 2) * x₁ =
      p ^ e * δ * v * w + p ^ j * φ * w ^ 2 := by
    have h := (eq_div_iff hden).mp hx
    rw [hq] at h
    field_simp [hwQ] at h
    have hQ : ((v : ℚ) ^ 2 - (p : ℚ) * γ * w ^ 2) * x₁ =
        (p : ℚ) ^ e * δ * v * w + (p : ℚ) ^ j * φ * w ^ 2 := by
      dsimp [p]
      linear_combination h
    exact_mod_cast hQ
  have hZ : w * z = v * x₁ - p ^ e * δ * w := by
    rw [hq] at hz
    field_simp [hwQ] at hz
    have hQ : (w : ℚ) * z = (v : ℚ) * x₁ - (p : ℚ) ^ e * δ * w := by
      dsimp [p]
      linear_combination hz
    exact_mod_cast hQ
  have hcancel (k : ℕ) (N t : ℤ) (hN : ¬ p ∣ N)
      (ht : p ^ k ∣ N * t) : p ^ k ∣ t :=
    ((hp.coprime_iff_not_dvd.mpr hN).pow_left (m := k)).dvd_of_dvd_mul_left ht
  by_cases hv : ¬ p ∣ v
  · have hN : ¬ p ∣ v ^ 2 - p * γ * w ^ 2 := by
      intro h
      apply hv
      apply hp.dvd_of_dvd_pow (n := 2)
      convert dvd_add h (dvd_mul_of_dvd_left (dvd_mul_right p γ) (w ^ 2)) using 1
      ring
    have he₀ : p ^ min e j ∣ p ^ e := pow_dvd_pow p (min_le_left _ _)
    have hj₀ : p ^ min e j ∣ p ^ j := pow_dvd_pow p (min_le_right _ _)
    have hd₀ : p ^ min e j ∣ p ^ e * δ := dvd_mul_of_dvd_left he₀ δ
    have hf₀ : p ^ min e j ∣ p ^ j * φ := dvd_mul_of_dvd_left hj₀ φ
    have hx₀ : p ^ min e j ∣ x₁ := by
      apply hcancel (min e j) (v ^ 2 - p * γ * w ^ 2) x₁ hN
      rw [hX]
      exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd₀ v) w)
        (dvd_mul_of_dvd_left hf₀ (w ^ 2))
    have hz₀ : p ^ min e j ∣ z := by
      apply hcancel (min e j) (v ^ 2 - p * γ * w ^ 2) z hN
      have hzN : (v ^ 2 - p * γ * w ^ 2) * z =
          p ^ j * φ * v * w + p ^ e * δ * (p * γ) * w ^ 2 := by
        apply mul_left_cancel₀ hw
        linear_combination (v ^ 2 - p * γ * w ^ 2) * hZ + v * hX
      rw [hzN]
      exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hf₀ v) w)
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd₀ (p * γ)) (w ^ 2))
    have hle : min e (j - 1) ≤ min e j := by omega
    exact ⟨dvd_trans (pow_dvd_pow p hle) hx₀, dvd_trans (pow_dvd_pow p hle) hz₀⟩
  · have hv' : p ∣ v := by simpa using hv
    have hw' : ¬ p ∣ w := fun h => hp.not_isUnit (hvw.isUnit_of_dvd' hv' h)
    obtain ⟨u, hu⟩ := hv'
    have hN : ¬ p ∣ p * u ^ 2 - γ * w ^ 2 := by
      intro h
      have hgw : p ∣ γ * w ^ 2 := by
        convert dvd_sub (dvd_mul_right p (u ^ 2)) h using 1
        ring
      rcases hp.dvd_mul.mp hgw with hγ | hw₂
      · exact hg hγ
      · exact hw' (hp.dvd_of_dvd_pow hw₂)
    have hjpow : p ^ j = p * p ^ (j - 1) := by
      calc
        p ^ j = p ^ ((j - 1) + 1) := by congr 1; omega
        _ = p * p ^ (j - 1) := by rw [pow_succ]; ring
    have hX' : (p * u ^ 2 - γ * w ^ 2) * x₁ =
        p ^ e * δ * u * w + p ^ (j - 1) * φ * w ^ 2 := by
      apply mul_left_cancel₀ hp₀
      rw [hu, hjpow] at hX
      linear_combination hX
    have he₀ : p ^ min e (j - 1) ∣ p ^ e := pow_dvd_pow p (min_le_left _ _)
    have hj₀ : p ^ min e (j - 1) ∣ p ^ (j - 1) := pow_dvd_pow p (min_le_right _ _)
    have hd₀ : p ^ min e (j - 1) ∣ p ^ e * δ := dvd_mul_of_dvd_left he₀ δ
    have hf₀ : p ^ min e (j - 1) ∣ p ^ (j - 1) * φ := dvd_mul_of_dvd_left hj₀ φ
    have hx₀ : p ^ min e (j - 1) ∣ x₁ := by
      apply hcancel (min e (j - 1)) (p * u ^ 2 - γ * w ^ 2) x₁ hN
      rw [hX']
      exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd₀ u) w)
        (dvd_mul_of_dvd_left hf₀ (w ^ 2))
    refine ⟨hx₀, ?_⟩
    apply hcancel (min e (j - 1)) w z hw'
    rw [hZ]
    exact dvd_sub (dvd_mul_of_dvd_right hx₀ v) (dvd_mul_of_dvd_left hd₀ w)

/-
4. Setzt man in diesen Gleichungen q = v/w, so wird

x₁ = [(dv+fw)/(v²−gw²)]·w² und fx₁−dz = [(d²g+f²)/(v²−gw²)]·w²;
-/

/-
Vermutlicher Druckfehler: Der erste Bruch erhält bei q = v/w den
Factor w statt w², wie schon auf Seite 15. Die Differenz zum hier
angegebenen Ausdruck und die Substitution mit w werden getrennt geprüft.
-/

example (d f g v w : ℚ) (hw : w ≠ 0)
    (_hd : v ^ 2 - g * w ^ 2 ≠ 0) :
    (d * (v / w) + f) / ((v / w) ^ 2 - g) -
      (d * v + f * w) / (v ^ 2 - g * w ^ 2) * w ^ 2 =
      (d * v + f * w) * (w - w ^ 2) / (v ^ 2 - g * w ^ 2) := by
  have he : (v / w) ^ 2 - g = (v ^ 2 - g * w ^ 2) / w ^ 2 := by
    field_simp
  rw [he]
  rw [div_div_eq_mul_div]
  field_simp [hw]

example (d f g v w : ℚ) (hw : w ≠ 0)
    (_hd : v ^ 2 - g * w ^ 2 ≠ 0) :
    (d * (v / w) + f) / ((v / w) ^ 2 - g) =
      (d * v + f * w) / (v ^ 2 - g * w ^ 2) * w := by
  have he : (v / w) ^ 2 - g = (v ^ 2 - g * w ^ 2) / w ^ 2 := by
    field_simp
  rw [he]
  field_simp

example (d f g v w : ℚ) (hw : w ≠ 0) :
    (d ^ 2 * g + f ^ 2) / ((v / w) ^ 2 - g) =
      (d ^ 2 * g + f ^ 2) / (v ^ 2 - g * w ^ 2) * w ^ 2 := by
  have he : (v / w) ^ 2 - g = (v ^ 2 - g * w ^ 2) / w ^ 2 := by
    field_simp
  rw [he, div_div_eq_mul_div]
  ring

/-
da in diesen Brüchen der Factor w² auf die Theilbarkeit des Zählers
durch den Nenner keinen Einfluss hat, so darf letzterer nur solche
Werthe annehmen, durch welche der zweite Zähler, d. i. die Stammzahl
theilbar ist.
-/

example (d f g v w x₁ z : ℤ)
    (hcop : IsCoprime (v ^ 2 - g * w ^ 2) w)
    (hVI : (f*x₁-d*z) * (v^2-g*w^2) = (d^2*g+f^2)*w^2) :
    v ^ 2 - g * w ^ 2 ∣ d ^ 2 * g + f ^ 2 := by
  apply (hcop.pow_right (n := 2)).dvd_of_dvd_mul_right
  exact ⟨f*x₁-d*z, by nlinarith [hVI]⟩

/-
5. Man zerlege daher diese Zahl in ihre einfachen und zusammengesetzten
Factoren und setze, falls g positiv ist, jeden solchen positiv und
negativ genommenen Factor dem Nenner v²−gw² gleich, lasse hierauf w die
Werthe 1, 2, 3, 4, ... durchlaufen und sehe, für welche dieser Werthe v²
eine positive Quadratzahl wird. Würde für w = k, v² = l² (eine
Quadratzahl), somit v = ±l, so könnten +k/l oder −k/l, für q in III
eingesetzt, diesen Bruch in eine ganze Zahl verwandeln, wovon man sich
durch Einsetzen dieser Brüche in III überzeugen muss; dabei gibt es
für die Grösse von k und l keine Grenzen.
-/

/-
Vermutlicher Druckfehler: Aus q = v/w, w = k und v = ±l folgen
die Brüche +l/k und −l/k, nicht die gedruckten +k/l und −k/l.
Die folgende Nachrechnung berichtigt nur diese Einsetzung;
ob III ganzzahlig wird, bleibt wie im Wortlaut eigens zu prüfen.
-/

example (q v w k l : ℚ) (_hk : k ≠ 0) (hq : q = v / w) (hw : w = k)
    (hv : v = l ∨ v = -l) : q = l / k ∨ q = -l / k := by
  rcases hv with hv | hv
  · exact Or.inl (by rw [hq, hv, hw])
  · exact Or.inr (by rw [hq, hv, hw])

/-
6. Ist g aber eine negative Zahl, so dürfen blos die positiven Factoren
der Stammzahl dem Nenner v²+gw² gleichgesetzt werden; nun lässt man w
in 1, 2, 3, 4, ... übergehen, bemerkt jene Glieder dieser Reihe, welche
für v² positive Quadratzahlen liefern, und erprobt die gefundenen
Werthe von v/w durch

Seite 18

Substitution für q in die Gleichung III; die Rechnung findet ihren Abschluss, sobald gw² gleich der Stammzahl
oder grösser als diese wird.

7. Im Hinblicke auf die Gleichung III, welche die Form

x = (A+x₁)/a

annehmen kann, wird man für x₁ nur solche Werthe suchen, die um A
vermehrt, eine durch a theilbare Summe geben. Wäre etwa m ein Factor von
a, so sind — wegen a prim gegen A — alle durch m theilbaren w
auszuschliessen, da sie blos solche x₁ erzeugen, welche Vielfache von m
sind.

8. Hätte im Nenner von III der Factor α vorzukommen (§. 1, 7), so ist
dieser Nenner nur jenen Factoren der Stammzahl gleichzusetzen, welche
durch α theilbar sind; die anderen Factoren von S sind nicht zu
gebrauchen.

9. Der Factor α muss aber im Nenner von III nicht vorkommen, wenn er
ein gemeinschaftlicher Theiler von a, b, c ist (§. 1, 1) oder wenn a
durch α² und b durch α theilbar sind (§. 1, 7) oder endlich, wenn die
Gleichung III behufs der Abkürzung des dortigen Bruches durch α² mit α
multiplicirt worden ist (§. 1. 9); in diesen drei Fällen muss der
Nenner in III kein Multiplum von α sein; er kann es aber sein. Ist S
durch α nicht theilbar, so kann kein Nenner den Factor α enthalten.

10. Zu jedem Werthe von q, welcher x in eine ganze Zahl verwandelt,
lässt sich ein zweiter Werth finden, der dasselbe bewirkt. Löst man
nämlich die Gleichung

x₁ = (dq+f)/(q²−g)

nach q auf, so ist

q = (1/(2x₁))(d±√(d²+4fx₁+4gx₁²)) ... λ.);
-/

example (d f g x₁ q : ℚ) (h : x₁ * (q ^ 2 - g) = d * q + f) :
    (2 * x₁ * q - d) ^ 2 = d ^ 2 + 4 * f * x₁ + 4 * g * x₁ ^ 2 := by
  linear_combination (4 * x₁) * h

/-
wäre für q = n,

x₁ = (dn+f)/(n²−g)

eine ganze Zahl, so setze man sie — hier diesen Scheinbruch —

Seite 19

in die Gleichung λ.) und es folgt:

q = [dn²−dg±(dn²+2fn+dg)]/[2(dn+f)].

somit

q₁ = n, q₂ = −(fn+dg)/(dn+f);
-/

example (d f g n : ℚ) (h : d * n + f ≠ 0) :
    (d * n ^ 2 - d * g + (d * n ^ 2 + 2 * f * n + d * g)) /
      (2 * (d * n + f)) = n := by
  apply (div_eq_iff (mul_ne_zero (by norm_num) h)).2
  ring

example (d f g n : ℚ) :
    (d * n ^ 2 - d * g - (d * n ^ 2 + 2 * f * n + d * g)) /
      (2 * (d * n + f)) = -(f * n + d * g) / (d * n + f) := by
  rw [div_mul_eq_div_div]
  ring

example (d f g n : ℚ) (h : d * n + f ≠ 0) :
    (d * n + f) * ((-(f * n + d * g) / (d * n + f)) ^ 2 - g) -
      d * (n ^ 2 - g) * (-(f * n + d * g) / (d * n + f)) -
      f * (n ^ 2 - g) = 0 := by
  ring_nf at h ⊢
  field_simp [h]
  ring

/-
diese beiden Substitutionen liefern für x₁ denselben ganzzahligen
Werth; doch können q₁ und q₂ einander auch gleich sein, wenn das
Radical in λ., Null wird.
Hat man für x einen ganzzahligen Werth ρ gefunden und setzt in III
−ρ für x, so dass

−aρ = A+(dq+f)/(q²−g),

so lassen sich aus dieser Gleichung häufig zwei rationale Zahlen für
q finden, welche wir mit q₃ und q₄ bezeichnen. Die vier Zahlen q₁, q₂,
q₃, q₄ geben numerisch gleiche Werthe für x und mögen äquivalente
Substitutionen heissen; mit veränderten Vorzeichen in die Gleichung III
eingesetzt, liefern sie oft neue Werthe für x.
-/

namespace Beispiel01

/-
11. Erstes Exempel.

x = (7p²+10p−3)/(3p²+2p−7) oder 3x = 7+(16p+40)/(3p²+2p−7),
-/

def x (p : ℚ) : ℚ := (7 * p ^ 2 + 10 * p - 3) / (3 * p ^ 2 + 2 * p - 7)

example (p : ℚ) :
    3 * (7 * p ^ 2 + 10 * p - 3) =
      7 * (3 * p ^ 2 + 2 * p - 7) + 16 * p + 40 := by ring

/-
für p = (q−1)/3 wird

III    3x = 7+(16q+104)/(q²−22)
-/

def x₁ (q : ℚ) : ℚ := (16 * q + 104) / (q ^ 2 - 22)

example (q : ℚ) (h : q ^ 2 - 22 ≠ 0) :
    3 * x ((q - 1) / 3) = 7 + x₁ q := by
  unfold x x₁
  have he : 3 * ((q - 1) / 3) ^ 2 + 2 * ((q - 1) / 3) - 7 =
      (q ^ 2 - 22) / 3 := by ring
  rw [he]
  ring_nf at h ⊢
  field_simp [h]
  ring

/-
die Stammzahl

S = (−22·16²+104²)/(4·2) = 648 oder S = 1·2³·3⁴;

somit v² = 22w²±(3, 6, 9, 12, 18, 24, 27, 36, 54, 72, 81, 108,
162, 216, 324, 648).
-/

#guard (-22 * 16^2 + 104^2 : ℚ) / (4*2) = 648

#guard (648 : ℕ) = 2^3 * 3^4

#guard ((List.range 649).filter fun d => d > 0 && 648 % d == 0 && d % 3 == 0) =
  [3,6,9,12,18,24,27,36,54,72,81,108,162,216,324,648]

/-
Hier wurde der kürzeren Rechnung wegen für p nicht (q−2)/6 sondern
(2q−2)/6 gesetzt und dadurch die Abkürzung des Bruches III durch 4
unter Einem vollzogen; und weil der Nenner

Seite 20

in III durch 3 theilbar sein muss, so wurden die durch 3 nicht
theilbaren Factoren der Stammzahl sogleich weggelassen; da ferner,
wegen x = (7+x₁)/3, die Zahl x₁ — d. i. der Bruch in III — kein
Vielfaches von 3 werden darf, so ist auch dem w kein solcher Werth zu
ertheilen; nun lasse man w in 1, 2, 4, 5, 7, ... übergehen und bemerke
jene Werthe von v², welche Quadratzahlen sind:

w   22w²    v²      q       x₁    x      p
1     22    16     +4      −28   −7      1
            25     −5        8    5     −2
            49     +7        8    5      2
2     88    64     ±4
            16     −2       −4    1     −1
           100     ±5
           196     ±7
           169   ±13/2       *
4    352     *
5    550     *
7   1078  1024   ±32/7       *

u. s. f.
-/

#guard ([1,2,4,5,7] : List ℚ).map (fun w => 22*w^2) = [22,88,352,550,1078]

#guard ([4,-5,7,-2] : List ℚ).map x₁ = [-28,8,8,-4]

#guard ([1,-2,2,-1] : List ℚ).map x = [-7,5,5,1]

#guard ([4,-5,7,-2] : List ℚ).map (fun q => (q-1)/3) = [1,-2,2,-1]

#guard ([4,5,7] : List ℚ).map (fun v => v^2) = [16,25,49]

#guard ([8,4,10,14,13] : List ℚ).map (fun v => v^2) = [64,16,100,196,169]

#guard (32 : ℕ)^2 = 1024

#guard ([13/2,-13/2,32/7,-32/7] : List ℚ).all fun q => ((7+x₁ q)/3).den != 1 || ([-7,5,1] : List ℚ).contains ((7+x₁ q)/3)

end Beispiel01

namespace Beispiel02

/-
12. Zweites Exempel.

x = (5p²+6p+27)/(3p²−2p+5) oder 3x = 5+(28p+56)/(3p²−2p+5)
-/

def x (p : ℚ) : ℚ := (5 * p ^ 2 + 6 * p + 27) / (3 * p ^ 2 - 2 * p + 5)

example (p : ℚ) :
    3 * (5 * p ^ 2 + 6 * p + 27) =
      5 * (3 * p ^ 2 - 2 * p + 5) + 28 * p + 56 := by ring

/-
für p = (q+1)/3 wird

3x−5 = x₁ = (28q+196)/(q²+14).
-/

def x₁ (q : ℚ) : ℚ := (28 * q + 196) / (q ^ 2 + 14)

example (q : ℚ) : 3 * x ((q + 1) / 3) - 5 = x₁ q := by
  unfold x x₁
  have he : 3 * ((q + 1) / 3) ^ 2 - 2 * ((q + 1) / 3) + 5 =
      (q ^ 2 + 14) / 3 := by ring
  rw [he]
  have h : q ^ 2 + 14 ≠ 0 := by positivity
  ring_nf at h ⊢
  field_simp [h]
  ring

/-
S = (14×28²+196²)/(28×14) = 126; hier wird die Stammzahl durch 28
dividirt, weil d = 28 und f = 196 durch 28 theilbar sind, und sie wird
ferner durch 14 dividirt, weil d und g den Factor 14 enthalten und in
f das Quadrat von 14 vorkommt. (§. 33).

Seite 21

Auch hier sind die durch 3 nicht theilbaren Factoren der Stammzahl
wegzulassen, und für w ist kein Vielfaches von 3 zu setzen. Es ist
sonach:

v² = (3, 6, 9, 18, 21, 42, 63, 126)−14w².
-/

#guard (14 * 28^2 + 196^2 : ℚ) / (28*14) = 126

#guard ((List.range 127).filter fun d => d > 0 && 126 % d == 0 && d % 3 == 0) =
  [3,6,9,18,21,42,63,126]

/-
w   44w²    v²     q     x₁    x    p
1     14     4    +2     14    *    *
                         *
            49    −7      0
2     56     *            *    *    *
-/

#guard ([1,2] : List ℕ).map (fun w => 14*w^2) = [14,56]

#guard ([2,-7] : List ℚ).map x₁ = [14,0]

#guard ([2,-7] : List ℚ).all fun q => ((5+x₁ q)/3).den != 1

/-
Vermutlicher Druckfehler: Der Spaltenkopf lautet 44w²; die vorstehende
Gleichung und die Einträge 14 und 56 entsprechen jedoch 14w².
Die Nachrechnung mit 14w² steht oben; hier wird die Abweichung des
Spaltenkopfes von den Einträgen geprüft.
-/

#guard ([1,2] : List ℕ).map (fun w => 44*w^2) ≠ [14,56]

#guard ([1,2] : List ℤ).all fun w =>
  ([-11,-10,-9,-8,-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8,9,10,11] : List ℤ).all
    fun v =>
      !([3,6,9,18,21,42,63,126] : List ℤ).contains (v^2+14*w^2) ||
        ((5+x₁ ((v : ℚ)/w))/3).den != 1

/-
Da w kleiner als 3 sein muss, so gibt es keine rationalen Zahlen für
q und p, welche x zu einer ganzen Zahl machen.
-/

#guard (14 * 3^2 : ℕ) = 126

example (p : ℚ) : ¬ ∃ z : ℤ, x p = z := by
  rintro ⟨z, hz⟩
  let q : ℚ := 3 * p - 1
  let v : ℤ := q.num
  let w : ℤ := q.den
  let N : ℤ := v ^ 2 + 14 * w ^ 2
  let k : ℤ := 3 * z - 5
  have hw : 0 < w := by dsimp [w]; exact_mod_cast q.den_pos
  have hwq : (w : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hw)
  have hq : (v : ℚ) / w = q := by simpa [v, w] using Rat.num_div_den q
  have hp : p = ((v : ℚ) / w + 1) / 3 := by rw [hq]; dsimp [q]; ring
  have hvw : IsCoprime v w := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa [v, w] using q.reduced
  have hNw : IsCoprime N w := by
    obtain ⟨s, t, h⟩ := hvw
    refine ⟨s ^ 2, -14 * w * s ^ 2 + 2 * s * t * v + t ^ 2 * w, ?_⟩
    dsimp [N]
    calc
      _ = (s * v + t * w) ^ 2 := by ring
      _ = 1 := by rw [h]; norm_num
  have hxn : N * k = w * (28 * v + 196 * w) := by
    have hd : 3 * p ^ 2 - 2 * p + 5 ≠ 0 := by nlinarith [sq_nonneg (p - 1 / 3)]
    have h := (div_eq_iff hd).mp hz
    rw [hp] at h
    field_simp [hwq] at h
    have he : ((v : ℚ) ^ 2 + 14 * w ^ 2) * (3 * z - 5) = w * (28 * v + 196 * w) := by
      linear_combination -h
    exact_mod_cast he
  obtain ⟨t, ht⟩ : N ∣ 28 * v + 196 * w := hNw.dvd_of_dvd_mul_left ⟨k, hxn.symm⟩
  let l : ℤ := v * t - 28
  have hln : N * l = 196 * v * w - 392 * w ^ 2 := by
    dsimp [l, N] at *
    linear_combination -v * ht
  have hfactor (ν d f g K : ℤ) (hν : Prime ν) (hg : ¬ ν ∣ g)
      (hn : N = v ^ 2 - ν * g * w ^ 2)
      (hK : N * K = ν * d * v * w + ν ^ 2 * f * w ^ 2) : ν ∣ K := by
    by_cases hv : ν ∣ v
    · have hnw : ¬ ν ∣ w := fun h => hν.not_isUnit (hvw.isUnit_of_dvd' hv h)
      obtain ⟨u, hu⟩ := hv
      have hD : ¬ ν ∣ ν * u ^ 2 - g * w ^ 2 := by
        intro h
        have hgw : ν ∣ g * w ^ 2 := by
          convert dvd_sub (dvd_mul_right ν (u ^ 2)) h using 1
          ring
        rcases hν.dvd_mul.mp hgw with h | h
        · exact hg h
        · exact hnw (hν.dvd_of_dvd_pow h)
      have hK' : (ν * u ^ 2 - g * w ^ 2) * K = ν * (d * u * w + f * w ^ 2) := by
        apply mul_left_cancel₀ hν.ne_zero
        rw [hn, hu] at hK
        linear_combination hK
      exact (hν.coprime_iff_not_dvd.mpr hD).dvd_of_dvd_mul_left ⟨d * u * w + f * w ^ 2, hK'⟩
    · have hD : ¬ ν ∣ N := by
        intro h
        apply hv
        apply hν.dvd_of_dvd_pow (n := 2)
        rw [hn] at h
        convert dvd_add h (dvd_mul_of_dvd_left (dvd_mul_right ν g) (w ^ 2)) using 1
        ring
      exact (hν.coprime_iff_not_dvd.mpr hD).dvd_of_dvd_mul_left
        ⟨d * v * w + ν * f * w ^ 2, by nlinarith [hK]⟩
  have hk2 : (2 : ℤ) ∣ k := hfactor 2 14 49 (-7) k (by norm_num) (by norm_num)
    (by dsimp [N]; ring) (by linear_combination hxn)
  have hk7 : (7 : ℤ) ∣ k := hfactor 7 4 4 (-2) k (by norm_num) (by norm_num)
    (by dsimp [N]; ring) (by linear_combination hxn)
  have hl2 : (2 : ℤ) ∣ l := hfactor 2 98 (-98) (-7) l (by norm_num) (by norm_num)
    (by dsimp [N]; ring) (by linear_combination hln)
  have hl7 : (7 : ℤ) ∣ l := hfactor 7 28 (-8) (-2) l (by norm_num) (by norm_num)
    (by dsimp [N]; ring) (by linear_combination hln)
  obtain ⟨A, hA⟩ : (14 : ℤ) ∣ k := (show IsCoprime (2 : ℤ) 7 by norm_num).mul_dvd hk2 hk7
  obtain ⟨B, hB⟩ : (14 : ℤ) ∣ l := (show IsCoprime (2 : ℤ) 7 by norm_num).mul_dvd hl2 hl7
  have h126 : N * (7 * A - B) = 126 * w ^ 2 := by
    rw [hA] at hxn
    rw [hB] at hln
    have h : 14 * (N * (7 * A - B) - 126 * w ^ 2) = 0 := by
      linear_combination 7 * hxn - hln
    nlinarith [h]
  have hd126 : N ∣ 126 := (hNw.pow_right (n := 2)).dvd_of_dvd_mul_right ⟨7 * A - B, h126.symm⟩
  have h3 : (N : ZMod 3) = 0 := by
    have h := congrArg (fun a : ℤ => (a : ZMod 3)) hxn
    dsimp [N, k] at h
    push_cast at h
    have hs : ∀ v w z : ZMod 3,
        (v ^ 2 + 14 * w ^ 2) * (3 * z - 5) = w * (28 * v + 196 * w) →
        v ^ 2 + 14 * w ^ 2 = 0 := by decide
    simpa [N] using hs v w z h
  have hd3 : (3 : ℤ) ∣ N := (ZMod.intCast_zmod_eq_zero_iff_dvd N 3).mp h3
  have hNbound : N ≤ 126 := Int.le_of_dvd (by norm_num) hd126
  have hwb : w ≤ 3 := by dsimp [N] at hNbound; nlinarith [sq_nonneg v, sq_nonneg (w - 4)]
  have hw3 : w < 3 := by
    by_contra h
    have hw' : w = 3 := by omega
    have hv : v = 0 := by dsimp [N] at hNbound; rw [hw'] at hNbound; nlinarith [sq_nonneg v]
    have hcop := Int.isCoprime_iff_gcd_eq_one.mp hvw
    norm_num [hv, hw'] at hcop
  have hvb : -11 ≤ v ∧ v ≤ 11 := by
    dsimp [N] at hNbound
    constructor <;> nlinarith [sq_nonneg w, sq_nonneg (v - 12), sq_nonneg (v + 12)]
  obtain ⟨hvlo, hvhi⟩ := hvb
  dsimp [N, k] at hd126 hd3 hxn
  interval_cases w <;> interval_cases v
  all_goals norm_num at hd126
  all_goals norm_num at hd3
  all_goals norm_num at hxn
  all_goals omega

end Beispiel02

/-
Auf diese Weise lassen sich für ein negatives alle und für ein
positives g beliebig viele ganzzahlige Werthe von x finden, falls
solche existiren, doch wird die Rechnung lästig, ja selbst unausführbar,
wenn w grössere Zahlenwerthe erhalten muss.
-/

end Kunerth1877.Paragraf03
