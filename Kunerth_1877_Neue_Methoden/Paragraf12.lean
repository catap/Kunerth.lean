/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf12

/-
Seite 44

§. 12.
Auflösung mittelst Congruenzen.

1. Jede Gleichung von der Form ay² = bx²+c kann so
transformirt werden, dass je zwei der Zahlen a, b, c relativ einfach
gegen einander sind; dabei sollen a und b von Eins verschieden
sein. Hat obige Gleichung diese Eigenschaft, so bringe man die
Congruenzen
ay² ≡ c (mod. b) und bx² ≡ −c (mod. a)
-/

example (a b c x y : ℤ) (h : a * y ^ 2 = b * x ^ 2 + c) :
    Int.ModEq b (a * y ^ 2) c ∧ Int.ModEq a (b * x ^ 2) (-c) := by
  constructor
  · exact Int.modEq_iff_dvd.mpr ⟨-x ^ 2, by linarith⟩
  · exact Int.modEq_iff_dvd.mpr ⟨-y ^ 2, by linarith⟩

/-
auf die Form
y² ≡ m (mod. b) und x² ≡ n (mod. a)    (μ)
und setze
y² = bu+m und x² = av+n
-/

example (a b c m y : ℤ) (hab : IsCoprime a b)
    (hm : Int.ModEq b (a * m) c) (hy : Int.ModEq b (a * y ^ 2) c) :
    Int.ModEq b (y ^ 2) m := by
  apply Int.modEq_iff_dvd.mpr
  apply hab.symm.dvd_of_dvd_mul_left
  convert dvd_sub (Int.modEq_iff_dvd.mp hy) (Int.modEq_iff_dvd.mp hm) using 1
  ring

example (a b c n x : ℤ) (hab : IsCoprime a b)
    (hn : Int.ModEq a (b * n) (-c)) (hx : Int.ModEq a (b * x ^ 2) (-c)) :
    Int.ModEq a (x ^ 2) n := by
  apply Int.modEq_iff_dvd.mpr
  apply hab.dvd_of_dvd_mul_left
  convert dvd_sub (Int.modEq_iff_dvd.mp hx) (Int.modEq_iff_dvd.mp hn) using 1
  ring

/-
Seite 45

in die erste Gleichung; da folgt
abu+am = abv+bn+c
und
u−v = (−am+bn+c)/(ab) = d
eine ganze Zahl, weil u−v eine solche ist.
-/

example (a b c m n u v : ℚ) :
    a * (b * u + m) - b * (a * v + n) - c =
      a * b * (u - v) + a * m - b * n - c := by ring

example (a b c m n u v : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a * b * u + a * m = a * b * v + b * n + c) :
    u - v = (-a * m + b * n + c) / (a * b) := by
  apply (eq_div_iff (mul_ne_zero ha hb)).mpr
  linarith

/-
Löst man nun die zwei Congruenzen in (μ) auf, so sind jene
Werthe von y und x, für welche u−v = d ist, Wurzeln der obigen
Gleichung und aus einem Paare derselben lassen sich mit
Hilfe der p-Function andere Werthe finden.
Diese Methode empfiehlt sich besonders dort, wo die
Coëfficienten grosse Zahlen sind, mit welchen die p-Function schwer
zu finden ist.
-/

example (a b c m n u v x y : ℤ)
    (hy : y ^ 2 = b * u + m) (hx : x ^ 2 = a * v + n)
    (h : a * b * (u - v) = -a * m + b * n + c) :
    a * y ^ 2 = b * x ^ 2 + c := by
  rw [hy, hx]
  linear_combination h

namespace Beispiel01

/-
2. Erstes Exempel.
11y² = 13x²+71    I
11y² ≡ 71 (mod. 13) und 13x² ≡ −71 (mod. 11)
daraus
y² ≡ 10 (mod. 13) und x² ≡ 3 (mod. 11),    II
somit
y² = 13u+10 und x² = 11v+3;
-/

#guard ((11 * 10 - 71 : ℤ) % 13 == 0) && ((13 * 3 + 71 : ℤ) % 11 == 0)

/-
in I gesetzt, folgt u = v. Aus den Congruenzen in II findet man
für u = v = 2 y = 6, x = 5; Wurzeln von I.
-/

example (u v : ℚ) : 11 * (13 * u + 10) - 13 * (11 * v + 3) - 71 = 143 * (u - v) := by
  ring

#guard (6 : ℤ) ^ 2 = 13 * 2 + 10

#guard (5 : ℤ) ^ 2 = 11 * 2 + 3

#guard (11 * 6 ^ 2 : ℤ) = 13 * 5 ^ 2 + 71

/-
Multiplicirt man
I mit 11 und setzt 11y = y₁, so ist
y₁² = 143x²+781    III
und da x = 5, y₁ = 66, so folgt
x = 5−22(6p−65)/(p²−143)
wobei
y₁ = p(x−5)+66
ist; S = 4.11.13.113; hiermit findet man
-/

example (x y : ℚ) : (11 * y) ^ 2 - 143 * x ^ 2 - 781 =
    11 * (11 * y ^ 2 - 13 * x ^ 2 - 71) := by ring

#guard (66 : ℤ) ^ 2 = 143 * 5 ^ 2 + 781

def x (p : ℚ) : ℚ := 5 - 22 * (6 * p - 65) / (p ^ 2 - 143)

def y₁ (p : ℚ) : ℚ := p * (x p - 5) + 66

#guard (4 * 11 * 13 * 113 : ℤ) = 64636

/-
p  =    11          12           13
x  = 6, −126    −149, 3019     −6, 126
y₁ = 77, 1507   −1782, 36102
y  = 7, 137     −162, 3282
-/

#guard ([(11, 6, 77, 7), (-11, -126, 1507, 137), (12, -149, -1782, -162),
    (-12, 3019, 36102, 3282)] : List (ℚ × ℚ × ℚ × ℚ)).all
  fun (p, u, v, y) => x p == u && (y₁ p) ^ 2 == v ^ 2 && v == 11 * y &&
    11 * y ^ 2 == 13 * u ^ 2 + 71

#guard x 13 = -6

#guard x (-13) = 126

/-
Seite 46

Auflösung mit Benützung der Methode von Leslie.

Man setze die den Congruenzen in II entsprechenden
Binome
y = 6+13n, x = 5+11m,
in denen m und n unbekannte Zahlen bezeichnen, in die
Gleichung I, so kommt
13n²+12n = 11m²+10m
oder
n(13n+12) = m(11m+10);
-/

example (m n : ℚ) :
    11 * (6 + 13 * n) ^ 2 - 13 * (5 + 11 * m) ^ 2 - 71 =
      143 * (13 * n ^ 2 + 12 * n - (11 * m ^ 2 + 10 * m)) := by ring

example (m n : ℚ) : 13 * n ^ 2 + 12 * n - (11 * m ^ 2 + 10 * m) =
    n * (13 * n + 12) - m * (11 * m + 10) := by ring

/-
setzt man nun
13n+12 = km, 11m+10 = kn
und eliminirt aus diesen Gleichungen m, so folgt
n = (10k+132)/(k²−143), S = 22×71
-/

example (m n k : ℚ) (h₁ : 13 * n + 12 = k * m) (h₂ : 11 * m + 10 = k * n) :
    n * (k ^ 2 - 143) = 10 * k + 132 := by
  linear_combination -11 * h₁ - k * h₂

def n (k : ℚ) : ℚ := (10 * k + 132) / (k ^ 2 - 143)

#guard (22 * 71 : ℤ) = 1562

/-
und gibt:
k =   1      11         12
n =  −1    −11, −1    252, 12
y =   7    137,  7   3282, 162
x =   6    126,  6   3019, 149
wie oben.
-/

#guard ([(1, -1, 7, 6), (11, -11, 137, 126), (-11, -1, 7, 6),
    (12, 252, 3282, 3019), (-12, 12, 162, 149)] : List (ℚ × ℚ × ℚ × ℚ)).all
  fun (k, u, y, x) => n k == u && (6 + 13 * u) ^ 2 == y ^ 2 &&
    (k * u - 5) ^ 2 == x ^ 2 && 11 * y ^ 2 == 13 * x ^ 2 + 71

end Beispiel01

namespace Beispiel02

/-
3. Zweites Exempel.
182y² = 165x²+857    I
182y² ≡ 857 (mod. 165), 165x² ≡ −857 (mod. 182)
oder
y² ≡ 31 (mod. 165), x² ≡ 29 (mod. 182)
somit
y² = 165u+31, x² = 182v+29
-/

#guard ((182 * 31 - 857 : ℤ) % 165 == 0) && ((165 * 29 + 857 : ℤ) % 182 == 0)

/-
in I gesetzt, folgt u = v. Löst man die zwei letzten Congruenzen
auf, so wird für u = v = 10
y = 41, x = 43.
Multiplicirt man die Gleichung I mit 182 und setzt 182y = y₁
so kommt
-/

example (u v : ℚ) :
    182 * (165 * u + 31) - 165 * (182 * v + 29) - 857 = 30030 * (u - v) := by ring

#guard (41 : ℤ) ^ 2 = 165 * 10 + 31

#guard (43 : ℤ) ^ 2 = 182 * 10 + 29

#guard (182 * 41 ^ 2 : ℤ) = 165 * 43 ^ 2 + 857

/-
Seite 47

y₁² = 30030x²+155974    II
und weil x = 43, y₁ = 7462 Wurzeln dieser Gleichung sind,
so ist
x = 43−2(7462p−30030×43)/(p²−30030)
oder
x = 43−364(41p−165×43)/(p²−165×182)    III
S = 165×182×857;
-/

example (x y : ℚ) : (182 * y) ^ 2 - 30030 * x ^ 2 - 155974 =
    182 * (182 * y ^ 2 - 165 * x ^ 2 - 857) := by ring

#guard (182 * 41 : ℤ) = 7462

def x (p : ℚ) : ℚ := 43 - 364 * (41 * p - 165 * 43) / (p ^ 2 - 165 * 182)

example (p : ℚ) : 43 - 2 * (7462 * p - 30030 * 43) / (p ^ 2 - 30030) = x p := by
  unfold x
  ring

/-
ein Factor von S ist 29995, und um 30030 vermehrt, kommt
245² als Summe; für p = −245 wird x = 251, und weil hier
y₁ = p(x−43)+7462,    (ρ)
so ist
y₁ = −43498 und y = 239.
-/

#guard (165 * 182 * 857 : ℤ) % 29995 = 0

#guard (29995 + 30030 : ℤ) = 245 ^ 2

#guard x (-245) = 251

def y₁ (p : ℚ) : ℚ := p * (x p - 43) + 7462

#guard y₁ (-245) = -43498

#guard ((-43498 / 182 : ℚ)) ^ 2 = 239 ^ 2

/-
Um fernere Wurzeln der Gleichung II zu finden, bestimme
man die äquivalenten Substitutionen für x = ±251; diese sind
p = −245, 693/4, −858/7, 520/3;
-/

#guard ([-245, 693/4, -858/7, 520/3] : List ℚ).all fun p => (x p) ^ 2 == 251 ^ 2

/-
für p = −693/4 kommt x₃ = −357925 und aus (ρ) y₁ = 62025418
somit y = 340799. Ferner ergibt sich für
p = (−y₂+y₃)/(+x₂−x₃) = 4159/24 ... x₄ = 2087861
-/

#guard x (-693 / 4) = -357925

#guard y₁ (-693 / 4) = 62025418

#guard (62025418 / 182 : ℚ) = 340799

#guard ((-(-43498) + 62025418) / (251 - (-357925)) : ℚ) = 4159 / 24

#guard (x (4159 / 24)) ^ 2 = 2087861 ^ 2

#guard (182 * 340799 ^ 2 : ℤ) = 165 * 357925 ^ 2 + 857

end Beispiel02

namespace Beispiel03

/-
4. Drittes Exempel.
15y² = 91x²+71    I
15y² ≡ 71 (mod. 91), 91x² ≡ −71 (mod. 15)
oder
y² ≡ 29 (mod. 91) und x² ≡ 4 (mod. 15)
somit
y² = 91u+29, x² = 15v+4
-/

#guard ((15 * 29 - 71 : ℤ) % 91 == 0) && ((91 * 4 + 71 : ℤ) % 15 == 0)

/-
in I gesetzt, folgt u = v; für u = v = 52 wird x = 28, y = 69:
multiplicirt man die Gleichung I mit 15 und setzt 15y = y₁, so
wird
-/

example (u v : ℚ) : 15 * (91 * u + 29) - 91 * (15 * v + 4) - 71 = 1365 * (u - v) := by ring

#guard (69 : ℤ) ^ 2 = 91 * 52 + 29

#guard (28 : ℤ) ^ 2 = 15 * 52 + 4

#guard (15 * 69 ^ 2 : ℤ) = 91 * 28 ^ 2 + 71

/-
Seite 48

y₁² = 1365x²+1065    II
und da x = 28, y₁ = 1035 ist, so wird
x = 28−30(69p−2548)/(p²−1365),
-/

example (x y : ℚ) : (15 * y) ^ 2 - 1365 * x ^ 2 - 1065 =
    15 * (15 * y ^ 2 - 91 * x ^ 2 - 71) := by ring

#guard (15 * 69 : ℤ) = 1035

def x (p : ℚ) : ℚ := 28 - 30 * (69 * p - 2548) / (p ^ 2 - 1365)

/-
S = 2.3.5.7.13.71 liefert kein ganzzahliges x; somit ist die
Gleichung
v²−1365w² = n
zu bilden, wo n ein Factor von S sein muss; da findet sich
v² = 1365w²−35.... = d²w²+(1365−d²)w²−35
hieraus
d² = 1365−35γ²;
-/

#guard (2 * 3 * 5 * 7 * 13 * 71 : ℤ) = 193830

example (w d : ℚ) : d ^ 2 * w ^ 2 + (1365 - d ^ 2) * w ^ 2 - 35 = 1365 * w ^ 2 - 35 := by ring

/-
für γ = 2 wird d = 35, also
v² = (35w)²+35(4w²−1)
-/

#guard (1365 - 35 * 2 ^ 2 : ℤ) = 35 ^ 2

example (w : ℚ) : 1365 * w ^ 2 - 35 = (35 * w) ^ 2 + 35 * (4 * w ^ 2 - 1) := by ring

/-
und
2w = 1−2(35q−1365)/(q²−1365)
oder
2w = 1−70(q−39)/(q²−1365), S₁ = 8.3.5.7.13
-/

def w (q : ℚ) : ℚ := (1 - 70 * (q - 39) / (q ^ 2 - 1365)) / 2

example (q : ℚ) : 1 - 2 * (35 * q - 1365) / (q ^ 2 - 1365) = 2 * w q := by
  unfold w
  ring

#guard (8 * 3 * 5 * 7 * 13 : ℤ) = 10920

/-
und weil
1365+4 = 37²
ist, so ist q = 37, w = 18, v = 665; für p = 665/18 wird x = 352
und aus
y₁ = 1035+p(x−28)
folgt
y₁ = 13005 und y = 867;
hier ist u = v = 8260.
-/

#guard (1365 + 4 : ℤ) = 37 ^ 2

#guard w 37 = 18

#guard (665 : ℤ) ^ 2 = 1365 * 18 ^ 2 - 35

#guard x (665 / 18) = 352

def y₁ (p : ℚ) : ℚ := 1035 + p * (x p - 28)

#guard y₁ (665 / 18) = 13005

#guard (13005 / 15 : ℚ) = 867

#guard (867 : ℤ) ^ 2 = 91 * 8260 + 29

#guard (352 : ℤ) ^ 2 = 15 * 8260 + 4

/-
Für p = −665/18 kommt x₃ = −1415528, y₁ = 52297965
und y = 3486531 u. s. f.
-/

#guard x (-665 / 18) = -1415528

#guard y₁ (-665 / 18) = 52297965

#guard (52297965 / 15 : ℚ) = 3486531

/-
5. Auflösung derselben Gleichung mittelst der
z-Function.
Setzt man
y₁ = 1365z+r
-/

/-
Seite 49

in die Gleichung II, so wird
x² = 1365z²+2rz+(r²−1065)/1365;
für r = 330 wird der letzte Bruch = 79 und
x² = 1365z²+660z+79    III
für z = −1 wird x = 28, y₁ = 1035. Um fernere Werthe zu
finden, bilde man die p-Function:
z = −1−2(28p+1035)/(p²−1365),
S = 30.71 gibt nichts.
-/

example (z r : ℚ) : ((1365 * z + r) ^ 2 - 1065) / 1365 =
    1365 * z ^ 2 + 2 * r * z + (r ^ 2 - 1065) / 1365 := by ring

#guard ((330 ^ 2 - 1065) / 1365 : ℚ) = 79

#guard (28 : ℤ) ^ 2 = 1365 * (-1) ^ 2 + 660 * (-1) + 79

#guard (1365 * (-1) + 330 : ℤ) ^ 2 = 1035 ^ 2

def z (p : ℚ) : ℚ := -1 - 2 * (28 * p + 1035) / (p ^ 2 - 1365)

#guard (30 * 71 : ℤ) = 2130

/-
Aus der Beschaffenheit der Gleichung III ist zu ersehen,
dass x auch dann eine ganze Zahl werden kann, wenn z einen
Bruch bezeichnet, dessen Nenner ein Factor von 1365 ist.
Um diese Brüche zu finden, bestimme man jene Factoren
von 1365, welche dem Binome v²−1365w² gleichgesetzt, eine in
ganzen Zahlen mögliche Gleichung geben. Diese Factoren sind:
+1, −35, +39, −1365.
-/

#guard ([1, -35, 39, -1365] : List ℤ).all fun d => 1365 % d == 0

example (n : ℤ) (hn : n ∣ 1365)
    (h : ∃ v w : ℤ, v ^ 2 = 1365 * w ^ 2 + n) :
    n ∈ ([1, -35, 39, -1365] : List ℤ) := by
  have hnat : n.natAbs ∈
      ({1, 3, 5, 7, 13, 15, 21, 35, 39, 65, 91, 105, 195, 273, 455, 1365} : Finset ℕ) := by
    rw [← show (1365 : ℕ).divisors =
      {1, 3, 5, 7, 13, 15, 21, 35, 39, 65, 91, 105, 195, 273, 455, 1365} by native_decide]
    exact Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hn, by decide⟩
  have hsign : n = (n.natAbs : ℤ) ∨ n = -(n.natAbs : ℤ) := by
    rcases le_total 0 n with hp | hp
    · left; simp [abs_of_nonneg hp]
    · right; simp [abs_of_nonpos hp]
  have hcases : n ∈ ([1, -1, 3, -3, 5, -5, 7, -7, 13, -13, 15, -15,
      21, -21, 35, -35, 39, -39, 65, -65, 91, -91, 105, -105,
      195, -195, 273, -273, 455, -455, 1365, -1365] : List ℤ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnat
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    omega
  have residues : ∀ k ∈ ([1, -1, 3, -3, 5, -5, 7, -7, 13, -13, 15, -15,
      21, -21, 35, -35, 39, -39, 65, -65, 91, -91, 105, -105,
      195, -195, 273, -273, 455, -455, 1365, -1365] : List ℤ),
      (∃ v w : ZMod 9, v ^ 2 - 1365 * w ^ 2 = (k : ZMod 9)) →
      (∃ v w : ZMod 25, v ^ 2 - 1365 * w ^ 2 = (k : ZMod 25)) →
      (∃ v w : ZMod 49, v ^ 2 - 1365 * w ^ 2 = (k : ZMod 49)) →
      k ∈ ([1, -35, 39, -1365] : List ℤ) := by native_decide
  obtain ⟨v, w, hvw⟩ := h
  have heq : v ^ 2 - 1365 * w ^ 2 = n := by linarith
  apply residues n hcases
  · refine ⟨v, w, ?_⟩
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod 9)) heq
  · refine ⟨v, w, ?_⟩
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod 25)) heq
  · refine ⟨v, w, ?_⟩
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod 49)) heq

/-
a) v² = 1365w²+1, w = −2p₁/(p₁²−1365), v = p₁w+1,
S = 2.3.5.7.13 liefert nichts. Nun folgt aus S:
v₁² = 1365w₁²−35 = (35w₁)²+35(4w₁²−1)
hieraus
2w₁ = 1−2(35q−1365)/(q²−1365)
oder
2w₁ = 1−70(q−39)/(q²−1365), S₁ = 8.3.5.7.13;
1365+4 = 37² = q²
und für q = 37 wird w₁ = 18, v₁ = 665 und für p₁ = 665/18 wird
w = 684 und v = 25271; endlich für p = 25271/684 folgt aus der
p-Function für z:
z = −481537 und x = 17790812
-/

#guard (-2 * (665/18) / ((665/18)^2 - 1365) : ℚ) = 684

#guard ((665/18) * 684 + 1 : ℚ) = 25271

#guard (25271 : ℤ) ^ 2 = 1365 * 684 ^ 2 + 1

/-
Zuordnung: Für das angegebene p = 25271/684 ergibt die Formel
z = −1936442305. Die folgende Nachrechnung prüft die Abweichung
vom angegebenen Werth −481537.
-/

#guard z (25271 / 684) ≠ -481537

/-
Vermutlicher Druckfehler: Gemeint ist wohl p = −25271/684.
Die folgende Nachrechnung prüft diese vermutete Berichtigung.
-/

#guard z (-25271 / 684) = -481537

#guard (17790812 : ℤ) ^ 2 = 1365 * (-481537) ^ 2 + 660 * (-481537) + 79

/-
Seite 50

und
y₁ = −657297675, y = −43819845,
-/

#guard (1365 * (-481537) + 330 : ℤ) = -657297675

#guard (-657297675 / 15 : ℚ) = -43819845

#guard (15 * (-43819845) ^ 2 : ℤ) = 91 * 17790812 ^ 2 + 71

/-
b) v² = 1365w²−35
hat nach a) w = 18, v = 665 und für
p = ∓665/18 kommt z = +65/7 und 268193/7
daher x = 352 respective 1415528.
-/

#guard z (-665 / 18) = 65 / 7

#guard z (665 / 18) = 268193 / 7

#guard ([(65/7, 352), (268193/7, 1415528)] : List (ℚ × ℚ)).all
  fun (z, x) => x ^ 2 == 1365 * z ^ 2 + 660 * z + 79

/-
c) v² = 1365w²+39 = (39w)²−39(4w²−1)
daraus
2w = 1−2(39q−1365)/(q²−1365), S₁ = 8.3.7.5.13;
für q = 37 wird w = 19, v = 702 also p = 702/19; es folgen für
x dieselben Werthe wie in b).
-/

example (w : ℚ) : 1365 * w ^ 2 + 39 = (39 * w) ^ 2 - 39 * (4 * w ^ 2 - 1) := by ring

/-
Zuordnung: Für q = 37 liefert die angegebene Formel w = −19.
Kunerth verwendet anschließend w = 19 und v = 702. Hier werden
die Quadrate verglichen; danach wird das angegebene positive
Wurzelpaar geprüft.
-/

#guard ((1 - 2 * (39 * 37 - 1365) / (37 ^ 2 - 1365)) / 2 : ℚ) ^ 2 = 19 ^ 2

#guard (702 : ℤ) ^ 2 = 1365 * 19 ^ 2 + 39

#guard ([702/19, -702/19] : List ℚ).all fun p =>
  let t := z p
  (1365 * t ^ 2 + 660 * t + 79 == 352 ^ 2) ||
    (1365 * t ^ 2 + 660 * t + 79 == 1415528 ^ 2)

/-
d) v² = 1365w²−1365... = 1365(w²−1),
für w = 1, ist v = 0 und für p = 0 wird z = 47/91 und x = 28,
welchen Werth man auch für p = ∞ und z = −1 erhalten hätte.
-/

example (w : ℚ) : 1365 * w ^ 2 - 1365 = 1365 * (w ^ 2 - 1) := by ring

#guard (0 : ℤ) ^ 2 = 1365 * (1 ^ 2 - 1)

#guard z 0 = 47 / 91

#guard (28 : ℚ) ^ 2 = 1365 * (47/91) ^ 2 + 660 * (47/91) + 79

/-
6. Es lassen sich somit die Werthe von x auch aus der
p-Function für z derartig berechnen, dass die Werthe von z
Brüche mit solchen Nennern werden, welche Factoren von a
sind; der Zahl a sind demnach die Constanten in den derivirten
Gleichungen zu entnehmen.
-/

#guard (1365 : ℤ) % 7 = 0

#guard (1365 : ℤ) % 91 = 0

end Beispiel03

end Kunerth1877.Paragraf12
