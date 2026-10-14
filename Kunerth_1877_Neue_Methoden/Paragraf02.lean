/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf02

/-
Seite 11

§. 2.

1. Ist die Gleichung III in ihrer einfachsten Form dargestellt, so
sind drei Fälle zu unterscheiden:
Ist g eine positive Quadratzahl, so ist zur Auffindung der ganzzahligen
Werthe von x und y die Gleichung I eigentlich

Seite 12

nicht nöthig; denn alsdann lässt sich eine der Unbekannten unmittelbar
als rationale Function der andern, und wenn dies nicht angeht, als
Bruchfunction von p mit linearem Nenner ausdrücken. Will man jedoch aus
der Gleichung III die ganzzahligen Werthe von x finden, so zerlege man
den Bruch daselbst in zwei Partialbrüche, setze q = v/w und ermittle
jene Werthe von v und w, welche x zu einer ganzen Zahl machen. In
diesem Falle, wie auch dann, wenn eine Bruchfunction von p mit linearem
Nenner angewendet wird, ist die Anzahl der ganzzahligen Werthe von x
eine begrenzte.

2. Zur Begründung dieses Verfahrens dienen folgende Betrachtungen:
Es sei

x₁ = (dp+f)/(p²−h²) = (1/(2h))[(dh+f)/(p−h)+(dh−f)/(p+h)]
-/

example (d f h p : ℚ) (hh : h ≠ 0)
    (h₁ : p - h ≠ 0) (h₂ : p + h ≠ 0) :
    (d * p + f) / (p ^ 2 - h ^ 2) =
      1 / (2 * h) * ((d * h + f) / (p - h) +
        (d * h - f) / (p + h)) := by
  rw [show p ^ 2 - h ^ 2 = (p - h) * (p + h) by ring]
  field_simp
  ring

/-
und f prim gegen h (§. 1, 10), so wird für

p = v/w,    x = (w/(2h))[(dh+f)/(v−hw)+(dh−f)/(v+hw)].
-/

example (d f h v w : ℚ) (hw : w ≠ 0) (hh : h ≠ 0)
    (h₁ : v - h * w ≠ 0) (h₂ : v + h * w ≠ 0) :
    (d * (v / w) + f) / ((v / w) ^ 2 - h ^ 2) =
      w / (2 * h) * ((d * h + f) / (v - h * w) +
        (d * h - f) / (v + h * w)) := by
  have hd : v ^ 2 - h ^ 2 * w ^ 2 ≠ 0 := by
    rw [show v ^ 2 - h ^ 2 * w ^ 2 = (v - h * w) * (v + h * w) by ring]
    exact mul_ne_zero h₁ h₂
  have he : (v / w) ^ 2 - h ^ 2 = (v ^ 2 - h ^ 2 * w ^ 2) / w ^ 2 := by
    field_simp
  rw [he]
  field_simp (disch := grind)
  ring

/-
Da v und w relative Primzahlen sind, so können die Nenner der
eingeklammerten Brüche nach Einsetzung der speciellen Werthe für v und
w und vollzogener Abkürzung nur dann einander gleich werden, wenn beide
in die Zahl 2 übergehen. Würde nämlich

v−hw = mk und v+hw = nk,

so folgt

v = (n+m)k/2 und w = (n−m)k/(2h);
-/

example (v w h m n k : ℚ) (hh : h ≠ 0)
    (h₁ : v - h * w = m * k) (h₂ : v + h * w = n * k) :
    v = (n + m) * k / 2 ∧ w = (n - m) * k / (2 * h) := by
  constructor
  · linarith
  · apply (eq_div_iff (mul_ne_zero (by norm_num) hh)).2
    linarith

/-
wegen w prim gegen v, kann k nur einen der drei Werthe 2, h, 2h
annehmen. Dem Falle k = 2 steht nichts entgegen, doch ist er
überflüssig, weil für k = 1 derselbe Werth für x erhalten wird.
Für k = h müsste v = hr sein, während f und w prim gegen h wären;
dann würde

x = (w/h²)((dhr+fw)/(r²−w²)),

Seite 13

welcher Ausdruck offenbar in eine ganze Zahl nicht übergehen kann.
Ebenso lässt sich zeigen, dass k den Werth 2h nicht erhalten darf.
Es können somit die Partialbrüche auch nach vollzogener Reduction
keine gleichen Nenner haben, mit Ausnahme des entbehrlichen Nenners 2.
-/

example (d f h v w x : ℤ) (k : ℕ) (_hh : 0 < h)
    (_hw : w ≠ 0) (_hden : v ^ 2 - h ^ 2 * w ^ 2 ≠ 0)
    (hfh : IsCoprime f h) (hvw : IsCoprime v w)
    (hx : (v ^ 2 - h ^ 2 * w ^ 2) * x = w * (d * v + f * w))
    (_hk : 0 < k) (hk₁ : (k : ℤ) ∣ v - h * w)
    (hk₂ : (k : ℤ) ∣ v + h * w) : k = 1 ∨ k = 2 := by
  have hd : v ∣ w ^ 2 * (f + h ^ 2 * x) := by
    refine ⟨v * x - d * w, ?_⟩
    linear_combination -hx
  have hd' : v ∣ f + h ^ 2 * x :=
    (hvw.pow_right (n := 2)).dvd_of_dvd_mul_left hd
  obtain ⟨z, hz⟩ := hd'
  obtain ⟨s, t, hst⟩ := hfh
  have hvh : IsCoprime v h := by
    refine ⟨s * z, t - s * h * x, ?_⟩
    linear_combination hst - s * hz
  obtain ⟨s, t, hst⟩ := hvh
  obtain ⟨u, z, huz⟩ := hvw
  have he : (s * u * v + s * z * w + t * u * h) * v +
      (t * z) * (h * w) = 1 := by
    calc
      _ = (s * v + t * h) * (u * v + z * w) := by ring
      _ = 1 := by rw [hst, huz]; norm_num
  have hkv : (k : ℤ) ∣ 2 * v := by
    convert dvd_add hk₁ hk₂ using 1
    ring
  have hkhw : (k : ℤ) ∣ 2 * (h * w) := by
    convert dvd_sub hk₂ hk₁ using 1
    ring
  have hk2 : (k : ℤ) ∣ 2 := by
    have ha := dvd_add
      (dvd_mul_of_dvd_right hkv (s * u * v + s * z * w + t * u * h))
      (dvd_mul_of_dvd_right hkhw (t * z))
    convert ha using 1
    linear_combination -2 * he
  have hk2' : k ∣ 2 := by exact_mod_cast hk2
  exact (Nat.dvd_prime Nat.prime_two).mp hk2'

/-
Es kann ferner die Summe oder die Differenz zweier reducirten Brüche
mit verschiedenen Nennern nie eine ganze Zahl werden. Angenommen,
es wäre

a/b ± c/d = n

eine ganze Zahl, wobei a prim gegen b, c prim gegen d und b < d ist,
so wäre ad ± bc = bdn und daher ±bc/d = bn−a, was nicht möglich ist.
-/

example (a b c d : ℤ) (hb : 0 < b) (hbd : b < d)
    (_hab : Int.gcd a b = 1) (hcd : Int.gcd c d = 1) :
    ¬ ∃ n : ℤ, (a : ℚ) / b + (c : ℚ) / d = n := by
  rintro ⟨n, hn⟩
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans hb hbd))
  have he : a * d + b * c = b * d * n := by
    field_simp at hn
    exact_mod_cast hn
  have hdc : d ∣ b * c := by
    refine ⟨n * b - a, ?_⟩
    nlinarith [he]
  have hdb : d ∣ b :=
    (Int.isCoprime_iff_gcd_eq_one.mpr hcd).symm.dvd_of_dvd_mul_right hdc
  have := Int.le_of_dvd hb hdb
  omega

example (a b c d n : ℚ) (hd : d ≠ 0)
    (h : a * d + b * c = b * d * n) :
    b * c / d = b * n - a := by
  apply (div_eq_iff hd).2
  nlinarith [h]

/-
Die Summe der obigen Partialbrüche kann somit nur dann eine ganze Zahl
werden, wenn jeder Bruch für sich in eine solche übergeht.

3. Hat man den Bruch (dp+f)/(p²−h²) derart abgekürzt, dass f prim gegen
h ist, so kann in den Partialbrüchen keine weitere Reduction vorgenommen
werden als die, dass man beide Zähler durch den vor der Klammer
stehenden Divisor 2 dividirt; dies ist aber nur dann zu thun, wenn
beide Zähler ungeradgerade Zahlen sind, weil sonst brauchbare Werthe
von p verloren gehen könnten.
Sind beide Zähler gerade, durch 4 nicht theilbare Zahlen und
1, 2, k, l..., resp. 1, 2, k′, l... ihre Factoren, so ergeben sich
die Werthe von v und w aus den Gleichungen

v−hw = 1, k, l, ... 2, 2k, 2l, ...
v+hw = 1, k′, l′, ..., 2, 2k′, 2l′, ...,

wobei die ohne 2 geschriebenen Zahlenglieder insgesammt ungerade Zahlen
bezeichnen.
Da nun v und w ganze Zahlen sein sollen, so sind zur Bestimmung ihrer
zusammengehörigen Werthe nur solche Gleichungspaare zu brauchen, deren
Zahlenglieder beide gerade oder beide ungerade Zahlen sind. Weil aber
mit den ungeraden

Seite 14

Zahlen dieselben Werthe erhalten werden, wie mit den geraden, indem
hier h eine ungerade Zahl sein muss, so kann man die geradzahligen
Factoren weglassen, was mittelst Division der Zähler durch 2 bewirkt
wird.
Wäre aber ein Zähler oder wären beide durch 4 theilbar, so müsste diese
Division unterbleiben, weil sonst brauchbare Werthe von p verloren
gehen könnten. Denn ohne Abkürzung käme man auf die Gleichungen

v−hw = 2k
v+hw = 4k′

somit v = k+2k′, eine ganze Zahl;
-/

example (v w h k k' : ℚ)
    (h₁ : v - h * w = 2 * k) (h₂ : v + h * w = 4 * k') :
    v = k + 2 * k' := by linarith

/-
mit Abkürzung aber wäre

v−hw = k
v+hw = 2k′

und v = (k+2k′)/2 ein Bruch.
-/

example (v w h k k' : ℚ)
    (h₁ : v - h * w = k) (h₂ : v + h * w = 2 * k') :
    v = (k + 2 * k') / 2 := by linarith

namespace Beispiel01

/-
4. Exempel:

x = (5p²+6p−67)/(3p²−14p−5) oder 3x = 5+(88p−176)/(3p²−14p−5)
-/

def x (p : ℚ) : ℚ := (5 * p ^ 2 + 6 * p - 67) / (3 * p ^ 2 - 14 * p - 5)

example (p : ℚ) (h : 3 * p ^ 2 - 14 * p - 5 ≠ 0) :
    3 * x p = 5 + (88 * p - 176) / (3 * p ^ 2 - 14 * p - 5) := by
  unfold x
  ring_nf at h ⊢
  field_simp [h]
  ring

/-
für p = (q+7)/3 wird

3x−5 = x₁ = (88q+88)/(q²−64)
-/

def x₁ (q : ℚ) : ℚ := (88 * q + 88) / (q ^ 2 - 64)

example (q : ℚ) (h : q ^ 2 - 64 ≠ 0) :
    3 * x ((q + 7) / 3) - 5 = x₁ q := by
  unfold x x₁
  have hd : 3 * ((q + 7) / 3) ^ 2 - 14 * ((q + 7) / 3) - 5 =
      (q ^ 2 - 64) / 3 := by ring
  rw [hd]
  field_simp [h]
  ring

/-
und für q = 4r wird

2x₁ = (44r+11)/(r²−4),
-/

example (r : ℚ) :
    2 * x₁ (4 * r) = (44 * r + 11) / (r ^ 2 - 4) := by
  unfold x₁
  rw [show (4 * r) ^ 2 - 64 = 16 * (r ^ 2 - 4) by ring,
    div_mul_eq_div_div]
  ring

/-
somit

x₁ = (w/8)[99/(v−2w)+77/(v+2w)],

daraus

v−2w = ±(1, 3, 9, 11, 33, 99)
v+2w = 1, 7, 11, 77;

aus diesen 48 Gleichungen folgt:
-/

#guard ([1, 3, 9, 11, 33, 99] : List ℤ).all (fun d => 99 % d == 0)

#guard ([1, 7, 11, 77] : List ℤ).all (fun d => 77 % d == 0)

#guard (2 * 6 * 4 : ℕ) = 48

def divisorTrials : List (ℚ × ℚ) :=
  ([1,3,9,11,33,99,-1,-3,-9,-11,-33,-99] : List ℚ).flatMap fun a =>
    ([1,7,11,77] : List ℚ).map fun b => ((a+b)/2, (b-a)/4)

/-
Seite 15

v−2w =   3     33    −3    −33
v+2w =  11      1    77      7
v    =   7     17    37    −13
w    =   2     −8    20     10
x₁   =  10    −80   −80     10
x    =   5    −25   −25      5
p    =   7   −1/2  24/5    3/5
-/

def rows : List (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) :=
  [(3, 11, 7, 2, 10, 5, 7), (33, 1, 17, -8, -80, -25, -1/2),
   (-3, 77, 37, 20, -80, -25, 24/5), (-33, 7, -13, 10, 10, 5, 3/5)]

#guard rows.all fun (a, b, v, w, z, u, p) =>
  v - 2*w == a && v + 2*w == b && x₁ (4*v/w) == z &&
    (5 + z)/3 == u && (4*v/w + 7)/3 == p && x p == u

#guard divisorTrials.filter (fun (v,w) =>
    v.den == 1 && w.den == 1 && w != 0 && (x ((4*v/w+7)/3)).den == 1) =
  [(7,2),(17,-8),(37,20),(-13,10)]

/-
sämmtliche Werthe von x.
-/

example (p : ℚ) (hden : 3 * p ^ 2 - 14 * p - 5 ≠ 0)
    (hint : ∃ n : ℤ, x p = n) : x p = 5 ∨ x p = -25 := by
  obtain ⟨n, hn⟩ := hint
  let r : ℚ := (3 * p - 7) / 4
  let v : ℤ := r.num
  let w : ℤ := r.den
  have hw : w ≠ 0 := by dsimp [w]; exact_mod_cast r.den_nz
  have hwq : (w : ℚ) ≠ 0 := by exact_mod_cast hw
  have hvw : IsCoprime v w := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa [v, w] using r.reduced
  have hr : (v : ℚ) / w = r := by simpa [v, w] using Rat.num_div_den r
  have hp : p = (4 * ((v : ℚ) / w) + 7) / 3 := by rw [hr]; dsimp [r]; ring
  have hx : (v ^ 2 - 4 * w ^ 2) * (6 * n - 10) = w * (44 * v + 11 * w) := by
    have he := (div_eq_iff hden).mp (show (5 * p ^ 2 + 6 * p - 67) / (3 * p ^ 2 - 14 * p - 5) = (n : ℚ) from hn)
    rw [hp] at he
    field_simp [hwq] at he
    have hq : ((v : ℚ) ^ 2 - 4 * w ^ 2) * (6 * n - 10) = w * (44 * (v : ℚ) + 11 * w) := by
      linear_combination -(1/8 : ℚ) * he
    exact_mod_cast hq
  let A : ℤ := v - 2 * w
  let B : ℤ := v + 2 * w
  have hAw : IsCoprime A w := by
    obtain ⟨s, t, h⟩ := hvw
    refine ⟨s, t + 2 * s, ?_⟩
    dsimp [A]
    linear_combination h
  have hBw : IsCoprime B w := by
    obtain ⟨s, t, h⟩ := hvw
    refine ⟨s, t - 2 * s, ?_⟩
    dsimp [B]
    linear_combination h
  have hA : A ∣ 99 := by
    apply (hAw.pow_right (n := 2)).dvd_of_dvd_mul_left
    refine ⟨B * (6 * n - 10) - 44 * w, ?_⟩
    dsimp [A, B]
    linear_combination -hx
  have hB : B ∣ 77 := by
    have h : B ∣ -77 := by
      apply (hBw.pow_right (n := 2)).dvd_of_dvd_mul_left
      refine ⟨A * (6 * n - 10) - 44 * w, ?_⟩
      dsimp [A, B]
      linear_combination -hx
    simpa using h
  have hAabs : A.natAbs ∈ ({1,3,9,11,33,99} : Finset ℕ) := by
    rw [← show (99 : ℕ).divisors = {1,3,9,11,33,99} by decide]
    exact Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hA, by decide⟩
  have hBabs : B.natAbs ∈ ({1,7,11,77} : Finset ℕ) := by
    rw [← show (77 : ℕ).divisors = {1,7,11,77} by decide]
    exact Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hB, by decide⟩
  have hsign (z : ℤ) : z = (z.natAbs : ℤ) ∨ z = -(z.natAbs : ℤ) := by
    rcases le_total 0 z with hz | hz
    · left; simp [abs_of_nonneg hz]
    · right; simp [abs_of_nonpos hz]
  have hAsign := hsign A
  have hBsign := hsign B
  simp only [Finset.mem_insert, Finset.mem_singleton] at hAabs hBabs
  have hAcases : A = 1 ∨ A = 3 ∨ A = 9 ∨ A = 11 ∨ A = 33 ∨ A = 99 ∨
      A = -1 ∨ A = -3 ∨ A = -9 ∨ A = -11 ∨ A = -33 ∨ A = -99 := by omega
  have hBcases : B = 1 ∨ B = 7 ∨ B = 11 ∨ B = 77 ∨
      B = -1 ∨ B = -7 ∨ B = -11 ∨ B = -77 := by omega
  have hpAB : p = (8 * ((A : ℚ) + B) / ((B : ℚ) - A) + 7) / 3 := by
    have hs : ((A : ℚ) + B) = 2 * v := by dsimp [A, B]; push_cast; ring
    have hd : ((B : ℚ) - A) = 4 * w := by dsimp [A, B]; push_cast; ring
    rw [hs, hd, hp]
    field_simp [hwq]
    ring
  have hi : (x p).den = 1 := by rw [hn]; exact Rat.den_intCast n
  have hw4 : B - A = 4 * w := by dsimp [A, B]; ring

  rcases hAcases with hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA <;>
    rcases hBcases with hB | hB | hB | hB | hB | hB | hB | hB <;>
    norm_num [hA, hB] at hpAB hw4 <;>
    try omega
  all_goals rw [hpAB] at hi ⊢
  all_goals norm_num [x] at hi
  all_goals norm_num [x]

end Beispiel01

end Kunerth1877.Paragraf02
