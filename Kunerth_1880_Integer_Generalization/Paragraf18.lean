/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf18

/-
Seite 358
§. 18.
I. Berechnung ganzzahliger Werthe von p₁.

A. Lässt sich in der Formel α = −np + α₁, zu welcher laut IV
die Formel β = mp + β₁ gehört, eine solche ganze Zahl für p
ersehen, dass a − α² eine Primzahl wird, so ist die Gleichung I
gelöst, sobald man sie auf die Form II gebracht hat.
-/

example (a b c α β γ δ n m : ℤ)
    (ha : a = α ^ 2 - n * γ)
    (hb : b = 2 * α * β + m * γ + n * δ)
    (hc : c = β ^ 2 - m * δ)
    (hp : Prime (a - α ^ 2)) :
    ∃ x y : ℤ, y ^ 2 = a * x ^ 2 + b * x + c := by
  have hproduct : a - α ^ 2 = (-n) * γ := by rw [ha]; ring
  rcases hp.irreducible.isUnit_or_isUnit hproduct with hn | hγ
  · rcases Int.isUnit_iff.mp hn with hn | hn
    · have : n = -1 := by omega
      subst n
      refine ⟨-m, α * (-m) + β, ?_⟩
      rw [ha, hb, hc]
      ring
    · have : n = 1 := by omega
      subst n
      refine ⟨m, α * m + β, ?_⟩
      rw [ha, hb, hc]
      ring
  · rcases Int.isUnit_iff.mp hγ with hγ | hγ
    · subst γ
      refine ⟨δ, α * δ + β, ?_⟩
      rw [ha, hb, hc]
      ring
    · subst γ
      refine ⟨-δ, α * (-δ) + β, ?_⟩
      rw [ha, hb, hc]
      ring

/-
Dasselbe findet statt, wenn a − α² das Doppelte einer Primzahl ist
und dabei b nebst βc gerade Zahlen sind.
-/

/-
Der Wortlaut schliesst die Primzahl 2 nicht aus. Eine Lesart mit einzeln
geraden β und c wäre eine andere Voraussetzung; sie wird der bisherigen
Productlesart hier nicht hinzugefügt.
-/

example : Prop := ∀ (a b c α β γ δ n m q : ℤ),
    a = α ^ 2 - n * γ →
    b = 2 * α * β + m * γ + n * δ →
    c = β ^ 2 - m * δ →
    Prime q → a - α ^ 2 = 2 * q → 2 ∣ b → 2 ∣ β * c →
    ∃ x y : ℤ, y ^ 2 = a * x ^ 2 + b * x + c

namespace Beispiel01

/-
1. Exempel:
y² = 61x²+111x−101 = (7x+8)²+(3x+11)(4x−15),
-/

example (x : ℚ) : 61 * x ^ 2 + 111 * x - 101 = (7 * x + 8) ^ 2 + (3 * x + 11) * (4 * x - 15) := by ring

/-
x = −11/3, α = 3p+7, β = 11p+8;
-/

example : (3 * (-11 / 3) + 11 : ℚ) = 0 := by norm_num

/-
für p = −5 wird
α = −8, β = −47, 61−64 = −3
-/

example : (3 * (-5) + 7 : ℤ) = -8 := by norm_num

example : (11 * (-5) + 8 : ℤ) = -47 := by norm_num

example : (61 - 64 : ℤ) = -3 := by norm_num

/-
und
y² = (8x+47)²−(3x+11)(x+210); x = −210, y = 1633.
-/

example (x : ℚ) : 61 * x ^ 2 + 111 * x - 101 = (8 * x + 47) ^ 2 - (3 * x + 11) * (x + 210) := by ring

example : (1633 : ℚ) ^ 2 = 61 * (-210) ^ 2 + (111) * (-210) + (-101) := by norm_num

end Beispiel01

namespace Beispiel02

/-
2. Exempel:
y² = 67x²−290x+244 = (12x−17)²−(7x−5)(11x−9),
-/

example (x : ℚ) : 67 * x ^ 2 - 290 * x + 244 = (12 * x - 17) ^ 2 - (7 * x - 5) * (11 * x - 9) := by ring

/-
x = 5/7, α = −7p+12, β = 5p−17;
-/

example : (7 * (5 / 7) - 5 : ℚ) = 0 := by norm_num

/-
für p = 3
wird α = −9, β = −2, 67−81 = −14
-/

example : (-7 * 3 + 12 : ℤ) = -9 := by norm_num

example : (5 * 3 - 17 : ℤ) = -2 := by norm_num

example : (67 - 81 : ℤ) = -14 := by norm_num

/-
und
y² = (9x+2)²−2(7x−5)(x+24), x = −24, y = 214.
-/

example (x : ℚ) : 67 * x ^ 2 - 290 * x + 244 = (9 * x + 2) ^ 2 - 2 * (7 * x - 5) * (x + 24) := by ring

example : (214 : ℚ) ^ 2 = 67 * (-24) ^ 2 + (-290) * (-24) + (244) := by norm_num

end Beispiel02

/-
B. Noch der Formel

nx = m + [2rp₁ + (2am + bn)]/(p₁² − a) ... VIII

Nach Ausscheidung der unzulässigen Divisoren von D (§. 8)
sind alle andern mit n zu multipliciren, diese Producte, wenn sie
a nicht übersteigen, mit beiden, sonst aber nur mit dem positiven
Vorzeichen dem Nenner p₁² − a gleichzusetzen und mit den sich
aus diesen Gleichungen für p₁ ergebenden ganzen Zahlen die
Werthe von x nach VIII zu berechnen.
-/

example (a N p : ℤ) (hN : a < N) (hp : p ^ 2 - a = -N) : False := by
  nlinarith [sq_nonneg p]

/-
Seite 359
-/

namespace Beispiel03

/-
3. Exempel:
y² = 156x²+447x+127 = (9x+19)²+3(5x−6)(5x+13),
-/

example (x : ℚ) : 156 * x ^ 2 + 447 * x + 127 = (9 * x + 19) ^ 2 + 3 * (5 * x - 6) * (5 * x + 13) := by ring

/-
D = 3.7.5741 x = 6/5, y = 149/5,
5x = 6+(298p+4107)/(p²−156)
-/

example : (447 ^ 2 - 4 * 156 * 127 : ℤ) = 3 * 7 * 5741 := by norm_num

example : (149 / 5 : ℚ) ^ 2 = 156 * (6 / 5) ^ 2 + (447) * (6 / 5) + (127) := by norm_num

example (p : ℚ) : (6) + (2 * (149) * p + (2 * 156 * (6) + (447) * 5)) / (p ^ 2 - 156) = (6) + 1 * ((298) * p + (4107)) / (p ^ 2 - 156) := by ring

/-
N = −35, p = 11, x = −41, y = 494.
-/

example : (11 ^ 2 - 156 : ℤ) = -35 := by norm_num

example : (6 + (298 * 11 + 4107) / (11 ^ 2 - 156) : ℚ) = 5 * (-41) := by norm_num

example : (494 : ℚ) ^ 2 = 156 * (-41) ^ 2 + (447) * (-41) + (127) := by norm_num

end Beispiel03

/-
C. Nach der Formel

nx = m + h(dp + f)/(p² − a) ... [1]

in §. 8.

Ist h₁ das grösste gemeinschaftliche Mass von n und h (= h₁ρ),
so sind alle zulässigen Factoren von D/ρ mit n zu multipliciren
und hierauf wie in B zu verfahren.
-/

namespace Beispiel04

/-
4. Exempel:
23z²−41xz−44z−17x²+36x+79 = 0,
für z = (y+41x+44)/46 wird
y² = 3245x²+296x−5332, D = 16.9.7³.23.61,
-/

example (x y : ℚ) : 92 * (23 * ((y + 41 * x + 44) / 46) ^ 2 - 41 * x * ((y + 41 * x + 44) / 46) - 44 * ((y + 41 * x + 44) / 46) - 17 * x ^ 2 + 36 * x + 79) = y ^ 2 - (3245 * x ^ 2 + 296 * x - 5332) := by ring

example : (296 ^ 2 - 4 * 3245 * (-5332) : ℤ) = 16 * 9 * 7 ^ 3 * 23 * 61 := by norm_num

/-
K² = 3245Δ²+D(α²−3245),
für α = 57 ist 4 der Rest; setzt man der kürzeren Rechnung wegen
K = 3.7.8k, Δ = 168d und dividirt durch 168², so kömmt
k² = 3245d²+9821;
-/

example : (57 ^ 2 - 3245 : ℤ) = 4 := by norm_num

example : (16 * 9 * 7 ^ 3 * 23 * 61 * 4 / 168 ^ 2 : ℚ) = 9821 := by norm_num

/-
Δ₁² = 3245β₁²+9821(α₁²−3245); α₁ = 57
und Δ₁² = 3245β₁²+39284;
-/

example : (9821 * (57 ^ 2 - 3245) : ℤ) = 39284 := by norm_num

/-
für Δ₁ = 3245z+r wird
β₁² = 3245z²+2rz−12+(r²−344)/3245,
r = 302, 347, 1128, 1468
B = 28, 37, 392, 664;
-/

example : ((302 ^ 2 - 344) / 3245 : ℚ) = 28 := by norm_num

example : ((347 ^ 2 - 344) / 3245 : ℚ) = 37 := by norm_num

example : ((1128 ^ 2 - 344) / 3245 : ℚ) = 392 := by norm_num

example : ((1468 ^ 2 - 344) / 3245 : ℚ) = 664 := by norm_num

/-
für die ersten zwei Werthe von r und für z = 0 wird β₁ = 4
beziehungsweise 5, also
k² = (57d+5)²−2(2d−31)(d+158);
-/

example : (-12 + 28 : ℤ) = 4 ^ 2 := by norm_num

example : (-12 + 37 : ℤ) = 5 ^ 2 := by norm_num

example (d : ℚ) : 3245 * d ^ 2 + 9821 = (57 * d + 5) ^ 2 - 2 * (2 * d - 31) * (d + 158) := by ring

/-
somit
d = −158, k = −9001, K = −1512168, β = (K+αb)/(2a) = −1152/5
-/

example : (57 * (-158) + 5 : ℤ) = -9001 := by norm_num

example : (168 * (-9001) : ℤ) = -1512168 := by norm_num

example : ((-1512168 + 57 * 296) / (2 * 3245) : ℚ) = -1152 / 5 := by norm_num

/-
und
25y² = (285x−1152)²+4(5x+33191)(5x−11);
x = 11/5, y = −525/5,
5x = 11+210(−5p+347)/(p²−3245), S = 25D.
-/

/-
Redaktionelle Nachrechnung: Im ersten Factor dürfte 33191−5x
statt 5x+33191 stehen. Zunächst wird der Unterschied der
gedruckten Ausdrücke, danach die vermutliche Berichtigung geprüft.
-/

example (x : ℚ) :
    (285 * x - 1152) ^ 2 + 4 * (5 * x + 33191) * (5 * x - 11) -
      25 * (3245 * x ^ 2 + 296 * x - 5332) = 40 * x * (5 * x - 11) := by ring

example (x : ℚ) : 25 * (3245 * x ^ 2 + 296 * x - 5332) =
    (285 * x - 1152) ^ 2 + 4 * (33191 - 5 * x) * (5 * x - 11) := by ring

example : (-525 / 5 : ℚ) ^ 2 = 3245 * (11 / 5) ^ 2 + (296) * (11 / 5) + (-5332) := by norm_num

example (p : ℚ) : (11) + (2 * (-525) * p + (2 * 3245 * (11) + (296) * 5)) / (p ^ 2 - 3245) = (11) + 210 * ((-5) * p + (347)) / (p ^ 2 - 3245) := by ring

/-
Seite 360

Hier ist h₁ = 5, ρ = 42, D/ρ = 8.3.7².23.61; da 3245 ein
Nichtrest von 3 und 8 ist, so sind diese zwei Divisoren und im
Hinblick auf den äquivalenten Nenner (§. 13, XIIa) auch 2 wegzulassen,
hierauf sämmtliche Factoren der Zahl 7².23.61 wie auch die
Vierfachen derselben mit 5 zu multipliciren und dem Nenner gleich
zu setzen.
-/

example : (16 * 9 * 7 ^ 3 * 23 * 61 / 42 : ℚ) = 8 * 3 * 7 ^ 2 * 23 * 61 := by norm_num

example : ¬ ∃ x : Fin 3, (x.val ^ 2) % 3 = 3245 % 3 := by decide

example : ¬ ∃ x : Fin 8, (x.val ^ 2) % 8 = 3245 % 8 := by decide

/-
Da findet man
p =  5,  45, −65
x = −2,  −2,  31
y = 84,     1767
z =  1        67
-/

example : (11 + 210 * (-5 * (5) + 347) / ((5) ^ 2 - 3245) : ℚ) = 5 * (-2) := by norm_num

example : (11 + 210 * (-5 * (45) + 347) / ((45) ^ 2 - 3245) : ℚ) = 5 * (-2) := by norm_num

example : (11 + 210 * (-5 * (-65) + 347) / ((-65) ^ 2 - 3245) : ℚ) = 5 * (31) := by norm_num

example : (84 : ℚ) ^ 2 = 3245 * (-2) ^ 2 + (296) * (-2) + (-5332) := by norm_num

example : ((84 + 41 * (-2) + 44) / 46 : ℚ) = 1 := by norm_num

example : (23 * 1 ^ 2 - 41 * (-2) * 1 - 44 * 1 - 17 * (-2) ^ 2 + 36 * (-2) + 79 : ℤ) = 0 := by norm_num

example : (1767 : ℚ) ^ 2 = 3245 * (31) ^ 2 + (296) * (31) + (-5332) := by norm_num

example : ((1767 + 41 * (31) + 44) / 46 : ℚ) = 67 := by norm_num

example : (23 * 67 ^ 2 - 41 * (31) * 67 - 44 * 67 - 17 * (31) ^ 2 + 36 * (31) + 79 : ℤ) = 0 := by norm_num

end Beispiel04

/-
D. Nach der Formel

nx = m + (dp₁ + f)/(p₁² − a₁) ... [2] in §. 9.
S,, = n²D/μ⁴ = −a₁d² + f².

Die Formel [2] entstand aus VIII durch Abkürzung des dortigen
Bruches mit μ², wobei n durch μ oder μ/2 theilbar sein muss.
Bezeichnen wir jeden der Quotienten n/μ und 2n/μ mit ν, so sind
alle zulässigen Divisoren von S,,/ν² mit ν zu multipliciren und dem
Nenner p₁² − a gleichzustellen.
-/

namespace Beispiel05

/-
5. Exempel:
y² = 639x²−15x−615 = (3x+20)²+5(21x−29)(6x+7),
-/

example (x : ℚ) : 639 * x ^ 2 - 15 * x - 615 = (3 * x + 20) ^ 2 + 5 * (21 * x - 29) * (6 * x + 7) := by ring

/-
D = 5.9.7².23.31, x = 29/21, y = 507/11,
-/

example : ((-15) ^ 2 - 4 * 639 * (-615) : ℤ) = 5 * 9 * 7 ^ 2 * 23 * 31 := by norm_num

/-
Redaktionelle Nachrechnung: Der Nenner 11 dürfte ein Druckfehler
für 21 sein. Für x = 29/21 wird 3x+20 = 507/21; auch der folgende
Zähler 1014p entspricht diesem Werth von y.
-/

example : (507 / 11 : ℚ) ^ 2 ≠ 639 * (29 / 21) ^ 2 + (-15) * (29 / 21) + (-615) := by norm_num

example : (3 * (29 / 21) + 20 : ℚ) = 507 / 21 := by norm_num

example : (507 / 21 : ℚ) ^ 2 = 639 * (29 / 21) ^ 2 + (-15) * (29 / 21) + (-615) := by norm_num

/-
21x = 29+(1014p+36747)/(p²−639);
-/

example (p : ℚ) : (29) + (2 * (507) * p + (2 * 639 * (29) + (-15) * 21)) / (p ^ 2 - 639) = (29) + 1 * ((1014) * p + (36747)) / (p ^ 2 - 639) := by ring

/-
für p = 3p₁ wird
21x = 29+(338p₁+4083)/(p₁²−71), S,, = 5.7⁴.23.31;
-/

example (p : ℚ) : (1014 * (3 * p) + 36747) * (p ^ 2 - 71) = (338 * p + 4083) * ((3 * p) ^ 2 - 639) := by ring

example : (21 ^ 2 * (5 * 9 * 7 ^ 2 * 23 * 31) / 3 ^ 4 : ℚ) = 5 * 7 ^ 4 * 23 * 31 := by norm_num

/-
von den Divisoren der Zahl S,,/7² ist bloss −1 zu brauchen; also
p₁²−71 = −7, p₁ = −8, x = −8, y = 201.
-/

/- Rechenschritt nach §. 18 D: ν = 21/3 = 7; die ganzzahligen
Parameter müssen auch einen ganzzahligen Werth von x liefern. -/

example :
    let S : ℕ := 5 * 7 ^ 4 * 23 * 31
    let ν : ℕ := 21 / 3
    let trials := (S / ν ^ 2).divisors.biUnion fun d =>
      ({(ν : ℤ) * d, -((ν : ℤ) * d)} : Finset ℤ).biUnion fun N =>
        let p : ℤ := Nat.sqrt (71 + N).toNat
        (({p, -p} : Finset ℤ).filter fun p =>
          p ^ 2 = 71 + N ∧
            (((29 : ℚ) + (338 * p + 4083) / N) / 21).den = 1).image
          (fun p => (N / ν, p))
    trials = {(-1, -8)} := by native_decide

example : ((-8) ^ 2 - 71 : ℤ) = -7 := by norm_num

example : (29 + (338 * (-8) + 4083) / ((-8) ^ 2 - 71) : ℚ) = 21 * (-8) := by norm_num

example : (201 : ℚ) ^ 2 = 639 * (-8) ^ 2 + (-15) * (-8) + (-615) := by norm_num

end Beispiel05

/-
E. Nach der Formel

nx = m + h(d₁p₁ + f₁)/(p₁² − a₁),
S¹,, = n²D/(hμ⁴) = h(−ad₁² + f₁²).

Seite 361

Ist h₁ das grösste gemeinsch. Mass von h und ν, welches letztere
in der obigen Bedeutung (D) zu verstehen ist, so hat man nach
§. 8 sämmtliche zulässigen Divisoren von [n²D/(μ⁴ν²) : h/h₁]
das ist von h₁S¹,,/ν² mit ν zu multipliciren u. s. w.
-/

namespace Beispiel06

/-
6. Exempel:
y² = 126x²+528x−264 = (9x+10)²+(15x−14)(3x+26),
-/

example (x : ℚ) : 126 * x ^ 2 + 528 * x - 264 = (9 * x + 10) ^ 2 + (15 * x - 14) * (3 * x + 26) := by ring

/-
D = 64.9.5.11.13, x = 14/15, y = 276/15,
-/

example : (528 ^ 2 - 4 * 126 * (-264) : ℤ) = 64 * 9 * 5 * 11 * 13 := by norm_num

example : (276 / 15 : ℚ) ^ 2 = 126 * (14 / 15) ^ 2 + (528) * (14 / 15) + (-264) := by norm_num

/-
15x = 14+24(23p+477)/(p²−126);
-/

example (p : ℚ) : (14) + (2 * (276) * p + (2 * 126 * (14) + (528) * 15)) / (p ^ 2 - 126) = (14) + 24 * ((23) * p + (477)) / (p ^ 2 - 126) := by ring

/-
für p = 3p₁ wird
15x = 14+8(23p₁+159)/(p₁²−14), S¹,, = 8.5³.11.13;
-/

example (p : ℚ) : 24 * (23 * (3 * p) + 477) * (p ^ 2 - 14) = 8 * (23 * p + 159) * ((3 * p) ^ 2 - 126) := by ring

example : (15 ^ 2 * (64 * 9 * 5 * 11 * 13) / (8 * 3 ^ 4) : ℚ) = 8 * 5 ^ 3 * 11 * 13 := by norm_num

/-
unter den Divisoren von 1.S¹,,/5² findet man als passend −2 und
55, daher
N  = −10, 275
p₁ =   2,  17
x  = −10,   2
y  =  84,  36.
-/

example : (2 ^ 2 - 14 : ℤ) = -10 := by norm_num

example : (14 + 8 * (23 * 2 + 159) / (2 ^ 2 - 14) : ℚ) = 15 * (-10) := by norm_num

example : (84 : ℚ) ^ 2 = 126 * (-10) ^ 2 + (528) * (-10) + (-264) := by norm_num

example : (17 ^ 2 - 14 : ℤ) = 275 := by norm_num

example : (14 + 8 * (23 * 17 + 159) / (17 ^ 2 - 14) : ℚ) = 15 * (2) := by norm_num

example : (36 : ℚ) ^ 2 = 126 * (2) ^ 2 + (528) * (2) + (-264) := by norm_num

end Beispiel06

/-
F. Nach der Formel

μnx = μm + (2rp₁ + f)/(p₁² − a₁),
S¹ = n²D/μ² = −4a₁r² + f² ... [4] in §. 11.
-/

namespace Beispiel07

/-
7. Exempel:
y² = 540x²−78x−110 = (22x+3)²+7(4x−17)(2x+1),
-/

example (x : ℚ) : 540 * x ^ 2 - 78 * x - 110 = (22 * x + 3) ^ 2 + 7 * (4 * x - 17) * (2 * x + 1) := by ring

/-
D = 4.9.7.967, x = −1/2, y = −16/2, und
-/

example : ((-78) ^ 2 - 4 * 540 * (-110) : ℤ) = 4 * 9 * 7 * 967 := by norm_num

example : (-16 / 2 : ℚ) ^ 2 = 540 * (-1 / 2) ^ 2 + (-78) * (-1 / 2) + (-110) := by norm_num

/-
2x = −1+4(−8p−309)/(p²−540);
-/

example (p : ℚ) : (-1) + (2 * (-16) * p + (2 * 540 * (-1) + (-78) * 2)) / (p ^ 2 - 540) = (-1) + 4 * ((-8) * p + (-309)) / (p ^ 2 - 540) := by ring

/-
multiplicirt man beide Seiten mit 3 und hebt den Bruch durch 36,
so wird
6x = −3+(−16p₁−103)/(p₁²−15), S¹ = 4D/(16.9) = 7.967,
-/

example (p : ℚ) : 12 * (-8 * (6 * p) - 309) * (p ^ 2 - 15) = (-16 * p - 103) * ((6 * p) ^ 2 - 540) := by ring

example : (4 * (4 * 9 * 7 * 967) / (16 * 9) : ℚ) = 7 * 967 := by norm_num

/-
N = 1, p₁ = −4, x = −7, y = 164.
-/

example : ((-4) ^ 2 - 15 : ℤ) = 1 := by norm_num

example : (-3 + (-16 * (-4) - 103) / ((-4) ^ 2 - 15) : ℚ) = 6 * (-7) := by norm_num

example : (164 : ℚ) ^ 2 = 540 * (-7) ^ 2 + (-78) * (-7) + (-110) := by norm_num

end Beispiel07

end Kunerth1880.Paragraf18
