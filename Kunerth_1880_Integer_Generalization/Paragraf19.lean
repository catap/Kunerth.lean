/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf19

/-
Seite 362
§. 19.
II. Berechnung gebrochener Zahlen für p₁ durch Kettenbrüche.

Kömmt für p₁ eine ganze Zahl nicht vor, so suche man dafür
einen Bruch v/w, und verwandle zu diesem Ende √a in einen
Kettenbruch, was am schnellsten nach Tenner’s Methode
geschieht, die im nächsten Exempel dargestellt ist. Findet man
unter den Nennern der vollständigen Quotienten (in der VI.
Verticalreihe) die Zahl n oder ein Vielfaches, etwa das gfache von n
und ist g ein Theiler von D, so setze man die diesen Nennern
entsprechenden Näherungsbrüche, welche Auflösungen von
v² − aw² = ±n beziehungsweise = ±gn sind, für p₁ (= v/w) in
die Formel VIII, oder die Werthe von v und w in X ein. Kämen
jedoch in der VI. Colonne weder n noch ng, wohl aber die
Factoren von n (= kl...) vor, so berechne man aus den diesen
Factoren entsprechenden Näherungsbrüchen die Auflösungen der
Gleichung v² − aw² = ±kl..., und mache mit ±v/w den Versuch.
-/

namespace Beispiel08

/-
8. Exempel:
y² = 199x²+97x−20 = (7x+8)²+3(5x−4)(10x+7),
-/

example (x : ℚ) : 199 * x ^ 2 + 97 * x - 20 = (7 * x + 8) ^ 2 + 3 * (5 * x - 4) * (10 * x + 7) := by ring

/-
D = 3.8443, x = −7/10, y = 31/10,
10x = −7+2(31p−908)/(p²−199);
-/

example : (97 ^ 2 - 4 * 199 * (-20) : ℤ) = 3 * 8443 := by norm_num

example : (31 / 10 : ℚ) ^ 2 = 199 * (-7 / 10) ^ 2 + (97) * (-7 / 10) + (-20) := by norm_num

example (p : ℚ) : (-7) + (2 * (31) * p + (2 * 199 * (-7) + (97) * 10)) / (p ^ 2 - 199) = (-7) + 2 * ((31) * p + (-908)) / (p ^ 2 - 199) := by ring

/-
I    II   III   IV    V    VI
14   ×    14 = 199    −     3
 9   1    13    169   30   10
 2   7     7     49  150   15
 1   6     8     64  135    9
 2   4    10    100   99   11
u. s. f.

(14+14)/3 = 9⅓, 14−1 = 13
(14+13)/10 = 2+7/10, 14−7 = 7
(14+7)/15 = 1+6/15, 14−6 = 8
-/

example :
    let step := fun (s : ℤ × ℤ × List (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × Bool)) (q : ℤ) =>
      let remainder := 14 + s.1 - q * s.2.1
      let m := q * s.2.1 - s.1
      let numerator := 199 - m ^ 2
      let d := numerator / s.2.1
      (m, d, s.2.2 ++ [(q, remainder, m, m^2, numerator, d,
        numerator % s.2.1 == 0)])
    (([9, 2, 1, 2] : List ℤ).foldl step (14, 3, [])).2.2 =
      [(9,1,13,169,30,10,true), (2,7,7,49,150,15,true),
       (1,6,8,64,135,9,true), (2,4,10,100,99,11,true)] := by norm_num

example : ((14 + 14) / 3 : ℚ) = 9 + 1 / 3 := by norm_num

example : ((14 + 13) / 10 : ℚ) = 2 + 7 / 10 := by norm_num

example : ((14 + 7) / 15 : ℚ) = 1 + 6 / 15 := by norm_num

/-
In der I. Verticalreihe stehen unter 14 die Nenner der Kette
und unter VI die Nenner N der vollständigen Quotienten, welche
Zahlenglieder der Gleichungen v² = aw²∓N sind, wo das Zeichen −
für die an den ungraden und + für die an den geraden Stellen
vorkommenden Nenner zu nehmen ist.
-/

example : Prop :=
  ∀ (a : ℤ) (A M Q V W : ℕ → ℤ)
    (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
    (_hM : M 0 = 0) (_hQ : Q 0 = 1)
    (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
      (Real.sqrt a + M k) / Q k < A k + 1)
    (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
    (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
    (_hV₀ : V 0 = A 0) (_hW₀ : W 0 = 1)
    (_hV₁ : V 1 = A 1 * A 0 + 1) (_hW₁ : W 1 = A 1)
    (_hVstep : ∀ k, V (k + 2) = A (k + 2) * V (k + 1) + V k)
    (_hWstep : ∀ k, W (k + 2) = A (k + 2) * W (k + 1) + W k),
    ∀ k, V k ^ 2 - a * W k ^ 2 = (-1) ^ (k + 1) * Q (k + 1)

/-
Seite 363

14   9   2   1   2 ... die Nenner des Kettenbruches;
14/1   127/9   268/19   395/28   1058/75 ... die Näherungsbrüche;
-/

example : (14 : ℚ) = 14 / 1 := by norm_num

example : (14 ^ 2 - 199 * 1 ^ 2 : ℤ) = -3 := by norm_num

example : (14 + 1 / (9) : ℚ) = 127 / 9 := by norm_num

example : (127 ^ 2 - 199 * 9 ^ 2 : ℤ) = 10 := by norm_num

example : (14 + 1 / (9 + 1 / (2)) : ℚ) = 268 / 19 := by norm_num

example : (268 ^ 2 - 199 * 19 ^ 2 : ℤ) = -15 := by norm_num

example : (14 + 1 / (9 + 1 / (2 + 1 / (1))) : ℚ) = 395 / 28 := by norm_num

example : (395 ^ 2 - 199 * 28 ^ 2 : ℤ) = 9 := by norm_num

example : (14 + 1 / (9 + 1 / (2 + 1 / (1 + 1 / (2)))) : ℚ) = 1058 / 75 := by norm_num

example : (1058 ^ 2 - 199 * 75 ^ 2 : ℤ) = -11 := by norm_num

/-
die Bruchglieder des zweiten sind die Auflösung der Gleichung
v² = 199w²+10; für p = 127/9 wird x = −763 und nach IX
in §. 5 ist y = (127/9)(−763+7/10)−31/10 = −10760.
-/

example : (-7 + 2 * (31 * (127 / 9) - 908) / ((127 / 9) ^ 2 - 199) : ℚ) = 10 * (-763) := by norm_num

example : ((127 / 9) * (-763 + 7 / 10) - 31 / 10 : ℚ) = -10760 := by norm_num

example : (-10760 : ℚ) ^ 2 = 199 * (-763) ^ 2 + (97) * (-763) + (-20) := by norm_num

end Beispiel08

namespace Beispiel09

/-
9. Exempel:
y² = 124x²+37x+7 = 1/16[(20x−13)²+(396x−19)(4x+3)]
-/

example (x : ℚ) : 124 * x ^ 2 + 37 * x + 7 = ((20 * x - 13) ^ 2 + (396 * x - 19) * (4 * x + 3)) / 16 := by ring

/-
D = −3.701, x = −3/4, y = −28/4,
4x = −3+4(−14p−149)/(p²−124),
-/

example : (37 ^ 2 - 4 * 124 * 7 : ℤ) = -3 * 701 := by norm_num

example : (-28 / 4 : ℚ) ^ 2 = 124 * (-3 / 4) ^ 2 + (37) * (-3 / 4) + (7) := by norm_num

example (p : ℚ) : (-3) + (2 * (-28) * p + (2 * 124 * (-3) + (37) * 4)) / (p ^ 2 - 124) = (-3) + 4 * ((-14) * p + (-149)) / (p ^ 2 - 124) := by ring

/-
S = 16D; unter VI steht an der fünften Stelle 12, ein Factor
von S, der fünfte Näherungsbruch p = −412/37 macht x = −787,
y = 8762.

I   124   IV
11 ...  3
 7 ...  8
 2 ... 11
 1 ...  9
 1 ... 12
-/

example :
    let step := fun (s : ℤ × ℤ × List (ℤ × Bool)) (q : ℤ) =>
      let m := q * s.2.1 - s.1
      let d := (124 - m ^ 2) / s.2.1
      (m, d, s.2.2 ++ [(d, (124 - m ^ 2) % s.2.1 == 0)])
    (([11, 7, 2, 1, 1] : List ℤ).foldl step (0, 1, [])).2.2 = [(3, true), (8, true), (11, true), (9, true), (12, true)] := by norm_num

example : (11 + 1 / (7 + 1 / (2 + 1 / (1 + 1 / (1)))) : ℚ) = 412 / 37 := by norm_num

example : (412 ^ 2 - 124 * 37 ^ 2 : ℤ) = -12 := by norm_num

example : (-3 + 4 * (-14 * (-412 / 37) - 149) / ((-412 / 37) ^ 2 - 124) : ℚ) = 4 * (-787) := by norm_num

example : (8762 : ℚ) ^ 2 = 124 * (-787) ^ 2 + (37) * (-787) + (7) := by norm_num

end Beispiel09

namespace Beispiel10

/-
10. Exempel:
y² = 46x²−417x−324 = (26x+14)²−5(14x+13)(9x+8);
-/

example (x : ℚ) : 46 * x ^ 2 - 417 * x - 324 = (26 * x + 14) ^ 2 - 5 * (14 * x + 13) * (9 * x + 8) := by ring

/-
D = 9.5.5189, x = −13/14, y = −142/14,
14x = −13+2(−142p−3517)/(p²−46), S₁ = 2.49D;
-/

example : ((-417) ^ 2 - 4 * 46 * (-324) : ℤ) = 9 * 5 * 5189 := by norm_num

example : (-142 / 14 : ℚ) ^ 2 = 46 * (-13 / 14) ^ 2 + (-417) * (-13 / 14) + (-324) := by norm_num

example (p : ℚ) : (-13) + (2 * (-142) * p + (2 * 46 * (-13) + (-417) * 14)) / (p ^ 2 - 46) = (-13) + 2 * ((-142) * p + (-3517)) / (p ^ 2 - 46) := by ring

/-
aus dem dritten und sechsten Näherungsbruche findet man die
Auflösung der Gleichung v² = 46w²−14, nämlich w = 3, v = 20;
für p = 20/3 wird x = 409, y = −2743.
-/

example : (20 ^ 2 - 46 * 3 ^ 2 : ℤ) = -14 := by norm_num

example : (-13 + 2 * (-142 * (20 / 3) - 3517) / ((20 / 3) ^ 2 - 46) : ℚ) = 14 * 409 := by norm_num

example : (-2743 : ℚ) ^ 2 = 46 * (409) ^ 2 + (-417) * (409) + (-324) := by norm_num

/-
Seite 364

I    46    VI
6 ... 10
1      3
3 ...  7
1      6
1 ...  5
2      2
-/

example :
    let step := fun (s : ℤ × ℤ × List (ℤ × Bool)) (q : ℤ) =>
      let m := q * s.2.1 - s.1
      let d := (46 - m ^ 2) / s.2.1
      (m, d, s.2.2 ++ [(d, (46 - m ^ 2) % s.2.1 == 0)])
    (([6, 1, 3, 1, 1, 2] : List ℤ).foldl step (0, 1, [])).2.2 = [(10, true), (3, true), (7, true), (6, true), (5, true), (2, true)] := by norm_num

/-
Oder: x = −8/9, y = −82/9, 9x = −8+(−164p−4489)/(p²−46);
-/

example : (-82 / 9 : ℚ) ^ 2 = 46 * (-8 / 9) ^ 2 + (-417) * (-8 / 9) + (-324) := by norm_num

/-
der zweite Näherungsbruch ist 7/1, er löst die Gleichung
v₁²−46w₁² = 3,
also entspricht der Gleichung
v²−46w² = 9, w = 14, v = 95;
-/

example : (7 ^ 2 - 46 * 1 ^ 2 : ℤ) = 3 := by norm_num

example : (95 ^ 2 - 46 * 14 ^ 2 : ℤ) = 9 := by norm_num

/-
für p = 95/14 wird x = −13556, y = 91972.
-/

example : (-8 + (-164 * (95 / 14) - 4489) / ((95 / 14) ^ 2 - 46) : ℚ) = 9 * (-13556) := by norm_num

example : (91972 : ℚ) ^ 2 = 46 * (-13556) ^ 2 + (-417) * (-13556) + (-324) := by norm_num

end Beispiel10

end Kunerth1880.Paragraf19
