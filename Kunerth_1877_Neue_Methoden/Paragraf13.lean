/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf13

/-
Seite 50

§. 13.
Auflösung einiger Gleichungen von der Form
y² = ax²+b, für negative Werthe von a.
-/

namespace Beispiel01

/-
1. Erstes Exempel.
y² = −43x²+3728983    I
Bestimmt man für den Divisor 8 die quadratischen Reste
beider Seiten dieser Gleichung, so zeigt sich, dass y eine gerade
und x eine ungerade Zahl bezeichnen muss.
-/

example : ∀ x y : ZMod 8, y ^ 2 = -43 * x ^ 2 + 3728983 →
    y.val % 2 = 0 ∧ x.val % 2 = 1 := by decide

/-
Seite 51

Für y = 43z+r wird
x² = −43z²−2rz+86720−(r²−23)/43;
aus der Lösung der diesem Scheinbruche entsprechenden
Congruenz ergibt sich r = 18, und der Bruch wird gleich 7. Es ist
somit
x² = −43z²−36z+86713.    II
-/

example (z r : ℚ) : (3728983 - (43 * z + r) ^ 2) / 43 =
    -43 * z ^ 2 - 2 * r * z + 86720 - (r ^ 2 - 23) / 43 := by ring

example : ((18 : ℚ) ^ 2 - 23) / 43 = 7 := by norm_num

example (z : ℚ) : (3728983 - (43 * z + 18) ^ 2) / 43 =
    -43 * z ^ 2 - 36 * z + 86713 := by ring

/-
Da y < 1931 ist, so muss z < 45 sein, und weil x eine
ungerade Zahl sein soll, so muss z im Hinblicke auf II wegen des
Achterrestes eine geradgerade Zahl sein, die wegen des Fünferrestes
in II kein Vielfaches von 5 ist. Man hat daher in II zu
setzen:
±z = 4, 8, 12, 16, 24, 28, 32, 36, 44;
-/

example : ((1931 : ℤ) + 1) ^ 2 > 3728983 ∧
    (3728983 - (1931 : ℤ) ^ 2) % 43 ≠ 0 := by norm_num

example : (534 : ℤ) < 1931 ∧ (12 : ℤ) < 45 ∧
    (283 : ℤ) % 2 = 1 ∧ (12 : ℤ) % 4 = 0 ∧ (12 : ℤ) % 5 ≠ 0 := by
  norm_num

example : ((List.range 45).filter (fun z => decide (z % 4 = 0 ∧ z % 5 ≠ 0))) =
    [4, 8, 12, 16, 24, 28, 32, 36, 44] := by decide

example : (([-44, -36, -32, -28, -24, -16, -12, -8, -4,
    4, 8, 12, 16, 24, 28, 32, 36, 44] : List ℤ).filter fun z =>
      let n := -43 * z ^ 2 - 36 * z + 86713
      decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) = [12] := by
  native_decide

/-
und da kommt für z = 12, x = 283, und da wegen
−2rz = −36.12,
r = +18 sein muss, so ist
y = 12×43+18 = 534;
-/

example : (283 : ℤ) ^ 2 = -43 * 12 ^ 2 - 36 * 12 + 86713 ∧
    -(2 : ℤ) * 18 * 12 = -36 * 12 ∧
    (12 : ℤ) * 43 + 18 = 534 := by norm_num

example : (534 : ℤ) ^ 2 = -43 * 283 ^ 2 + 3728983 := by norm_num

/-
sonst gibt es keine ganzzahligen Werthe für x und y.
-/

example : ((List.range 89).map (fun n => (n : ℤ) - 44)).filter
    (fun z => let n := -43 * z ^ 2 - 36 * z + 86713
      decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) = [12] := by
  native_decide

end Beispiel01

namespace Beispiel02

/-
2. Zweites Exempel.
y² = −140x²+141035661.    I
Wegen des Achterrestes müssen x und y ungerade Zahlen
sein, und weil das Zahlenglied durch 9² theilbar ist, so kann
x = 9x₁ und y = 9y₁ gesetzt werden. Dann folgt:
y₁² = −140x₁²+1741181    II
-/

example : ∀ x y : ZMod 8, y ^ 2 = -140 * x ^ 2 + 141035661 →
    x.val % 2 = 1 ∧ y.val % 2 = 1 := by decide

example : (141035661 : ℚ) / 9 ^ 2 = 1741181 := by norm_num

example (x₁ y₁ : ℚ) : (9 * y₁) ^ 2 + 140 * (9 * x₁) ^ 2 - 141035661 =
    81 * (y₁ ^ 2 + 140 * x₁ ^ 2 - 1741181) := by ring

/-
y₁ < 1320, y₁ = 140z+r,
also
z < 10 und x₁² = −140z²−2rz+12437−(r²−1)/140;
bezeichnen wir diesen Bruch mit n, so findet sich für
n = 0    6   12   34
r = 1   29   41   69,
die ersten vier Glieder der aus acht Gliedern bestehenden ersten
-/

example (z r : ℚ) : (1741181 - (140 * z + r) ^ 2) / 140 =
    -140 * z ^ 2 - 2 * r * z + 12437 - (r ^ 2 - 1) / 140 := by ring

example : ([1, 29, 41, 69] : List ℚ).map (fun r => (r ^ 2 - 1) / 140) =
    [0, 6, 12, 34] := by norm_num

example : ((List.range 70).filter fun r => decide (r ^ 2 % 140 = 1)) =
    [1, 29, 41, 69] := by decide

/-
Seite 52

Periode der Wurzeln der obigen Congruenz. Setzt man diese
Zahlen in die letzte Gleichung für r und n, so folgt
x₁² = −140z²−  2z+12437...(α) hier kann ±z = 1, 2
x₁² = −140z²− 58z+12431...(β)  „    „   ±z = 1, 5
x₁² = −140z²− 82z+12425...(γ)  „    „   ±z = 1, 4, 5, 7, 8
x₁² = −140z²−138z+12403...(δ)  „    „   ±z = 1, 3, 9
sein.
Es sind nämlich im Vorhinein jene Substitutionen auszuschliessen,
von denen die rechten Seiten der vier oberen Gleichungen
keine quadratischen Reste sein können.
-/

example (z : ℚ) :
    (1741181 - (140 * z + 1) ^ 2) / 140 = -140 * z ^ 2 - 2 * z + 12437 ∧
    (1741181 - (140 * z + 29) ^ 2) / 140 = -140 * z ^ 2 - 58 * z + 12431 ∧
    (1741181 - (140 * z + 41) ^ 2) / 140 = -140 * z ^ 2 - 82 * z + 12425 ∧
    (1741181 - (140 * z + 69) ^ 2) / 140 = -140 * z ^ 2 - 138 * z + 12403 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

example : (([-2, -1, 1, 2] : List ℤ).filter fun z =>
    let n := -140 * z ^ 2 - 2 * z + 12437
    decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) = [-2] := by native_decide

example : (([-5, -1, 1, 5] : List ℤ).filter fun z =>
    let n := -140 * z ^ 2 - 58 * z + 12431
    decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) = [] := by native_decide

example : (([-8, -7, -5, -4, -1, 1, 4, 5, 7, 8] : List ℤ).filter fun z =>
    let n := -140 * z ^ 2 - 82 * z + 12425
    decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) = [8] := by native_decide

example : (([-9, -3, -1, 1, 3, 9] : List ℤ).filter fun z =>
    let n := -140 * z ^ 2 - 138 * z + 12403
    decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) = [] := by native_decide

example : ((List.range 19).map (fun n => (n : ℤ) - 9)).filter
    (fun z => let n := -140 * z ^ 2 - 2 * z + 12437
      decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) =
        [-2] := by native_decide

example : ((List.range 19).map (fun n => (n : ℤ) - 9)).filter
    (fun z => let n := -140 * z ^ 2 - 58 * z + 12431
      decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) =
        [] := by native_decide

example : ((List.range 19).map (fun n => (n : ℤ) - 9)).filter
    (fun z => let n := -140 * z ^ 2 - 82 * z + 12425
      decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) =
        [8] := by native_decide

example : ((List.range 19).map (fun n => (n : ℤ) - 9)).filter
    (fun z => let n := -140 * z ^ 2 - 138 * z + 12403
      decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) =
        [] := by native_decide

/-
Aus (α) folgt für
z = −2, x₁ = 109, y₁ = 279 und x = 981, y = 2511;
aus (γ) folgt für
z = 8, x₁ = 53, y₁ = 1161 und x = 477, y = 10449.
-/

example : (109 : ℤ) ^ 2 = -140 * (-2) ^ 2 - 2 * (-2) + 12437 ∧
    |(140 : ℤ) * (-2) + 1| = 279 ∧
    (9 : ℤ) * 109 = 981 ∧ (9 : ℤ) * 279 = 2511 := by norm_num

example : (53 : ℤ) ^ 2 = -140 * 8 ^ 2 - 82 * 8 + 12425 ∧
    (140 : ℤ) * 8 + 41 = 1161 ∧
    (9 : ℤ) * 53 = 477 ∧ (9 : ℤ) * 1161 = 10449 ∧
    (1161 : ℤ) < 1320 ∧ (8 : ℤ) < 10 := by norm_num

/-
Um fernere Werthe von x zu finden, bilde man aus I die
p-Function:
x = 477−9(1161q+3710)/(q²+35);
hier ist p = 2q, S = 9.5.7.13.151.887; für
q =     2       28      −56
wird
x =   915       79      651
y =  4881    11839     9039.
-/

example (q : ℚ) :
    477 - 2 * (10449 * (2 * q) + 140 * 477) / ((2 * q) ^ 2 + 140) =
      477 - 9 * (1161 * q + 3710) / (q ^ 2 + 35) := by
  have h : q ^ 2 + 35 ≠ 0 := by positivity
  have h' : (2 * q) ^ 2 + 140 ≠ 0 := by positivity
  field_simp
  ring

example : (9 * 5 * 7 * 13 * 151 * 887 : ℤ) % (2 ^ 2 + 35) = 0 ∧
    (9 * 5 * 7 * 13 * 151 * 887 : ℤ) % (28 ^ 2 + 35) = 0 ∧
    (9 * 5 * 7 * 13 * 151 * 887 : ℤ) % ((-56) ^ 2 + 35) = 0 := by norm_num

example : ([2, 28, -56] : List ℚ).map
    (fun q => |477 - 9 * (1161 * q + 3710) / (q ^ 2 + 35)|) =
      [915, 79, 651] := by norm_num

/-
Nun suche man entsprechende Werthe für q durch Addition
und Subtraction der letzt gefundenen Wurzeln; da ergibt sich für
q = (9039+4881)/[2(651+915)] = 40/9, x = 981,
wie aus (α), und benützt man auch diesen Werth, so wird für
q = (11839−2511)/[2(79+981)] = 22/5
x = 983 und y = 2399.
-/

example : ((9039 : ℚ) + 4881) / (2 * (651 + 915)) = 40 / 9 ∧
    |477 - 9 * (1161 * ((40 : ℚ) / 9) + 3710) / ((40 / 9) ^ 2 + 35)| = 981 := by
  norm_num

example : ((11839 : ℚ) - 2511) / (2 * (79 + 981)) = 22 / 5 ∧
    |477 - 9 * (1161 * ((22 : ℚ) / 5) + 3710) / ((22 / 5) ^ 2 + 35)| = 983 := by
  norm_num

/-
Ausser diesen sechs Paaren von Wurzeln, besitzt die
Gleichung I keine anderen in ganzen Zahlen.
-/

example : ([(477, 10449), (981, 2511), (915, 4881), (79, 11839),
    (651, 9039), (983, 2399)] : List (ℤ × ℤ)).all
      (fun (x, y) => decide (y ^ 2 = -140 * x ^ 2 + 141035661)) = true := by decide

example : ((11875 : ℤ) + 1) ^ 2 > 141035661 ∧
    (141035661 - (11875 : ℤ) ^ 2) % 140 ≠ 0 := by norm_num

example : ((List.range 11875).filter fun y =>
    let n : ℤ := (141035661 - (y : ℤ) ^ 2) / 140
    decide ((141035661 - (y : ℤ) ^ 2) % 140 = 0 ∧ 0 ≤ n ∧
      (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) =
        [2399, 2511, 4881, 9039, 10449, 11839] := by native_decide

/-
Seite 53

Weil hier die p-Function durch 4 abgekürzt wurde, was daran
zu erkennen ist, dass in ihrem Nenner anstatt 140, die Zahl 35
steht, so mussten nach §. 9, 3 die zwei letzt gefundenen Werthe
von p durch 2 dividirt und erst hierauf gleich q gesetzt werden.
-/

end Beispiel02

end Kunerth1877.Paragraf13
