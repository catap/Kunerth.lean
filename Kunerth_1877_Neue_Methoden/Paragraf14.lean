/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf14

/-
Seite 53

§. 14.
1. Ist in der möglichst reducirten Gleichung
y² = −ax²+b    I
die obere Grenze von y eine grosse Zahl, so kann für y = az+r
auch z einen grösseren Werth g erfordern und die Rechnung wird
dann lästig. In diesem Falle setze man 4z oder 8z anstatt z,
wodurch der Werth dieser Unbekannten verkleinert wird.
Für y = 8az+r ist
x² = −a(8z)²−2r(8z)+(b−r²)/a
-/

example (a b z r : ℚ) (ha : a ≠ 0) :
    (b - (8 * a * z + r) ^ 2) / a =
      -a * (8 * z) ^ 2 - 2 * r * (8 * z) + (b - r ^ 2) / a := by
  field_simp
  ring

/-
und wenn b = ac+d ist, so folgt:
x² = −a(8z)²−2r(8z)+c−(r²−d)/a;    II
-/

example (a c d z r : ℚ) (ha : a ≠ 0) :
    -a * (8 * z) ^ 2 - 2 * r * (8 * z) + (a * c + d - r ^ 2) / a =
      -a * (8 * z) ^ 2 - 2 * r * (8 * z) + c - (r ^ 2 - d) / a := by
  field_simp
  ring

/-
hätte die Congruenz r² ≡ d (mod. a) innerhalb der ersten Periode
n Wurzeln, so wären wegen r < 8a die Wurzeln der ersten acht
Perioden in II einzusetzen, was 8n Gleichungen gäbe; weil z
aber positiv oder negativ genommen werden kann, so kann r
immer kleiner als 4a sein, und man braucht nur die Wurzeln der
ersten vier Perioden für r in II zu setzen.
-/

example (a z r : ℤ) : 8 * a * (-z - 1) + (8 * a - r) = -(8 * a * z + r) := by
  ring

example : ((List.range (4 * 140)).filter fun r => decide (r ^ 2 % 140 = 81)).length =
    4 * 8 := by native_decide

/-
Dies gibt ein System
von 4n Gleichungen, von denen nur jene beizubehalten sind,
deren Zahlenglieder quadratische Achterreste lassen. In diesen
Gleichungen ertheile man nun der Unbekannten z alle Werthe
der natürlichen Zahlenreihe von 0 bis g/8+1, und bemerke jene
Werthe von z, welche x² zu einer Quadratzahl machen.
Um die Rechnung abzukürzen, sind im Vorhinein jene
Substitutionen auszuscheiden, für welche das Zahlenglied einen
quadratischen Nichtrest gibt.
-/

namespace Beispiel01

/-
2. Exempel. Es sei die letzt behandelte Gleichung auf
diese Art zu lösen:
y² = −140x²+141035661,    I
y < 11875, somit z₁ < 86; man setze daher
-/

example : (11839 : ℤ) < 11875 ∧ (11875 : ℚ) / 140 < 86 ∧ (86 : ℚ) / 8 + 1 < 12 := by norm_num

/-
Seite 54

y = 140.8z+r,
jetzt ist z < 12
x² = −140(8z)²−2r(8z)+1007397−(r²−81)/140;    II
-/

example (z r : ℚ) : (141035661 - (140 * 8 * z + r) ^ 2) / 140 =
    -140 * (8 * z) ^ 2 - 2 * r * (8 * z) + 1007397 - (r ^ 2 - 81) / 140 := by
  ring

/-
Da es hier in der ersten Periode acht Werthe von r gibt, so
müssen 32 aufeinander folgende Werthe für r und für den mit k
zu bezeichnenden Bruch genommen werden; diese sind;
k =    0     2    18    26   **44**   56    104    122
r =    9    19    51    61     79    89    121    131
k =  158 **180** **260** 288   342   374    486  **524**
r =  149   159   191   201    219   229    261    271
k = **596** 638  782   830    920 **972** **1148** 1206
r =  289   299   331   341    359   369    401    411
k = 1314  1376  1584 **1652** 1778  1850   2090   2168
r =  429   439   471   481    499   509    541    551
-/

example : ((List.range (4 * 140)).filter fun r => decide (r ^ 2 % 140 = 81)) =
    [9, 19, 51, 61, 79, 89, 121, 131, 149, 159, 191, 201, 219, 229, 261, 271, 289, 299, 331, 341, 359, 369, 401, 411, 429, 439, 471, 481, 499, 509, 541, 551] := by native_decide

example : ([9, 19, 51, 61, 79, 89, 121, 131, 149, 159, 191, 201, 219, 229, 261, 271, 289, 299, 331, 341, 359, 369, 401, 411, 429, 439, 471, 481, 499, 509, 541, 551] : List ℚ).map (fun r => (r ^ 2 - 81) / 140) =
    [0, 2, 18, 26, 44, 56, 104, 122, 158, 180, 260, 288, 342, 374, 486, 524, 596, 638, 782, 830, 920, 972, 1148, 1206, 1314, 1376, 1584, 1652, 1778, 1850, 2090, 2168] := by norm_num

/-
Da x eine ungerade Zahl bezeichnet und der Achterrest des
Zahlengliedes in II 5 ist, so muss der Achterrest von k 4 sein und
es können sonach nur die hervorgehobenen Werthe von k
gebraucht werden; dies gibt folgende acht Gleichungen:
-/

example : ([0, 2, 18, 26, 44, 56, 104, 122, 158, 180, 260, 288, 342, 374, 486, 524, 596, 638, 782, 830, 920, 972, 1148, 1206, 1314, 1376, 1584, 1652, 1778, 1850, 2090, 2168] : List ℤ).filter (fun k => decide (k % 8 = 4)) =
    [44, 180, 260, 524, 596, 972, 1148, 1652] := by decide

/-
                                      Ausgeschlossen sind:
x² = −35(16z)²− 79(16z)+1007353 (1)...z = 0, 5, 10, 11
 „        „   −159  „  +1007217 (2)...z = 0, 5, 10, 11
 „        „   −191  „  +1007137 (3)...z = 0, 5, 7, 10, 11
 „        „   −271  „  +1006873 (4)...z = 0, 5, 10, 11
 „        „   −289  „  +1006801 (5)...z = 7
 „        „   −369  „  +1006425 (6)...z = 11
 „        „   −401  „  +1006249 (7)...z = 7, 11
 „        „   −481  „  +1005745 (8)...z = 3, 7, 9
-/

example (z : ℚ) : (141035661 - (140 * 8 * z + 79) ^ 2) / 140 =
    -35 * (16 * z) ^ 2 - 79 * (16 * z) + 1007353 := by ring

example : ([0, 5, 10, 11] : List ℤ).all (fun z =>
    [z, -z].all (fun t => let n := -35 * (16 * t) ^ 2 - 79 * (16 * t) + 1007353
      decide (n < 0 ∨ (Nat.sqrt n.toNat : ℤ) ^ 2 ≠ n))) = true := by
  native_decide

example : ((List.range 23).map (fun n => (n : ℤ) - 11)).filter
    (fun z => let n := -35 * (16 * z) ^ 2 - 79 * (16 * z) + 1007353
      decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) =
        [8] := by native_decide

example (z : ℚ) : (141035661 - (140 * 8 * z + 159) ^ 2) / 140 =
    -35 * (16 * z) ^ 2 - 159 * (16 * z) + 1007217 := by ring

example : ([0, 5, 10, 11] : List ℤ).all (fun z =>
    [z, -z].all (fun t => let n := -35 * (16 * t) ^ 2 - 159 * (16 * t) + 1007217
      decide (n < 0 ∨ (Nat.sqrt n.toNat : ℤ) ^ 2 ≠ n))) = true := by
  native_decide

example : ((List.range 23).map (fun n => (n : ℤ) - 11)).filter
    (fun z => let n := -35 * (16 * z) ^ 2 - 159 * (16 * z) + 1007217
      decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) =
        [2] := by native_decide

example (z : ℚ) : (141035661 - (140 * 8 * z + 191) ^ 2) / 140 =
    -35 * (16 * z) ^ 2 - 191 * (16 * z) + 1007137 := by ring

example : ([0, 5, 7, 10, 11] : List ℤ).all (fun z =>
    [z, -z].all (fun t => let n := -35 * (16 * t) ^ 2 - 191 * (16 * t) + 1007137
      decide (n < 0 ∨ (Nat.sqrt n.toNat : ℤ) ^ 2 ≠ n))) = true := by
  native_decide

example : ((List.range 23).map (fun n => (n : ℤ) - 11)).filter
    (fun z => let n := -35 * (16 * z) ^ 2 - 191 * (16 * z) + 1007137
      decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) =
        [] := by native_decide

example (z : ℚ) : (141035661 - (140 * 8 * z + 271) ^ 2) / 140 =
    -35 * (16 * z) ^ 2 - 271 * (16 * z) + 1006873 := by ring

example : ([0, 5, 10, 11] : List ℤ).all (fun z =>
    [z, -z].all (fun t => let n := -35 * (16 * t) ^ 2 - 271 * (16 * t) + 1006873
      decide (n < 0 ∨ (Nat.sqrt n.toNat : ℤ) ^ 2 ≠ n))) = true := by
  native_decide

example : ((List.range 23).map (fun n => (n : ℤ) - 11)).filter
    (fun z => let n := -35 * (16 * z) ^ 2 - 271 * (16 * z) + 1006873
      decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) =
        [2] := by native_decide

example (z : ℚ) : (141035661 - (140 * 8 * z + 289) ^ 2) / 140 =
    -35 * (16 * z) ^ 2 - 289 * (16 * z) + 1006801 := by ring

example : ([7] : List ℤ).all (fun z =>
    [z, -z].all (fun t => let n := -35 * (16 * t) ^ 2 - 289 * (16 * t) + 1006801
      decide (n < 0 ∨ (Nat.sqrt n.toNat : ℤ) ^ 2 ≠ n))) = true := by
  native_decide

example : ((List.range 23).map (fun n => (n : ℤ) - 11)).filter
    (fun z => let n := -35 * (16 * z) ^ 2 - 289 * (16 * z) + 1006801
      decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) =
        [] := by native_decide

example (z : ℚ) : (141035661 - (140 * 8 * z + 369) ^ 2) / 140 =
    -35 * (16 * z) ^ 2 - 369 * (16 * z) + 1006425 := by ring

example : ([11] : List ℤ).all (fun z =>
    [z, -z].all (fun t => let n := -35 * (16 * t) ^ 2 - 369 * (16 * t) + 1006425
      decide (n < 0 ∨ (Nat.sqrt n.toNat : ℤ) ^ 2 ≠ n))) = true := by
  native_decide

example : ((List.range 23).map (fun n => (n : ℤ) - 11)).filter
    (fun z => let n := -35 * (16 * z) ^ 2 - 369 * (16 * z) + 1006425
      decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) =
        [9] := by native_decide

example (z : ℚ) : (141035661 - (140 * 8 * z + 401) ^ 2) / 140 =
    -35 * (16 * z) ^ 2 - 401 * (16 * z) + 1006249 := by ring

example : ([7, 11] : List ℤ).all (fun z =>
    [z, -z].all (fun t => let n := -35 * (16 * t) ^ 2 - 401 * (16 * t) + 1006249
      decide (n < 0 ∨ (Nat.sqrt n.toNat : ℤ) ^ 2 ≠ n))) = true := by
  native_decide

example : ((List.range 23).map (fun n => (n : ℤ) - 11)).filter
    (fun z => let n := -35 * (16 * z) ^ 2 - 401 * (16 * z) + 1006249
      decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) =
        [4] := by native_decide

example (z : ℚ) : (141035661 - (140 * 8 * z + 481) ^ 2) / 140 =
    -35 * (16 * z) ^ 2 - 481 * (16 * z) + 1005745 := by ring

example : ([3, 7, 9] : List ℤ).all (fun z =>
    [z, -z].all (fun t => let n := -35 * (16 * t) ^ 2 - 481 * (16 * t) + 1005745
      decide (n < 0 ∨ (Nat.sqrt n.toNat : ℤ) ^ 2 ≠ n))) = true := by
  native_decide

example : ((List.range 23).map (fun n => (n : ℤ) - 11)).filter
    (fun z => let n := -35 * (16 * z) ^ 2 - 481 * (16 * z) + 1005745
      decide (0 ≤ n ∧ (Nat.sqrt n.toNat : ℤ) ^ 2 = n)) =
        [-11] := by native_decide

/-
Aus (1) kommt für z = +8,   x = 651
 „  (2)   „    „  z = +2,   x = 983
 „  (3)   „             —
 „  (4)   „    „  z = +2,   x = 981
 „  (5)   „             —
 „  (6)   „    „  z = +9,   x = 477
 „  (7)   „    „  z = +4,   x = 915
 „  (8)   „    „  z = −11,  x = 79
wie in der ersten Rechnung.
-/

example : (651 : ℤ) ^ 2 = -35 * (16 * (8)) ^ 2 - 79 * (16 * (8)) + 1007353 := by
  norm_num

example : (983 : ℤ) ^ 2 = -35 * (16 * (2)) ^ 2 - 159 * (16 * (2)) + 1007217 := by
  norm_num

example : (981 : ℤ) ^ 2 = -35 * (16 * (2)) ^ 2 - 271 * (16 * (2)) + 1006873 := by
  norm_num

example : (477 : ℤ) ^ 2 = -35 * (16 * (9)) ^ 2 - 369 * (16 * (9)) + 1006425 := by
  norm_num

example : (915 : ℤ) ^ 2 = -35 * (16 * (4)) ^ 2 - 401 * (16 * (4)) + 1006249 := by
  norm_num

example : (79 : ℤ) ^ 2 = -35 * (16 * (-11)) ^ 2 - 481 * (16 * (-11)) + 1005745 := by
  norm_num

end Beispiel01

end Kunerth1877.Paragraf14
