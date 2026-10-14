/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf24

/-
Seite 370
§. 24.
-/

namespace Beispiel14

/-
14. Exempel:
y² = 194x²+63x+479 = (5x−21)²+(13x+2)(13x+19),
-/

example (x : ℚ) : 194 * x ^ 2 + 63 * x + 479 = (5 * x - 21) ^ 2 + (13 * x + 2) * (13 * x + 19) := by ring

/-
D = −5.73547 x = −2/13, y = −283/13,
13x = −2+(−566p+43)/(p²−194);
-/

example : (63 ^ 2 - 4 * 194 * 479 : ℤ) = -5 * 73547 := by norm_num

example : (-283 / 13 : ℚ) ^ 2 = 194 * (-2 / 13) ^ 2 + (63) * (-2 / 13) + (479) := by norm_num

example (p : ℚ) : (-2) + (2 * (-283) * p + (2 * 194 * (-2) + (63) * 13)) / (p ^ 2 - 194) = (-2) + 1 * ((-566) * p + (43)) / (p ^ 2 - 194) := by ring

/-
I   194   VI
13       25
 1 ...    2
12       25
 1 ...    1
-/

example :
    let step := fun (s : ℤ × ℤ × List (ℤ × Bool)) (q : ℤ) =>
      let m := q * s.2.1 - s.1
      let d := (194 - m ^ 2) / s.2.1
      (m, d, s.2.2 ++ [(d, (194 - m ^ 2) % s.2.1 == 0)])
    (([13, 1, 12, 1] : List ℤ).foldl step (0, 1, [])).2.2 = [(25, true), (2, true), (25, true), (1, true)] := by norm_num

/-
streicht man nach §. 14 den grösseren Factor in D, so sind ±65
die allein möglichen Zahlenglieder; also
v² = 194w²+65 = (14w+1)²−2(w−2)(w+16)
und v = 29, respective 223;
-/

/- Rechenschritt: Nach Wegfall von 73547 werden die Divisoren von 5
mit n = 13 multiplicirt und nach dem Kriterium des §. 23 mit der
angegebenen VI. Reihe verglichen. -/

example :
    let n : ℕ := 13
    let D : ℤ := -5 * 73547
    let S : ℤ := (n : ℤ) ^ 2 * D
    let candidates := (S.natAbs / n ^ 2 / 73547).divisors.biUnion fun d =>
      ({(n : ℤ) * d, -((n : ℤ) * d)} : Finset ℤ)
    candidates.filter (fun N =>
      ¬ (N ^ 2 < 194 ∧ |N| ∉ ([25, 2, 25, 1] : List ℤ))) =
        {-65, 65} := by decide

example (w : ℚ) : 194 * w ^ 2 + 65 = (14 * w + 1) ^ 2 - 2 * (w - 2) * (w + 16) := by ring

example : (29 : ℤ) ^ 2 = 194 * 2 ^ 2 + 65 := by norm_num

example : (223 : ℤ) ^ 2 = 194 * (-16) ^ 2 + 65 := by norm_num

/-
diese Zahlen entsprechen nicht.
-/

example : ([29/2, -29/2, 223/16, -223/16] : List ℚ).all
    (fun p => ((-2 + (-566*p+43)/(p^2-194))/13).den != 1) := by norm_num

/-
Also
v² = 194w²−65 = (14w+1)²−2(w+3)(w+11), v = 41
beziehungsweise 153;
-/

example (w : ℚ) : 194 * w ^ 2 - 65 = (14 * w + 1) ^ 2 - 2 * (w + 3) * (w + 11) := by ring

/-
für p = −41/3 oder 153/11 wird
x = −83 oder 1121, y = 1154 respective 15616.
-/

example : (-2 + (-566 * (-41 / 3) + 43) / ((-41 / 3) ^ 2 - 194) : ℚ) = 13 * (-83) := by norm_num

example : (1154 : ℚ) ^ 2 = 194 * (-83) ^ 2 + (63) * (-83) + (479) := by norm_num

example : (-2 + (-566 * (153 / 11) + 43) / ((153 / 11) ^ 2 - 194) : ℚ) = 13 * (1121) := by norm_num

example : (15616 : ℚ) ^ 2 = 194 * (1121) ^ 2 + (63) * (1121) + (479) := by norm_num

/-
Nach §. 21 ist für
x = −2/13 α = −13p+5, β = −2p−21,
x = −(2p²+42p−19)/(13p²−10p−13);
für p = +1 ist
x = 5/2, α = −8, β = −23, y = 86/2,
-/

example : (-(2 * 1 ^ 2 + 42 * 1 - 19) / (13 * 1 ^ 2 - 10 * 1 - 13) : ℚ) = 5 / 2 := by norm_num

example : (-13 * 1 + 5 : ℤ) = -8 := by norm_num

example : (-2 * 1 - 21 : ℤ) = -23 := by norm_num

example : (86 / 2 : ℚ) ^ 2 = 194 * (5 / 2) ^ 2 + (63) * (5 / 2) + (479) := by norm_num

/-
2x = 5+2(86p+1033)/(p²−194),
S₁ = −2D, p = −14 und 14, x = −83, respective 1121.
-/

example : (5 + 2 * (86 * (-14) + 1033) / ((-14) ^ 2 - 194) : ℚ) = 2 * (-83) := by norm_num

example : (5 + 2 * (86 * (14) + 1033) / ((14) ^ 2 - 194) : ℚ) = 2 * (1121) := by norm_num

example : (-2 * (-5 * 73547) : ℤ) = 735470 := by norm_num

/-
Oder:
K² = 194Δ²−D(α²−194), α = 14, K² = 194Δ²−735470,
-/

/-
Redaktionelle Nachrechnung: Bei dem oben angegebenen D = −5.73547
ergiebt −D(14²−194) den Werth +735470. Vor D dürfte daher ein
Pluszeichen stehen, damit das anschließende Zahlenglied −735470
folgt.
-/

example : (-(-5 * 73547) * (14 ^ 2 - 194) : ℤ) ≠ -735470 := by norm_num

example : ((-5 * 73547) * (14 ^ 2 - 194) : ℤ) = -735470 := by norm_num

/-
K = 194z+r, Δ² = 194z²+176z+3831, z = 11, Δ = 171,
K = 2222, β = 8, y² = (14x+8)²−(2x−5)(x+83).
-/

example : (171 : ℤ) ^ 2 = 194 * 11 ^ 2 + 176 * 11 + 3831 := by norm_num

example : (2222 : ℤ) ^ 2 = 194 * 171 ^ 2 - 735470 := by norm_num

example : ((2222 + 14 * 63) / (2 * 194) : ℚ) = 8 := by norm_num

example (x : ℚ) : 194 * x ^ 2 + 63 * x + 479 = (14 * x + 8) ^ 2 - (2 * x - 5) * (x + 83) := by ring

end Beispiel14

namespace Beispiel15

/-
Seite 371

15. Exempel:
y² = 290x²+199x−123 = (15x+9)²+(5x−12)(13x+17)
D = 11.73.227.
-/

example (x : ℚ) : 290 * x ^ 2 + 199 * x - 123 = (15 * x + 9) ^ 2 + (5 * x - 12) * (13 * x + 17) := by ring

example : (199 ^ 2 - 4 * 290 * (-123) : ℤ) = 11 * 73 * 227 := by norm_num

/-
In der VI. Reihe stehen lauter Einser.
-/

example :
    let step := fun (s : ℤ × ℤ × List (ℤ × Bool)) (q : ℤ) =>
      let m := q * s.2.1 - s.1
      let d := (290 - m ^ 2) / s.2.1
      (m, d, s.2.2 ++ [(d, (290 - m ^ 2) % s.2.1 == 0)])
    (([17, 34] : List ℤ).foldl step (0, 1, [])).2.2 = [(1, true), (1, true)] := by norm_num

example :
    let step := fun (s : ℤ × ℤ) =>
      let q := (17 + s.1) / s.2
      let m := q * s.2 - s.1
      (m, (290 - m ^ 2) / s.2)
    ∀ k : ℕ, ((step^[k + 1]) (0, 1)).2 = 1 := by
  let step := fun (s : ℤ × ℤ) =>
    let q := (17 + s.1) / s.2
    let m := q * s.2 - s.1
    (m, (290 - m ^ 2) / s.2)
  change ∀ k : ℕ, ((step^[k + 1]) (0, 1)).2 = 1
  have hstart : step (0, 1) = (17, 1) := by norm_num [step]
  have hcycle : step (17, 1) = (17, 1) := by norm_num [step]
  intro k
  have hstate : (step^[k + 1]) (0, 1) = (17, 1) := by
    induction k with
    | zero => simpa using hstart
    | succ k ih => rw [Function.iterate_succ_apply', ih, hcycle]
  exact congrArg Prod.snd hstate

/-
x = 12/5, y = 225/5, also 5x = 12+5(90p+1591)/(p²−290),
S₁ = 5D,
-/

example : (225 / 5 : ℚ) ^ 2 = 290 * (12 / 5) ^ 2 + (199) * (12 / 5) + (-123) := by norm_num

example (p : ℚ) : (12) + (2 * (225) * p + (2 * 290 * (12) + (199) * 5)) / (p ^ 2 - 290) = (12) + 5 * ((90) * p + (1591)) / (p ^ 2 - 290) := by ring

/-
v² = 290w²−4015 = (17w+7)²+(w+16)(w−254);
v = 265, respective 4325;
-/

example (w : ℚ) : 290 * w ^ 2 - 4015 = (17 * w + 7) ^ 2 + (w + 16) * (w - 254) := by ring

/-
für p = −265/16, 4325/254 wird
x = −4 respective −50188, y = 61, respective
(4325/254)(−50188−12/5)−225/5 = −854665.
-/

example : (12 + 5 * (90 * (-265 / 16) + 1591) / ((-265 / 16) ^ 2 - 290) : ℚ) = 5 * (-4) := by norm_num

example : (61 : ℚ) ^ 2 = 290 * (-4) ^ 2 + (199) * (-4) + (-123) := by norm_num

example : (12 + 5 * (90 * (4325 / 254) + 1591) / ((4325 / 254) ^ 2 - 290) : ℚ) = 5 * (-50188) := by norm_num

example : (-854665 : ℚ) ^ 2 = 290 * (-50188) ^ 2 + (199) * (-50188) + (-123) := by norm_num

example : ((4325 / 254) * (-50188 - 12 / 5) - 225 / 5 : ℚ) = -854665 := by norm_num

/-
Die Gleichung
v² = 290w²+4015 = (17w+16)²+(w−7)(w−537)
führt auf p = 135/7, x = 43, y = 738.
-/

example (w : ℚ) : 290 * w ^ 2 + 4015 = (17 * w + 16) ^ 2 + (w - 7) * (w - 537) := by ring

example : (12 + 5 * (90 * (135 / 7) + 1591) / ((135 / 7) ^ 2 - 290) : ℚ) = 5 * (43) := by norm_num

example : (738 : ℚ) ^ 2 = 290 * (43) ^ 2 + (199) * (43) + (-123) := by norm_num

/-
Die äquivalenten Gleichungen v² = 290w²±5.227 leisten dasselbe.
-/

example :
    let equivalent := fun p : ℚ => -(7955*p + 130500) / (450*p + 7955)
    let x := fun p : ℚ => (12 + 5*(90*p + 1591)/(p^2-290))/5
    let trials : List ℚ := [-265/16, 4325/254, 135/7]
    (trials.map fun p =>
      let q := equivalent p
      (q.num^2 - 290*(q.den : ℤ)^2, x q)) =
        [(-5*227, -4), (-5*227, -50188), (5*227, 43)] := by
  norm_num

end Beispiel15

end Kunerth1880.Paragraf24
