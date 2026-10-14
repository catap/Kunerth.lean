/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf06

/-
Seite 24.

§. 6.
Das Pell’sche Problem.

1. y² = ax² + 1; setzt man ax² + 1 = (px + 1)², so folgt:

x = −2p/(p² − a) und y = px + 1;
-/

example (a p x : ℚ) : (p * x + 1) ^ 2 - (a * x ^ 2 + 1) =
    x * ((p ^ 2 - a) * x + 2 * p) := by ring

example (a p : ℚ) (h : p ^ 2 - a ≠ 0) :
    (p * (-2 * p / (p ^ 2 - a)) + 1) ^ 2 =
      a * (-2 * p / (p ^ 2 - a)) ^ 2 + 1 := by field_simp; ring

/-
für diese p-Function ist S = 2a und wenn a eine Primzahl bedeutet, so
ist S = 2; denn in diesem Falle ist für p = v/w

x = −2vw/(v² − aw²);
-/

example (a v w : ℚ) (hw : w ≠ 0) :
    -2 * (v / w) / ((v / w) ^ 2 - a) = -2 * v * w / (v ^ 2 - a * w ^ 2) := by
  field_simp

/-
setzt man v² = aw² + 2a, so muss v = av₁ sein; dann kömmt w² = av₁² − 2,
und wäre hier v₁ = m, w = n, so wäre v = am und

x = −2amn/(2a) = −mn.
-/

example (a : ℕ) (v w : ℤ) (ha : a.Prime)
    (h : v ^ 2 = a * w ^ 2 + 2 * a) : ∃ v₁ : ℤ, v = a * v₁ := by
  have hp : Prime (a : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using ha)
  have hd : (a : ℤ) ∣ v ^ 2 := ⟨w ^ 2 + 2, by nlinarith [h]⟩
  exact hp.dvd_of_dvd_pow hd

example (a v₁ w : ℚ) (ha : a ≠ 0)
    (h : (a * v₁) ^ 2 = a * w ^ 2 + 2 * a) : w ^ 2 = a * v₁ ^ 2 - 2 := by
  apply (mul_left_cancel₀ ha)
  nlinarith [h]

example (a m n : ℚ) (ha : a ≠ 0) : -2 * a * m * n / (2 * a) = -m * n := by
  field_simp

/-
Dann aber liefert die Gleichung v² = aw² − 2 auch die Werthe w = m und v
= n, somit

Seite 25.

x = −2mn/(−2) = +mn

wie oben; daher ist der Primfactor a in der Stammzahl überflüssig und
kann weggelassen werden; also S = 2.
-/

example (m n : ℚ) : -2 * m * n / (-2) = m * n := by ring

namespace Beispiel01

/-
2. Erstes Exempel:

y² = 109x² + 1, x = −2vw/(v² − 109w²); S = 2,

v² = 109w² − 1 ... = 100w² + (3w + 1)(3w − 1),

hieraus

3w = 1 − 2(10p − 109)/(p² − 109)

S = 18 × 109 liefert kein w; somit
-/

example (w : ℚ) : 109 * w ^ 2 - 1 = 100 * w ^ 2 + (3 * w + 1) * (3 * w - 1) := by ring

private def wOf (p : ℚ) : ℚ := (1 - 2 * (10 * p - 109) / (p ^ 2 - 109)) / 3

example : ((List.range (Nat.sqrt (18 * 109 + 109) + 1)).flatMap
    (fun n => [(n : ℤ), -(n : ℤ)])).filter
    (fun p => decide (p ^ 2 - 109 ≠ 0 ∧ (18 * 109 : ℤ) % (p ^ 2 - 109) = 0 ∧
      (wOf p).den = 1 ∧ wOf p ≠ 0)) = [] := by native_decide

/-
v₁² = 109w₁² + 3 ... = (11w₁)² − 3(2w₁ + 1)(2w₁ − 1)

und

2w₁ = 1 − 2(11p₁ − 109)/(p₁² − 109)

S₁ = 24·109 gibt nichts; also
-/

example (w₁ : ℚ) : 109 * w₁ ^ 2 + 3 = (11 * w₁) ^ 2 - 3 * (2 * w₁ + 1) * (2 * w₁ - 1) := by ring

private def w₁Of (p : ℚ) : ℚ := (1 - 2 * (11 * p - 109) / (p ^ 2 - 109)) / 2

example : ((List.range (Nat.sqrt (24 * 109 + 109) + 1)).flatMap
    (fun n => [(n : ℤ), -(n : ℤ)])).filter
    (fun p => decide (p ^ 2 - 109 ≠ 0 ∧ (24 * 109 : ℤ) % (p ^ 2 - 109) = 0 ∧
      (w₁Of p).den = 1 ∧ w₁Of p ≠ 0)) = [] := by native_decide

/-
v₁₁² = 109w₁₁² − 4 ... = (10w₁₁)² + (3w + 2)(3w − 2)

3w₁₁ = 2 − 4(10p₁₁ − 109)/(p₁₁² − 109) ... S₁₁ = 36 × 109;

hier wird 109 + 12 = 121 = p₁₁²
-/

/-
Formale Zuordnung: In den Faktoren (3w + 2)(3w − 2) steht w
ohne Index; die übrige Zerlegung verwendet w₁₁. Die folgende
Nachrechnung setzt dort redaktionell w₁₁ ein und bezeichnet dieses
w₁₁ in Lean mit w₂ : ℚ. Sie prüft diese vereinheitlichte Lesart.
-/

example (w₂ : ℚ) : 109 * w₂ ^ 2 - 4 = (10 * w₂) ^ 2 + (3 * w₂ + 2) * (3 * w₂ - 2) := by ring

private def w₂Of (p : ℚ) : ℚ := (2 - 4 * (10 * p - 109) / (p ^ 2 - 109)) / 3

example : (36 * 109 : ℤ) % ((-11) ^ 2 - 109) = 0 ∧ (109 : ℤ) + 12 = (-11) ^ 2 := by norm_num

/-
und für p₁₁ = −11 ist w₁₁ = 25
v₁₁ = 261; w₁ = 913, v₁ = 9532; w = 851525, v = 8890182
x = 15,140.424,455.100, y = 158,070.671,986.249.
-/

example : |w₂Of (-11)| = 25 := by norm_num [w₂Of]

example : (261 : ℤ) ^ 2 = 109 * (25) ^ 2 + (-4) := by norm_num

example : |w₁Of (261 / 25)| = 913 := by norm_num [w₁Of]

example : (9532 : ℤ) ^ 2 = 109 * (913) ^ 2 + (3) := by norm_num

example : |wOf (9532 / 913)| = 851525 := by norm_num [wOf]

example : (8890182 : ℤ) ^ 2 = 109 * (851525) ^ 2 + (-1) := by norm_num

example : |-(2 : ℚ) * 8890182 * 851525 / (8890182 ^ 2 - 109 * 851525 ^ 2)| = 15140424455100 := by norm_num

example : |(8890182 : ℚ) / 851525 * (-2 * 8890182 * 851525 / (8890182 ^ 2 - 109 * 851525 ^ 2)) + 1| = 158070671986249 := by norm_num

example : (158070671986249 : ℤ) ^ 2 = 109 * (15140424455100 : ℤ) ^ 2 + 1 := by norm_num

/-
Hätte man

v₁² = 109w₁² − 3 ... = w² + 3(6w₁ + 1)(6w₁ − 1)

gesetzt, so käme

6w₁ = 1 − 2(q₁ − 109)/(q₁² − 109)

S₁ = 216 × 109 gibt nichts;
-/

/-
Formale Zuordnung: Der einzelne Summand w² steht im Druck ohne
Index. Die folgende Nachrechnung verwendet dort w₁² wie in den
übrigen Gliedern der Zerlegung und prüft diese redaktionell
vereinheitlichte Lesart für w₁ : ℚ.
-/

example (w₁ : ℚ) : 109 * w₁ ^ 2 - 3 = w₁ ^ 2 + 3 * (6 * w₁ + 1) * (6 * w₁ - 1) := by ring

private def wAlt₁Of (p : ℚ) : ℚ := (1 - 2 * (1 * p - 109) / (p ^ 2 - 109)) / 6

example : ((List.range (Nat.sqrt (216 * 109 + 109) + 1)).flatMap
    (fun n => [(n : ℤ), -(n : ℤ)])).filter
    (fun p => decide (p ^ 2 - 109 ≠ 0 ∧ (216 * 109 : ℤ) % (p ^ 2 - 109) = 0 ∧
      (wAlt₁Of p).den = 1 ∧ wAlt₁Of p ≠ 0)) = [] := by native_decide

/-
v₁₁² = 109w₁₁² − 12 ... = w₁₁² + 12(3w₁₁ + 1)(3w₁₁ − 1)

3w₁₁ = 1 − 2(q₁₁ − 109)/(q₁₁² − 109)

Seite 26.

S₁₁ = 216 × 109: hier ist 109 − 9 = 100 = q₁₁²
-/

example (w₂ : ℚ) : 109 * w₂ ^ 2 - 12 = w₂ ^ 2 + 12 * (3 * w₂ + 1) * (3 * w₂ - 1) := by ring

private def wAlt₂Of (p : ℚ) : ℚ := (1 - 2 * (1 * p - 109) / (p ^ 2 - 109)) / 3

example : (216 * 109 : ℤ) % (10 ^ 2 - 109) = 0 ∧ (109 : ℤ) - 9 = 10 ^ 2 := by norm_num

/-
und für q₁₁ = 10 wird

w₁₁ = 7,  w₁ = 134,  w = 851525
v₁₁ = 73, v₁ = 1399, v = 8890182

wie oben.
-/

example : |wAlt₂Of (10)| = 7 := by norm_num [wAlt₂Of]

example : (73 : ℤ) ^ 2 = 109 * (7) ^ 2 + (-12) := by norm_num

example : |wAlt₁Of (73 / 7)| = 134 := by norm_num [wAlt₁Of]

example : (1399 : ℤ) ^ 2 = 109 * (134) ^ 2 + (-3) := by norm_num

example : |wOf (-1399 / 134)| = 851525 := by norm_num [wOf]

example : (8890182 : ℤ) ^ 2 = 109 * (851525) ^ 2 + (-1) := by norm_num

/-
Hieraus ist zu ersehen, dass oft mehrere Factoren der Stammzahl dasselbe
leisten; auch kann die Zerlegung der Binome aw² + b in den Derivirten
oft auf mehrere Arten geschehen.

Wäre in der ersten Rechnung die zweite Derivirte folgender Weise zerlegt
worden:

v₁² = 109w₁² + 3 = (16w₁)² − 3(7w₁ + 1)(7w₁ − 1),

so käme

7w₁ = 1 − 2(16p₁ − 109)/(p₁² − 109)
-/

example (w₁ : ℚ) : 109 * w₁ ^ 2 + 3 = (16 * w₁) ^ 2 - 3 * (7 * w₁ + 1) * (7 * w₁ - 1) := by ring

private def wThird₁Of (p : ℚ) : ℚ := (1 - 2 * (16 * p - 109) / (p ^ 2 - 109)) / 7

/-
und weil die Stammzahl hier kein ganzzahliges w₁ liefert, so setzt man

v₁₁² = 109w₁₁² + 7 = (19w₁₁)² − 7(6w₁₁ + 1)(6w₁₁ − 1)

und

6w₁₁ = 1 − 2(19p₁₁ − 109)/(p₁₁² − 109)

S₁₁ = 504 × 109 für 109 + 12 = 121 = p₁₁² ist p₁₁ = −11
-/

example (w₂ : ℚ) : 109 * w₂ ^ 2 + 7 = (19 * w₂) ^ 2 - 7 * (6 * w₂ + 1) * (6 * w₂ - 1) := by ring

private def wThird₂Of (p : ℚ) : ℚ := (1 - 2 * (19 * p - 109) / (p ^ 2 - 109)) / 6

example : (504 * 109 : ℤ) % ((-11) ^ 2 - 109) = 0 ∧ (109 : ℤ) + 12 = (-11) ^ 2 := by norm_num

/-
und

w₁₁ = 9,  w₁ = 913
v₁₁ = 94, v₁ = 9532

wie dort.
-/

example : |wThird₂Of (-11)| = 9 := by norm_num [wThird₂Of]

example : (94 : ℤ) ^ 2 = 109 * (9) ^ 2 + (7) := by norm_num

example : |wThird₁Of (-94 / 9)| = 913 := by norm_num [wThird₁Of]

example : (9532 : ℤ) ^ 2 = 109 * (913) ^ 2 + (3) := by norm_num

end Beispiel01

/-
3. Ist für die Gleichung v² = aw² + b diese Zerlegung auszuführen, so
setze man v² = d²w² + (a − d²)w² + b und die Determinante −b(a − d²) =
c² und trachte diese Gleichung nach c und d in ganzen Zahlen aufzulösen;
gelingt dies und ist b positiv, so bestehen die Gleichungen

b = mβ² und d² − a = mγ²;
-/

example (a b d w : ℚ) : a * w ^ 2 + b = d ^ 2 * w ^ 2 + (a - d ^ 2) * w ^ 2 + b := by
  ring

example : Prop :=
  ∀ a b c d : ℤ, 0 < b → -b * (a - d ^ 2) = c ^ 2 →
    ∃ m β γ : ℤ, b = m * β ^ 2 ∧ d ^ 2 - a = m * γ ^ 2

/-
dann ist

v² = d²w² − m(γ²w² − β²) = [dw + p(γw − β)]²

und hieraus

w = (βp² − βm)/(γp² + 2dp + mγ)
-/

example (a b d m β γ w : ℚ) (hb : b = m * β ^ 2) (ha : d ^ 2 - a = m * γ ^ 2) :
    a * w ^ 2 + b = d ^ 2 * w ^ 2 - m * (γ ^ 2 * w ^ 2 - β ^ 2) := by
  rw [hb]
  nlinarith [ha]

example (d m β γ w p : ℚ) :
    (d * w + p * (γ * w - β)) ^ 2 - (d ^ 2 * w ^ 2 - m * (γ ^ 2 * w ^ 2 - β ^ 2)) =
      (γ * w - β) * ((γ * p ^ 2 + 2 * d * p + m * γ) * w - (β * p ^ 2 - β * m)) := by
  ring

/-
Seite 27.

oder

γw = β − 2β(dp + mγ)/(γp² + 2dp + mγ)
-/

example (d m β γ p : ℚ) (h : γ * p ^ 2 + 2 * d * p + m * γ ≠ 0) :
    γ * ((β * p ^ 2 - β * m) / (γ * p ^ 2 + 2 * d * p + m * γ)) =
      β - 2 * β * (d * p + m * γ) / (γ * p ^ 2 + 2 * d * p + m * γ) := by
  rw [← mul_div_assoc]
  have hn : γ * (β * p ^ 2 - β * m) =
      β * (γ * p ^ 2 + 2 * d * p + m * γ) - 2 * β * (d * p + m * γ) := by ring
  rw [hn, sub_div, mul_div_cancel_right₀ β h]

/-
und für p = (q − d)/γ wird

γw = β − 2β(dq − a)/(q² − a) M)
-/

example (a d m β γ q : ℚ) (hγ : γ ≠ 0) (ha : d ^ 2 - a = m * γ ^ 2)
    (hq : q ^ 2 - a ≠ 0) :
    β - 2 * β * (d * ((q - d) / γ) + m * γ) /
      (γ * ((q - d) / γ) ^ 2 + 2 * d * ((q - d) / γ) + m * γ) =
        β - 2 * β * (d * q - a) / (q ^ 2 - a) := by
  have he : γ * ((q - d) / γ) ^ 2 + 2 * d * ((q - d) / γ) + m * γ =
      (q ^ 2 - a) / γ := by field_simp; nlinarith [ha]
  rw [he]
  field_simp
  linear_combination 2 * β * ha

/-
Für ein negatives b ist

−b = mβ², a − d² = mγ²
-/

example : Prop :=
  ∀ a b c d : ℤ, b < 0 → -b * (a - d ^ 2) = c ^ 2 →
    ∃ m β γ : ℤ, -b = m * β ^ 2 ∧ a - d ^ 2 = m * γ ^ 2

/-
und

v² = d²w² + m(γ²w² − β²) = [dw + p(γw − β)]²

und hieraus

γw = β − 2β(dp − mγ)/(γp² + 2dp − mγ);
-/

example (a b d m β γ w : ℚ) (hb : -b = m * β ^ 2) (ha : a - d ^ 2 = m * γ ^ 2) :
    a * w ^ 2 + b = d ^ 2 * w ^ 2 + m * (γ ^ 2 * w ^ 2 - β ^ 2) := by
  nlinarith [ha, hb]

example (d m β γ w p : ℚ) :
    (d * w + p * (γ * w - β)) ^ 2 - (d ^ 2 * w ^ 2 + m * (γ ^ 2 * w ^ 2 - β ^ 2)) =
      (γ * w - β) * ((γ * p ^ 2 + 2 * d * p - m * γ) * w - (β * p ^ 2 + β * m)) := by
  ring

/-
für p = (q − d)/γ wird

γw = β − 2β(dq − a)/(q² − a)

wie oben.
-/

example (a d m β γ q : ℚ) (hγ : γ ≠ 0) (ha : a - d ^ 2 = m * γ ^ 2)
    (hq : q ^ 2 - a ≠ 0) :
    β - 2 * β * (d * ((q - d) / γ) - m * γ) /
      (γ * ((q - d) / γ) ^ 2 + 2 * d * ((q - d) / γ) - m * γ) =
        β - 2 * β * (d * q - a) / (q ^ 2 - a) := by
  have he : γ * ((q - d) / γ) ^ 2 + 2 * d * ((q - d) / γ) - m * γ =
      (q ^ 2 - a) / γ := by field_simp; nlinarith [ha]
  rw [he]
  field_simp
  linear_combination -2 * β * ha

/-
4. Wäre a negativ, so wird

γw = β − 2β(dq + a)/(q² + a) N)

Mittelst der Formeln M) und N) können nach erfolgter Zerlegung jener
Binome die p-Functionen sofort gebildet werden.
-/

example (a d β q : ℚ) : β - 2 * β * (d * q - (-a)) / (q ^ 2 - (-a)) =
    β - 2 * β * (d * q + a) / (q ^ 2 + a) := by ring

/-
5. Ist obige Zerlegung nicht möglich, so gelingt es manchmal eine
bestimmte Quadratzahl abzusondern;

v² = aw² + (b − d²) + d² = a(w² − c²) + d²,

woraus w₁ = c und v₁ = d.
-/

example (a b c d w : ℚ) (h : b - d ^ 2 = -a * c ^ 2) :
    a * w ^ 2 + b = a * (w ^ 2 - c ^ 2) + d ^ 2 := by nlinarith [h]

example (a c d : ℚ) : a * (c ^ 2 - c ^ 2) + d ^ 2 = d ^ 2 := by ring

/-
Für ein positives a ist

w = w₁ − 2(v₁p − aw₁)/(p² − a)
-/

example (a w w₁ v₁ p : ℚ) :
    (p * (w - w₁) + v₁) ^ 2 - (a * (w ^ 2 - w₁ ^ 2) + v₁ ^ 2) =
      (w - w₁) * ((p ^ 2 - a) * (w - w₁) + 2 * (v₁ * p - a * w₁)) := by ring

/-
und für ein negatives a ist

w = w₁ − 2(v₁p + aw₁)/(p² + a).
-/

example (a w w₁ v₁ p : ℚ) :
    (p * (w - w₁) + v₁) ^ 2 - (-a * (w ^ 2 - w₁ ^ 2) + v₁ ^ 2) =
      (w - w₁) * ((p ^ 2 + a) * (w - w₁) + 2 * (v₁ * p + a * w₁)) := by ring

/-
Seite 28.
-/

namespace Beispiel02

/-
6. Zweites Exempel

y² = 331x² + 1, x = −2vw/(v² − 331w²), S = 2

v² = 331w² − 2 = (13w)² + 2(9w + 1)(9w − 1)

9w = 1 − 2(13p − 331)/(p² − 331); S₁ = 324 × 331 liefert nichts.
-/

example (w : ℚ) : 331 * w ^ 2 - 2 = (13 * w) ^ 2 + 2 * (9 * w + 1) * (9 * w - 1) := by ring

private def wOf (p : ℚ) : ℚ := (1 - 2 * (13 * p - 331) / (p ^ 2 - 331)) / 9

example : ((List.range (Nat.sqrt (324 * 331 + 331) + 1)).flatMap
    (fun n => [(n : ℤ), -(n : ℤ)])).filter
    (fun p => decide (p ^ 2 - 331 ≠ 0 ∧ (324 * 331 : ℤ) % (p ^ 2 - 331) = 0 ∧
      (wOf p).den = 1 ∧ wOf p ≠ 0)) = [] := by native_decide

/-
v₁² = 331w₁² + 9 = (p₁w₁ + 3)²

hieraus

w₁ = 6p₁/(p₁² − 331), S₁₁ = 6;

somit kann der Nenner dieses Bruches nur solche Werthe erhalten, welche
Theiler von 6 sind. +1 führt auf die gegebene Gleichung; −1 ist
unmöglich; −2 führt auf die erste Derivirte; +2 ist unmöglich; −3
liefert nicht sofort ein brauchbares p₁; +3 ist unmöglich, ebenso −6;
somit bleibt blos +6 und da ist
-/

example (p w₁ : ℚ) : (p * w₁ + 3) ^ 2 - (331 * w₁ ^ 2 + 9) = w₁ * ((p ^ 2 - 331) * w₁ + 6 * p) := by ring

private def w₁Of (p : ℚ) : ℚ := 6 * p / (p ^ 2 - 331)

example : ((List.range 7).filter fun n => decide (n ≠ 0 ∧ 6 % n = 0)) = [1, 2, 3, 6] := by decide

example : ¬ ∃ v w : ℤ,
    v ^ 2 - 331 * w ^ 2 ∈ ([-1, 2, 3, -6] : List ℤ) := by
  rintro ⟨v, w, h⟩
  have hm : ∀ v w : ZMod 8,
      v ^ 2 - 331 * w ^ 2 ∉ ([-1, 2, 3, -6] : List (ZMod 8)) := by decide
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with h | h | h | h
  all_goals
    have hz := congrArg (fun n : ℤ => (n : ZMod 8)) h
    push_cast at hz
    apply hm v w
    rw [hz]
    simp

/-
v₁₁² = 331w₁₁² + 6 = 625w₁₁² − 6(49w₁₁² − 1)

und

7w₁₁ = 1 − 2(25p₁₁ − 331)/(p₁₁² − 331); S₁₁₁ = 12 × 49, 331 − 7 = 324 =
p₁₁²;
-/

example (w₂ : ℚ) : 331 * w₂ ^ 2 + 6 = 625 * w₂ ^ 2 - 6 * (49 * w₂ ^ 2 - 1) := by ring

private def w₂Of (p : ℚ) : ℚ := (1 - 2 * (25 * p - 331) / (p ^ 2 - 331)) / 7

example : (12 * 49 : ℤ) % (18 ^ 2 - 331) = 0 ∧ (331 : ℤ) - 7 = 18 ^ 2 := by norm_num

/-
für p₁₁ = 18 wird w₁₁ = 5, v₁₁ = 91;
für p₁ = −91/5 ist w₁ = 455, v₁ = 8278;
für p = 8278/455 wird w = 2900979, v = 52778687

und

x = 153,159.067,394.476
y = 2.778,719.023,511.331

die kleinsten Werthe.
-/

/-
Formale Zuordnung: „die kleinsten Werthe“ wird als kleinste positive
ganzzahlige Lösung in beiden Koordinaten gelesen; Null und negative
Werthe gehören nicht zu diesem Vergleich. Die folgende Proposition
hält die Behauptung für die gedruckten Zahlen fest, ohne sie zu
beweisen. Die Abweichungen und die berichtigten Zahlen folgen unten.
-/

example : Prop :=
  (2778719023511331 : ℤ) ^ 2 = 331 * (153159067394476 : ℤ) ^ 2 + 1 ∧
    ∀ x y : ℤ, 0 < x → 0 < y → y ^ 2 = 331 * x ^ 2 + 1 →
      153159067394476 ≤ x ∧ 2778719023511331 ≤ y

example : |w₂Of (18)| = 5 := by norm_num [w₂Of]

example : (91 : ℤ) ^ 2 = 331 * (5) ^ 2 + (6) := by norm_num

/-
Vermutlicher Vorzeichenfehler in der Formel für w₁: Die vorstehende
Ausmultiplizierung führt für w₁ ≠ 0 auf −6p₁/(p₁² − 331).
Für das angegebene p₁ = −91/5 liefert die Formel ohne Minuszeichen
w₁ = −455 statt 455. Danach wird die vermutete Berichtigung geprüft.
-/

example : w₁Of (-91 / 5) = -455 ∧ w₁Of (-91 / 5) ≠ 455 := by
  norm_num [w₁Of]

example : -(6 : ℚ) * (-91 / 5) / ((-91 / 5) ^ 2 - 331) = 455 := by
  norm_num

example : (8278 : ℤ) ^ 2 = 331 * (455) ^ 2 + (9) := by norm_num

/-
Zuordnung: Für p = 8278/455 ergibt die Formel w = 39121819/81.
Die folgende Nachrechnung prüft die Abweichung vom angegebenen Werth.
-/

example : |wOf (8278 / 455)| ≠ 2900979 := by norm_num [wOf]

/-
Vermutlicher Druckfehler: Vor 8278/455 fehlt wohl das Minuszeichen.
Die folgende Nachrechnung prüft diese vermutete Berichtigung.
-/

example : wOf (-8278 / 455) = 2900979 := by norm_num [wOf]

example : (52778687 : ℤ) ^ 2 = 331 * (2900979) ^ 2 + (-2) := by norm_num

/-
Zuordnung: Die angegebenen Zahlen w = 2900979 und v = 52778687
erfüllen die Derivirte, ergeben aber andere Endwerthe als angegeben.
Die folgenden Nachrechnungen prüfen diese Abweichungen.
-/

example : |-(2 : ℚ) * 52778687 * 2900979 / (52778687 ^ 2 - 331 * 2900979 ^ 2)| ≠ 153159067394476 := by norm_num

example : |(52778687 : ℚ) / 2900979 * (-2 * 52778687 * 2900979 / (52778687 ^ 2 - 331 * 2900979 ^ 2)) + 1| ≠ 2778719023511331 := by norm_num

example : (2778719023511331 : ℤ) ^ 2 ≠ 331 * (153159067394476 : ℤ) ^ 2 + 1 := by norm_num

/-
Vermutliche Druck- oder Rechenfehler in den Endwerthen.
Gesonderte Nachrechnung nach den angegebenen Formeln:

x = 153,109.862,634.573,
y = 2.785,589.801,443.970.

Die Nachrechnungen prüfen die Werthe und die Gleichung. Die Kleinheit
wird anschliessend als redaktionell berichtigte Proposition unter
derselben positiven Lesart festgehalten, nicht bewiesen.
-/

example : |-(2 : ℚ) * 52778687 * 2900979 / (52778687 ^ 2 - 331 * 2900979 ^ 2)| = 153109862634573 := by norm_num

example : |(52778687 : ℚ) / 2900979 * (-2 * 52778687 * 2900979 / (52778687 ^ 2 - 331 * 2900979 ^ 2)) + 1| = 2785589801443970 := by norm_num

example : (2785589801443970 : ℤ) ^ 2 = 331 * (153109862634573 : ℤ) ^ 2 + 1 := by norm_num

example : Prop :=
  (2785589801443970 : ℤ) ^ 2 = 331 * (153109862634573 : ℤ) ^ 2 + 1 ∧
    ∀ x y : ℤ, 0 < x → 0 < y → y ^ 2 = 331 * x ^ 2 + 1 →
      153109862634573 ≤ x ∧ 2785589801443970 ≤ y

/-
Würde man die zweite Derivirte so zerlegt haben:

v₁² = 331w² + 9 = (166w₁)² − 9(55²w₁² − 1)

so wäre

55w₁ = 1 − 2(166p₁ − 331)/(p₁² − 331)

und weil S₁₁ nichts gibt, so setze man

v₁₁² = 331w₁₁² − 55;
-/

/-
Vermutlich fehlt in 331w² der Index 1. Die folgende Nachrechnung
prüft die redaktionelle Berichtigung 331w₁² für w₁ : ℚ; die
gedruckte Formel bleibt oben unverändert.
-/

example (w₁ : ℚ) : 331 * w₁ ^ 2 + 9 = (166 * w₁) ^ 2 - 9 * (55 ^ 2 * w₁ ^ 2 - 1) := by ring

private def wAlt₁Of (p : ℚ) : ℚ := (1 - 2 * (166 * p - 331) / (p ^ 2 - 331)) / 55

/-
Seite 29.

da sich die p-Function für w₁₁ nicht finden lässt, so sei

v₁₁ = 331z + r,

daher

w₁₁² = 331z² + 2rz + (r² + 55)/331,

also

r² ≡ −55 (mod. 331);

da findet sich r₁ = 40, r₂ = 291.
-/

example (z r : ℚ) : ((331 * z + r) ^ 2 + 55) / 331 = 331 * z ^ 2 + 2 * r * z + (r ^ 2 + 55) / 331 := by ring

example : (40 : ℤ) ^ 2 % 331 = (-55) % 331 ∧ (291 : ℤ) ^ 2 % 331 = (-55) % 331 ∧ ((40 : ℚ) ^ 2 + 55) / 331 = 5 ∧ ((291 : ℚ) ^ 2 + 55) / 331 = 256 := by norm_num

/-
Für r = 40 ist

w₁₁² = 331z² + 80z + 5

und für z = −1 ist w₁₁ = 16, v₁₁ = 291, w₁ = 455 wie oben.
-/

example (z : ℚ) : ((331 * z + 40) ^ 2 + 55) / 331 = 331 * z ^ 2 + 80 * z + 5 ∧
    ((331 * z + 291) ^ 2 + 55) / 331 = 331 * z ^ 2 + 582 * z + 256 := by constructor <;> ring

example : (16 : ℤ) ^ 2 = 331 * (-1) ^ 2 + 80 * (-1) + 5 ∧ |(331 : ℤ) * (-1) + 40| = 291 ∧ (16 : ℤ) ^ 2 = 331 * 0 ^ 2 + 582 * 0 + 256 ∧ (331 : ℤ) * 0 + 291 = 291 := by norm_num

example : (291 : ℤ) ^ 2 = 331 * (16) ^ 2 + (-55) := by norm_num

example : |wAlt₁Of (291 / 16)| = 455 := by norm_num [wAlt₁Of]

/-
Hätte man den Werth von z nicht so leicht gefunden, so wäre mit
Zuhilfenahme der Determinante folgende Zerlegung zu machen:

w₁₁² = 16z² + 5(9z + 1)(7z + 1) = [4z + p(7z + 1)]²

und hieraus

7z = −1 + 2(4p − 51)/(p² − 331); S = 2·5·7·7·11; 331 − 7 = 324 = p²;

für p = 18 wird z = −1, wie zuvor.
-/

example (z : ℚ) : 331 * z ^ 2 + 80 * z + 5 = 16 * z ^ 2 + 5 * (9 * z + 1) * (7 * z + 1) := by ring

example (z p : ℚ) :
    (4 * z + p * (7 * z + 1)) ^ 2 - (331 * z ^ 2 + 80 * z + 5) =
      (7 * z + 1) * ((7 * p ^ 2 + 8 * p - 45) * z + p ^ 2 - 5) := by ring

example : ((-1 : ℚ) + 2 * (4 * 18 - 51) / (18 ^ 2 - 331)) / 7 = -1 ∧ (2 * 5 * 7 * 7 * 11 : ℤ) % (18 ^ 2 - 331) = 0 := by norm_num

/-
Würde man aber r = 291 gesetzt haben, so wäre

w₁₁² = 331z² + 582z + 256

und für z = 0 wird w₁₁ = 16, v₁₁ = 291 wie oben.
-/

end Beispiel02

namespace Beispiel03

/-
7. Drittes Exempel.

y² = 397x² + 1, x = −2vw/(v² − 397w²)

v² = 397w² − 1 = 36w² + 361w² − 1 = (6w)² + (19²w² − 1)

19w = 1 − 2(6p − 397)/(p² − 397); S₁ = 2·19²·397 liefert nichts.
-/

example (w : ℚ) : 397 * w ^ 2 - 1 = 36 * w ^ 2 + 361 * w ^ 2 - 1 ∧
    397 * w ^ 2 - 1 = (6 * w) ^ 2 + (19 ^ 2 * w ^ 2 - 1) := by constructor <;> ring

private def wOf (p : ℚ) : ℚ := (1 - 2 * (6 * p - 397) / (p ^ 2 - 397)) / 19

example : ((List.range (Nat.sqrt (2 * 19 ^ 2 * 397 + 397) + 1)).flatMap
    (fun n => [(n : ℤ), -(n : ℤ)])).filter
    (fun p => decide (p ^ 2 - 397 ≠ 0 ∧ (2 * 19 ^ 2 * 397 : ℤ) % (p ^ 2 - 397) = 0 ∧
      (wOf p).den = 1 ∧ wOf p ≠ 0)) = [] := by native_decide

/-
v₁² = 397w₁² + 19 = (44w₁)² − 19(81w₁² − 1),

9w₁ = 1 − 2(44p₁ − 397)/(p₁² − 397);

da auch S₁₁ nichts bietet, so kömmt
-/

example (w₁ : ℚ) : 397 * w₁ ^ 2 + 19 = (44 * w₁) ^ 2 - 19 * (81 * w₁ ^ 2 - 1) := by ring

private def w₁Of (p : ℚ) : ℚ := (1 - 2 * (44 * p - 397) / (p ^ 2 - 397)) / 9

/-
Seite 30.

v₁₁² = 397w₁₁² + 9 = (p₁₁w₁₁ + 3)², w₁₁ = −6p₁₁/(p₁₁² − 397), S = 6,
-/

example (p w₂ : ℚ) : (p * w₂ + 3) ^ 2 - (397 * w₂ ^ 2 + 9) = w₂ * ((p ^ 2 - 397) * w₂ + 6 * p) := by ring

private def w₂Of (p : ℚ) : ℚ := -6 * p / (p ^ 2 - 397)

example : (6 : ℤ) % (20 ^ 2 - 397) = 0 := by norm_num

/-
p₁₁ = 20,
w₁₁ = 40,  w₁ = 18951,  w = 1027776565
v₁₁ = 797, v₁ = 377596, v = 20478302982

und

x = 42,094.239,791.738,433.660
y = 838,721.786,045.180,184.649.
-/

example : |w₂Of (20)| = 40 := by norm_num [w₂Of]

example : (797 : ℤ) ^ 2 = 397 * (40) ^ 2 + (9) := by norm_num

example : |w₁Of (797 / 40)| = 18951 := by norm_num [w₁Of]

example : (377596 : ℤ) ^ 2 = 397 * (18951) ^ 2 + (19) := by norm_num

example : |wOf (-377596 / 18951)| = 1027776565 := by norm_num [wOf]

example : (20478302982 : ℤ) ^ 2 = 397 * (1027776565) ^ 2 + (-1) := by norm_num

example : |-(2 : ℚ) * 20478302982 * 1027776565 / (20478302982 ^ 2 - 397 * 1027776565 ^ 2)| = 42094239791738433660 := by norm_num

example : |(20478302982 : ℚ) / 1027776565 * (-2 * 20478302982 * 1027776565 / (20478302982 ^ 2 - 397 * 1027776565 ^ 2)) + 1| = 838721786045180184649 := by norm_num

example : (838721786045180184649 : ℤ) ^ 2 = 397 * (42094239791738433660 : ℤ) ^ 2 + 1 := by norm_num

end Beispiel03

/-
8. Setzt man bei diesen recurrenten Substitutionen jedes p mit seinem
eigenthümlichen Vorzeichen in die zur Bestimmung der v dienenden
Gleichungen ein, so findet man die v schneller als aus den derivirten
Gleichungen, woselbst die Quadrate der w berechnet werden müssen.
-/

namespace Beispiel04

/-
9. Viertes Exempel.

y² = 1231x² + 1, x = −2vw/(v² − 1231w²)

v² = 1231w² + 2 = (41w)² − 2(15²w² − 1),

somit

15w = 1 − 2(41p − 1231)/(p² − 1231);
-/

example (w : ℚ) : 1231 * w ^ 2 + 2 = (41 * w) ^ 2 - 2 * (15 ^ 2 * w ^ 2 - 1) := by ring

private def wOf (p : ℚ) : ℚ := (1 - 2 * (41 * p - 1231) / (p ^ 2 - 1231)) / 15

/-
da die Stammzahl den Dienst versagt, so ist

v₁² = 1231w₁² − 15 = 16w₁² + 15(81w₁² − 1)

hieraus

9w₁ = 1 − 2(4p₁ − 1231)/(p₁² − 1231),
-/

example (w₁ : ℚ) : 1231 * w₁ ^ 2 - 15 = 16 * w₁ ^ 2 + 15 * (81 * w₁ ^ 2 - 1) := by ring

private def w₁Of (p : ℚ) : ℚ := (1 - 2 * (4 * p - 1231) / (p ^ 2 - 1231)) / 9

/-
auch hier bietet S₁₁ nichts Brauchbares; daher

v₁₁² = 1231w₁₁² + 9 = (p₁₁w₁₁ + 3)²,

hieraus

w₁₁ = −6p₁₁/(p₁₁² − 1231), S₁₁₁ = 6;
-/

example (p w₂ : ℚ) : (p * w₂ + 3) ^ 2 - (1231 * w₂ ^ 2 + 9) = w₂ * ((p ^ 2 - 1231) * w₂ + 6 * p) := by ring

private def w₂Of (p : ℚ) : ℚ := -6 * p / (p ^ 2 - 1231)

example : (6 : ℤ) % (35 ^ 2 - 1231) = 0 := by norm_num

/-
für p₁₁ = 35 wird

w₁₁ = 35,   w₁ = 41479,   w = 40825882727,
v₁₁ = 1228, v₁ = 1455316, v = 1432400982351.

x = 58.479,034.523,501.522,751.177
y = 2,051.772,574.240,109.318,487.200

die kleinsten Werthe.
-/

/-
Formale Zuordnung: „die kleinsten Werthe“ wird als kleinste positive
ganzzahlige Lösung in beiden Koordinaten gelesen; Null und negative
Werthe gehören nicht zu diesem Vergleich. Die folgende Proposition
hält die Behauptung für die gedruckten Zahlen fest, ohne sie zu
beweisen. Die Abweichung und der berichtigte y-Werth folgen unten.
-/

example : Prop :=
  (2051772574240109318487200 : ℤ) ^ 2 =
      1231 * (58479034523501522751177 : ℤ) ^ 2 + 1 ∧
    ∀ x y : ℤ, 0 < x → 0 < y → y ^ 2 = 1231 * x ^ 2 + 1 →
      58479034523501522751177 ≤ x ∧ 2051772574240109318487200 ≤ y

example : |w₂Of (35)| = 35 := by norm_num [w₂Of]

example : (1228 : ℤ) ^ 2 = 1231 * (35) ^ 2 + (9) := by norm_num

example : |w₁Of (-1228 / 35)| = 41479 := by norm_num [w₁Of]

example : (1455316 : ℤ) ^ 2 = 1231 * (41479) ^ 2 + (-15) := by norm_num

example : |wOf (-1455316 / 41479)| = 40825882727 := by norm_num [wOf]

example : (1432400982351 : ℤ) ^ 2 = 1231 * (40825882727) ^ 2 + (2) := by norm_num

example : |-(2 : ℚ) * 1432400982351 * 40825882727 / (1432400982351 ^ 2 - 1231 * 40825882727 ^ 2)| = 58479034523501522751177 := by norm_num

/-
Zuordnung: Die folgenden Nachrechnungen prüfen die Abweichung des
angegebenen y-Werthes von der Formel und von der gegebenen Gleichung.
-/

example : |(1432400982351 : ℚ) / 40825882727 * (-2 * 1432400982351 * 40825882727 / (1432400982351 ^ 2 - 1231 * 40825882727 ^ 2)) + 1| ≠ 2051772574240109318487200 := by norm_num

example : (2051772574240109318487200 : ℤ) ^ 2 ≠ 1231 * (58479034523501522751177 : ℤ) ^ 2 + 1 := by norm_num

/-
Vermutlicher Druckfehler: Die Zifferngruppe 318 in y sollte wohl 813
lauten. Gesonderte Nachrechnung nach der angegebenen Formel:

y = 2,051.772,574.240,109.813,487.200.

Die Nachrechnungen prüfen den Werth und die Gleichung. Die Kleinheit
wird anschliessend als redaktionell berichtigte Proposition unter
derselben positiven Lesart festgehalten, nicht bewiesen.
-/

example : |(1432400982351 : ℚ) / 40825882727 * (-2 * 1432400982351 * 40825882727 / (1432400982351 ^ 2 - 1231 * 40825882727 ^ 2)) + 1| = 2051772574240109813487200 := by norm_num

example : (2051772574240109813487200 : ℤ) ^ 2 = 1231 * (58479034523501522751177 : ℤ) ^ 2 + 1 := by norm_num

example : Prop :=
  (2051772574240109813487200 : ℤ) ^ 2 =
      1231 * (58479034523501522751177 : ℤ) ^ 2 + 1 ∧
    ∀ x y : ℤ, 0 < x → 0 < y → y ^ 2 = 1231 * x ^ 2 + 1 →
      58479034523501522751177 ≤ x ∧ 2051772574240109813487200 ≤ y

end Beispiel04

end Kunerth1877.Paragraf06
