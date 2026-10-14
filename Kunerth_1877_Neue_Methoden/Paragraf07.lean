/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf07

/-
Seite 31.

§. 7.

Wenn a eine zusammengesetzte Zahl ist, so setze man zur Auffindung der
ersten derivirten Gleichung den Nenner v² − aw² den aufeinanderfolgenden
Factoren der Stammzahl versuchsweise gleich, bis man mit
Berücksichtigung der quadratischen Reste auf eine in ganzen Zahlen
mögliche Gleichung kömmt.

Bei der Untersuchung der Gleichung v² = aw² + b beschränke man sich
nicht auf die drei Bedingungen ihrer Möglichkeit, sondern dividire auch
noch jede Seite durch 3 und 8 und sehe, ob die Reste diesen Divisoren
entsprechen. So sind die Gleichungen v² = 153w² − 1 und v² = 153w² − 2,
obschon sie den bekannten drei Bedingungen entsprechen, in ganzen Zahlen
doch nicht möglich, weil die erste Gleichung durch 3 und die zweite
durch 8 dividirt, auf ihren rechten Seiten Reste lassen, welche diesen
Divisoren nicht entsprechen.
-/

example : ∀ v w : ZMod 3, v ^ 2 ≠ 153 * w ^ 2 - 1 := by decide

example : ∀ v w : ZMod 8, v ^ 2 ≠ 153 * w ^ 2 - 2 := by decide

example : ¬ ∃ v w : ℤ, v ^ 2 = 153 * w ^ 2 - 1 := by
  rintro ⟨v, w, h⟩
  have hm : ∀ v w : ZMod 3, v ^ 2 ≠ 153 * w ^ 2 - 1 := by decide
  have hz := congrArg (fun z : ℤ => (z : ZMod 3)) h
  push_cast at hz
  exact hm v w hz

example : ¬ ∃ v w : ℤ, v ^ 2 = 153 * w ^ 2 - 2 := by
  rintro ⟨v, w, h⟩
  have hm : ∀ v w : ZMod 8, v ^ 2 ≠ 153 * w ^ 2 - 2 := by decide
  have hz := congrArg (fun z : ℤ => (z : ZMod 8)) h
  push_cast at hz
  exact hm v w hz

/-
Doch gewährt auch dieses Kriterium keine Sicherheit, wie an der
Gleichung v² = 101w² + 19 erprobt werden kann, indem sie allen jenen
Bedingungen entspricht, und in ganzen Zahlen doch nicht zu lösen ist.
-/

example : (∃ v w : ZMod 3, v ^ 2 = 101 * w ^ 2 + 19) ∧
    (∃ v w : ZMod 8, v ^ 2 = 101 * w ^ 2 + 19) := by decide

example : Prop :=
  ¬ ∃ v w : ℤ, v ^ 2 = 101 * w ^ 2 + 19

namespace Beispiel01

/-
2. Erstes Exempel.

y² = 610x² + 1, x = −2vw/(v² − 610w²)

S = 610 gibt kein ganzzahliges x. —
-/

private def xOf (p : ℚ) : ℚ := -2 * p / (p ^ 2 - 610)

example : ((List.range (Nat.sqrt (610 + 610) + 1)).flatMap
    (fun n => [(n : ℤ), -(n : ℤ)])).filter
    (fun p => decide (p ^ 2 - 610 ≠ 0 ∧ (610 : ℤ) % (p ^ 2 - 610) = 0 ∧
      (xOf p).den = 1 ∧ xOf p ≠ 0)) = [] := by native_decide

/-
v² = 610w² − 1 = 529w² + (81w² − 1)

9w = 1 − 2(23p₁ − 610)/(p₁² − 610), S₁ = 81·5·61 liefert nichts.
-/

example (w : ℚ) : 610 * w ^ 2 - 1 = 529 * w ^ 2 + (81 * w ^ 2 - 1) := by ring

private def wOf (p : ℚ) : ℚ := (1 - 2 * (23 * p - 610) / (p ^ 2 - 610)) / 9

example : ((List.range (Nat.sqrt (81 * 5 * 61 + 610) + 1)).flatMap
    (fun n => [(n : ℤ), -(n : ℤ)])).filter
    (fun p => decide (p ^ 2 - 610 ≠ 0 ∧ (81 * 5 * 61 : ℤ) % (p ^ 2 - 610) = 0 ∧
      (wOf p).den = 1 ∧ wOf p ≠ 0)) = [] := by native_decide

/-
v₁² = 610w₁² + 9 = (p₁₁w₁ + 3)²,

hieraus

w₁ = 6p₁₁/(p₁₁² − 610). S₁₁ = 6·5·61;
-/

/-
Vorzeichenabweichung im Druck: Für w₁ ≠ 0 folgt aus dem Ansatz
(p₁₁w₁ + 3)² der Bruch −6p₁₁/(p₁₁² − 610). Der gedruckte
positive Bruch entspricht dagegen dem Ansatz (p₁₁w₁ − 3)².
Beide gedruckten Formeln bleiben stehen; die späteren Werthe
p₁₁ = 25, w₁ = 10 und v₁ = 247 passen zum zweiten Ansatz.
-/

example (p w₁ : ℚ) : (p * w₁ + 3) ^ 2 - (610 * w₁ ^ 2 + 9) = w₁ * ((p ^ 2 - 610) * w₁ + 6 * p) := by ring

example (p w₁ : ℚ) (hw : w₁ ≠ 0) (hp : p ^ 2 - 610 ≠ 0)
    (h : (p * w₁ + 3) ^ 2 = 610 * w₁ ^ 2 + 9) :
    w₁ = -6 * p / (p ^ 2 - 610) := by
  have hf : w₁ * ((p ^ 2 - 610) * w₁ + 6 * p) = 0 := by
    calc
      _ = (p * w₁ + 3) ^ 2 - (610 * w₁ ^ 2 + 9) := by ring
      _ = 0 := by rw [h]; ring
  have hz := (mul_eq_zero.mp hf).resolve_left hw
  apply (eq_div_iff hp).2
  nlinarith [hz]

/- Nachrechnung des Ansatzes mit −3 für den gedruckten Bruch. -/

example (p : ℚ) (hp : p ^ 2 - 610 ≠ 0) :
    (p * (6 * p / (p ^ 2 - 610)) - 3) ^ 2 =
      610 * (6 * p / (p ^ 2 - 610)) ^ 2 + 9 := by
  field_simp
  ring

private def w₁Of (p : ℚ) : ℚ := 6 * p / (p ^ 2 - 610)

example : (6 * 5 * 61 : ℤ) % (25 ^ 2 - 610) = 0 := by norm_num

/-
für p₁₁ = 25 wird

w₁ = 10,  w = 2909,  x = 418005846
v₁ = 247, v = 71847, y = 10323982819.
-/

/- Nachrechnung der beiden Vorzeichen mit den gedruckten Zahlen. -/

example : (-6 : ℚ) * 25 / (25 ^ 2 - 610) = -10 ∧
    ((25 : ℚ) * 10 + 3) ^ 2 ≠ 610 * 10 ^ 2 + 9 ∧
    (25 : ℚ) * 10 - 3 = 247 := by norm_num

example : |w₁Of (25)| = 10 := by norm_num [w₁Of]

example : (247 : ℤ) ^ 2 = 610 * (10) ^ 2 + (9) := by norm_num

example : |wOf (-247 / 10)| = 2909 := by norm_num [wOf]

example : (71847 : ℤ) ^ 2 = 610 * (2909) ^ 2 + (-1) := by norm_num

example : |-(2 : ℚ) * 71847 * 2909 / (71847 ^ 2 - 610 * 2909 ^ 2)| = 418005846 := by norm_num

example : |(71847 : ℚ) / 2909 * (-2 * 71847 * 2909 / (71847 ^ 2 - 610 * 2909 ^ 2)) + 1| = 10323982819 := by norm_num

example : (10323982819 : ℤ) ^ 2 = 610 * (418005846 : ℤ) ^ 2 + 1 := by norm_num

end Beispiel01

/-
Seite 32.
-/

namespace Beispiel02

/-
3. Zweites Exempel.

y² = 91x² + 1, x = −2vw/(v² − 91w²)

S = 2 × 91 gibt nichts; v² − 91w² = −1, = ±2, = ±7, −14 sind unmögliche
Gleichungen;
-/

private def xOf (p : ℚ) : ℚ := -2 * p / (p ^ 2 - 91)

example : ((List.range (Nat.sqrt (2 * 91 + 91) + 1)).flatMap
    (fun n => [(n : ℤ), -(n : ℤ)])).filter
    (fun p => decide (p ^ 2 - 91 ≠ 0 ∧ (2 * 91 : ℤ) % (p ^ 2 - 91) = 0 ∧
      (xOf p).den = 1 ∧ xOf p ≠ 0)) = [] := by native_decide

example : ¬ ∃ v w : ℤ,
    v ^ 2 - 91 * w ^ 2 ∈ ([-1, 2, -2, 7, -7, -14] : List ℤ) := by
  rintro ⟨v, w, h⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with h | h | h | h | h | h
  · have hm : ∀ v w : ZMod 8, v ^ 2 - 91 * w ^ 2 ≠ -1 := by decide
    have hz := congrArg (fun n : ℤ => (n : ZMod 8)) h
    push_cast at hz
    exact hm v w hz
  · have hm : ∀ v w : ZMod 8, v ^ 2 - 91 * w ^ 2 ≠ 2 := by decide
    have hz := congrArg (fun n : ℤ => (n : ZMod 8)) h
    push_cast at hz
    exact hm v w hz
  · have hm : ∀ v w : ZMod 7, v ^ 2 - 91 * w ^ 2 ≠ -2 := by decide
    have hz := congrArg (fun n : ℤ => (n : ZMod 7)) h
    push_cast at hz
    exact hm v w hz
  · have hm : ∀ v w : ZMod 8, v ^ 2 - 91 * w ^ 2 ≠ 7 := by decide
    have hz := congrArg (fun n : ℤ => (n : ZMod 8)) h
    push_cast at hz
    exact hm v w hz
  · have hm : ∀ v w : ZMod 13, v ^ 2 - 91 * w ^ 2 ≠ -7 := by decide
    have hz := congrArg (fun n : ℤ => (n : ZMod 13)) h
    push_cast at hz
    exact hm v w hz
  · have hm : ∀ v w : ZMod 8, v ^ 2 - 91 * w ^ 2 ≠ -14 := by decide
    have hz := congrArg (fun n : ℤ => (n : ZMod 8)) h
    push_cast at hz
    exact hm v w hz

/-
v² = 91w² + 14 = (21w)² − 14(25w² − 1)

5w = 1 − 2(21p₁ − 91)/(p₁² − 91), S₁ = 100 × 91;
-/

example (w : ℚ) : 91 * w ^ 2 + 14 = (21 * w) ^ 2 - 14 * (25 * w ^ 2 - 1) := by ring

private def wOf (p : ℚ) : ℚ := (1 - 2 * (21 * p - 91) / (p ^ 2 - 91)) / 5

example : (100 * 91 : ℤ) % (9 ^ 2 - 91) = 0 := by norm_num

/-
für p₁ = 9 wird

w = 11,  x = 165,
v = 105, y = 1574.
-/

/-
Zuordnung: Für das angegebene p₁ = 9 ergibt die Formel w = 103/25.
Die folgende Nachrechnung prüft die Abweichung vom angegebenen Werth 11.
-/

example : |wOf (9)| ≠ 11 := by norm_num [wOf]

/-
Vermutlicher Druckfehler: Gemeint sind wohl p₁ = −9 und w = −11.
Die folgende Nachrechnung prüft diese vermutete Berichtigung.
-/

example : wOf (-9) = -11 := by norm_num [wOf]

example : (105 : ℤ) ^ 2 = 91 * (11) ^ 2 + (14) := by norm_num

example : |-(2 : ℚ) * 105 * 11 / (105 ^ 2 - 91 * 11 ^ 2)| = 165 := by norm_num

example : |(105 : ℚ) / 11 * (-2 * 105 * 11 / (105 ^ 2 - 91 * 11 ^ 2)) + 1| = 1574 := by norm_num

example : (1574 : ℤ) ^ 2 = 91 * (165 : ℤ) ^ 2 + 1 := by norm_num

end Beispiel02

namespace Beispiel03

/-
4. Drittes Exempel.

y² = 817x² + 1, x = −2vw/(v² − 817w²)

S = 2·19·43; v² − 817w² = −1, = ±2 sind unmöglich;
-/

private def xOf (p : ℚ) : ℚ := -2 * p / (p ^ 2 - 817)

example : ((List.range (Nat.sqrt (2 * 19 * 43 + 817) + 1)).flatMap
    (fun n => [(n : ℤ), -(n : ℤ)])).filter
    (fun p => decide (p ^ 2 - 817 ≠ 0 ∧ (2 * 19 * 43 : ℤ) % (p ^ 2 - 817) = 0 ∧
      (xOf p).den = 1 ∧ xOf p ≠ 0)) = [] := by native_decide

example : ¬ ∃ v w : ℤ,
    v ^ 2 - 817 * w ^ 2 ∈ ([-1, 2, -2] : List ℤ) := by
  rintro ⟨v, w, h⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with h | h | h
  · have hm : ∀ v w : ZMod 19, v ^ 2 - 817 * w ^ 2 ≠ -1 := by decide
    have hz := congrArg (fun n : ℤ => (n : ZMod 19)) h
    push_cast at hz
    exact hm v w hz
  · have hm : ∀ v w : ZMod 8, v ^ 2 - 817 * w ^ 2 ≠ 2 := by decide
    have hz := congrArg (fun n : ℤ => (n : ZMod 8)) h
    push_cast at hz
    exact hm v w hz
  · have hm : ∀ v w : ZMod 8, v ^ 2 - 817 * w ^ 2 ≠ -2 := by decide
    have hz := congrArg (fun n : ℤ => (n : ZMod 8)) h
    push_cast at hz
    exact hm v w hz

/-
v² = 817w² − 19

ist möglich, doch die Zerlegung schwierig; somit

v = 817z + r,

also

w² = 817z² + 2rz + (r² + 19)/817;
-/

example (z r : ℚ) : ((817 * z + r) ^ 2 + 19) / 817 = 817 * z ^ 2 + 2 * r * z + (r ^ 2 + 19) / 817 := by ring

/-
für r = 57 wird der letzte Bruch = 4, also w = 2, v = 57 und x = 12, y =
343.
-/

example : ((57 : ℚ) ^ 2 + 19) / 817 = 4 ∧ (2 : ℚ) ^ 2 = 817 * 0 ^ 2 + 2 * 57 * 0 + 4 ∧ (817 : ℚ) * 0 + 57 = 57 := by norm_num

example : (57 : ℤ) ^ 2 = 817 * (2) ^ 2 + (-19) := by norm_num

example : |-(2 : ℚ) * 57 * 2 / (57 ^ 2 - 817 * 2 ^ 2)| = 12 := by norm_num

example : |(57 : ℚ) / 2 * (-2 * 57 * 2 / (57 ^ 2 - 817 * 2 ^ 2)) + 1| = 343 := by norm_num

example : (343 : ℤ) ^ 2 = 817 * (12 : ℤ) ^ 2 + 1 := by norm_num

/-
Andere Auflösung.

y² = 817x² + 1 = (31x)² − (144x² − 1),

also

12x = 1 − 2(31p − 817)/(p² − 817);

S = 288 × 817; für p = −29 wird x = 12.
-/

example (x : ℚ) : 817 * x ^ 2 + 1 = (31 * x) ^ 2 - (144 * x ^ 2 - 1) := by ring

private def xAltOf (p : ℚ) : ℚ := (1 - 2 * (31 * p - 817) / (p ^ 2 - 817)) / 12

example : (288 * 817 : ℤ) % ((-29) ^ 2 - 817) = 0 := by norm_num

example : |xAltOf (-29)| = 12 := by norm_num [xAltOf]

example : (343 : ℤ) ^ 2 = 817 * (12) ^ 2 + (1) := by norm_num

end Beispiel03

namespace Beispiel04

/-
5. Viertes Exempel.

y² = 76x² + 1, x = −2p/(p² − 76) = −q/(q² − 19);
-/

example (q : ℚ) : -2 * (2 * q) / ((2 * q) ^ 2 - 76) = -q / (q ^ 2 - 19) := by
  have h : (2 * q) ^ 2 - 76 = 4 * (q ^ 2 - 19) := by ring
  rw [h]
  rw [div_mul_eq_div_div]
  ring

private def xOf (q : ℚ) : ℚ := -q / (q ^ 2 - 19)

/-
Seite 33.

S = 19 gibt nichts.
-/

example : ((List.range (Nat.sqrt (19 + 19) + 1)).flatMap
    (fun n => [(n : ℤ), -(n : ℤ)])).filter
    (fun p => decide (p ^ 2 - 19 ≠ 0 ∧ (19 : ℤ) % (p ^ 2 - 19) = 0 ∧
      (xOf p).den = 1 ∧ xOf p ≠ 0)) = [] := by native_decide

/-
v² = 19w² + 1, w = −2q₁/(q₁² − 19),

S₁ = 38 liefert nichts;
-/

private def wOf (p : ℚ) : ℚ := -2 * p / (p ^ 2 - 19)

example : ((List.range (Nat.sqrt (38 + 19) + 1)).flatMap
    (fun n => [(n : ℤ), -(n : ℤ)])).filter
    (fun p => decide (p ^ 2 - 19 ≠ 0 ∧ (38 : ℤ) % (p ^ 2 - 19) = 0 ∧
      (wOf p).den = 1 ∧ wOf p ≠ 0)) = [] := by native_decide

/-
v₁² = 19w₁² − 2 = w₁² + 2(9w₁² − 1) ... 3w₁ = 1 − 2(q₁₁ − 19)/(q₁₁² −
19);

S₁₁ = 36 × 19;
-/

example (w₁ : ℚ) : 19 * w₁ ^ 2 - 2 = w₁ ^ 2 + 2 * (9 * w₁ ^ 2 - 1) := by ring

private def w₁Of (p : ℚ) : ℚ := (1 - 2 * (1 * p - 19) / (p ^ 2 - 19)) / 3

example : (36 * 19 : ℤ) % (4 ^ 2 - 19) = 0 := by norm_num

/-
für

q₁₁ = 4, q₁ = 13/3, q = 170/39
w₁ = 3,  w = 39
v₁ = 13, v = 170

wird

x = 6630, y = 57799.
-/

example : |w₁Of (4)| = 3 := by norm_num [w₁Of]

example : (13 : ℤ) ^ 2 = 19 * (3) ^ 2 + (-2) := by norm_num

example : |wOf (13 / 3)| = 39 := by norm_num [wOf]

example : (170 : ℤ) ^ 2 = 19 * (39) ^ 2 + (1) := by norm_num

example : |xOf (170 / 39)| = 6630 := by norm_num [xOf]

example : |2 * ((170 : ℚ) / 39) * xOf (170 / 39) + 1| = 57799 := by norm_num [xOf]

example : (57799 : ℤ) ^ 2 = 76 * (6630) ^ 2 + (1) := by norm_num

end Beispiel04

end Kunerth1877.Paragraf07
