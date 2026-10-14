/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Kunerth_1880_Integer_Generalization.Paragraf07
import Kunerth_1880_Integer_Generalization.Paragraf13
import Kunerth_1880_Integer_Generalization.Paragraf16
import Mathlib

namespace Kunerth1880.Paragraf25

/-
Seite 371
§. 25.
IV. Gleichungen, die in gebrochenen, nicht aber in ganzen Zahlen
möglich sind, nebst den betreffenden Kriterien.
-/

namespace Beispiel01

/-
1. Exempel:
y² = 113x²+460x+22;
        1     4    6
die Achterreste der Constanten sind 1, 4, 6;
-/

example : ([113 % 8, 460 % 8, 22 % 8] : List ℕ) = [1, 4, 6] := by norm_num

/-
für
x = 8n±(1, 3, 2, 4, 0)
lässt die rechte Seite der Gleichung beziehungsweise die
Achterreste ±3, ±2, welche Zahlen quadratische Nichtreste von 8 sind;
-/

example : (([-3, -2, -1, 0, 1, 2, 3, 4] : List ℤ).map (fun x => (113 * x ^ 2 + 460 * x + 22) % 8)).toFinset = {2, 3, 6} := by norm_num

example : ∀ x y : Fin 8, ((y.val : ℤ) ^ 2 - (113 * (x.val : ℤ) ^ 2 + 460 * x.val + 22)) % 8 ≠ 0 := by decide

/-
folglich kann x keine ganze Zahl sein.
-/

example : ((List.range 8).map (fun r => r ^ 2 % 8)).toFinset = {0, 1, 4} := by decide

example : ¬ ∃ x y : ℤ, y ^ 2 = 113 * x ^ 2 + (460) * x + (22) := by
  rintro ⟨x, y, h⟩
  have hmod : ∀ u v : ZMod 8, v ^ 2 ≠ 113 * u ^ 2 + 460 * u + (22) := by
    decide
  apply hmod (x : ZMod 8) (y : ZMod 8)
  have he := congrArg (fun z : ℤ => (z : ZMod 8)) h
  push_cast at he
  exact he

end Beispiel01

namespace Beispiel02

/-
2. Exempel:
y² = 18x²+21x−13;
der rechtsseitige Dreierrest ist −1, ein Nichtrest von 3.
-/

example : ((List.range 3).map (fun r => r ^ 2 % 3)).toFinset = {0, 1} := by decide

example : ∀ x : Fin 3, (18 * (x.val : ℤ) ^ 2 + 21 * x.val - 13) % 3 = (-1 : ℤ) % 3 := by decide

example : ∀ x y : Fin 3, ((y.val : ℤ) ^ 2 - (18 * (x.val : ℤ) ^ 2 + 21 * x.val - 13)) % 3 ≠ 0 := by decide

example : ¬ ∃ x y : ℤ, y ^ 2 = 18 * x ^ 2 + (21) * x + (-13) := by
  rintro ⟨x, y, h⟩
  have hmod : ∀ u v : ZMod 3, v ^ 2 ≠ 18 * u ^ 2 + 21 * u + (-13) := by
    decide
  apply hmod (x : ZMod 3) (y : ZMod 3)
  have he := congrArg (fun z : ℤ => (z : ZMod 3)) h
  push_cast at he
  exact he

end Beispiel02

namespace Beispiel03

/-
Seite 372

3. Exempel:
y² = 79x²+24x+2, D = −56, K² = 79Δ²−56(α²−79),
-/

example : (24 ^ 2 - 4 * 79 * 2 : ℤ) = -56 := by norm_num

/-
für α = 9 wird das Zahlenglied −112; da 79 ein Nichtrest von
4 ist, so muss durch 16 dividirt werden;
-/

example : (-56 * (9 ^ 2 - 79) : ℤ) = -112 := by norm_num

example : ¬ ∃ x : Fin 4, x.val ^ 2 % 4 = 79 % 4 := by decide

example : (-112 / 16 : ℚ) = -7 := by norm_num

/-
also K₁² = 79Δ₁²−7, in
ganzen Zahlen unmöglich;
-/

example : (8 : ℤ) ^ 2 ≤ 79 ∧ 79 < (8 + 1) ^ 2 := by decide

/- Hilfsdefinition: Ein Rechenschritt der Kettenbruchentwicklung. -/

private def tennerStep79 (s : ℤ × ℤ) : ℤ × ℤ :=
  let q := (8 + s.1) / s.2
  let m := q * s.2 - s.1
  (m, (79 - m ^ 2) / s.2)

example :
    ((List.range 5).map fun k => (tennerStep79^[k + 1]) (0, 1)) =
      [(8, 15), (7, 2), (7, 15), (8, 1), (8, 15)] := by decide

example : ([((0, 1) : ℤ × ℤ), (8, 15), (7, 2), (7, 15), (8, 1)]).all
    (fun s => decide (s.2 ≠ 0) && (79 - (tennerStep79 s).1 ^ 2) % s.2 == 0) := by decide

/- Hilfsschritt: Fortsetzung der berechneten Kettenbruchperiode. -/

private theorem tennerStates79 (k : ℕ) :
    (tennerStep79^[k + 1]) (0, 1) ∈
      ([(8, 15), (7, 2), (7, 15), (8, 1)] : List (ℤ × ℤ)) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ih
    rcases ih with h | h | h | h <;> rw [h] <;> decide

/- Hilfsschritt: Fortsetzung der berechneten Kettenbruchperiode. -/

private theorem tennerAllStates79 (k : ℕ) :
    (tennerStep79^[k]) (0, 1) ∈
      ([(0, 1), (8, 15), (7, 2), (7, 15), (8, 1)] : List (ℤ × ℤ)) := by
  cases k with
  | zero => decide
  | succ k => exact List.mem_cons_of_mem _ (tennerStates79 k)

/- Hilfsdefinition: Die III. Verticalreihe der Rechnung. -/

private def tennerM79 (k : ℕ) : ℤ := ((tennerStep79^[k]) (0, 1)).1

/- Hilfsdefinition: Die VI. Verticalreihe der Rechnung. -/

private def tennerQ79 (k : ℕ) : ℤ := ((tennerStep79^[k]) (0, 1)).2

/- Hilfsdefinition: Die I. Verticalreihe der Rechnung. -/

private def tennerA79 (k : ℕ) : ℤ := (8 + tennerM79 k) / tennerQ79 k

/- Hilfsschritt: Ganzzahlige Quotienten und genaue Divisionen der Kette. -/

private theorem tennerData79 : tennerM79 0 = 0 ∧ tennerQ79 0 = 1 ∧
    (∀ k, (tennerA79 k : ℝ) ≤
        (Real.sqrt (79 : ℤ) + tennerM79 k) / tennerQ79 k ∧
      (Real.sqrt (79 : ℤ) + tennerM79 k) / tennerQ79 k < tennerA79 k + 1) ∧
    (∀ k, tennerM79 (k + 1) = tennerA79 k * tennerQ79 k - tennerM79 k) ∧
    (∀ k, tennerQ79 (k + 1) * tennerQ79 k = 79 - tennerM79 (k + 1) ^ 2) := by
  have hs : (Real.sqrt 79) ^ 2 = 79 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 79 := Real.sqrt_nonneg _
  have hlo : (8 : ℝ) ≤ Real.sqrt 79 := by nlinarith
  have hhi : Real.sqrt 79 < (9 : ℝ) := by nlinarith
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro k
    have hk := tennerAllStates79 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with hk | hk | hk | hk | hk
    all_goals norm_num [tennerA79, tennerM79, tennerQ79, hk]
    all_goals constructor <;> linarith
  · intro k
    simp only [tennerM79, tennerA79, tennerQ79, Function.iterate_succ_apply']
    rfl
  · intro k
    have hk := tennerAllStates79 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    simp only [tennerM79, tennerQ79, Function.iterate_succ_apply']
    rcases hk with hk | hk | hk | hk | hk <;> rw [hk] <;> decide

/- Hilfsschritt: Anwendung des als Voraussetzung geführten Kriteriums. -/

private theorem specializeCriterion79
    (hCriterion : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ∀ N : ℤ, N ^ 2 < 79 →
      (∀ k : ℕ, ((tennerStep79^[k + 1]) (0, 1)).2 ≠ |N|) →
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 + N := by
  intro N hN habsent
  obtain ⟨hM, hQ, hfloor, hMstep, hQstep⟩ := tennerData79
  have hns : ¬ ∃ q : ℤ, q ^ 2 = 79 := by
    rintro ⟨q, hq⟩
    have hs : IsSquare (79 : ℤ) := ⟨q, by nlinarith [hq]⟩
    norm_num at hs
  have hNreal : (|N| : ℤ) < Real.sqrt (79 : ℤ) := by
    have hsq : (((|N| : ℤ) : ℝ)) ^ 2 < 79 := by
      exact_mod_cast (show |N| ^ 2 < 79 by simpa only [sq_abs] using hN)
    have hs : (Real.sqrt 79) ^ 2 = 79 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt 79 := Real.sqrt_nonneg _
    norm_num only [Int.cast_ofNat]
    nlinarith
  exact hCriterion 79 N tennerA79 tennerM79 tennerQ79 (by norm_num) hns
    hM hQ hfloor hMstep hQstep hNreal habsent

/- Hilfsschritt: Ausschluss des Zahlengliedes −7 mit dem vorausgesetzten Kriterium. -/

private theorem auxiliaryImpossible79
    (hCriterion : ∀ N : ℤ, N ^ 2 < 79 →
      (∀ k : ℕ, ((tennerStep79^[k + 1]) (0, 1)).2 ≠ |N|) →
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 + N) :
    ¬ ∃ v w : ℤ, v ^ 2 = 79 * w ^ 2 - 7 := by
  rintro ⟨v, w, h⟩
  have hcop : Int.gcd v w = 1 := by
      let g : ℤ := Int.gcd v w
      have hgv : g ∣ v := Int.gcd_dvd_left v w
      have hgw : g ∣ w := Int.gcd_dvd_right v w
      have hd : g ^ 2 ∣ -7 := by
        have hdiff := dvd_sub (pow_dvd_pow_of_dvd hgv 2)
          (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hgw 2) 79)
        simpa only [h, add_sub_cancel_right, sub_sub_cancel_left] using hdiff
      have hdpos : g ^ 2 ∣ (7 : ℤ) := by simpa only [dvd_neg] using hd
      have hdNat : (Int.gcd v w) ^ 2 ∣ 7 := by
        dsimp [g] at hdpos
        exact_mod_cast hdpos
      have hs : Squarefree (7 : ℕ) := (by decide : Nat.Prime 7).squarefree
      have hu : IsUnit (Int.gcd v w) := hs (Int.gcd v w) (by simpa only [pow_two] using hdNat)
      exact Nat.isUnit_iff.mp hu
  have hrow : ∀ k : ℕ, ((tennerStep79^[k + 1]) (0, 1)).2 ≠ |(-7 : ℤ)| := by
    intro k
    have hs := tennerStates79 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with h | h | h | h <;> rw [h] <;> norm_num
  apply hCriterion (-7) (by decide) hrow
  exact ⟨v, w, hcop, by linarith [h]⟩

/-
somit existirt hier kein ganzzahliges β
und nach §. 23, Absatz 2, auch keine ganze Zahl für x.
-/

/- Folgerung mit dem als Voraussetzung geführten Kriterium des §. 23. -/

example
    (hSource : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ¬ ∃ x y : ℤ, y ^ 2 = 79 * x ^ 2 + 24 * x + 2 := by
  have haux := auxiliaryImpossible79 (specializeCriterion79 hSource)
  have even_pair (K Δ t : ℤ) (h : K ^ 2 = 79 * Δ ^ 2 + 4 * t) :
      2 ∣ K ∧ 2 ∣ Δ := by
    have hK0 := Int.emod_nonneg K (by norm_num : (4 : ℤ) ≠ 0)
    have hK4 := Int.emod_lt_of_pos K (by norm_num : (0 : ℤ) < 4)
    have hΔ0 := Int.emod_nonneg Δ (by norm_num : (4 : ℤ) ≠ 0)
    have hΔ4 := Int.emod_lt_of_pos Δ (by norm_num : (0 : ℤ) < 4)
    have hm : (K ^ 2 - 79 * Δ ^ 2) % 4 = 0 := by rw [h]; omega
    have hm' : ((K % 4) ^ 2 - 79 * (Δ % 4) ^ 2) % 4 = 0 := by
      simpa only [pow_two, Int.sub_emod, Int.mul_emod, Int.emod_emod] using hm
    have heven : K % 2 = 0 ∧ Δ % 2 = 0 := by
      interval_cases hk : K % 4 <;> interval_cases hd : Δ % 4 <;>
        norm_num [hk, hd] at hm' <;> omega
    exact ⟨Int.dvd_of_emod_eq_zero heven.1, Int.dvd_of_emod_eq_zero heven.2⟩
  rintro ⟨x, y, h⟩
  let β := y - 9 * x
  have hIII : y = 9 * x + β := by dsimp [β]; ring
  have hquadratic : (79 - 9 ^ 2) * x ^ 2 + (24 - 2 * 9 * β) * x +
      2 - β ^ 2 = 0 := by
    rw [hIII] at h
    linear_combination -h
  let Δ := 2 * (79 - 9 ^ 2) * x + 24 - 2 * 9 * β
  have hIV : Δ ^ 2 = 4 * (79 * β ^ 2 - 24 * 9 * β + 2 * 9 ^ 2) +
      24 ^ 2 - 4 * 79 * 2 := by
    dsimp [Δ]
    linear_combination 4 * (79 - 9 ^ 2) * hquadratic
  let K := 2 * 79 * β - 24 * 9
  have hV : K ^ 2 = 79 * Δ ^ 2 + 4 * (-28) := by
    dsimp [K]
    linear_combination -79 * hIV
  obtain ⟨⟨k, hk⟩, ⟨d, hd⟩⟩ := even_pair K Δ (-28) hV
  have h₁ : k ^ 2 = 79 * d ^ 2 + 4 * (-7) := by
    rw [hk, hd] at hV
    nlinarith [hV]
  obtain ⟨⟨K₁, hK₁⟩, ⟨Δ₁, hΔ₁⟩⟩ := even_pair k d (-7) h₁
  apply haux
  refine ⟨K₁, Δ₁, ?_⟩
  rw [hK₁, hΔ₁] at h₁
  nlinarith [h₁]

end Beispiel03

namespace Beispiel04

/-
4. Exempel:
x² = 101x²+19 = (x+5²)+2(10x−3)(5x+1);
-/

/-
Redaktionelle Nachrechnung: In (x+5²) dürfte die schließende Klammer
vor dem Exponenten stehen. Der Unterschied der beiden rechten
Ausdrücke wird zuerst mit der gedruckten Stellung der Klammer
berechnet; danach wird die vermutliche Berichtigung (x+5)² geprüft.
Die vorangestellte linke Seite x² bleibt im Wortlaut erhalten.
-/

example (x : ℚ) : 101 * x ^ 2 + 19 -
    ((x + 5 ^ 2) + 2 * (10 * x - 3) * (5 * x + 1)) = x * (x + 9) := by ring

example (x : ℚ) : 101 * x ^ 2 + 19 =
    (x + 5) ^ 2 + 2 * (10 * x - 3) * (5 * x + 1) := by ring

/-
5x = −1+2(24p−101)/(p²−101), S₁ = −2.19.101.5²;
-/

example (p : ℚ) : (-1) + (2 * (24) * p + (2 * 101 * (-1) + (0) * 5)) / (p ^ 2 - 101) = (-1) + 2 * ((24) * p + (-101)) / (p ^ 2 - 101) := by ring

example : (5 ^ 2 * (-4 * 101 * 19) / 2 : ℚ) = -2 * 19 * 101 * 5 ^ 2 := by norm_num

/-
streicht man 19 und 101 nach §. 16, so bleibt für das Zahlenglied N
bloss 10, womit sich keine in ganzen Zahlen mögliche Gleichung
bilden lässt.
-/

example : (10 : ℤ) ^ 2 ≤ 101 ∧ 101 < (10 + 1) ^ 2 := by decide

/- Hilfsdefinition: Ein Rechenschritt der Kettenbruchentwicklung. -/

private def tennerStep101 (s : ℤ × ℤ) : ℤ × ℤ :=
  let q := (10 + s.1) / s.2
  let m := q * s.2 - s.1
  (m, (101 - m ^ 2) / s.2)

example : (tennerStep101 (0, 1), tennerStep101 (10, 1)) =
    ((10, 1), (10, 1)) := by decide

/- Hilfsschritt: Fortsetzung der berechneten Kettenbruchperiode. -/

private theorem tennerState101 (k : ℕ) :
    (tennerStep101^[k + 1]) (0, 1) = (10, 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    decide

/- Hilfsschritt: Fortsetzung der berechneten Kettenbruchperiode. -/

private theorem tennerAllStates101 (k : ℕ) :
    (tennerStep101^[k]) (0, 1) ∈
      ([(0, 1), (10, 1)] : List (ℤ × ℤ)) := by
  cases k with
  | zero => decide
  | succ k =>
    rw [tennerState101 k]
    decide

/- Hilfsdefinition: Die III. Verticalreihe der Rechnung. -/

private def tennerM101 (k : ℕ) : ℤ := ((tennerStep101^[k]) (0, 1)).1

/- Hilfsdefinition: Die VI. Verticalreihe der Rechnung. -/

private def tennerQ101 (k : ℕ) : ℤ := ((tennerStep101^[k]) (0, 1)).2

/- Hilfsdefinition: Die I. Verticalreihe der Rechnung. -/

private def tennerA101 (k : ℕ) : ℤ := (10 + tennerM101 k) / tennerQ101 k

/- Hilfsschritt: Ganzzahlige Quotienten und genaue Divisionen der Kette. -/

private theorem tennerData101 : tennerM101 0 = 0 ∧ tennerQ101 0 = 1 ∧
    (∀ k, (tennerA101 k : ℝ) ≤
        (Real.sqrt (101 : ℤ) + tennerM101 k) / tennerQ101 k ∧
      (Real.sqrt (101 : ℤ) + tennerM101 k) / tennerQ101 k < tennerA101 k + 1) ∧
    (∀ k, tennerM101 (k + 1) = tennerA101 k * tennerQ101 k - tennerM101 k) ∧
    (∀ k, tennerQ101 (k + 1) * tennerQ101 k = 101 - tennerM101 (k + 1) ^ 2) := by
  have hs : (Real.sqrt 101) ^ 2 = 101 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 101 := Real.sqrt_nonneg _
  have hlo : (10 : ℝ) ≤ Real.sqrt 101 := by nlinarith
  have hhi : Real.sqrt 101 < (11 : ℝ) := by nlinarith
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro k
    have hk := tennerAllStates101 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with hk | hk
    all_goals norm_num [tennerA101, tennerM101, tennerQ101, hk]
    all_goals constructor <;> linarith
  · intro k
    simp only [tennerM101, tennerA101, tennerQ101, Function.iterate_succ_apply']
    rfl
  · intro k
    have hk := tennerAllStates101 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    simp only [tennerM101, tennerQ101, Function.iterate_succ_apply']
    rcases hk with hk | hk <;> rw [hk] <;> decide

/- Hilfsschritt: Anwendung des als Voraussetzung geführten Kriteriums. -/

private theorem specializeCriterion101
    (hCriterion : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ∀ N : ℤ, N ^ 2 < 101 →
      (∀ k : ℕ, ((tennerStep101^[k + 1]) (0, 1)).2 ≠ |N|) →
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 101 * w ^ 2 + N := by
  intro N hN habsent
  obtain ⟨hM, hQ, hfloor, hMstep, hQstep⟩ := tennerData101
  have hns : ¬ ∃ q : ℤ, q ^ 2 = 101 := by
    rintro ⟨q, hq⟩
    have hs : IsSquare (101 : ℤ) := ⟨q, by nlinarith [hq]⟩
    norm_num at hs
  have hNreal : (|N| : ℤ) < Real.sqrt (101 : ℤ) := by
    have hsq : (((|N| : ℤ) : ℝ)) ^ 2 < 101 := by
      exact_mod_cast (show |N| ^ 2 < 101 by simpa only [sq_abs] using hN)
    have hs : (Real.sqrt 101) ^ 2 = 101 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt 101 := Real.sqrt_nonneg _
    norm_num only [Int.cast_ofNat]
    nlinarith
  exact hCriterion 101 N tennerA101 tennerM101 tennerQ101 (by norm_num) hns
    hM hQ hfloor hMstep hQstep hNreal habsent

/- Folgerung mit dem als Voraussetzung geführten Kriterium des §. 23. -/

example
    (hCriterion : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ¬ ∃ v w : ℤ, v ^ 2 = 101 * w ^ 2 + 10 := by
  rintro ⟨v, w, h⟩
  have hcop : Int.gcd v w = 1 := by
    let g : ℤ := Int.gcd v w
    have hgv : g ∣ v := Int.gcd_dvd_left v w
    have hgw : g ∣ w := Int.gcd_dvd_right v w
    have hd : g ^ 2 ∣ 10 := by
      have hdiff := dvd_sub (pow_dvd_pow_of_dvd hgv 2)
        (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hgw 2) 101)
      have heq : v ^ 2 - 101 * w ^ 2 = 10 := by linarith [h]
      rwa [heq] at hdiff
    have hdNat : (Int.gcd v w) ^ 2 ∣ 10 := by
      dsimp [g] at hd
      exact_mod_cast hd
    have hs : Squarefree (10 : ℕ) := by
      have h2 : Squarefree (2 : ℕ) := (by decide : Nat.Prime 2).squarefree
      have h5 : Squarefree (5 : ℕ) := (by decide : Nat.Prime 5).squarefree
      simpa using (Nat.squarefree_mul (by decide : Nat.Coprime 2 5)).2 ⟨h2, h5⟩
    have hu : IsUnit (Int.gcd v w) := hs (Int.gcd v w) (by simpa only [pow_two] using hdNat)
    exact Nat.isUnit_iff.mp hu
  have hrow : ∀ k : ℕ, ((tennerStep101^[k + 1]) (0, 1)).2 ≠ |(10 : ℤ)| := by
    intro k
    rw [tennerState101]
    norm_num
  exact specializeCriterion101 hCriterion 10 (by decide) hrow ⟨v, w, hcop, h⟩

end Beispiel04

namespace Beispiel05

/-
5. Exempel
y² = 170x²+134x+69 = (11x+8)²+(7x−5)(7x−1),
-/

example (x : ℚ) : 170 * x ^ 2 + 134 * x + 69 = (11 * x + 8) ^ 2 + (7 * x - 5) * (7 * x - 1) := by ring

/-
D = −4.13.557, x = 1/7, y = 67/7,
7x = 1+2(67p+639)/(p²−170),
-/

example : (134 ^ 2 - 4 * 170 * 69 : ℤ) = -4 * 13 * 557 := by norm_num

example : (67 / 7 : ℚ) ^ 2 = 170 * (1 / 7) ^ 2 + (134) * (1 / 7) + (69) := by norm_num

example (p : ℚ) : (1) + (2 * (67) * p + (2 * 170 * (1) + (134) * 7)) / (p ^ 2 - 170) = (1) + 2 * ((67) * p + (639)) / (p ^ 2 - 170) := by ring

/-
S₁ = −2.13.557.7²;
-/

example : (2 * (-170 * 67 ^ 2 + 639 ^ 2) : ℤ) = -2 * 13 * 557 * 7 ^ 2 := by norm_num

/-
nach Wegfall von 557 hat man die Gleichungen
v² = 170w²∓7(1, 2, 13, 26),
welche insgesammt unmöglich sind, weil 7 ein Nichtrest, jede in
den Klammern stehende Zahl aber ein Rest von 17 ist.
-/

example : ¬ ∃ x : Fin 17, x.val ^ 2 % 17 = 7 := by decide

example : ∃ x : Fin 17, x.val ^ 2 % 17 = 1 % 17 := by decide

example : ∃ x : Fin 17, x.val ^ 2 % 17 = 2 % 17 := by decide

example : ∃ x : Fin 17, x.val ^ 2 % 17 = 13 % 17 := by decide

example : ∃ x : Fin 17, x.val ^ 2 % 17 = 26 % 17 := by decide

/- Hilfsschritt: Anwendung der Reste von 17 auf die angegebenen Zahlen. -/

private theorem noListedNorms : ∀ N ∈ ([7, -7, 14, -14, 91, -91, 182, -182] : List ℤ), ¬ ∃ v w : ℤ, v ^ 2 = 170 * w ^ 2 + N := by
  intro N hN
  have hf : ∀ t ∈ ([7, -7, 14, -14, 91, -91, 182, -182] : List (ZMod 17)),
      ∀ v w : ZMod 17, v ^ 2 ≠ 170 * w ^ 2 + t := by decide
  have hN' : (N : ZMod 17) ∈ ([7, -7, 14, -14, 91, -91, 182, -182] : List (ZMod 17)) := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rintro ⟨v, w, h⟩
  apply hf (N : ZMod 17) hN' (v : ZMod 17) (w : ZMod 17)
  have he := congrArg (fun z : ℤ => (z : ZMod 17)) h
  push_cast at he
  exact he

/- Hilfsschritt: Der Nenner der p-Function ist nicht Null. -/

private theorem notSquare170 (p : ℚ) : p ^ 2 - 170 ≠ 0 := by
  intro h
  have hs : IsSquare (170 : ℚ) := ⟨p, by nlinarith [h]⟩
  have hi : IsSquare (170 : ℤ) := Rat.isSquare_intCast_iff.mp hs
  norm_num at hi

/- Hilfsschritt: Theilbarkeit des Nenners und die Stammzahl. -/

private theorem normStock (x : ℤ) (p : ℚ)
    (hX : (7 : ℚ) * x = 1 + (134 * p + 1278) / (p ^ 2 - 170)) :
    7 ∣ p.num ^ 2 - 170 * (p.den : ℤ) ^ 2 ∧
      p.num ^ 2 - 170 * (p.den : ℤ) ^ 2 ∣ 101374 := by
  have hp := notSquare170 p
  have hX' : (7 : ℚ) * x = 1 +
      (2 * 67 * p + (2 * 170 * 1 + 134 * 7)) / (p ^ 2 - 170) := by
    convert hX using 1; ring
  have hdata := Kunerth1880.Paragraf07.normData 170 134 69 1 7 67 11 8 (-7) (-5)
    x p (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hp hX'
  obtain ⟨k, hk⟩ := Kunerth1880.Paragraf07.preparationFromVIII 170 134 1 7 67 11 8 (-7) (-5)
    x p (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp hX'
  have hprep : p.num = 7 * k - 11 * (p.den : ℤ) := by linear_combination hk
  let v : ℤ := p.num
  let w : ℤ := p.den
  let N := v ^ 2 - 170 * w ^ 2
  have hwq : (w : ℚ) ≠ 0 := by dsimp [w]; exact_mod_cast p.den_nz
  have hpv : p = (v : ℚ) / w := by simpa [v, w] using (Rat.num_div_den p).symm
  have hcross : ((7 : ℚ) * x - 1) * (p ^ 2 - 170) = 134 * p + 1278 := by
    exact (eq_div_iff hp).mp (by linear_combination hX)
  rw [hpv] at hcross
  field_simp [hwq] at hcross
  have hXI : (7 * x - 1) * N = (134 * v + 1278 * w) * w := by
    have hI : (7 * x - 1) * (v ^ 2 - w ^ 2 * 170) = w * (v * 134 + w * 1278) := by
      exact_mod_cast hcross
    dsimp [N]
    linear_combination hI
  have hL : N * (x * (67 * v - 639 * w) - 67 * k - 1086 * w) = 101374 * w ^ 3 := by
    apply mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num)
    dsimp [N, v, w] at hXI ⊢
    linear_combination (67 * p.num - 639 * (p.den : ℤ)) * hXI +
      67 * (p.num ^ 2 - 170 * (p.den : ℤ) ^ 2) * hprep
  have hcop : IsCoprime N (w ^ 3) := by
    apply Kunerth1880.Paragraf07.normCoprime
    simpa [v, w, Int.gcd] using p.reduced
  refine ⟨hdata.1, ?_⟩
  apply hcop.dvd_of_dvd_mul_right
  exact ⟨x * (67 * v - 639 * w) - 67 * k - 1086 * w, hL.symm⟩

/- Hilfsschritt: Ausschluss der aus der Stammzahl verbleibenden Nenner. -/

private theorem excludeStock (p : ℚ) (k : ℤ)
    (hN : p.num ^ 2 - 170 * (p.den : ℤ) ^ 2 = 7 * k)
    (hstock : p.num ^ 2 - 170 * (p.den : ℤ) ^ 2 ∣ 101374)
    (h557 : ¬ (557 : ℤ) ∣ k) : False := by
  have hk : k ∣ 14482 := by
    obtain ⟨t, ht⟩ := hstock
    refine ⟨t, ?_⟩
    rw [hN] at ht
    nlinarith [ht]
  have hcop : IsCoprime k (557 : ℤ) :=
    ((show Prime (557 : ℤ) by norm_num).coprime_iff_not_dvd.mpr h557).symm
  have hk26 : k ∣ 26 := hcop.dvd_of_dvd_mul_right (by convert hk using 1; norm_num)
  have hkmem : k ∈ (26 : ℤ).divisors := Int.mem_divisors.mpr ⟨hk26, by norm_num⟩
  have hdivs : (26 : ℤ).divisors = {1, -1, 2, -2, 13, -13, 26, -26} := by decide
  rw [hdivs] at hkmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hkmem
  rcases hkmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply noListedNorms (p.num ^ 2 - 170 * (p.den : ℤ) ^ 2) (by rw [hN]; decide)
    exact ⟨p.num, (p.den : ℤ), by ring⟩

example : ¬ ∃ x y : ℤ, y ^ 2 = 170 * x ^ 2 + (134) * x + (69) := by
  rintro ⟨x, y, h⟩
  have hsI : 7 * x - 1 ≠ 0 := by omega
  have hs : (7 : ℚ) * x - 1 ≠ 0 := by exact_mod_cast hsI
  have hQ : (y : ℚ) ^ 2 = 170 * (x : ℚ) ^ 2 + 134 * x + 69 := by exact_mod_cast h
  let p : ℚ := (7 * y + 67) / (7 * x - 1)
  have hP : ((7 : ℚ) * x - 1) * p = 7 * y + 67 := by
    dsimp [p]
    field_simp
  have hp := notSquare170 p
  have hcross : ((7 : ℚ) * x - 1) * (p ^ 2 - 170) = 134 * p + 1278 := by
    apply mul_left_cancel₀ hs
    linear_combination (((7 : ℚ) * x - 1) * p + 7 * y - 67) * hP + 49 * hQ
  have hX : (7 : ℚ) * x = 1 + (134 * p + 1278) / (p ^ 2 - 170) := by
    have hc := (eq_div_iff hp).mpr hcross
    linarith
  have hg : 134 * p + 1278 ≠ 0 := by
    intro hz
    rw [hz, zero_div] at hX
    exact hs (by linarith)
  let q : ℚ := -(1278 * p + 22780) / (134 * p + 1278)
  have hq := notSquare170 q
  have hqcross : q * (134 * p + 1278) = -(1278 * p + 22780) := by
    dsimp [q]
    exact div_mul_cancel₀ _ hg
  have heq : (134 * q + 1278) / (q ^ 2 - 170) =
      (134 * p + 1278) / (p ^ 2 - 170) := by
    apply (div_eq_div_iff hq hp).mpr
    linear_combination (p - q) * hqcross
  have hXq : (7 : ℚ) * x = 1 + (134 * q + 1278) / (q ^ 2 - 170) := by
    rw [heq]
    exact hX
  have hX' : (7 : ℚ) * x = 1 +
      (2 * 67 * p + (2 * 170 * 1 + 134 * 7)) / (p ^ 2 - 170) := by
    convert hX using 1; ring
  have hg' : 2 * (67 : ℚ) * p + (2 * 170 * 1 + 134 * 7) ≠ 0 := by
    convert hg using 1; ring
  have hpairs := Kunerth1880.Paragraf13.pairedNorms 170 134 69 1 7 67 x p
    (by norm_num) (by norm_num) (by norm_num) hp hg' hX'
  have hpair : ∃ ρ : ℤ, ρ ≠ 0 ∧ Int.gcd ρ 7 = 1 ∧
      (p.num ^ 2 - 170 * (p.den : ℤ) ^ 2) *
        (q.num ^ 2 - 170 * (q.den : ℤ) ^ 2) * ρ ^ 2 = 7 ^ 2 * (-28964) := by
    convert hpairs (by convert hq using 1; norm_num [q]) using 1; norm_num [q]
  obtain ⟨ρ, _hρ, _hρ7, hpair⟩ := hpair
  obtain ⟨hNp, hpstock⟩ := normStock x p hX
  obtain ⟨hNq, hqstock⟩ := normStock x q hXq
  obtain ⟨k₁, hk₁⟩ := hNp
  obtain ⟨k₂, hk₂⟩ := hNq
  /- Hilfsschritt: Nach XIIa müsste 557² die Zahl 7²(−4·13·557) theilen. -/
  have hnotboth : ¬ ((557 : ℤ) ∣ p.num ^ 2 - 170 * (p.den : ℤ) ^ 2 ∧
      (557 : ℤ) ∣ q.num ^ 2 - 170 * (q.den : ℤ) ^ 2) := by
    rintro ⟨h₁, h₂⟩
    have hdiv := dvd_mul_of_dvd_left (mul_dvd_mul h₁ h₂) (ρ ^ 2)
    rw [hpair] at hdiv
    norm_num at hdiv
  rw [hk₁, hk₂] at hnotboth
  by_cases hd : (557 : ℤ) ∣ k₁
  · exact excludeStock q k₂ hk₂ hqstock (fun h₂ =>
      hnotboth ⟨dvd_mul_of_dvd_right hd 7, dvd_mul_of_dvd_right h₂ 7⟩)
  · exact excludeStock p k₁ hk₁ hpstock hd

end Beispiel05

namespace Beispiel06

/-
6. Exempel:
y² = 145x²+20x−19 = (10x+1)²+5(3x+2)(3x−2);
-/

example (x : ℚ) : 145 * x ^ 2 + 20 * x - 19 = (10 * x + 1) ^ 2 + 5 * (3 * x + 2) * (3 * x - 2) := by ring

/- Rechenschritt: Der Nullpunkt eines angegebenen linearen Factors. -/

example : ∃ x y : ℚ, y ^ 2 = 145 * x ^ 2 + (20) * x + (-19) := by
  exact ⟨2 / 3, 23 / 3, by norm_num⟩

/-
3x = 2+2(23p+320)/(p²−145), S₁ = 3².2.5(571);
-/

example (p : ℚ) : (2) + (2 * (23) * p + (2 * 145 * (2) + (20) * 3)) / (p ^ 2 - 145) = (2) + 2 * ((23) * p + (320)) / (p ^ 2 - 145) := by ring

example : (3 ^ 2 * (20 ^ 2 - 4 * 145 * (-19)) / 2 : ℚ) = 3 ^ 2 * 2 * 5 * 571 := by norm_num

/-
streift man den eingeklammerten Factor ab, so können in Betracht
kommen: v² = 145w²∓15, in rationalen Zahlen unmöglich;
-/

private def noRational15 : Prop :=
  ∀ N : ℤ, N ∈ ([15, -15] : List ℤ) →
    ¬ ∃ v w : ℚ, v ^ 2 = 145 * w ^ 2 + N

private theorem noPlus15 (hRational : noRational15) :
    ¬ ∃ v w : ℚ, v ^ 2 = 145 * w ^ 2 + 15 :=
  hRational 15 (by simp)

private theorem noMinus15 (hRational : noRational15) :
    ¬ ∃ v w : ℚ, v ^ 2 = 145 * w ^ 2 - 15 := by
  simpa only [Int.cast_neg, Int.cast_ofNat, sub_eq_add_neg] using
    hRational (-15) (by simp)

/-
und v² = 145w²∓30 der 8-Reste wegen in ganzen Zahlen
unmöglich.
-/

example : ∀ v w : Fin 8, ((v.val : ℤ) ^ 2 - 145 * (w.val : ℤ) ^ 2 - (30)) % 8 ≠ 0 := by decide

example : ∀ v w : Fin 8, ((v.val : ℤ) ^ 2 - 145 * (w.val : ℤ) ^ 2 - (-30)) % 8 ≠ 0 := by decide

/- Hilfsschritt: Anwendung der Achterreste. -/

private theorem noThirty : ∀ N ∈ ([30, -30] : List ℤ),
    ¬ ∃ v w : ℤ, v ^ 2 = 145 * w ^ 2 + N := by
  intro N hN
  have hf : ∀ t ∈ ([30, -30] : List (ZMod 8)),
      ∀ v w : ZMod 8, v ^ 2 ≠ 145 * w ^ 2 + t := by decide
  have hN' : (N : ZMod 8) ∈ ([30, -30] : List (ZMod 8)) := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
    rcases hN with rfl | rfl <;> decide
  rintro ⟨v, w, h⟩
  apply hf (N : ZMod 8) hN' (v : ZMod 8) (w : ZMod 8)
  have he := congrArg (fun z : ℤ => (z : ZMod 8)) h
  push_cast at he
  exact he

/- Hilfsschritt: Der Nenner der p-Function ist nicht Null. -/

private theorem notSquare145 (p : ℚ) : p ^ 2 - 145 ≠ 0 := by
  intro h
  exact (show ¬ IsSquare (145 : ℚ) by norm_num) ⟨p, by nlinarith [h]⟩

/- Hilfsschritt: Theilbarkeit des Nenners und die Stammzahl. -/

private theorem normStock (x : ℤ) (p : ℚ)
    (hX : (3 : ℚ) * x = 2 + (46 * p + 640) / (p ^ 2 - 145)) :
    3 ∣ p.num ^ 2 - 145 * (p.den : ℤ) ^ 2 ∧
      p.num ^ 2 - 145 * (p.den : ℤ) ^ 2 ∣ 17130 := by
  have hp := notSquare145 p
  have hXd : (3 : ℚ) * x = 2 + (2 * 23 * p + (2 * 145 * 2 + 20 * 3)) / (p ^ 2 - 145) := by
    norm_num at *
    exact hX
  obtain ⟨k, hk⟩ := Kunerth1880.Paragraf07.preparationFromVIII
    145 20 2 3 23 10 1 (-15) 10 x p (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hp hXd
  let v := p.num
  let w : ℤ := p.den
  let N : ℤ := v ^ 2 - 145 * w ^ 2
  have hprep : v = 3 * k - 10 * w := by dsimp [v, w]; linear_combination hk
  have hcop : Int.gcd v w = 1 := by simpa [v,w,Int.gcd] using p.reduced
  have hN3 : 3 ∣ N := Kunerth1880.Paragraf06.normMultiple 145 3 10 (-15) k v w hprep (by norm_num)
  have hw : (w : ℚ) ≠ 0 := by dsimp [w]; exact_mod_cast p.den_nz
  have hpv : p = (v : ℚ) / w := by simpa [v,w] using (Rat.num_div_den p).symm
  have hcross : ((3 : ℚ) * x - 2) * (p ^ 2 - 145) = 46 * p + 640 := by
    exact (eq_div_iff hp).mp (by linear_combination hX)
  rw [hpv] at hcross
  field_simp [hw] at hcross
  have hXi : (3 * x - 2) * N = (46 * v + 640 * w) * w := by
    have hq : ((3 : ℚ) * x - 2) * ((v : ℚ) ^ 2 - 145 * w ^ 2) =
        (46 * v + 640 * w) * w := by linear_combination hcross
    exact_mod_cast hq
  let L := x * (23 * v - 320 * w) + 14 * w - 46 * k
  have hL : N * L = -17130 * w ^ 3 := by
    have h : 3 * (N * L + 17130 * w ^ 3) = 0 := by
      dsimp [N, L] at *
      linear_combination (23 * v - 320 * w) * hXi + 46 * (v ^ 2 - 145 * w ^ 2) * hprep
    linarith
  refine ⟨hN3, ?_⟩
  apply (Kunerth1880.Paragraf07.normCoprime 145 v w hcop).dvd_of_dvd_mul_left
  exact ⟨-L, by linear_combination hL⟩

/- Hilfsschritt: Ausscheidung der unzulässigen Factoren. -/

private theorem stockCandidates (p : ℚ) (k : ℤ)
    (hN : p.num ^ 2 - 145 * (p.den : ℤ) ^ 2 = 3 * k)
    (hstock : p.num ^ 2 - 145 * (p.den : ℤ) ^ 2 ∣ 17130)
    (hprime : ¬ (571 : ℤ) ∣ k) :
    p.num ^ 2 - 145 * (p.den : ℤ) ^ 2 ∈ ([3,-3,6,-6,15,-15,30,-30] : List ℤ) := by
  have hk : k ∣ 5710 := by
    obtain ⟨t, ht⟩ := hstock
    refine ⟨t, ?_⟩
    rw [hN] at ht
    nlinarith [ht]
  have hcop : IsCoprime k (571 : ℤ) :=
    ((show Prime (571 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hprime).symm
  have hsmall : k ∣ 10 := hcop.dvd_of_dvd_mul_right (by convert hk using 1; norm_num)
  have hkmem : k ∈ (10 : ℤ).divisors := Int.mem_divisors.mpr ⟨hsmall, by norm_num⟩
  have hdivs : (10 : ℤ).divisors = {1,-1,2,-2,5,-5,10,-10} := by decide
  rw [hdivs] at hkmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hkmem
  rcases hkmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [hN]; decide

/- Hilfsschritt: Übergang von der Gleichung zu den Nennern. -/

private theorem normCandidates (x y : ℤ)
    (h : y ^ 2 = 145 * x ^ 2 + 20 * x + (-19)) :
    ∃ v w : ℤ, Int.gcd v w = 1 ∧
      v ^ 2 - 145 * w ^ 2 ∈ ([3,-3,6,-6,15,-15,30,-30] : List ℤ) := by
  have hsI : 3 * x - (2) ≠ 0 := by omega
  have hs : (3 : ℚ) * x - (2) ≠ 0 := by exact_mod_cast hsI
  have hQ : (y : ℚ) ^ 2 = 145 * (x : ℚ) ^ 2 + 20 * x + (-19) := by exact_mod_cast h
  let p : ℚ := (3 * y + 23) / (3 * x - (2))
  have hP : ((3 : ℚ) * x - (2)) * p = 3 * y + 23 := by dsimp [p]; field_simp
  have hp := notSquare145 p
  have hcross : ((3 : ℚ) * x - (2)) * (p ^ 2 - 145) = 46 * p + 640 := by
    apply mul_left_cancel₀ hs
    linear_combination (((3 : ℚ) * x - (2)) * p + 3 * y - 23) * hP + 9 * hQ
  have hX : (3 : ℚ) * x = (2) + (46 * p + 640) / (p ^ 2 - 145) := by
    have hc := (eq_div_iff hp).mpr hcross
    linarith
  have hg : 46 * p + 640 ≠ 0 := by
    intro hz
    rw [hz, zero_div] at hX
    exact hs (by linarith)
  let q : ℚ := -(640 * p + 6670) / (46 * p + 640)
  have hq := notSquare145 q
  have hqcross : q * (46 * p + 640) = -(640 * p + 6670) := by
    dsimp [q]
    exact div_mul_cancel₀ _ hg
  have heq : (46 * q + 640) / (q ^ 2 - 145) = (46 * p + 640) / (p ^ 2 - 145) := by
    apply (div_eq_div_iff hq hp).mpr
    linear_combination (p - q) * hqcross
  have hXq : (3 : ℚ) * x = (2) + (46 * q + 640) / (q ^ 2 - 145) := by rw [heq]; exact hX
  have hX' : (3 : ℚ) * x = (2) +
      (2 * 23 * p + (2 * 145 * (2) + 20 * 3)) / (p ^ 2 - 145) := by convert hX using 1; ring
  have hg' : 2 * (23 : ℚ) * p + (2 * 145 * (2) + 20 * 3) ≠ 0 := by convert hg using 1; ring
  have hpairs := Kunerth1880.Paragraf13.pairedNorms 145 20 (-19) (2) 3 23 x p
    (by norm_num) (by norm_num) (by norm_num) hp hg' hX'
  have hpair : ∃ ρ : ℤ, ρ ≠ 0 ∧ Int.gcd ρ 3 = 1 ∧
      (p.num ^ 2 - 145 * (p.den : ℤ) ^ 2) *
        (q.num ^ 2 - 145 * (q.den : ℤ) ^ 2) * ρ ^ 2 = 3 ^ 2 * (11420) := by
    convert hpairs (by convert hq using 1; norm_num [q]) using 1; norm_num [q]
  obtain ⟨ρ, _hρ, _hρn, hpair⟩ := hpair
  obtain ⟨hNp,hpstock⟩ := normStock x p hX
  obtain ⟨hNq,hqstock⟩ := normStock x q hXq
  obtain ⟨k₁,hk₁⟩ := hNp
  obtain ⟨k₂,hk₂⟩ := hNq
  /- Hilfsschritt: XIIa mit n = 3 und D = 4 · 5 · 571. -/
  have hnotboth : ¬ ((571 : ℤ) ∣ p.num ^ 2 - 145 * (p.den : ℤ) ^ 2 ∧
      (571 : ℤ) ∣ q.num ^ 2 - 145 * (q.den : ℤ) ^ 2) := by
    rintro ⟨h₁, h₂⟩
    have hdiv := dvd_mul_of_dvd_left (mul_dvd_mul h₁ h₂) (ρ ^ 2)
    rw [hpair] at hdiv
    norm_num at hdiv
  rw [hk₁, hk₂] at hnotboth
  by_cases hd : (571 : ℤ) ∣ k₁
  · refine ⟨q.num, (q.den : ℤ), ?_, stockCandidates q k₂ hk₂ hqstock (fun h₂ =>
      hnotboth ⟨dvd_mul_of_dvd_right hd 3, dvd_mul_of_dvd_right h₂ 3⟩)⟩
    simpa [Int.gcd] using q.reduced
  · refine ⟨p.num, (p.den : ℤ), ?_, stockCandidates p k₁ hk₁ hpstock hd⟩
    simpa [Int.gcd] using p.reduced

/- Hilfsdefinition: Ein Rechenschritt der Kettenbruchentwicklung. -/

private def tennerStep145 (s : ℤ × ℤ) : ℤ × ℤ :=
  let q := (12 + s.1) / s.2
  let m := q * s.2 - s.1
  (m, (145 - m ^ 2) / s.2)

/- Hilfsschritt: Fortsetzung der berechneten Kettenbruchperiode. -/

private theorem tennerState145 (k : ℕ) :
    (tennerStep145^[k + 1]) (0, 1) = (12, 1) := by
  induction k with
  | zero => decide
  | succ k ih => rw [Function.iterate_succ_apply', ih]; decide

/- Hilfsschritt: Fortsetzung der berechneten Kettenbruchperiode. -/

private theorem tennerAllStates145 (k : ℕ) :
    (tennerStep145^[k]) (0, 1) ∈ ([(0, 1), (12, 1)] : List (ℤ × ℤ)) := by
  cases k with
  | zero => decide
  | succ k => rw [tennerState145]; decide

/- Hilfsdefinition: Die III. Verticalreihe der Rechnung. -/

private def tennerM145 (k : ℕ) : ℤ := ((tennerStep145^[k]) (0, 1)).1

/- Hilfsdefinition: Die VI. Verticalreihe der Rechnung. -/

private def tennerQ145 (k : ℕ) : ℤ := ((tennerStep145^[k]) (0, 1)).2

/- Hilfsdefinition: Die I. Verticalreihe der Rechnung. -/

private def tennerA145 (k : ℕ) : ℤ := (12 + tennerM145 k) / tennerQ145 k

/- Hilfsschritt: Ganzzahlige Quotienten und genaue Divisionen der Kette. -/

private theorem tennerData145 : tennerM145 0 = 0 ∧ tennerQ145 0 = 1 ∧
    (∀ k, (tennerA145 k : ℝ) ≤
        (Real.sqrt (145 : ℤ) + tennerM145 k) / tennerQ145 k ∧
      (Real.sqrt (145 : ℤ) + tennerM145 k) / tennerQ145 k < tennerA145 k + 1) ∧
    (∀ k, tennerM145 (k + 1) = tennerA145 k * tennerQ145 k - tennerM145 k) ∧
    (∀ k, tennerQ145 (k + 1) * tennerQ145 k = 145 - tennerM145 (k + 1) ^ 2) := by
  have hs : (Real.sqrt 145) ^ 2 = 145 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 145 := Real.sqrt_nonneg _
  have hlo : (12 : ℝ) ≤ Real.sqrt 145 := by nlinarith
  have hhi : Real.sqrt 145 < (13 : ℝ) := by nlinarith
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro k
    have hk := tennerAllStates145 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with hk | hk
    all_goals norm_num [tennerA145, tennerM145, tennerQ145, hk]
    all_goals constructor <;> linarith
  · intro k
    simp only [tennerM145, tennerA145, tennerQ145, Function.iterate_succ_apply']
    rfl
  · intro k
    have hk := tennerAllStates145 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    simp only [tennerM145, tennerQ145, Function.iterate_succ_apply']
    rcases hk with hk | hk <;> rw [hk] <;> decide

/- Hilfsschritt: Anwendung des als Voraussetzung geführten Kriteriums. -/

private theorem specializeCriterion145
    (hCriterion : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ∀ N : ℤ, N ^ 2 < 145 →
      (∀ k : ℕ, ((tennerStep145^[k + 1]) (0, 1)).2 ≠ |N|) →
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 145 * w ^ 2 + N := by
  intro N hN habsent
  obtain ⟨hM, hQ, hfloor, hMstep, hQstep⟩ := tennerData145
  have hns : ¬ ∃ q : ℤ, q ^ 2 = 145 := by
    rintro ⟨q, hq⟩
    have hs : IsSquare (145 : ℤ) := ⟨q, by nlinarith [hq]⟩
    norm_num at hs
  have hNreal : (|N| : ℤ) < Real.sqrt (145 : ℤ) := by
    have hsq : (((|N| : ℤ) : ℝ)) ^ 2 < 145 := by
      exact_mod_cast (show |N| ^ 2 < 145 by simpa only [sq_abs] using hN)
    have hs : (Real.sqrt 145) ^ 2 = 145 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt 145 := Real.sqrt_nonneg _
    norm_num only [Int.cast_ofNat]
    nlinarith
  exact hCriterion 145 N tennerA145 tennerM145 tennerQ145 (by norm_num) hns
    hM hQ hfloor hMstep hQstep hNreal habsent

/- Folgerung unter Voraussetzung der behaupteten rationalen Unmöglichkeit
und des Kriteriums des §. 23. -/

example
    (hRational : noRational15)
    (hSource : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ¬ ∃ x y : ℤ, y ^ 2 = 145 * x ^ 2 + 20 * x - 19 := by
  have hsmall : ∀ N ∈ ([3,-3,6,-6] : List ℤ),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 145 * w ^ 2 + N := by
    intro N hN
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
    rcases hN with rfl | rfl | rfl | rfl
    all_goals apply specializeCriterion145 hSource _ (by norm_num)
    all_goals intro k; rw [tennerState145]; norm_num
  rintro ⟨x,y,h⟩
  obtain ⟨v,w,hcop,hN⟩ := normCandidates x y h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
  rcases hN with hN | hN | hN | hN | hN | hN | hN | hN
  · exact hsmall 3 (by decide) ⟨v,w,hcop,by linarith⟩
  · exact hsmall (-3) (by decide) ⟨v,w,hcop,by linarith⟩
  · exact hsmall 6 (by decide) ⟨v,w,hcop,by linarith⟩
  · exact hsmall (-6) (by decide) ⟨v,w,hcop,by linarith⟩
  · apply noPlus15 hRational
    refine ⟨v,w,?_⟩
    exact_mod_cast (show v ^ 2 = 145 * w ^ 2 + 15 by linarith)
  · apply noMinus15 hRational
    refine ⟨v,w,?_⟩
    exact_mod_cast (show v ^ 2 = 145 * w ^ 2 - 15 by linarith)
  · exact noThirty 30 (by decide) ⟨v,w,by linarith⟩
  · exact noThirty (-30) (by decide) ⟨v,w,by linarith⟩

end Beispiel06

namespace Beispiel07

/-
7. Exempel:
y² = 79x²−14 = (3x+2)²+2(7x+3)(5x−3),
-/

example (x : ℚ) : 79 * x ^ 2 - 14 = (3 * x + 2) ^ 2 + 2 * (7 * x + 3) * (5 * x - 3) := by ring

/- Rechenschritt: Der Nullpunkt eines angegebenen linearen Factors. -/

example : ∃ x y : ℚ, y ^ 2 = 79 * x ^ 2 + (0) * x + (-14) := by
  exact ⟨3 / 5, 19 / 5, by norm_num⟩

/-
5x = 3+2(19p+237)/(p²−79), S₁ = 5².4.(7.79)
-/

example (p : ℚ) : (3) + (2 * (19) * p + (2 * 79 * (3) + (0) * 5)) / (p ^ 2 - 79) = (3) + 2 * ((19) * p + (237)) / (p ^ 2 - 79) := by ring

example : (5 ^ 2 * (-4 * 79 * (-14)) / 2 : ℚ) = 5 ^ 2 * 4 * (7 * 79) := by norm_num

/-
Seite 373

löscht man 7 und 79, so bleibt
v² = 79w²+10, Δ² = 79β²+10(α²−79), α = 9
und durch 4 dividiren: Δ₁² = 79β₁²+5 in ganzen Zahlen unmöglich.
-/

example : (10 * (9 ^ 2 - 79) / 4 : ℚ) = 5 := by norm_num

example : (8 : ℤ) ^ 2 ≤ 79 ∧ 79 < (8 + 1) ^ 2 := by decide

/- Hilfsdefinition: Ein Rechenschritt der Kettenbruchentwicklung. -/

private def tennerStep79 (s : ℤ × ℤ) : ℤ × ℤ :=
  let q := (8 + s.1) / s.2
  let m := q * s.2 - s.1
  (m, (79 - m ^ 2) / s.2)

example :
    ((List.range 5).map fun k => (tennerStep79^[k + 1]) (0, 1)) =
      [(8, 15), (7, 2), (7, 15), (8, 1), (8, 15)] := by decide

example : ([((0, 1) : ℤ × ℤ), (8, 15), (7, 2), (7, 15), (8, 1)]).all
    (fun s => decide (s.2 ≠ 0) && (79 - (tennerStep79 s).1 ^ 2) % s.2 == 0) := by decide

/- Hilfsschritt: Fortsetzung der berechneten Kettenbruchperiode. -/

private theorem tennerStates79 (k : ℕ) :
    (tennerStep79^[k + 1]) (0, 1) ∈
      ([(8, 15), (7, 2), (7, 15), (8, 1)] : List (ℤ × ℤ)) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ih
    rcases ih with h | h | h | h <;> rw [h] <;> decide

/- Hilfsschritt: Fortsetzung der berechneten Kettenbruchperiode. -/

private theorem tennerAllStates79 (k : ℕ) :
    (tennerStep79^[k]) (0, 1) ∈
      ([(0, 1), (8, 15), (7, 2), (7, 15), (8, 1)] : List (ℤ × ℤ)) := by
  cases k with
  | zero => decide
  | succ k => exact List.mem_cons_of_mem _ (tennerStates79 k)

/- Hilfsdefinition: Die III. Verticalreihe der Rechnung. -/

private def tennerM79 (k : ℕ) : ℤ := ((tennerStep79^[k]) (0, 1)).1

/- Hilfsdefinition: Die VI. Verticalreihe der Rechnung. -/

private def tennerQ79 (k : ℕ) : ℤ := ((tennerStep79^[k]) (0, 1)).2

/- Hilfsdefinition: Die I. Verticalreihe der Rechnung. -/

private def tennerA79 (k : ℕ) : ℤ := (8 + tennerM79 k) / tennerQ79 k

/- Hilfsschritt: Ganzzahlige Quotienten und genaue Divisionen der Kette. -/

private theorem tennerData79 : tennerM79 0 = 0 ∧ tennerQ79 0 = 1 ∧
    (∀ k, (tennerA79 k : ℝ) ≤
        (Real.sqrt (79 : ℤ) + tennerM79 k) / tennerQ79 k ∧
      (Real.sqrt (79 : ℤ) + tennerM79 k) / tennerQ79 k < tennerA79 k + 1) ∧
    (∀ k, tennerM79 (k + 1) = tennerA79 k * tennerQ79 k - tennerM79 k) ∧
    (∀ k, tennerQ79 (k + 1) * tennerQ79 k = 79 - tennerM79 (k + 1) ^ 2) := by
  have hs : (Real.sqrt 79) ^ 2 = 79 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 79 := Real.sqrt_nonneg _
  have hlo : (8 : ℝ) ≤ Real.sqrt 79 := by nlinarith
  have hhi : Real.sqrt 79 < (9 : ℝ) := by nlinarith
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro k
    have hk := tennerAllStates79 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with hk | hk | hk | hk | hk
    all_goals norm_num [tennerA79, tennerM79, tennerQ79, hk]
    all_goals constructor <;> linarith
  · intro k
    simp only [tennerM79, tennerA79, tennerQ79, Function.iterate_succ_apply']
    rfl
  · intro k
    have hk := tennerAllStates79 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    simp only [tennerM79, tennerQ79, Function.iterate_succ_apply']
    rcases hk with hk | hk | hk | hk | hk <;> rw [hk] <;> decide

/- Hilfsschritt: Anwendung des als Voraussetzung geführten Kriteriums. -/

private theorem specializeCriterion79
    (hCriterion : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ∀ N : ℤ, N ^ 2 < 79 →
      (∀ k : ℕ, ((tennerStep79^[k + 1]) (0, 1)).2 ≠ |N|) →
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 + N := by
  intro N hN habsent
  obtain ⟨hM, hQ, hfloor, hMstep, hQstep⟩ := tennerData79
  have hns : ¬ ∃ q : ℤ, q ^ 2 = 79 := by
    rintro ⟨q, hq⟩
    have hs : IsSquare (79 : ℤ) := ⟨q, by nlinarith [hq]⟩
    norm_num at hs
  have hNreal : (|N| : ℤ) < Real.sqrt (79 : ℤ) := by
    have hsq : (((|N| : ℤ) : ℝ)) ^ 2 < 79 := by
      exact_mod_cast (show |N| ^ 2 < 79 by simpa only [sq_abs] using hN)
    have hs : (Real.sqrt 79) ^ 2 = 79 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt 79 := Real.sqrt_nonneg _
    norm_num only [Int.cast_ofNat]
    nlinarith
  exact hCriterion 79 N tennerA79 tennerM79 tennerQ79 (by norm_num) hns
    hM hQ hfloor hMstep hQstep hNreal habsent

/- Hilfsschritt: Ausschluss des Zahlengliedes 5 mit dem vorausgesetzten Kriterium. -/

private theorem auxiliaryImpossible5
    (hCriterion : ∀ N : ℤ, N ^ 2 < 79 →
      (∀ k : ℕ, ((tennerStep79^[k + 1]) (0, 1)).2 ≠ |N|) →
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 + N) :
    ¬ ∃ v w : ℤ, v ^ 2 = 79 * w ^ 2 + 5 := by
  rintro ⟨v, w, h⟩
  let g : ℤ := Int.gcd v w
  have hgv : g ∣ v := Int.gcd_dvd_left v w
  have hgw : g ∣ w := Int.gcd_dvd_right v w
  have hd : g ^ 2 ∣ 5 := by
    have hdiff := dvd_sub (pow_dvd_pow_of_dvd hgv 2)
      (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hgw 2) 79)
    have heq : v ^ 2 - 79 * w ^ 2 = 5 := by linarith [h]
    rwa [heq] at hdiff
  have hdNat : (Int.gcd v w) ^ 2 ∣ 5 := by
    dsimp [g] at hd
    exact_mod_cast hd
  have hs : Squarefree (5 : ℕ) := (by decide : Nat.Prime 5).squarefree
  have hu : IsUnit (Int.gcd v w) := hs (Int.gcd v w) (by simpa only [pow_two] using hdNat)
  have hcop := Nat.isUnit_iff.mp hu
  have hrow : ∀ k : ℕ, ((tennerStep79^[k + 1]) (0, 1)).2 ≠ |(5 : ℤ)| := by
    intro k
    have ht := tennerStates79 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with h | h | h | h <;> rw [h] <;> norm_num
  exact hCriterion 5 (by decide) hrow ⟨v, w, hcop, h⟩

/- Hilfsschritt: α = 9 und die Division durch 4. -/

private theorem norm10Impossible
    (hCriterion : ∀ N : ℤ, N ^ 2 < 79 →
      (∀ k : ℕ, ((tennerStep79^[k + 1]) (0, 1)).2 ≠ |N|) →
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 + N) :
    ¬ ∃ v w : ℤ, v ^ 2 = 79 * w ^ 2 + 10 := by
  rintro ⟨v, w, h⟩
  let β := v - 9 * w
  have hIII : v = 9 * w + β := by dsimp [β]; ring
  have hquadratic : (79 - 9 ^ 2) * w ^ 2 - 2 * 9 * β * w + 10 - β ^ 2 = 0 := by
    rw [hIII] at h
    linear_combination -h
  let Δ := (79 - 9 ^ 2) * w - 9 * β
  have hIV : Δ ^ 2 = 79 * β ^ 2 + 20 := by
    dsimp [Δ]
    linear_combination (79 - 9 ^ 2) * hquadratic
  have hΔ0 := Int.emod_nonneg Δ (by norm_num : (4 : ℤ) ≠ 0)
  have hΔ4 := Int.emod_lt_of_pos Δ (by norm_num : (0 : ℤ) < 4)
  have hβ0 := Int.emod_nonneg β (by norm_num : (4 : ℤ) ≠ 0)
  have hβ4 := Int.emod_lt_of_pos β (by norm_num : (0 : ℤ) < 4)
  have hm : (Δ ^ 2 - 79 * β ^ 2) % 4 = 0 := by rw [hIV]; norm_num
  have hm' : ((Δ % 4) ^ 2 - 79 * (β % 4) ^ 2) % 4 = 0 := by
    simpa only [pow_two, Int.sub_emod, Int.mul_emod, Int.emod_emod] using hm
  have heven : Δ % 2 = 0 ∧ β % 2 = 0 := by
    interval_cases hd : Δ % 4 <;> interval_cases hb : β % 4 <;>
      norm_num [hd, hb] at hm' <;> omega
  obtain ⟨Δ₁, hΔ₁⟩ := Int.dvd_of_emod_eq_zero heven.1
  obtain ⟨β₁, hβ₁⟩ := Int.dvd_of_emod_eq_zero heven.2
  apply auxiliaryImpossible5 hCriterion
  refine ⟨Δ₁, β₁, ?_⟩
  rw [hΔ₁, hβ₁] at hIV
  nlinarith [hIV]

/- Hilfsschritt: Der Nenner der p-Function ist nicht Null. -/

private theorem notSquare79 (p : ℚ) : p ^ 2 - 79 ≠ 0 := by
  intro h
  have hs : IsSquare (79 : ℚ) := ⟨p, by nlinarith [h]⟩
  have hi : IsSquare (79 : ℤ) := Rat.isSquare_intCast_iff.mp hs
  norm_num at hi

/- Hilfsschritt: Bildung des Parameters der p-Function. -/

private theorem parameter79 (b c m n r x y : ℤ)
    (hbase : r ^ 2 = 79 * m ^ 2 + b * m * n + c * n ^ 2)
    (hroot : y ^ 2 = 79 * x ^ 2 + b * x + c) (hx : n * x - m ≠ 0) :
    ∃ p : ℚ, (n : ℚ) * x = m +
      (2 * r * p + (2 * 79 * m + b * n)) / (p ^ 2 - 79) := by
  have hxQ : (n : ℚ) * x - m ≠ 0 := by exact_mod_cast hx
  let p : ℚ := (n * (y : ℚ) + r) / (n * x - m)
  have hline : p * ((n : ℚ) * x - m) = n * y + r := by
    dsimp [p]
    exact div_mul_cancel₀ _ hxQ
  have hbQ : (r : ℚ) ^ 2 = 79 * (m : ℚ) ^ 2 + b * m * n + c * n ^ 2 := by exact_mod_cast hbase
  have hrQ : (y : ℚ) ^ 2 = 79 * (x : ℚ) ^ 2 + b * x + c := by exact_mod_cast hroot
  have hpoly : ((n : ℚ) * x - m) * (p ^ 2 - 79) =
      2 * r * p + (2 * 79 * m + b * n) := by
    apply mul_right_cancel₀ hxQ
    linear_combination (p * ((n : ℚ) * x - m) + n * y - r) * hline + n ^ 2 * hrQ - hbQ
  refine ⟨p, ?_⟩
  have he := (eq_div_iff (notSquare79 p)).2 hpoly
  linear_combination he

/- Hilfsschritt: Auswahl des äquivalenten Parameters. -/

private theorem selectAux79
    (hSelection : Kunerth1880.Paragraf16.singularPrimeSelection)
    (c m n r α β γ δ t x y : ℤ)
    (hn : 0 < n) (hmn : Int.gcd m n = 1) (hnm : ¬ n ∣ m)
    (ha : 79 = α ^ 2 - n * γ) (hb : 0 = 2 * α * β + m * γ + n * δ)
    (hc : c = β ^ 2 - m * δ) (hr : r = m * α + n * β)
    (ht : Prime t) (htc : t ∣ c)
    (hs79 : ¬ (79 : ℤ) ^ 2 ∣ -4 * 79 * c) (hst : ¬ t ^ 2 ∣ -4 * 79 * c)
    (hroot : y ^ 2 = 79 * x ^ 2 + c) :
    ∃ q : ℚ, ∃ z : ℤ,
      (n : ℚ) * z = m + (2 * r * q + 2 * 79 * m) / (q ^ 2 - 79) ∧
      n ∣ (q.num ^ 2 - 79 * (q.den : ℤ) ^ 2) ∧ ¬ 79 ∣ (q.num ^ 2 - 79 * (q.den : ℤ) ^ 2) ∧ ¬ t ∣ (q.num ^ 2 - 79 * (q.den : ℤ) ^ 2) := by
  have hbase : r ^ 2 = 79 * m ^ 2 + c * n ^ 2 := by
    rw [ha, hc, hr]
    linear_combination -m * n * hb
  have hx : n * x - m ≠ 0 := by
    intro h
    exact hnm ⟨x, by linear_combination -h⟩
  obtain ⟨p, hX⟩ := parameter79 0 c m n r x y (by simpa using hbase) (by simpa using hroot) hx
  simp only [Int.cast_zero, zero_mul, add_zero] at hX
  have hxQ : (n : ℚ) * x - m ≠ 0 := by exact_mod_cast hx
  have hpoly : ((n : ℚ) * x - m) * (p ^ 2 - 79) = 2 * r * p + 2 * 79 * m := by
    apply (eq_div_iff (notSquare79 p)).mp
    linear_combination hX
  have hleft : (n : ℚ) * x ≠ -(m : ℚ) := by
    intro he
    have heI : n * x = -m := by exact_mod_cast he
    exact hnm ⟨-x, by linear_combination heI⟩
  have hp0 : p ≠ 0 := by
    intro he
    rw [he] at hpoly
    apply hleft
    linear_combination (-1 / 79 : ℚ) * hpoly
  have hden1 : (r : ℚ) * p + 79 * m ≠ 0 := by
    intro he
    have hz : ((n : ℚ) * x - m) * (p ^ 2 - 79) = 0 := by linear_combination hpoly + 2 * he
    exact mul_ne_zero hxQ (notSquare79 p) hz
  have hden2 : (m : ℚ) * p + r ≠ 0 := by
    intro he
    have hz : ((n : ℚ) * x + m) * (p ^ 2 - 79) = 0 := by linear_combination hpoly + 2 * p * he
    have hzero := (mul_eq_zero.mp hz).resolve_right (notSquare79 p)
    apply hleft
    linear_combination hzero
  obtain ⟨k, hk⟩ := Kunerth1880.Paragraf07.preparationFromVIII 79 0 m n r α β γ δ x p
    (ne_of_gt hn) hmn ha hb hr (notSquare79 p) (by simpa using hX)
  have hprep : p.num = n * k - α * (p.den : ℤ) := by linear_combination hk
  have hsel := hSelection 79 c m n r x α β γ k 79 t p
    hn hmn hbase hr (by linear_combination -ha) hprep hp0 (notSquare79 p) hden1 hden2
    (by linear_combination hX) (by norm_num) ht (by norm_num) htc hs79 hst
  dsimp only at hsel
  obtain ⟨q, _hchoices, _hq, ⟨z, hZ⟩, hN, h79, htN⟩ :=
    hsel (notSquare79 _) (notSquare79 _) (notSquare79 _)
  refine ⟨q, z, ?_, hN, h79, htN⟩
  linear_combination hZ

/- Hilfsschritt: Ausscheidung von 7 und 79 aus der Stammzahl. -/

private theorem parameterCases79
    (hSelection : Kunerth1880.Paragraf16.singularPrimeSelection)
    (x y : ℤ) (hroot : y ^ 2 = 79 * x ^ 2 - 14) :
    ∃ p : ℚ, ∃ z : ℤ,
      (5 : ℚ) * z = 3 + (38 * p + 474) / (p ^ 2 - 79) ∧
      (p.num ^ 2 - 79 * (p.den : ℤ) ^ 2) ∈ ([-10, -5, 5, 10] : List ℤ) := by
  obtain ⟨p, z, hX, h5, h79, h7⟩ := selectAux79 hSelection (-14) 3 5 19 3 2 (-14) 6 7 x y
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by linarith [hroot])
  have hstock := (Kunerth1880.Paragraf07.normData 79 0 (-14) 3 5 19 3 2 (-14) 6 z p
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (notSquare79 p) (by simpa using hX)).2
  let N := p.num ^ 2 - 79 * (p.den : ℤ) ^ 2
  have hc79 : IsCoprime N 79 := ((show Prime (79 : ℤ) by norm_num).coprime_iff_not_dvd.mpr h79).symm
  have hc7 : IsCoprime N 7 := ((show Prime (7 : ℤ) by norm_num).coprime_iff_not_dvd.mpr h7).symm
  have h40 : N ∣ 40 := by
    apply (hc7.mul_right hc79).dvd_of_dvd_mul_right
    convert hstock using 1; norm_num
  obtain ⟨t, ht⟩ := h5
  have ht8 : t ∣ 8 := by
    obtain ⟨u, hu⟩ := h40
    refine ⟨u, ?_⟩
    change N = 5 * t at ht
    rw [ht] at hu
    nlinarith [hu]
  have hcop : Int.gcd p.num (p.den : ℤ) = 1 := by
    simpa [Int.gcd] using p.reduced
  have hnot4 : ¬ 4 ∣ N := by
    rintro ⟨u, hu⟩
    have hnorm : p.num ^ 2 = 79 * (p.den : ℤ) ^ 2 + 4 * u := by
      dsimp [N] at hu
      linear_combination hu
    have hm := congrArg (fun k : ℤ => (k : ZMod 8)) hnorm
    push_cast at hm
    have table : ∀ v w u : ZMod 8, v ^ 2 = 79 * w ^ 2 + 4 * u →
        (ZMod.cast v : ZMod 2) = 0 ∧ (ZMod.cast w : ZMod 2) = 0 := by decide
    have hev := table _ _ _ hm
    rw [ZMod.cast_intCast (by decide : 2 ∣ 8), ZMod.cast_natCast (by decide : 2 ∣ 8)] at hev
    have hpv : (2 : ℤ) ∣ p.num := (ZMod.intCast_zmod_eq_zero_iff_dvd p.num 2).mp hev.1
    have hpw : (2 : ℤ) ∣ (p.den : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (p.den : ℤ) 2).mp hev.2
    have hdiv := Int.dvd_gcd hpv hpw
    rw [hcop] at hdiv
    norm_num at hdiv
  have hnot4t : ¬ 4 ∣ t := by
    rintro ⟨u, hu⟩
    apply hnot4
    exact ⟨5 * u, by dsimp [N]; rw [ht, hu]; ring⟩
  have hmem : t ∈ (8 : ℤ).divisors := Int.mem_divisors.mpr ⟨ht8, by norm_num⟩
  have hdivs : (8 : ℤ).divisors = {1, -1, 2, -2, 4, -4, 8, -8} := by decide
  rw [hdivs] at hmem
  refine ⟨p, z, ?_, ?_⟩
  · convert hX using 1; norm_num
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals solve | norm_num [ht] | exact False.elim (hnot4t (by norm_num))

/- Folgerung mit den als Voraussetzungen geführten Aussagen aus §. 16
und §. 23. -/

theorem noIntegerSolutions
    (hSelection : Kunerth1880.Paragraf16.singularPrimeSelection)
    (hSource : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ¬ ∃ x y : ℤ, y ^ 2 = 79 * x ^ 2 - 14 := by
  rintro ⟨x, y, hroot⟩
  have hCriterion := specializeCriterion79 hSource
  obtain ⟨p, _z, _hX, hcases⟩ := parameterCases79 hSelection x y hroot
  have hcop : Int.gcd p.num (p.den : ℤ) = 1 := by
    simpa [Int.gcd] using p.reduced
  have hnorm : p.num ^ 2 = 79 * (p.den : ℤ) ^ 2 +
      (p.num ^ 2 - 79 * (p.den : ℤ) ^ 2) := by ring
  have hrow : ∀ k : ℕ, ((tennerStep79^[k + 1]) (0, 1)).2 ≠ (5 : ℤ) := by
    intro k
    have hs := tennerStates79 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with h | h | h | h <;> rw [h] <;> norm_num
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcases
  rcases hcases with h | h | h | h
  · have hm := congrArg (fun z : ℤ => (z : ZMod 8)) hnorm
    rw [h] at hm
    push_cast at hm
    have table : ∀ v w : ZMod 8, v ^ 2 ≠ 79 * w ^ 2 + (-10) := by decide
    exact table _ _ hm
  · apply hCriterion (-5) (by decide) (by simpa using hrow)
    exact ⟨p.num, p.den, hcop, by simpa [h] using hnorm⟩
  · apply hCriterion 5 (by decide) (by simpa using hrow)
    exact ⟨p.num, p.den, hcop, by simpa [h] using hnorm⟩
  · apply norm10Impossible hCriterion
    exact ⟨p.num, p.den, by simpa [h] using hnorm⟩

end Beispiel07

namespace Beispiel08

/-
8. Exempel:
y² = 79x²+7.2399 = (10x+53)²−(3x+184)(7x−76);
-/

example (x : ℚ) : 79 * x ^ 2 + 7 * 2399 = (10 * x + 53) ^ 2 - (3 * x + 184) * (7 * x - 76) := by ring

/- Rechenschritt: Der Nullpunkt eines angegebenen linearen Factors. -/

example : ∃ x y : ℚ, y ^ 2 = 79 * x ^ 2 + (0) * x + (16793) := by
  exact ⟨76 / 7, 1131 / 7, by norm_num⟩

/-
7x = 76+2(1131p+6004)/(p²−79) S₁ = −2.7³(79.2399);
-/

example (p : ℚ) : (76) + (2 * (1131) * p + (2 * 79 * (76) + (0) * 7)) / (p ^ 2 - 79) = (76) + 2 * ((1131) * p + (6004)) / (p ^ 2 - 79) := by ring

example : (7 ^ 2 * (-4 * 79 * 7 * 2399) / 2 : ℚ) = -2 * 7 ^ 3 * (79 * 2399) := by norm_num

/-
hier kommen in Betracht:
v² = 79w²∓7(1, 2, 7, 14); N = −7
ist wegen der VI. Verticalreihe und N = −14 laut 7. Exempels
unbrauchbar;
-/

example : (8 : ℤ) ^ 2 ≤ 79 ∧ 79 < (8 + 1) ^ 2 := by decide

/- Hilfsdefinition: Ein Rechenschritt der Kettenbruchentwicklung. -/

private def tennerStep79 (s : ℤ × ℤ) : ℤ × ℤ :=
  let q := (8 + s.1) / s.2
  let m := q * s.2 - s.1
  (m, (79 - m ^ 2) / s.2)

example :
    ((List.range 5).map fun k => (tennerStep79^[k + 1]) (0, 1)) =
      [(8, 15), (7, 2), (7, 15), (8, 1), (8, 15)] := by decide

example : ([((0, 1) : ℤ × ℤ), (8, 15), (7, 2), (7, 15), (8, 1)]).all
    (fun s => decide (s.2 ≠ 0) && (79 - (tennerStep79 s).1 ^ 2) % s.2 == 0) := by decide

/- Hilfsschritt: Fortsetzung der berechneten Kettenbruchperiode. -/

private theorem tennerStates79 (k : ℕ) :
    (tennerStep79^[k + 1]) (0, 1) ∈
      ([(8, 15), (7, 2), (7, 15), (8, 1)] : List (ℤ × ℤ)) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ih
    rcases ih with h | h | h | h <;> rw [h] <;> decide

/- Hilfsschritt: Fortsetzung der berechneten Kettenbruchperiode. -/

private theorem tennerAllStates79 (k : ℕ) :
    (tennerStep79^[k]) (0, 1) ∈
      ([(0, 1), (8, 15), (7, 2), (7, 15), (8, 1)] : List (ℤ × ℤ)) := by
  cases k with
  | zero => decide
  | succ k => exact List.mem_cons_of_mem _ (tennerStates79 k)

/- Hilfsdefinition: Die III. Verticalreihe der Rechnung. -/

private def tennerM79 (k : ℕ) : ℤ := ((tennerStep79^[k]) (0, 1)).1

/- Hilfsdefinition: Die VI. Verticalreihe der Rechnung. -/

private def tennerQ79 (k : ℕ) : ℤ := ((tennerStep79^[k]) (0, 1)).2

/- Hilfsdefinition: Die I. Verticalreihe der Rechnung. -/

private def tennerA79 (k : ℕ) : ℤ := (8 + tennerM79 k) / tennerQ79 k

/- Hilfsschritt: Ganzzahlige Quotienten und genaue Divisionen der Kette. -/

private theorem tennerData79 : tennerM79 0 = 0 ∧ tennerQ79 0 = 1 ∧
    (∀ k, (tennerA79 k : ℝ) ≤
        (Real.sqrt (79 : ℤ) + tennerM79 k) / tennerQ79 k ∧
      (Real.sqrt (79 : ℤ) + tennerM79 k) / tennerQ79 k < tennerA79 k + 1) ∧
    (∀ k, tennerM79 (k + 1) = tennerA79 k * tennerQ79 k - tennerM79 k) ∧
    (∀ k, tennerQ79 (k + 1) * tennerQ79 k = 79 - tennerM79 (k + 1) ^ 2) := by
  have hs : (Real.sqrt 79) ^ 2 = 79 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 79 := Real.sqrt_nonneg _
  have hlo : (8 : ℝ) ≤ Real.sqrt 79 := by nlinarith
  have hhi : Real.sqrt 79 < (9 : ℝ) := by nlinarith
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro k
    have hk := tennerAllStates79 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with hk | hk | hk | hk | hk
    all_goals norm_num [tennerA79, tennerM79, tennerQ79, hk]
    all_goals constructor <;> linarith
  · intro k
    simp only [tennerM79, tennerA79, tennerQ79, Function.iterate_succ_apply']
    rfl
  · intro k
    have hk := tennerAllStates79 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    simp only [tennerM79, tennerQ79, Function.iterate_succ_apply']
    rcases hk with hk | hk | hk | hk | hk <;> rw [hk] <;> decide

/- Hilfsschritt: Anwendung des als Voraussetzung geführten Kriteriums. -/

private theorem specializeCriterion79
    (hCriterion : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ∀ N : ℤ, N ^ 2 < 79 →
      (∀ k : ℕ, ((tennerStep79^[k + 1]) (0, 1)).2 ≠ |N|) →
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 + N := by
  intro N hN habsent
  obtain ⟨hM, hQ, hfloor, hMstep, hQstep⟩ := tennerData79
  have hns : ¬ ∃ q : ℤ, q ^ 2 = 79 := by
    rintro ⟨q, hq⟩
    have hs : IsSquare (79 : ℤ) := ⟨q, by nlinarith [hq]⟩
    norm_num at hs
  have hNreal : (|N| : ℤ) < Real.sqrt (79 : ℤ) := by
    have hsq : (((|N| : ℤ) : ℝ)) ^ 2 < 79 := by
      exact_mod_cast (show |N| ^ 2 < 79 by simpa only [sq_abs] using hN)
    have hs : (Real.sqrt 79) ^ 2 = 79 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt 79 := Real.sqrt_nonneg _
    norm_num only [Int.cast_ofNat]
    nlinarith
  exact hCriterion 79 N tennerA79 tennerM79 tennerQ79 (by norm_num) hns
    hM hQ hfloor hMstep hQstep hNreal habsent

/- Hilfsschritt: VI. Verticalreihe und das 7. Exempel. -/

private theorem tenner_exclusions79
    (hVI : ∀ N : ℤ, N ^ 2 < 79 →
      (∀ k : ℕ, ((tennerStep79^[k + 1]) (0, 1)).2 ≠ |N|) →
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 + N)
    (hExample7 : ¬ ∃ v w : ℤ, v ^ 2 = 79 * w ^ 2 - 14) :
    ∀ N ∈ ([-7, -14] : List ℤ),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 + N := by
  intro N hN
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
  rcases hN with rfl | rfl
  · apply hVI (-7) (by decide)
    intro k
    have hs := tennerStates79 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with h | h | h | h <;> rw [h] <;> norm_num
  · rintro ⟨v, w, _hcop, h⟩
    apply hExample7
    exact ⟨v, w, by linarith [h]⟩

/-
v² = 79w²+49, w = 0, v = 7, w = 14p₁/(p₁²−79),
S₁ = −14(79);
-/

example : (7 : ℤ) ^ 2 = 79 * 0 ^ 2 + 49 := by norm_num

example (p : ℚ) : (2 * 7 * p) / (p ^ 2 - 79) = 14 * p / (p ^ 2 - 79) := by ring

example : (-4 * 79 * 49 / 14 : ℚ) = -14 * 79 := by norm_num

/-
hier soll N ein 7faches sein; N = −7 und −14 sind aber
unzulässig;
-/

/- Hilfsschritt: Product der äquivalenten Nenner nach XIIa. -/

private theorem equivalent_parameter_product (a b c m n r x : ℤ) (p : ℚ) (_hn : 0 < n)
    (hmn : Int.gcd m n = 1)
    (hroot : r ^ 2 = a * m ^ 2 + b * m * n + c * n ^ 2)
    (hp : p ^ 2 - a ≠ 0)
    (hg : 2 * (r : ℚ) * p + (2 * a * m + b * n) ≠ 0)
    (hX : (n : ℚ) * x = m + (2 * r * p + (2 * a * m + b * n)) / (p ^ 2 - a)) :
    let q := -(((2 * a * m + b * n : ℤ) : ℚ) * p + 2 * a * r) /
      (2 * r * p + (2 * a * m + b * n))
    q ^ 2 - a ≠ 0 →
      ∃ ρ : ℤ, ρ ≠ 0 ∧ Int.gcd ρ n = 1 ∧
        (p.num ^ 2 - a * (p.den : ℤ) ^ 2) *
          (q.num ^ 2 - a * (q.den : ℤ) ^ 2) * ρ ^ 2 =
            n ^ 2 * (b ^ 2 - 4 * a * c) := by
  have denominator_product (s d C v₁ w₁ v₂ w₂ : ℤ)
      (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0)
      (hcop₁ : IsCoprime v₁ w₁) (hcop₂ : IsCoprime v₂ w₂)
      (hsum : s * (v₁ * w₂ + v₂ * w₁) = d * w₁ * w₂)
      (hprod : s * v₁ * v₂ = -C * w₁ * w₂) :
      ∃ ρ : ℤ, s = ρ * w₁ * w₂ := by
    have hroot : s * v₁ ^ 2 = w₁ * (d * v₁ + C * w₁) := by
      apply mul_right_cancel₀ hw₂
      linear_combination v₁ * hsum - w₁ * hprod
    have hw₁s : w₁ ∣ s := by
      apply (hcop₁.symm.pow_right (n := 2)).dvd_of_dvd_mul_left
      exact ⟨d * v₁ + C * w₁, by linear_combination hroot⟩
    obtain ⟨t, ht⟩ := hw₁s
    have hsumt : t * (v₁ * w₂ + v₂ * w₁) = d * w₂ := by
      apply mul_left_cancel₀ hw₁
      rw [ht] at hsum
      linear_combination hsum
    have hprodt : t * v₁ * v₂ = -C * w₂ := by
      apply mul_left_cancel₀ hw₁
      rw [ht] at hprod
      linear_combination hprod
    have h₁ : w₂ ∣ t * v₁ := by
      apply hcop₂.symm.dvd_of_dvd_mul_right
      exact ⟨-C, by linear_combination hprodt⟩
    have h₂ : w₂ ∣ t * w₁ := by
      apply hcop₂.symm.dvd_of_dvd_mul_left
      exact ⟨d - t * v₁, by linear_combination hsumt⟩
    have hwt : w₂ ∣ t := by
      obtain ⟨A, B, hBez⟩ := hcop₁
      obtain ⟨u, hu⟩ := h₁
      obtain ⟨v, hv⟩ := h₂
      refine ⟨A * u + B * v, ?_⟩
      linear_combination A * hu + B * hv - t * hBez
    obtain ⟨ρ, hρ⟩ := hwt
    refine ⟨ρ, ?_⟩
    rw [ht, hρ]
    ring
  have equivalent_denominators (a m n r g D x : ℤ) (p q : ℚ)
      (hmn : Int.gcd m n = 1)
      (hS : g ^ 2 - 4 * a * r ^ 2 = n ^ 2 * D)
      (hp : p ^ 2 - a ≠ 0) (hg : 2 * (r : ℚ) * p + g ≠ 0)
      (hX : (n : ℚ) * x = m + (2 * r * p + g) / (p ^ 2 - a))
      (heq : q = -((g : ℚ) * p + 2 * a * r) / (2 * r * p + g)) :
      ∃ ρ : ℤ, ρ ≠ 0 ∧ Int.gcd ρ n = 1 ∧
        (p.num ^ 2 - a * (p.den : ℤ) ^ 2) *
          (q.num ^ 2 - a * (q.den : ℤ) ^ 2) * ρ ^ 2 = n ^ 2 * D := by
    let s : ℤ := n * x - m
    let v₁ := p.num
    let w₁ : ℤ := p.den
    let v₂ := q.num
    let w₂ : ℤ := q.den
    have hw₁ : w₁ ≠ 0 := by dsimp [w₁]; exact_mod_cast p.den_nz
    have hw₂ : w₂ ≠ 0 := by dsimp [w₂]; exact_mod_cast q.den_nz
    have hw₁Q : (w₁ : ℚ) ≠ 0 := by exact_mod_cast hw₁
    have hw₂Q : (w₂ : ℚ) ≠ 0 := by exact_mod_cast hw₂
    have hpv : p = (v₁ : ℚ) / w₁ := by simpa [v₁, w₁] using (Rat.num_div_den p).symm
    have hqv : q = (v₂ : ℚ) / w₂ := by simpa [v₂, w₂] using (Rat.num_div_den q).symm
    have hcop₁ : IsCoprime v₁ w₁ := by
      apply Int.isCoprime_iff_nat_coprime.mpr
      simpa [v₁, w₁] using p.reduced
    have hcop₂ : IsCoprime v₂ w₂ := by
      apply Int.isCoprime_iff_nat_coprime.mpr
      simpa [v₂, w₂] using q.reduced
    have hsX : (s : ℚ) = (2 * r * p + g) / (p ^ 2 - a) := by
      dsimp [s]
      push_cast
      linear_combination hX
    have hcross := (eq_div_iff hp).mp hsX
    have hqcross := (eq_div_iff hg).mp heq
    have hsumQ : (s : ℚ) * (p + q) = 2 * r := by
      have h : (p ^ 2 - a) * ((s : ℚ) * (p + q) - 2 * r) = 0 := by
        linear_combination (p + q) * hcross + hqcross
      have h' := (mul_eq_zero.mp h).resolve_left hp
      linarith
    have hprodQ : (s : ℚ) * p * q = -((a : ℚ) * s + g) := by
      linear_combination p * hsumQ - hcross
    have hsum : s * (v₁ * w₂ + v₂ * w₁) = 2 * r * w₁ * w₂ := by
      rw [hpv, hqv] at hsumQ
      field_simp [hw₁Q, hw₂Q] at hsumQ
      have hQ : (s : ℚ) * (v₁ * w₂ + v₂ * w₁) = 2 * r * w₁ * w₂ := by
        linear_combination hsumQ
      exact_mod_cast hQ
    have hprod : s * v₁ * v₂ = -(a * s + g) * w₁ * w₂ := by
      rw [hpv, hqv] at hprodQ
      field_simp [hw₁Q, hw₂Q] at hprodQ
      have hQ : (s : ℚ) * v₁ * v₂ = -((a : ℚ) * s + g) * w₁ * w₂ := by
        linear_combination hprodQ
      exact_mod_cast hQ
    obtain ⟨ρ, hρ⟩ := denominator_product s (2 * r) (a * s + g)
      v₁ w₁ v₂ w₂ hw₁ hw₂ hcop₁ hcop₂ hsum hprod
    have hs₀ : (s : ℚ) ≠ 0 := by
      intro hs
      apply hg
      linear_combination -hcross + (p ^ 2 - a) * hs
    refine ⟨ρ, ?_, ?_, ?_⟩
    · intro h
      apply hs₀
      have hs : s = 0 := by rw [hρ, h]; ring
      exact_mod_cast hs
    · apply Int.isCoprime_iff_gcd_eq_one.mp
      have h := Int.gcd_eq_gcd_ab m n
      rw [hmn] at h
      norm_num at h
      refine ⟨-w₁ * w₂ * Int.gcdA m n, x * Int.gcdA m n + Int.gcdB m n, ?_⟩
      dsimp [s] at hρ
      linear_combination -h + Int.gcdA m n * hρ
    · have hnormQ : (s : ℚ) ^ 2 * (p ^ 2 - a) * (q ^ 2 - a) =
          (g : ℚ) ^ 2 - 4 * a * r ^ 2 := by
        linear_combination ((s : ℚ) * p * q + a * s - g) * hprodQ -
          a * ((s : ℚ) * (p + q) + 2 * r) * hsumQ
      have hSQ : (g : ℚ) ^ 2 - 4 * a * r ^ 2 = (n : ℚ) ^ 2 * D := by exact_mod_cast hS
      rw [hSQ, hpv, hqv] at hnormQ
      have hρQ : (s : ℚ) = (ρ : ℚ) * w₁ * w₂ := by exact_mod_cast hρ
      rw [hρQ] at hnormQ
      field_simp [hw₁Q, hw₂Q] at hnormQ
      have hQ : ((v₁ : ℚ) ^ 2 - a * w₁ ^ 2) *
          ((v₂ : ℚ) ^ 2 - a * w₂ ^ 2) * ρ ^ 2 = (n : ℚ) ^ 2 * D := by
        linear_combination hnormQ
      dsimp [v₁, w₁, v₂, w₂] at hQ
      exact_mod_cast hQ
  let q : ℚ := -(((2 * a * m + b * n : ℤ) : ℚ) * p + 2 * a * r) /
    (2 * r * p + (2 * a * m + b * n))
  change q ^ 2 - a ≠ 0 → _
  intro _hq
  have hS : (2 * a * m + b * n) ^ 2 - 4 * a * r ^ 2 =
      n ^ 2 * (b ^ 2 - 4 * a * c) := by
    linear_combination -4 * a * hroot
  refine equivalent_denominators a m n r (2 * a * m + b * n)
    (b ^ 2 - 4 * a * c) x p q hmn hS hp ?_ ?_ ?_
  · simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hg
  · simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hX
  · dsimp [q]
    push_cast
    rfl

/- Hilfsschritt: Der Nenner der p-Function ist nicht Null. -/

private theorem notSquare79 (p : ℚ) : p ^ 2 - 79 ≠ 0 := by
  intro h
  have hs : IsSquare (79 : ℚ) := ⟨p, by nlinarith [h]⟩
  have hi : IsSquare (79 : ℤ) := Rat.isSquare_intCast_iff.mp hs
  norm_num at hi

/- Hilfsschritt: Auswahl des Parameters nach §. 16. -/

private theorem selected_parameter79 (m r C x y : ℤ)
    (hbase : r ^ 2 = 79 * m ^ 2 + C)
    (hroot : y ^ 2 = 79 * x ^ 2 + C) (hxm : x ≠ m)
    (hD : ¬ (79 : ℤ) ^ 2 ∣ -4 * 79 * C) :
    ∃ p : ℚ,
      (x : ℚ) = m + (2 * r * p + 2 * 79 * m) / (p ^ 2 - 79) ∧
      ¬ (79 : ℤ) ∣ p.num ^ 2 - 79 * (p.den : ℤ) ^ 2 := by
  have hxmQ : (x : ℚ) - m ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hxm
  let p : ℚ := ((y : ℚ) + r) / (x - m)
  have hline : p * ((x : ℚ) - m) = y + r := by
    dsimp [p]
    exact div_mul_cancel₀ _ hxmQ
  have hbQ : (r : ℚ) ^ 2 = 79 * (m : ℚ) ^ 2 + C := by exact_mod_cast hbase
  have hrQ : (y : ℚ) ^ 2 = 79 * (x : ℚ) ^ 2 + C := by exact_mod_cast hroot
  have hpoly : ((x : ℚ) - m) * (p ^ 2 - 79) = 2 * r * p + 2 * 79 * m := by
    apply mul_right_cancel₀ hxmQ
    linear_combination (p * ((x : ℚ) - m) + y - r) * hline + hrQ - hbQ
  have hX : (x : ℚ) = m + (2 * r * p + 2 * 79 * m) / (p ^ 2 - 79) := by
    have he := (eq_div_iff (notSquare79 p)).2 hpoly
    linear_combination he
  have hden : 2 * (r : ℚ) * p + 2 * 79 * m ≠ 0 := by
    rw [← hpoly]
    exact mul_ne_zero hxmQ (notSquare79 p)
  let q : ℚ := -(2 * 79 * (m : ℚ) * p + 2 * 79 * r) /
    (2 * r * p + 2 * 79 * m)
  have hq : q * (2 * (r : ℚ) * p + 2 * 79 * m) =
      -(2 * 79 * m * p + 2 * 79 * r) := by
    dsimp [q]
    exact div_mul_cancel₀ _ hden
  have hsame : (m : ℚ) + (2 * r * q + 2 * 79 * m) / (q ^ 2 - 79) =
      m + (2 * r * p + 2 * 79 * m) / (p ^ 2 - 79) := by
    field_simp [notSquare79 p, notSquare79 q]
    linear_combination (p - q) * hq
  have hXq : (x : ℚ) = m + (2 * r * q + 2 * 79 * m) / (q ^ 2 - 79) := by
    rw [hsame]
    exact hX
  have hpair : ∃ ρ : ℤ, ρ ≠ 0 ∧ Int.gcd ρ 1 = 1 ∧
      (p.num ^ 2 - 79 * (p.den : ℤ) ^ 2) *
        (q.num ^ 2 - 79 * (q.den : ℤ) ^ 2) * ρ ^ 2 = -4 * 79 * C := by
    have h := equivalent_parameter_product 79 0 C m 1 r x p (by norm_num)
      (by simp) (by simpa using hbase) (notSquare79 p)
      (by simpa using hden) (by simpa using hX)
    dsimp only at h
    norm_num only [Int.cast_ofNat, Int.cast_add, Int.cast_mul, zero_mul, add_zero,
      one_pow, one_mul, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_sub] at h
    have hq79 : (-(158 * (m : ℚ) * p + 158 * r) / (2 * r * p + 158 * m)) ^ 2 - 79 ≠ 0 := by
      simpa [q, show (2 : ℚ) * 79 = 158 by norm_num] using notSquare79 q
    simpa [q, show (2 : ℚ) * 79 = 158 by norm_num] using h hq79
  obtain ⟨ρ, _hρ, _hcop, hpair⟩ := hpair
  by_cases hp79 : (79 : ℤ) ∣ p.num ^ 2 - 79 * (p.den : ℤ) ^ 2
  · refine ⟨q, hXq, ?_⟩
    intro hq79
    apply hD
    rw [← hpair]
    exact dvd_mul_of_dvd_left (by simpa [pow_two] using mul_dvd_mul hp79 hq79) (ρ ^ 2)
  · exact ⟨p, hX, hp79⟩

/- Hilfsschritt: Nenner der p-Function und Stammzahl. -/

private theorem parameter_stock79 (m r h d f x : ℤ) (p : ℚ)
    (hr : 2 * r = h * d) (hg : 2 * 79 * m = h * f)
    (hX : (x : ℚ) = m + (2 * r * p + 2 * 79 * m) / (p ^ 2 - 79)) :
    let N := p.num ^ 2 - 79 * (p.den : ℤ) ^ 2
    (x - m) * N = h * (d * p.num + f * (p.den : ℤ)) * (p.den : ℤ) ∧
      N ∣ h * (f ^ 2 - 79 * d ^ 2) := by
  let u : ℤ := p.num
  let z : ℤ := p.den
  let N := u ^ 2 - 79 * z ^ 2
  have hzQ : (z : ℚ) ≠ 0 := by dsimp [z]; exact_mod_cast p.den_nz
  have hp : p = (u : ℚ) / z := by simpa [u, z] using (Rat.num_div_den p).symm
  have hrQ : 2 * (r : ℚ) = h * d := by exact_mod_cast hr
  have hgQ : 2 * 79 * (m : ℚ) = h * f := by exact_mod_cast hg
  have heq : (x - m) * N = h * (d * u + f * z) * z := by
    have ht : ((x : ℚ) - m) * (p ^ 2 - 79) = 2 * r * p + 2 * 79 * m := by
      apply (eq_div_iff (notSquare79 p)).mp
      linear_combination hX
    rw [hrQ, hgQ, hp] at ht
    field_simp [hzQ] at ht
    dsimp [N]
    have htI : (x - m) * (u ^ 2 - z ^ 2 * 79) = z * h * (u * d + z * f) := by exact_mod_cast ht
    linear_combination htI
  refine ⟨heq, ?_⟩
  change N ∣ h * (f ^ 2 - 79 * d ^ 2)
  have hcop : IsCoprime u z := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa [u, z] using p.reduced
  obtain ⟨s, t, hst⟩ := hcop
  have hNz : IsCoprime N z := by
    refine ⟨s ^ 2, 79 * z * s ^ 2 + 2 * s * t * u + t ^ 2 * z, ?_⟩
    calc
      _ = (s * u + t * z) ^ 2 := by dsimp [N]; ring
      _ = 1 := by rw [hst]; norm_num
  apply (hNz.pow_right (n := 3)).dvd_of_dvd_mul_left
  refine ⟨-((x - m) * (d * u - f * z) - h * d ^ 2 * z), ?_⟩
  dsimp [N] at heq ⊢
  linear_combination (d * u - f * z) * heq

/- Hilfsschritt: Bedingung theilfremder Zahlen. -/

private theorem primitive_coordinate79 (k C x y : ℤ) (hk : Prime k) (hC : k ∣ C)
    (hroot : y ^ 2 = 79 * x ^ 2 + C) (hcop : Int.gcd y x = 1) : ¬ k ∣ x := by
  intro hx
  have hy2 : k ∣ y ^ 2 := by
    rw [hroot]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_pow hx (by decide)) 79) hC
  have hy : k ∣ y := hk.dvd_of_dvd_pow hy2
  obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  apply hk.not_dvd_one
  rw [← huv]
  exact dvd_add (dvd_mul_of_dvd_right hy u) (dvd_mul_of_dvd_right hx v)

/- Hilfsschritt: Der Nenner muss den bezeichneten Factor enthalten. -/

private theorem necessary_parameter79 (k C m r d f S x y : ℤ)
    (hk : Prime k) (hC : k ∣ C) (hm : k ∣ m)
    (hbase : r ^ 2 = 79 * m ^ 2 + C)
    (hroot : y ^ 2 = 79 * x ^ 2 + C) (hcop : Int.gcd y x = 1)
    (hD : ¬ (79 : ℤ) ^ 2 ∣ -4 * 79 * C)
    (hr : 2 * r = (2 * k) * d) (hg : 2 * 79 * m = (2 * k) * f)
    (hS : (2 * k) * (f ^ 2 - 79 * d ^ 2) = 79 * S) :
    ∃ u z N : ℤ, Int.gcd u z = 1 ∧ u ^ 2 = 79 * z ^ 2 + N ∧ N ∣ S ∧ k ∣ N := by
  have hkx := primitive_coordinate79 k C x y hk hC hroot hcop
  have hxm : x ≠ m := by intro he; exact hkx (he ▸ hm)
  obtain ⟨p, hX, h79⟩ := selected_parameter79 m r C x y hbase hroot hxm hD
  obtain ⟨hcross, hstock⟩ := parameter_stock79 m r (2 * k) d f x p hr hg hX
  let N := p.num ^ 2 - 79 * (p.den : ℤ) ^ 2
  have hd : N ∣ S := by
    have hcop79 : IsCoprime N 79 := ((show Prime (79 : ℤ) by norm_num).coprime_iff_not_dvd.mpr h79).symm
    apply hcop79.dvd_of_dvd_mul_right
    rw [mul_comm S 79, ← hS]
    exact hstock
  have hkN : k ∣ N := by
    have hprod : k ∣ (x - m) * N := by
      rw [hcross]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ⟨2, by ring⟩ _) _
    rcases hk.dvd_mul.mp hprod with hxm | hN
    · exact False.elim (hkx (by simpa using dvd_add hxm hm))
    · exact hN
  refine ⟨p.num, p.den, N, ?_, ?_, hd, hkN⟩
  · exact Int.isCoprime_iff_gcd_eq_one.mp (by
      apply Int.isCoprime_iff_nat_coprime.mpr
      simpa using p.reduced)
  · dsimp [N]
    ring

/- Hilfsschritt: Achterreste und theilfremde Zahlen. -/

private theorem residue_exclusions79 (u z N : ℤ) (hcop : Int.gcd u z = 1)
    (hN : N ∈ ([7, 14, 28, -28] : List ℤ)) (hnorm : u ^ 2 = 79 * z ^ 2 + N) : False := by
  have hmod := congrArg (fun a : ℤ => (a : ZMod 8)) hnorm
  push_cast at hmod
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
  rcases hN with rfl | rfl | rfl | rfl
  · have obstruction : ∀ u z : ZMod 8, u ^ 2 ≠ 79 * z ^ 2 + 7 := by decide
    exact obstruction _ _ hmod
  · have obstruction : ∀ u z : ZMod 8, u ^ 2 ≠ 79 * z ^ 2 + 14 := by decide
    exact obstruction _ _ hmod
  all_goals
    have heven : ∀ u z : ZMod 8, u ^ 2 = 79 * z ^ 2 + 4 →
        (ZMod.cast u : ZMod 2) = 0 ∧ (ZMod.cast z : ZMod 2) = 0 := by decide
    have htwo := heven (u : ZMod 8) (z : ZMod 8) (by norm_num at hmod ⊢; exact hmod)
    rw [ZMod.cast_intCast (by decide : 2 ∣ 8), ZMod.cast_intCast (by decide : 2 ∣ 8)] at htwo
    have hu : (2 : ℤ) ∣ u := (ZMod.intCast_zmod_eq_zero_iff_dvd u 2).mp htwo.1
    have hz : (2 : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z 2).mp htwo.2
    obtain ⟨a, b, hab⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hcop
    have hbad : (2 : ℤ) ∣ 1 := by
      rw [← hab]
      exact dvd_add (dvd_mul_of_dvd_right hu a) (dvd_mul_of_dvd_right hz b)
    norm_num at hbad

/- Hilfsschritt: Ausschluss der verbleibenden Nenner. -/

private theorem candidates79 (u z N : ℤ) (hcop : Int.gcd u z = 1)
    (hnorm : u ^ 2 = 79 * z ^ 2 + N) (hdiv : N ∣ 28) (hseven : 7 ∣ N)
    (hminus7 : ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 - 7)
    (hminus14 : ¬ ∃ v w : ℤ, v ^ 2 = 79 * w ^ 2 - 14) : False := by
  have hbound : |N| ≤ 28 := by
    have hn : (N.natAbs : ℤ) ∣ 28 := by simpa using hdiv
    simpa using Int.le_of_dvd (by norm_num : (0 : ℤ) < 28) hn
  have hcases : N ∈ ([-7, -14, 7, 14, 28, -28] : List ℤ) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hbound
    interval_cases N
    all_goals solve | norm_num | norm_num at hdiv | norm_num at hseven
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcases
  rcases hcases with rfl | rfl | hN
  · exact hminus7 ⟨u, z, hcop, by linarith [hnorm]⟩
  · exact hminus14 ⟨u, z, by linarith [hnorm]⟩
  · exact residue_exclusions79 u z N hcop (by simpa using hN) hnorm

/- Hilfsschritt: Ausschluss für das Zahlenglied 49. -/

private theorem exclude49_79
    (hminus7 : ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 - 7)
    (hminus14 : ¬ ∃ v w : ℤ, v ^ 2 = 79 * w ^ 2 - 14) :
    ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 + 49 := by
  rintro ⟨v, w, hcop, h⟩
  obtain ⟨u, z, N, hcopN, hN, hdiv, hseven⟩ :=
    necessary_parameter79 7 49 0 7 1 0 (-14) w v (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h hcop (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  apply candidates79 u z N hcopN hN ?_ hseven hminus7 hminus14
  exact dvd_trans (by simpa using hdiv : N ∣ 14) (by norm_num)

/-
endlich
v² = 79w²+98 = 81w²−2(w²−49), w = 7, v = 63,
w = 7+14(9p,,+79)/(p,,²−79), S₁ = −4.7.(79),
-/

example (w : ℚ) : 79 * w ^ 2 + 98 = 81 * w ^ 2 - 2 * (w ^ 2 - 49) := by ring

example : (63 : ℤ) ^ 2 = 79 * 7 ^ 2 + 98 := by norm_num

example (p : ℚ) : (7) + (2 * (63) * p + (2 * 79 * (7) + (0) * 1)) / (p ^ 2 - 79) = (7) + 14 * ((9) * p + (79)) / (p ^ 2 - 79) := by ring

example : (-4 * 79 * 98 / 14 : ℚ) = -4 * 7 * 79 := by norm_num

/-
auch hier sollte N den Factor 7 enthalten, was unmöglich ist.
-/

/- Hilfsschritt: Ausschluss für das Zahlenglied 98. -/

private theorem exclude98_79
    (hminus7 : ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 - 7)
    (hminus14 : ¬ ∃ v w : ℤ, v ^ 2 = 79 * w ^ 2 - 14) :
    ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 + 98 := by
  rintro ⟨v, w, hcop, h⟩
  obtain ⟨u, z, N, hcopN, hN, hdiv, hseven⟩ :=
    necessary_parameter79 7 98 7 63 9 79 (-28) w v (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h hcop (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact candidates79 u z N hcopN hN (by simpa using hdiv) hseven hminus7 hminus14

/- Hilfsschritt: Vorbereitung des Bruches aus VI. -/

private theorem preparation_from_VI (m n α β γ δ x : ℤ) (P p : ℚ)
    (hmn : Int.gcd m n = 1)
    (hVI : (x : ℚ) * (n * P ^ 2 - 2 * α * P + γ) =
      m * P ^ 2 + 2 * β * P + δ)
    (hp : p = n * P - α) : n ∣ p.num + α * (p.den : ℤ) := by
  let V : ℤ := P.num
  let W : ℤ := P.den
  have hW : W ≠ 0 := by dsimp [W]; exact_mod_cast P.den_nz
  have hWq : (W : ℚ) ≠ 0 := by exact_mod_cast hW
  have hP : P = (V : ℚ) / W := by simpa [V, W] using (Rat.num_div_den P).symm
  have hVW : IsCoprime V W := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa [V, W] using P.reduced
  have hroot : (n * x - m) * V ^ 2 =
      W * ((2 * α * x + 2 * β) * V + (δ - γ * x) * W) := by
    rw [hP] at hVI
    field_simp [hWq] at hVI
    have hI : x * (V * (n * V - W * 2 * α) + W ^ 2 * γ) =
        V * (V * m + W * 2 * β) + W ^ 2 * δ := by exact_mod_cast hVI
    linear_combination hI
  have hWs : W ∣ n * x - m := by
    apply (hVW.symm.pow_right (n := 2)).dvd_of_dvd_mul_right
    exact ⟨(2 * α * x + 2 * β) * V + (δ - γ * x) * W, hroot⟩
  obtain ⟨k, hk⟩ := hWs
  have hnW : IsCoprime n W := by
    obtain ⟨u, t, hut⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hmn
    refine ⟨u * x + t, -u * k, ?_⟩
    linear_combination hut + u * hk
  have hpD : (p.den : ℚ) ≠ 0 := by exact_mod_cast p.den_nz
  have hcross : W * (p.num + α * (p.den : ℤ)) = n * V * (p.den : ℤ) := by
    have h := hp
    rw [hP, ← Rat.num_div_den p] at h
    field_simp [hWq, hpD] at h
    have hI : p.num * W = (p.den : ℤ) * (n * V - W * α) := by
      exact_mod_cast h
    linear_combination hI
  apply hnW.dvd_of_dvd_mul_left
  exact ⟨V * (p.den : ℤ), by linear_combination hcross⟩

/- Hilfsschritt: Vorbereitung des Parameters der p-Function. -/

private theorem parameter_preparation79 (c m n r α β γ x : ℤ) (q : ℚ)
    (hn : 0 < n) (hmn : Int.gcd m n = 1)
    (hr : r ^ 2 = 79 * m ^ 2 + c * n ^ 2)
    (hline : r = m * α + n * β) (hA : α ^ 2 - 79 = n * γ)
    (hq : q ^ 2 - 79 ≠ 0)
    (hX : (n : ℚ) * x = m + 2 * (r * q + 79 * m) / (q ^ 2 - 79)) :
    ∃ k : ℤ, q.num = n * k - α * (q.den : ℤ) := by
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hcoeff : m * (m * γ + 2 * α * β) + n * (β ^ 2 - c) = 0 := by
    apply mul_left_cancel₀ hn0
    linear_combination hr - (r + m * α + n * β) * hline - m ^ 2 * hA
  have hd : n ∣ m * γ + 2 * α * β := by
    apply (Int.isCoprime_iff_gcd_eq_one.mpr hmn).symm.dvd_of_dvd_mul_left
    exact ⟨c - β ^ 2, by linear_combination hcoeff⟩
  obtain ⟨t, ht⟩ := hd
  let δ : ℤ := -t
  have hδ : m * γ + 2 * α * β + n * δ = 0 := by dsimp [δ]; linear_combination ht
  let P : ℚ := (q + α) / n
  have hP : q = n * P - α := by dsimp [P]; field_simp; ring
  have hAq : (α : ℚ) ^ 2 - 79 = n * γ := by exact_mod_cast hA
  have hrq : (r : ℚ) = m * α + n * β := by exact_mod_cast hline
  have hδq : (m : ℚ) * γ + 2 * α * β + n * δ = 0 := by exact_mod_cast hδ
  have hcross : ((n : ℚ) * x - m) * (q ^ 2 - 79) = 2 * (r * q + 79 * m) := by
    exact (eq_div_iff hq).mp (by linear_combination hX)
  have hVI : (x : ℚ) * (n * P ^ 2 - 2 * α * P + γ) =
      m * P ^ 2 + 2 * β * P + δ := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hnq)
    linear_combination hcross -
      ((n : ℚ) * x - m) * (q + n * P - α) * hP -
      ((n : ℚ) * x - m) * hAq -
      2 * m * hAq - n * hδq +
      2 * r * hP + 2 * (n * P - α) * hrq
  obtain ⟨k, hk⟩ := preparation_from_VI m n α β γ δ x P q hmn hVI hP
  refine ⟨k, ?_⟩
  linear_combination hk

/- Hilfsschritt: Anwendung der Stammzahl auf den vorbereiteten Parameter. -/

private theorem prepared_stock79 (c m n r α β γ x : ℤ) (q : ℚ)
    (hn : 0 < n) (hmn : Int.gcd m n = 1)
    (hr : r ^ 2 = 79 * m ^ 2 + c * n ^ 2)
    (hline : r = m * α + n * β) (hA : α ^ 2 - 79 = n * γ)
    (hq : q ^ 2 - 79 ≠ 0)
    (hX : (n : ℚ) * x = m + 2 * (r * q + 79 * m) / (q ^ 2 - 79)) :
    let N := q.num ^ 2 - 79 * (q.den : ℤ) ^ 2
    n ∣ N ∧ N ∣ n * (-4 * 79 * c) := by
  obtain ⟨k, hk⟩ := parameter_preparation79 c m n r α β γ x q hn hmn hr hline hA hq hX
  let u : ℤ := q.num
  let w : ℤ := q.den
  let N := u ^ 2 - 79 * w ^ 2
  change n ∣ N ∧ N ∣ n * (-4 * 79 * c)
  have hnum : u = n * k - α * w := hk
  have hcop : IsCoprime u w := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa [u, w] using q.reduced
  obtain ⟨s, t, hst⟩ := hcop
  have hNw : IsCoprime N w := by
    refine ⟨s ^ 2, 79 * w * s ^ 2 + 2 * s * t * u + t ^ 2 * w, ?_⟩
    calc
      _ = (s * u + t * w) ^ 2 := by dsimp [N]; ring
      _ = 1 := by rw [hst]; norm_num
  have hwQ : (w : ℚ) ≠ 0 := by dsimp [w]; exact_mod_cast q.den_nz
  have hqv : q = (u : ℚ) / w := by simpa [u, w] using (Rat.num_div_den q).symm
  have hcross : (n * x - m) * N = (2 * r * u + 2 * 79 * m * w) * w := by
    have h : ((n : ℚ) * x - m) * (q ^ 2 - 79) = 2 * (r * q + 79 * m) := by
      exact (eq_div_iff hq).mp (by linear_combination hX)
    rw [hqv] at h
    field_simp [hwQ] at h
    have hI : (n * x - m) * (u ^ 2 - w ^ 2 * 79) = w * 2 * (u * r + m * w * 79) := by
      exact_mod_cast h
    dsimp [N]
    linear_combination hI
  constructor
  · refine ⟨n * k ^ 2 - 2 * α * k * w + γ * w ^ 2, ?_⟩
    dsimp [N]
    rw [hnum]
    linear_combination w ^ 2 * hA
  · let L := x * (2 * r * u - 2 * 79 * m * w) - 2 * w * c * n -
        2 * r * (k * m + β * w)
    have hmv : m * u + r * w = n * (k * m + β * w) := by
      rw [hnum, hline]
      ring
    have hL : (n * x - m) * (2 * r * u - 2 * 79 * m * w) - 4 * r ^ 2 * w = n * L := by
      dsimp [L]
      linear_combination -2 * w * hr - 2 * r * hmv
    have hXI : N * ((n * x - m) * (2 * r * u - 2 * 79 * m * w) - 4 * r ^ 2 * w) =
        -n ^ 2 * (-4 * 79 * c) * w ^ 3 := by
      dsimp [N] at hcross ⊢
      linear_combination (2 * r * u - 2 * 79 * m * w) * hcross + 4 * 79 * w ^ 3 * hr
    have he : n * (N * L) = n * (-n * (-4 * 79 * c) * w ^ 3) := by
      rw [hL] at hXI
      linear_combination hXI
    have he' := mul_left_cancel₀ (ne_of_gt hn) he
    apply (hNw.pow_right (n := 3)).dvd_of_dvd_mul_left
    exact ⟨-L, by linear_combination he'⟩

/- Folgerung mit den als Voraussetzungen geführten Aussagen aus §. 16
und §. 23. -/

theorem noIntegerSolutions
    (hSelection : Kunerth1880.Paragraf16.singularPrimeSelection)
    (hSource : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ¬ ∃ x y : ℤ, y ^ 2 = 79 * x ^ 2 + (0) * x + (7 * 2399) := by
  have hVI := specializeCriterion79 hSource
  have hExample7 : ¬ ∃ v w : ℤ, v ^ 2 = 79 * w ^ 2 - 14 := by
    rintro ⟨v, w, h⟩
    exact Kunerth1880.Paragraf25.Beispiel07.noIntegerSolutions hSelection hSource ⟨w, v, h⟩
  rintro ⟨x, y, hroot⟩
  simp only [zero_mul, add_zero] at hroot
  have hx : 7 * x - 76 ≠ 0 := by omega
  have hxQ : 7 * (x : ℚ) - 76 ≠ 0 := by exact_mod_cast hx
  let p : ℚ := (7 * (y : ℚ) + 1131) / (7 * x - 76)
  have hline : p * (7 * (x : ℚ) - 76) = 7 * y + 1131 := by
    dsimp [p]
    exact div_mul_cancel₀ _ hxQ
  have hrootQ : (y : ℚ) ^ 2 = 79 * (x : ℚ) ^ 2 + 7 * 2399 := by
    exact_mod_cast hroot
  have hpoly : (7 * (x : ℚ) - 76) * (p ^ 2 - 79) = 2 * (1131 * p + 6004) := by
    apply mul_right_cancel₀ hxQ
    linear_combination (p * (7 * (x : ℚ) - 76) + 7 * y - 1131) * hline + 49 * hrootQ
  have hX : 7 * (x : ℚ) = 76 + 2 * (1131 * p + 6004) / (p ^ 2 - 79) := by
    have he := (eq_div_iff (notSquare79 p)).2 hpoly
    linear_combination he
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp] at hline
    have hyQ : 7 * (y : ℚ) + 1131 = 0 := by linarith
    have hyI : 7 * y + 1131 = 0 := by exact_mod_cast hyQ
    omega
  have hden1 : 1131 * p + 79 * 76 ≠ 0 := by
    intro h
    have hz : (7 * (x : ℚ) - 76) * (p ^ 2 - 79) = 0 := by linear_combination hpoly + 2 * h
    exact mul_ne_zero hxQ (notSquare79 p) hz
  have hden2 : 76 * p + 1131 ≠ 0 := by
    intro h
    have hp : p = -1131 / 76 := by linarith
    rw [hp] at hpoly
    have hxQ' : 7 * (x : ℚ) = -76 := by norm_num at hpoly; linarith
    have hxI : 7 * x = -76 := by exact_mod_cast hxQ'
    omega
  obtain ⟨k, hk⟩ := parameter_preparation79 (7 * 2399) 76 7 1131 10 53 3 x p
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (notSquare79 p) (by norm_num; exact hX)
  have hselection := hSelection
    79 (7 * 2399) 76 7 1131 x 10 53 (3) k 79 2399 p
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk hp0 (notSquare79 p) hden1 hden2 (by norm_num; exact hX)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  dsimp only at hselection
  obtain ⟨q, _hchoices, _hq, ⟨z, hZ⟩, h7, h79, h2399⟩ :=
    hselection (notSquare79 _) (notSquare79 _) (notSquare79 _)
  norm_num at hZ
  obtain ⟨_h7, hD⟩ := prepared_stock79 (7 * 2399) 76 7 1131 10 53 3 z q
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (notSquare79 q) (by norm_num; exact hZ)
  obtain ⟨_hcross, hS⟩ := parameter_stock79 76 1131 2 1131 6004 (7 * z) q
    (by norm_num) (by norm_num) (by push_cast; linear_combination hZ)
  let u : ℤ := q.num
  let w : ℤ := q.den
  let N := u ^ 2 - 79 * w ^ 2
  have hcop : Int.gcd u w = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa [u, w] using q.reduced
  change 7 ∣ N at h7
  change ¬ 79 ∣ N at h79
  change ¬ 2399 ∣ N at h2399
  have hdiv : N ∣ 98 * 79 * 2399 := by
    have hcomb := dvd_sub hS (dvd_mul_of_dvd_left hD 3)
    norm_num at hcomb
    simpa [N, u, w] using hcomb
  have hcop79 : IsCoprime N 79 := ((show Prime (79 : ℤ) by norm_num).coprime_iff_not_dvd.mpr h79).symm
  have hcop2399 : IsCoprime N 2399 := ((show Prime (2399 : ℤ) by norm_num).coprime_iff_not_dvd.mpr h2399).symm
  have hdiv98 : N ∣ 98 := by
    apply (hcop79.mul_right hcop2399).dvd_of_dvd_mul_right
    simpa [mul_assoc] using hdiv
  have hbound : |N| ≤ 98 := by
    have hn : (N.natAbs : ℤ) ∣ 98 := by simpa using hdiv98
    simpa using Int.le_of_dvd (by norm_num : (0 : ℤ) < 98) hn
  have hcases : N ∈ ([-7, -14, 7, 14, -49, -98, 49, 98] : List ℤ) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hbound
    interval_cases N
    all_goals solve | norm_num | norm_num at hdiv98 | norm_num at h7
  have hminus7 : ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 - 7 := by
    simpa only [sub_eq_add_neg] using tenner_exclusions79 hVI hExample7 (-7) (by simp)
  have hnorm : u ^ 2 = 79 * w ^ 2 + N := by dsimp [N]; ring
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcases
  rcases hcases with hn | hn | hn | hn | hn | hn | hn | hn
  · exact hminus7 ⟨u, w, hcop, by linarith [hnorm]⟩
  · exact hExample7 ⟨u, w, by linarith [hnorm]⟩
  · exact residue_exclusions79 u w N hcop (by simp [hn]) hnorm
  · exact residue_exclusions79 u w N hcop (by simp [hn]) hnorm
  · have hmod := congrArg (fun a : ℤ => (a : ZMod 8)) hnorm
    rw [hn] at hmod
    push_cast at hmod
    have obstruction : ∀ u w : ZMod 8, u ^ 2 ≠ 79 * w ^ 2 + (-49) := by decide
    exact obstruction _ _ hmod
  · have hmod := congrArg (fun a : ℤ => (a : ZMod 8)) hnorm
    rw [hn] at hmod
    push_cast at hmod
    have obstruction : ∀ u w : ZMod 8, u ^ 2 ≠ 79 * w ^ 2 + (-98) := by decide
    exact obstruction _ _ hmod
  · exact exclude49_79 hminus7 hExample7 ⟨u, w, hcop, by linarith [hnorm]⟩
  · exact exclude98_79 hminus7 hExample7 ⟨u, w, hcop, by linarith [hnorm]⟩

/- Folgerung mit dem als Voraussetzung geführten Kriterium des §. 23. -/

theorem normMinusSevenImpossible
    (hSource : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 - 7 := by
  have hVI := specializeCriterion79 hSource
  have hrow : ∀ k : ℕ, ((tennerStep79^[k + 1]) (0, 1)).2 ≠ |(-7 : ℤ)| := by
    intro k
    have hs := tennerStates79 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with h | h | h | h <;> rw [h] <;> norm_num
  simpa only [sub_eq_add_neg] using hVI (-7) (by decide) hrow

end Beispiel08

namespace Beispiel09

/-
9. Exempel:
y² = 79x²+219x+129 = (11x+8)²−(6x+5)(7x−13),
-/

example (x : ℚ) : 79 * x ^ 2 + 219 * x + 129 = (11 * x + 8) ^ 2 - (6 * x + 5) * (7 * x - 13) := by ring

/-
D = 3.2399, x = 13/7, y = 199/7,
7x = 13+(398p+3587)/(p²−79),
-/

example : (219 ^ 2 - 4 * 79 * 129 : ℤ) = 3 * 2399 := by norm_num

example : (199 / 7 : ℚ) ^ 2 = 79 * (13 / 7) ^ 2 + (219) * (13 / 7) + (129) := by norm_num

example (p : ℚ) : (13) + (2 * (199) * p + (2 * 79 * (13) + (219) * 7)) / (p ^ 2 - 79) = (13) + 1 * ((398) * p + (3587)) / (p ^ 2 - 79) := by ring

/-
S = 3.7².(2399);
-/

example : (7 ^ 2 * (219 ^ 2 - 4 * 79 * 129) : ℤ) = 3 * 7 ^ 2 * 2399 := by norm_num

/-
die Auflösungen der Gleichung v² = 79w²+21 entsprechen
nicht; die äquivalente Gleichung v² = 79w²+7.2399 ist laut
8. Exempels unmöglich, daher ist I in ganzen Zahlen nicht zu
lösen.
-/

/- Hilfsschritt: Der Nenner der p-Function ist nicht Null. -/

private theorem notSquare79 (p : ℚ) : p ^ 2 - 79 ≠ 0 := by
  intro h
  have hs : IsSquare (79 : ℚ) := ⟨p, by nlinarith [h]⟩
  have hi : IsSquare (79 : ℤ) := Rat.isSquare_intCast_iff.mp hs
  norm_num at hi

/- Hilfsschritt: Nenner und Stammzahl der angegebenen p-Function. -/

private theorem normData (x : ℤ) (p : ℚ)
    (hX : (7 : ℚ) * x = 13 + (398 * p + 3587) / (p ^ 2 - 79)) :
    7 ∣ p.num ^ 2 - 79 * (p.den : ℤ) ^ 2 ∧
      p.num ^ 2 - 79 * (p.den : ℤ) ^ 2 ∣ 50379 := by
  have hX' : (7 : ℚ) * x = 13 +
      (2 * 199 * p + (2 * 79 * 13 + 219 * 7)) / (p ^ 2 - 79) := by
    convert hX using 1; ring
  simpa using Kunerth1880.Paragraf07.normData 79 219 129 13 7 199 11 8 6 (-5)
    x p (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (notSquare79 p) hX'

/- Hilfsschritt: Bildung des äquivalenten Parameters. -/

private theorem pairedParameter (x : ℤ) (p : ℚ)
    (hX : (7 : ℚ) * x = 13 + (398 * p + 3587) / (p ^ 2 - 79)) :
    ∃ q : ℚ, (7 : ℚ) * x = 13 + (398 * q + 3587) / (q ^ 2 - 79) ∧
      ∃ ρ : ℤ, ρ ≠ 0 ∧ Int.gcd ρ 7 = 1 ∧
        (p.num ^ 2 - 79 * (p.den : ℤ) ^ 2) *
          (q.num ^ 2 - 79 * (q.den : ℤ) ^ 2) * ρ ^ 2 = 49 * 7197 := by
  have hsI : 7 * x - 13 ≠ 0 := by omega
  have hs : (7 : ℚ) * x - 13 ≠ 0 := by exact_mod_cast hsI
  have hg : 398 * p + 3587 ≠ 0 := by
    intro hz
    rw [hz, zero_div] at hX
    exact hs (by linarith)
  let q : ℚ := -(3587 * p + 31442) / (398 * p + 3587)
  have hqcross : q * (398 * p + 3587) = -(3587 * p + 31442) := by
    exact div_mul_cancel₀ _ hg
  have heq : (398 * q + 3587) / (q ^ 2 - 79) =
      (398 * p + 3587) / (p ^ 2 - 79) := by
    apply (div_eq_div_iff (notSquare79 q) (notSquare79 p)).mpr
    linear_combination (p - q) * hqcross
  have hXq : (7 : ℚ) * x = 13 + (398 * q + 3587) / (q ^ 2 - 79) := by
    rw [heq]
    exact hX
  have hX' : (7 : ℚ) * x = 13 +
      (2 * 199 * p + (2 * 79 * 13 + 219 * 7)) / (p ^ 2 - 79) := by
    convert hX using 1; ring
  have hg' : 2 * (199 : ℚ) * p + (2 * 79 * 13 + 219 * 7) ≠ 0 := by
    convert hg using 1; ring
  have hpairs := Kunerth1880.Paragraf13.pairedNorms 79 219 129 13 7 199 x p
    (by norm_num) (by norm_num) (by norm_num) (notSquare79 p) hg' hX'
  have hpairs' : ∃ ρ : ℤ, ρ ≠ 0 ∧ Int.gcd ρ 7 = 1 ∧
      (p.num ^ 2 - 79 * (p.den : ℤ) ^ 2) *
        (q.num ^ 2 - 79 * (q.den : ℤ) ^ 2) * ρ ^ 2 = 49 * 7197 := by
    convert hpairs (by convert notSquare79 q using 1; norm_num [q]) using 1; norm_num [q]
  obtain ⟨ρ, hρ, hρ7, hpair⟩ := hpairs'
  exact ⟨q, hXq, ρ, hρ, hρ7, hpair⟩

/- Hilfsschritt: Das Zahlenglied 21 und die äquivalente Gleichung. -/

private theorem norm21Equivalent (x : ℤ) (p : ℚ)
    (hX : (7 : ℚ) * x = 13 + (398 * p + 3587) / (p ^ 2 - 79))
    (hN : p.num ^ 2 - 79 * (p.den : ℤ) ^ 2 = 21) :
    ∃ v w : ℤ, v ^ 2 = 79 * w ^ 2 + 7 * 2399 := by
  obtain ⟨q, hXq, ρ, _hρ, _hρ7, hpair⟩ := pairedParameter x p hX
  obtain ⟨⟨k, hk⟩, _hstock⟩ := normData x q hXq
  rw [hN, hk] at hpair
  have hprod : k * ρ ^ 2 = 2399 := by nlinarith [hpair]
  have hsf : Squarefree (2399 : ℤ) := (show Prime (2399 : ℤ) by norm_num).squarefree
  have hu : IsUnit ρ := hsf ρ ⟨k, by nlinarith [hprod]⟩
  have hρsq : ρ ^ 2 = 1 := by
    rcases Int.isUnit_iff.mp hu with h | h <;> rw [h] <;> norm_num
  refine ⟨q.num, (q.den : ℤ), ?_⟩
  rw [hρsq] at hprod
  nlinarith [hk, hprod]

/- Hilfsschritt: Der Bruch aus theilfremden Zahlen. -/

private theorem primitiveNorm (v w : ℤ) (hw : w ≠ 0) (hcop : Int.gcd v w = 1) :
    let p : ℚ := (v : ℚ) / w
    p.num ^ 2 - 79 * (p.den : ℤ) ^ 2 = v ^ 2 - 79 * w ^ 2 := by
  let p : ℚ := (v : ℚ) / w
  obtain ⟨g, hv, hwg⟩ := Rat.num_den_mk (q := p) (n := v) (d := w) hw
    (by simp [p, Rat.divInt_eq_div])
  obtain ⟨s, t, hst⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hg : g ∣ (1 : ℤ) := by
    refine ⟨s * p.num + t * (p.den : ℤ), ?_⟩
    rw [hv, hwg] at hst
    linear_combination -hst
  have hu : IsUnit g := isUnit_of_dvd_one hg
  change p.num ^ 2 - 79 * (p.den : ℤ) ^ 2 = _
  rw [hv, hwg]
  rcases Int.isUnit_iff.mp hu with h | h <;> rw [h] <;> ring

example (v w : ℤ) (hw : w ≠ 0) (hcop : Int.gcd v w = 1)
    (hN : v ^ 2 = 79 * w ^ 2 + 21) (x : ℤ)
    (hX : 7 * (x : ℚ) = 13 +
      (398 * ((v : ℚ) / w) + 3587) / (((v : ℚ) / w) ^ 2 - 79)) :
    ∃ v₂ w₂ : ℤ, v₂ ^ 2 = 79 * w₂ ^ 2 + 7 * 2399 := by
  apply norm21Equivalent x ((v : ℚ) / w) hX
  rw [primitiveNorm v w hw hcop]
  linarith

/- Hilfsschritt: Ausscheidung der unzulässigen Factoren. -/

private theorem candidateNorm (p : ℚ) (k : ℤ)
    (hN : p.num ^ 2 - 79 * (p.den : ℤ) ^ 2 = 7 * k)
    (hstock : p.num ^ 2 - 79 * (p.den : ℤ) ^ 2 ∣ 50379)
    (h2399 : ¬ (2399 : ℤ) ∣ k) :
    p.num ^ 2 - 79 * (p.den : ℤ) ^ 2 = -7 ∨
      p.num ^ 2 - 79 * (p.den : ℤ) ^ 2 = 21 := by
  have hk : k ∣ 7197 := by
    obtain ⟨t, ht⟩ := hstock
    refine ⟨t, ?_⟩
    rw [hN] at ht
    nlinarith [ht]
  have hcop : IsCoprime k (2399 : ℤ) :=
    ((show Prime (2399 : ℤ) by norm_num).coprime_iff_not_dvd.mpr h2399).symm
  have hk3 : k ∣ 3 := hcop.dvd_of_dvd_mul_right (by convert hk using 1; norm_num)
  have hkmem : k ∈ (3 : ℤ).divisors := Int.mem_divisors.mpr ⟨hk3, by norm_num⟩
  have hdivs : (3 : ℤ).divisors = {1, -1, 3, -3} := by decide
  rw [hdivs] at hkmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hkmem
  rcases hkmem with rfl | rfl | rfl | rfl
  · have hm := congrArg (fun t : ℤ => (t : ZMod 8)) hN
    push_cast at hm
    have hno : ∀ v w : ZMod 8, v ^ 2 - 79 * w ^ 2 ≠ 7 := by decide
    exact False.elim (hno _ _ (by simpa using hm))
  · left; linear_combination hN
  · right; linear_combination hN
  · have hm := congrArg (fun t : ℤ => (t : ZMod 8)) hN
    push_cast at hm
    have hno : ∀ v w : ZMod 8, v ^ 2 - 79 * w ^ 2 ≠ -21 := by decide
    exact False.elim (hno _ _ (by simpa using hm))

/- Hilfsschritt: Übergang von der ursprünglichen Gleichung zu den Nennern. -/

private theorem originalCandidates (x y : ℤ)
    (h : y ^ 2 = 79 * x ^ 2 + 219 * x + 129) :
    ∃ p : ℚ, (7 : ℚ) * x = 13 + (398 * p + 3587) / (p ^ 2 - 79) ∧
      (p.num ^ 2 - 79 * (p.den : ℤ) ^ 2 = -7 ∨
        p.num ^ 2 - 79 * (p.den : ℤ) ^ 2 = 21) := by
  have hsI : 7 * x - 13 ≠ 0 := by omega
  have hs : (7 : ℚ) * x - 13 ≠ 0 := by exact_mod_cast hsI
  have hQ : (y : ℚ) ^ 2 = 79 * (x : ℚ) ^ 2 + 219 * x + 129 := by exact_mod_cast h
  let p : ℚ := (7 * y + 199) / (7 * x - 13)
  have hP : ((7 : ℚ) * x - 13) * p = 7 * y + 199 := by
    dsimp [p]
    field_simp
  have hcross : ((7 : ℚ) * x - 13) * (p ^ 2 - 79) = 398 * p + 3587 := by
    apply mul_left_cancel₀ hs
    linear_combination (((7 : ℚ) * x - 13) * p + 7 * y - 199) * hP + 49 * hQ
  have hX : (7 : ℚ) * x = 13 + (398 * p + 3587) / (p ^ 2 - 79) := by
    have hc := (eq_div_iff (notSquare79 p)).mpr hcross
    linarith
  obtain ⟨q, hXq, ρ, _hρ, _hρ7, hpair⟩ := pairedParameter x p hX
  obtain ⟨⟨k₁, hk₁⟩, hstockp⟩ := normData x p hX
  obtain ⟨⟨k₂, hk₂⟩, hstockq⟩ := normData x q hXq
  /- Hilfsschritt: Nach XIIa müsste 2399² die Zahl 7²(3·2399) theilen. -/
  have hnotboth : ¬ ((2399 : ℤ) ∣ p.num ^ 2 - 79 * (p.den : ℤ) ^ 2 ∧
      (2399 : ℤ) ∣ q.num ^ 2 - 79 * (q.den : ℤ) ^ 2) := by
    rintro ⟨h₁, h₂⟩
    have hdiv := dvd_mul_of_dvd_left (mul_dvd_mul h₁ h₂) (ρ ^ 2)
    rw [hpair] at hdiv
    norm_num at hdiv
  rw [hk₁, hk₂] at hnotboth
  by_cases hd : (2399 : ℤ) ∣ k₁
  · exact ⟨q, hXq, candidateNorm q k₂ hk₂ hstockq (fun h₂ =>
      hnotboth ⟨dvd_mul_of_dvd_right hd 7, dvd_mul_of_dvd_right h₂ 7⟩)⟩
  · exact ⟨p, hX, candidateNorm p k₁ hk₁ hstockp hd⟩

example (x y : ℤ) (h : y ^ 2 = 79 * x ^ 2 + 219 * x + 129) :
    (∃ v w : ℤ, v ^ 2 = 79 * w ^ 2 - 7) ∨
      (∃ v w : ℤ, v ^ 2 = 79 * w ^ 2 + 7 * 2399) := by
  obtain ⟨p, hX, hN | hN⟩ := originalCandidates x y h
  · left
    exact ⟨p.num, (p.den : ℤ), by linear_combination hN⟩
  · right
    exact norm21Equivalent x p hX hN

/- Folgerung mit den als Voraussetzungen geführten Aussagen aus §. 16
und §. 23. -/

example
    (hSelection : Kunerth1880.Paragraf16.singularPrimeSelection)
    (hSource : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N)
    (v w : ℤ) (hw : w ≠ 0) (hcop : Int.gcd v w = 1)
    (hN : v ^ 2 = 79 * w ^ 2 + 21) :
    ¬ ∃ x : ℤ, 7 * (x : ℚ) = 13 +
      (398 * ((v : ℚ) / w) + 3587) / (((v : ℚ) / w) ^ 2 - 79) := by
  rintro ⟨x, hX⟩
  have hNp : ((v : ℚ) / w).num ^ 2 - 79 * (((v : ℚ) / w).den : ℤ) ^ 2 = 21 := by
    rw [primitiveNorm v w hw hcop]
    linarith
  obtain ⟨v₂, w₂, h₂⟩ := norm21Equivalent x ((v : ℚ) / w) hX hNp
  apply Kunerth1880.Paragraf25.Beispiel08.noIntegerSolutions hSelection hSource
  exact ⟨w₂, v₂, by simpa using h₂⟩

/- Folgerung mit den als Voraussetzungen geführten Aussagen aus §. 16
und §. 23. -/

example
    (hSelection : Kunerth1880.Paragraf16.singularPrimeSelection)
    (hSource : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ¬ ∃ v w : ℤ, v ^ 2 = 79 * w ^ 2 + 7 * 2399 := by
  rintro ⟨v, w, h⟩
  apply Kunerth1880.Paragraf25.Beispiel08.noIntegerSolutions hSelection hSource
  exact ⟨w, v, by simpa using h⟩

/- Folgerung mit den als Voraussetzungen geführten Aussagen aus §. 16
und §. 23. -/

example
    (hSelection : Kunerth1880.Paragraf16.singularPrimeSelection)
    (hSource : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ¬ ∃ x y : ℤ, y ^ 2 = 79 * x ^ 2 + (219) * x + (129) := by
  rintro ⟨x, y, h⟩
  obtain ⟨p, hX, hN | hN⟩ := originalCandidates x y h
  · apply Kunerth1880.Paragraf25.Beispiel08.normMinusSevenImpossible hSource
    refine ⟨p.num, (p.den : ℤ), ?_, ?_⟩
    · simpa [Int.gcd] using p.reduced
    · linear_combination hN
  · obtain ⟨v, w, hvw⟩ := norm21Equivalent x p hX hN
    apply Kunerth1880.Paragraf25.Beispiel08.noIntegerSolutions hSelection hSource
    exact ⟨w, v, by simpa using hvw⟩

end Beispiel09

namespace Beispiel10

/-
10. Exempel:
y² = 79x²+3.2399, Δ² = 79β²+3.2399(α²−79), α = 9,
Δ² = 79β²+6.2399, 6.2399 = −6.−2399, also
-/

example : (3 * 2399 * (9 ^ 2 - 79) : ℤ) = 6 * 2399 := by norm_num

example : (6 * 2399 : ℤ) = (-6) * (-2399) := by norm_num

/-
Δ₁² = 79β₁²−6 und β₁ = 1/3, Δ₁ = 5/3;
-/

example : (5 / 3 : ℚ) ^ 2 = 79 * (1 / 3) ^ 2 - 6 := by norm_num

/-
Seite 374

ferner
Δ,,² = 79β,,²−2399 und β,, = 15, Δ,, = 124,
-/

example : (124 : ℤ) ^ 2 = 79 * 15 ^ 2 - 2399 := by norm_num

/-
somit nach dem letzten Absatz in §. 16
β = 49/3, Δ = 565/3 und 3β = 49+2(565p+3871)/(p²−79),
-/

example : (124 * (1 / 3) - (5 / 3) * 15 : ℚ) = 49 / 3 := by norm_num

example : (79 * (1 / 3) * 15 - (5 / 3) * 124 : ℚ) = 565 / 3 := by norm_num

example : (49 / 3 : ℚ) ^ 2 * 79 + 6 * 2399 = (565 / 3) ^ 2 := by norm_num

example (p : ℚ) : (49) + (2 * (565) * p + (2 * 79 * (49) + (0) * 3)) / (p ^ 2 - 79) = (49) + 2 * ((565) * p + (3871)) / (p ^ 2 - 79) := by ring

/-
S₁ = −4.3³(79.2399);
-/

example : (3 ^ 2 * (-4 * 79 * (6 * 2399)) / 2 : ℚ) = -4 * 3 ^ 3 * (79 * 2399) := by norm_num

/-
in den Gleichungen v² = 79w²∓3(1, 2, 3, 6) sind die
Zahlenglieder 3 und 6 wegen der VI. Verticalreihe unzulässig;
-/

example : (8 : ℤ) ^ 2 ≤ 79 ∧ 79 < (8 + 1) ^ 2 := by decide

/- Hilfsdefinition: Ein Rechenschritt der Kettenbruchentwicklung. -/

private def tennerStep79 (s : ℤ × ℤ) : ℤ × ℤ :=
  let q := (8 + s.1) / s.2
  let m := q * s.2 - s.1
  (m, (79 - m ^ 2) / s.2)

example :
    ((List.range 5).map fun k => (tennerStep79^[k + 1]) (0, 1)) =
      [(8, 15), (7, 2), (7, 15), (8, 1), (8, 15)] := by decide

example : ([((0, 1) : ℤ × ℤ), (8, 15), (7, 2), (7, 15), (8, 1)]).all
    (fun s => decide (s.2 ≠ 0) && (79 - (tennerStep79 s).1 ^ 2) % s.2 == 0) := by decide

/- Hilfsschritt: Fortsetzung der berechneten Kettenbruchperiode. -/

private theorem tennerStates79 (k : ℕ) :
    (tennerStep79^[k + 1]) (0, 1) ∈
      ([(8, 15), (7, 2), (7, 15), (8, 1)] : List (ℤ × ℤ)) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ih
    rcases ih with h | h | h | h <;> rw [h] <;> decide

/- Hilfsschritt: Achterreste für −9 und −18. -/

example (u z N : ℤ)
    (hN : N ∈ ([-9, -18] : List ℤ)) (hnorm : u ^ 2 = 79 * z ^ 2 + N) : False := by
  have hmod := congrArg (fun a : ℤ => (a : ZMod 8)) hnorm
  push_cast at hmod
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
  rcases hN with rfl | rfl
  · have obstruction : ∀ u z : ZMod 8, u ^ 2 ≠ 79 * z ^ 2 + (-9) := by decide
    exact obstruction _ _ hmod
  · have obstruction : ∀ u z : ZMod 8, u ^ 2 ≠ 79 * z ^ 2 + (-18) := by decide
    exact obstruction _ _ hmod

/- Hilfsschritt: Die Zahlenglieder 3 und 6 im vorausgesetzten Kriterium. -/

example
    (hVI : ∀ N : ℤ, N ^ 2 < 79 →
      (∀ k : ℕ, ((tennerStep79^[k + 1]) (0, 1)).2 ≠ |N|) →
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 + N) :
    ∀ N ∈ ([3, -3, 6, -6] : List ℤ),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 + N := by
  intro N hN
  apply hVI N
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
    rcases hN with rfl | rfl | rfl | rfl <;> norm_num
  · intro k
    have hs := tennerStates79 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs hN
    rcases hs with hs | hs | hs | hs <;> rw [hs] <;>
      rcases hN with rfl | rfl | rfl | rfl <;> norm_num

/- 9 und 18 führen zu Auflösungen in relativ zusammengesetzten Zahlen; -/

example : Prop :=
  ∀ N ∈ ([9, 18] : List ℤ),
    ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 79 * w ^ 2 + N

/-
folglich gibt es für β und x keine ganzen Zahlen
(8. Absatz im §. 23).
-/

private def noSix2399 : Prop :=
  ¬ ∃ β Δ : ℤ, Δ ^ 2 = 79 * β ^ 2 + 6 * 2399

/- Hilfsschritt: Folgerung für x mit α = 9 unter Voraussetzung der
behaupteten Unmöglichkeit für β. -/

example (hSource : noSix2399) :
    ¬ ∃ x y : ℤ, y ^ 2 = 79 * x ^ 2 + 3 * 2399 := by
  have haux : ¬ ∃ Δ β : ℤ, Δ ^ 2 = 79 * β ^ 2 + 6 * 2399 := by
    rintro ⟨Δ, β, h⟩
    exact hSource ⟨β, Δ, by simpa using h⟩
  rintro ⟨x, y, h⟩
  let β := y - 9 * x
  have hIII : y = 9 * x + β := by dsimp [β]; ring
  have hquadratic : (79 - 9 ^ 2) * x ^ 2 - 2 * 9 * β * x +
      3 * 2399 - β ^ 2 = 0 := by
    rw [hIII] at h
    linear_combination -h
  apply haux
  refine ⟨(79 - 9 ^ 2) * x - 9 * β, β, ?_⟩
  linear_combination (79 - 9 ^ 2) * hquadratic

end Beispiel10

namespace Beispiel11

/-
11. Exempel:
y² = 386x²+538x+193 = (10x+9)²+2(11x+7)(13x+8),
-/

example (x : ℚ) : 386 * x ^ 2 + 538 * x + 193 = (10 * x + 9) ^ 2 + 2 * (11 * x + 7) * (13 * x + 8) := by ring

/- Rechenschritt: Der Nullpunkt eines angegebenen linearen Factors. -/

example : ∃ x y : ℚ, y ^ 2 = 386 * x ^ 2 + (538) * x + (193) := by
  exact ⟨-7 / 11, 29 / 11, by norm_num⟩

/-
D = −4.2137, 11x = −7+2(29p+257)/(p²−386),
-/

example : (538 ^ 2 - 4 * 386 * 193 : ℤ) = -4 * 2137 := by norm_num

example (p : ℚ) : (-7) + (2 * (29) * p + (2 * 386 * (-7) + (538) * 11)) / (p ^ 2 - 386) = (-7) + 2 * ((29) * p + (257)) / (p ^ 2 - 386) := by ring

/-
S₁ = −2.11²(2137);
-/

example : (11 ^ 2 * (-4 * 2137) / 2 : ℚ) = -2 * 11 ^ 2 * 2137 := by norm_num

/-
da v² = 386w²∓22 in rationalen Zahlen unmöglich sind, so gibt
es keine ganzen Zahlen für x.
-/

private def noRational22 : Prop :=
  ∀ N : ℤ, N ∈ ([22, -22] : List ℤ) →
    ¬ ∃ v w : ℚ, v ^ 2 = 386 * w ^ 2 + N

private theorem noPlus22 (hRational : noRational22) :
    ¬ ∃ v w : ℚ, v ^ 2 = 386 * w ^ 2 + 22 :=
  hRational 22 (by simp)

private theorem noMinus22 (hRational : noRational22) :
    ¬ ∃ v w : ℚ, v ^ 2 = 386 * w ^ 2 - 22 := by
  simpa only [Int.cast_neg, Int.cast_ofNat, sub_eq_add_neg] using
    hRational (-22) (by simp)

/- Hilfsschritt: Der Nenner der p-Function ist nicht Null. -/

private theorem notSquare386 (p : ℚ) : p ^ 2 - 386 ≠ 0 := by
  intro h
  exact (show ¬ IsSquare (386 : ℚ) by norm_num) ⟨p, by nlinarith [h]⟩

/- Hilfsschritt: Theilbarkeit des Nenners und die Stammzahl. -/

private theorem normStock (x : ℤ) (p : ℚ)
    (hX : (11 : ℚ) * x = -7 + (58 * p + 514) / (p ^ 2 - 386)) :
    11 ∣ p.num ^ 2 - 386 * (p.den : ℤ) ^ 2 ∧
      p.num ^ 2 - 386 * (p.den : ℤ) ^ 2 ∣ 47014 := by
  have hp := notSquare386 p
  have hX' : (11 : ℚ) * x = -7 +
      (2 * 29 * p + (2 * 386 * (-7) + 538 * 11)) / (p ^ 2 - 386) := by
    convert hX using 1; ring
  have hdata := Kunerth1880.Paragraf07.normData 386 538 193 (-7) 11 29 10 9 (-26) 16
    x p (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hp hX'
  obtain ⟨k,hk⟩ := Kunerth1880.Paragraf07.preparationFromVIII 386 538 (-7) 11 29 10 9 (-26) 16
    x p (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp hX'
  have hprep : p.num = 11 * k - 10 * (p.den : ℤ) := by linear_combination hk
  let v : ℤ := p.num
  let w : ℤ := p.den
  let N := v ^ 2 - 386 * w ^ 2
  have hwq : (w : ℚ) ≠ 0 := by dsimp [w]; exact_mod_cast p.den_nz
  have hpv : p = (v : ℚ) / w := by simpa [v,w] using (Rat.num_div_den p).symm
  have hcross : ((11 : ℚ) * x + 7) * (p ^ 2 - 386) = 58 * p + 514 := by
    exact (eq_div_iff hp).mp (by linear_combination hX)
  rw [hpv] at hcross
  field_simp [hwq] at hcross
  have hXI : (11 * x + 7) * N = (58 * v + 514 * w) * w := by
    have hi : (11 * x + 7) * (v ^ 2 - w ^ 2 * 386) = w * (v * 58 + w * 514) := by
      exact_mod_cast hcross
    dsimp [N]
    linear_combination hi
  have hL : N * (x * (29 * v - 257 * w) + 203 * k - 501 * w) = 47014 * w ^ 3 := by
    apply mul_left_cancel₀ (show (11 : ℤ) ≠ 0 by norm_num)
    dsimp [N,v,w] at hXI ⊢
    linear_combination (29 * p.num - 257 * (p.den : ℤ)) * hXI -
      203 * (p.num ^ 2 - 386 * (p.den : ℤ) ^ 2) * hprep
  have hcop : IsCoprime N (w ^ 3) := by
    apply Kunerth1880.Paragraf07.normCoprime
    simpa [v,w,Int.gcd] using p.reduced
  refine ⟨hdata.1, ?_⟩
  exact hcop.dvd_of_dvd_mul_right ⟨x * (29 * v - 257 * w) + 203 * k - 501 * w, hL.symm⟩

/- Hilfsschritt: Ausscheidung der unzulässigen Factoren. -/

private theorem stockCandidates (p : ℚ) (k : ℤ)
    (hN : p.num ^ 2 - 386 * (p.den : ℤ) ^ 2 = 11 * k)
    (hstock : p.num ^ 2 - 386 * (p.den : ℤ) ^ 2 ∣ 47014)
    (hprime : ¬ (2137 : ℤ) ∣ k) :
    p.num ^ 2 - 386 * (p.den : ℤ) ^ 2 ∈ ([11,-11,22,-22] : List ℤ) := by
  have hk : k ∣ 4274 := by
    obtain ⟨t, ht⟩ := hstock
    refine ⟨t, ?_⟩
    rw [hN] at ht
    nlinarith [ht]
  have hcop : IsCoprime k (2137 : ℤ) :=
    ((show Prime (2137 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hprime).symm
  have hsmall : k ∣ 2 := hcop.dvd_of_dvd_mul_right (by convert hk using 1; norm_num)
  have hkmem : k ∈ (2 : ℤ).divisors := Int.mem_divisors.mpr ⟨hsmall, by norm_num⟩
  have hdivs : (2 : ℤ).divisors = {1,-1,2,-2} := by decide
  rw [hdivs] at hkmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hkmem
  rcases hkmem with rfl | rfl | rfl | rfl
  all_goals rw [hN]; decide

/- Hilfsschritt: Übergang von der Gleichung zu den Nennern. -/

private theorem normCandidates (x y : ℤ)
    (h : y ^ 2 = 386 * x ^ 2 + 538 * x + (193)) :
    ∃ v w : ℤ, Int.gcd v w = 1 ∧
      v ^ 2 - 386 * w ^ 2 ∈ ([11,-11,22,-22] : List ℤ) := by
  have hsI : 11 * x - (-7) ≠ 0 := by omega
  have hs : (11 : ℚ) * x - (-7) ≠ 0 := by exact_mod_cast hsI
  have hQ : (y : ℚ) ^ 2 = 386 * (x : ℚ) ^ 2 + 538 * x + (193) := by exact_mod_cast h
  let p : ℚ := (11 * y + 29) / (11 * x - (-7))
  have hP : ((11 : ℚ) * x - (-7)) * p = 11 * y + 29 := by dsimp [p]; field_simp
  have hp := notSquare386 p
  have hcross : ((11 : ℚ) * x - (-7)) * (p ^ 2 - 386) = 58 * p + 514 := by
    apply mul_left_cancel₀ hs
    linear_combination (((11 : ℚ) * x - (-7)) * p + 11 * y - 29) * hP + 121 * hQ
  have hX : (11 : ℚ) * x = (-7) + (58 * p + 514) / (p ^ 2 - 386) := by
    have hc := (eq_div_iff hp).mpr hcross
    linarith
  have hg : 58 * p + 514 ≠ 0 := by
    intro hz
    rw [hz, zero_div] at hX
    exact hs (by linarith)
  let q : ℚ := -(514 * p + 22388) / (58 * p + 514)
  have hq := notSquare386 q
  have hqcross : q * (58 * p + 514) = -(514 * p + 22388) := by
    dsimp [q]
    exact div_mul_cancel₀ _ hg
  have heq : (58 * q + 514) / (q ^ 2 - 386) = (58 * p + 514) / (p ^ 2 - 386) := by
    apply (div_eq_div_iff hq hp).mpr
    linear_combination (p - q) * hqcross
  have hXq : (11 : ℚ) * x = (-7) + (58 * q + 514) / (q ^ 2 - 386) := by rw [heq]; exact hX
  have hX' : (11 : ℚ) * x = (-7) +
      (2 * 29 * p + (2 * 386 * (-7) + 538 * 11)) / (p ^ 2 - 386) := by convert hX using 1; ring
  have hg' : 2 * (29 : ℚ) * p + (2 * 386 * (-7) + 538 * 11) ≠ 0 := by convert hg using 1; ring
  have hpairs := Kunerth1880.Paragraf13.pairedNorms 386 538 (193) (-7) 11 29 x p
    (by norm_num) (by norm_num) (by norm_num) hp hg' hX'
  have hpair : ∃ ρ : ℤ, ρ ≠ 0 ∧ Int.gcd ρ 11 = 1 ∧
      (p.num ^ 2 - 386 * (p.den : ℤ) ^ 2) *
        (q.num ^ 2 - 386 * (q.den : ℤ) ^ 2) * ρ ^ 2 = 11 ^ 2 * (-8548) := by
    convert hpairs (by convert hq using 1; norm_num [q]) using 1; norm_num [q]
  obtain ⟨ρ, _hρ, _hρn, hpair⟩ := hpair
  obtain ⟨hNp,hpstock⟩ := normStock x p hX
  obtain ⟨hNq,hqstock⟩ := normStock x q hXq
  obtain ⟨k₁,hk₁⟩ := hNp
  obtain ⟨k₂,hk₂⟩ := hNq
  /- Hilfsschritt: XIIa mit n = 11 und D = −4 · 2137. -/
  have hnotboth : ¬ ((2137 : ℤ) ∣ p.num ^ 2 - 386 * (p.den : ℤ) ^ 2 ∧
      (2137 : ℤ) ∣ q.num ^ 2 - 386 * (q.den : ℤ) ^ 2) := by
    rintro ⟨h₁, h₂⟩
    have hdiv := dvd_mul_of_dvd_left (mul_dvd_mul h₁ h₂) (ρ ^ 2)
    rw [hpair] at hdiv
    norm_num at hdiv
  rw [hk₁, hk₂] at hnotboth
  by_cases hd : (2137 : ℤ) ∣ k₁
  · refine ⟨q.num, (q.den : ℤ), ?_, stockCandidates q k₂ hk₂ hqstock (fun h₂ =>
      hnotboth ⟨dvd_mul_of_dvd_right hd 11, dvd_mul_of_dvd_right h₂ 11⟩)⟩
    simpa [Int.gcd] using q.reduced
  · refine ⟨p.num, (p.den : ℤ), ?_, stockCandidates p k₁ hk₁ hpstock hd⟩
    simpa [Int.gcd] using p.reduced

/- Hilfsdefinition: Glieder einer Periode der Kettenbruchentwicklung. -/

private def cfState : Fin 12 → ℤ × ℤ × ℤ :=
  ![(1,19,25), (1,6,14), (1,8,23), (4,15,7), (1,13,31), (18,18,2),
    (1,18,31), (4,13,7), (1,15,23), (1,8,14), (1,6,25), (38,19,1)]

/- Hilfsdefinition: Die I. Verticalreihe der Rechnung. -/

private def cfA : ℕ → ℤ
  | 0 => 19
  | k + 1 => (cfState ⟨k % 12, Nat.mod_lt _ (by decide)⟩).1

/- Hilfsdefinition: Die III. Verticalreihe der Rechnung. -/

private def cfM : ℕ → ℤ
  | 0 => 0
  | k + 1 => (cfState ⟨k % 12, Nat.mod_lt _ (by decide)⟩).2.1

/- Hilfsdefinition: Die VI. Verticalreihe der Rechnung. -/

private def cfQ : ℕ → ℤ
  | 0 => 1
  | k + 1 => (cfState ⟨k % 12, Nat.mod_lt _ (by decide)⟩).2.2

/- Hilfsschritt: Quotienten und Divisionen der Kette; Ausschluss von 11. -/

private theorem cfData386 : cfM 0 = 0 ∧ cfQ 0 = 1 ∧
    (∀ k, (cfA k : ℝ) ≤ (Real.sqrt 386 + cfM k) / cfQ k ∧
      (Real.sqrt 386 + cfM k) / cfQ k < cfA k + 1) ∧
    (∀ k, cfM (k + 1) = cfA k * cfQ k - cfM k) ∧
    (∀ k, cfQ (k + 1) * cfQ k = 386 - cfM (k + 1) ^ 2) ∧
    (∀ k, cfQ (k + 1) ≠ 11) := by
  have hs : (Real.sqrt 386) ^ 2 = 386 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 386 := Real.sqrt_nonneg _
  have hlo : (19 : ℝ) ≤ Real.sqrt 386 := by nlinarith
  have hhi : Real.sqrt 386 < (20 : ℝ) := by nlinarith
  have hbounds : ∀ j : Fin 12, 0 < (cfState j).2.2 ∧
      (cfState j).1 * (cfState j).2.2 ≤ 19 + (cfState j).2.1 ∧
      20 + (cfState j).2.1 ≤ ((cfState j).1 + 1) * (cfState j).2.2 := by decide
  have hstep : ∀ j : Fin 12,
      let j' : Fin 12 := ⟨(j.val + 1) % 12, Nat.mod_lt _ (by decide)⟩
      (cfState j').2.1 = (cfState j).1 * (cfState j).2.2 - (cfState j).2.1 ∧
      (cfState j').2.2 * (cfState j).2.2 = 386 - (cfState j').2.1 ^ 2 := by decide
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro k
    cases k with
    | zero => simpa [cfA, cfM, cfQ] using (show (19 : ℝ) ≤ Real.sqrt 386 ∧ Real.sqrt 386 < 19 + 1 by norm_num; exact ⟨hlo, hhi⟩)
    | succ k =>
      let j : Fin 12 := ⟨k % 12, Nat.mod_lt _ (by decide)⟩
      obtain ⟨hQ, hL, hU⟩ := hbounds j
      change ((cfState j).1 : ℝ) ≤ (Real.sqrt 386 + (cfState j).2.1) / (cfState j).2.2 ∧
        (Real.sqrt 386 + (cfState j).2.1) / (cfState j).2.2 < (cfState j).1 + 1
      have hQ' : (0 : ℝ) < (cfState j).2.2 := by exact_mod_cast hQ
      have hL' : ((cfState j).1 : ℝ) * (cfState j).2.2 ≤ 19 + (cfState j).2.1 := by exact_mod_cast hL
      have hU' : (20 : ℝ) + (cfState j).2.1 ≤ ((cfState j).1 + 1) * (cfState j).2.2 := by exact_mod_cast hU
      constructor
      · apply (le_div_iff₀ hQ').mpr
        linarith
      · apply (div_lt_iff₀ hQ').mpr
        linarith
  · intro k
    cases k with
    | zero => norm_num [cfM, cfA, cfQ, cfState]
    | succ k =>
      have h := (hstep ⟨k % 12, Nat.mod_lt _ (by decide)⟩).1
      simpa [cfM, cfA, cfQ, Nat.add_mod] using h
  · intro k
    cases k with
    | zero => norm_num [cfM, cfA, cfQ, cfState]
    | succ k =>
      have h := (hstep ⟨k % 12, Nat.mod_lt _ (by decide)⟩).2
      simpa [cfM, cfA, cfQ, Nat.add_mod] using h
  · intro k
    have h : ∀ j : Fin 12, (cfState j).2.2 ≠ 11 := by decide
    exact h ⟨k % 12, Nat.mod_lt _ (by decide)⟩

/- Hilfsschritt: Anwendung des als Voraussetzung geführten Kriteriums. -/

private theorem specializeCriterion386
    (hCriterion : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ∀ N : ℤ, N ^ 2 < 386 →
      (∀ k : ℕ, cfQ (k + 1) ≠ |N|) →
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 386 * w ^ 2 + N := by
  intro N hN habsent
  obtain ⟨hM, hQ, hfloor, hMstep, hQstep, _hrow⟩ := cfData386
  have hns : ¬ ∃ q : ℤ, q ^ 2 = 386 := by
    rintro ⟨q, hq⟩
    have hs : IsSquare (386 : ℤ) := ⟨q, by nlinarith [hq]⟩
    norm_num at hs
  have hNreal : (|N| : ℤ) < Real.sqrt (386 : ℤ) := by
    have hsq : (((|N| : ℤ) : ℝ)) ^ 2 < 386 := by
      exact_mod_cast (show |N| ^ 2 < 386 by simpa only [sq_abs] using hN)
    have hs : (Real.sqrt 386) ^ 2 = 386 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt 386 := Real.sqrt_nonneg _
    norm_num only [Int.cast_ofNat]
    nlinarith
  exact hCriterion 386 N cfA cfM cfQ (by norm_num) hns
    hM hQ hfloor hMstep hQstep hNreal habsent

/- Folgerung unter Voraussetzung der behaupteten rationalen Unmöglichkeit
und des Kriteriums des §. 23. -/

example
    (hRational : noRational22)
    (hSource : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ¬ ∃ x y : ℤ, y ^ 2 = 386 * x ^ 2 + 538 * x + 193 := by
  have hsmall : ∀ N ∈ ([11,-11] : List ℤ),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 386 * w ^ 2 + N := by
    intro N hN
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
    rcases hN with rfl | rfl
    all_goals apply specializeCriterion386 hSource _ (by norm_num)
    all_goals
      intro k
      simpa using cfData386.2.2.2.2.2 k
  rintro ⟨x,y,h⟩
  obtain ⟨v,w,hcop,hN⟩ := normCandidates x y h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
  rcases hN with hN | hN | hN | hN
  · exact hsmall 11 (by decide) ⟨v,w,hcop,by linarith⟩
  · exact hsmall (-11) (by decide) ⟨v,w,hcop,by linarith⟩
  · apply noPlus22 hRational
    refine ⟨v,w,?_⟩
    exact_mod_cast (show v ^ 2 = 386 * w ^ 2 + 22 by linarith)
  · apply noMinus22 hRational
    refine ⟨v,w,?_⟩
    exact_mod_cast (show v ^ 2 = 386 * w ^ 2 - 22 by linarith)

end Beispiel11

namespace Beispiel12

/-
12. Exempel:
y² = 291x²+115x+461 = (14x−11)²+(5x+17)(19x+20);
-/

example (x : ℚ) : 291 * x ^ 2 + 115 * x + 461 = (14 * x - 11) ^ 2 + (5 * x + 17) * (19 * x + 20) := by ring

/-
D = −17².1811, 5x = −17+(−586p−9319)/(p²−291),
S = −5².17²(1811);
-/

example : (115 ^ 2 - 4 * 291 * 461 : ℤ) = -17 ^ 2 * 1811 := by norm_num

example (p : ℚ) : (-17) + (2 * (-293) * p + (2 * 291 * (-17) + (115) * 5)) / (p ^ 2 - 291) = (-17) + 1 * ((-586) * p + (-9319)) / (p ^ 2 - 291) := by ring

/-
für N = 85 und −85.1811 findet man unpassende Werthe für p,
und für N = −5.17² eine unmögliche Gleichung.
-/

example : ¬ ∃ v w : ℤ, v ^ 2 = 291 * w ^ 2 - 5 * 17 ^ 2 := by
  rintro ⟨v, w, h⟩
  have hm : ∀ v w : ZMod 8, v ^ 2 ≠ 291 * w ^ 2 - 5 * 17 ^ 2 := by decide
  have he := congrArg (fun z : ℤ => (z : ZMod 8)) h
  push_cast at he
  exact hm v w he

/-
Nun bilde man nach §. 17 eine p-Function, deren Nenner
den Factor 17² nicht enthalten darf.
K² = 291Δ²−17².1811(α²−291), für α = 17, K = 17k,
Δ = 17d wird k² = 291d²+3622;
-/

example : (-17 ^ 2 * 1811 * (17 ^ 2 - 291) / 17 ^ 2 : ℚ) = 3622 := by norm_num

/-
für k = 291z+r wird
d² = 291z²+2rz−12+(r²−130)/291, r = 79, 115
B = 21, 45
-/

example : ((79 ^ 2 - 130) / 291 : ℚ) = 21 := by norm_num

example : ((115 ^ 2 - 130) / 291 : ℚ) = 45 := by norm_num

/-
für r = 79 wird das Zahlenglied −12+21 = 9, somit für z = 0
d = 3, k = 79, K = ±1343, β = 17/3 und
-/

example : (-12 + 21 : ℤ) = 3 ^ 2 := by norm_num

example : (79 : ℤ) ^ 2 = 291 * 3 ^ 2 + 3622 := by norm_num

example : (17 * 79 : ℤ) = 1343 := by norm_num

example : ((1343 + 17 * 115) / (2 * 291) : ℚ) = 17 / 3 := by norm_num

/-
9y² = (51x+17)²+(6x−193)(3x−20),
-/

example (x : ℚ) : 9 * (291 * x ^ 2 + 115 * x + 461) = (51 * x + 17) ^ 2 + (6 * x - 193) * (3 * x - 20) := by ring

/- Rechenschritt: Der Nullpunkt eines angegebenen linearen Factors. -/

example : ∃ x y : ℚ, y ^ 2 = 291 * x ^ 2 + (115) * x + (461) := by
  exact ⟨20 / 3, 357 / 3, by norm_num⟩

/-
Seite 375

somit 3x = 20+17(42p+705)/(p²−291), S₁ = −17.9(1811);
-/

example (p : ℚ) : (20) + (2 * (357) * p + (2 * 291 * (20) + (115) * 3)) / (p ^ 2 - 291) = (20) + 17 * ((42) * p + (705)) / (p ^ 2 - 291) := by ring

example : (3 ^ 2 * (-17 ^ 2 * 1811) / 17 : ℚ) = -17 * 9 * 1811 := by norm_num

/-
hier können bloss die Gleichungen v² = 291w²±51 aufgestellt
werden, welche in Rationalzahlen unmöglich sind.
-/

example : Prop :=
  ∀ N : ℤ, N ∈ ([51, -51] : List ℤ) →
    ¬ ∃ v w : ℚ, v ^ 2 = 291 * w ^ 2 + N

/- Folgerung für die ursprüngliche Gleichung. -/

example : Prop :=
  ¬ ∃ x y : ℤ, y ^ 2 = 291 * x ^ 2 + 115 * x + 461

end Beispiel12

namespace Beispiel13

/-
13. Exempel:
y² = 257x²+53x+10 = (6x−2)²+(17x+2)(13x+3),
-/

example (x : ℚ) : 257 * x ^ 2 + 53 * x + 10 = (6 * x - 2) ^ 2 + (17 * x + 2) * (13 * x + 3) := by ring

/- Rechenschritt: Der Nullpunkt eines angegebenen linearen Factors. -/

example : ∃ x y : ℚ, y ^ 2 = 257 * x ^ 2 + (53) * x + (10) := by
  exact ⟨-3 / 13, -44 / 13, by norm_num⟩

/-
D = −31.241, 13x = −3+(−88p−853)/(p²−257),
S = −13².241(31);
-/

example : (53 ^ 2 - 4 * 257 * 10 : ℤ) = -31 * 241 := by norm_num

example (p : ℚ) : (-3) + (2 * (-44) * p + (2 * 257 * (-3) + (53) * 13)) / (p ^ 2 - 257) = (-3) + 1 * ((-88) * p + (-853)) / (p ^ 2 - 257) := by ring

/-
da in der VI. Reihe lauter Einser stehen, so kann nach Wegfall
von 31 der Nenner N₁ nur ±13.241 sein.
-/

example :
    let step := fun (s : ℤ × ℤ × List (ℤ × Bool)) (q : ℤ) =>
      let m := q * s.2.1 - s.1
      let d := (257 - m ^ 2) / s.2.1
      (m, d, s.2.2 ++ [(d, (257 - m ^ 2) % s.2.1 == 0)])
    (([16, 32] : List ℤ).foldl step (0, 1, [])).2.2 = [(1, true), (1, true)] := by norm_num

/- Hilfsdefinition: Ein Rechenschritt der Kettenbruchentwicklung. -/

private def tennerStep257 (s : ℤ × ℤ) : ℤ × ℤ :=
  let q := (16 + s.1) / s.2
  let m := q * s.2 - s.1
  (m, (257 - m ^ 2) / s.2)

example : (16 : ℤ) ^ 2 ≤ 257 ∧ 257 < (16 + 1) ^ 2 := by decide

/- Hilfsschritt: Fortsetzung der berechneten Kettenbruchperiode. -/

private theorem tennerState257 (k : ℕ) :
    (tennerStep257^[k + 1]) (0, 1) = (16, 1) := by
  have hstart : tennerStep257 (0, 1) = (16, 1) := by decide
  have hcycle : tennerStep257 (16, 1) = (16, 1) := by decide
  induction k with
  | zero => exact hstart
  | succ k ih => rw [Function.iterate_succ_apply', ih, hcycle]

/- Hilfsschritt: Fortsetzung der berechneten Kettenbruchperiode. -/

private theorem tennerAllStates257 (k : ℕ) :
    (tennerStep257^[k]) (0, 1) ∈
      ([(0, 1), (16, 1)] : List (ℤ × ℤ)) := by
  cases k with
  | zero => decide
  | succ k =>
    rw [tennerState257 k]
    decide

/- Hilfsdefinition: Die III. Verticalreihe der Rechnung. -/

private def tennerM257 (k : ℕ) : ℤ := ((tennerStep257^[k]) (0, 1)).1

/- Hilfsdefinition: Die VI. Verticalreihe der Rechnung. -/

private def tennerQ257 (k : ℕ) : ℤ := ((tennerStep257^[k]) (0, 1)).2

/- Hilfsdefinition: Die I. Verticalreihe der Rechnung. -/

private def tennerA257 (k : ℕ) : ℤ := (16 + tennerM257 k) / tennerQ257 k

/- Hilfsschritt: Ganzzahlige Quotienten und genaue Divisionen der Kette. -/

private theorem tennerData257 : tennerM257 0 = 0 ∧ tennerQ257 0 = 1 ∧
    (∀ k, (tennerA257 k : ℝ) ≤
        (Real.sqrt (257 : ℤ) + tennerM257 k) / tennerQ257 k ∧
      (Real.sqrt (257 : ℤ) + tennerM257 k) / tennerQ257 k < tennerA257 k + 1) ∧
    (∀ k, tennerM257 (k + 1) = tennerA257 k * tennerQ257 k - tennerM257 k) ∧
    (∀ k, tennerQ257 (k + 1) * tennerQ257 k = 257 - tennerM257 (k + 1) ^ 2) := by
  have hs : (Real.sqrt 257) ^ 2 = 257 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 257 := Real.sqrt_nonneg _
  have hlo : (16 : ℝ) ≤ Real.sqrt 257 := by nlinarith
  have hhi : Real.sqrt 257 < (17 : ℝ) := by nlinarith
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro k
    have hk := tennerAllStates257 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with hk | hk
    all_goals norm_num [tennerA257, tennerM257, tennerQ257, hk]
    all_goals constructor <;> linarith
  · intro k
    simp only [tennerM257, tennerA257, tennerQ257, Function.iterate_succ_apply']
    rfl
  · intro k
    have hk := tennerAllStates257 k
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    simp only [tennerM257, tennerQ257, Function.iterate_succ_apply']
    rcases hk with hk | hk <;> rw [hk] <;> decide

/- Hilfsschritt: Anwendung des als Voraussetzung geführten Kriteriums. -/

private theorem specializeCriterion257
    (hCriterion : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ∀ N : ℤ, N ^ 2 < 257 →
      (∀ k : ℕ, ((tennerStep257^[k + 1]) (0, 1)).2 ≠ |N|) →
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 257 * w ^ 2 + N := by
  intro N hN habsent
  obtain ⟨hM, hQ, hfloor, hMstep, hQstep⟩ := tennerData257
  have hns : ¬ ∃ q : ℤ, q ^ 2 = 257 := by
    rintro ⟨q, hq⟩
    have hs : IsSquare (257 : ℤ) := ⟨q, by nlinarith [hq]⟩
    norm_num at hs
  have hNreal : (|N| : ℤ) < Real.sqrt (257 : ℤ) := by
    have hsq : (((|N| : ℤ) : ℝ)) ^ 2 < 257 := by
      exact_mod_cast (show |N| ^ 2 < 257 by simpa only [sq_abs] using hN)
    have hs : (Real.sqrt 257) ^ 2 = 257 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt 257 := Real.sqrt_nonneg _
    norm_num only [Int.cast_ofNat]
    nlinarith
  exact hCriterion 257 N tennerA257 tennerM257 tennerQ257 (by norm_num) hns
    hM hQ hfloor hMstep hQstep hNreal habsent

example : ∀ k : ℕ, ((tennerStep257^[k + 1]) (0, 1)).2 = 1 := by
  intro k
  rw [tennerState257 k]

/- Hilfsschritt: Der Nenner der p-Function ist nicht Null. -/

private theorem notSquare257 (p : ℚ) : p ^ 2 - 257 ≠ 0 := by
  intro h
  have hs : IsSquare (257 : ℚ) := ⟨p, by nlinarith [h]⟩
  have hi : IsSquare (257 : ℤ) := Rat.isSquare_intCast_iff.mp hs
  norm_num at hi

/- Hilfsschritt: Die kleinen Nenner im vorausgesetzten Kriterium. -/

private theorem smallNorms257
    (hVI : ∀ N : ℤ, N ^ 2 < 257 →
      (∀ k : ℕ, ((tennerStep257^[k + 1]) (0, 1)).2 ≠ |N|) →
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 257 * w ^ 2 + N) :
    ∀ N ∈ ([-16, -13, -8, 8, 13, 16] : List ℤ),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 257 * w ^ 2 + N := by
  intro N hN
  apply hVI N
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro k
    rw [tennerState257 k]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-
Ist v² = aw²−1 in
ganzen Zahlen möglich, so sind die Gleichungen v² = aw²±N in
ganzen Zahlen zugleich möglich oder zugleich unmöglich.
-/

/- Hilfsschritt: Erster Näherungsbruch der bereits benützten Kette. -/

private theorem firstConvergent257 : (16 : ℤ) ^ 2 = 257 * 1 ^ 2 - 1 := by decide

/- Hilfsschritt: Anwendung der Zusammensetzung auf das Zahlenglied −1. -/

private theorem flipNorm257 (N v w : ℤ) (h : v ^ 2 = 257 * w ^ 2 + N) :
    (16 * v + 257 * w) ^ 2 = 257 * (v + 16 * w) ^ 2 - N := by
  linear_combination -h

/- Hilfsschritt: Zusammensetzung am Ende des §. 16 für die beiden Vorzeichen. -/

private theorem opposite3133 (h : ∃ v w : ℤ, v ^ 2 = 257 * w ^ 2 - 1) :
    (∃ v w : ℤ, v ^ 2 = 257 * w ^ 2 + 3133) ↔
      ∃ v w : ℤ, v ^ 2 = 257 * w ^ 2 - 3133 := by
  obtain ⟨r, s, hrs⟩ := h
  have compose (N v w : ℤ) (hv : v ^ 2 = 257 * w ^ 2 + N) :
      (v * r + 257 * w * s) ^ 2 = 257 * (v * s + w * r) ^ 2 - N := by
    linear_combination (r ^ 2 - 257 * s ^ 2) * hv + N * hrs
  constructor
  · rintro ⟨v, w, hv⟩
    exact ⟨v * r + 257 * w * s, v * s + w * r, compose 3133 v w hv⟩
  · rintro ⟨v, w, hv⟩
    refine ⟨v * r + 257 * w * s, v * s + w * r, ?_⟩
    simpa using compose (-3133) v w (by linarith [hv])

/-
Also
v² = 257w²+3133 = (15w+30)²+(8w−203)(4w−11) und
4w = 11+2(285q+2827)/(q²−257), S = −64.241.(13.257);
-/

example (w : ℚ) : 257 * w ^ 2 + 3133 = (15 * w + 30) ^ 2 + (8 * w - 203) * (4 * w - 11) := by ring

example (p : ℚ) : (11) + (2 * (285) * p + (2 * 257 * (11) + (0) * 4)) / (p ^ 2 - 257) = (11) + 2 * ((285) * p + (2827)) / (p ^ 2 - 257) := by ring

example : (4 ^ 2 * (-4 * 257 * 3133) : ℤ) = -64 * 241 * (13 * 257) := by norm_num

/-
der zu bildende Nenner N¹ muss durch 8 theilbar sein, denn
v₁² = 257w₁²+4.241 ist in theilfremden Zahlen der 8-Reste wegen
nicht möglich; N¹ darf aber kein Vielfaches von 16 sein, weil
sonst für den nächsten äquivalenten Nenner (§. 15) nur 4
verbliebe.
-/

example : ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 257 * w ^ 2 + 4 * 241 := by
  rintro ⟨v, w, hcop, h⟩
  have hv0 : 0 ≤ v % 8 := Int.emod_nonneg _ (by norm_num)
  have hw0 : 0 ≤ w % 8 := Int.emod_nonneg _ (by norm_num)
  have hv8 : v % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
  have hw8 : w % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
  have hm : (v ^ 2 - 257 * w ^ 2 - 4 * 241) % 8 = 0 := by rw [h]; norm_num
  have hm' : ((v % 8) ^ 2 - 257 * (w % 8) ^ 2 - 4 * 241) % 8 = 0 := by
    simpa only [pow_two, Int.sub_emod, Int.mul_emod, Int.emod_emod] using hm
  have hev : v % 2 = 0 ∧ w % 2 = 0 := by
    interval_cases hv : v % 8 <;> interval_cases hw : w % 8 <;>
      norm_num [hv, hw] at hm' <;> omega
  have hv : (2 : ℤ) ∣ v := Int.dvd_of_emod_eq_zero hev.1
  have hw : (2 : ℤ) ∣ w := Int.dvd_of_emod_eq_zero hev.2
  obtain ⟨s, t, hst⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hc : (2 : ℤ) ∣ 1 := by
    rw [← hst]
    exact dvd_add (dvd_mul_of_dvd_right hv _) (dvd_mul_of_dvd_right hw _)
  norm_num at hc

/- Hilfsschritt: Die geforderte Theilbarkeit durch 8. -/

private theorem eight_dvd_norm257 (v w N : ℤ) (hcop : Int.gcd v w = 1)
    (hnorm : v ^ 2 = 257 * w ^ 2 + N) (h2 : 2 ∣ N) : 8 ∣ N := by
  have table : ∀ V W M : ZMod 8,
      V ^ 2 = 257 * W ^ 2 + M → (ZMod.cast M : ZMod 2) = 0 →
      M = 0 ∨ ((ZMod.cast V : ZMod 2) = 0 ∧ (ZMod.cast W : ZMod 2) = 0) := by
    decide
  have hmod := congrArg (fun t : ℤ => (t : ZMod 8)) hnorm
  push_cast at hmod
  have h2mod : (ZMod.cast (N : ZMod 8) : ZMod 2) = 0 := by
    rw [ZMod.cast_intCast (by decide : 2 ∣ 8)]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd N 2).mpr h2
  rcases table (v : ZMod 8) (w : ZMod 8) (N : ZMod 8) hmod h2mod with h8 | heven
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd N 8).mp h8
  · rw [ZMod.cast_intCast (by decide : 2 ∣ 8), ZMod.cast_intCast (by decide : 2 ∣ 8)] at heven
    have hv : (2 : ℤ) ∣ v := (ZMod.intCast_zmod_eq_zero_iff_dvd v 2).mp heven.1
    have hw : (2 : ℤ) ∣ w := (ZMod.intCast_zmod_eq_zero_iff_dvd w 2).mp heven.2
    obtain ⟨a, b, hab⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hcop
    have hbad : (2 : ℤ) ∣ 1 := by
      rw [← hab]
      exact dvd_add (dvd_mul_of_dvd_right hv a) (dvd_mul_of_dvd_right hw b)
    norm_num at hbad

/- Hilfsdefinition: Zahlenglied aus Zähler und Nenner des Parameters. -/

private def parameterNorm257 (p : ℚ) : ℤ := p.num ^ 2 - 257 * (p.den : ℤ) ^ 2

/- Hilfsschritt: Bildung des Parameters der p-Function. -/

private theorem parameter257 (b c m n r x y : ℤ)
    (hbase : r ^ 2 = 257 * m ^ 2 + b * m * n + c * n ^ 2)
    (hroot : y ^ 2 = 257 * x ^ 2 + b * x + c) (hx : n * x - m ≠ 0) :
    ∃ p : ℚ, (n : ℚ) * x = m +
      (2 * r * p + (2 * 257 * m + b * n)) / (p ^ 2 - 257) := by
  have hxQ : (n : ℚ) * x - m ≠ 0 := by exact_mod_cast hx
  let p : ℚ := (n * (y : ℚ) + r) / (n * x - m)
  have hline : p * ((n : ℚ) * x - m) = n * y + r := by
    dsimp [p]
    exact div_mul_cancel₀ _ hxQ
  have hbQ : (r : ℚ) ^ 2 = 257 * (m : ℚ) ^ 2 + b * m * n + c * n ^ 2 := by exact_mod_cast hbase
  have hrQ : (y : ℚ) ^ 2 = 257 * (x : ℚ) ^ 2 + b * x + c := by exact_mod_cast hroot
  have hpoly : ((n : ℚ) * x - m) * (p ^ 2 - 257) =
      2 * r * p + (2 * 257 * m + b * n) := by
    apply mul_right_cancel₀ hxQ
    linear_combination (p * ((n : ℚ) * x - m) + n * y - r) * hline + n ^ 2 * hrQ - hbQ
  refine ⟨p, ?_⟩
  have he := (eq_div_iff (notSquare257 p)).2 hpoly
  linear_combination he

/- Hilfsschritt: Daten der äquivalenten Nenner. -/

private theorem pairedData257 (b c m n r α β γ δ x : ℤ) (p : ℚ)
    (hn : 0 < n) (hmn : Int.gcd m n = 1) (hx : n * x - m ≠ 0)
    (ha : 257 = α ^ 2 - n * γ) (hb : b = 2 * α * β + m * γ + n * δ)
    (hc : c = β ^ 2 - m * δ) (hr : r = m * α + n * β)
    (hX : (n : ℚ) * x = m + (2 * r * p + (2 * 257 * m + b * n)) / (p ^ 2 - 257)) :
    ∃ q : ℚ, ∃ ρ : ℤ,
      (n : ℚ) * x = m + (2 * r * q + (2 * 257 * m + b * n)) / (q ^ 2 - 257) ∧
      n ∣ parameterNorm257 q ∧
      parameterNorm257 p * parameterNorm257 q * ρ ^ 2 = n ^ 2 * (b ^ 2 - 4 * 257 * c) := by
  have hxQ : (n : ℚ) * x - m ≠ 0 := by exact_mod_cast hx
  have hpoly : ((n : ℚ) * x - m) * (p ^ 2 - 257) = 2 * r * p + (2 * 257 * m + b * n) := by
    apply (eq_div_iff (notSquare257 p)).mp
    linear_combination hX
  have hden : 2 * (r : ℚ) * p + (2 * 257 * m + b * n) ≠ 0 := by
    rw [← hpoly]
    exact mul_ne_zero hxQ (notSquare257 p)
  let q : ℚ := -(((2 * 257 * m + b * n : ℤ) : ℚ) * p + 2 * 257 * r) /
    (2 * r * p + (2 * 257 * m + b * n))
  have heq : q * (2 * (r : ℚ) * p + (2 * 257 * m + b * n)) =
      -((2 * 257 * m + b * n) * p + 2 * 257 * r) := by
    dsimp [q]
    push_cast
    simpa only [show (2 : ℚ) * 257 = 514 by norm_num] using
      (div_mul_cancel₀ (-((2 * 257 * (m : ℚ) + b * n) * p + 2 * 257 * r)) hden)
  have hsame : (m : ℚ) + (2 * r * q + (2 * 257 * m + b * n)) / (q ^ 2 - 257) =
      m + (2 * r * p + (2 * 257 * m + b * n)) / (p ^ 2 - 257) := by
    field_simp [notSquare257 p, notSquare257 q]
    linear_combination (p - q) * heq
  have hXq : (n : ℚ) * x = m + (2 * r * q + (2 * 257 * m + b * n)) / (q ^ 2 - 257) := by
    rw [hsame]
    exact hX
  have hbase : r ^ 2 = 257 * m ^ 2 + b * m * n + c * n ^ 2 := by
    rw [ha, hb, hc, hr]
    ring
  have hpair := Kunerth1880.Paragraf13.pairedNorms 257 b c m n r x p hn hmn hbase
    (notSquare257 p) hden hX
  dsimp only at hpair
  obtain ⟨ρ, _hρ, _hcop, hpair⟩ := hpair (notSquare257 _)
  refine ⟨q, ρ, hXq, ?_, ?_⟩
  · exact (Kunerth1880.Paragraf07.normData 257 b c m n r α β γ δ x q
      (ne_of_gt hn) hmn ha hb hc hr (notSquare257 q) hXq).1
  · simpa only [parameterNorm257, q, Int.cast_ofNat] using hpair

/- Hilfsschritt: Auswahl des äquivalenten Parameters. -/

private theorem selectAux257
    (hSelection : Kunerth1880.Paragraf16.singularPrimeSelection)
    (c m n r α β γ δ t x y : ℤ)
    (hn : 0 < n) (hmn : Int.gcd m n = 1) (hnm : ¬ n ∣ m)
    (ha : 257 = α ^ 2 - n * γ) (hb : 0 = 2 * α * β + m * γ + n * δ)
    (hc : c = β ^ 2 - m * δ) (hr : r = m * α + n * β)
    (ht : Prime t) (htc : t ∣ c)
    (hs257 : ¬ (257 : ℤ) ^ 2 ∣ -4 * 257 * c) (hst : ¬ t ^ 2 ∣ -4 * 257 * c)
    (hroot : y ^ 2 = 257 * x ^ 2 + c) :
    ∃ q : ℚ, ∃ z : ℤ,
      (n : ℚ) * z = m + (2 * r * q + 2 * 257 * m) / (q ^ 2 - 257) ∧
      n ∣ parameterNorm257 q ∧ ¬ 257 ∣ parameterNorm257 q ∧ ¬ t ∣ parameterNorm257 q := by
  have hbase : r ^ 2 = 257 * m ^ 2 + c * n ^ 2 := by
    rw [ha, hc, hr]
    linear_combination -m * n * hb
  have hx : n * x - m ≠ 0 := by
    intro h
    exact hnm ⟨x, by linear_combination -h⟩
  obtain ⟨p, hX⟩ := parameter257 0 c m n r x y (by simpa using hbase) (by simpa using hroot) hx
  simp only [Int.cast_zero, zero_mul, add_zero] at hX
  have hxQ : (n : ℚ) * x - m ≠ 0 := by exact_mod_cast hx
  have hpoly : ((n : ℚ) * x - m) * (p ^ 2 - 257) = 2 * r * p + 2 * 257 * m := by
    apply (eq_div_iff (notSquare257 p)).mp
    linear_combination hX
  have hleft : (n : ℚ) * x ≠ -(m : ℚ) := by
    intro he
    have heI : n * x = -m := by exact_mod_cast he
    exact hnm ⟨-x, by linear_combination heI⟩
  have hp0 : p ≠ 0 := by
    intro he
    rw [he] at hpoly
    apply hleft
    linear_combination (-1 / 257 : ℚ) * hpoly
  have hden1 : (r : ℚ) * p + 257 * m ≠ 0 := by
    intro he
    have hz : ((n : ℚ) * x - m) * (p ^ 2 - 257) = 0 := by linear_combination hpoly + 2 * he
    exact mul_ne_zero hxQ (notSquare257 p) hz
  have hden2 : (m : ℚ) * p + r ≠ 0 := by
    intro he
    have hz : ((n : ℚ) * x + m) * (p ^ 2 - 257) = 0 := by linear_combination hpoly + 2 * p * he
    have hzero := (mul_eq_zero.mp hz).resolve_right (notSquare257 p)
    apply hleft
    linear_combination hzero
  obtain ⟨k, hk⟩ := Kunerth1880.Paragraf07.preparationFromVIII 257 0 m n r α β γ δ x p
    (ne_of_gt hn) hmn ha hb hr (notSquare257 p) (by simpa using hX)
  have hprep : p.num = n * k - α * (p.den : ℤ) := by linear_combination hk
  have hsel := hSelection 257 c m n r x α β γ k 257 t p
    hn hmn hbase hr (by linear_combination -ha) hprep hp0 (notSquare257 p) hden1 hden2
    (by linear_combination hX) (by norm_num) ht (by norm_num) htc hs257 hst
  dsimp only at hsel
  obtain ⟨q, _hchoices, _hq, ⟨z, hZ⟩, hN, h257, htN⟩ :=
    hsel (notSquare257 _) (notSquare257 _) (notSquare257 _)
  refine ⟨q, z, ?_, hN, h257, htN⟩
  linear_combination hZ

/- Hilfsschritt: Theilfremdheit der Bruchglieder. -/

private theorem normFacts257 (p : ℚ) :
    Int.gcd p.num (p.den : ℤ) = 1 ∧
      p.num ^ 2 = 257 * (p.den : ℤ) ^ 2 + parameterNorm257 p := by
  constructor
  · simpa [Int.gcd] using p.reduced
  · dsimp [parameterNorm257]
    ring

/- Hilfsschritt: Divisoren des verbliebenen Factors 241. -/

private theorem divisors241 (t : ℤ) (ht : t ∣ 241) :
    t = 1 ∨ t = -1 ∨ t = 241 ∨ t = -241 := by
  have hNat : t.natAbs ∣ 241 := by simpa using Int.natAbs_dvd_natAbs.mpr ht
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 241)).mp hNat with h | h
  · rcases Int.natAbs_eq_iff.mp h with ht | ht <;> simp_all
  · rcases Int.natAbs_eq_iff.mp h with ht | ht <;> simp_all

/- Hilfsschritt: Theilbarkeit durch 8, aber nicht durch 16. -/

private theorem cases1928 (N : ℤ) (hdiv : N ∣ 64 * 241) (h8 : 8 ∣ N) (h16 : ¬ 16 ∣ N) :
    N = 8 ∨ N = -8 ∨ N = 8 * 241 ∨ N = -(8 * 241) := by
  obtain ⟨t, ht⟩ := h8
  obtain ⟨u, hu⟩ := hdiv
  have htD : t ∣ 8 * 241 := by
    refine ⟨u, ?_⟩
    apply mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0)
    rw [ht] at hu
    linear_combination hu
  have ht2 : ¬ 2 ∣ t := by
    rintro ⟨v, hv⟩
    apply h16
    exact ⟨v, by rw [ht, hv]; ring⟩
  have hcop2 : IsCoprime t 2 := ((show Prime (2 : ℤ) by norm_num).coprime_iff_not_dvd.mpr ht2).symm
  have hcop8 : IsCoprime t 8 := by simpa using hcop2.pow_right (n := 3)
  have ht241 : t ∣ 241 := hcop8.dvd_of_dvd_mul_left htD
  rcases divisors241 t ht241 with h | h | h | h <;> norm_num [ht, h]

/-
Somit
v₁² = 257w₁²+8.241 = (15w₁+16)²+8(2w₁−19)(2w₁−11) und
2w₁ = 11+2(197r+2827)/(r²−257), S = −128(241.257);
-/

example (w : ℚ) : 257 * w ^ 2 + 8 * 241 = (15 * w + 16) ^ 2 + 8 * (2 * w - 19) * (2 * w - 11) := by ring

example (p : ℚ) : (11) + (2 * (197) * p + (2 * 257 * (11) + (0) * 2)) / (p ^ 2 - 257) = (11) + 2 * ((197) * p + (2827)) / (p ^ 2 - 257) := by ring

example : (2 ^ 2 * (-4 * 257 * (8 * 241)) : ℤ) = -128 * (241 * 257) := by norm_num

/-
da die eingeklammerten Zahlen ausser Betracht kommen, und
für den nächsten äquivalenten Nenner 8 zu reserviren ist, so
bleiben für den ersten Nenner bloss 8 oder 16 übrig, mit denen
keine in relativen Primzahlen auflösliche Gleichung gebildet
werden kann.
-/

/- Hilfsschritt: Ausschluss der Gleichung mit dem Zahlenglied 8.241. -/

private theorem no1928
    (hSelection : Kunerth1880.Paragraf16.singularPrimeSelection)
    (hsmall : ∀ N ∈ ([-16, -13, -8, 8, 13, 16] : List ℤ),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 257 * w ^ 2 + N) :
    ¬ ∃ x y : ℤ, y ^ 2 = 257 * x ^ 2 + 8 * 241 := by
  rintro ⟨x, y, hroot⟩
  obtain ⟨p, z, hX, h2, h257, h241⟩ :=
    selectAux257 hSelection (8 * 241) 11 2 197 15 16 (-16) (-152) 241 x y
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hroot
  obtain ⟨q, ρ, _hXq, h2q, hpair⟩ :=
    pairedData257 0 (8 * 241) 11 2 197 15 16 (-16) (-152) z p
      (by norm_num) (by norm_num) (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by simpa using hX)
  let N := parameterNorm257 p
  let M := parameterNorm257 q
  obtain ⟨hcopN, hnormN⟩ := normFacts257 p
  obtain ⟨hcopM, hnormM⟩ := normFacts257 q
  have h8N : 8 ∣ N := eight_dvd_norm257 _ _ _ hcopN hnormN h2
  have h8M : 8 ∣ M := eight_dvd_norm257 _ _ _ hcopM hnormM h2q
  have hpair' : N * M * ρ ^ 2 = -128 * 241 * 257 := by
    dsimp [N, M]
    norm_num at hpair ⊢
    exact hpair
  have hnot32 : ¬ 32 ∣ N := by
    intro h32
    have h256 : (256 : ℤ) ∣ N * M * ρ ^ 2 :=
      dvd_mul_of_dvd_left (by simpa using mul_dvd_mul h32 h8M) (ρ ^ 2)
    rw [hpair'] at h256
    norm_num at h256
  have hstock : N ∣ 128 * 241 * 257 := by
    refine ⟨-(M * ρ ^ 2), ?_⟩
    linear_combination hpair'
  have hcop257 : IsCoprime N 257 := ((show Prime (257 : ℤ) by norm_num).coprime_iff_not_dvd.mpr h257).symm
  have hcop241 : IsCoprime N 241 := ((show Prime (241 : ℤ) by norm_num).coprime_iff_not_dvd.mpr h241).symm
  have hdiv : N ∣ 128 := by
    apply (hcop241.mul_right hcop257).dvd_of_dvd_mul_right
    simpa [mul_assoc] using hstock
  obtain ⟨t, ht⟩ := h8N
  have hdt : t ∣ 16 := by
    obtain ⟨u, hu⟩ := hdiv
    refine ⟨u, ?_⟩
    apply mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0)
    rw [ht] at hu
    linear_combination hu
  have hnot4 : ¬ 4 ∣ t := by
    rintro ⟨u, hu⟩
    apply hnot32
    exact ⟨u, by rw [ht, hu]; ring⟩
  have hbound : |t| ≤ 16 := by
    have hn : (t.natAbs : ℤ) ∣ 16 := by simpa using hdt
    simpa using Int.le_of_dvd (by norm_num : (0 : ℤ) < 16) hn
  have htcase : t ∈ ([-2, -1, 1, 2] : List ℤ) := by
    have table : ∀ k : Fin 33, ((k.val : ℤ) - 16) ∣ 16 →
        ¬ 4 ∣ (k.val : ℤ) - 16 →
        (k.val : ℤ) - 16 ∈ ([-2, -1, 1, 2] : List ℤ) := by decide
    obtain ⟨hlo, hhi⟩ := abs_le.mp hbound
    let k : Fin 33 := ⟨(t + 16).toNat, by omega⟩
    have hk : (k.val : ℤ) - 16 = t := by dsimp [k]; omega
    have h := table k
    rw [hk] at h
    exact h hdt hnot4
  have hcases : N ∈ ([-16, -8, 8, 16] : List ℤ) := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at htcase
    rcases htcase with h | h | h | h <;> norm_num [ht, h]
  apply hsmall N ?_ ⟨p.num, p.den, hcopN, hnormN⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcases
  rcases hcases with h | h | h | h <;> simp [h]

/- Hilfsschritt: Rückgang zur Gleichung mit dem Zahlenglied 3133. -/

private theorem no3133
    (hSelection : Kunerth1880.Paragraf16.singularPrimeSelection)
    (hsmall : ∀ N ∈ ([-16, -13, -8, 8, 13, 16] : List ℤ),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 257 * w ^ 2 + N) :
    ¬ ∃ x y : ℤ, y ^ 2 = 257 * x ^ 2 + 3133 := by
  rintro ⟨x, y, hroot⟩
  obtain ⟨p, z, hX, h4, h257, h13⟩ :=
    selectAux257 hSelection 3133 11 4 285 15 30 (-8) (-203) 13 x y
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hroot
  obtain ⟨q, ρ, _hXq, h4q, hpair⟩ :=
    pairedData257 0 3133 11 4 285 15 30 (-8) (-203) z p
      (by norm_num) (by norm_num) (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by simpa using hX)
  let N := parameterNorm257 p
  let M := parameterNorm257 q
  obtain ⟨hcopN, hnormN⟩ := normFacts257 p
  obtain ⟨hcopM, hnormM⟩ := normFacts257 q
  have h8N : 8 ∣ N := eight_dvd_norm257 _ _ _ hcopN hnormN (dvd_trans (by norm_num : (2 : ℤ) ∣ 4) h4)
  have h8M : 8 ∣ M := eight_dvd_norm257 _ _ _ hcopM hnormM (dvd_trans (by norm_num : (2 : ℤ) ∣ 4) h4q)
  have hpair' : N * M * ρ ^ 2 = -64 * 241 * 13 * 257 := by
    dsimp [N, M]
    norm_num at hpair ⊢
    exact hpair
  have hnot16 : ¬ 16 ∣ N := by
    intro h16
    have h128 : (128 : ℤ) ∣ N * M * ρ ^ 2 :=
      dvd_mul_of_dvd_left (by simpa using mul_dvd_mul h16 h8M) (ρ ^ 2)
    rw [hpair'] at h128
    norm_num at h128
  have hstock : N ∣ 64 * 241 * 13 * 257 := by
    refine ⟨-(M * ρ ^ 2), ?_⟩
    linear_combination hpair'
  have hcop257 : IsCoprime N 257 := ((show Prime (257 : ℤ) by norm_num).coprime_iff_not_dvd.mpr h257).symm
  have hcop13 : IsCoprime N 13 := ((show Prime (13 : ℤ) by norm_num).coprime_iff_not_dvd.mpr h13).symm
  have hdiv : N ∣ 64 * 241 := by
    apply (hcop13.mul_right hcop257).dvd_of_dvd_mul_right
    simpa [mul_assoc] using hstock
  change p.num ^ 2 = 257 * (p.den : ℤ) ^ 2 + N at hnormN
  rcases cases1928 N hdiv h8N hnot16 with h | h | h | h
  · exact hsmall N (by simp [h]) ⟨p.num, p.den, hcopN, hnormN⟩
  · exact hsmall N (by simp [h]) ⟨p.num, p.den, hcopN, hnormN⟩
  · exact no1928 hSelection hsmall ⟨p.den, p.num, by simpa only [h] using hnormN⟩
  · have hflip := flipNorm257 N p.num (p.den : ℤ) hnormN
    apply no1928 hSelection hsmall
    exact ⟨p.num + 16 * (p.den : ℤ), 16 * p.num + 257 * (p.den : ℤ), by simpa [h] using hflip⟩

/- Folgerung mit dem als Voraussetzung geführten Kriterium des §. 23. -/

example
    (hCriterion : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ∀ N ∈ ([8, 16] : List ℤ),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 257 * w ^ 2 + N := by
  intro N hN
  apply smallNorms257 (specializeCriterion257 hCriterion) N
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
  rcases hN with h | h <;> simp [h]

/-
Die erste Gleichung ist somit in ganzen Zahlen
unmöglich.
-/

/- Hilfsschritt: Rückgang zur ersten Gleichung. -/

private theorem initialNoSolution257
    (hSelection : Kunerth1880.Paragraf16.singularPrimeSelection)
    (hsmall : ∀ N ∈ ([-16, -13, -8, 8, 13, 16] : List ℤ),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = 257 * w ^ 2 + N) :
    ¬ ∃ x y : ℤ, y ^ 2 = 257 * x ^ 2 + 53 * x + 10 := by
  rintro ⟨x, y, hroot⟩
  have hx : 13 * x - (-3) ≠ 0 := by omega
  obtain ⟨p, hX⟩ := parameter257 53 10 (-3) 13 (-44) x y (by norm_num) hroot hx
  obtain ⟨q, ρ, hXq, _hnq, hpair⟩ :=
    pairedData257 53 10 (-3) 13 (-44) 6 (-2) (-17) 2 x p
      (by norm_num) (by norm_num) hx (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hX
  have data (s : ℚ)
      (hS : (13 : ℚ) * x = -3 + (2 * (-44) * s + (2 * 257 * (-3) + 53 * 13)) / (s ^ 2 - 257)) :
      13 ∣ parameterNorm257 s ∧ parameterNorm257 s ∣ -(13 * 31 * 241) := by
    have h := Kunerth1880.Paragraf07.normData 257 53 10 (-3) 13 (-44) 6 (-2) (-17) 2 x s
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (notSquare257 s) (by norm_num at hS ⊢; exact hS)
    dsimp [parameterNorm257]
    norm_num at h ⊢
    exact h
  have hpdata := data p (by norm_num at hX ⊢; exact hX)
  have hqdata := data q (by norm_num at hXq ⊢; exact hXq)
  have hpair' : parameterNorm257 p * parameterNorm257 q * ρ ^ 2 = -(13 ^ 2 * 31 * 241) := by
    norm_num at hpair ⊢
    exact hpair
  obtain ⟨s, h13, hstock, h31⟩ : ∃ s : ℚ,
      13 ∣ parameterNorm257 s ∧ parameterNorm257 s ∣ -(13 * 31 * 241) ∧
        ¬ 31 ∣ parameterNorm257 s := by
    by_cases hp31 : 31 ∣ parameterNorm257 p
    · refine ⟨q, hqdata.1, hqdata.2, ?_⟩
      intro hq31
      have hd : (31 : ℤ) ^ 2 ∣ parameterNorm257 p * parameterNorm257 q * ρ ^ 2 :=
        dvd_mul_of_dvd_left (by simpa [pow_two] using mul_dvd_mul hp31 hq31) (ρ ^ 2)
      rw [hpair'] at hd
      norm_num at hd
    · exact ⟨p, hpdata.1, hpdata.2, hp31⟩
  let N := parameterNorm257 s
  obtain ⟨hcopN, hnormN⟩ := normFacts257 s
  have hcop31 : IsCoprime N 31 := ((show Prime (31 : ℤ) by norm_num).coprime_iff_not_dvd.mpr h31).symm
  have hdiv : N ∣ 13 * 241 := by
    apply hcop31.dvd_of_dvd_mul_right
    convert (dvd_neg.mp hstock) using 1
    ring
  obtain ⟨t, ht⟩ := h13
  have ht241 : t ∣ 241 := by
    obtain ⟨u, hu⟩ := hdiv
    refine ⟨u, ?_⟩
    apply mul_left_cancel₀ (by norm_num : (13 : ℤ) ≠ 0)
    change N = 13 * t at ht
    rw [ht] at hu
    linear_combination hu
  have hcases : N = 13 ∨ N = -13 ∨ N = 3133 ∨ N = -3133 := by
    change N = 13 * t at ht
    rcases divisors241 t ht241 with h | h | h | h <;> norm_num [ht, h]
  change s.num ^ 2 = 257 * (s.den : ℤ) ^ 2 + N at hnormN
  rcases hcases with h | h | h | h
  · exact hsmall N (by simp [h]) ⟨s.num, s.den, hcopN, hnormN⟩
  · exact hsmall N (by simp [h]) ⟨s.num, s.den, hcopN, hnormN⟩
  · exact no3133 hSelection hsmall ⟨s.den, s.num, by simpa only [h] using hnormN⟩
  · have hneg : ∃ v w : ℤ, v ^ 2 = 257 * w ^ 2 - 3133 :=
      ⟨s.num, s.den, by simpa [h, sub_eq_add_neg] using hnormN⟩
    obtain ⟨v, w, hvw⟩ := (opposite3133 ⟨16, 1, firstConvergent257⟩).mpr hneg
    exact no3133 hSelection hsmall ⟨w, v, hvw⟩

/- Folgerung mit den als Voraussetzungen geführten Aussagen aus §. 16
und §. 23. -/

example
    (hSelection : Kunerth1880.Paragraf16.singularPrimeSelection)
    (hCriterion : ∀ (a N : ℤ) (A M Q : ℕ → ℤ)
      (_ha : 0 < a) (_hns : ¬ ∃ q : ℤ, q ^ 2 = a)
      (_hM : M 0 = 0) (_hQ : Q 0 = 1)
      (_hfloor : ∀ k, (A k : ℝ) ≤ (Real.sqrt a + M k) / Q k ∧
        (Real.sqrt a + M k) / Q k < A k + 1)
      (_hMstep : ∀ k, M (k + 1) = A k * Q k - M k)
      (_hQstep : ∀ k, Q (k + 1) * Q k = a - M (k + 1) ^ 2)
      (_hN : (|N| : ℤ) < Real.sqrt a)
      (_habsent : ∀ k, Q (k + 1) ≠ |N|),
      ¬ ∃ v w : ℤ, Int.gcd v w = 1 ∧ v ^ 2 = a * w ^ 2 + N) :
    ¬ ∃ x y : ℤ, y ^ 2 = 257 * x ^ 2 + 53 * x + 10 := by
  exact initialNoSolution257 hSelection (smallNorms257 (specializeCriterion257 hCriterion))

end Beispiel13

/-
Die im theoretischen Theile dieses Schriftchens entwickelten
Sätze, ermöglichen sonach eine rasche Auflösung unbestimmter
quadratischer Gleichungen mit zwei Unbekannten in ganzen Zahlen,
wie auch die Ermittlung von Kriterien für die Unmöglichkeit einer
solchen Lösung.
-/

end Kunerth1880.Paragraf25
