/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf10

/-
Seite 350
§. 10.

Bezüglich des Nenners v₁² − a₁w² ist Folgendes zu merken:
Während v² − aw² mindestens durch die höchste Potenz jeder in
n vorkommenden Primzahl μ₁ theilbar sein muss, ist v₁² − a₁w² an
den Factor μ₁ gebunden, wenn die ganze Zahl n/μ₁² oder wenn d

Seite 351

und f durch μ₁ theilbar sind. Ist nämlich n = μ₁³n₁, so bleibt im
Quotienten (v² − aw²)/μ₁², dessen Dividend ein nfaches ist, μ₁ zurück,
und demzufolge auch in v₁² − a₁w²;
-/

example (a a₁ n n₁ μ₁ v v₁ w : ℤ) (_hprime : Prime μ₁)
    (ha : a = μ₁ ^ 2 * a₁) (hv : v = μ₁ * v₁)
    (hn : n = μ₁ ^ 3 * n₁) (hN : n ∣ v ^ 2 - a * w ^ 2)
    (hμ : μ₁ ≠ 0) : μ₁ ∣ v₁ ^ 2 - a₁ * w ^ 2 := by
  rcases hN with ⟨t, ht⟩
  refine ⟨n₁ * t, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hμ)
  rw [ha, hv, hn] at ht
  linear_combination ht

/-
kommt aber μ₁ in d und f vor, so muss, weil n prim gegen m ist,
der Factor μ₁ hinausfallen, wenn die rechte Seite in [2] eine
ganze Zahl werden soll.
-/

example (a₁ d f m n v₁ w x μ₁ : ℤ)
    (hprime : Prime μ₁) (hμn : μ₁ ∣ n) (hmn : Int.gcd m n = 1)
    (hX : (n * x - m) * (v₁ ^ 2 - a₁ * w ^ 2) = (d * v₁ + f * w) * w)
    (hd : μ₁ ∣ d) (hf : μ₁ ∣ f) :
    μ₁ ∣ v₁ ^ 2 - a₁ * w ^ 2 := by
  have hprod : μ₁ ∣ (n * x - m) * (v₁ ^ 2 - a₁ * w ^ 2) := by
    rw [hX]
    exact dvd_mul_of_dvd_left (dvd_add (dvd_mul_of_dvd_left hd v₁)
      (dvd_mul_of_dvd_left hf w)) w
  rcases hprime.dvd_mul.mp hprod with hs | hN
  · have hm : μ₁ ∣ m := by
      convert dvd_sub (dvd_mul_of_dvd_left hμn x) hs using 1
      ring
    have hb := Int.gcd_eq_gcd_ab m n
    rw [hmn] at hb
    have h : μ₁ ∣ (1 : ℤ) := by
      rw [show (1 : ℤ) = m * Int.gcdA m n + n * Int.gcdB m n from hb]
      exact dvd_add (dvd_mul_of_dvd_left hm _) (dvd_mul_of_dvd_left hμn _)
    exact False.elim (hprime.not_dvd_one h)
  · exact hN

/-
Findet jedoch keiner dieser zwei Fälle statt, und enthielte S,, selbst
eine wirkliche Potenz von μ₁, so kann v₁² − a₁w² an μ₁ gebunden
sein oder nicht, daher in diesem Falle die Rechnung alternirend
zu führen ist. Kommt μ₁ in S,, gar nicht, oder nicht potenzirt vor,
so muss, beziehungsweise kann es in v₁² − a₁w² fehlen (§. 14).
-/

example (μ₁ S N : ℤ) (_hprime : Prime μ₁) (hN : N ∣ S) (habsent : ¬ μ₁ ∣ S) : ¬ μ₁ ∣ N := by
  exact fun h => habsent (dvd_trans h hN)

end Kunerth1880.Paragraf10
