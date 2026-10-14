/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf08

/-
Seite 349
§. 8.

Ist 2r = dh und 2am + bn = fh, und man dividirt XI
durchgehends mit h, so wird im ersten Bruche der Zähler gleich

S/h = S₁ = h(−ad² + f²) ... die reducirte Stammzahl, und

nx = m + h(dv + fw)w/(v² − aw²) ... [1];

dies ist die Formel X nach dem Herausheben des grössten
gemeinen Factors h im Zähler.
-/

example (a d f h v w m : ℚ) (_hN : v ^ 2 - a * w ^ 2 ≠ 0) :
    m + ((d * h * v + f * h * w) / (v ^ 2 - a * w ^ 2)) * w =
      m + h * ((d * v + f * w) / (v ^ 2 - a * w ^ 2)) * w := by
  ring

example (a d f h : ℚ) :
    -a * (d * h) ^ 2 + (f * h) ^ 2 = h ^ 2 * (-a * d ^ 2 + f ^ 2) := by
  ring

/-
Ist dabei h₁ das grösste gemeinschaftliche Mass von n (= h₁n₁)
und h (= h₁ρ), so wird durch obige Division mit h der Zähler des
zweiten Bruches gleich

(n/h₁) · [n(b² − 4ac)/ρ].

und wenn wir die Determinante b² − 4ac mit D bezeichnen, so
wird nD/ρ ein Dividuum von v² − aw²;
-/

example (N w n D ρ q L : ℤ) (_hρ : ρ ≠ 0) (hcop : IsCoprime N (w ^ 3))
    (hdiv : n * D = ρ * q) (hXI : N * L = -q * w ^ 3) : ρ * N ∣ n * D := by
  have hd : N ∣ q := hcop.dvd_of_dvd_mul_left ⟨-L, by linear_combination hXI⟩
  rcases hd with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [hdiv, ht]
  ring

/-
da aber der Zähler des

Seite 350

ersten Bruches in XI durch h² (= h₁²ρ²) theilbar ist, so ist es auch
der zweite Zähler (= h₁²n₁²D), und weil n₁² und ρ² relative
Primzahlen sind, so muss D durch ρ² theilbar sein.
-/

example (h₁ n₁ ρ D a d f : ℤ) (hh₁ : h₁ ≠ 0) (_hρ : ρ ≠ 0)
    (hcop : Int.gcd ρ n₁ = 1)
    (hS : (h₁ * ρ) ^ 2 * (-a * d ^ 2 + f ^ 2) = (h₁ * n₁) ^ 2 * D) :
    ρ ^ 2 ∣ D := by
  have he : h₁ ^ 2 * (ρ ^ 2 * (-a * d ^ 2 + f ^ 2)) = h₁ ^ 2 * (n₁ ^ 2 * D) := by
    linear_combination hS
  have he' := mul_left_cancel₀ (pow_ne_zero 2 hh₁) he
  apply ((Int.isCoprime_iff_gcd_eq_one.mpr hcop).pow_left.pow_right).dvd_of_dvd_mul_left
  exact ⟨-a * d ^ 2 + f ^ 2, he'.symm⟩

/-
Der Factor ρ (= h/h₁) kann somit in D gelöscht werden; dadurch
wird die Anzahl der etwa möglichen Factoren von v² − aw² vermindert
und die Rechnung abgekürzt. Der Nenner N darf nur solche
Factoren enthalten, von denen a ein quadratischer Rest ist, da
sonst die Gleichung v² = aw² + N in ganzen und theilfremden
Zahlen nicht möglich wäre.
-/

example (a v w N q : ℤ) (hvw : Int.gcd v w = 1)
    (hN : v ^ 2 = a * w ^ 2 + N) (hq : q ∣ N) :
    ∃ t : ℤ, q ∣ t ^ 2 - a := by
  have hNw : IsCoprime N w := by
    obtain ⟨s, t, hst⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hvw
    refine ⟨s ^ 2, a * w * s ^ 2 + 2 * s * t * v + t ^ 2 * w, ?_⟩
    calc
      _ = (s * v + t * w) ^ 2 := by linear_combination -(s ^ 2) * hN
      _ = 1 := by rw [hst]; norm_num
  obtain ⟨k, hk⟩ := hq
  have hqw : IsCoprime q w := by
    obtain ⟨u, z, huz⟩ := hNw
    refine ⟨u * k, z, ?_⟩
    rw [hk] at huz
    linear_combination huz
  obtain ⟨u, z, huz⟩ := hqw
  refine ⟨z * v, k * z ^ 2 - a * u * (z * w + 1), ?_⟩
  linear_combination z ^ 2 * hN + z ^ 2 * hk + a * (z * w + 1) * huz

end Kunerth1880.Paragraf08
