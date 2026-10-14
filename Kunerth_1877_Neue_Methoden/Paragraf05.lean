/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf05

/-
Seite 23
-/

/-
§. 5.

Auflösung von Congruenzen für einen zusammengesetzten Modulus.

y² ≡ 109 (mod. 420) oder y² = 420x+109; für x = 1 wird y = 23,
also y² = 420(x−1)+529 = [p(x−1)−23]², hieraus

x = 1+2(23p+210)/p²
-/

#guard (23 : ℤ)^2 = 420 * 1 + 109

example (x p : ℚ) :
    (p * (x - 1) - 23) ^ 2 - (420 * (x - 1) + 529) =
      (x - 1) * (p ^ 2 * (x - 1) - 46 * p - 420) := by ring

/-
und für p = 2q

x = 1+(23q+105)/q², S = 105²,
-/

def x (q : ℚ) : ℚ := 1 + (23 * q + 105) / q ^ 2

example (p : ℚ) (hp : p ≠ 0) :
    1 + 2 * (23 * (2 * p) + 210) / (2 * p) ^ 2 = x p := by
  unfold x
  field_simp
  ring

#guard (105 : ℕ)^2 = 11025

/-
somit

q = ±(1, 3, 5, 7, ....).

Die Anzahl der incongruenten Wurzeln innerhalb der ersten Periode ist
hier 2⁴ = 16; man setze

q = 1/n, = 3/n, = 5/n, = 7/n
-/

#guard (2 : ℕ)^4 = 16

/-
Seite 24

und ertheile dem Nenner n die zwei kleinsten positiven und negativen
Werthe, welche obige q-Function in eine ganze Zahl verwandeln; so wird
für q = 5/n

x = 1+[(23+21n)/5]·n;
-/

example (n : ℚ) (hn : n ≠ 0) :
    x (5/n) = 1 + (23 + 21*n)/5*n := by
  unfold x
  field_simp
  ring

/-
für n =   2     7    −3    −8
wird
    x =  27   239    25   233
    y = 107   317   103   313.
-/

#guard ([2,7,-3,-8] : List ℚ).map (fun n => x (5/n)) = [27,239,25,233]

#guard ([27,239,25,233] : List ℤ).map (fun n => 420*n+109) =
  ([107,317,103,313] : List ℤ).map (fun y => y^2)

/-
Ebenso findet man für jeden der drei anderen Werthe von q vier
Wurzeln, welche hier in natürlicher Ordnung folgen:

y = 23, 37, 47, 103, 107, 163, 173, 187, 233, 247, 257, 313,
317, 373, 383, 397.
-/

#guard (List.range 420).filter (fun y => y^2 % 420 == 109) =
  [23,37,47,103,107,163,173,187,233,247,257,313,317,373,383,397]

/-
Hat der Modul weniger Factoren, so genügt es für n blos den kleinsten
positiven und den kleinsten negativen Werth zu setzen.
-/

end Kunerth1877.Paragraf05
