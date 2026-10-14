/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf12

/-
Seite 351
§. 12.

Im Allgemeinen gibt es für jeden beliebigen Werth von p₁
einen zugehörigen zweiten Werth pⅡ, welcher in der Formel

Seite 352

nx = m + [2rp₁ + (2am + bn)]/(p₁² − a) ... VIII

für x dieselbe Zahl hervorbringt, wie pⅠ. Um pⅡ zu finden,
schreiben wir in VIII s für nx − m, g für 2am + bn und lösen die
Gleichung

s = (2rp₁ + g)/(p₁² − a) ... [5],

oder geordnet:

p₁² − (2r/s)p₁ − (as + g)/s = 0 ... [6]
-/

example (a r g s p : ℚ) (hs : s ≠ 0)
    (heq : s * (p ^ 2 - a) = 2 * r * p + g) :
    p ^ 2 - (2 * r / s) * p - (a * s + g) / s = 0 := by
  field_simp [hs]
  linear_combination heq

/-
nach p₁ auf; also

p₁ = [r ± √(as² + gs + r²)]/s;

führen wir für s den obigen Bruch wieder ein und radiciren, so
wird

p₁ = [rp₁² − ar ± (rp₁² + gp₁ + ar)]/(2rp₁ + g),
-/

example (a r g p : ℚ) :
    a * (2 * r * p + g) ^ 2 + g * (2 * r * p + g) * (p ^ 2 - a) +
      r ^ 2 * (p ^ 2 - a) ^ 2 = (r * p ^ 2 + g * p + a * r) ^ 2 := by
  ring

/-
somit

pⅠ = p₁ = vⅠ/wⅠ und
pⅡ = −[(2am + bn)p₁ + 2ar]/[2rp₁ + (2am + bn)] = vⅡ/wⅡ;
-/

example (a r g p : ℚ) (hg : 2 * r * p + g ≠ 0) :
    (r * p ^ 2 - a * r + (r * p ^ 2 + g * p + a * r)) / (2 * r * p + g) = p := by
  apply (div_eq_iff hg).2
  ring

example (a r g p : ℚ) (_hg : 2 * r * p + g ≠ 0) :
    (r * p ^ 2 - a * r - (r * p ^ 2 + g * p + a * r)) / (2 * r * p + g) =
      -(g * p + 2 * a * r) / (2 * r * p + g) := by
  ring

/-
dies sind allgemein zwei äquivalente Substitutionen und

vⅠ² − awⅠ² (= NⅠ) und vⅡ² − awⅡ² (= NⅡ)

die ihnen entsprechenden äquivalenten Nenner.
-/

example (a r g p q : ℚ) (hp : p ^ 2 - a ≠ 0) (hq : q ^ 2 - a ≠ 0)
    (hg : 2 * r * p + g ≠ 0)
    (heq : q = -(g * p + 2 * a * r) / (2 * r * p + g)) :
    (2 * r * q + g) / (q ^ 2 - a) = (2 * r * p + g) / (p ^ 2 - a) := by
  have h := (eq_div_iff hg).1 heq
  apply (div_eq_div_iff hq hp).2
  linear_combination (p - q) * h

/-
Der Bruch pⅡ lässt sich durch das grösste gemeinschaftliche
Mass von g und 2r sonst aber stets durch n heben, was
sogleich ersichtlich wird, wenn man daselbst

pⅠ = (kn − α₁l)/l, (§. 6), r = mα₁ + nβ₁

und hierauf im Nenner α₁² − a = nγ setzt.
-/

end Kunerth1880.Paragraf12
