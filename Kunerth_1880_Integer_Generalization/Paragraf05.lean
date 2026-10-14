/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf05

/-
Seite 346
§. 5.

Die Formel VIII entsteht auch durch Subtraction der
identischen Gleichung

r²/n² = a m²/n² + b m/n + c

von der unter I stehenden; also

y² = a(x² − m²/n²) + b(x − m/n) + r²/n²;

setzt man für dieses Trinom das Quadrat

[p₁(x − m/n) − r/n]²,

reducirt, und entwickelt x, so kommt

x = [mp₁² + 2rp₁ + (am + bn)]/[n(p₁² − a)], wie in VIIb.
-/

example (a b c m n r p x : ℚ)
    (hr : r ^ 2 = a * m ^ 2 + b * m * n + c * n ^ 2) :
    (p * (n * x - m) - r) ^ 2 -
      (a * (n * x) ^ 2 + b * n ^ 2 * x + c * n ^ 2) =
      (n * x - m) * ((p ^ 2 - a) * (n * x - m) -
        2 * r * p - (2 * a * m + b * n)) := by
  linear_combination hr

/-
Der Satz

y = p₁(x − m/n) − r/n ... IX

gestattet eine bequeme Berechnung von y aus dem für x
gefundenen Werthe. Stellt man hier für x den Bruch aus VIIb ein,

Seite 347

so wird

ny = r + [(2am + bn)p₁ + 2ar]/(p₁² − a).
-/

example (a b m n r p : ℚ) (hn : n ≠ 0) (hp : p ^ 2 - a ≠ 0) :
    n * (p * ((m * p ^ 2 + 2 * r * p + (a * m + b * n)) /
      (n * (p ^ 2 - a)) - m / n) - r / n) =
      r + ((2 * a * m + b * n) * p + 2 * a * r) / (p ^ 2 - a) := by
  field_simp
  ring

/-
In allen diesen Formeln ist r mit jenem Vorzeichen zu nehmen,
welches ihm nach III zukömmt.

Im Allgemeinen sind die brauchbaren Werthe von p und p₁
gebrochene, oft aber nebstbei auch ganze Zahlen; daher setze
man in VIII p₁ = v/w, wodurch

nx = m + [2rv + (2am + bn)w]w/(v² − aw²) ... X

wird.
-/

example (a b m n r v w : ℚ) (hw : w ≠ 0) (_hN : v ^ 2 - a * w ^ 2 ≠ 0) :
    m + (2 * r * (v / w) + (2 * a * m + b * n)) / ((v / w) ^ 2 - a) =
      m + ((2 * r * v + (2 * a * m + b * n) * w) / (v ^ 2 - a * w ^ 2)) * w := by
  field_simp

end Kunerth1880.Paragraf05
