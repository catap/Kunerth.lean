/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf10

/-
Seite 39

§. 10.
1. Diese Art der Auffindung brauchbarer Werthe von p durch
Addition und Subtraction bekannter Wurzeln ist auch dann
anwendbar, wenn aus einer Gleichung von der Form
-/

/-
Seite 40

y² = ax²+bx+c    I
ohne Beseitigung des Gliedes bx die Unbekannte 1x durch die
p-Function unmittelbar ausgedrückt wird. Letzteres ist nur dann
möglich, wenn man einen Werth von x bereits gefunden hat, sei
es durch Versuche, sei es durch Absonderung eines quadratischen
Gliedes.
Es seien x₁ und y₁ ganzzahlige Werthe der Gleichung I,
so ist
y² = a(x²−x₁²)+b(x−x₁)+y₁² = [p(x−x₁)+y₁]²
und hieraus
x = x₁−(2y₁p−2ax₁−b)/(p²−a)    II
-/

example (a b c x x₁ y₁ : ℚ) (h : y₁ ^ 2 = a * x₁ ^ 2 + b * x₁ + c) :
    a * x ^ 2 + b * x + c = a * (x ^ 2 - x₁ ^ 2) + b * (x - x₁) + y₁ ^ 2 := by
  linear_combination -h

example (a b p x x₁ y₁ : ℚ) :
    (p * (x - x₁) + y₁) ^ 2 - (a * (x ^ 2 - x₁ ^ 2) + b * (x - x₁) + y₁ ^ 2) =
      (x - x₁) * ((p ^ 2 - a) * (x - x₁) + 2 * y₁ * p - 2 * a * x₁ - b) := by ring

/-
und
y = −y₁+[(2ax₁+b)p−2ay₁]/(p²−a).    III
-/

example (a b p x₁ y₁ : ℚ) (hd : p ^ 2 - a ≠ 0) :
    p * ((x₁ - (2 * y₁ * p - 2 * a * x₁ - b) / (p ^ 2 - a)) - x₁) + y₁ =
      -y₁ + ((2 * a * x₁ + b) * p - 2 * a * y₁) / (p ^ 2 - a) := by
  ring_nf at hd ⊢
  field_simp [hd]
  ring

/-
Für x = (z−b)/(2a) geht I über in
z² = 4ay²+(b²−4ac)    IV
-/

example (a b c z : ℚ) (ha : a ≠ 0) :
    4 * a * (a * ((z - b) / (2 * a)) ^ 2 + b * ((z - b) / (2 * a)) + c) =
      z ^ 2 - (b ^ 2 - 4 * a * c) := by
  field_simp
  ring

/-
und da y₁ und z₁ bekannte Wurzeln dieser Gleichung sind, so ist
z² = 4a(y²−y₁²)+z₁² = [q(y−y₁)+z₁]²
und
y = y₁−(2z₁q−8ay₁)/(q²−4a);
für q = 2r und z₁ = 2ax₁+b wird
y = y₁−[(2ax₁+b)r−2ay₁]/(r²−a);    V
-/

example (a x₁ y₁ b r : ℚ) :
    y₁ - (2 * (2 * a * x₁ + b) * (2 * r) - 8 * a * y₁) / ((2 * r) ^ 2 - 4 * a) =
      y₁ - ((2 * a * x₁ + b) * r - 2 * a * y₁) / (r ^ 2 - a) := by
  rw [show (2 * r) ^ 2 - 4 * a = 4 * (r ^ 2 - a) by ring, div_mul_eq_div_div]
  ring

/-
da von dem Vorzeichen abgesehen — was bei y statthaft ist —
dieser letzte Ausdruck für y mit dem in III stehenden identisch
ist, so wird jeder Werth von r, welcher y zu einer ganzen Zahl
macht, für p in die Gleichung II gesetzt, auch x in eine ganze
Zahl verwandeln, sobald (z−b)/(2a) in eine solche übergeht, oder es
wird dies durch einen äquivalenten Werth von r bewirkt (§. 3 10)
den man aus den bereits bekannten Wurzeln der Gleichung I
-/

example (a b p x₁ y₁ : ℚ) :
    y₁ - ((2 * a * x₁ + b) * p - 2 * a * y₁) / (p ^ 2 - a) =
      -(-y₁ + ((2 * a * x₁ + b) * p - 2 * a * y₁) / (p ^ 2 - a)) := by ring

/-
Seite 41

finden kann; offenbar muss p äquivalent mit r sein, weil auch p
der Gleichung V Genüge leistet.
In der ersten Rechnung ist y = p(x−x₁)+y₁ und in der
zweiten Rechnung ist z = q(y−y₁)+z₁ hieraus
z = pq(x−x₁)+z₁,
und für z und z₁ die Werthe gesetzt
2ax+b = pq(x−x₁)+2ax₁+b,
somit
pq = 2a und p = 2a/q.
-/

example (p q x x₁ y₁ z₁ : ℚ) :
    q * ((p * (x - x₁) + y₁) - y₁) + z₁ = p * q * (x - x₁) + z₁ := by ring

example (a b p q x x₁ : ℚ) (hx : x ≠ x₁)
    (h : 2 * a * x + b = p * q * (x - x₁) + 2 * a * x₁ + b) : p * q = 2 * a := by
  have he : (p * q - 2 * a) * (x - x₁) = 0 := by linarith
  rcases mul_eq_zero.mp he with hzero | hzero
  · linarith
  · exact False.elim (hx (sub_eq_zero.mp hzero))

example (a p q : ℚ) (hq : q ≠ 0) (h : p * q = 2 * a) : p = 2 * a / q := by
  exact (eq_div_iff hq).mpr h

/-
Wären x₂, x₃; y₂, y₃; z₂, z₃ ganzzahlige Werthe der
Gleichungen I und IV und
q = (z₂−z₃)/(y₂−y₃) = 2a(x₂−x₃)/(y₂−y₃)
ein brauchbarer Werth zur Bestimmung eines neuen ganzzahligen
y, so könnte auch
p = 2a : [2a(x₂−x₃)/(y₂−y₃)] = (y₂−y₃)/(x₂−x₃)
ein ganzzahliges x liefern, und dieser Werth von p lässt sich aus
der für I geführten Rechnung finden.
-/

example (a b x₂ x₃ y₂ y₃ : ℚ) :
    ((2 * a * x₂ + b) - (2 * a * x₃ + b)) / (y₂ - y₃) =
      2 * a * (x₂ - x₃) / (y₂ - y₃) := by ring

example (a x₂ x₃ y₂ y₃ : ℚ) (ha : a ≠ 0) (hx : x₂ - x₃ ≠ 0)
    (hy : y₂ - y₃ ≠ 0) :
    2 * a / (2 * a * (x₂ - x₃) / (y₂ - y₃)) = (y₂ - y₃) / (x₂ - x₃) := by
  field_simp

namespace Beispiel01

/-
2. Exempel.
y² = 7x²−16x+21;
hier ist x = 3, y = 6 also
y² = 7(x²−9)−16(x−3)+36 = [p(x−3)−6]²
-/

example (x : ℚ) : 7 * (x ^ 2 - 9) - 16 * (x - 3) + 36 =
    7 * x ^ 2 - 16 * x + 21 := by ring

#guard (6 : ℤ) ^ 2 = 7 * 3 ^ 2 - 16 * 3 + 21

/-
und daraus
x = 3+2(6p+13)/(p²−7), S = 2×83;
-/

def x (p : ℚ) : ℚ := 3 + 2 * (6 * p + 13) / (p ^ 2 - 7)

def y (p : ℚ) : ℚ := p * (x p - 3) - 6

#guard (2 * 83 : ℤ) = 166

/-
für p = +3     −3     (87+9)/(34+2) = 8/3     −8/3
    x = +34    −2           +525              −51
    y =  87     9           1386              138.
-/

#guard ((87 + 9) / (34 + 2) : ℚ) = 8 / 3

#guard ([(3, 34, 87), (-3, -2, 9), (8/3, 525, 1386), (-8/3, -51, 138)] :
    List (ℚ × ℚ × ℚ)).all fun (p, u, v) =>
      x p == u && y p == v && v ^ 2 == 7 * u ^ 2 - 16 * u + 21

end Beispiel01

end Kunerth1877.Paragraf10
