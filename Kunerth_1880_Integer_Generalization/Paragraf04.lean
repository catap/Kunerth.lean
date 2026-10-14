/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf04

/-
Seite 345
§. 4.

Schafft man in VIa mittelst der Substitution p = (p₁ + α₁)/n das
zweite Glied des Nenners weg, so wird

x = [mp₁² + 2(mα₁ + nβ₁)p₁ + (mα₁² + 2nα₁β₁ + n²δ)] /
    [n(p₁² − a)] ... VIIa;
-/

example (m n α₁ β₁ δ p : ℚ) :
    n ^ 2 * (m * p ^ 2 + 2 * β₁ * p + δ) =
    m * (n * p - α₁) ^ 2 + 2 * (m * α₁ + n * β₁) * (n * p - α₁) +
      (m * α₁ ^ 2 + 2 * n * α₁ * β₁ + n ^ 2 * δ) := by
  ring

example (n α₁ γ p : ℚ) :
    n * (n * p ^ 2 - 2 * α₁ * p + γ) =
      (n * p - α₁) ^ 2 - (α₁ ^ 2 - n * γ) := by
  ring

/-
ersetzt man im Zähler die Grösse δ durch (β₁² − c)/m (§. 2),
hierauf mα₁ + nβ₁ durch r (nach III), endlich r² − cn² durch
am² + bmn, da r² = am² + bmn + cn² ist, so folgt:

Seite 346

x = [mp₁² + 2rp₁ + (am + bn)]/[n(p₁² − a)] ... VIIb;

multiplicirt man nun beide Seiten mit n und verwandelt den Bruch
in eine gemischte Zahl, so erhält man die Hauptformel

nx = m + [2rp₁ + (2am + bn)]/(p₁² − a) ... VIII,
-/

example (a b m n r p : ℚ) (hn : n ≠ 0) (hp : p ^ 2 - a ≠ 0) :
    n * ((m * p ^ 2 + 2 * r * p + (a * m + b * n)) / (n * (p ^ 2 - a))) =
      m + (2 * r * p + (2 * a * m + b * n)) / (p ^ 2 - a) := by
  field_simp
  ring

/-
welche fortan aus den Werthen der Unbekannten:
x = m/n, y = r/n
und den Constanten in I aufgestellt werden kann. Ist in der
Gleichung I b = 0, so wird

nx = m + 2(rp₁ + am)/(p₁² − a).
-/

example (a m r p : ℚ) (_hp : p ^ 2 - a ≠ 0) :
    m + (2 * r * p + 2 * a * m) / (p ^ 2 - a) =
      m + 2 * ((r * p + a * m) / (p ^ 2 - a)) := by
  ring

end Kunerth1880.Paragraf04
