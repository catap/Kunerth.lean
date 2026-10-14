/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1877.Paragraf16

/-
Seite 56
-/

/-
§. 16.
Anhang.

Zum Schlusse folge noch eine Berichtigung der zwar ohne
Beweis gegebenen, dabei aber vortrefflichen Regel Tenner's
für die Verwandlung von √N in einen Kettenbruch, wie dies bei
der Auflösung einer unbestimmten quadratischen Gleichung nach
der Methode von Lagrange erforderlich ist.
Sollte man √109 in einen Kettenbruch verwandeln, so ist
nach Tenner in folgender Weise zu rechnen:
1. Man schreibe
I     II    III    IV    V    VI
10     ×     10 = 109    —     9
(Die vollständige Rechnung steht auf der folgenden Seite.)
2. Darauf dividire man 10+10 durch 9 und setze den Quotienten
   (2) unter I, den Rest (2) unter II.
-/

/- Hilfsdefinition: Die sechs Einträge sind die Spalten I bis VI. -/

private def tennerRow (N a third denominator : ℤ) : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ :=
  let quotient := (a + third) / denominator
  let remainder := (a + third) % denominator
  let nextThird := a - remainder
  let square := nextThird ^ 2
  let difference := N - square
  (quotient, remainder, nextThird, square, difference, difference / denominator)

example : (10 : ℤ) ^ 2 < 109 ∧ (11 : ℤ) ^ 2 > 109 ∧
    (109 : ℤ) - 10 ^ 2 = 9 := by norm_num

/-
Seite 57

3. Diesen Rest subtrahire man von 10 und setze den Rest (8)
   unter III, das Quadrat dieses Restes (64) in IV, subtrahire
   es von 109 und setze den Rest (45) in V.
4. Man dividire diesen durch die Zahl 9 der zunächst vorhergehenden
   Reihe in VI und setze den Quotienten (5) in VI.
5. Man dividire wieder 10+III, d. i. 10+8 durch die Zahl (5)
   in VI, setze den Quotienten (3) in I, den Rest (3) in II,
   subtrahire ihn von 10, setze den Rest (7) in III u. s. w.
6. Sobald man in II oder in VI dieselbe Zahl erhält, die
   unmittelbar darüber steht, so ist die Rechnung geschlossen.
   Sollte einmal der Divisor in VI in der nächstfolgenden
   Zahl in V nicht aufgehen, so ist dies ein Zeichen, dass ein
   Rechnungsfehler vorgefallen ist.
In I steht die dem Kettenbruche vorangehende ganze Zahl
(10) und darunter stehen die Nenner des periodischen Kettenbruches;
in VI aber stehen die Nenner der vollständigen Quotienten,
welche aus der Entwicklung von √N in einen Kettenbruch
nach der Methode von Lagrange hervorgehen.
-/

example : tennerRow 109 10 10 9 = (2, 2, 8, 64, 45, 5) := by
  norm_num [tennerRow]

example : tennerRow 109 10 8 5 = (3, 3, 7, 49, 60, 12) := by
  norm_num [tennerRow]

/-
Wie aus der nachstehenden Tabelle zu ersehen ist, trifft die
in 6 aufgestellte Behauptung nicht immer zu, denn obgleich in
VI die Zahl 3 zweimal nacheinander auftritt, so ist die Rechnung
noch nicht geschlossen, sondern es geschieht dies erst dann,
wenn in I die Zahl 20 zu stehen kommt, neben welcher in II eine
sich unmittelbar wiederholende Zahl (Null) steht.
Daher muss die Rechnung so lange fortgesetzt werden, bis
in I die daselbst oben stehende Zahl (10) verdoppelt auftritt,
dann erst ist die Rechnung geschlossen.
-/

example : let previousDenominator : ℤ := 3
          let current := tennerRow 109 10 8 previousDenominator
          current.2.2.2.2.2 = previousDenominator ∧ current.1 ≠ 2 * 10 := by
  norm_num [tennerRow]

/-
 I   II   III   IV    V   VI
10    ×    10 = 109    —    9
 2    2     8    64   45    5
 3    3     7    49   60   12
 1    5     5    25   84    7
 2    1     9    81   28    4
 4    3     7    49   60   15
 1    2     8    64   45    3
 6    0    10   100    9    3
 6    2     8    64   45   15
-/

example : let remainder : ℤ := (10 + 10) % 9
          let nextThird := 10 - remainder
          (((10 + 10) / 9, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 9) =
            (2, 2, 8, 64, 45, 5)) ∧
          (109 - nextThird ^ 2) % 9 = 0 := by norm_num

example : let remainder : ℤ := (10 + 8) % 5
          let nextThird := 10 - remainder
          (((10 + 8) / 5, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 5) =
            (3, 3, 7, 49, 60, 12)) ∧
          (109 - nextThird ^ 2) % 5 = 0 := by norm_num

example : let remainder : ℤ := (10 + 7) % 12
          let nextThird := 10 - remainder
          (((10 + 7) / 12, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 12) =
            (1, 5, 5, 25, 84, 7)) ∧
          (109 - nextThird ^ 2) % 12 = 0 := by norm_num

example : let remainder : ℤ := (10 + 5) % 7
          let nextThird := 10 - remainder
          (((10 + 5) / 7, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 7) =
            (2, 1, 9, 81, 28, 4)) ∧
          (109 - nextThird ^ 2) % 7 = 0 := by norm_num

example : let remainder : ℤ := (10 + 9) % 4
          let nextThird := 10 - remainder
          (((10 + 9) / 4, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 4) =
            (4, 3, 7, 49, 60, 15)) ∧
          (109 - nextThird ^ 2) % 4 = 0 := by norm_num

example : let remainder : ℤ := (10 + 7) % 15
          let nextThird := 10 - remainder
          (((10 + 7) / 15, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 15) =
            (1, 2, 8, 64, 45, 3)) ∧
          (109 - nextThird ^ 2) % 15 = 0 := by norm_num

example : let remainder : ℤ := (10 + 8) % 3
          let nextThird := 10 - remainder
          (((10 + 8) / 3, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 3) =
            (6, 0, 10, 100, 9, 3)) ∧
          (109 - nextThird ^ 2) % 3 = 0 := by norm_num

example : let remainder : ℤ := (10 + 10) % 3
          let nextThird := 10 - remainder
          (((10 + 10) / 3, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 3) =
            (6, 2, 8, 64, 45, 15)) ∧
          (109 - nextThird ^ 2) % 3 = 0 := by norm_num

/-
Seite 58

 I   II   III   IV    V   VI
 1    3     7    49   60    4
 4    1     9    81   28    7
 2    5     5    25   84   12
 1    3     7    49   60    5
 3    2     8    64   45   15
 1    3     7    49   60    4
 4    1     9    81   28    7
 2    5     5    25   84   12
 1    3     7    49   60    5
 3    2     8    64   45    9
 2    0    10   100    9    1
20    0    10   100    9    9.
-/

example : let remainder : ℤ := (10 + 8) % 15
          let nextThird := 10 - remainder
          (((10 + 8) / 15, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 15) =
            (1, 3, 7, 49, 60, 4)) ∧
          (109 - nextThird ^ 2) % 15 = 0 := by norm_num

example : let remainder : ℤ := (10 + 7) % 4
          let nextThird := 10 - remainder
          (((10 + 7) / 4, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 4) =
            (4, 1, 9, 81, 28, 7)) ∧
          (109 - nextThird ^ 2) % 4 = 0 := by norm_num

example : let remainder : ℤ := (10 + 9) % 7
          let nextThird := 10 - remainder
          (((10 + 9) / 7, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 7) =
            (2, 5, 5, 25, 84, 12)) ∧
          (109 - nextThird ^ 2) % 7 = 0 := by norm_num

example : let remainder : ℤ := (10 + 5) % 12
          let nextThird := 10 - remainder
          (((10 + 5) / 12, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 12) =
            (1, 3, 7, 49, 60, 5)) ∧
          (109 - nextThird ^ 2) % 12 = 0 := by norm_num

/-
Zuordnung: In der fünften Reihe auf Seite 58 steht in VI die Zahl 15.
Nach Nr. 4 ist hier 45 durch die 5 in VI der vorhergehenden Reihe zu
dividiren. Die folgende Nachrechnung prüft die ersten fünf Spalten,
die Abweichung in VI und die Theilbarkeit.
-/

example : let remainder : ℤ := (10 + 7) % 5
          let nextThird := 10 - remainder
          (((10 + 7) / 5, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2) =
            (3, 2, 8, 64, 45)) ∧
          (109 - nextThird ^ 2) / 5 ≠ 15 ∧
          (109 - nextThird ^ 2) % 5 = 0 := by norm_num

/-
Vermutlicher Tabellenfehler: 45 : 5 ergibt 9 statt 15. Mit 9 würden
unmittelbar die beiden Schlussreihen mit I = 2 und I = 20 folgen.
Dazwischen steht hier ein Block von fünf weiteren Reihen; seine ersten
vier wiederholen die ersten vier Reihen auf Seite 58.
Die ursprüngliche Tabelle bleibt wörtlich erhalten; die nachfolgenden
Prüfungen gehen jeweils von der dort angegebenen Vorreihe aus.

Berichtigte Gesamttabelle nach der angegebenen Rechenregel
(redaktionelle Nachrechnung):

 I   II   III   IV    V   VI
10    ×    10 = 109    —    9
 2    2     8    64   45    5
 3    3     7    49   60   12
 1    5     5    25   84    7
 2    1     9    81   28    4
 4    3     7    49   60   15
 1    2     8    64   45    3
 6    0    10   100    9    3
 6    2     8    64   45   15
 1    3     7    49   60    4
 4    1     9    81   28    7
 2    5     5    25   84   12
 1    3     7    49   60    5
 3    2     8    64   45    9
 2    0    10   100    9    1
20    0    10   100    9    9.
-/

example : (45 : ℤ) / 5 = 9 := by norm_num

example : let remainder : ℤ := (10 + 8) % 15
          let nextThird := 10 - remainder
          (((10 + 8) / 15, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 15) =
            (1, 3, 7, 49, 60, 4)) ∧
          (109 - nextThird ^ 2) % 15 = 0 := by norm_num

example : let remainder : ℤ := (10 + 7) % 4
          let nextThird := 10 - remainder
          (((10 + 7) / 4, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 4) =
            (4, 1, 9, 81, 28, 7)) ∧
          (109 - nextThird ^ 2) % 4 = 0 := by norm_num

example : let remainder : ℤ := (10 + 9) % 7
          let nextThird := 10 - remainder
          (((10 + 9) / 7, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 7) =
            (2, 5, 5, 25, 84, 12)) ∧
          (109 - nextThird ^ 2) % 7 = 0 := by norm_num

example : let remainder : ℤ := (10 + 5) % 12
          let nextThird := 10 - remainder
          (((10 + 5) / 12, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 12) =
            (1, 3, 7, 49, 60, 5)) ∧
          (109 - nextThird ^ 2) % 12 = 0 := by norm_num

example : let remainder : ℤ := (10 + 7) % 5
          let nextThird := 10 - remainder
          (((10 + 7) / 5, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 5) =
            (3, 2, 8, 64, 45, 9)) ∧
          (109 - nextThird ^ 2) % 5 = 0 := by norm_num

example : let remainder : ℤ := (10 + 8) % 9
          let nextThird := 10 - remainder
          (((10 + 8) / 9, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 9) =
            (2, 0, 10, 100, 9, 1)) ∧
          (109 - nextThird ^ 2) % 9 = 0 := by norm_num

example : let remainder : ℤ := (10 + 10) % 1
          let nextThird := 10 - remainder
          (((10 + 10) / 1, remainder, nextThird,
            nextThird ^ 2, 109 - nextThird ^ 2, (109 - nextThird ^ 2) / 1) =
            (20, 0, 10, 100, 9, 9)) ∧
          (109 - nextThird ^ 2) % 1 = 0 := by norm_num

/-
Jetzt ist die Rechnung geschlossen.
-/

example : (20 : ℤ) = 2 * 10 ∧ ((10 : ℤ), 9) = (10, 109 - 10 ^ 2) := by
  norm_num

example : let current := tennerRow 109 10 10 1
          current.1 = 2 * 10 ∧ current.2.1 = 0 ∧
          (current.2.2.1, current.2.2.2.2.2) = (10, 9) := by
  norm_num [tennerRow]

end Kunerth1877.Paragraf16
