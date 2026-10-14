/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Kunerth_1880_Integer_Generalization.Paragraf06

namespace Kunerth1880.Paragraf07

/-
Seite 348
§. 7.

2. Der Nenner v² − aw² muss stets ein Theiler von n(b² − 4ac)
sein. Um dies zu beweisen, bringen wir in X die Zahl m nach
links, multipliciren hierauf beide Seiten mit 2rv − (2am + bn)w
und addiren −4r²w hinzu; da wird nach rechtsseitig vollzogener
Reduction:

(nx − m)[v2r − (2am + bn)w] − 4r²w =
−[−4ar² + (2am + bn)²]w³/(v² − aw²) =
−n²(b² − 4ac)w³/(v² − aw²) ... XI;
-/

example (a g r v w : ℚ) (hN : v ^ 2 - a * w ^ 2 ≠ 0) :
    ((2 * r * v + g * w) * w / (v ^ 2 - a * w ^ 2)) * (2 * r * v - g * w) -
      4 * r ^ 2 * w = -((-4 * a * r ^ 2 + g ^ 2) / (v ^ 2 - a * w ^ 2)) * w ^ 3 := by
  have hi := mul_inv_cancel₀ hN
  linear_combination 4 * r ^ 2 * w * hi

example (a b c m n r : ℚ)
    (hr : r ^ 2 = a * m ^ 2 + b * m * n + c * n ^ 2) :
    -4 * a * r ^ 2 + (2 * a * m + b * n) ^ 2 = n ^ 2 * (b ^ 2 - 4 * a * c) := by
  linear_combination -4 * a * hr

/-
von x abgesehen, bezeichnen alle hier vorkommenden Buchstaben
ganze Zahlen.

Die linke Seite dieser Gleichung lässt sich in zwei Theile
zerlegen, von denen der eine den Factor n explicite, der andere
aber implicite enthält; dieser ist:

−2mrv + 2am²w − 4r²w oder 2w(am² − r²) − 2r(mv + rw).

Da nach §. 6 die Brüche (kn − α₁l)/l und v/w einander gleich und
reducirt sind, so ist v = kn − α₁l, w = l; und weil r = mα₁ + nβ₁
(nach III), so wird mv = kmn − α₁lm und rw = β₁ln + α₁lm, daher

Seite 349

nach Addition beider Gleichungen: mv + rw = n(km + β₁l);
-/

example (m n k l α₁ β₁ : ℤ) :
    m * (k * n - α₁ * l) + (m * α₁ + n * β₁) * l = n * (k * m + β₁ * l) := by
  ring

/-
weil ferner r² = am² + bmn + cn², so ist am² − r² = −n(bm + cn)
und jener zweite Theil ist gleich −2nw(bm + cn) − 2nr(km + β₁l).
Der linke Flügel der Gleichung XI ist somit durch n theilbar und
nach beiderseitiger Division mit n bleibt rechts der Bruch

−n(b² − 4ac)w³/(v² − aw²);

da aber w³ prim gegen den Nenner ist, so muss n(b² − 4ac) durch
v² − aw² theilbar sein.
-/

theorem normCoprime (a v w : ℤ) (hvw : Int.gcd v w = 1) :
    IsCoprime (v ^ 2 - a * w ^ 2) (w ^ 3) := by
  apply IsCoprime.pow_right
  have h := Int.gcd_eq_gcd_ab v w
  rw [hvw] at h
  norm_num at h
  refine ⟨(Int.gcdA v w) ^ 2,
    a * w * (Int.gcdA v w) ^ 2 + 2 * v * Int.gcdA v w * Int.gcdB v w +
      w * (Int.gcdB v w) ^ 2, ?_⟩
  nlinarith [sq_nonneg (v * Int.gcdA v w + w * Int.gcdB v w - 1)]

theorem normDividesDiscriminant (a b c m n r v w x k α₁ β₁ : ℤ) (hn : n ≠ 0)
    (hr : r ^ 2 = a * m ^ 2 + b * m * n + c * n ^ 2)
    (hline : r = m * α₁ + n * β₁) (hv : v = k * n - α₁ * w)
    (hcop : IsCoprime (v ^ 2 - a * w ^ 2) (w ^ 3))
    (hX : (n * x - m) * (v ^ 2 - a * w ^ 2) =
      (2 * r * v + (2 * a * m + b * n) * w) * w) :
    v ^ 2 - a * w ^ 2 ∣ n * (b ^ 2 - 4 * a * c) := by
  let L := x * (2 * r * v - (2 * a * m + b * n) * w) + b * m * w -
    2 * w * (b * m + c * n) - 2 * r * (k * m + β₁ * w)
  have hmv : m * v + r * w = n * (k * m + β₁ * w) := by
    rw [hv, hline]
    ring
  have hL : (n * x - m) * (2 * r * v - (2 * a * m + b * n) * w) -
      4 * r ^ 2 * w = n * L := by
    dsimp [L]
    linear_combination -2 * w * hr - 2 * r * hmv
  have hXI : (v ^ 2 - a * w ^ 2) *
      ((n * x - m) * (2 * r * v - (2 * a * m + b * n) * w) - 4 * r ^ 2 * w) =
      -n ^ 2 * (b ^ 2 - 4 * a * c) * w ^ 3 := by
    linear_combination (2 * r * v - (2 * a * m + b * n) * w) * hX + 4 * a * w ^ 3 * hr
  have he : n * ((v ^ 2 - a * w ^ 2) * L) =
      n * (-n * (b ^ 2 - 4 * a * c) * w ^ 3) := by
    rw [hL] at hXI
    linear_combination hXI
  have he' := mul_left_cancel₀ hn he
  apply hcop.dvd_of_dvd_mul_left
  refine ⟨-L, ?_⟩
  linear_combination he'

/-
Das Product n²(b² − 4ac) bezeichnen wir mit S und nennen
es die Stammzahl, weil ihm alle passenden Werthe von v und w
entstammen, falls solche vorkommen; es ist auch

S = −4ar² + (2am + bn)².

In der Gleichung XI können unter gewissen Bedingungen
Abkürzungen vorgenommen werden, welche die Rechnung
vereinfachen; sie werden in den nächsten neun Paragraphen
behandelt.
-/

theorem preparationFromVIII (a b m n r α β γ δ x : ℤ) (p : ℚ)
    (hn : n ≠ 0) (hmn : Int.gcd m n = 1)
    (ha : a = α ^ 2 - n * γ) (hb : b = 2 * α * β + m * γ + n * δ)
    (hr : r = m * α + n * β) (hp : p ^ 2 - a ≠ 0)
    (hX : (n : ℚ) * x = m + (2 * r * p + (2 * a * m + b * n)) / (p ^ 2 - a)) :
    n ∣ p.num + α * (p.den : ℤ) := by
  let P : ℚ := (p + α) / n
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hP : p = n * P - α := by dsimp [P]; field_simp; ring
  have hcross : ((n : ℚ) * x - m) * (p ^ 2 - a) =
      2 * r * p + (2 * a * m + b * n) := by
    exact (eq_div_iff hp).mp (by linear_combination hX)
  have haq : (a : ℚ) = (α : ℚ) ^ 2 - n * γ := by exact_mod_cast ha
  have hbq : (b : ℚ) = 2 * (α : ℚ) * β + m * γ + n * δ := by exact_mod_cast hb
  have hrq : (r : ℚ) = (m : ℚ) * α + n * β := by exact_mod_cast hr
  have hVI : (x : ℚ) * (n * P ^ 2 - 2 * α * P + γ) =
      m * P ^ 2 + 2 * β * P + δ := by
    rw [haq, hbq, hrq] at hcross
    dsimp [P]
    field_simp
    linear_combination hcross
  exact Kunerth1880.Paragraf06.preparationFromVI m n α β γ δ x P p hmn hVI hP

theorem normData (a b c m n r α β γ δ x : ℤ) (p : ℚ)
    (hn : n ≠ 0) (hmn : Int.gcd m n = 1)
    (ha : a = α ^ 2 - n * γ) (hb : b = 2 * α * β + m * γ + n * δ)
    (hc : c = β ^ 2 - m * δ) (hr : r = m * α + n * β)
    (hp : p ^ 2 - a ≠ 0)
    (hX : (n : ℚ) * x = m + (2 * r * p + (2 * a * m + b * n)) / (p ^ 2 - a)) :
    n ∣ p.num ^ 2 - a * (p.den : ℤ) ^ 2 ∧
      p.num ^ 2 - a * (p.den : ℤ) ^ 2 ∣ n * (b ^ 2 - 4 * a * c) := by
  obtain ⟨k, hk⟩ := preparationFromVIII a b m n r α β γ δ x p hn hmn ha hb hr hp hX
  have hprep : p.num = k * n - α * (p.den : ℤ) := by linear_combination hk
  have hroot : r ^ 2 = a * m ^ 2 + b * m * n + c * n ^ 2 := by
    rw [ha, hb, hc, hr]
    ring
  have hcop : Int.gcd p.num (p.den : ℤ) = 1 := by
    simpa [Int.gcd] using p.reduced
  have hwq : (p.den : ℚ) ≠ 0 := by exact_mod_cast p.den_nz
  have hpv : p = (p.num : ℚ) / p.den := (Rat.num_div_den p).symm
  have hcross : ((n : ℚ) * x - m) * (p ^ 2 - a) =
      2 * r * p + (2 * a * m + b * n) := by
    exact (eq_div_iff hp).mp (by linear_combination hX)
  rw [hpv] at hcross
  field_simp [hwq] at hcross
  have hXint : (n * x - m) * (p.num ^ 2 - a * (p.den : ℤ) ^ 2) =
      (2 * r * p.num + (2 * a * m + b * n) * (p.den : ℤ)) * (p.den : ℤ) := by
    have hq : ((n : ℚ) * x - m) * ((p.num : ℚ) ^ 2 - a * (p.den : ℚ) ^ 2) =
        (2 * r * (p.num : ℚ) + (2 * a * m + b * n) * (p.den : ℚ)) * (p.den : ℚ) := by
      linear_combination hcross
    exact_mod_cast hq
  constructor
  · apply Kunerth1880.Paragraf06.normMultiple a n α γ k p.num (p.den : ℤ)
    · linear_combination hprep
    · linear_combination -ha
  · exact normDividesDiscriminant a b c m n r p.num (p.den : ℤ) x k α β
      hn hroot hr hprep (normCoprime a p.num (p.den : ℤ) hcop) hXint

end Kunerth1880.Paragraf07
