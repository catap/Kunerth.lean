/-
Kunerth.lean - translation of Prof. Adolf Kunerth's works into Lean.

Written in 2026 by Kirill A. Korinsky <kirill@korins.ky>

This work is released into the public domain with CC0 1.0.
-/

import Mathlib

namespace Kunerth1880.Paragraf06

/-
Seite 347
§. 6.

Damit x eine ganze Zahl werden könne, müssen die noch
unbestimmten, ganzen und gegen einander theilfremden Zahlen
v und w zwei Bedingungen erfüllen.

1. Der Nenner v² − aw² muss immer durch n theilbar sein.
Für p darf kein Bruch gesetzt werden, dessen Nenner mit n einen
Factor gemein hat; denn ist n = νπ und p = k/(νl), so wird in VIa

x = (mk² + 2β₁kνl + δν²l²)/(νπk² − 2α₁kνl + γν²l²);

da nun νπ, d. i. n prim gegen m und ν prim gegen k ist, so kann
der Zähler dieses Bruches durch ν nicht theilbar sein und letzterer
keine ganze Zahl werden.
-/

example (m ν π k l α₁ β₁ γ δ : ℤ) (hν : ¬ IsUnit ν)
    (hm : Int.gcd ν m = 1) (hk : Int.gcd ν k = 1) :
    ¬ ∃ x : ℤ,
      x * (ν * π * k ^ 2 - 2 * α₁ * k * ν * l + γ * ν ^ 2 * l ^ 2) =
        m * k ^ 2 + 2 * β₁ * k * ν * l + δ * ν ^ 2 * l ^ 2 := by
  rintro ⟨x, hx⟩
  apply hν
  apply ((Int.isCoprime_iff_gcd_eq_one.mpr hm).mul_right
    ((Int.isCoprime_iff_gcd_eq_one.mpr hk).pow_right (n := 2))).isUnit_of_dvd
  refine ⟨x * (π * k ^ 2 - 2 * α₁ * k * l + γ * ν * l ^ 2) -
    (2 * β₁ * k * l + δ * ν * l ^ 2), ?_⟩
  linear_combination -hx

/-
Ertheilt man jedoch der Variablen p einen solchen Werth k/l,
dass l prim gegen n ist, so wird in der Gleichung p₁ = np − α₁
(nach §. 4) das Product np (= nk/l) sich nicht abkürzen lassen,
und nach Einsetzen dieses Binoms für p₁ in VIIa wird

x = n²(mp² + 2β₁p + δ)/[n²(np² − 2α₁p + γ)]

oder

x = n²(mk² + 2β₁kl + δl²)/[n²(nk² − 2α₁kl + γl²)] ... (1),

und dieser Bruch kann eine ganze Zahl werden.
-/

theorem preparationFromVI (m n α β γ δ x : ℤ) (P p : ℚ)
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

/-
Seite 348

Da nun die gesuchten Werthe von p₁ die Form np − α₁ mit
Ausschluss jeder Reduction von np haben müssen, so lehrt uns
die letzte Formel, dass für p₁ nur solche Brüche — auch vom
Nenner Eins — zulässig sind, welche den Nenner des Bruches
in VII in ein Vielfaches von n² verwandeln.

Schreiben wir v/w statt p₁ in VIIb, so wird

x = [mv² + 2rvw + (am + bn)w²]/[n(v² − aw²)] ... (2)

und da die Brüche in (1) und (2) aus den identischen Brüchen in
VIIa und VIIb durch Einsetzen desselben reducirten Bruches
nk/l − α₁ respective v/w entstanden und ungekürzt geblieben sind,
so müssen auch sie identisch und ihre Nenner einander gleich sein;
also ist n²(nk² − 2α₁kl + γl²) = n(v² − aw²) und v² − aw² ein
Dividuum von n.
-/

example (n k l α₁ γ : ℤ) :
    (n * k - α₁ * l) ^ 2 - (α₁ ^ 2 - n * γ) * l ^ 2 =
      n * (n * k ^ 2 - 2 * α₁ * k * l + γ * l ^ 2) := by
  ring

theorem normMultiple (a n α₁ γ k v w : ℤ) (hv : v = n * k - α₁ * w)
    (hA : α₁ ^ 2 - a = n * γ) : n ∣ v ^ 2 - a * w ^ 2 := by
  refine ⟨n * k ^ 2 - 2 * α₁ * k * w + γ * w ^ 2, ?_⟩
  rw [hv]
  linear_combination w ^ 2 * hA

end Kunerth1880.Paragraf06
