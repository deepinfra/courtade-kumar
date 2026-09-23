import CK.LargeBias
import CK.LargeCoordinate
import CK.MiddleHigh
import CK.FourierCap
import CK.ScalarMixing
import CK.Relabel
import CK.SmallGap

/-!
# The complementary branch and the main theorem (manuscript Sec. 6.6, Theorem thm:main)

For `1/20 ≤ p ≤ 1/2` (so `ρ = 1 − 2p ∈ [0, 9/10]`) the Courtade–Kumar bound
`I(f(X);Y) ≤ log 2 − h(p)` is obtained by a four-way case split on the Fourier data of
`F = signOf f`, `m = E F`, `b_i = F̂({i})`:

* `|m| ≥ 13/20`: Lemma lem:bias (`large_bias`);
* some `|b_i| ≥ 13/20`: Lemma lem:largecoordinate, after relabelling coordinate `i` to the last
  position (`large_coordinate_last`, `information_relabel`, `fourierCoeff_comp_perm_singleton`);
* otherwise Prop prop:cap gives `m² + W₁(F) ≤ 31/40` (`bias_inclusive_cap`), and
  Prop prop:middle (`middle_range`, `ρ ≥ 3/5`) or Prop prop:high (`high_noise`, `ρ ≤ 3/5`)
  concludes.

Together with the low-noise branch `lowNoise_proved` this assembles Theorem thm:main
(`courtadeKumar_proved`).
-/
noncomputable section
namespace CK
open scoped BigOperators

/-- Lemma lem:largecoordinate at an arbitrary coordinate: if `|b_i| ≥ 13/20` for some `i` and
`ρ ≤ 9/10`, then `I(f(X);Y) ≤ log 2 − h(p)`.  Reduces to the last coordinate by the
transposition `σ = (i, last)`. -/
theorem large_coordinate {n : ℕ} (f : BooleanFunction n) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1 / 2) (hρ : 1 - 2 * p ≤ 9 / 10) {i : Fin n}
    (hc : 13 / 20 ≤ |fourierCoeff (signOf f) {i}|) :
    information f p ≤ Real.log 2 - binaryEntropy p := by
  cases n with
  | zero => exact i.elim0
  | succ k =>
    let σ : Equiv.Perm (Fin (k + 1)) := Equiv.swap i (Fin.last k)
    have hI : information (relabel σ f) p = information f p := information_relabel σ f p
    have hcoef : fourierCoeff (signOf (relabel σ f)) {Fin.last k}
        = fourierCoeff (signOf f) {i} := by
      have h := fourierCoeff_comp_perm_singleton σ (signOf f) (Fin.last k)
      have hσ : σ.symm (Fin.last k) = i := by
        simp [σ, Equiv.symm_swap, Equiv.swap_apply_right]
      rw [hσ] at h
      exact h
    have hb : 13 / 20 ≤ |mean (sectionLast (relabel σ f) true)
        - mean (sectionLast (relabel σ f) false)| := by
      rw [← fourierCoeff_singleton_last, hcoef]
      exact hc
    rw [← hI]
    exact large_coordinate_last (relabel σ f) hp0 hp1 hρ hb

/-- Sections 5–6: the CK bound for 1/20 ≤ p ≤ 1/2. -/
theorem complementary_proved : complementaryCK := by
  intro n f p hp hp'
  have hp0 : 0 ≤ p := by linarith
  have hρ0 : 0 ≤ 1 - 2 * p := by linarith
  have hρ1 : 1 - 2 * p ≤ 9 / 10 := by linarith
  by_cases hm : 13 / 20 ≤ |avg (signOf f)|
  · exact large_bias f hp0 hp' hm
  · by_cases hc : ∃ i, 13 / 20 ≤ |fourierCoeff (signOf f) {i}|
    · obtain ⟨i, hi⟩ := hc
      exact large_coordinate f hp0 hp' hρ1 hi
    · push_neg at hm hc
      have hcap := bias_inclusive_cap f hm.le (fun i => (hc i).le)
      by_cases h35 : 3 / 5 ≤ 1 - 2 * p
      · exact middle_range f h35 hρ1 hcap
      · push_neg at h35
        exact high_noise f hρ0 h35.le hcap

/-- Theorem thm:main: the Courtade–Kumar inequality. -/
theorem courtadeKumar_proved : CourtadeKumar :=
  assemble_conditional lowNoise_proved complementary_proved

end CK
