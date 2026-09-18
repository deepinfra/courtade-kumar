import CK.InteriorEstimate
import CK.EndpointSmall
import CK.EndpointLarge
import CK.Bridge
import CK.Transfer
import CK.Pinsker
import CK.Constants

/-!
# Theorem thm:linear-mixing and the low-noise branch (manuscript Sec. 3.6, Cor. cor:low)

Assembly of the scalar mixing inequality `q(d) ≥ (p/500) t²` from the three regimes
established earlier:

* `mixing_interior`       : `0 < t ≤ 22/25` via `interior_product` + `transfer_product`;
* `mixing_endpoint_small` : `t > 22/25`, `ε = (1-t)/2 ≤ p` via `gain_dominance`,
  `transfer_gain` and `endpoint_interval`;
* `mixing_endpoint_large` : `t > 22/25`, `p ≤ ε` via `endpoint_normalized` + `transfer_relative`;

together with the trivial regimes `t = 0` and `t = 1` from `CK.Bridge`.
Then `linear_scalar_mixing` (thm:linear-mixing), `scalar_mixing` (v9.1 Lemma 2.1) and
`lowNoise_proved` (cor:low).
-/
noncomputable section
namespace CK

/-- Interior regime of the proof of `lem:mixing`: for `0 < t ≤ 22/25`,
`q(d) ≥ (1999/1250000) p t² / ln 2 ≥ (p/500) t²` (eq:interiorproduct + product transfer). -/
theorem mixing_interior {p t nu d : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht0 : 0 < t)
    (ht1 : t ≤ 22 / 25) (hnu : 0 ≤ nu) (hsum : nu + t ≤ 1) :
    p / 500 * t ^ 2 ≤ (pairEntropy nu ((1 - 2 * p) * t) - pairEntropy nu t)
      + pairEntropy nu ((1 - 2 * p) * t) * d ^ 2 - 2 * (binaryEntropy p * t) * d := by
  have hp2 : p < 1 / 2 := by linarith
  have ht1' : t < 1 := by linarith
  have hg := interior_product hp0 hp1 ht0 ht1
  have hpt : 0 ≤ p * t ^ 2 := by positivity
  have hg0 : 0 ≤ 1999 / 1250000 * p * t ^ 2 := by positivity
  have htr := transfer_product (l := binaryEntropy p * t) hp0 hp2 ht0 ht1' hnu hsum hg0 hg d
  have hlog := AppF.row_log_q2_hi
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : 1999 / 1250000 * p * t ^ 2 / (7 / 10) ≤ 1999 / 1250000 * p * t ^ 2 / Real.log 2 :=
    div_le_div_of_nonneg_left hg0 hlog0 hlog.le
  have h2 : p / 500 * t ^ 2 ≤ 1999 / 1250000 * p * t ^ 2 / (7 / 10) := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hpt]
  linarith

/-- Endpoint regime `ε = (1-t)/2 ≤ p` (app:rsmall): gain dominance `K₀ ≥ M₀/3 ≥ (1/2)² M₀`
transfers `q₀(d) ≤ q(d)`, and `q₀(d) ≥ (23/3600) p t ≥ (p/500) t²`. -/
theorem mixing_endpoint_small {p t nu d : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20)
    (ht : 22 / 25 ≤ t) (ht1 : t < 1) (hr : (1 - t) / 2 ≤ p) (hnu : 0 ≤ nu) (hsum : nu + t ≤ 1)
    (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2) :
    p / 500 * t ^ 2 ≤ (pairEntropy nu ((1 - 2 * p) * t) - pairEntropy nu t)
      + pairEntropy nu ((1 - 2 * p) * t) * d ^ 2 - 2 * (binaryEntropy p * t) * d := by
  have hp2 : p < 1 / 2 := by linarith
  have ht0 : 0 < t := by linarith
  have hgd := gain_dominance hp0 hp1 ht ht1 hr
  have hM0 : 0 ≤ eta ((1 - 2 * p) * t) :=
    eta_nonneg (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 2 * p) ht0.le])
      (by nlinarith [mul_nonneg hp0.le ht0.le])
  have hD : (1 / 2 : ℝ) ^ 2 * eta ((1 - 2 * p) * t) ≤ eta ((1 - 2 * p) * t) - eta t := by
    nlinarith
  have htg := transfer_gain (l := binaryEntropy p * t) hp0 hp2 ht0 ht1 hnu hsum hD hd0 hd
  have hei := endpoint_interval hp0 hp1 ht ht1 hr hd0 hd
  have hcmp : p / 500 * t ^ 2 ≤ 23 / 3600 * p * t := by
    nlinarith [mul_nonneg (mul_nonneg hp0.le ht0.le) (sub_nonneg.mpr ht1.le)]
  linarith

/-- Endpoint regime `p ≤ ε = (1-t)/2` (app:rlarge / app:normalized): the retained-denominator
transfer gives `q(d) ≥ (K₀M₀ - ℓ²)/M₀ ≥ (453/40000) p t ≥ (p/500) t²`. -/
theorem mixing_endpoint_large {p t nu d : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20)
    (ht : 22 / 25 ≤ t) (ht1 : t < 1) (hr : p ≤ (1 - t) / 2) (hnu : 0 ≤ nu) (hsum : nu + t ≤ 1) :
    p / 500 * t ^ 2 ≤ (pairEntropy nu ((1 - 2 * p) * t) - pairEntropy nu t)
      + pairEntropy nu ((1 - 2 * p) * t) * d ^ 2 - 2 * (binaryEntropy p * t) * d := by
  have hp2 : p < 1 / 2 := by linarith
  have ht0 : 0 < t := by linarith
  obtain ⟨hnum, hbd⟩ := endpoint_normalized hp0 hp1 ht ht1 hr
  have htr := transfer_relative (d := d) hp0 hp2 ht0 ht1 hnu hsum hnum
  have hcmp : p / 500 * t ^ 2 ≤ 453 / 40000 * p * t := by
    nlinarith [mul_nonneg (mul_nonneg hp0.le ht0.le) (sub_nonneg.mpr ht1.le)]
  linarith

/-- Theorem thm:linear-mixing (v11 eq:mixing): the p/500 two-posterior mixing inequality. -/
theorem linear_scalar_mixing : LinearScalarMixingClaim := by
  intro p a b d hp0 hp1 ha0 ha1 hb0 hb1 hd0 hd1
  have hsum := nu_add_t_le_one ha0 ha1 hb0 hb1
  have hnu : 0 ≤ |a + b - 1| := abs_nonneg _
  have ht0 : 0 ≤ |a - b| := abs_nonneg _
  have ht1 : |a - b| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hsq : (a - b) ^ 2 = |a - b| ^ 2 := (sq_abs (a - b)).symm
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · -- t = 0: a = b and the slack is d² h(a) ≥ 0
    have hab : a = b := by
      have := abs_eq_zero.mp h0.symm
      linarith
    rw [hab]
    calc p / 500 * (b - b) ^ 2 = 0 := by ring
      _ ≤ scalarSlack p d b b := scalarSlack_nonneg_of_eq hb0 hb1
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · -- t = 1: the corners (0,1), (1,0), slack ≥ p/4
    have hend := scalarSlack_endpoints hp0 hp1 hd0 hd1
    rcases abs_sub_eq_one_cases ha0 ha1 hb0 hb1 h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
      have e : p / 500 * ((0:ℝ) - 1) ^ 2 = p / 500 := by ring
      rw [e]
      linarith [hend.1]
    · rw [ha, hb]
      have e : p / 500 * ((1:ℝ) - 0) ^ 2 = p / 500 := by ring
      rw [e]
      linarith [hend.2]
  -- 0 < t < 1: centered coordinates
  rw [scalarSlack_eq, hsq]
  rcases le_or_lt |a - b| (22 / 25) with hle | hgt
  · exact mixing_interior hp0 hp1 h0 hle hnu hsum
  · rcases le_or_lt ((1 - |a - b|) / 2) p with hr | hr
    · exact mixing_endpoint_small hp0 hp1 hgt.le h1 hr hnu hsum hd0 hd1
    · exact mixing_endpoint_large hp0 hp1 hgt.le h1 hr.le hnu hsum

/-- v9.1 Lemma 2.1 (p²/25), implied by the linear version on p ≤ 1/20. -/
theorem scalar_mixing : ScalarMixingClaim := by
  intro p a b d hp0 hp1 ha0 ha1 hb0 hb1 hd0 hd1
  have h := linear_scalar_mixing p a b d hp0 hp1 ha0 ha1 hb0 hb1 hd0 hd1
  have hm := Algebra.linear_margin_dominates p hp0.le hp1
  calc p ^ 2 / 25 * (a - b) ^ 2 ≤ p / 500 * (a - b) ^ 2 :=
        mul_le_mul_of_nonneg_right hm (sq_nonneg _)
    _ ≤ scalarSlack p d a b := h

/-- Corollary cor:low: the Courtade–Kumar bound for 0 ≤ p ≤ 1/20. -/
theorem lowNoise_proved : lowNoiseCK := lowNoiseCK_of_scalar scalar_mixing

end CK
