import CK.AvgLemmas
import CK.ProfileInduction

/-! Elementary bounds on the binary entropy used by Corollary 2.5. -/
noncomputable section
namespace CK

theorem log_five_le_two : Real.log 5 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  norm_num at h
  linarith

theorem log_twenty_le : Real.log 20 ≤ 8 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)
  norm_num at h
  linarith

/-- `h(p) ≤ 1/2` for `0 < p ≤ 1/20`, by elementary log bounds (no calculus). -/
theorem binaryEntropy_le_half_of_small (p : ℝ) (hp0 : 0 < p) (hp : p ≤ 1 / 20) :
    binaryEntropy p ≤ 1 / 2 := by
  unfold binaryEntropy
  have h20 := log_twenty_le
  have h20pos : 0 ≤ Real.log 20 := Real.log_nonneg (by norm_num)
  have h1p : 0 < 1 - p := by linarith
  have hy : Real.log (1 / (20 * p)) ≤ 1 / (20 * p) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hsplit : Real.log p = -(Real.log 20 + Real.log (1 / (20 * p))) := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_mul (by norm_num) hp0.ne',
      Real.log_one]
    ring
  have hq : 1 - 1 / (1 - p) ≤ Real.log (1 - p) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 / (1 - p))
    rw [Real.log_div (by norm_num) h1p.ne', Real.log_one] at h
    linarith
  have e1 : -p * Real.log p ≤ p * Real.log 20 + 1 / 20 - p := by
    rw [hsplit]
    have hm : p * Real.log (1 / (20 * p)) ≤ p * (1 / (20 * p) - 1) :=
      mul_le_mul_of_nonneg_left hy hp0.le
    have hc : p * (1 / (20 * p)) = 1 / 20 := by
      field_simp
      ring
    nlinarith [hm, hc]
  have e2 : -(1 - p) * Real.log (1 - p) ≤ p := by
    have hm : (1 - p) * (1 - 1 / (1 - p)) ≤ (1 - p) * Real.log (1 - p) :=
      mul_le_mul_of_nonneg_left hq h1p.le
    have hc : (1 - p) * (1 - 1 / (1 - p)) = -p := by
      field_simp
      ring
    nlinarith [hm, hc]
  have e3 : p * Real.log 20 ≤ (1 / 20) * Real.log 20 := mul_le_mul_of_nonneg_right hp h20pos
  nlinarith [e1, e2, e3, h20]

end CK

namespace CK

/-- Corollary 2.5, conditional on the profile bound and on the Bernoulli Pinsker
inequality `h(μ) ≤ ln 2 - (2μ-1)²/2`: the CK bound for `0 ≤ p ≤ 1/20`. -/
theorem lowNoiseCK_of_profile
    (hProf : LowNoiseProfileClaim)
    (hPinsker : ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 →
      binaryEntropy μ ≤ Real.log 2 - (2 * μ - 1) ^ 2 / 2) :
    ∀ (n : ℕ) (f : BooleanFunction n) (p : ℝ), 0 ≤ p → p ≤ 1 / 20 →
      information f p ≤ Real.log 2 - binaryEntropy p := by
  intro n f p hp0 hp1
  have hhalf : binaryEntropy p ≤ 1 / 2 := by
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [← h, binaryEntropy_zero]; norm_num
    · exact binaryEntropy_le_half_of_small p h hp1
  have hprof := hProf n f p hp0 hp1
  have hV : varianceProfile (mean f) = 1 - (2 * mean f - 1) ^ 2 := by
    unfold varianceProfile; ring
  rw [hV] at hprof
  exact Algebra.bias_payment (2 * mean f - 1) (binaryEntropy (mean f)) (binaryEntropy p)
    (Real.log 2) (conditionalEntropy f p) (information f p) hhalf hprof
    (hPinsker (mean f) (mean_nonneg f) (mean_le_one f)) rfl

end CK

namespace CK

/-- The whole low-noise branch reduced to Lemma 2.1 and Bernoulli Pinsker. -/
theorem lowNoiseCK_of_scalar_and_pinsker (hS : ScalarMixingClaim)
    (hPinsker : ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 →
      binaryEntropy μ ≤ Real.log 2 - (2 * μ - 1) ^ 2 / 2) : lowNoiseCK :=
  lowNoiseCK_of_profile (lowNoiseProfile_of_scalar hS) hPinsker

end CK
