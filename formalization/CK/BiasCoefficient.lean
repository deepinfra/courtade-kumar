import CK.Entropy

/-! The coefficient `c(mu)` in Lemma `biased-comparison`. -/

noncomputable section
namespace CourtadeKumar

def biasCoefficientUpper (μ : ℝ) : ℝ := Real.log (1 / μ) / (4 * (1 - μ) ^ 2)

def biasCoefficient (μ : ℝ) : ℝ :=
  if 1 / 2 ≤ μ then biasCoefficientUpper μ else biasCoefficientUpper (1 - μ)

theorem biasCoefficientUpper_pos {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    0 < biasCoefficientUpper μ := by
  unfold biasCoefficientUpper
  apply div_pos
  · apply Real.log_pos
    exact (one_lt_div hμ0).mpr hμ1
  · have h : 0 < 1 - μ := sub_pos.mpr hμ1
    positivity

theorem quadratic_mul_biasCoefficientUpper {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    4 * μ * (1 - μ) * biasCoefficientUpper μ ≤ 1 := by
  have hden : 0 < 1 - μ := sub_pos.mpr hμ1
  have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 / μ)
  have hm := mul_le_mul_of_nonneg_left hlog hμ0.le
  have heq : μ * (1 / μ - 1) = 1 - μ := by
    field_simp [hμ0.ne']
  rw [heq] at hm
  have hform : 4 * μ * (1 - μ) * biasCoefficientUpper μ =
      (μ * Real.log (1 / μ)) / (1 - μ) := by
    unfold biasCoefficientUpper
    field_simp [hden.ne']
    ring
  rw [hform]
  exact (div_le_one hden).mpr hm

theorem biasCoefficient_pos {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    0 < biasCoefficient μ := by
  unfold biasCoefficient
  split_ifs
  · exact biasCoefficientUpper_pos hμ0 hμ1
  · exact biasCoefficientUpper_pos (by linarith) (by linarith)

/-- The second assertion of Lemma `biased-comparison`, with no analytic premises. -/
theorem quadratic_mul_biasCoefficient {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    4 * μ * (1 - μ) * biasCoefficient μ ≤ 1 := by
  unfold biasCoefficient
  split_ifs
  · exact quadratic_mul_biasCoefficientUpper hμ0 hμ1
  · have h := quadratic_mul_biasCoefficientUpper (by linarith : 0 < 1 - μ)
      (by linarith : 1 - μ < 1)
    convert h using 1
    ring

end CourtadeKumar
