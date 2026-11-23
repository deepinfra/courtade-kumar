import CK.BiasDivergence

/-! Both Bernoulli-divergence estimates, with an explicit KL formula bridge. -/

noncomputable section
namespace CourtadeKumar
open Set MeasureTheory

theorem binaryDivergenceNats_eq_kl {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 < b) (hb1 : b < 1) :
    binaryDivergenceNats a b =
      a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) := by
  by_cases ha : a = 0
  · subst a
    simp [one_div, Real.log_inv]
  by_cases ha' : a = 1
  · subst a
    simp [one_div, Real.log_inv]
  have hane : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha')
  have hbne : 1 - b ≠ 0 := by linarith
  rw [Real.log_div ha hb0.ne', Real.log_div hane hbne]
  unfold binaryDivergenceNats Real.binEntropy
  simp only [Real.log_inv]
  ring

private theorem binaryDivergenceNats_lower_interior {a b : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) :
    2 * (a - b) ^ 2 ≤ binaryDivergenceNats a b := by
  have hcont : ContinuousOn (fun t : ℝ =>
      (1 - t) / ((b + t * (a - b)) * (1 - b - t * (a - b)))) (uIcc 0 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    have ht0 : 0 ≤ t := by simpa using ht.1
    have ht1 : t ≤ 1 := by simpa using ht.2
    have hz : 0 < b + t * (a - b) ∧ b + t * (a - b) < 1 := by
      have hseg := (convex_Ioo (0 : ℝ) 1 : Convex ℝ (Ioo (0 : ℝ) 1)) hb ha
        (sub_nonneg.mpr ht1) ht0 (by ring : (1 - t) + t = 1)
      simpa only [smul_eq_mul, show (1 - t) * b + t * a = b + t * (a - b) by ring] using hseg
    exact mul_ne_zero hz.1.ne' (by linarith [hz.2])
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1, 4 * (1 - t) ≤
      (1 - t) / ((b + t * (a - b)) * (1 - b - t * (a - b))) := by
    intro t ht
    have hseg := (convex_Ioo (0 : ℝ) 1 : Convex ℝ (Ioo (0 : ℝ) 1)) hb ha
      (sub_nonneg.mpr ht.2) ht.1 (by ring : (1 - t) + t = 1)
    have hz : 0 < b + t * (a - b) ∧ b + t * (a - b) < 1 := by
      simpa only [smul_eq_mul, show (1 - t) * b + t * a = b + t * (a - b) by ring] using hseg
    have hden : 0 < (b + t * (a - b)) * (1 - b - t * (a - b)) :=
      mul_pos hz.1 (by linarith [hz.2])
    apply (le_div_iff₀ hden).mpr
    have hsq := mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg (2 * (b + t * (a - b)) - 1))
    nlinarith
  have hint := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((by fun_prop : Continuous (fun t : ℝ => 4 * (1 - t))).intervalIntegrable _ _)
    hcont.intervalIntegrable hpoint
  have hval : (∫ t : ℝ in (0 : ℝ)..1, 4 * (1 - t)) = 2 := by
    have hs := intervalIntegral.integral_sub (μ := volume) (f := fun _ : ℝ => (1 : ℝ))
      (g := fun t : ℝ => t) (a := (0 : ℝ)) (b := 1)
      (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul, hs]
    norm_num
  rw [hval] at hint
  rw [binaryDivergenceNats_taylor_integral ha hb]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hint (sq_nonneg (a - b))

/-- Bernoulli Pinsker estimate for every reference mean in the open unit interval. -/
theorem binaryDivergenceNats_lower {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ binaryDivergenceNats a b := by
  have hclosed : IsClosed {x : ℝ | 2 * (x - b) ^ 2 ≤ binaryDivergenceNats x b} := by
    apply isClosed_le (by fun_prop)
    unfold binaryDivergenceNats
    fun_prop
  have hsub : Ioo (0 : ℝ) 1 ⊆ {x : ℝ | 2 * (x - b) ^ 2 ≤ binaryDivergenceNats x b} :=
    fun x hx => binaryDivergenceNats_lower_interior hx ⟨hb0, hb1⟩
  have h := hclosed.closure_subset_iff.mpr hsub
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at h
  exact h ⟨ha0, ha1⟩

def binaryDivergenceBits (a b : ℝ) : ℝ := binaryDivergenceNats a b / Real.log 2

/-- Both inequalities in the manuscript's `binary-divergence-comparison` lemma. -/
theorem binaryDivergenceBits_bounds {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 1 / 2 ≤ b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 / Real.log 2 ≤ binaryDivergenceBits a b ∧
      binaryDivergenceBits a b ≤
        Real.log (1 / b) / ((1 - b) ^ 2 * Real.log 2) * (a - b) ^ 2 := by
  have hbpos : 0 < b := by linarith
  constructor
  · exact div_le_div_of_nonneg_right (binaryDivergenceNats_lower ha0 ha1 hbpos hb1) log_two_pos.le
  · have h := div_le_div_of_nonneg_right (binaryDivergenceNats_upper ha0 ha1 hb0 hb1) log_two_pos.le
    unfold binaryDivergenceBits
    convert h using 1
    rw [one_div, Real.log_inv]
    field_simp [log_two_pos.ne', ne_of_gt (sub_pos.mpr hb1)]

end CourtadeKumar
