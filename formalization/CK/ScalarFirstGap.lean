import CK.ScalarJensen
import CK.ScalarIntegral

/-!
# Integrated countable Jensen bound for the first three-bit gap

The exponentially damped derivative series is dominated by the summable first
moment. Dominated convergence and the exponential supporting line produce the
paper's lower bound at any exponent above the weighted mean.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace CourtadeKumar
namespace Scalar
open Set MeasureTheory Filter

/-- Exponentially damped derivative series of the divergence generating function. -/
def laplaceK (q t : ℝ) : ℝ := ∑' n : ℕ,kWeight q n*Real.exp (-t*n)

private theorem continuousOn_laplaceK {q z : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ContinuousOn (laplaceK q) (Icc 0 z) := by
  unfold laplaceK
  apply continuousOn_tsum (u := kWeight q)
    (fun n => (by fun_prop : Continuous (fun t : ℝ => kWeight q n*Real.exp (-t*n))).continuousOn)
    (summable_kWeight hq0 hq1)
  intro n t ht
  have hn : 0 ≤ kWeight q n*Real.exp (-t*n) :=
    mul_nonneg (kWeight_nonneg hq0 n) (Real.exp_pos _).le
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  exact (mul_le_mul_of_nonneg_left
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [ht.1]) (Nat.cast_nonneg n)))
    (kWeight_nonneg hq0 n)).trans_eq (mul_one _)

/-- Elementary integral of a decaying exponential. -/
theorem integral_exp_neg {h : ℝ} (hh : 0 < h) (z : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..z, Real.exp (-t*h)) = (1-Real.exp (-z*h))/h := by
  have heq : (fun t : ℝ => Real.exp (-t*h))=(fun t : ℝ => Real.exp ((-h)*t)) := by
    funext t
    congr 1
    ring
  rw [heq,intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr (ne_of_gt hh)),
    integral_exp]
  simp only [mul_zero,Real.exp_zero,smul_eq_mul]
  rw [show (-h)*z=-z*h by ring]
  field_simp [ne_of_gt hh]
  ring

private theorem integral_kWeight_exp (q z : ℝ) (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..z,kWeight q n*Real.exp (-t*n)) =
      a n*q^n-a n*(q*Real.exp (-z))^n := by
  by_cases hn : n=0
  · simp [hn,kWeight,a_zero]
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [intervalIntegral.integral_const_mul,integral_exp_neg hnpos z]
  have heq : (q*Real.exp (-z))^n=q^n*Real.exp (-z*n) := by
    rw [mul_pow,← Real.exp_nat_mul]
    congr 1
    congr 1
    ring
  rw [heq]
  unfold kWeight
  field_simp
  ring

/-- Exact integral identity for the first gap, with all sum exchanges justified. -/
theorem integral_laplaceK {q z : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hz : 0 ≤ z) :
    (∫ t : ℝ in (0 : ℝ)..z,laplaceK q t) =
      divergenceSeries q-divergenceSeries (q*Real.exp (-z)) := by
  have hw := summable_kWeight hq0 hq1
  have hsum : HasSum
      (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..z,kWeight q n*Real.exp (-t*n))
      (∫ t : ℝ in (0 : ℝ)..z,laplaceK q t) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => kWeight q n)
      (fun n => (by fun_prop : Continuous (fun t : ℝ => kWeight q n*Real.exp (-t*n))).aestronglyMeasurable)
    · intro n
      filter_upwards with t ht
      have ht0 : 0 ≤ t := (Set.uIoc_of_le hz ▸ ht).1.le
      rw [Real.norm_eq_abs,abs_of_nonneg
        (mul_nonneg (kWeight_nonneg hq0 n) (Real.exp_pos _).le)]
      exact (mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg n)))
        (kWeight_nonneg hq0 n)).trans_eq (mul_one _)
    · exact ae_of_all _ (fun _ _ => hw)
    · exact intervalIntegrable_const
    · filter_upwards with t ht
      have ht0 : 0 ≤ t := (Set.uIoc_of_le hz ▸ ht).1.le
      exact (summable_weighted_exp hw (kWeight_nonneg hq0) (by linarith : -t≤0)).hasSum
  rw [← hsum.tsum_eq]
  have hqexp0 : 0 ≤ q*Real.exp (-z) := mul_nonneg hq0 (Real.exp_pos _).le
  have hqexp1 : q*Real.exp (-z) ≤ 1 :=
    (mul_le_of_le_one_right hq0 (Real.exp_le_one_iff.mpr (by linarith))).trans hq1.le
  have ha := summable_divergenceSeries hq0 hq1.le
  have hb := summable_divergenceSeries hqexp0 hqexp1
  unfold divergenceSeries
  rw [← ha.tsum_sub hb]
  exact tsum_congr (integral_kWeight_exp q z)

/-- First-gap Jensen lower bound at any exponent above the actual weighted mean. -/
theorem first_gap_jensen {q z h : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hz : 0 ≤ z) (hh : 0 < h) (hmean : kMoment q ≤ h*kMass q) :
    kMass q*(1-Real.exp (-z*h))/h ≤
      divergenceSeries q-divergenceSeries (q*Real.exp (-z)) := by
  have hi : (∫ t : ℝ in (0 : ℝ)..z,kMass q*Real.exp (-t*h)) ≤
      (∫ t : ℝ in (0 : ℝ)..z,laplaceK q t) := by
    apply intervalIntegral.integral_mono_on hz
      ((by fun_prop : Continuous (fun t : ℝ => kMass q*Real.exp (-t*h))).intervalIntegrable 0 z)
      ((continuousOn_laplaceK hq0 hq1).intervalIntegrable_of_Icc hz)
    intro t ht
    exact weighted_exp_lower (summable_kWeight hq0 hq1) (summable_kMoment hq0 hq1)
      (kWeight_nonneg hq0) (by linarith [ht.1] : -t≤0) hmean
  rw [intervalIntegral.integral_const_mul,integral_exp_neg hh z,
    integral_laplaceK hq0 hq1 hz] at hi
  simpa only [mul_div_assoc] using hi

end Scalar
end CourtadeKumar
