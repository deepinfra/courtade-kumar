import CK.ScalarGaps
import CK.ScalarJensen

/-!
# Countable Jensen comparison for the second three-bit gap

The proven tail rescaling theorem is applied term by term, followed by Jensen
for the positive exponential tail series. Endpoint correlations are included.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace CourtadeKumar
namespace Scalar

private theorem tailLaplace_nonneg (c x : ℝ) : 0 ≤ tailLaplace c x := by
  apply tsum_nonneg
  intro k
  exact mul_nonneg (a_nonneg _) (Real.exp_pos _).le

private theorem tailLaplace_le_b_one {c x : ℝ} (hc : c ≤ 0) (hx : 0 ≤ x) :
    tailLaplace c x ≤ b (Real.log 2) 1 := by
  have ha : Summable (fun k : ℕ => a (k+2)) := (summable_nat_add_iff 2).mpr summable_a
  have heq : (∑' k : ℕ,a (k+2))=b (Real.log 2) 1 := by
    have h := b_eq_s_one (by omega : 1 ≤ (1:ℕ))
    simpa only [s,one_pow,mul_one] using h.symm
  rw [← heq]
  apply tsum_le_tsum _ (summable_tailLaplace hc hx) ha
  intro k
  have hp : Real.exp (c*((2*(k:ℝ)+3)*x)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg hc (mul_nonneg (by positivity) hx)
  exact (mul_le_mul_of_nonneg_left hp (a_nonneg _)).trans_eq (mul_one _)

/-- The rescaled-tail/Jensen lower bound at any exponent above the `j`-mean. -/
theorem second_gap_jensen {q c h : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hc : c ≤ 0) (hh : 0 ≤ h) (hmean : jMoment q ≤ h*alpha q) :
    alpha q*(s 1 (Real.exp (c*h))/Real.exp (c*h)) ≤
      (b (Real.log 2) 1/Real.exp c)*tailMass q (Real.exp c) := by
  let σ := Real.exp c
  have hσ0 : 0 < σ := Real.exp_pos _
  have hσ1 : σ ≤ 1 := Real.exp_le_one_iff.mpr hc
  have hb1 : 0 < b (Real.log 2) 1 := b_log_two_pos (by omega)
  have hw := summable_jWeight hq0.le hq1
  have hwt := summable_tailWeight hq0.le hq1 hσ0.le hσ1
  have hψ : Summable (fun n : ℕ => jWeight q n*tailLaplace c n) := by
    apply (hw.mul_left (b (Real.log 2) 1)).of_nonneg_of_le
    · intro n
      exact mul_nonneg (jWeight_nonneg hq0.le n) (tailLaplace_nonneg _ _)
    · intro n
      have hp := mul_le_mul_of_nonneg_left (tailLaplace_le_b_one hc (Nat.cast_nonneg n))
        (jWeight_nonneg hq0.le n)
      nlinarith
  have hpoint (n : ℕ) : jWeight q n*tailLaplace c n ≤
      (b (Real.log 2) 1/σ)*tailWeight q σ n := by
    by_cases hn : n=0
    · simp [hn,jWeight,tailWeight]
    have hn1 : 1 ≤ n := by omega
    have hbn : 0 < b (Real.log 2) n := b_log_two_pos hn1
    have hr := tail_rescaling hσ0 hσ1 hn1
    have hr' := (div_le_div_iff₀ (mul_pos (pow_pos hσ0 n) hb1) (mul_pos hσ0 hbn)).mp hr
    have hexp : Real.exp (c*(n:ℝ))=σ^n := by
      rw [mul_comm,Real.exp_nat_mul]
    have hp : b (Real.log 2) n*(s 1 (σ^n)/(σ^n)) ≤ b (Real.log 2) 1*s n σ/σ := by
      simp only [← mul_div_assoc]
      apply (div_le_div_iff₀ (pow_pos hσ0 n) hσ0).mpr
      nlinarith [hr']
    have hpq := mul_le_mul_of_nonneg_right hp (pow_nonneg hq0.le n)
    simp only [jWeight,tailWeight,if_neg hn,tailLaplace_eq,hexp]
    convert hpq using 1 <;> ring
  have hsum := tsum_le_tsum hpoint hψ (hwt.mul_left (b (Real.log 2) 1/σ))
  rw [tsum_mul_left] at hsum
  have hj := weighted_tailLaplace_lower hw (summable_jMoment hq0.le hq1)
    (jWeight_nonneg hq0.le) hc hh hmean
  rw [tailLaplace_eq] at hj
  exact hj.trans hsum

end Scalar
end CourtadeKumar
