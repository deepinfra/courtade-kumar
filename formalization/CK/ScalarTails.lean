import CK.ScalarCertificates
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Tactic.FieldSimp

/-!
# Integral tail representation and the complete coefficient inequality

The finite coefficient sequence `b (log 2) j` is identified with
`∫₀¹ u^(2j)/(1+u) du` for `j ≥ 1`. This yields positivity and
`j b_j ≤ 1/4`. Finite-sum algebra then proves the convolution comparison
for every index, including the exact small cases from `ScalarCertificates`.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable section
namespace CourtadeKumar
namespace Scalar

open Finset MeasureTheory

private theorem tail_integrable (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => x^(2*n) / (1+x)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (continuousOn_id.pow _) (continuousOn_const.add continuousOn_id)
  intro x hx
  have hx0 : 0 ≤ x := by
    norm_num at hx
    exact hx.1
  change 1+x ≠ 0
  linarith

private theorem tail_integral_zero :
    (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), x^(2*0) / (1+x)) = Real.log 2 := by
  simp only [mul_zero, pow_zero]
  have h := intervalIntegral.integral_comp_add_left (fun x : ℝ => 1/x)
    (a := (0 : ℝ)) (b := 1) 1
  norm_num only [zero_add, one_add_one_eq_two] at h
  rw [h, integral_one_div_of_pos (by norm_num) (by norm_num)]
  norm_num

private theorem a_succ_difference (n : ℕ) :
    a (n+1) = 1 / (2*(n : ℝ)+1) - 1 / (2*(n : ℝ)+2) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : 2*(n : ℝ)+1 ≠ 0 := by linarith
  have h2 : 2*(n : ℝ)+2 ≠ 0 := by linarith
  unfold a
  push_cast
  rw [show 2*((n : ℝ)+1)*(2*((n : ℝ)+1)-1) =
    (2*(n : ℝ)+2)*(2*(n : ℝ)+1) by ring]
  field_simp [h1, h2]
  ring

private theorem tail_integral_step (n : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), x^(2*(n+1)) / (1+x)) =
      (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), x^(2*n) / (1+x)) - a (n+1) := by
  have hp : (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), x^(2*n) / (1+x)) -
      (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), x^(2*(n+1)) / (1+x)) = a (n+1) := by
    rw [← intervalIntegral.integral_sub (tail_integrable n) (tail_integrable (n+1))]
    calc (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), x^(2*n) / (1+x) - x^(2*(n+1)) / (1+x))
        = ∫ x : ℝ in (0 : ℝ)..(1 : ℝ), x^(2*n) - x^(2*n+1) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hx0 : 0 ≤ x := by
            norm_num at hx
            exact hx.1
          have hxne : 1+x ≠ 0 := by linarith
          rw [show 2*(n+1) = 2*n+2 by omega]
          simp only [pow_add, pow_one]
          field_simp [hxne]
          ring
      _ = 1/(2*(n : ℝ)+1) - 1/(2*(n : ℝ)+2) := by
          rw [intervalIntegral.integral_sub ((continuous_pow _).intervalIntegrable 0 1) ((continuous_pow _).intervalIntegrable 0 1)]
          simp only [integral_pow]
          norm_num
          ring
      _ = a (n+1) := (a_succ_difference n).symm
  linarith

private theorem partial_succ (n : ℕ) : partialSum (n+1) = partialSum n + a (n+1) := by
  unfold partialSum
  rw [sum_range_succ]

private theorem e_succ (n : ℕ) : e (n+1) = e n + (n+1 : ℕ) * a (n+1) := by
  unfold e
  rw [sum_range_succ]

/-- Integral representation before imposing the exceptional convention `b₀ = 1`. -/
theorem tail_integral_eq (n : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), x^(2*n) / (1+x)) = Real.log 2 - partialSum n := by
  induction n with
  | zero => simpa [partialSum] using tail_integral_zero
  | succ n ih =>
      rw [tail_integral_step, ih, partial_succ]
      ring

/-- The manuscript's integral formula for every positive tail index. -/
theorem b_integral {n : ℕ} (hn : 1 ≤ n) :
    b (Real.log 2) n = ∫ x : ℝ in (0 : ℝ)..(1 : ℝ), x^(2*n) / (1+x) := by
  rw [b, if_neg (by omega), tail_integral_eq]

theorem b_log_two_nonneg (n : ℕ) : 0 ≤ b (Real.log 2) n := by
  rcases n with _ | n
  · simp
  · rw [b_integral (by omega)]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact div_nonneg (pow_nonneg hx.1 _) (by linarith [hx.1])

/-- The uniform tail estimate needed in the convolution bound. -/
theorem weighted_tail_le_quarter {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * b (Real.log 2) n ≤ 1/4 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [b_integral (by omega)]
  have hmono : (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), x^(2*(m+1))/(1+x)) ≤
      (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), x^(2*m+1)/2) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (tail_integrable (m+1))
      (((continuous_pow _).div_const 2).intervalIntegrable 0 1)
    intro x hx
    have hxden : 0 < 1+x := by linarith [hx.1]
    have hp : 0 ≤ x^(2*m+1) := pow_nonneg hx.1 _
    rw [show 2*(m+1) = (2*m+1)+1 by omega, pow_succ]
    apply (div_le_iff₀ hxden).2
    have hprod := mul_nonneg hp (sub_nonneg.mpr hx.2)
    nlinarith
  have hint : (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), x^(2*m+1)/2) = 1/(4*((m : ℝ)+1)) := by
    rw [intervalIntegral.integral_div, integral_pow]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    norm_num
    field_simp
    ring
  rw [hint] at hmono
  have hmul := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg (m+1))
  have hcancel : ((m+1 : ℕ) : ℝ) * (1/(4*((m : ℝ)+1))) = 1/4 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    field_simp [show (m : ℝ)+1 ≠ 0 by linarith]
    ring
  simpa only [hcancel] using hmul

/-- A simple lower bound from `1+x ≤ 2` on the integration interval. -/
theorem weighted_tail_lower {n : ℕ} (hn : 1 ≤ n) :
    (1/2 : ℝ) ≤ (2*(n : ℝ)+1) * b (Real.log 2) n := by
  have hmono : (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), x^(2*n)/2) ≤ b (Real.log 2) n := by
    rw [b_integral hn]
    apply intervalIntegral.integral_mono_on (by norm_num)
      (((continuous_pow _).div_const 2).intervalIntegrable 0 1) (tail_integrable n)
    intro x hx
    apply div_le_div_of_nonneg_left (pow_nonneg hx.1 _) (by linarith [hx.1])
    linarith [hx.2]
  have hint : (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), x^(2*n)/2) = 1/(2*(2*(n : ℝ)+1)) := by
    rw [intervalIntegral.integral_div, integral_pow]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    norm_num
    field_simp
  rw [hint] at hmono
  have hmul := mul_le_mul_of_nonneg_left hmono
    (by positivity : 0 ≤ 2*(n : ℝ)+1)
  have hcancel : (2*(n : ℝ)+1) * (1/(2*(2*(n : ℝ)+1))) = 1/2 := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    field_simp
    ring
  simpa only [hcancel] using hmul

theorem b_log_two_pos {n : ℕ} (hn : 1 ≤ n) : 0 < b (Real.log 2) n := by
  have h := weighted_tail_lower hn
  have hnonneg := b_log_two_nonneg n
  by_contra hnot
  have hzero : b (Real.log 2) n = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  rw [hzero] at h
  norm_num at h

private theorem b_succ {n : ℕ} (hn : 1 ≤ n) :
    b (Real.log 2) (n+1) = b (Real.log 2) n - a (n+1) := by
  simp only [b, if_neg (by omega : n+1 ≠ 0), if_neg (by omega : n ≠ 0), partial_succ]
  ring

/-- The ratio of the two coefficient weights in the manuscript. -/
def weightRatio (n : ℕ) : ℝ := 2*(2*(n : ℝ)-1) * b (Real.log 2) n

theorem weightRatio_eq {n : ℕ} (hn : 1 ≤ n) :
    weightRatio n = b (Real.log 2) n / ((n : ℝ) * a n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold weightRatio a
  field_simp
  ring

/-- Elementary alternative to the stochastic-order step for `k_* ≤ j_*`. -/
theorem weightRatio_succ_gt {n : ℕ} (hn : 1 ≤ n) :
    weightRatio n < weightRatio (n+1) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb := weighted_tail_lower hn
  have hbp := b_log_two_pos hn
  have hden : 0 < 2*(n : ℝ)+2 := by linarith
  have hidentity : (weightRatio (n+1) - weightRatio n) * (2*(n : ℝ)+2) =
      4*(2*(n : ℝ)+2)*b (Real.log 2) n - 2 := by
    unfold weightRatio
    rw [b_succ hn, a_succ_difference]
    push_cast
    field_simp
    ring
  have hp : 0 < (weightRatio (n+1)-weightRatio n) * (2*(n : ℝ)+2) := by
    rw [hidentity]
    nlinarith
  have := (mul_pos_iff_of_pos_right hden).mp hp
  linarith

theorem weightRatio_strictMono : StrictMono (fun n : ℕ => weightRatio (n+1)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact weightRatio_succ_gt (by omega)

/-- Finite tail-sum identity used in the coefficient comparison. -/
theorem sum_b_range {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ range n, b (Real.log 2) j =
      1 + e n + (n : ℝ) * b (Real.log 2) n - Real.log 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [e, a, sum_range_succ] ; ring
  | succ n hn ih =>
    rw [sum_range_succ, ih, e_succ, b_succ hn]
    push_cast
    ring

/-- The large-index convolution estimate, proved for all positive indices. -/
theorem convolution_upper {n : ℕ} (hn : 1 ≤ n) :
    convolution (Real.log 2) n ≤ (e n + 5/4 - Real.log 2)/4 := by
  have hsum : convolution (Real.log 2) n ≤
      (1/4 : ℝ) * ∑ j ∈ range n, b (Real.log 2) j := by
    unfold convolution
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    calc (∑ j ∈ range n, ((j+1 : ℕ) : ℝ) * b (Real.log 2) (j+1) * b (Real.log 2) (n-(j+1)))
        ≤ ∑ j ∈ range n, (1/4 : ℝ) * b (Real.log 2) (n-(j+1)) := by
          apply sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_right (weighted_tail_le_quarter (by omega))
            (b_log_two_nonneg _)
      _ = (1/4 : ℝ) * ∑ j ∈ range n, b (Real.log 2) j := by
          rw [← mul_sum]
          congr 1
          simpa only [Nat.sub_sub, Nat.add_comm] using sum_range_reflect (b (Real.log 2)) n
  have hnq := weighted_tail_le_quarter hn
  rw [sum_b_range hn] at hsum
  linarith

/-- Full coefficient inequality from the latest three-bit proof, all indices. -/
theorem coefficient_convolution {n : ℕ} (hn : 1 ≤ n) :
    convolution (Real.log 2) n ≤ 2 * b (Real.log 2) 1 * e n := by
  by_cases h1 : n = 1
  · subst n
    have h := coefficientDeficit_one (Real.log 2)
    unfold coefficientDeficit at h
    linarith
  by_cases hsmall : n ≤ 8
  · have h := coefficientDeficit_log_two_pos_small (by omega) hsmall
    unfold coefficientDeficit at h
    linarith
  · exact (convolution_upper hn).trans (large_index_log_two (by omega)).le

/-- Except at index one, the convolution comparison is strict. -/
theorem coefficient_convolution_strict {n : ℕ} (hn : 2 ≤ n) :
    convolution (Real.log 2) n < 2 * b (Real.log 2) 1 * e n := by
  by_cases hsmall : n ≤ 8
  · have h := coefficientDeficit_log_two_pos_small hn hsmall
    unfold coefficientDeficit at h
    linarith
  · exact (convolution_upper (by omega)).trans_lt (large_index_log_two (by omega))

end Scalar
end CourtadeKumar
