import CK.ScalarMeans

/-!
# Endpoint identities for the scalar power series

The uniform tail bound proves the total coefficient mass exactly. This supplies
both endpoint divergence identities and identifies the paper's `b_j` with the
actual tail `s_j(1)`.
-/

noncomputable section
namespace CourtadeKumar
namespace Scalar
open Finset Filter Topology

/-- The exact coefficient mass, including the boundary of the convergence disk. -/
theorem tsum_a_eq_log_two : (∑' n : ℕ, a n) = Real.log 2 := by
  have hb : Tendsto (fun n : ℕ => b (Real.log 2) (n+1)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => b_log_two_nonneg (n+1))
      (g := fun n : ℕ => (1/4 : ℝ) * (1 / ((n:ℝ)+1)))
    · intro n
      have h := weighted_tail_le_quarter (n := n+1) (by omega)
      have hn : (0 : ℝ) < (n:ℝ)+1 := by positivity
      simp only [one_div]
      apply (le_mul_inv_iff₀ hn).2
      simpa only [Nat.cast_add, Nat.cast_one, mul_comm, one_div, mul_assoc] using h
    · simpa only [mul_zero] using
        tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
  have hp : Tendsto (fun n : ℕ => partialSum (n+1)) atTop (𝓝 (∑' n : ℕ, a n)) := by
    exact summable_a.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)
  have hsub : Tendsto (fun n : ℕ => b (Real.log 2) (n+1)) atTop
      (𝓝 (Real.log 2 - ∑' n : ℕ, a n)) := by
    simpa only [b, if_neg (Nat.succ_ne_zero _)] using tendsto_const_nhds.sub hp
  have he := tendsto_nhds_unique hb hsub
  linarith

/-- The series divergence agrees with binary divergence on the closed unit interval. -/
theorem divergenceSeries_eq_divergenceNats_closed {rho : ℝ} (hrho : |rho| ≤ 1) :
    divergenceSeries (rho^2) = divergenceNats rho := by
  rcases lt_or_eq_of_le hrho with hlt | heq
  · exact divergenceSeries_eq_divergenceNats hlt
  have hsq : rho^2 = 1 := by nlinarith [sq_abs rho]
  have hdiv : divergenceNats rho = Real.log 2 := by
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp heq with hp | hm
    · simpa [hp] using divergenceNats_one
    · simpa [hm] using divergenceNats_even 1
  simpa only [hsq, divergenceSeries, one_pow, mul_one, hdiv] using tsum_a_eq_log_two

/-- Full binary-divergence series, including `t = ±1`. -/
theorem hasSum_divergenceNats_closed {t : ℝ} (ht : |t| ≤ 1) :
    HasSum (fun n : ℕ => a (n+1)*t^(2*(n+1))) (divergenceNats t) := by
  have hq : t^2 ≤ 1 := by nlinarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
  have ha := summable_divergenceSeries (sq_nonneg t) hq
  have hs : Summable (fun n : ℕ => a (n+1)*(t^2)^(n+1)) :=
    (summable_nat_add_iff 1).mpr ha
  have heq : (∑' n : ℕ, a (n+1)*(t^2)^(n+1)) = divergenceNats t := by
    have h := divergenceSeries_eq_divergenceNats_closed ht
    unfold divergenceSeries at h
    rw [ha.tsum_eq_zero_add] at h
    simpa only [a_zero, zero_mul, zero_add] using h
  convert hs.hasSum using 1
  · funext n
    rw [pow_mul]
  · exact heq.symm

/-- The notation `b_j = s_j(1)` from the manuscript, for every positive index. -/
theorem b_eq_s_one {j : ℕ} (hj : 1 ≤ j) : b (Real.log 2) j = s j 1 := by
  have h := summable_a.sum_add_tsum_nat_add (j+1)
  rw [tsum_a_eq_log_two] at h
  have hb : b (Real.log 2) j = Real.log 2 - partialSum j := by
    simp only [b, if_neg (by omega : j ≠ 0)]
  rw [hb]
  unfold s partialSum
  simp only [one_pow, mul_one, Nat.add_assoc]
  linarith

end Scalar
end CourtadeKumar
