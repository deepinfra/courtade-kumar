import CK.ScalarEndpoints
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Compact-interval integral for the exact tail series

A uniformly geometric majorant justifies exchanging the power series with the
integral. The result applies to every integer tail, including tail zero.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace CourtadeKumar
namespace Scalar
open Set MeasureTheory Filter Finset

private theorem monomial_tail_integral (m : ℕ) :
    (∫ v : ℝ in (0 : ℝ)..(1 : ℝ), (1-v)*v^m) =
      1/(((m:ℝ)+1)*((m:ℝ)+2)) := by
  calc
    _ = ∫ v : ℝ in (0 : ℝ)..(1 : ℝ), v^m-v^(m+1) := by
      apply intervalIntegral.integral_congr
      intro v _
      change (1-v)*v^m = v^m-v^(m+1)
      rw [pow_succ]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub
        ((continuous_pow m).intervalIntegrable 0 1)
        ((continuous_pow (m+1)).intervalIntegrable 0 1), integral_pow, integral_pow]
      norm_num
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      field_simp
      <;> ring

/-- Integrating a geometrically dominated sequence yields the exact tail coefficients. -/
theorem hasSum_tail_integral {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) :
    HasSum (fun k : ℕ => a (k+j+1)*q^k)
      (∫ v : ℝ in (0 : ℝ)..(1 : ℝ), (1-v)*v^(2*j)/(1-q*v^2)) := by
  let F : ℕ → ℝ → ℝ := fun k v => q^k*(1-v)*v^(2*(k+j))
  have hgeo : Summable (fun k : ℕ => q^k) := summable_geometric_of_lt_one hq0 hq1
  have hF (k : ℕ) : Continuous (F k) := by dsimp [F]; fun_prop
  have hsum : HasSum (fun k : ℕ => ∫ v : ℝ in (0 : ℝ)..(1 : ℝ), F k v)
      (∫ v : ℝ in (0 : ℝ)..(1 : ℝ), (1-v)*v^(2*j)/(1-q*v^2)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k _ => q^k) (fun k => (hF k).aestronglyMeasurable)
    · intro k
      filter_upwards with v hv
      norm_num at hv
      have hv0 : 0 ≤ v := hv.1.le
      have hf0 : 0 ≤ F k v := by
        dsimp [F]
        exact mul_nonneg (mul_nonneg (pow_nonneg hq0 _) (sub_nonneg.mpr hv.2))
          (pow_nonneg hv0 _)
      rw [Real.norm_eq_abs, abs_of_nonneg hf0]
      have hp : (1-v)*v^(2*(k+j)) ≤ 1 :=
        mul_le_one₀ (by linarith) (pow_nonneg hv0 _) (pow_le_one₀ hv0 hv.2)
      have h := mul_le_mul_of_nonneg_left hp (pow_nonneg hq0 k)
      dsimp [F]
      nlinarith
    · exact ae_of_all _ (fun _ _ => hgeo)
    · exact intervalIntegrable_const
    · filter_upwards with v hv
      norm_num at hv
      have hv0 : 0 ≤ v := hv.1.le
      have hqv0 : 0 ≤ q*v^2 := mul_nonneg hq0 (sq_nonneg v)
      have hqv1 : q*v^2 < 1 :=
        (mul_le_of_le_one_right hq0 (by nlinarith [hv.2])).trans_lt hq1
      have h := (hasSum_geometric_of_lt_one hqv0 hqv1).mul_left ((1-v)*v^(2*j))
      convert h using 1
      · funext k
        dsimp [F]
        rw [mul_pow, show 2*(k+j)=2*j+2*k by omega, pow_add,
          show 2*k=2*k by rfl, pow_mul]
        ring
  convert hsum using 1
  funext k
  dsimp [F]
  rw [show (fun v : ℝ => q^k*(1-v)*v^(2*(k+j))) =
      (fun v : ℝ => q^k*((1-v)*v^(2*(k+j)))) by funext v; ring,
    intervalIntegral.integral_const_mul, monomial_tail_integral]
  rw [mul_comm (a (k+j+1)) (q^k)]
  congr 1
  unfold a
  congr 1
  push_cast
  ring

/-- The manuscript tail is an integral over the fixed compact unit interval. -/
theorem s_eq_integral {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (j : ℕ) :
    s j σ = σ^(2*j+2) *
      (∫ v : ℝ in (0 : ℝ)..(1 : ℝ), (1-v)*v^(2*j)/(1-σ^2*v^2)) := by
  have hq1 : σ^2 < 1 := by nlinarith
  rw [← (hasSum_tail_integral (sq_nonneg σ) hq1 j).tsum_eq, ← tsum_mul_left]
  unfold s
  apply tsum_congr
  intro k
  rw [show 2*(k+j+1)=(2*j+2)+2*k by omega, pow_add, pow_mul]
  ring

/-- Change of variables by a positive integer power on the unit interval. -/
theorem integral_pow_substitution {g : ℝ → ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hg : ContinuousOn g (Icc 0 1)) :
    (∫ v : ℝ in (0 : ℝ)..(1 : ℝ), g (v^j)*((j:ℝ)*v^(j-1))) =
      (∫ v : ℝ in (0 : ℝ)..(1 : ℝ), g v) := by
  have h : (∫ v : ℝ in (0 : ℝ)..(1 : ℝ),
      (g ∘ (fun v : ℝ => v^j)) v*((j:ℝ)*v^(j-1))) =
      (∫ v : ℝ in (0 : ℝ)^j..(1 : ℝ)^j, g v) := by
    apply intervalIntegral.integral_comp_mul_deriv'
      (fun v _ => hasDerivAt_pow j v) (continuous_const.mul (continuous_pow (j-1))).continuousOn
    apply hg.mono
    rintro u ⟨v, hv, rfl⟩
    norm_num at hv
    exact ⟨pow_nonneg hv.1 j, pow_le_one₀ hv.1 hv.2⟩
  simpa only [Function.comp_apply, zero_pow (by omega : j ≠ 0), one_pow] using h

end Scalar
end CourtadeKumar
