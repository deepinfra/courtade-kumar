import CK.ScalarFirstGap
import CK.ScalarSecondGap
import CK.ScalarAssembly
import CK.ScalarParameters

/-!
# The three-bit scalar inequality

Both countable Jensen bounds are evaluated at the proved common exponent.
The strict tail-series barrier then supplies the manuscript's exact scalar
inequality, including the deterministic endpoint of the comparison channel.
-/

noncomputable section
namespace CourtadeKumar
namespace Scalar

theorem three_bit_nats {ρ σ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    (1 - ρ ^ 2) * alpha (ρ ^ 2) <
      (divergenceNats ρ - divergenceNats (ρ * σ)) / (2 * (1 + alpha (ρ ^ 2))) +
        2 * (ρ ^ 2 * divergenceNats σ - divergenceNats (ρ * σ)) / σ := by
  have hq0 : 0 < ρ ^ 2 := sq_pos_of_pos hρ0
  have hq1 : ρ ^ 2 < 1 := by nlinarith
  have hρabs : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  have hρσabs : |ρ * σ| < 1 := by
    rw [abs_of_pos (mul_pos hρ0 hσ0)]
    exact (mul_le_of_le_one_right hρ0.le hσ1).trans_lt hρ1
  let h := commonExponent (ρ ^ 2)
  let t := Real.exp (Real.log σ * h)
  have hh : 0 < h := commonExponent_pos hq0 hq1
  have ht : 0 < t := Real.exp_pos _
  have hc : Real.log σ ≤ 0 := Real.log_nonpos hσ0.le hσ1
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hc hh.le)
  have hα : 0 < alpha (ρ ^ 2) := alpha_pos hq0 hq1
  have hJ : 0 < (1 - ρ ^ 2) * alpha (ρ ^ 2) := mul_pos (sub_pos.mpr hq1) hα
  have hB : 0 < b (Real.log 2) 1 := b_log_two_pos (by omega)
  have hL : 0 < 1 + alpha (ρ ^ 2) := by linarith
  have heσ : Real.exp (Real.log σ) = σ := Real.exp_log hσ0
  have heσsq : Real.exp (-(-2 * Real.log σ)) = σ ^ 2 := by
    rw [show -(-2 * Real.log σ) = Real.log σ + Real.log σ by ring, Real.exp_add, heσ]
    ring
  have het : Real.exp (-(-2 * Real.log σ) * h) = t ^ 2 := by
    change Real.exp (-(-2 * Real.log σ) * h) = Real.exp (Real.log σ * h) ^ 2
    rw [show -(-2 * Real.log σ) * h = Real.log σ * h + Real.log σ * h by ring, Real.exp_add]
    ring
  have hfirst := first_gap_jensen (q := ρ ^ 2) (z := -2 * Real.log σ) hq0.le hq1
    (by linarith) hh (kMoment_le_commonExponent hq0 hq1)
  rw [het, heσsq, ← mul_pow, divergenceSeries_eq_divergenceNats hρabs,
    divergenceSeries_eq_divergenceNats hρσabs] at hfirst
  have hs := second_gap_jensen (q := ρ ^ 2) (c := Real.log σ) hq0 hq1 hc hh.le
    (jMoment_le_commonExponent hq0 hq1)
  change alpha (ρ ^ 2) * (s 1 t / t) ≤ (b (Real.log 2) 1 / Real.exp (Real.log σ)) *
    tailMass (ρ ^ 2) (Real.exp (Real.log σ)) at hs
  rw [heσ] at hs
  have hsecond : (1 - ρ ^ 2) * alpha (ρ ^ 2) * s 1 t / t ≤
      b (Real.log 2) 1 * (ρ ^ 2 * divergenceNats σ - divergenceNats (ρ * σ)) / σ := by
    calc
      _ = (1 - ρ ^ 2) * (alpha (ρ ^ 2) * (s 1 t / t)) := by ring
      _ ≤ (1 - ρ ^ 2) * ((b (Real.log 2) 1 / σ) * tailMass (ρ ^ 2) σ) :=
        mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hq1.le)
      _ = b (Real.log 2) 1 * ((1 - ρ ^ 2) * tailMass (ρ ^ 2) σ) / σ := by ring
      _ = _ := by rw [second_gap_divergence hρ0.le hρ1 hσ0.le hσ1]
  exact scalar_barrier_assembly hJ hB hh hL ht hσ0
    (commonExponent_identity hq0 hq1) hfirst hsecond (tail_series_barrier ht ht1)

end Scalar

namespace Spec

/-- The independently stated scalar target, with no analytic assumptions left. -/
theorem threeBit : ThreeBitTarget := by
  intro ρ σ hρ0 hρ1 hσ0 hσ1
  have hq1 : ρ ^ 2 < 1 := by nlinarith
  have hρabs : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  have hnats := Scalar.three_bit_nats hρ0 hρ1 hσ0 hσ1
  have h := div_lt_div_of_pos_right hnats log_two_pos
  have hleft : ((1 - ρ ^ 2) * Scalar.alpha (ρ ^ 2)) / Real.log 2 = ρ ^ 2 - divergence ρ := by
    rw [Scalar.alpha_series_identity (sq_nonneg ρ) hq1,
      Scalar.divergenceSeries_eq_divergenceNats hρabs, divergence_eq_divergenceNats]
    field_simp [log_two_pos.ne']
  have hright :
      ((divergenceNats ρ - divergenceNats (ρ * σ)) / (2 * (1 + Scalar.alpha (ρ ^ 2))) +
        2 * (ρ ^ 2 * divergenceNats σ - divergenceNats (ρ * σ)) / σ) / Real.log 2 =
      (divergence ρ - divergence (ρ * σ)) / (2 * (1 + Scalar.alpha (ρ ^ 2))) +
        2 * (ρ ^ 2 * divergence σ - divergence (ρ * σ)) / σ := by
    simp only [divergence_eq_divergenceNats, div_eq_mul_inv]
    ring
  rw [hleft, hright, Scalar.alpha_eq_paper hρabs] at h
  exact h

end Spec
end CourtadeKumar
