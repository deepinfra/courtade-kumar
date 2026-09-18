import CK.AnalyticTargets
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Appendix F: the rational log enclosure (`LogEnclosureGoal`)

`log v = log(1+z) - log(1-z)` with `z = (v-1)/(v+1) ∈ [0, 1/3]`, expanded by the
`atanh` series; the partial sum is a lower bound (nonnegative terms) and the
tail is dominated by a geometric series.
-/
noncomputable section
namespace CK
open Finset

theorem logEnclosure_proved : LogEnclosureGoal := by
  intro N v hN hv1 hv2
  set z : ℝ := (v - 1) / (v + 1) with hz
  have hv0 : 0 < v + 1 := by linarith
  have hz0 : 0 ≤ z := by rw [hz]; apply div_nonneg <;> linarith
  have hz1 : z ≤ 1 / 3 := by rw [hz, div_le_iff₀ hv0]; linarith
  have hzlt : z < 1 := by linarith
  have hzabs : |z| < 1 := by rw [abs_of_nonneg hz0]; exact hzlt
  have hlog : Real.log v = Real.log (1 + z) - Real.log (1 - z) := by
    have h1 : 1 + z = 2 * v / (v + 1) := by rw [hz]; field_simp; ring
    have h2 : 1 - z = 2 / (v + 1) := by rw [hz]; field_simp; ring
    rw [h1, h2, Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by linarith)]
    ring
  have hf := Real.hasSum_log_sub_log_of_abs_lt_one hzabs
  rw [← hlog] at hf
  have hterm_nonneg : ∀ k : ℕ, 0 ≤ 2 * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1) :=
    fun k => by positivity
  have hpartial : (∑ i ∈ range N, 2 * (1 / (2 * (i : ℝ) + 1)) * z ^ (2 * i + 1))
      = logPartial N v := by
    simp only [logPartial]
    rw [← hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  constructor
  · rw [← hpartial]
    exact sum_le_hasSum (range N) (fun i _ => hterm_nonneg i) hf
  · have htail : HasSum (fun n : ℕ => 2 * (1 / (2 * ((n + N : ℕ) : ℝ) + 1)) * z ^ (2 * (n + N) + 1))
        (Real.log v - logPartial N v) := by
      refine (hasSum_nat_add_iff
        (f := fun n : ℕ => 2 * (1 / (2 * (n : ℝ) + 1)) * z ^ (2 * n + 1)) N).mpr ?_
      rw [hpartial, sub_add_cancel]
      exact hf
    have hz2 : z ^ 2 < 1 := by nlinarith
    have hgeo := (hasSum_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ z ^ 2) hz2).mul_left
      (2 * (1 / (2 * (N : ℝ) + 1)) * z ^ (2 * N + 1))
    have hle : ∀ n : ℕ, 2 * (1 / (2 * ((n + N : ℕ) : ℝ) + 1)) * z ^ (2 * (n + N) + 1)
        ≤ 2 * (1 / (2 * (N : ℝ) + 1)) * z ^ (2 * N + 1) * (z ^ 2) ^ n := by
      intro n
      have e : z ^ (2 * (n + N) + 1) = z ^ (2 * N + 1) * (z ^ 2) ^ n := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
      rw [e]
      have hden : (1 : ℝ) / (2 * ((n + N : ℕ) : ℝ) + 1) ≤ 1 / (2 * (N : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hp : 0 ≤ z ^ (2 * N + 1) * (z ^ 2) ^ n := by positivity
      nlinarith [hden, hp]
    have hcomp := hasSum_le hle htail hgeo
    have hz2' : 0 < 1 - z ^ 2 := by linarith
    have e : 2 * (1 / (2 * (N : ℝ) + 1)) * z ^ (2 * N + 1) * (1 - z ^ 2)⁻¹
        = logTail N v := by
      simp only [logTail]
      rw [← hz]
      field_simp
    linarith

end CK
