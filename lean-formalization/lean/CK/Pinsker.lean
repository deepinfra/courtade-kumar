import CK.EntropyBounds
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Complex.ExponentialBounds

/-!
# Bernoulli Pinsker inequality: `h(μ) ≤ ln 2 - (2μ-1)²/2` on `[0,1]`

Proof: for `μ ∈ [1/2, 1)` the function `F(x) = ln 2 - (2x-1)²/2 - h(x)` has
`F(1/2) = 0` and `F'(x) = log x - log(1-x) - 2(2x-1) ≥ 0`, the last inequality
being the first term of the `atanh` series; the case `μ ≤ 1/2` follows by the
symmetry `h(1-μ) = h(μ)`.
-/
noncomputable section
namespace CK

theorem binaryEntropy_eq_binEntropy : binaryEntropy = Real.binEntropy := by
  funext p
  unfold binaryEntropy Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  ring

/-- First term of the `atanh` series: `2x ≤ log(1+x) - log(1-x)` for `0 ≤ x < 1`. -/
theorem two_mul_le_log_sub_log (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    2 * x ≤ Real.log (1 + x) - Real.log (1 - x) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := x)
    (by rw [abs_of_nonneg hx0]; exact hx1)
  have h0 := le_hasSum h 0 (fun j _ => by positivity)
  simpa using h0

theorem binEntropy_half : Real.binEntropy (1 / 2) = Real.log 2 := by
  unfold Real.binEntropy
  norm_num
  ring

theorem hasDerivAt_F (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y : ℝ => Real.log 2 - (2 * y - 1) ^ 2 / 2 - Real.binEntropy y)
      (Real.log x - Real.log (1 - x) - 2 * (2 * x - 1)) x := by
  have hb := Real.hasDerivAt_binEntropy (p := x) hx0.ne' hx1.ne
  have h1 : HasDerivAt (fun y : ℝ => 2 * y - 1) 2 x := by
    simpa using ((hasDerivAt_id x).const_mul 2).sub_const 1
  have h2 : HasDerivAt (fun y : ℝ => (2 * y - 1) ^ 2 / 2) (2 * (2 * x - 1)) x := by
    have h := (h1.pow 2).div_const 2
    convert h using 1
    norm_num
  have hq := ((hasDerivAt_const x (Real.log 2)).sub h2).sub hb
  convert hq using 1
  ring

theorem pinsker_upper (μ : ℝ) (h1 : 1 / 2 ≤ μ) (h2 : μ < 1) :
    binaryEntropy μ ≤ Real.log 2 - (2 * μ - 1) ^ 2 / 2 := by
  rw [binaryEntropy_eq_binEntropy]
  have hmono : MonotoneOn (fun y : ℝ => Real.log 2 - (2 * y - 1) ^ 2 / 2 - Real.binEntropy y)
      (Set.Ico (1 / 2 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico _ _)
    · intro x hx
      exact (hasDerivAt_F x (by linarith [hx.1]) hx.2).continuousAt.continuousWithinAt
    · rw [interior_Ico]
      intro x hx
      exact (hasDerivAt_F x (by linarith [hx.1]) hx.2).differentiableAt.differentiableWithinAt
    · rw [interior_Ico]
      intro x hx
      rw [(hasDerivAt_F x (by linarith [hx.1]) hx.2).deriv]
      have hm0 : 0 ≤ 2 * x - 1 := by linarith [hx.1]
      have hm1 : 2 * x - 1 < 1 := by linarith [hx.2]
      have key := two_mul_le_log_sub_log (2 * x - 1) hm0 hm1
      have e1 : Real.log (1 + (2 * x - 1)) = Real.log x + Real.log 2 := by
        rw [show (1 + (2 * x - 1)) = x * 2 by ring, Real.log_mul (by linarith [hx.1]) (by norm_num)]
      have e2 : Real.log (1 - (2 * x - 1)) = Real.log (1 - x) + Real.log 2 := by
        rw [show (1 - (2 * x - 1)) = (1 - x) * 2 by ring,
          Real.log_mul (by linarith [hx.2]) (by norm_num)]
      rw [e1, e2] at key
      linarith
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ico (1 / 2 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have hμ : μ ∈ Set.Ico (1 / 2 : ℝ) 1 := ⟨h1, h2⟩
  have := hmono hhalf hμ h1
  simp only at this
  rw [binEntropy_half] at this
  linarith

/-- Bernoulli Pinsker inequality on `[0,1]`. -/
theorem pinsker (μ : ℝ) (h0 : 0 ≤ μ) (h1 : μ ≤ 1) :
    binaryEntropy μ ≤ Real.log 2 - (2 * μ - 1) ^ 2 / 2 := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  rcases eq_or_lt_of_le h1 with hμ1 | hμ1
  · rw [hμ1, binaryEntropy_one]; norm_num; linarith
  rcases eq_or_lt_of_le h0 with hμ0 | hμ0
  · rw [← hμ0, binaryEntropy_zero]; norm_num; linarith
  rcases le_or_lt (1 / 2) μ with hh | hh
  · exact pinsker_upper μ hh hμ1
  · have h := pinsker_upper (1 - μ) (by linarith) (by linarith)
    rw [binaryEntropy_symm] at h
    have e : (2 * (1 - μ) - 1) ^ 2 = (2 * μ - 1) ^ 2 := by ring
    rw [e] at h
    exact h

/-- The low-noise branch of CK, conditional only on Lemma 2.1. -/
theorem lowNoiseCK_of_scalar (hS : ScalarMixingClaim) : lowNoiseCK :=
  lowNoiseCK_of_scalar_and_pinsker hS pinsker

end CK
