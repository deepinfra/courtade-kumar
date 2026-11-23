import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!+# Algebra of the latest manuscript's induction step

This file verifies the cancellation and coefficient comparisons in `proof.tex`.
The two information bounds and the three-bit inequality are explicit hypotheses.
The file does not assert those analytic/probabilistic hypotheses.
-/

noncomputable section
namespace CourtadeKumar

/-- The coefficient called `alpha_p` in the paper. -/
def alphaCoefficient (q J L : ℝ) : ℝ := J * L / (1 - q)

/-- The nonnegative multiplier of the second gap bound. -/
def gapMultiplier (b V v c α : ℝ) : ℝ := b / (2 * V * v * (c + α))

theorem alphaCoefficient_nonneg {q J L : ℝ}
    (hq : q < 1) (hJ : 0 ≤ J) (hL : 0 ≤ L) :
    0 ≤ alphaCoefficient q J L := by
  unfold alphaCoefficient
  exact div_nonneg (mul_nonneg hJ hL) (sub_nonneg.mpr hq.le)

theorem gapMultiplier_nonneg {b V v c α : ℝ}
    (hb : 0 ≤ b) (hV : 0 < V) (hv : 0 < v) (hc : 0 < c + α) :
    0 ≤ gapMultiplier b V v c α := by
  unfold gapMultiplier
  positivity

/-- Exact cancellation of the coefficient of `I_2(C;U)`. -/
theorem gapMultiplier_cancels {q J L b V v c : ℝ}
    (hq : q < 1) (hL : 0 < L) (hV : 0 < V) (hv : 0 < v)
    (hc : 0 < c + alphaCoefficient q J L) :
    gapMultiplier b V v c (alphaCoefficient q J L) *
        ((1 - q) * c / L + J) =
      (1 - q) * b / (2 * L * V * v) := by
  have hq' : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  have hsplit : (1 - q) * c / L + J =
      ((1 - q) / L) * (c + alphaCoefficient q J L) := by
    unfold alphaCoefficient
    field_simp [hq', hL.ne']
    ring
  have hcancel (k d m : ℝ) (hd : d ≠ 0) :
      (b / (k * d)) * (m * d) = b * m / k := by
    rw [div_mul_eq_mul_div, show b * (m * d) = (b * m) * d by ring,
      mul_div_mul_right _ _ hd]
  rw [hsplit]
  unfold gapMultiplier
  rw [hcancel (2 * V * v) _ _ (ne_of_gt hc)]
  field_simp [hL.ne', hV.ne', hv.ne']
  ring

/-- Equation `gap-combined` from the two preceding gap bounds. -/
theorem combine_gap_bounds {g Δ v R S J b u κ β lam : ℝ}
    (hlam : 0 ≤ lam)
    (hfirst : Δ + v * R + κ * u - J * b ≤ g)
    (hsecond : v * S - β * u ≤ g)
    (hcancel : lam * β = κ) :
    Δ + v * R + lam * v * S - J * b ≤ (1 + lam) * g := by
  have hscaled := mul_le_mul_of_nonneg_left hsecond hlam
  calc
    Δ + v * R + lam * v * S - J * b =
        (Δ + v * R + κ * u - J * b) + lam * (v * S - β * u) := by
      rw [← hcancel]
      ring
    _ ≤ g + lam * g := add_le_add hfirst hscaled
    _ = (1 + lam) * g := by ring

/-- Good-coordinate and comparison-correlation bounds give the first coefficient.
Here `theta` is the absolute correlation of the comparison bits. -/
theorem comparison_coefficient {b v θ : ℝ}
    (hb : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hv : 0 ≤ v) (hθ : 0 ≤ θ)
    (hcorrelation : b ≤ v ^ 2 * θ ^ 2) :
    2 * b ≤ v * θ := by
  have hb2 : 4 * b ^ 2 ≤ b := by nlinarith
  have hvθ : 0 ≤ v * θ := mul_nonneg hv hθ
  have hsq : (2 * b) ^ 2 ≤ (v * θ) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (v * θ - 2 * b)]

theorem comparison_coefficient_mul {b v θ R : ℝ}
    (hθ : 0 < θ) (hR : 0 ≤ R) (hcoef : 2 * b ≤ v * θ) :
    b * (2 * R / θ) ≤ v * R := by
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hθ).mpr
  have h := mul_le_mul_of_nonneg_right hcoef hR
  convert h using 1 <;> ring

/-- The bias-sensitive estimate `V*c <= 1` gives the second coefficient. -/
theorem bias_coefficient {V c α : ℝ}
    (hV : 0 < V) (hV1 : V ≤ 1) (hα : 0 ≤ α)
    (hc : 0 < c + α) (hVc : V * c ≤ 1) :
    1 / (2 * (1 + α)) ≤ 1 / (2 * V * (c + α)) := by
  apply one_div_le_one_div_of_le
  · positivity
  · have h := mul_le_mul_of_nonneg_right hV1 hα
    nlinarith

theorem gapMultiplier_times_v {b V v c α : ℝ}
    (hv : v ≠ 0) :
    gapMultiplier b V v c α * v = b / (2 * V * (c + α)) := by
  unfold gapMultiplier
  rw [show 2 * V * v * (c + α) = (2 * V * (c + α)) * v by ring,
    div_mul_eq_div_div, div_mul_cancel₀ _ hv]

/-- The final algebraic inference from the combined gap and three-bit bound. -/
theorem induction_gap_from_coefficients {g Δ v R S J b lam α θ : ℝ}
    (hlam : 0 ≤ lam) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hcombined : Δ + v * R + lam * v * S - J * b ≤ (1 + lam) * g)
    (hcoefR : b * (2 * R / θ) ≤ v * R)
    (hcoefS : b * (1 / (2 * (1 + α))) ≤ lam * v)
    (hthree : J ≤ S / (2 * (1 + α)) + 2 * R / θ) :
    Δ / (1 + lam) ≤ g := by
  have hpositive : 0 < 1 + lam := by linarith
  have hS' := mul_le_mul_of_nonneg_right hcoefS hS
  have hthree' := mul_le_mul_of_nonneg_left hthree hb
  simp only [div_eq_mul_inv, one_mul] at hcoefR hS' hthree'
  have hnonneg : 0 ≤ v * R + lam * v * S - J * b := by
    nlinarith
  apply (div_le_iff₀ hpositive).mpr
  nlinarith

/-- Full algebraic assembly of Lemma `ind-step` for its nondegenerate case.
The hypotheses are exactly the quantitative statements still supplied by
probability and three-bit analysis, rather than an assumed final CK bound. -/
theorem induction_gap_nondegenerate
    {g Δ q J L b V v c u R S θ : ℝ}
    (hq : q < 1) (hJ : 0 ≤ J) (hL : 0 < L)
    (hb : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hV : 0 < V) (hV1 : V ≤ 1) (hv : 0 < v)
    (hc : 0 < c + alphaCoefficient q J L) (hVc : V * c ≤ 1)
    (hθ : 0 < θ) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hcorrelation : b ≤ v ^ 2 * θ ^ 2)
    (hfirst : Δ + v * R + (1 - q) * b / (2 * L * V * v) * u - J * b ≤ g)
    (hsecond : v * S - ((1 - q) * c / L + J) * u ≤ g)
    (hthree : J ≤ S / (2 * (1 + alphaCoefficient q J L)) + 2 * R / θ) :
    Δ / (1 + gapMultiplier b V v c (alphaCoefficient q J L)) ≤ g := by
  let α := alphaCoefficient q J L
  let lam := gapMultiplier b V v c α
  have hα : 0 ≤ α := alphaCoefficient_nonneg hq hJ hL.le
  have hlam : 0 ≤ lam := gapMultiplier_nonneg hb hV hv hc
  have hcancel : lam * ((1 - q) * c / L + J) =
      (1 - q) * b / (2 * L * V * v) :=
    gapMultiplier_cancels hq hL hV hv hc
  have hcombined := combine_gap_bounds hlam hfirst hsecond hcancel
  have hcoefR : b * (2 * R / θ) ≤ v * R :=
    comparison_coefficient_mul hθ hR
      (comparison_coefficient hb hbquarter hv.le hθ.le hcorrelation)
  have hcoefS : b * (1 / (2 * (1 + α))) ≤ lam * v := by
    have h := mul_le_mul_of_nonneg_left (bias_coefficient hV hV1 hα hc hVc) hb
    dsimp [lam]
    rw [gapMultiplier_times_v hv.ne']
    simpa [div_eq_mul_inv] using h
  exact induction_gap_from_coefficients hlam hb hS hcombined hcoefR hcoefS hthree

/-- Turning a nonnegative conditional gap into a nonnegative unconditional gap. -/
theorem gap_nonneg_of_conditional {g Δ lam : ℝ}
    (hlam : 0 ≤ lam) (hΔ : 0 ≤ Δ) (hgap : Δ / (1 + lam) ≤ g) : 0 ≤ g := by
  exact (div_nonneg hΔ (by linarith)).trans hgap

end CourtadeKumar
