import CK.ScalarMeans

/-! # Positivity and exact normalization of the common Jensen exponent -/

noncomputable section
namespace CourtadeKumar
namespace Scalar

/-- The common Jensen exponent is positive in the nondegenerate channel range. -/
theorem commonExponent_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < commonExponent q := by
  have hb := b_log_two_pos (by omega : 1 ≤ (1:ℕ))
  have hk := kMass_pos hq0 hq1
  have ha := alpha_pos hq0 hq1
  have hq : 0 < 1-q := by linarith
  unfold commonExponent
  positivity

/-- The `k` moment bound in the unnormalized form used by countable Jensen. -/
theorem kMoment_le_commonExponent {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    kMoment q ≤ commonExponent q*kMass q := by
  have h := (means_order hq0 hq1).1.trans (means_order hq0 hq1).2
  exact (div_le_iff₀ (kMass_pos hq0 hq1)).mp h

/-- The `j` moment bound in the unnormalized form used by countable Jensen. -/
theorem jMoment_le_commonExponent {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    jMoment q ≤ commonExponent q*alpha q := by
  exact (div_le_iff₀ (alpha_pos hq0 hq1)).mp (jMean_le_commonExponent hq0 hq1)

/-- Clearing the positive denominator gives the exact exponent normalization. -/
theorem commonExponent_identity {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    commonExponent q*(1+alpha q)*((1-q)*alpha q) =
      2*b (Real.log 2) 1*kMass q := by
  have ha := alpha_pos hq0 hq1
  have hq : 0 < 1-q := by linarith
  have hd : (1+alpha q)*(1-q)*alpha q ≠ 0 := by positivity
  unfold commonExponent
  calc
    (2*b (Real.log 2) 1*kMass q/((1+alpha q)*(1-q)*alpha q)) *
        (1+alpha q)*((1-q)*alpha q)
      = (2*b (Real.log 2) 1*kMass q/((1+alpha q)*(1-q)*alpha q)) *
          ((1+alpha q)*(1-q)*alpha q) := by ring
    _ = _ := div_mul_cancel₀ _ hd

end Scalar
end CourtadeKumar
