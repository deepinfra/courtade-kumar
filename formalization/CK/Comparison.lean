import CK.Entropy
import CK.Spec

/-!
# Pointwise comparison estimates and the single-crossing summation principle

These are parts of Lemma `comparison-calculus`. The matched-profile inequality
and concavity of the full comparison function remain separate obligations.
-/

noncomputable section
namespace CourtadeKumar.Spec
open scoped BigOperators

theorem divergence_eq_divergenceNats (t : ℝ) :
    divergence t = divergenceNats t / Real.log 2 := by
  unfold divergence entropy divergenceNats
  field_simp [ne_of_gt log_two_pos]

theorem divergence_nonneg (t : ℝ) : 0 ≤ divergence t := by
  have h := entropyBits_le_one ((1 + t) / 2)
  change 0 ≤ 1 - entropyBits ((1 + t) / 2)
  linarith

theorem divergence_le_square {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    divergence t ≤ t ^ 2 := by
  rw [divergence_eq_divergenceNats]
  apply (div_le_iff₀ log_two_pos).mpr
  exact divergenceNats_upper ht0 ht1

theorem divergence_scaling {ρ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    divergence (ρ * t) ≤ ρ ^ 2 * divergence t := by
  simp only [divergence_eq_divergenceNats]
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right
    (divergenceNats_scaling hρ0 hρ1 ht0 ht1) log_two_pos.le

theorem binaryProfile_domain {x d : ℝ} (hx : |x| < 1) (hxd : |x| + |d| ≤ 1) :
    0 < 1 - x ^ 2 ∧ |d| ≤ 1 - x ^ 2 ∧
      |d / (1 + x)| ≤ 1 ∧ |d / (1 - x)| ≤ 1 := by
  have hx0 : -1 < x := (abs_lt.mp hx).1
  have hx1 : x < 1 := (abs_lt.mp hx).2
  have hplus : 0 < 1 + x := by linarith
  have hminus : 0 < 1 - x := by linarith
  have hV : 0 < 1 - x ^ 2 := by nlinarith [mul_pos hplus hminus]
  have hxabs : 0 ≤ |x| := abs_nonneg x
  have hxsq : x ^ 2 ≤ |x| := by
    have := mul_nonneg hxabs (sub_nonneg.mpr hx.le)
    nlinarith [sq_abs x]
  refine ⟨hV, by linarith, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hplus]
    apply (div_le_iff₀ hplus).mpr
    linarith [neg_le_abs x]
  · rw [abs_div, abs_of_pos hminus]
    apply (div_le_iff₀ hminus).mpr
    linarith [le_abs_self x]

/-- The explicit profile is bounded by its quadratic divergence. -/
theorem binaryProfile_le_quadratic {x d : ℝ}
    (hx : |x| < 1) (hxd : |x| + |d| ≤ 1) :
    binaryProfile x d ≤ d ^ 2 / (1 - x ^ 2) := by
  have hdom := binaryProfile_domain hx hxd
  have hplus : 0 < 1 + x := by linarith [(abs_lt.mp hx).1]
  have hminus : 0 < 1 - x := by linarith [(abs_lt.mp hx).2]
  have hp := divergence_le_square (abs_le.mp hdom.2.2.1).1 (abs_le.mp hdom.2.2.1).2
  have hm := divergence_le_square (abs_le.mp hdom.2.2.2).1 (abs_le.mp hdom.2.2.2).2
  have hp' := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (1 + x) / 2)
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (1 - x) / 2)
  have heq : (1 + x) / 2 * (d / (1 + x)) ^ 2 +
      (1 - x) / 2 * (d / (1 - x)) ^ 2 = d ^ 2 / (1 - x ^ 2) := by
    field_simp [hplus.ne', hminus.ne', hdom.1.ne']
    ring
  unfold binaryProfile
  linarith

/-- First inequality in Lemma `comparison-calculus`: `I(B;C) <= T(C)`. -/
theorem binaryProfile_le_variance {x d : ℝ}
    (hx : |x| < 1) (hxd : |x| + |d| ≤ 1) :
    binaryProfile x d ≤ 1 - x ^ 2 := by
  have hdom := binaryProfile_domain hx hxd
  refine (binaryProfile_le_quadratic hx hxd).trans ?_
  apply (div_le_iff₀ hdom.1).mpr
  have hmul := mul_self_le_mul_self (abs_nonneg d) hdom.2.1
  nlinarith [sq_abs d]

theorem binaryProfile_nonneg {x d : ℝ} (hx : |x| < 1) :
    0 ≤ binaryProfile x d := by
  have hplus : 0 ≤ (1 + x) / 2 := by linarith [(abs_lt.mp hx).1]
  have hminus : 0 ≤ (1 - x) / 2 := by linarith [(abs_lt.mp hx).2]
  exact add_nonneg (mul_nonneg hplus (divergence_nonneg _))
    (mul_nonneg hminus (divergence_nonneg _))

end CourtadeKumar.Spec

namespace CourtadeKumar
open scoped BigOperators

/-- The infinite-series sign-change principle used by the comparison proof.
All summability and sign assumptions are explicit; both sides are actual tsums. -/
theorem singleCrossing_tsum_nonpos {a w : ℕ → ℝ} (k : ℕ)
    (ha : Summable a) (hwa : Summable (fun i => w i * a i))
    (hsum : ∑' i, a i = 0) (hw : Antitone w)
    (hleft : ∀ i, i < k → a i ≤ 0)
    (hright : ∀ i, k ≤ i → 0 ≤ a i) :
    ∑' i, w i * a i ≤ 0 := by
  have hpoint : ∀ i, w i * a i - w k * a i ≤ 0 := by
    intro i
    by_cases hi : i < k
    · have hweight : 0 ≤ w i - w k := sub_nonneg.mpr (hw hi.le)
      have h := mul_nonpos_of_nonneg_of_nonpos hweight (hleft i hi)
      nlinarith
    · have hi' : k ≤ i := Nat.le_of_not_gt hi
      have hweight : w i - w k ≤ 0 := sub_nonpos.mpr (hw hi')
      have h := mul_nonpos_of_nonpos_of_nonneg hweight (hright i hi')
      nlinarith
  have h := tsum_nonpos hpoint
  rw [hwa.tsum_sub (ha.mul_left (w k)), tsum_mul_left, hsum, mul_zero, sub_zero] at h
  exact h

end CourtadeKumar
