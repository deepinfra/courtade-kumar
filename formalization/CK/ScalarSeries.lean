import CK.ScalarCertificates
import Mathlib.Analysis.PSeries

/-!
# Positive tail series and the final scalar barrier

This module proves summability of the manuscript's tails on the closed unit
interval, the two-term lower bound, and the strict final scalar barrier. The
reductions to this barrier (rescaling the tails and Jensen comparisons of the
means) remain separate obligations.
-/

noncomputable section
namespace CourtadeKumar
namespace Scalar

open Finset

theorem a_le_inv_square (k : ℕ) : a k ≤ 1/(k : ℝ)^2 := by
  by_cases hk : k = 0
  · simp [hk]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
  unfold a
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem summable_a : Summable a :=
  (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ))).of_nonneg_of_le
    a_nonneg a_le_inv_square

theorem summable_scaled_a {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Summable (fun k : ℕ => a k * t^(2*k)) := by
  apply summable_a.of_nonneg_of_le
  · intro k
    exact mul_nonneg (a_nonneg k) (pow_nonneg ht _)
  · intro k
    calc a k * t^(2*k) ≤ a k * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ ht ht1) (a_nonneg k)
      _ = a k := mul_one _

/-- The exact tail series from the latest paper. -/
def s (j : ℕ) (t : ℝ) : ℝ :=
  ∑' k : ℕ, a (k+j+1) * t^(2*(k+j+1))

theorem summable_s {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (j : ℕ) :
    Summable (fun k : ℕ => a (k+j+1) * t^(2*(k+j+1))) := by
  simpa only [Nat.add_assoc] using
    (summable_nat_add_iff (j+1)).mpr (summable_scaled_a ht ht1)

theorem s_nonneg {t : ℝ} (ht : 0 ≤ t) (j : ℕ) : 0 ≤ s j t := by
  apply tsum_nonneg
  intro k
  exact mul_nonneg (a_nonneg _) (pow_nonneg ht _)

/-- Dropping all but the first two nonnegative terms gives the paper's barrier. -/
theorem s_one_lower {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t^4/12 + t^6/30 ≤ s 1 t := by
  have h := (summable_s ht ht1 1).sum_le_tsum (range 2)
    (fun k _ => mul_nonneg (a_nonneg _) (pow_nonneg ht _))
  calc t^4/12 + t^6/30
      = ∑ k ∈ range 2, a (k+1+1) * t^(2*(k+1+1)) := by
          norm_num [sum_range_succ, a]
          ring
    _ ≤ s 1 t := h

/-- The manuscript's final scalar barrier, for its actual infinite tail series. -/
theorem tail_series_barrier {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    2 * b (Real.log 2) 1 < (1-t^2)/2 + 4*s 1 t/t := by
  have h := tail_barrier ht ht1 (s_one_lower ht.le ht1)
  rw [b_one]
  linarith

end Scalar
end CourtadeKumar
