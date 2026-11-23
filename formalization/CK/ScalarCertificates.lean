import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases

/-!
# Exact scalar certificates for the November 20 manuscript

These declarations implement the rational coefficient comparisons and the
cubic/quintic barrier in `proof.tex`, subsection "The three-bit lemma", at
source commit `45ad4866a41e04722f2cfcef4129a1050e59d3ca`.

The logarithm enclosure follows from Mathlib's checked numerical log-two bounds.
The finite coefficient certificates are exact rational arithmetic. The
polynomial barrier uses an explicit nonnegative factorization, equivalent to
the manuscript's tangent argument. This module does not establish the infinite
series rescaling/Jensen reductions connecting these certificates to the
three-bit information inequality.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable section
namespace CourtadeKumar
namespace Scalar

open Finset

/-- The binary divergence coefficients, with the harmless value `a 0 = 0`. -/
def a (k : ℕ) : ℝ := 1 / (2 * (k : ℝ) * (2 * (k : ℝ) - 1))

/-- `∑_{k=1}^n a_k`; including index zero does not alter the sum. -/
def partialSum (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), a k

/-- The paper's `e_n = ∑_{k=1}^n k a_k`. -/
def e (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), (k : ℝ) * a k

/-- Finite representation of the tails, with the paper's convention `b₀ = 1`.
For `L = log 2`, identifying this with an infinite tail is a separate analytic
step. -/
def b (L : ℝ) (n : ℕ) : ℝ := if n = 0 then 1 else L - partialSum n

/-- The coefficient on the left of the manuscript's convolution estimate. -/
def convolution (L : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range (n + 1), (j : ℝ) * b L j * b L (n - j)

/-- The deficit whose nonnegativity proves the coefficient estimate. -/
def coefficientDeficit (L : ℝ) (n : ℕ) : ℝ :=
  2 * b L 1 * e n - convolution L n

/-- The lower bound used in the paper: lower endpoint in the positive term,
upper endpoint in both factors of every subtracted summand. -/
def rationalDeficit (n : ℕ) : ℝ :=
  2 * b (6931 / 10000) 1 * e n - convolution (6932 / 10000) n

@[simp] theorem a_zero : a 0 = 0 := by norm_num [a]
@[simp] theorem b_zero (L : ℝ) : b L 0 = 1 := by simp [b]
@[simp] theorem b_one (L : ℝ) : b L 1 = L - 1 / 2 := by
  norm_num [b, partialSum, a, sum_range_succ]

theorem a_nonneg (k : ℕ) : 0 ≤ a k := by
  cases k with
  | zero => simp
  | succ k =>
    unfold a
    apply one_div_nonneg.mpr
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    push_cast
    nlinarith

theorem e_nonneg (n : ℕ) : 0 ≤ e n := by
  exact sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k) (a_nonneg k)

theorem b_mono {L M : ℝ} (hLM : L ≤ M) (n : ℕ) : b L n ≤ b M n := by
  unfold b
  split_ifs <;> linarith

theorem b_nonneg_le_eight {L : ℝ} (hL : (6931 / 10000 : ℝ) ≤ L)
    {n : ℕ} (hn : n ≤ 8) : 0 ≤ b L n := by
  interval_cases n <;> norm_num [b, partialSum, a, sum_range_succ] <;> linarith

theorem convolution_mono_le_eight {L M : ℝ}
    (hL : (6931 / 10000 : ℝ) ≤ L) (hLM : L ≤ M)
    {n : ℕ} (hn : n ≤ 8) : convolution L n ≤ convolution M n := by
  apply sum_le_sum
  intro j hj
  have hjn : j ≤ n := by have := mem_range.mp hj; omega
  have hj8 : j ≤ 8 := hjn.trans hn
  have hnj8 : n - j ≤ 8 := (Nat.sub_le n j).trans hn
  have hjpos : 0 ≤ b L j := b_nonneg_le_eight hL hj8
  have hnjpos : 0 ≤ b L (n-j) := b_nonneg_le_eight hL hnj8
  have hM : (6931 / 10000 : ℝ) ≤ M := hL.trans hLM
  have hMnjpos : 0 ≤ b M (n-j) := b_nonneg_le_eight hM hnj8
  calc (j : ℝ) * b L j * b L (n-j)
      = (j : ℝ) * (b L j * b L (n-j)) := by ring
    _ ≤ (j : ℝ) * (b M j * b M (n-j)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg j)
      exact mul_le_mul (b_mono hLM j) (b_mono hLM (n-j)) hnjpos
        (b_nonneg_le_eight hM hj8)
    _ = (j : ℝ) * b M j * b M (n-j) := by ring

theorem rationalDeficit_le {L : ℝ}
    (hlo : (6931 / 10000 : ℝ) ≤ L) (hhi : L ≤ (6932 / 10000 : ℝ))
    {n : ℕ} (hn : n ≤ 8) : rationalDeficit n ≤ coefficientDeficit L n := by
  have hc := convolution_mono_le_eight hlo hhi hn
  have hp := mul_le_mul_of_nonneg_right (b_mono hlo 1) (e_nonneg n)
  unfold rationalDeficit coefficientDeficit
  linarith

/-- The seven exact margins printed in the latest manuscript. -/
theorem rationalDeficit_margins :
    (40 / 100000 : ℝ) < rationalDeficit 2 ∧
    (280 / 100000 : ℝ) < rationalDeficit 3 ∧
    (565 / 100000 : ℝ) < rationalDeficit 4 ∧
    (855 / 100000 : ℝ) < rationalDeficit 5 ∧
    (1135 / 100000 : ℝ) < rationalDeficit 6 ∧
    (1395 / 100000 : ℝ) < rationalDeficit 7 ∧
    (1640 / 100000 : ℝ) < rationalDeficit 8 := by
  norm_num [rationalDeficit, convolution, b, partialSum, e, a, sum_range_succ]

theorem coefficientDeficit_pos_small {L : ℝ}
    (hlo : (6931 / 10000 : ℝ) ≤ L) (hhi : L ≤ (6932 / 10000 : ℝ))
    {n : ℕ} (hnlo : 2 ≤ n) (hnhi : n ≤ 8) : 0 < coefficientDeficit L n := by
  have h := rationalDeficit_le hlo hhi hnhi
  have hp : 0 < rationalDeficit n := by
    interval_cases n <;>
      norm_num [rationalDeficit, convolution, b, partialSum, e, a, sum_range_succ]
  exact hp.trans_le h

@[simp] theorem coefficientDeficit_one (L : ℝ) : coefficientDeficit L 1 = 0 := by
  norm_num [coefficientDeficit, convolution, b, partialSum, e, a, sum_range_succ]
  ring

/-- Exact ninth partial sum; this is stronger than the manuscript's `e₉ > 1.03`. -/
theorem e_nine_exact : e 9 = (1593269 / 1531530 : ℝ) := by
  norm_num [e, a, sum_range_succ]

theorem e_nine_gt : (103 / 100 : ℝ) < e 9 := by
  rw [e_nine_exact]
  norm_num

/-- The large-index numerical step, independently of the tail-series estimates
which must supply the input `E ≥ e₉`. -/
theorem large_index_arithmetic {L E : ℝ}
    (hL : (6931 / 10000 : ℝ) ≤ L) (hE : (103 / 100 : ℝ) ≤ E) :
    (E + 5 / 4 - L) / 4 < 2 * (L - 1 / 2) * E := by
  have hp : 0 ≤ (L - 6931 / 10000) * (E - 103 / 100) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The paper's log-two interval, discharged by Mathlib's stronger enclosure. -/
theorem log_two_interval :
    (6931 / 10000 : ℝ) < Real.log 2 ∧ Real.log 2 < (6932 / 10000 : ℝ) := by
  constructor
  · linarith [Real.log_two_gt_d9]
  · linarith [Real.log_two_lt_d9]

/-- The actual small-index convolution inequality, without a log-bound hypothesis. -/
theorem coefficientDeficit_log_two_pos_small {n : ℕ}
    (hnlo : 2 ≤ n) (hnhi : n ≤ 8) : 0 < coefficientDeficit (Real.log 2) n :=
  coefficientDeficit_pos_small log_two_interval.1.le log_two_interval.2.le hnlo hnhi

theorem e_monotone : Monotone e := by
  intro m n hmn
  unfold e
  apply sum_le_sum_of_subset_of_nonneg
  · exact range_mono (by omega)
  · intro k _ _
    exact mul_nonneg (Nat.cast_nonneg k) (a_nonneg k)

theorem e_gt_of_nine_le {n : ℕ} (hn : 9 ≤ n) : (103 / 100 : ℝ) < e n :=
  e_nine_gt.trans_le (e_monotone hn)

/-- The complete large-index numerical step with the actual paper constants. -/
theorem large_index_log_two {n : ℕ} (hn : 9 ≤ n) :
    (e n + 5 / 4 - Real.log 2) / 4 < 2 * b (Real.log 2) 1 * e n := by
  rw [b_one]
  exact large_index_arithmetic log_two_interval.1.le (e_gt_of_nine_le hn).le

/-- Cubic and quintic terms retained from `4 s₁(t) / t`. -/
def barrier (t : ℝ) : ℝ := (1 - t^2) / 2 + t^3 / 3 + 2 * t^5 / 15

/-- The tangent remainder factors as a square times a nonnegative polynomial. -/
theorem tangent_remainder (a t : ℝ) :
    t^3 / 3 + 2 * t^5 / 15 -
      (a^3 / 3 + 2 * a^5 / 15 + (a / 2 + a^3 / 3) * (t^2 - a^2)) =
    (t - a)^2 * (6*a^3 + 12*a^2*t + 8*a*t^2 + 5*a + 4*t^3 + 10*t) / 30 := by
  ring

theorem tangent_minorant {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    a^3 / 3 + 2*a^5 / 15 + (a / 2 + a^3 / 3) * (t^2 - a^2)
      ≤ t^3 / 3 + 2*t^5 / 15 := by
  have hp : 0 ≤ (t - a)^2 *
      (6*a^3 + 12*a^2*t + 8*a*t^2 + 5*a + 4*t^3 + 10*t) / 30 := by
    positivity
  rw [← tangent_remainder] at hp
  linarith

/-- Exact barrier lower bound at the manuscript's tangent point `11/15`. -/
theorem barrier_lower {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1480699 / 3796875 : ℝ) ≤ barrier t := by
  have h := tangent_minorant (a := (11 / 15 : ℝ)) (by norm_num) ht
  have ht2 : t^2 ≤ 1 := by nlinarith
  norm_num at h
  unfold barrier
  nlinarith

theorem barrier_gt_seven_eighteenths {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (7 / 18 : ℝ) < barrier t := by
  have h := barrier_lower ht ht1
  have : (7 / 18 : ℝ) < 1480699 / 3796875 := by norm_num
  exact this.trans_le h

/-- The final polynomial barrier exceeds the actual logarithmic target. -/
theorem barrier_gt_log_target {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    2 * Real.log 2 - 1 < barrier t := by
  have hb := barrier_gt_seven_eighteenths ht ht1
  have hl := log_two_interval.2
  linarith

/-- Once the positive tail dominates its first two terms, the final scalar
barrier follows. The tail estimate is explicitly a hypothesis here. -/
theorem tail_barrier {t s : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hs : t^4 / 12 + t^6 / 30 ≤ s) :
    2 * Real.log 2 - 1 < (1 - t^2) / 2 + 4 * s / t := by
  have hb := barrier_gt_log_target ht.le ht1
  have hpoly : t^3 / 3 + 2*t^5 / 15 ≤ 4*s/t := by
    apply (le_div_iff₀ ht).2
    nlinarith [hs]
  unfold barrier at hb
  linarith

end Scalar
end CourtadeKumar
