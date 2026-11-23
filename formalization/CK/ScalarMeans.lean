import CK.ScalarTails
import CK.ScalarSeries
import CK.Comparison
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The two weighted means in the latest three-bit argument

All masses and moments below are actual convergent series for `0 < q < 1`.
The coefficient convolution estimate proves `jMean q ≤ commonExponent q`.
The increasing ratio of the two weight sequences proves `kMean q ≤ jMean q`
using the checked single-crossing summation principle.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace CourtadeKumar
namespace Scalar
open Finset

/-- Weights `k a_k q^k`, with zero weight at zero. -/
def kWeight (q : ℝ) (n : ℕ) : ℝ := (n : ℝ) * a n * q^n

/-- Weights `b_j q^j` on positive indices; zero is excluded. -/
def jWeight (q : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else b (Real.log 2) n * q^n

private def allTailWeight (q : ℝ) (n : ℕ) : ℝ := b (Real.log 2) n * q^n

def alpha (q : ℝ) : ℝ := ∑' n : ℕ, jWeight q n

def kMass (q : ℝ) : ℝ := ∑' n : ℕ, kWeight q n

def kMoment (q : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) * kWeight q n

def jMoment (q : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) * jWeight q n

def kMean (q : ℝ) : ℝ := kMoment q / kMass q

def jMean (q : ℝ) : ℝ := jMoment q / alpha q

/-- The common exponent after `J log 2 = (1-q) alpha` is substituted. -/
def commonExponent (q : ℝ) : ℝ :=
  2 * b (Real.log 2) 1 * kMass q / ((1 + alpha q) * (1-q) * alpha q)

private theorem weighted_a_sq_le_one (n : ℕ) : (n : ℝ)^2 * a n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have h := (le_div_iff₀ (sq_pos_of_pos hn0)).mp (a_le_inv_square n)
  nlinarith

private theorem weighted_a_le_one (n : ℕ) : (n : ℝ) * a n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have h := weighted_a_sq_le_one n
  have ha := a_nonneg n
  have hnn : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hnn ha
  linarith

private theorem weighted_b_le_one (n : ℕ) : (n : ℝ) * b (Real.log 2) n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have h := weighted_tail_le_quarter (Nat.one_le_iff_ne_zero.mpr hn)
  linarith

private theorem b_le_one (n : ℕ) : b (Real.log 2) n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hb := b_log_two_nonneg n
  have hmul := mul_nonneg (sub_nonneg.mpr hn1) hb
  have h := weighted_b_le_one n
  nlinarith

theorem kWeight_nonneg {q : ℝ} (hq : 0 ≤ q) (n : ℕ) : 0 ≤ kWeight q n := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (a_nonneg n)) (pow_nonneg hq _)

theorem jWeight_nonneg {q : ℝ} (hq : 0 ≤ q) (n : ℕ) : 0 ≤ jWeight q n := by
  unfold jWeight
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (b_log_two_nonneg n) (pow_nonneg hq _)

private theorem allTailWeight_nonneg {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ allTailWeight q n := mul_nonneg (b_log_two_nonneg n) (pow_nonneg hq _)

@[simp] theorem nat_mul_jWeight (q : ℝ) (n : ℕ) :
    (n : ℝ) * jWeight q n = (n : ℝ) * b (Real.log 2) n * q^n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [jWeight, if_neg hn]
    ring

theorem summable_kWeight {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (kWeight q) := by
  apply (summable_geometric_of_lt_one hq0 hq1).of_nonneg_of_le (kWeight_nonneg hq0)
  intro n
  exact (mul_le_mul_of_nonneg_right (weighted_a_le_one n) (pow_nonneg hq0 n)).trans_eq (one_mul _)

theorem summable_jWeight {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (jWeight q) := by
  apply (summable_geometric_of_lt_one hq0 hq1).of_nonneg_of_le (jWeight_nonneg hq0)
  intro n
  unfold jWeight
  split_ifs
  · exact pow_nonneg hq0 n
  · exact (mul_le_mul_of_nonneg_right (b_le_one n) (pow_nonneg hq0 n)).trans_eq (one_mul _)

private theorem summable_allTailWeight {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (allTailWeight q) := by
  apply (summable_geometric_of_lt_one hq0 hq1).of_nonneg_of_le (allTailWeight_nonneg hq0)
  intro n
  exact (mul_le_mul_of_nonneg_right (b_le_one n) (pow_nonneg hq0 n)).trans_eq (one_mul _)

theorem summable_kMoment {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => (n : ℝ) * kWeight q n) := by
  apply (summable_geometric_of_lt_one hq0 hq1).of_nonneg_of_le
    (fun n => mul_nonneg (Nat.cast_nonneg n) (kWeight_nonneg hq0 n))
  intro n
  have h := mul_le_mul_of_nonneg_right (weighted_a_sq_le_one n) (pow_nonneg hq0 n)
  unfold kWeight
  nlinarith

theorem summable_jMoment {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => (n : ℝ) * jWeight q n) := by
  apply (summable_geometric_of_lt_one hq0 hq1).of_nonneg_of_le
    (fun n => mul_nonneg (Nat.cast_nonneg n) (jWeight_nonneg hq0 n))
  intro n
  rw [nat_mul_jWeight]
  exact (mul_le_mul_of_nonneg_right (weighted_b_le_one n) (pow_nonneg hq0 n)).trans_eq (one_mul _)

theorem kMass_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : 0 < kMass q := by
  have h := (summable_kWeight hq0.le hq1).le_tsum 1 (fun n _ => kWeight_nonneg hq0.le n)
  have hp : 0 < kWeight q 1 := by norm_num [kWeight, a]; positivity
  exact hp.trans_le h

theorem alpha_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : 0 < alpha q := by
  have h := (summable_jWeight hq0.le hq1).le_tsum 1 (fun n _ => jWeight_nonneg hq0.le n)
  have hp : 0 < jWeight q 1 := by
    simp only [jWeight, if_neg (by decide : (1 : ℕ) ≠ 0), pow_one]
    exact mul_pos (b_log_two_pos (by decide)) hq0
  exact hp.trans_le h

theorem alpha_eq_positive_tsum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    alpha q = ∑' n : ℕ, b (Real.log 2) (n+1) * q^(n+1) := by
  unfold alpha
  rw [(summable_jWeight hq0 hq1).tsum_eq_zero_add]
  simp [jWeight]

private theorem allTailWeight_tsum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' n : ℕ, allTailWeight q n = 1 + alpha q := by
  rw [(summable_allTailWeight hq0 hq1).tsum_eq_zero_add, alpha_eq_positive_tsum hq0 hq1]
  simp [allTailWeight]

private theorem cauchy_left (q : ℝ) (n : ℕ) :
    (∑ j ∈ range (n+1), ((j : ℝ) * jWeight q j) * allTailWeight q (n-j)) =
      convolution (Real.log 2) n * q^n := by
  unfold convolution
  rw [sum_mul]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := mem_range.mp hj; omega
  have hpow : q^j * q^(n-j) = q^n := by rw [← pow_add, Nat.add_sub_of_le hjn]
  rw [nat_mul_jWeight]
  unfold allTailWeight
  calc (j : ℝ) * b (Real.log 2) j * q^j * (b (Real.log 2) (n-j) * q^(n-j))
      = (j : ℝ) * b (Real.log 2) j * b (Real.log 2) (n-j) * (q^j*q^(n-j)) := by ring
    _ = _ := by rw [hpow]

private theorem cauchy_right (q : ℝ) (n : ℕ) :
    (∑ j ∈ range (n+1), kWeight q j * q^(n-j)) = e n * q^n := by
  unfold e
  rw [sum_mul]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := mem_range.mp hj; omega
  have hpow : q^j * q^(n-j) = q^n := by rw [← pow_add, Nat.add_sub_of_le hjn]
  unfold kWeight
  rw [mul_assoc, hpow]

/-- The coefficient comparison lifted to the actual generating series. -/
theorem generating_mean_bound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (1 + alpha q) * jMoment q ≤ (2*b (Real.log 2) 1 / (1-q)) * kMass q := by
  have hW := summable_jMoment hq0 hq1
  have hB := summable_allTailWeight hq0 hq1
  have hK := summable_kWeight hq0 hq1
  have hG := summable_geometric_of_lt_one hq0 hq1
  have hWB := hW.mul_of_nonneg hB
    (fun n => mul_nonneg (Nat.cast_nonneg n) (jWeight_nonneg hq0 n))
    (allTailWeight_nonneg hq0)
  have hKG := hK.mul_of_nonneg hG (kWeight_nonneg hq0) (pow_nonneg hq0)
  have hL : Summable (fun n : ℕ => convolution (Real.log 2) n * q^n) := by
    exact (summable_sum_mul_range_of_summable_mul
      (f := fun n : ℕ => (n : ℝ)*jWeight q n) (g := allTailWeight q) hWB).congr
      (cauchy_left q)
  have hR : Summable (fun n : ℕ => e n * q^n) := by
    exact (summable_sum_mul_range_of_summable_mul
      (f := kWeight q) (g := fun n : ℕ => q^n) hKG).congr (cauchy_right q)
  have hpoint : ∀ n : ℕ, convolution (Real.log 2) n * q^n ≤
      (2*b (Real.log 2) 1) * (e n * q^n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      norm_num [convolution, e, a, sum_range_succ]
    · have h := mul_le_mul_of_nonneg_right
        (coefficient_convolution (Nat.one_le_iff_ne_zero.mpr hn)) (pow_nonneg hq0 n)
      nlinarith
  have htsum := hL.tsum_le_tsum hpoint (hR.mul_left (2*b (Real.log 2) 1))
  have hleft := (hW.tsum_mul_tsum_eq_tsum_sum_range hB hWB).trans (tsum_congr (cauchy_left q))
  have hright := (hK.tsum_mul_tsum_eq_tsum_sum_range hG hKG).trans (tsum_congr (cauchy_right q))
  rw [tsum_mul_left, ← hleft, ← hright, allTailWeight_tsum hq0 hq1,
    tsum_geometric_of_lt_one hq0 hq1] at htsum
  change (1 + alpha q) * (∑' n : ℕ, (n : ℝ) * jWeight q n) ≤
    (2*b (Real.log 2) 1 / (1-q)) * (∑' n : ℕ, kWeight q n)
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using htsum

/-- The second actual mean inequality in the paper: `j_* ≤ h`. -/
theorem jMean_le_commonExponent {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    jMean q ≤ commonExponent q := by
  have ha := alpha_pos hq0 hq1
  have hq : 0 < 1-q := by linarith
  have hden : 0 < (1+alpha q)*(1-q)*alpha q := by positivity
  have hg := generating_mean_bound hq0.le hq1
  have hg' : (1+alpha q)*jMoment q ≤ 2*b (Real.log 2) 1*kMass q/(1-q) := by
    convert hg using 1 <;> ring
  have hgm := (le_div_iff₀ hq).mp hg'
  unfold jMean commonExponent
  apply (le_div_iff₀ hden).2
  have heq : (jMoment q / alpha q) * ((1+alpha q)*(1-q)*alpha q) =
      (1+alpha q)*jMoment q*(1-q) := by
    field_simp [ha.ne']
    ring
  rw [heq]
  exact hgm

/-- Ratio at zero is irrelevant to the weights; choose zero to make it monotone. -/
def meanRatio (n : ℕ) : ℝ := if n = 0 then 0 else weightRatio n

private theorem meanRatio_nonneg (n : ℕ) : 0 ≤ meanRatio n := by
  by_cases hn : n = 0
  · simp [hn, meanRatio]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  unfold meanRatio weightRatio
  rw [if_neg hn]
  exact mul_nonneg (by linarith) (b_log_two_nonneg n)

theorem meanRatio_monotone : Monotone meanRatio := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n = 0
  · subst n
    simpa [meanRatio] using meanRatio_nonneg 1
  · simp only [meanRatio, if_neg hn, if_neg (by omega : n+1 ≠ 0)]
    exact (weightRatio_succ_gt (Nat.one_le_iff_ne_zero.mpr hn)).le

theorem jWeight_eq_ratio_mul_kWeight (q : ℝ) (n : ℕ) :
    jWeight q n = meanRatio n * kWeight q n := by
  by_cases hn : n = 0
  · simp [hn, jWeight, meanRatio, kWeight]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hna : (n : ℝ)*a n ≠ 0 := by
    apply mul_ne_zero (by linarith)
    unfold a
    apply one_div_ne_zero
    exact mul_ne_zero (by linarith) (by linarith)
  simp only [jWeight, meanRatio, if_neg hn, kWeight]
  rw [weightRatio_eq (Nat.one_le_iff_ne_zero.mpr hn)]
  field_simp [hna]
  ring

/-- The first actual mean inequality in the paper: `k_* ≤ j_*`. -/
theorem kMean_le_jMean {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : kMean q ≤ jMean q := by
  have hk := summable_kWeight hq0.le hq1
  have hkm := summable_kMoment hq0.le hq1
  have hj := summable_jWeight hq0.le hq1
  have hjm := summable_jMoment hq0.le hq1
  have hmass := kMass_pos hq0 hq1
  have halpha := alpha_pos hq0 hq1
  let center : ℕ → ℝ := fun n => (n : ℝ)*kWeight q n - kMean q*kWeight q n
  have hc : Summable center := hkm.sub (hk.mul_left (kMean q))
  have hcs : ∑' n, center n = 0 := by
    change (∑' n : ℕ, ((n : ℝ)*kWeight q n - kMean q*kWeight q n)) = 0
    rw [hkm.tsum_sub (hk.mul_left (kMean q)), tsum_mul_left]
    change kMoment q - kMean q*kMass q = 0
    unfold kMean
    field_simp [hmass.ne']
  have hrel : ∀ n : ℕ, (-meanRatio n)*center n =
      -((n : ℝ)*jWeight q n - kMean q*jWeight q n) := by
    intro n
    dsimp [center]
    rw [jWeight_eq_ratio_mul_kWeight]
    ring
  have hwc : Summable (fun n : ℕ => (-meanRatio n)*center n) :=
    (hjm.sub (hj.mul_left (kMean q))).neg.congr (fun n => (hrel n).symm)
  have hleft : ∀ n : ℕ, n < Nat.ceil (kMean q) → center n ≤ 0 := by
    intro n hn
    have hnr : (n : ℝ) ≤ kMean q := (Nat.lt_ceil.mp hn).le
    have h := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hnr) (kWeight_nonneg hq0.le n)
    dsimp [center]
    nlinarith
  have hright : ∀ n : ℕ, Nat.ceil (kMean q) ≤ n → 0 ≤ center n := by
    intro n hn
    have hnr : kMean q ≤ (n : ℝ) := Nat.le_of_ceil_le hn
    have h := mul_nonneg (sub_nonneg.mpr hnr) (kWeight_nonneg hq0.le n)
    dsimp [center]
    nlinarith
  have hcross := singleCrossing_tsum_nonpos (a := center) (w := fun n => -meanRatio n)
    (Nat.ceil (kMean q)) hc hwc hcs
    (fun i j hij => neg_le_neg (meanRatio_monotone hij)) hleft hright
  rw [tsum_congr hrel, tsum_neg, hjm.tsum_sub (hj.mul_left (kMean q)), tsum_mul_left] at hcross
  change -(jMoment q - kMean q*alpha q) ≤ 0 at hcross
  unfold jMean
  apply (le_div_iff₀ halpha).2
  linarith

/-- Both weighted-mean comparisons, with summability discharged from `0<q<1`. -/
theorem means_order {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    kMean q ≤ jMean q ∧ jMean q ≤ commonExponent q :=
  ⟨kMean_le_jMean hq0 hq1, jMean_le_commonExponent hq0 hq1⟩

/-- The same divergence series with `q = rho²` as the power variable. -/
def divergenceSeries (q : ℝ) : ℝ := ∑' n : ℕ, a n * q^n

theorem summable_divergenceSeries {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Summable (fun n : ℕ => a n*q^n) := by
  apply summable_a.of_nonneg_of_le
  · intro n
    exact mul_nonneg (a_nonneg n) (pow_nonneg hq0 n)
  · intro n
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1) (a_nonneg n)).trans_eq (mul_one _)

private theorem b_positive_recurrence (n : ℕ) :
    b (Real.log 2) (n+1) = b (Real.log 2) (n+2) + a (n+2) := by
  have hp : partialSum (n+2) = partialSum (n+1) + a (n+2) := by
    unfold partialSum
    rw [sum_range_succ]
  simp only [b, if_neg (by omega : n+1 ≠ 0), if_neg (by omega : n+2 ≠ 0), hp]
  ring

/-- The generating identity linking the tail mass to the entropy series.
This is the paper's `J log 2 = (1-q) alpha`, with no series assumption. -/
theorem alpha_series_identity {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (1-q) * alpha q = q*Real.log 2 - divergenceSeries q := by
  have hj := summable_jWeight hq0 hq1
  have ha := summable_divergenceSeries hq0 hq1.le
  let F : ℕ → ℝ := fun n => b (Real.log 2) (n+1) * q^(n+1)
  let T : ℕ → ℝ := fun n => b (Real.log 2) (n+2) * q^(n+2)
  let G : ℕ → ℝ := fun n => b (Real.log 2) (n+1) * q^(n+2)
  let A : ℕ → ℝ := fun n => a (n+2) * q^(n+2)
  have hF : Summable F := by
    simpa only [jWeight, if_neg (Nat.succ_ne_zero _)] using (summable_nat_add_iff 1).mpr hj
  have hT : Summable T := by
    exact (summable_nat_add_iff 1).mpr hF
  have hA : Summable A := (summable_nat_add_iff 2).mpr ha
  have hG : Summable G := by
    convert hF.mul_left q using 1
    funext n
    dsimp [G, F]
    rw [show n+2 = (n+1)+1 by omega, pow_succ]
    ring
  have hFsum : ∑' n, F n = alpha q := (alpha_eq_positive_tsum hq0 hq1).symm
  have hTsum : b (Real.log 2) 1*q + (∑' n, T n) = alpha q := by
    have h := hF.sum_add_tsum_nat_add 1
    change (∑ i ∈ range 1, F i) + (∑' i, F (i+1)) = ∑' i, F i at h
    norm_num only [sum_range_succ, sum_range_zero, zero_add] at h
    change b (Real.log 2) 1*q^1 + (∑' i, T i) = ∑' i, F i at h
    simpa only [pow_one, hFsum] using h
  have hAsum : (1/2 : ℝ)*q + (∑' n, A n) = divergenceSeries q := by
    have h := ha.sum_add_tsum_nat_add 2
    simp only [sum_range_succ, sum_range_zero, zero_add, a_zero, zero_mul, pow_one,
      show a 1 = (1/2 : ℝ) by norm_num [a]] at h
    exact h
  have hGsum : ∑' n, G n = q*alpha q := by
    rw [← hFsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [G, F]
    rw [show n+2 = (n+1)+1 by omega, pow_succ]
    ring
  have hGA : ∑' n, G n = (∑' n, T n) + (∑' n, A n) := by
    rw [← hT.tsum_add hA]
    apply tsum_congr
    intro n
    dsimp [G, T, A]
    rw [b_positive_recurrence]
    ring
  rw [b_one] at hTsum
  rw [hGsum] at hGA
  nlinarith

/-- Exact identification with the natural-log binary divergence from `Entropy`. -/
theorem divergenceSeries_eq_divergenceNats {rho : ℝ} (hrho : |rho| < 1) :
    divergenceSeries (rho^2) = divergenceNats rho := by
  have hq : rho^2 ≤ 1 := by nlinarith [(abs_lt.mp hrho).1, (abs_lt.mp hrho).2]
  have ha := summable_divergenceSeries (sq_nonneg rho) hq
  have hs : HasSum (fun n : ℕ => a (n+1)*(rho^2)^(n+1)) (divergenceNats rho) := by
    convert hasSum_divergenceNats hrho using 1
    funext n
    simp only [a, Nat.cast_add, Nat.cast_one, pow_mul, div_eq_mul_inv]
    ring
  unfold divergenceSeries
  rw [ha.tsum_eq_zero_add]
  simp only [a_zero, zero_mul, zero_add]
  exact hs.tsum_eq

/-- The actual tail-series mass equals the paper's closed-form `alpha_p`. -/
theorem alpha_eq_paper {rho : ℝ} (hrho : |rho| < 1) :
    alpha (rho^2) = ((rho^2 - Spec.divergence rho) * Real.log 2) / (1-rho^2) := by
  have hq : rho^2 < 1 := by nlinarith [(abs_lt.mp hrho).1, (abs_lt.mp hrho).2]
  have h := alpha_series_identity (sq_nonneg rho) hq
  rw [divergenceSeries_eq_divergenceNats hrho] at h
  rw [Spec.divergence_eq_divergenceNats]
  apply (eq_div_iff (by linarith : (1 : ℝ)-rho^2 ≠ 0)).2
  have hL : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  field_simp [hL]
  nlinarith

/-- The common exponent is exactly the paper's expression, in bits. -/
theorem commonExponent_eq_paper {rho : ℝ} (hrho : |rho| < 1) :
    commonExponent (rho^2) =
      2*b (Real.log 2) 1*kMass (rho^2) /
      ((1+alpha (rho^2)) * (rho^2-Spec.divergence rho) * Real.log 2) := by
  have hq : rho^2 < 1 := by nlinarith [(abs_lt.mp hrho).1, (abs_lt.mp hrho).2]
  have h := alpha_series_identity (sq_nonneg rho) hq
  rw [divergenceSeries_eq_divergenceNats hrho] at h
  have heq : (1-rho^2)*alpha (rho^2) = (rho^2-Spec.divergence rho)*Real.log 2 := by
    rw [Spec.divergence_eq_divergenceNats]
    field_simp [ne_of_gt log_two_pos]
    nlinarith
  unfold commonExponent
  congr 1
  calc (1+alpha (rho^2))*(1-rho^2)*alpha (rho^2)
      = (1+alpha (rho^2))*((1-rho^2)*alpha (rho^2)) := by ring
    _ = (1+alpha (rho^2))*((rho^2-Spec.divergence rho)*Real.log 2) := by rw [heq]
    _ = _ := by ring

end Scalar
end CourtadeKumar
