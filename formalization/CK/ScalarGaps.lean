import CK.ScalarRescaling

/-!
# Exact generating-series identities for the three-bit gaps

The second gap is expressed as a positive weighted sum of the actual tails;
all sums converge on the full closed interval of the second correlation.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace CourtadeKumar
namespace Scalar
open Finset

/-- The positive tail is bounded by its endpoint value. -/
theorem s_le_b {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) {j : ℕ} (hj : 1 ≤ j) :
    s j σ ≤ b (Real.log 2) j := by
  rw [b_eq_s_one hj]
  unfold s
  apply tsum_le_tsum _ (summable_s hσ0 hσ1 j) (summable_s (by norm_num) (by norm_num) j)
  intro n
  simp only [one_pow, mul_one]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hσ0 hσ1) (a_nonneg _)).trans_eq (mul_one _)

theorem s_recurrence {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (j : ℕ) :
    s j σ = a (j+1)*σ^(2*(j+1)) + s (j+1) σ := by
  have h := (summable_s hσ0 hσ1 j).tsum_eq_zero_add
  simpa only [s, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Positive-index weights for the exact second-gap generating series. -/
def tailWeight (q σ : ℝ) (n : ℕ) : ℝ := if n=0 then 0 else s n σ*q^n

def tailMass (q σ : ℝ) : ℝ := ∑' n : ℕ, tailWeight q σ n

theorem tailWeight_nonneg {q σ : ℝ} (hq : 0 ≤ q) (hσ : 0 ≤ σ) (n : ℕ) :
    0 ≤ tailWeight q σ n := by
  unfold tailWeight
  split_ifs
  · rfl
  · exact mul_nonneg (s_nonneg hσ n) (pow_nonneg hq n)

theorem summable_tailWeight {q σ : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) : Summable (tailWeight q σ) := by
  apply (summable_jWeight hq0 hq1).of_nonneg_of_le (tailWeight_nonneg hq0 hσ0)
  intro n
  by_cases hn : n=0
  · simp [tailWeight, jWeight, hn]
  · simp only [tailWeight, jWeight, if_neg hn]
    exact mul_le_mul_of_nonneg_right (s_le_b hσ0 hσ1 (by omega)) (pow_nonneg hq0 n)

theorem tailMass_eq_positive_tsum {q σ : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    tailMass q σ = ∑' n : ℕ, s (n+1) σ*q^(n+1) := by
  unfold tailMass
  rw [(summable_tailWeight hq0 hq1 hσ0 hσ1).tsum_eq_zero_add]
  simp [tailWeight]

/-- The exact generating identity for the second three-bit gap. -/
theorem second_gap_series {q σ : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (1-q)*tailMass q σ = q*divergenceSeries (σ^2)-divergenceSeries (q*σ^2) := by
  have hσsq : σ^2 ≤ 1 := by nlinarith
  have hqσ0 : 0 ≤ q*σ^2 := mul_nonneg hq0 (sq_nonneg σ)
  have hqσ1 : q*σ^2 ≤ 1 := (mul_le_of_le_one_right hq0 hσsq).trans hq1.le
  have ht := summable_tailWeight hq0 hq1 hσ0 hσ1
  have ha := summable_divergenceSeries hqσ0 hqσ1
  let F : ℕ → ℝ := fun n => s (n+1) σ*q^(n+1)
  let T : ℕ → ℝ := fun n => s (n+2) σ*q^(n+2)
  let G : ℕ → ℝ := fun n => s (n+1) σ*q^(n+2)
  let A : ℕ → ℝ := fun n => a (n+2)*(q*σ^2)^(n+2)
  have hF : Summable F := by
    simpa only [tailWeight, if_neg (Nat.succ_ne_zero _)] using (summable_nat_add_iff 1).mpr ht
  have hT : Summable T := (summable_nat_add_iff 1).mpr hF
  have hA : Summable A := (summable_nat_add_iff 2).mpr ha
  have hG : Summable G := by
    convert hF.mul_left q using 1
    funext n
    dsimp [G,F]
    rw [show n+2=(n+1)+1 by omega, pow_succ]
    ring
  have hFsum : (∑' n, F n)=tailMass q σ := (tailMass_eq_positive_tsum hq0 hq1 hσ0 hσ1).symm
  have hTsum : s 1 σ*q+(∑' n,T n)=tailMass q σ := by
    have h := hF.sum_add_tsum_nat_add 1
    change (∑ i ∈ range 1, F i)+(∑' i,F (i+1))=∑' i,F i at h
    norm_num only [sum_range_succ, sum_range_zero, zero_add] at h
    change s 1 σ*q^1+(∑' i,T i)=∑' i,F i at h
    simpa only [pow_one,hFsum] using h
  have hAsum : (1/2:ℝ)*(q*σ^2)+(∑' n,A n)=divergenceSeries (q*σ^2) := by
    have h := ha.sum_add_tsum_nat_add 2
    simp only [sum_range_succ, sum_range_zero, zero_add, a_zero, zero_mul, pow_one,
      show a 1=(1/2:ℝ) by norm_num [a]] at h
    exact h
  have hGsum : (∑' n,G n)=q*tailMass q σ := by
    rw [← hFsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [G,F]
    rw [show n+2=(n+1)+1 by omega,pow_succ]
    ring
  have hGA : (∑' n,G n)=(∑' n,T n)+(∑' n,A n) := by
    rw [← hT.tsum_add hA]
    apply tsum_congr
    intro n
    dsimp [G,T,A]
    rw [s_recurrence hσ0 hσ1 (n+1)]
    rw [mul_pow, pow_mul]
    ring
  have hD : divergenceSeries (σ^2)=(1/2:ℝ)*σ^2+s 1 σ := by
    have h := (summable_divergenceSeries (sq_nonneg σ) hσsq).sum_add_tsum_nat_add 2
    simp only [sum_range_succ,sum_range_zero,zero_add,a_zero,zero_mul,pow_one,
      show a 1=(1/2:ℝ) by norm_num [a]] at h
    unfold divergenceSeries
    rw [← h]
    congr 1
    unfold s
    apply tsum_congr
    intro n
    rw [pow_mul]
  rw [hGsum] at hGA
  rw [hD]
  nlinarith

/-- Second gap written with actual binary divergence, including `σ=1`. -/
theorem second_gap_divergence {ρ σ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (1-ρ^2)*tailMass (ρ^2) σ = ρ^2*divergenceNats σ-divergenceNats (ρ*σ) := by
  have hq1 : ρ^2 < 1 := by nlinarith
  have hρσ0 : 0 ≤ ρ*σ := mul_nonneg hρ0 hσ0
  have hρσ1 : ρ*σ ≤ 1 := (mul_le_of_le_one_right hρ0 hσ1).trans hρ1.le
  have h := second_gap_series (sq_nonneg ρ) hq1 hσ0 hσ1
  rw [divergenceSeries_eq_divergenceNats_closed (by simpa only [abs_of_nonneg hσ0] using hσ1),
    ← mul_pow, divergenceSeries_eq_divergenceNats_closed
      (by simpa only [abs_of_nonneg hρσ0] using hρσ1)] at h
  exact h

end Scalar
end CourtadeKumar
