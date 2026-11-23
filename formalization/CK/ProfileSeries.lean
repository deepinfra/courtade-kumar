import CK.ProfileWeights
import CK.ScalarEndpoints

/-!
# The actual power series of the biased binary profile

All series are proved convergent on the closed binary domain. In particular,
deterministic conditional bits are included, rather than removed by an
unproved endpoint-continuity assertion.
-/

noncomputable section
namespace CourtadeKumar.Spec
open scoped BigOperators

def comparisonCoeff (n : ℕ) : ℝ := Scalar.a (n + 1) / Real.log 2

theorem comparisonCoeff_pos (n : ℕ) : 0 < comparisonCoeff n := by
  unfold comparisonCoeff Scalar.a
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  apply div_pos
  · apply one_div_pos.mpr
    apply mul_pos <;> linarith
  · exact log_two_pos

theorem hasSum_divergence_closed {t : ℝ} (ht : |t| ≤ 1) :
    HasSum (fun n : ℕ => comparisonCoeff n * t ^ (2 * (n + 1))) (divergence t) := by
  have h := (Scalar.hasSum_divergenceNats_closed ht).div_const (Real.log 2)
  rw [divergence_eq_divergenceNats]
  convert h using 1
  funext n
  unfold comparisonCoeff
  ring

private theorem profile_term_algebra {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (d : ℝ) (k : ℕ) :
    (a / 2 * (d / a) ^ (k + 1) + b / 2 * (d / b) ^ (k + 1)) / (a * b) =
      ((a ^ k + b ^ k) / 2) * (d / (a * b)) ^ (k + 1) := by
  simp only [div_pow, mul_pow, pow_succ]
  field_simp
  ring

theorem hasSum_binaryProfile {x d : ℝ} (hx : |x| < 1) (hxd : |x| + |d| ≤ 1) :
    HasSum (fun n : ℕ => comparisonCoeff n * profileWeight x n *
      (d / (1 - x ^ 2)) ^ (2 * (n + 1))) (binaryProfile x d / (1 - x ^ 2)) := by
  have hdom := binaryProfile_domain hx hxd
  have hp : 0 < 1 + x := by linarith [(abs_lt.mp hx).1]
  have hm : 0 < 1 - x := by linarith [(abs_lt.mp hx).2]
  have h := (((hasSum_divergence_closed hdom.2.2.1).mul_left ((1 + x) / 2)).add
    ((hasSum_divergence_closed hdom.2.2.2).mul_left ((1 - x) / 2))).div_const (1 - x ^ 2)
  convert h using 1
  · funext n
    have he := profile_term_algebra hp.ne' hm.ne' d (2 * n + 1)
    rw [show (1 + x) * (1 - x) = 1 - x ^ 2 by ring,
      show 2 * n + 1 + 1 = 2 * (n + 1) by omega] at he
    unfold profileWeight
    calc
      _ = comparisonCoeff n *
          (((1 + x) / 2 * (d / (1 + x)) ^ (2 * (n + 1)) +
            (1 - x) / 2 * (d / (1 - x)) ^ (2 * (n + 1))) / (1 - x ^ 2)) := by
            rw [he]
            ring
      _ = _ := by ring

/-- The lower profile estimate, including every deterministic conditional endpoint. -/
theorem binaryProfile_lower {x d : ℝ} (hx : |x| < 1) (hxd : |x| + |d| ≤ 1) :
    (1 - x ^ 2) * divergence (d / (1 - x ^ 2)) ≤ binaryProfile x d := by
  have hdom := binaryProfile_domain hx hxd
  have hdv : |d / (1 - x ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hdom.1]
    exact (div_le_one hdom.1).mpr hdom.2.1
  have h := hasSum_le (f := fun n => comparisonCoeff n *
      (d / (1 - x ^ 2)) ^ (2 * (n + 1))) (fun n => ?_)
    (hasSum_divergence_closed hdv) (hasSum_binaryProfile hx hxd)
  · simpa [mul_comm] using (le_div_iff₀ hdom.1).mp h
  · have hp : 0 ≤ (d / (1 - x ^ 2)) ^ (2 * (n + 1)) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) _
    have hw := profileWeight_ge_one hx.le n
    nlinarith [mul_nonneg (comparisonCoeff_pos n).le hp,
      mul_nonneg (mul_nonneg (comparisonCoeff_pos n).le hp) (sub_nonneg.mpr hw)]

private theorem normalized_power_factor (z t W : ℝ) (ht : t ≠ 0) (n : ℕ) :
    W * z ^ (2 * (n + 1)) - t ^ (2 * (n + 1)) =
      t ^ (2 * (n + 1)) * (W * (z ^ 2 / t ^ 2) ^ (n + 1) - 1) := by
  simp only [pow_mul, div_pow]
  field_simp

/-- Complete pointwise domination by the channel matching normalized information. -/
theorem binaryProfile_matched_domination {ρ x d t : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hx : |x| < 1) (hxd : |x| + |d| ≤ 1)
    (ht : t ∈ Set.Icc 0 1)
    (hmatch : divergence t = binaryProfile x d / (1 - x ^ 2)) :
    binaryProfile x (ρ * d) ≤ (1 - x ^ 2) * divergence (ρ * t) := by
  have hdom := binaryProfile_domain hx hxd
  have hlower := binaryProfile_lower hx hxd
  have hcorr := matched_correlation_bound hdom.1 hdom.2.1 ht hmatch hlower
  have hcorr' : (d / (1 - x ^ 2)) ^ 2 ≤ t ^ 2 := by simpa [div_pow] using hcorr
  by_cases htzero : t = 0
  · have hz : (d / (1 - x ^ 2)) ^ 2 = 0 := by
      apply le_antisymm
      · simpa [htzero] using hcorr'
      · exact sq_nonneg _
    have hd : d = 0 := (div_eq_zero_iff.mp (sq_eq_zero_iff.mp hz)).resolve_right hdom.1.ne'
    simp [hd, htzero, binaryProfile, divergence_zero]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
  let r : ℝ := (d / (1 - x ^ 2)) ^ 2 / t ^ 2
  have hr0 : 0 ≤ r := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hr1 : r ≤ 1 := (div_le_one (sq_pos_of_pos htpos)).mpr hcorr'
  have ht_abs : |t| ≤ 1 := by simpa [abs_of_nonneg ht.1] using ht.2
  have hρt : |ρ * t| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hρ0, abs_of_nonneg ht.1]
    calc ρ * t ≤ 1 * t := mul_le_mul_of_nonneg_right hρ1 ht.1
      _ = t := one_mul _
      _ ≤ 1 := ht.2
  have hρxd : |x| + |ρ * d| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hρ0]
    have hm := mul_le_mul_of_nonneg_right hρ1 (abs_nonneg d)
    linarith
  let a : ℕ → ℝ := fun n =>
    comparisonCoeff n * profileWeight x n * (d / (1 - x ^ 2)) ^ (2 * (n + 1)) -
      comparisonCoeff n * t ^ (2 * (n + 1))
  let w : ℕ → ℝ := fun n => ρ ^ (2 * (n + 1))
  have ha : HasSum a 0 := by
    have h := (hasSum_binaryProfile hx hxd).sub (hasSum_divergence_closed ht_abs)
    simpa only [← hmatch, sub_self] using h
  have hwa : HasSum (fun n => w n * a n)
      (binaryProfile x (ρ * d) / (1 - x ^ 2) - divergence (ρ * t)) := by
    have h := (hasSum_binaryProfile hx hρxd).sub (hasSum_divergence_closed hρt)
    convert h using 1
    funext n
    dsimp [a, w]
    rw [show ρ * d / (1 - x ^ 2) = ρ * (d / (1 - x ^ 2)) by ring]
    simp only [mul_pow]
    ring
  have hfactor : ∀ n, a n = comparisonCoeff n * t ^ (2 * (n + 1)) *
      (profileWeight x n * r ^ (n + 1) - 1) := by
    intro n
    have h := normalized_power_factor (d / (1 - x ^ 2)) t (profileWeight x n) htzero n
    dsimp [a, r]
    calc
      _ = comparisonCoeff n *
          (profileWeight x n * (d / (1 - x ^ 2)) ^ (2 * (n + 1)) - t ^ (2 * (n + 1))) := by ring
      _ = _ := by rw [h]; ring
  have hcross : ∀ k m, k ≤ m → 0 < a k → 0 ≤ a m := by
    intro k m hkm hk
    have hkpos : 0 < comparisonCoeff k * t ^ (2 * (k + 1)) :=
      mul_pos (comparisonCoeff_pos k) (pow_pos htpos _)
    have hk' : 1 < profileWeight x k * r ^ (k + 1) := by
      rw [hfactor k] at hk
      have h := (mul_pos_iff_of_pos_left hkpos).mp hk
      linarith
    have hm := scaled_profileWeight_persists hx.le hr0 hr1 hkm hk'
    rw [hfactor m]
    exact mul_nonneg (mul_nonneg (comparisonCoeff_pos m).le (pow_nonneg ht.1 _))
      (sub_nonneg.mpr hm.le)
  have hw : Antitone w := by
    intro i j hij
    exact pow_le_pow_of_le_one hρ0 hρ1 (by omega)
  have hsum := persistentCrossing_tsum_nonpos ha.summable hwa.summable ha.tsum_eq hw
    (fun n => pow_nonneg hρ0 _) hcross
  rw [hwa.tsum_eq] at hsum
  have hdiv : binaryProfile x (ρ * d) / (1 - x ^ 2) ≤ divergence (ρ * t) := by linarith
  simpa [mul_comm] using (div_le_iff₀ hdom.1).mp hdiv

/-- Exact independently stated pointwise comparison target from the latest paper. -/
theorem pointwiseComparison : PointwiseComparisonTarget := by
  intro ρ x d hρ0 hρ1 hx hxd
  obtain ⟨t, ht, hmatch⟩ := exists_pointwise_matching_parameter hx hxd
  have hV := (binaryProfile_domain hx hxd).1
  have hmatch' : divergence t = binaryProfile x d / (1 - x ^ 2) := by
    rw [hmatch]
    field_simp
  exact ⟨t, ht.1, ht.2, hmatch,
    binaryProfile_matched_domination hρ0 hρ1 hx hxd ht hmatch',
    (binaryProfile_domain hx hxd).2.1, binaryProfile_lower hx hxd⟩

end CourtadeKumar.Spec
