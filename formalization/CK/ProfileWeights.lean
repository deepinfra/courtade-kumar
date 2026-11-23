import CK.Matching
import Mathlib.Analysis.Convex.Mul

/-!
# The comparison profile's logarithmically convex coefficients

The index here is `n = k - 1`, so `profileWeight x 0 = W₁(x) = 1`.
The crossing argument uses a direct discrete inequality and does not introduce
real roots or assume the desired matched-profile comparison.
-/

noncomputable section
namespace CourtadeKumar
open scoped BigOperators

/-- A drop in a nonnegative log-convex sequence can only occur below its first value. -/
theorem logConvex_drop_le_first {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hc : ∀ n, a (n + 1) ^ 2 ≤ a n * a (n + 2)) (n : ℕ)
    (hdrop : a (n + 1) < a n) : a n ≤ a 0 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hdrop' : a (n + 2) < a (n + 1) := by simpa [Nat.add_assoc] using hdrop
    have hp : 0 < a (n + 1) := lt_of_le_of_lt (ha (n + 2)) hdrop'
    have hprev : a (n + 1) < a n := by
      by_contra hn
      have hle : a n ≤ a (n + 1) := le_of_not_gt hn
      have hm := mul_le_mul_of_nonneg_right hle (ha (n + 2))
      have hs := mul_lt_mul_of_pos_left hdrop' hp
      nlinarith [hc n]
    exact hprev.le.trans (ih hprev)

/-- Once such a sequence rises above a level bounding its first value, it stays above it. -/
theorem logConvex_persists_above {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hc : ∀ n, a (n + 1) ^ 2 ≤ a n * a (n + 2))
    {r : ℝ} (hfirst : a 0 ≤ r) {k m : ℕ} (hk : r < a k) (hkm : k ≤ m) :
    r < a m := by
  induction m, hkm using Nat.le_induction with
  | base => exact hk
  | succ m hkm ih =>
    have hstep : a m ≤ a (m + 1) := by
      by_contra hn
      have h := logConvex_drop_le_first ha hc m (lt_of_not_ge hn)
      linarith
    exact ih.trans_le hstep

/-- Summable coefficients with this persistence property have the required single crossing. -/
theorem persistentCrossing_tsum_nonpos {a w : ℕ → ℝ}
    (ha : Summable a) (hwa : Summable (fun n => w n * a n))
    (hsum : ∑' n, a n = 0) (hw : Antitone w) (hw0 : ∀ n, 0 ≤ w n)
    (hcross : ∀ k m, k ≤ m → 0 < a k → 0 ≤ a m) :
    ∑' n, w n * a n ≤ 0 := by
  classical
  by_cases hex : ∃ k, 0 < a k
  · let k := Nat.find hex
    apply singleCrossing_tsum_nonpos k ha hwa hsum hw
    · intro i hi
      exact le_of_not_gt (Nat.find_min hex hi)
    · intro i hi
      exact hcross k i hi (Nat.find_spec hex)
  · apply tsum_nonpos
    intro i
    apply mul_nonpos_of_nonneg_of_nonpos (hw0 i)
    exact le_of_not_gt (fun hi => hex ⟨i, hi⟩)

namespace Spec

def profileWeight (x : ℝ) (n : ℕ) : ℝ :=
  ((1 + x) ^ (2 * n + 1) + (1 - x) ^ (2 * n + 1)) / 2

@[simp] theorem profileWeight_zero (x : ℝ) : profileWeight x 0 = 1 := by
  simp [profileWeight]

theorem profileWeight_ge_one {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    1 ≤ profileWeight x n := by
  have hp : (1 + x) ∈ Set.Ici (0 : ℝ) := by
    change 0 ≤ 1 + x
    linarith [(abs_le.mp hx).1]
  have hm : (1 - x) ∈ Set.Ici (0 : ℝ) := by
    change 0 ≤ 1 - x
    linarith [(abs_le.mp hx).2]
  have h := (convexOn_pow (𝕜 := ℝ) (2 * n + 1)).2 hp hm
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at h
  rw [show (1 / 2 : ℝ) * (1 + x) + 1 / 2 * (1 - x) = 1 by ring, one_pow] at h
  unfold profileWeight
  linarith

theorem profileWeight_nonneg {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    0 ≤ profileWeight x n := (by norm_num : (0 : ℝ) ≤ 1).trans (profileWeight_ge_one hx n)

private theorem two_moment_logConvex {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (a b : ℝ) : ((u * a + v * b) / 2) ^ 2 ≤
      ((u + v) / 2) * ((u * a ^ 2 + v * b ^ 2) / 2) := by
  have h := mul_nonneg (mul_nonneg hu hv) (sq_nonneg (a - b))
  nlinarith

theorem profileWeight_logConvex {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    profileWeight x (n + 1) ^ 2 ≤ profileWeight x n * profileWeight x (n + 2) := by
  have hp : 0 ≤ 1 + x := by linarith [(abs_le.mp hx).1]
  have hm : 0 ≤ 1 - x := by linarith [(abs_le.mp hx).2]
  have h := two_moment_logConvex (pow_nonneg hp (2 * n + 1))
    (pow_nonneg hm (2 * n + 1)) ((1 + x) ^ 2) ((1 - x) ^ 2)
  unfold profileWeight
  rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
    show 2 * (n + 2) + 1 = (2 * n + 1) + 4 by omega]
  simp only [pow_add]
  convert h using 1 <;> ring

theorem scaled_profileWeight_logConvex {x r : ℝ} (hx : |x| ≤ 1)
    (n : ℕ) :
    (profileWeight x (n + 1) * r ^ (n + 2)) ^ 2 ≤
      (profileWeight x n * r ^ (n + 1)) *
        (profileWeight x (n + 2) * r ^ (n + 3)) := by
  have h := mul_le_mul_of_nonneg_right (profileWeight_logConvex hx n)
    (sq_nonneg (r ^ (n + 2)))
  convert h using 1
  · ring
  · simp only [show n + 2 = (n + 1) + 1 by omega,
      show n + 3 = (n + 1) + 2 by omega, pow_add, pow_one]
    ring

/-- The normalized profile coefficients cross the matching channel's coefficients once. -/
theorem scaled_profileWeight_persists {x r : ℝ} (hx : |x| ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {k m : ℕ} (hkm : k ≤ m)
    (hk : 1 < profileWeight x k * r ^ (k + 1)) :
    1 < profileWeight x m * r ^ (m + 1) := by
  apply logConvex_persists_above
    (a := fun n => profileWeight x n * r ^ (n + 1))
    (fun n => mul_nonneg (profileWeight_nonneg hx n) (pow_nonneg hr0 _))
    (fun n => by simpa [Nat.add_assoc] using scaled_profileWeight_logConvex hx (r := r) n)
    (by simpa using hr1) hk hkm

end Spec
end CourtadeKumar
