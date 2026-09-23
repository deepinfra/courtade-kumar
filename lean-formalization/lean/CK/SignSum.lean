import CK.Algebra
import CK.Sections
import CK.AvgLemmas
import Mathlib.Algebra.BigOperators.Field

/-!
# Moments of a weighted sign sum and the capped sign-sum estimate

Manuscript Lemma `lem:rademacher` (Appendix D).  For weights `a : Fin n → ℝ` the Rademacher
sum `R(x) = ∑ i, a i * sign (x i)` has odd moments zero and even moments (up to order ten) given
by polynomials in the power sums `pw a k = ∑ i, a i ^ k`.  Under `∑ a i ^ 2 = 1` and
`max |a i| ≤ 2/5`, the polynomial majorant of `|·|` (`Algebra.majorant`) yields `E|R| ≤ 7/8`.
-/
noncomputable section
namespace CK
open scoped BigOperators
open Finset

/-- The weighted sign sum `R(x) = ∑ i, a i * sign (x i)`. -/
def signSum {n : ℕ} (a : Fin n → ℝ) (x : Cube n) : ℝ := ∑ i, a i * sign (x i)

/-- Power sums of the weights. -/
def pw {n : ℕ} (a : Fin n → ℝ) (k : ℕ) : ℝ := ∑ i, a i ^ k

/-- The `k`-th moment of the sign sum under the uniform distribution on the cube. -/
def mom {n : ℕ} (a : Fin n → ℝ) (k : ℕ) : ℝ := avg (fun x => signSum a x ^ k)

theorem sign_true : sign true = 1 := by simp [sign]

theorem sign_false : sign false = -1 := by simp [sign]

/-- Splitting the last coordinate of the sign sum. -/
theorem signSum_snoc {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (x : Cube n) (s : Bool) :
    signSum (Fin.snoc a c : Fin (n + 1) → ℝ) (Fin.snoc x s) = signSum a x + c * sign s := by
  unfold signSum
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Splitting the last weight of a power sum. -/
theorem pw_snoc {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (k : ℕ) :
    pw (Fin.snoc a c : Fin (n + 1) → ℝ) k = pw a k + c ^ k := by
  unfold pw
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- The average of a constant. -/
theorem avg_const_cube {n : ℕ} (c : ℝ) : avg (fun _ : Cube n => c) = c := by
  induction n with
  | zero => exact avg_of_unique _
  | succ n ih =>
    rw [avg_snoc]
    simp only [ih]
    ring

/-- The average commutes with finite sums. -/
theorem avg_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Cube n → ℝ) :
    avg (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, avg (f i) := by
  unfold avg
  rw [Finset.sum_comm, Finset.sum_div]

theorem avg_mul_const {n : ℕ} (u : Cube n → ℝ) (c : ℝ) :
    avg (fun x => u x * c) = avg u * c := by
  unfold avg
  rw [← Finset.sum_mul]
  ring

/-- One-step moment recursion: averaging `(R + cσ)^k` over `σ = ±1` keeps the even binomial
terms only. -/
theorem mom_snoc {n : ℕ} (b : Fin n → ℝ) (c : ℝ) (k : ℕ) :
    mom (Fin.snoc b c : Fin (n + 1) → ℝ) k =
      ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * ((c ^ (k - j) + (-c) ^ (k - j)) / 2) * mom b j := by
  unfold mom
  rw [avg_snoc]
  simp only [signSum_snoc, sign_true, sign_false, mul_one, mul_neg]
  simp only [add_pow, avg_sum]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [avg_mul_const]
  ring

/-- The first eleven moments of the sign sum in terms of the power sums. -/
def Moments {n : ℕ} (a : Fin n → ℝ) : Prop :=
  mom a 0 = 1 ∧ mom a 1 = 0 ∧ mom a 2 = pw a 2 ∧ mom a 3 = 0 ∧
  mom a 4 = 3 * pw a 2 ^ 2 - 2 * pw a 4 ∧ mom a 5 = 0 ∧
  mom a 6 = 15 * pw a 2 ^ 3 - 30 * pw a 2 * pw a 4 + 16 * pw a 6 ∧ mom a 7 = 0 ∧
  mom a 8 = 105 * pw a 2 ^ 4 - 420 * pw a 2 ^ 2 * pw a 4 + 140 * pw a 4 ^ 2
    + 448 * pw a 2 * pw a 6 - 272 * pw a 8 ∧ mom a 9 = 0 ∧
  mom a 10 = 945 * pw a 2 ^ 5 - 6300 * pw a 2 ^ 3 * pw a 4 + 6300 * pw a 2 * pw a 4 ^ 2
    + 10080 * pw a 2 ^ 2 * pw a 6 - 6720 * pw a 4 * pw a 6 - 12240 * pw a 2 * pw a 8
    + 7936 * pw a 10

theorem moments_zero (a : Fin 0 → ℝ) : Moments a := by
  simp [Moments, mom, signSum, pw, avg_of_unique]

theorem moments_snoc {n : ℕ} (b : Fin n → ℝ) (c : ℝ) (ih : Moments b) :
    Moments (Fin.snoc b c : Fin (n + 1) → ℝ) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := ih
  unfold Moments
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [mom_snoc, Finset.sum_range_succ, Finset.sum_range_zero, pw_snoc,
      h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Nat.choose_succ_succ, Nat.choose_zero_right,
      Nat.choose_zero_succ, Nat.choose_self]
     push_cast
     ring)

/-- All moments up to order ten, by induction on the dimension along `Fin.snoc`. -/
theorem moments {n : ℕ} (a : Fin n → ℝ) : Moments a := by
  induction n with
  | zero => exact moments_zero a
  | succ n ih =>
    have h := moments_snoc (Fin.init a) (a (Fin.last n)) (ih (Fin.init a))
    rwa [Fin.snoc_init_self] at h

theorem avg_signSum_sq {n : ℕ} (a : Fin n → ℝ) : avg (fun x => signSum a x ^ 2) = pw a 2 := by
  obtain ⟨_, _, h, _⟩ := moments a
  exact h

theorem avg_signSum_pow4 {n : ℕ} (a : Fin n → ℝ) :
    avg (fun x => signSum a x ^ 4) = 3 * pw a 2 ^ 2 - 2 * pw a 4 := by
  obtain ⟨_, _, _, _, h, _⟩ := moments a
  exact h

theorem avg_signSum_pow6 {n : ℕ} (a : Fin n → ℝ) :
    avg (fun x => signSum a x ^ 6) = 15 * pw a 2 ^ 3 - 30 * pw a 2 * pw a 4 + 16 * pw a 6 := by
  obtain ⟨_, _, _, _, _, _, h, _⟩ := moments a
  exact h

theorem avg_signSum_pow8 {n : ℕ} (a : Fin n → ℝ) : avg (fun x => signSum a x ^ 8) =
    105 * pw a 2 ^ 4 - 420 * pw a 2 ^ 2 * pw a 4 + 140 * pw a 4 ^ 2 + 448 * pw a 2 * pw a 6
      - 272 * pw a 8 := by
  obtain ⟨_, _, _, _, _, _, _, _, h, _⟩ := moments a
  exact h

theorem avg_signSum_pow10 {n : ℕ} (a : Fin n → ℝ) : avg (fun x => signSum a x ^ 10) =
    945 * pw a 2 ^ 5 - 6300 * pw a 2 ^ 3 * pw a 4 + 6300 * pw a 2 * pw a 4 ^ 2
      + 10080 * pw a 2 ^ 2 * pw a 6 - 6720 * pw a 4 * pw a 6 - 12240 * pw a 2 * pw a 8
      + 7936 * pw a 10 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := moments a
  exact h

theorem avg_signSum {n : ℕ} (a : Fin n → ℝ) : avg (fun x => signSum a x) = 0 := by
  obtain ⟨_, h, _⟩ := moments a
  simpa [mom] using h

/-- The average of the polynomial majorant of `|R|` in terms of the moments. -/
theorem avg_majorant_signSum {n : ℕ} (a : Fin n → ℝ) :
    avg (fun x => Algebra.majorant (signSum a x)) =
      (4336 * mom a 10 - 117880 * mom a 8 + 1187295 * mom a 6 - 5572600 * mom a 4
        + 15433465 * mom a 2 + 2903076) / 12862500 := by
  have h : (fun x => Algebra.majorant (signSum a x)) = fun x : Cube n =>
      (1 / 12862500 : ℝ) * (4336 * signSum a x ^ 10 - 117880 * signSum a x ^ 8
        + 1187295 * signSum a x ^ 6 - 5572600 * signSum a x ^ 4
        + 15433465 * signSum a x ^ 2 + 2903076) := by
    funext x
    unfold Algebra.majorant
    ring
  rw [h]
  unfold mom
  simp only [avg_const_mul, avg_add, avg_sub, avg_const_cube]
  ring

theorem pw_nonneg {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (hk : ∀ i, 0 ≤ a i ^ k) : 0 ≤ pw a k :=
  Finset.sum_nonneg fun i _ => hk i

/-- Under the cap `|a i| ≤ 2/5`, each even power sum is at most `4/25` times the previous one. -/
theorem pw_add_two_le {n : ℕ} (a : Fin n → ℝ) (hcap : ∀ i, |a i| ≤ 2 / 5) (k : ℕ)
    (hk : ∀ i, 0 ≤ a i ^ k) : pw a (k + 2) ≤ 4 / 25 * pw a k := by
  unfold pw
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := abs_le.mp (hcap i)
  have h1 : a i ^ 2 ≤ 4 / 25 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h.2) (by linarith : (0 : ℝ) ≤ a i + 2 / 5)]
  rw [pow_add]
  nlinarith [mul_le_mul_of_nonneg_left h1 (hk i)]

/-- The closing real-arithmetic estimate of `lem:rademacher` (App. D): with
`t = pw a 4`, `u = pw a 6`, `v = pw a 8`, `w = pw a 10` and the cap chain, the majorant average
is at most `7/8`. -/
theorem capped_poly_bound (t u v w : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 4 / 25)
    (hu : u ≤ 4 / 25 * t) (hv0 : 0 ≤ v) (hw : w ≤ 4 / 25 * v) :
    (5406800 * t ^ 2 - 14568960 * t * u - 1140425 * t + 4946680 * u - 10504640 * v
      + 17205248 * w + 5574143) / 6431250 ≤ 7 / 8 := by
  rw [div_le_iff₀ (by norm_num)]
  have h1 : 0 ≤ (4946680 - 14568960 * t) * (4 / 25 * t - u) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ t * (4 / 25 - t) := mul_nonneg ht0 (by linarith)
  nlinarith [h1, h2]

/-- Lemma lem:rademacher: Σ a_i² = 1 and max|a_i| ≤ 2/5 imply E|R| ≤ 7/8. -/
theorem capped_sign_sum {n : ℕ} (a : Fin n → ℝ) (hnorm : ∑ i, a i ^ 2 = 1)
    (hcap : ∀ i, |a i| ≤ 2 / 5) :
    avg (fun x => |signSum a x|) ≤ 7 / 8 := by
  have hmaj : avg (fun x => |signSum a x|) ≤ avg (fun x => Algebra.majorant (signSum a x)) :=
    avg_le_avg fun x => Algebra.majorant_absolute _
  refine le_trans hmaj ?_
  rw [avg_majorant_signSum]
  obtain ⟨_, _, h2, _, h4, _, h6, _, h8, _, h10⟩ := moments a
  have hP2 : pw a 2 = 1 := hnorm
  rw [h2, h4, h6, h8, h10, hP2]
  have e2 : ∀ i, 0 ≤ a i ^ 2 := fun i => by positivity
  have e4 : ∀ i, 0 ≤ a i ^ 4 := fun i => by positivity
  have e8 : ∀ i, 0 ≤ a i ^ 8 := fun i => by positivity
  have ht0 : 0 ≤ pw a 4 := pw_nonneg a 4 e4
  have hv0 : 0 ≤ pw a 8 := pw_nonneg a 8 e8
  have ht : pw a 4 ≤ 4 / 25 * pw a 2 := pw_add_two_le a hcap 2 e2
  have hu : pw a 6 ≤ 4 / 25 * pw a 4 := pw_add_two_le a hcap 4 e4
  have hw : pw a 10 ≤ 4 / 25 * pw a 8 := pw_add_two_le a hcap 8 e8
  rw [hP2, mul_one] at ht
  have key := capped_poly_bound (pw a 4) (pw a 6) (pw a 8) (pw a 10) ht0 ht hu hv0 hw
  refine le_trans (le_of_eq ?_) key
  ring

end CK
