import CK.Spec
import CK.Entropy

/-!+# Finite semantics of the binary symmetric channel

The product-channel arguments are adapted from the earlier branch's
`CK/Semantics.lean`, with independent definitions and base-two entropies.
-/

noncomputable section
namespace CourtadeKumar.Spec
open scoped BigOperators

theorem bit_nonneg (b : Bool) : 0 ≤ bit b := by cases b <;> simp [bit]
theorem bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> simp [bit]

theorem bool_channel_sum (p : ℝ) (b : Bool) :
    (∑ c : Bool, if b = c then 1 - p else p) = 1 := by
  cases b <;> simp [Fintype.sum_bool]

theorem channel_row_sum {n : ℕ} (p : ℝ) (x : Cube n) :
    (∑ y : Cube n, channel p x y) = 1 := by
  unfold channel
  have h := Fintype.prod_sum
    (fun (i : Fin n) (b : Bool) => if x i = b then 1 - p else p)
  simp only [bool_channel_sum, Finset.prod_const_one] at h
  exact h.symm

theorem channel_symm {n : ℕ} (p : ℝ) (x y : Cube n) :
    channel p x y = channel p y x := by
  unfold channel
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : x i = y i
  · simp [h]
  · have h' : ¬y i = x i := fun e => h e.symm
    simp [h, h']

theorem channel_column_sum {n : ℕ} (p : ℝ) (y : Cube n) :
    (∑ x : Cube n, channel p x y) = 1 := by
  simp_rw [channel_symm p _ y]
  exact channel_row_sum p y

theorem channel_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x y : Cube n) : 0 ≤ channel p x y := by
  unfold channel
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

theorem average_const (n : ℕ) (c : ℝ) : average (n := n) (fun _ => c) = c := by
  unfold average
  simp [Cube, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

theorem average_nonneg {n : ℕ} {f : Cube n → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ average f := by
  unfold average
  exact div_nonneg (Finset.sum_nonneg (fun x _ => hf x)) (by positivity)

theorem average_mono {n : ℕ} {f g : Cube n → ℝ} (hfg : ∀ x, f x ≤ g x) :
    average f ≤ average g := by
  unfold average
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hfg x)) (by positivity)

theorem outputMean_mem {n : ℕ} (f : Cube n → Bool) :
    0 ≤ outputMean f ∧ outputMean f ≤ 1 := by
  constructor
  · exact average_nonneg (fun x => bit_nonneg (f x))
  · calc outputMean f ≤ average (n := n) (fun _ => 1) :=
           average_mono (fun x => bit_le_one (f x))
      _ = 1 := average_const n 1

theorem outputPosterior_mem {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Cube n) :
    0 ≤ outputPosterior f p x ∧ outputPosterior f p x ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun y _ =>
      mul_nonneg (channel_nonneg hp0 hp1 x y) (bit_nonneg (f y)))
  · calc outputPosterior f p x ≤ ∑ y : Cube n, channel p x y := by
           apply Finset.sum_le_sum
           intro y _
           exact mul_le_of_le_one_right (channel_nonneg hp0 hp1 x y) (bit_le_one (f y))
      _ = 1 := channel_row_sum p x

/-- The product channel preserves the uniform measure. -/
theorem average_outputPosterior {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    average (outputPosterior f p) = outputMean f := by
  unfold average outputMean outputPosterior
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_mul, channel_column_sum, one_mul]

/-- Fully discharged right-hand inequality of Theorem `thm:ck+`. -/
theorem progressiveBound_le_capacity {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    progressiveBound p (outputMean f) ≤ 1 - entropy p := by
  have hmean := outputMean_mem f
  exact progressiveEntropy_le_noiseInformation hp0 hp1 hmean.1 hmean.2

theorem classical_of_latest (h : LatestPaperTarget) : ClassicalTarget := by
  intro n f p hp0 hp1
  exact (h n f p hp0 hp1).1.trans (h n f p hp0 hp1).2

end CourtadeKumar.Spec
