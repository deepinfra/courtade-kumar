import CK.Definitions

/-!
# Layer A: finite channel semantics -- NEW DRAFT (session 2), NOT YET ELABORATED

Row sums, symmetry and range of the product BSC kernel, and the mean of the
posterior. These are the first proof-dependency-order obligations (A1, A2, A5
in OBLIGATIONS.json). No proof shortcuts are used.
-/
noncomputable section
namespace CK
open scoped BigOperators
open Finset

theorem bool_sum_kernel_factor (p : ℝ) (b : Bool) :
    (∑ c : Bool, (if b = c then (1 - p) else p)) = 1 := by
  cases b <;> simp [Fintype.sum_bool]

/-- A1: every row of the product kernel sums to one. -/
theorem kernel_row_sum {n : ℕ} (p : ℝ) (y : Cube n) :
    (∑ x : Cube n, kernel p y x) = 1 := by
  unfold kernel
  have h := Fintype.prod_sum (fun (i : Fin n) (j : Bool) => if y i = j then (1 - p) else p)
  simp only [bool_sum_kernel_factor, Finset.prod_const_one] at h
  exact h.symm

/-- A2: the kernel is symmetric. -/
theorem kernel_symm {n : ℕ} (p : ℝ) (y x : Cube n) :
    kernel p y x = kernel p x y := by
  unfold kernel
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : y i = x i
  · simp [h]
  · have h' : ¬ x i = y i := fun e => h e.symm
    simp [h, h']

theorem kernel_nonneg {n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (y x : Cube n) :
    0 ≤ kernel p y x := by
  unfold kernel
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

theorem indicator_nonneg (b : Bool) : 0 ≤ indicator b := by
  cases b <;> simp [indicator]

theorem indicator_le_one (b : Bool) : indicator b ≤ 1 := by
  cases b <;> simp [indicator]

/-- The posterior is a probability. -/
theorem posterior_nonneg {n : ℕ} (f : BooleanFunction n) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (y : Cube n) : 0 ≤ posterior f p y := by
  unfold posterior
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (kernel_nonneg p hp0 hp1 y x) (indicator_nonneg (f x))

theorem posterior_le_one {n : ℕ} (f : BooleanFunction n) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (y : Cube n) : posterior f p y ≤ 1 := by
  unfold posterior
  calc (∑ x : Cube n, kernel p y x * indicator (f x))
      ≤ ∑ x : Cube n, kernel p y x := by
        apply Finset.sum_le_sum
        intro x _
        have := kernel_nonneg p hp0 hp1 y x
        nlinarith [indicator_le_one (f x)]
    _ = 1 := kernel_row_sum p y

/-- A5: the average posterior equals the output mean (the output is uniform). -/
theorem posterior_mean {n : ℕ} (f : BooleanFunction n) (p : ℝ) :
    avg (fun y => posterior f p y) = mean f := by
  unfold avg mean posterior
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul]
  have : (∑ y : Cube n, kernel p y x) = 1 := by
    calc (∑ y : Cube n, kernel p y x) = ∑ y : Cube n, kernel p x y :=
          Finset.sum_congr rfl fun y _ => kernel_symm p y x
      _ = 1 := kernel_row_sum p x
  rw [this, one_mul]

end CK
