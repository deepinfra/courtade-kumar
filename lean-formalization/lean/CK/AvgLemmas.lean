import CK.Semantics

/-! Linearity and monotonicity of the uniform average, and entropy positivity. -/
noncomputable section
namespace CK
open scoped BigOperators
open Finset

theorem avg_add {n : ℕ} (u v : Cube n → ℝ) :
    avg (fun x => u x + v x) = avg u + avg v := by
  unfold avg
  rw [Finset.sum_add_distrib, add_div]

theorem avg_const_mul {n : ℕ} (c : ℝ) (u : Cube n → ℝ) :
    avg (fun x => c * u x) = c * avg u := by
  unfold avg
  rw [← Finset.mul_sum, mul_div_assoc]

theorem avg_sub {n : ℕ} (u v : Cube n → ℝ) :
    avg (fun x => u x - v x) = avg u - avg v := by
  unfold avg
  rw [Finset.sum_sub_distrib, sub_div]

theorem avg_le_avg {n : ℕ} {u v : Cube n → ℝ} (h : ∀ x, u x ≤ v x) : avg u ≤ avg v := by
  unfold avg
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (by positivity)

theorem abs_avg_le_avg_abs {n : ℕ} (u : Cube n → ℝ) : |avg u| ≤ avg (fun x => |u x|) := by
  unfold avg
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)

theorem avg_of_unique (u : Cube 0 → ℝ) : avg u = u default := by
  unfold avg
  rw [Fintype.sum_unique]
  simp only [pow_zero, div_one]
  exact congrArg u (Subsingleton.elim _ _)

theorem binaryEntropy_nonneg' {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : 0 ≤ binaryEntropy a := by
  unfold binaryEntropy
  have l1 := Real.log_nonpos h0 h1
  have l2 := Real.log_nonpos (by linarith : (0 : ℝ) ≤ 1 - a) (by linarith : 1 - a ≤ 1)
  nlinarith

theorem binaryEntropy_symm (a : ℝ) : binaryEntropy (1 - a) = binaryEntropy a := by
  unfold binaryEntropy
  simp only [sub_sub_cancel]
  ring

theorem conditionalEntropy_nonneg {n : ℕ} (f : BooleanFunction n) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ conditionalEntropy f p := by
  unfold conditionalEntropy avg
  apply div_nonneg _ (by positivity)
  exact Finset.sum_nonneg fun y _ =>
    binaryEntropy_nonneg' (posterior_nonneg f p hp0 hp1 y) (posterior_le_one f p hp0 hp1 y)

theorem posterior_zero (g : BooleanFunction 0) (p : ℝ) (w : Cube 0) :
    posterior g p w = indicator (g default) := by
  unfold posterior
  rw [Fintype.sum_unique]
  have h := kernel_row_sum p w
  rw [Fintype.sum_unique] at h
  rw [h, one_mul]
  exact congrArg (fun x => indicator (g x)) (Subsingleton.elim _ _)

theorem mean_zero (g : BooleanFunction 0) : mean g = indicator (g default) := by
  unfold mean
  exact avg_of_unique _

end CK
