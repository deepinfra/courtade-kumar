import CK.Sections

/-!
# Layer A6a: coordinate relabelling invariance

Permuting the input coordinates of `f` (and the observation accordingly)
changes neither the mean nor the conditional entropy. This is what lets the
induction put the small-gap coordinate of Lemma 2.2 in the last position.
-/
noncomputable section
namespace CK
open scoped BigOperators
open Finset

/-- Relabel the coordinates of `f` by the permutation `σ`. -/
def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : BooleanFunction n) : BooleanFunction n :=
  fun x => f (x ∘ σ)

/-- Precomposition with `σ` is a bijection of the cube. -/
def permCube {n : ℕ} (σ : Equiv.Perm (Fin n)) : Cube n ≃ Cube n where
  toFun x := x ∘ σ
  invFun x := x ∘ σ.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

theorem permCube_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Cube n) :
    permCube σ x = x ∘ σ := rfl

theorem sum_cube_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (F : Cube n → ℝ) :
    (∑ x : Cube n, F (x ∘ σ)) = ∑ x : Cube n, F x :=
  Equiv.sum_comp (permCube σ) F

theorem kernel_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : ℝ) (y x : Cube n) :
    kernel p (y ∘ σ) (x ∘ σ) = kernel p y x := by
  unfold kernel
  exact Equiv.prod_comp σ (fun j => if y j = x j then (1 - p) else p)

theorem posterior_relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : BooleanFunction n) (p : ℝ)
    (y : Cube n) : posterior (relabel σ f) p y = posterior f p (y ∘ σ) := by
  unfold posterior relabel
  rw [← sum_cube_comp σ.symm (fun x => kernel p y x * indicator (f (x ∘ σ)))]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : (x ∘ ⇑σ.symm) ∘ ⇑σ = x := by funext i; simp
  have h2 : kernel p y (x ∘ ⇑σ.symm) = kernel p (y ∘ σ) x := by
    rw [← kernel_comp σ p y (x ∘ ⇑σ.symm), h1]
  rw [h1, h2]

theorem avg_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Cube n → ℝ) :
    avg (fun y => v (y ∘ σ)) = avg v := by
  unfold avg
  rw [sum_cube_comp σ v]

theorem mean_relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : BooleanFunction n) :
    mean (relabel σ f) = mean f := by
  unfold mean relabel
  exact avg_comp σ (fun x => indicator (f x))

theorem conditionalEntropy_relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : BooleanFunction n)
    (p : ℝ) : conditionalEntropy (relabel σ f) p = conditionalEntropy f p := by
  unfold conditionalEntropy
  simp only [posterior_relabel]
  exact avg_comp σ (fun y => binaryEntropy (posterior f p y))

theorem information_relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : BooleanFunction n)
    (p : ℝ) : information (relabel σ f) p = information f p := by
  unfold information
  rw [mean_relabel, conditionalEntropy_relabel]

end CK
