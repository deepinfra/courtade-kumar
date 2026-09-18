import CK.Semantics

/-!
# Layer A3: posterior mixtures along the last coordinate (Lemma 2.3 / (2.4))

For `f` on `n+1` bits, split the last coordinate. `sectionLast f s` is the
section of `f` with the last input fixed to `s`. The posterior of `f` at an
observation whose last coordinate is `b` is the `(1-p, p)` mixture of the
posteriors of the two sections at the first `n` observed coordinates.
-/
noncomputable section
namespace CK
open scoped BigOperators
open Finset

/-- Section of `f` with the last coordinate fixed to `s`. -/
def sectionLast {n : ℕ} (f : BooleanFunction (n + 1)) (s : Bool) : BooleanFunction n :=
  fun w => f (Fin.snoc w s)

/-- The product kernel factors along the last coordinate. -/
theorem kernel_snoc {n : ℕ} (p : ℝ) (w w' : Cube n) (b s : Bool) :
    kernel p (Fin.snoc w b) (Fin.snoc w' s) =
      kernel p w w' * (if b = s then (1 - p) else p) := by
  unfold kernel
  rw [Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Lemma 2.3 / (2.4): the posterior is a mixture of the two section posteriors. -/
theorem posterior_snoc {n : ℕ} (f : BooleanFunction (n + 1)) (p : ℝ) (w : Cube n) (b : Bool) :
    posterior f p (Fin.snoc w b) =
      (1 - p) * posterior (sectionLast f b) p w + p * posterior (sectionLast f (!b)) p w := by
  unfold posterior
  rw [← Fintype.sum_equiv (Fin.snocEquiv fun _ => Bool) _ _ (fun q => rfl), Fintype.sum_prod_type]
  show (∑ s : Bool, ∑ w' : Cube n,
      kernel p (Fin.snoc w b) (Fin.snoc w' s) * indicator (f (Fin.snoc w' s))) = _
  simp_rw [kernel_snoc]
  rw [Fintype.sum_bool, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w' _ => ?_
  simp only [sectionLast]
  cases b <;> simp <;> ring

/-- Averaging over the `(n+1)`-cube splits into the two sections. -/
theorem avg_snoc {n : ℕ} (v : Cube (n + 1) → ℝ) :
    avg v = (avg (fun w : Cube n => v (Fin.snoc w true)) +
             avg (fun w : Cube n => v (Fin.snoc w false))) / 2 := by
  unfold avg
  rw [← Fintype.sum_equiv (Fin.snocEquiv fun _ => Bool) _ _ (fun q => rfl), Fintype.sum_prod_type]
  show (∑ s : Bool, ∑ w' : Cube n, v (Fin.snoc w' s)) / (2 : ℝ) ^ (n + 1) = _
  rw [Fintype.sum_bool, pow_succ]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  field_simp

/-- (2.6): the mean of `f` is the average of the section means. -/
theorem mean_snoc {n : ℕ} (f : BooleanFunction (n + 1)) :
    mean f = (mean (sectionLast f true) + mean (sectionLast f false)) / 2 := by
  unfold mean
  rw [avg_snoc]
  rfl

/-- (2.5): the conditional entropy is the average of the two-posterior mixture entropies. -/
theorem conditionalEntropy_snoc {n : ℕ} (f : BooleanFunction (n + 1)) (p : ℝ) :
    conditionalEntropy f p =
      avg (fun w : Cube n =>
        (binaryEntropy ((1 - p) * posterior (sectionLast f true) p w
                        + p * posterior (sectionLast f false) p w)
         + binaryEntropy ((1 - p) * posterior (sectionLast f false) p w
                        + p * posterior (sectionLast f true) p w)) / 2) := by
  unfold conditionalEntropy
  rw [avg_snoc]
  simp only [posterior_snoc, Bool.not_true, Bool.not_false]
  unfold avg
  beta_reduce
  rw [div_add_div_same, ← Finset.sum_add_distrib, div_div, div_eq_inv_mul, div_eq_inv_mul,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  field_simp
