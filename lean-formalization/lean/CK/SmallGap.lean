import CK.Relabel
import CK.Algebra

/-!
# Layer A6b: the small-gap coordinate (Lemma 2.2)

For `f` on `n+2` bits, either the last coordinate or the second-to-last
coordinate has section-mean gap at most `1/2`, because the two gaps add up to
at most one (both are signed combinations of the four quarter means).
-/
noncomputable section
namespace CK
open scoped BigOperators
open Finset

/-- The transposition of the last two coordinates. -/
def swapLast (n : ℕ) : Equiv.Perm (Fin (n + 2)) :=
  Equiv.swap (Fin.last (n + 1)) (Fin.castSucc (Fin.last n))

theorem snoc_snoc_swap {n : ℕ} (w : Cube n) (s t : Bool) :
    ((Fin.snoc (Fin.snoc w s) t : Cube (n + 2)) ∘ ⇑(swapLast n)) =
      (Fin.snoc (Fin.snoc w t) s : Cube (n + 2)) := by
  funext i
  simp only [Function.comp]
  induction i using Fin.lastCases with
  | last => simp [swapLast, Fin.snoc_last, Fin.snoc_castSucc]
  | cast i =>
    induction i using Fin.lastCases with
    | last => simp [swapLast, Fin.snoc_last, Fin.snoc_castSucc]
    | cast k =>
      have h1 : Fin.castSucc (Fin.castSucc k) ≠ Fin.last (n + 1) :=
        (Fin.castSucc_lt_last _).ne
      have h2 : Fin.castSucc (Fin.castSucc k) ≠ Fin.castSucc (Fin.last n) :=
        fun h => (Fin.castSucc_lt_last k).ne (Fin.castSucc_injective _ h)
      simp [swapLast, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.snoc_castSucc]

theorem sectionLast_relabel_swap {n : ℕ} (f : BooleanFunction (n + 2)) (t : Bool) (s : Bool) :
    sectionLast (sectionLast (relabel (swapLast n) f) t) s =
      sectionLast (sectionLast f s) t := by
  funext w
  simp only [sectionLast, relabel]
  rw [snoc_snoc_swap]

theorem mean_nonneg {n : ℕ} (f : BooleanFunction n) : 0 ≤ mean f := by
  unfold mean avg
  apply div_nonneg
  · exact Finset.sum_nonneg fun x _ => indicator_nonneg (f x)
  · positivity

theorem mean_le_one {n : ℕ} (f : BooleanFunction n) : mean f ≤ 1 := by
  unfold mean avg
  rw [div_le_one (by positivity)]
  calc (∑ x : Cube n, indicator (f x)) ≤ ∑ _x : Cube n, (1 : ℝ) :=
        Finset.sum_le_sum fun x _ => indicator_le_one (f x)
    _ = (2 : ℝ) ^ n := by simp [Finset.card_univ, Fintype.card_fun]

/-- Gap between the two section means along the last coordinate. -/
def gapLast {n : ℕ} (f : BooleanFunction (n + 1)) : ℝ :=
  |mean (sectionLast f true) - mean (sectionLast f false)|

theorem mean_sectionLast_relabel_swap {n : ℕ} (f : BooleanFunction (n + 2)) (t : Bool) :
    mean (sectionLast (relabel (swapLast n) f) t) =
      (mean (sectionLast (sectionLast f true) t) + mean (sectionLast (sectionLast f false) t)) / 2 := by
  rw [mean_snoc, sectionLast_relabel_swap, sectionLast_relabel_swap]

/-- Lemma 2.2, two-coordinate form: the two gaps sum to at most one. -/
theorem gap_sum_le_one {n : ℕ} (f : BooleanFunction (n + 2)) :
    gapLast f + gapLast (relabel (swapLast n) f) ≤ 1 := by
  unfold gapLast
  rw [mean_snoc (sectionLast f true), mean_snoc (sectionLast f false),
    mean_sectionLast_relabel_swap, mean_sectionLast_relabel_swap]
  have a1 := mean_nonneg (sectionLast (sectionLast f true) true)
  have a2 := mean_le_one (sectionLast (sectionLast f true) true)
  have b1 := mean_nonneg (sectionLast (sectionLast f true) false)
  have b2 := mean_le_one (sectionLast (sectionLast f true) false)
  have c1 := mean_nonneg (sectionLast (sectionLast f false) true)
  have c2 := mean_le_one (sectionLast (sectionLast f false) true)
  have d1 := mean_nonneg (sectionLast (sectionLast f false) false)
  have d2 := mean_le_one (sectionLast (sectionLast f false) false)
  rcases abs_cases ((mean (sectionLast (sectionLast f true) true) + mean (sectionLast (sectionLast f true) false)) / 2 -
      (mean (sectionLast (sectionLast f false) true) + mean (sectionLast (sectionLast f false) false)) / 2) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
  rcases abs_cases ((mean (sectionLast (sectionLast f true) true) + mean (sectionLast (sectionLast f false) true)) / 2 -
      (mean (sectionLast (sectionLast f true) false) + mean (sectionLast (sectionLast f false) false)) / 2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
  linarith

theorem relabel_one {n : ℕ} (f : BooleanFunction n) : relabel 1 f = f := by
  funext x; rfl

/-- Lemma 2.2 in the form the induction uses: some relabelling has last-coordinate gap `≤ 1/2`. -/
theorem exists_small_gap {n : ℕ} (f : BooleanFunction (n + 2)) :
    ∃ σ : Equiv.Perm (Fin (n + 2)), gapLast (relabel σ f) ≤ 1 / 2 := by
  rcases Algebra.small_gap_pair _ _ (gap_sum_le_one f) with h | h
  · exact ⟨1, by rw [relabel_one]; exact h⟩
  · exact ⟨swapLast n, h⟩

end CK
