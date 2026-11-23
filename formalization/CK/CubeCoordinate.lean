import CK.Channel
import CK.GoodCoordinate

/-!
# The good-coordinate lemma on the exact Boolean cube

The uniform law below has expectation equal to the independently specified
`Spec.average`.  Independence and unbiasedness of two distinct coordinates are
proved by explicit coordinate-flip bijections, then the four-cell theorem gives
the manuscript's existential good-coordinate conclusion.
-/

noncomputable section
namespace CourtadeKumar.Spec
open scoped BigOperators

/-- The actual uniform probability law on the paper's Boolean cube. -/
def uniformCube (n : ℕ) : FiniteLaw (Cube n) where
  mass _ := 1 / (2 : ℝ) ^ n
  mass_nonneg _ := by positivity
  mass_sum := by
    simp [Cube, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

theorem uniformCube_expect_average {n : ℕ} (f : Cube n → ℝ) :
    (uniformCube n).expect f = average f := by
  change (∑ x : Cube n, (1 / (2 : ℝ) ^ n) * f x) = (∑ x : Cube n, f x) / 2 ^ n
  rw [← Finset.mul_sum]
  ring

/-- Flipping one coordinate is a bijection of the cube. -/
def flipCoordinate {n : ℕ} (i : Fin n) : Cube n ≃ Cube n where
  toFun x := Function.update x i (!(x i))
  invFun x := Function.update x i (!(x i))
  left_inv x := by
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [Function.update_apply, hk]
  right_inv x := by
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [Function.update_apply, hk]

@[simp] theorem flipCoordinate_same {n : ℕ} (i : Fin n) (x : Cube n) :
    flipCoordinate i x i = !(x i) := by simp [flipCoordinate]

theorem flipCoordinate_other {n : ℕ} (i j : Fin n) (hji : j ≠ i) (x : Cube n) :
    flipCoordinate i x j = x j := by simp [flipCoordinate, Function.update_apply, hji]

theorem uniformCube_pair_flip_first {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (s t : Bool) :
    (uniformCube n).fibreMass (fun x => (x i, x j)) (!s, t) =
      (uniformCube n).fibreMass (fun x => (x i, x j)) (s, t) := by
  unfold FiniteLaw.fibreMass
  change (∑ x : Cube n, if (x i, x j) = (!s, t) then 1 / (2 : ℝ) ^ n else 0) =
    ∑ x : Cube n, if (x i, x j) = (s, t) then 1 / (2 : ℝ) ^ n else 0
  rw [← (flipCoordinate i).sum_comp
    (fun x => if (x i, x j) = (s, t) then 1 / (2 : ℝ) ^ n else 0)]
  apply Finset.sum_congr rfl
  intro x _
  rw [flipCoordinate_same, flipCoordinate_other i j (Ne.symm hij)]
  cases hx : x i <;> cases s <;> simp [hx]

theorem uniformCube_pair_flip_second {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (s t : Bool) :
    (uniformCube n).fibreMass (fun x => (x i, x j)) (s, !t) =
      (uniformCube n).fibreMass (fun x => (x i, x j)) (s, t) := by
  unfold FiniteLaw.fibreMass
  change (∑ x : Cube n, if (x i, x j) = (s, !t) then 1 / (2 : ℝ) ^ n else 0) =
    ∑ x : Cube n, if (x i, x j) = (s, t) then 1 / (2 : ℝ) ^ n else 0
  rw [← (flipCoordinate j).sum_comp
    (fun x => if (x i, x j) = (s, t) then 1 / (2 : ℝ) ^ n else 0)]
  apply Finset.sum_congr rfl
  intro x _
  rw [flipCoordinate_other j i hij, flipCoordinate_same]
  cases hx : x j <;> cases t <;> simp [hx]

/-- Distinct coordinates of the uniform cube are independent unbiased bits. -/
theorem uniformCube_pair_mass {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (s t : Bool) :
    (uniformCube n).fibreMass (fun x => (x i, x j)) (s, t) = 1 / 4 := by
  have h10 := uniformCube_pair_flip_first i j hij false false
  have h01 := uniformCube_pair_flip_second i j hij false false
  have h11 := uniformCube_pair_flip_first i j hij false true
  have hsum := (uniformCube n).fibreMass_sum (fun x => (x i, x j))
  simp only [Bool.not_false] at h10 h01 h11
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at hsum
  cases s <;> cases t <;> linarith

/-- The manuscript's good-coordinate lemma, with all cube hypotheses discharged. -/
theorem good_coordinate {n : ℕ} (hn : 2 ≤ n) (f : Cube n → Bool) :
    ∃ i : Fin n,
      (uniformCube n).quadraticInformation (fun x => bit (f x)) (fun x => x i) ≤ 1 / 4 := by
  apply (uniformCube n).exists_good_coordinate hn (fun i x => x i) (fun x => bit (f x))
  · exact fun x => bit_nonneg (f x)
  · exact fun x => bit_le_one (f x)
  · exact fun i j hij s t => uniformCube_pair_mass i j hij s t

/-- The finite-law output mean agrees with the separately specified channel model. -/
theorem uniformCube_outputMean {n : ℕ} (f : Cube n → Bool) :
    (uniformCube n).expect (fun x => bit (f x)) = outputMean f :=
  uniformCube_expect_average _

end CourtadeKumar.Spec
