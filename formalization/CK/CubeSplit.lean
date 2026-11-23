import CK.CubeCoordinate
import CK.GapBounds
import CK.MapLaws
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field

/-!
# Coordinate restriction and the actual product-noise probability law

This file constructs the joint law used by the independently specified cube
target and splits any chosen coordinate into its own binary channel.
-/

noncomputable section
namespace CourtadeKumar.Spec
open scoped BigOperators

/-- Insert one distinguished coordinate; its inverse is restriction to all others. -/
def joinCoordinate {n : ℕ} (i : Fin (n + 1)) : Bool × Cube n ≃ Cube (n + 1) :=
  Fin.insertNthEquiv (fun _ => Bool) i

def restrictCoordinate {n : ℕ} (i : Fin (n + 1)) (f : Cube (n + 1) → Bool)
    (b : Bool) : Cube n → Bool := fun y => f (joinCoordinate i (b, y))

@[simp] theorem joinCoordinate_same {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Cube n) :
    joinCoordinate i (b, x) i = b := Fin.insertNth_apply_same (α := fun _ => Bool) i b x

@[simp] theorem joinCoordinate_other {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Cube n)
    (j : Fin n) : joinCoordinate i (b, x) (i.succAbove j) = x j :=
  Fin.insertNth_apply_succAbove (α := fun _ => Bool) i b x j

theorem channel_joinCoordinate {n : ℕ} (i : Fin (n + 1)) (p : ℝ)
    (a b : Bool) (x y : Cube n) :
    channel p (joinCoordinate i (a, x)) (joinCoordinate i (b, y)) =
      (if a = b then 1 - p else p) * channel p x y := by
  unfold channel
  rw [Fin.prod_univ_succAbove _ i]
  simp

theorem sum_joinCoordinate {n : ℕ} (i : Fin (n + 1)) (g : Cube (n + 1) → ℝ) :
    ∑ x, g x = ∑ b : Bool, ∑ y : Cube n, g (joinCoordinate i (b, y)) := by
  rw [← (joinCoordinate i).sum_comp g, Fintype.sum_prod_type]

theorem sum_coordinate_fibre {n : ℕ} (i : Fin (n + 1)) (g : Cube (n + 1) → ℝ) (b : Bool) :
    (∑ y, if y i = b then g y else 0) = ∑ z : Cube n, g (joinCoordinate i (b, z)) := by
  rw [sum_joinCoordinate i]
  simp only [joinCoordinate_same, ← Finset.sum_ite_irrel]
  simp

theorem average_joinCoordinate {n : ℕ} (i : Fin (n + 1)) (g : Cube (n + 1) → ℝ) :
    average g = (average (fun y => g (joinCoordinate i (false, y))) +
      average (fun y => g (joinCoordinate i (true, y)))) / 2 := by
  unfold average
  rw [sum_joinCoordinate i, Fintype.sum_bool, pow_succ]
  ring

/-- The uniform input and product binary-symmetric channel, on its actual sample space. -/
def jointLaw (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteLaw (Cube n × Cube n) where
  mass xy := channel p xy.1 xy.2 / (2 : ℝ) ^ n
  mass_nonneg xy := div_nonneg (channel_nonneg hp0 hp1 xy.1 xy.2) (by positivity)
  mass_sum := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_div, channel_row_sum]
    simp [Cube, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

theorem jointLaw_fibreMass_first {n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : Cube n) : (jointLaw n p hp0 hp1).fibreMass Prod.fst x = 1 / (2 : ℝ) ^ n := by
  unfold FiniteLaw.fibreMass jointLaw
  rw [Fintype.sum_prod_type]
  simp only [ite_div, zero_div, ← Finset.sum_ite_irrel, ← Finset.sum_div, channel_row_sum]
  simp
  rw [← Finset.sum_div, channel_row_sum]
  simp

theorem jointLaw_fibreMass_second {n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (y : Cube n) : (jointLaw n p hp0 hp1).fibreMass Prod.snd y = 1 / (2 : ℝ) ^ n := by
  unfold FiniteLaw.fibreMass jointLaw
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [ite_div, zero_div, ← Finset.sum_ite_irrel, ← Finset.sum_div, channel_column_sum]
  simp
  rw [← Finset.sum_div, channel_column_sum]
  simp

theorem jointLaw_expect_second {n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (g : Cube n → ℝ) : (jointLaw n p hp0 hp1).expect (fun xy => g xy.2) = average g := by
  unfold FiniteLaw.expect jointLaw average
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, ← Finset.sum_mul, channel_column_sum, one_mul]

theorem jointLaw_fibreMoment_first {n : ℕ} (f : Cube n → Bool) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Cube n) :
    (jointLaw n p hp0 hp1).fibreMoment Prod.fst (fun xy => FiniteLaw.bitValue (f xy.2)) x =
      outputPosterior f p x / (2 : ℝ) ^ n := by
  unfold FiniteLaw.fibreMoment jointLaw outputPosterior
  rw [Fintype.sum_prod_type]
  simp only [← Finset.sum_ite_irrel]
  simp [FiniteLaw.bitValue, bit, div_mul_eq_mul_div, Finset.sum_div, ite_div]

theorem jointLaw_conditionalMean_first {n : ℕ} (f : Cube n → Bool) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Cube n) :
    (jointLaw n p hp0 hp1).conditionalMean Prod.fst (fun xy => FiniteLaw.bitValue (f xy.2)) x =
      outputPosterior f p x := by
  unfold FiniteLaw.conditionalMean
  rw [jointLaw_fibreMoment_first, jointLaw_fibreMass_first]
  field_simp

/-- Agreement with the independently stated finite-sum information target. -/
theorem jointLaw_shannonInformation {n : ℕ} (f : Cube n → Bool) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (jointLaw n p hp0 hp1).shannonInformation (fun xy => FiniteLaw.bitValue (f xy.2)) Prod.fst =
      mutualInformation f p := by
  unfold FiniteLaw.shannonInformation
  rw [jointLaw_expect_second p hp0 hp1 (fun y => FiniteLaw.bitValue (f y))]
  change entropy (outputMean f) - _ = _
  unfold FiniteLaw.conditionalShannonEntropy FiniteLaw.expect FiniteLaw.map mutualInformation average
  simp only [jointLaw_fibreMass_first, jointLaw_conditionalMean_first]
  change _ - ∑ x, 1 / (2 : ℝ) ^ n * entropy (outputPosterior f p x) = _
  rw [← Finset.mul_sum]
  ring

theorem jointLaw_progressiveGap {n : ℕ} (f : Cube n → Bool) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (jointLaw n p hp0 hp1).progressiveGap p (fun xy => f xy.2) Prod.fst =
      progressiveBound p (outputMean f) - mutualInformation f p := by
  unfold FiniteLaw.progressiveGap
  rw [jointLaw_expect_second p hp0 hp1 (fun y => FiniteLaw.bitValue (f y)), jointLaw_shannonInformation]
  rfl

theorem jointLaw_map_second {n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (jointLaw n p hp0 hp1).map Prod.snd = uniformCube n := by
  apply FiniteLaw.eq_of_mass_eq
  exact jointLaw_fibreMass_second p hp0 hp1

theorem jointLaw_quadraticInformation_coordinate {n : ℕ} (f : Cube n → Bool) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin n) :
    (jointLaw n p hp0 hp1).quadraticInformation (fun xy => bit (f xy.2)) (fun xy => xy.2 i) =
      (uniformCube n).quadraticInformation (fun y => bit (f y)) (fun y => y i) := by
  rw [← (jointLaw n p hp0 hp1).quadraticInformation_map Prod.snd (fun y => y i)
    (fun y => bit (f y)), jointLaw_map_second]

theorem jointLaw_fibreMass_coordinate {n : ℕ} (i : Fin (n + 1)) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    (jointLaw (n + 1) p hp0 hp1).fibreMass (fun xy => xy.2 i) b = 1 / 2 := by
  rw [FiniteLaw.fibreMass_eq_expect, jointLaw_expect_second p hp0 hp1
    (fun y => if y i = b then 1 else 0)]
  unfold average
  rw [sum_coordinate_fibre i (fun _ => 1)]
  simp [Cube, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, pow_succ]
  field_simp

theorem jointLaw_fibreMoment_coordinate {n : ℕ} (i : Fin (n + 1)) (f : Cube (n + 1) → Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    (jointLaw (n + 1) p hp0 hp1).fibreMoment (fun xy => xy.2 i)
      (fun xy => FiniteLaw.bitValue (f xy.2)) b = outputMean (restrictCoordinate i f b) / 2 := by
  rw [FiniteLaw.fibreMoment_eq_expect, jointLaw_expect_second p hp0 hp1
    (fun y => if y i = b then FiniteLaw.bitValue (f y) else 0)]
  unfold average
  rw [sum_coordinate_fibre i]
  change (∑ y, bit (restrictCoordinate i f b y)) / 2 ^ (n + 1) = _
  unfold outputMean average
  rw [pow_succ]
  ring

theorem jointLaw_conditionalMean_coordinate {n : ℕ} (i : Fin (n + 1)) (f : Cube (n + 1) → Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    (jointLaw (n + 1) p hp0 hp1).conditionalMean (fun xy => xy.2 i)
      (fun xy => FiniteLaw.bitValue (f xy.2)) b = outputMean (restrictCoordinate i f b) := by
  unfold FiniteLaw.conditionalMean
  rw [jointLaw_fibreMoment_coordinate, jointLaw_fibreMass_coordinate]
  ring

theorem jointLaw_coordinate_entropy {n : ℕ} (i : Fin (n + 1)) (f : Cube (n + 1) → Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : ℝ → ℝ) :
    ((jointLaw (n + 1) p hp0 hp1).map (fun xy => xy.2 i)).expect
      (fun b => F ((jointLaw (n + 1) p hp0 hp1).conditionalMean (fun xy => xy.2 i)
        (fun xy => FiniteLaw.bitValue (f xy.2)) b)) =
      (F (outputMean (restrictCoordinate i f false)) + F (outputMean (restrictCoordinate i f true))) / 2 := by
  unfold FiniteLaw.expect FiniteLaw.map
  simp only [jointLaw_fibreMass_coordinate, jointLaw_conditionalMean_coordinate, Fintype.sum_bool]
  ring

theorem jointLaw_coordinate_input_moment {n : ℕ} (i : Fin (n + 1)) (g : Cube (n + 1) → ℝ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) (x : Cube (n + 1)) :
    (jointLaw (n + 1) p hp0 hp1).fibreMoment (fun xy => (xy.2 i, xy.1))
      (fun xy => g xy.2) (b, x) =
      (∑ y, if y i = b then channel p x y * g y else 0) / (2 : ℝ) ^ (n + 1) := by
  unfold FiniteLaw.fibreMoment jointLaw
  rw [Fintype.sum_prod_type]
  simp only [Prod.mk.injEq, and_comm, ite_and, ← Finset.sum_ite_irrel]
  simp [div_mul_eq_mul_div, Finset.sum_div, ite_div, zero_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y i = b
  · simp [hy]
  · simp [hy]

theorem jointLaw_coordinate_input_fibreMoment {n : ℕ} (i : Fin (n + 1))
    (f : Cube (n + 1) → Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : Bool) (x : Cube n) :
    (jointLaw (n + 1) p hp0 hp1).fibreMoment (fun xy => (xy.2 i, xy.1))
      (fun xy => FiniteLaw.bitValue (f xy.2)) (b, joinCoordinate i (a, x)) =
      (if a = b then 1 - p else p) * outputPosterior (restrictCoordinate i f b) p x /
        (2 : ℝ) ^ (n + 1) := by
  rw [jointLaw_coordinate_input_moment i (fun y => FiniteLaw.bitValue (f y)) p hp0 hp1 b,
    sum_coordinate_fibre i]
  simp only [channel_joinCoordinate]
  rw [show (∑ y : Cube n,
      (if a = b then 1 - p else p) * channel p x y *
        FiniteLaw.bitValue (f (joinCoordinate i (b, y)))) =
      (if a = b then 1 - p else p) *
        (∑ y : Cube n, channel p x y * bit (restrictCoordinate i f b y)) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    change (if a = b then 1 - p else p) * channel p x y * bit (restrictCoordinate i f b y) = _
    ring]
  rfl

theorem jointLaw_coordinate_input_fibreMass {n : ℕ} (i : Fin (n + 1))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a b : Bool) (x : Cube n) :
    (jointLaw (n + 1) p hp0 hp1).fibreMass (fun xy => (xy.2 i, xy.1))
      (b, joinCoordinate i (a, x)) = (if a = b then 1 - p else p) / (2 : ℝ) ^ (n + 1) := by
  have he : (jointLaw (n + 1) p hp0 hp1).fibreMass (fun xy => (xy.2 i, xy.1))
      (b, joinCoordinate i (a, x)) =
    (jointLaw (n + 1) p hp0 hp1).fibreMoment (fun xy => (xy.2 i, xy.1))
      (fun _ => 1) (b, joinCoordinate i (a, x)) := by simp [FiniteLaw.fibreMass, FiniteLaw.fibreMoment]
  rw [he, jointLaw_coordinate_input_moment i (fun _ => 1) p hp0 hp1 b,
    sum_coordinate_fibre i]
  simp only [channel_joinCoordinate, mul_one, ← Finset.mul_sum, channel_row_sum]

theorem jointLaw_coordinate_input_mean_function {n : ℕ} (i : Fin (n + 1))
    (f : Cube (n + 1) → Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : Bool) (x : Cube n) (F : ℝ → ℝ) :
    (jointLaw (n + 1) p hp0 hp1).fibreMass (fun xy => (xy.2 i, xy.1)) (b, joinCoordinate i (a, x)) *
      F ((jointLaw (n + 1) p hp0 hp1).conditionalMean (fun xy => (xy.2 i, xy.1))
        (fun xy => FiniteLaw.bitValue (f xy.2)) (b, joinCoordinate i (a, x))) =
      (if a = b then 1 - p else p) / (2 : ℝ) ^ (n + 1) *
        F (outputPosterior (restrictCoordinate i f b) p x) := by
  unfold FiniteLaw.conditionalMean
  rw [jointLaw_coordinate_input_fibreMass, jointLaw_coordinate_input_fibreMoment]
  by_cases hw : (if a = b then 1 - p else p) = 0
  · simp [hw]
  · congr 1
    congr 1
    by_cases hab : a = b
    · simp only [if_pos hab] at hw ⊢
      field_simp [hw]
    · simp only [if_neg hab] at hw ⊢
      field_simp [hw]

theorem jointLaw_coordinate_input_entropy {n : ℕ} (i : Fin (n + 1))
    (f : Cube (n + 1) → Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : ℝ → ℝ) :
    ((jointLaw (n + 1) p hp0 hp1).map (fun xy => (xy.2 i, xy.1))).expect
      (fun bx => F ((jointLaw (n + 1) p hp0 hp1).conditionalMean (fun xy => (xy.2 i, xy.1))
        (fun xy => FiniteLaw.bitValue (f xy.2)) bx)) =
      (average (fun x => F (outputPosterior (restrictCoordinate i f false) p x)) +
        average (fun x => F (outputPosterior (restrictCoordinate i f true) p x))) / 2 := by
  unfold FiniteLaw.expect FiniteLaw.map
  rw [Fintype.sum_prod_type]
  simp_rw [sum_joinCoordinate i, jointLaw_coordinate_input_mean_function]
  have hs (b : Bool) :
      (∑ a : Bool, ∑ x : Cube n, (if a = b then 1 - p else p) / (2 : ℝ) ^ (n + 1) *
        F (outputPosterior (restrictCoordinate i f b) p x)) =
      (∑ x : Cube n, F (outputPosterior (restrictCoordinate i f b) p x)) / (2 : ℝ) ^ (n + 1) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Finset.sum_div]
    have hb : (∑ a : Bool, if a = b then 1 - p else p) = 1 := by
      cases b <;> simp [Fintype.sum_bool]
    rw [hb]
    rw [← Finset.mul_sum]
    ring
  simp_rw [hs]
  rw [Fintype.sum_bool]
  unfold average
  rw [pow_succ]
  ring

/-- Conditioning on a coordinate leaves exactly the average of the two lower-dimensional gaps. -/
theorem jointLaw_conditionalProgressiveGap {n : ℕ} (i : Fin (n + 1))
    (f : Cube (n + 1) → Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (jointLaw (n + 1) p hp0 hp1).conditionalProgressiveGap p (fun xy => f xy.2)
      Prod.fst (fun xy => xy.2 i) =
      ((progressiveBound p (outputMean (restrictCoordinate i f false)) -
          mutualInformation (restrictCoordinate i f false) p) +
        (progressiveBound p (outputMean (restrictCoordinate i f true)) -
          mutualInformation (restrictCoordinate i f true) p)) / 2 := by
  rw [FiniteLaw.conditionalProgressiveGap_eq, FiniteLaw.conditionalShannonInformation_eq_entropy_diff]
  unfold FiniteLaw.conditionalShannonEntropy FiniteLaw.conditionalQuadraticEntropy
  rw [jointLaw_coordinate_entropy, jointLaw_coordinate_entropy, jointLaw_coordinate_input_entropy]
  unfold progressiveBound mutualInformation noiseGap noiseInformation noiseCorrelationSq
    quadraticEntropy entropyBits entropy
  ring

/-- The induction hypothesis on the two literal coordinate restrictions supplies `Δ ≥ 0`. -/
theorem jointLaw_conditionalGap_nonneg {n : ℕ} (i : Fin (n + 1))
    (f : Cube (n + 1) → Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hIH : ∀ g : Cube n → Bool, mutualInformation g p ≤ progressiveBound p (outputMean g)) :
    0 ≤ (jointLaw (n + 1) p hp0 hp1).conditionalProgressiveGap p (fun xy => f xy.2)
      Prod.fst (fun xy => xy.2 i) := by
  rw [jointLaw_conditionalProgressiveGap]
  have hf := hIH (restrictCoordinate i f false)
  have ht := hIH (restrictCoordinate i f true)
  linarith

end CourtadeKumar.Spec
