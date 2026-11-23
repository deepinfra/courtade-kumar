import CK.CubeSplit
import CK.BinaryProfileSemantics

/-! # The coordinate channel: literal independence and Markov factorization -/

noncomputable section
namespace CourtadeKumar.FiniteLaw
open scoped BigOperators

theorem sum_pair_fibreMoment {Ω U Z : Type*} [Fintype Ω] [DecidableEq U]
    [Fintype Z] [DecidableEq Z] (μ : FiniteLaw Ω) (u : Ω → U) (z : Ω → Z)
    (c : Ω → ℝ) (a : U) :
    ∑ b, μ.fibreMoment (fun ω => (u ω, z ω)) c (a, b) = μ.fibreMoment u c a := by
  unfold fibreMoment
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hu : u ω = a <;> simp [hu]

theorem fibreMoment_bit_pair {Ω U : Type*} [Fintype Ω] [DecidableEq U]
    (μ : FiniteLaw Ω) (u : Ω → U) (b : Ω → Bool) (a : U) :
    μ.fibreMoment u (fun ω => bitValue (b ω)) a =
      μ.fibreMass (fun ω => (u ω, b ω)) (a, true) := by
  unfold fibreMoment fibreMass
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hu : u ω = a <;> cases hb : b ω <;> simp [hu, hb, bitValue]

theorem conditionalIndependence_conditionOn {Ω U : Type*} [Fintype Ω]
    [Fintype U] [DecidableEq U] (μ : FiniteLaw Ω) (a b c : Ω → Bool) (u : Ω → U)
    (hmark : μ.conditionallyIndependentBit c a (fun ω => (u ω, b ω)))
    (s : U) (hs : μ.fibreMass u s ≠ 0) :
    (μ.conditionOn u s).conditionallyIndependentBit c a b := by
  intro t z
  have hm := μ.mass_mul_conditionOn_fibreMass u b s t
  have hM := μ.mass_mul_conditionOn_fibreMoment u b s t (fun ω => bitValue (c ω))
  have hmp := μ.mass_mul_conditionOn_fibreMass u (fun ω => (b ω, a ω)) s (t, z)
  have hMp := μ.mass_mul_conditionOn_fibreMoment u (fun ω => (b ω, a ω)) s (t, z)
    (fun ω => bitValue (c ω))
  have em : μ.fibreMass (fun ω => (u ω, (b ω, a ω))) (s, (t, z)) =
      μ.fibreMass (fun ω => ((u ω, b ω), a ω)) ((s, t), z) := by
    simp [fibreMass, Prod.mk.injEq, and_assoc]
  have eM : μ.fibreMoment (fun ω => (u ω, (b ω, a ω))) (fun ω => bitValue (c ω)) (s, (t, z)) =
      μ.fibreMoment (fun ω => ((u ω, b ω), a ω)) (fun ω => bitValue (c ω)) ((s, t), z) := by
    simp [fibreMoment, Prod.mk.injEq, and_assoc]
  rw [em] at hmp
  rw [eM] at hMp
  have h := hmark (s, t) z
  rw [← hm, ← hM, ← hmp, ← hMp] at h
  apply (mul_left_cancel₀ (mul_ne_zero hs hs))
  nlinarith only [h]

end CourtadeKumar.FiniteLaw

namespace CourtadeKumar.Spec
open scoped BigOperators

def otherCoordinates {n : ℕ} (i : Fin (n + 1)) (x : Cube (n + 1)) : Cube n :=
  Fin.removeNth i x

def splitInput {n : ℕ} (i : Fin (n + 1)) : Cube (n + 1) ≃ Cube n × Bool :=
  (joinCoordinate i).symm.trans (Equiv.prodComm Bool (Cube n))

@[simp] theorem splitInput_apply {n : ℕ} (i : Fin (n + 1)) (x : Cube (n + 1)) :
    splitInput i x = (otherCoordinates i x, x i) := rfl

def rearrangeCoordinateObservation {n : ℕ} (i : Fin (n + 1)) :
    (Bool × Cube (n + 1)) ≃ ((Cube n × Bool) × Bool) where
  toFun bx := ((otherCoordinates i bx.2, bx.1), bx.2 i)
  invFun uba := (uba.1.2, joinCoordinate i (uba.2, uba.1.1))
  left_inv bx := by
    rcases bx with ⟨b, x⟩
    change (b, Fin.insertNth i (x i) (Fin.removeNth i x)) = (b, x)
    rw [Fin.insertNth_self_removeNth]
  right_inv uba := by
    rcases uba with ⟨⟨u, b⟩, a⟩
    simp [otherCoordinates, joinCoordinate, Fin.insertNthEquiv]

theorem jointLaw_triple_fibreMass {n : ℕ} (i : Fin (n + 1))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Cube n) (a b : Bool) :
    (jointLaw (n + 1) p hp0 hp1).fibreMass
      (fun xy => ((otherCoordinates i xy.1, xy.2 i), xy.1 i)) ((x, b), a) =
      (if a = b then 1 - p else p) / (2 : ℝ) ^ (n + 1) := by
  have he := (jointLaw (n + 1) p hp0 hp1).fibreMass_comp_equiv
    (fun xy => (xy.2 i, xy.1)) (rearrangeCoordinateObservation i) (b, joinCoordinate i (a, x))
  simp only [rearrangeCoordinateObservation, Equiv.coe_fn_mk, joinCoordinate_same,
    otherCoordinates, joinCoordinate, Fin.insertNthEquiv, Fin.removeNth_insertNth,
    Fin.insertNth_apply_same] at he
  exact he.trans (jointLaw_coordinate_input_fibreMass i p hp0 hp1 a b x)

theorem jointLaw_triple_fibreMoment {n : ℕ} (i : Fin (n + 1)) (f : Cube (n + 1) → Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Cube n) (a b : Bool) :
    (jointLaw (n + 1) p hp0 hp1).fibreMoment
      (fun xy => ((otherCoordinates i xy.1, xy.2 i), xy.1 i))
      (fun xy => FiniteLaw.bitValue (f xy.2)) ((x, b), a) =
      (if a = b then 1 - p else p) * outputPosterior (restrictCoordinate i f b) p x /
        (2 : ℝ) ^ (n + 1) := by
  have he := (jointLaw (n + 1) p hp0 hp1).fibreMoment_comp_equiv
    (fun xy => (xy.2 i, xy.1)) (rearrangeCoordinateObservation i) (b, joinCoordinate i (a, x))
    (fun xy => FiniteLaw.bitValue (f xy.2))
  simp only [rearrangeCoordinateObservation, Equiv.coe_fn_mk, joinCoordinate_same,
    otherCoordinates, joinCoordinate, Fin.insertNthEquiv, Fin.removeNth_insertNth,
    Fin.insertNth_apply_same] at he
  exact he.trans (jointLaw_coordinate_input_fibreMoment i f p hp0 hp1 a b x)

theorem jointLaw_other_output_fibreMass {n : ℕ} (i : Fin (n + 1))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Cube n) (b : Bool) :
    (jointLaw (n + 1) p hp0 hp1).fibreMass
      (fun xy => (otherCoordinates i xy.1, xy.2 i)) (x, b) = 1 / (2 : ℝ) ^ (n + 1) := by
  rw [← (jointLaw (n + 1) p hp0 hp1).sum_pair_fibreMass
    (fun xy => (otherCoordinates i xy.1, xy.2 i)) (fun xy => xy.1 i) (x, b)]
  simp_rw [jointLaw_triple_fibreMass]
  cases b <;> simp [Fintype.sum_bool] <;> ring

theorem jointLaw_other_output_fibreMoment {n : ℕ} (i : Fin (n + 1)) (f : Cube (n + 1) → Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Cube n) (b : Bool) :
    (jointLaw (n + 1) p hp0 hp1).fibreMoment
      (fun xy => (otherCoordinates i xy.1, xy.2 i))
      (fun xy => FiniteLaw.bitValue (f xy.2)) (x, b) =
      outputPosterior (restrictCoordinate i f b) p x / (2 : ℝ) ^ (n + 1) := by
  rw [← (jointLaw (n + 1) p hp0 hp1).sum_pair_fibreMoment
    (fun xy => (otherCoordinates i xy.1, xy.2 i)) (fun xy => xy.1 i)
    (fun xy => FiniteLaw.bitValue (f xy.2)) (x, b)]
  simp_rw [jointLaw_triple_fibreMoment]
  cases b <;> simp [Fintype.sum_bool] <;> ring

theorem jointLaw_other_fibreMass {n : ℕ} (i : Fin (n + 1))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Cube n) :
    (jointLaw (n + 1) p hp0 hp1).fibreMass (fun xy => otherCoordinates i xy.1) x =
      1 / (2 : ℝ) ^ n := by
  rw [← (jointLaw (n + 1) p hp0 hp1).sum_pair_fibreMass
    (fun xy => otherCoordinates i xy.1) (fun xy => xy.2 i) x]
  simp_rw [jointLaw_other_output_fibreMass]
  simp only [Fintype.sum_bool, pow_succ]
  ring

theorem jointLaw_independentUnbiased_output {n : ℕ} (i : Fin (n + 1))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (jointLaw (n + 1) p hp0 hp1).independentUnbiasedBit
      (fun xy => xy.2 i) (fun xy => otherCoordinates i xy.1) := by
  intro x
  rw [FiniteLaw.fibreMoment_bit_pair, jointLaw_other_output_fibreMass, jointLaw_other_fibreMass]
  rw [pow_succ]
  ring

/-- The output bit uses only `(U,B)` and private channel randomness. -/
theorem jointLaw_markov {n : ℕ} (i : Fin (n + 1)) (f : Cube (n + 1) → Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (jointLaw (n + 1) p hp0 hp1).conditionallyIndependentBit (fun xy => f xy.2)
      (fun xy => xy.1 i) (fun xy => (otherCoordinates i xy.1, xy.2 i)) := by
  rintro ⟨x, b⟩ a
  rw [jointLaw_triple_fibreMoment, jointLaw_triple_fibreMass,
    jointLaw_other_output_fibreMass, jointLaw_other_output_fibreMoment]
  ring

theorem jointLaw_other_input_fibreMass {n : ℕ} (i : Fin (n + 1))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Cube n) (a : Bool) :
    (jointLaw (n + 1) p hp0 hp1).fibreMass
      (fun xy => (otherCoordinates i xy.1, xy.1 i)) (x, a) = 1 / (2 : ℝ) ^ (n + 1) := by
  have he := (jointLaw (n + 1) p hp0 hp1).fibreMass_comp_equiv Prod.fst (splitInput i)
    (joinCoordinate i (a, x))
  simp only [splitInput_apply, otherCoordinates, joinCoordinate, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.removeNth_insertNth, Fin.insertNth_apply_same] at he
  exact he.trans (jointLaw_fibreMass_first p hp0 hp1 (joinCoordinate i (a, x)))

theorem jointLaw_independentUnbiased_input {n : ℕ} (i : Fin (n + 1))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (jointLaw (n + 1) p hp0 hp1).independentUnbiasedBit
      (fun xy => xy.1 i) (fun xy => otherCoordinates i xy.1) := by
  intro x
  rw [FiniteLaw.fibreMoment_bit_pair, jointLaw_other_input_fibreMass, jointLaw_other_fibreMass]
  rw [pow_succ]
  ring

theorem jointLaw_conditionOn_pair {n : ℕ} (i : Fin (n + 1))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Cube n) (a b : Bool) :
    ((jointLaw (n + 1) p hp0 hp1).conditionOn (fun xy => otherCoordinates i xy.1) x).fibreMass
      (fun xy => (xy.2 i, xy.1 i)) (b, a) = (if a = b then 1 - p else p) / 2 := by
  have hm := (jointLaw (n + 1) p hp0 hp1).mass_mul_conditionOn_fibreMass
    (fun xy => otherCoordinates i xy.1) (fun xy => (xy.2 i, xy.1 i)) x (b, a)
  have he : (jointLaw (n + 1) p hp0 hp1).fibreMass
      (fun xy => (otherCoordinates i xy.1, (xy.2 i, xy.1 i))) (x, (b, a)) =
    (jointLaw (n + 1) p hp0 hp1).fibreMass
      (fun xy => ((otherCoordinates i xy.1, xy.2 i), xy.1 i)) ((x, b), a) := by
    simp [FiniteLaw.fibreMass, Prod.mk.injEq, and_assoc]
  rw [he, jointLaw_other_fibreMass, jointLaw_triple_fibreMass, pow_succ] at hm
  apply (mul_left_cancel₀ (show 1 / (2 : ℝ) ^ n ≠ 0 by positivity))
  rw [hm]
  ring

theorem jointLaw_conditionOn_correlation {n : ℕ} (i : Fin (n + 1))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Cube n) :
    ((jointLaw (n + 1) p hp0 hp1).conditionOn (fun xy => otherCoordinates i xy.1) x).bitCorrelation
      (fun xy => xy.1 i) (fun xy => xy.2 i) = 1 - 2 * p := by
  let μ := jointLaw (n + 1) p hp0 hp1
  have ha := μ.conditionOn_mean_of_independentUnbiasedBit (fun xy => xy.1 i)
    (fun xy => otherCoordinates i xy.1) (jointLaw_independentUnbiased_input i p hp0 hp1) x
  have hb := μ.conditionOn_mean_of_independentUnbiasedBit (fun xy => xy.2 i)
    (fun xy => otherCoordinates i xy.1) (jointLaw_independentUnbiased_output i p hp0 hp1) x
  rw [FiniteLaw.bitCorrelation_symm, FiniteLaw.bitCorrelation_unbiased _ _ _ hb, ha,
    FiniteLaw.expect_bitValue_mul, FiniteLaw.fibreMoment_bit_pair]
  rw [jointLaw_conditionOn_pair]
  norm_num
  ring

theorem jointLaw_conditionOn_markov {n : ℕ} (i : Fin (n + 1)) (f : Cube (n + 1) → Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Cube n) :
    ((jointLaw (n + 1) p hp0 hp1).conditionOn (fun xy => otherCoordinates i xy.1) x).conditionallyIndependentBit
      (fun xy => f xy.2) (fun xy => xy.1 i) (fun xy => xy.2 i) := by
  apply FiniteLaw.conditionalIndependence_conditionOn _ _ _ _ _ (jointLaw_markov i f p hp0 hp1)
  rw [jointLaw_other_fibreMass]
  positivity

theorem jointLaw_split_progressiveGap {n : ℕ} (i : Fin (n + 1)) (f : Cube (n + 1) → Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (jointLaw (n + 1) p hp0 hp1).progressiveGap p (fun xy => f xy.2)
      (fun xy => (otherCoordinates i xy.1, xy.1 i)) =
      progressiveBound p (outputMean f) - mutualInformation f p := by
  have he := (jointLaw (n + 1) p hp0 hp1).shannonInformation_equiv Prod.fst (splitInput i)
    (fun xy => FiniteLaw.bitValue (f xy.2))
  simp only [splitInput_apply] at he
  unfold FiniteLaw.progressiveGap
  rw [he]
  exact jointLaw_progressiveGap f p hp0 hp1

theorem jointLaw_split_conditionalProgressiveGap {n : ℕ} (i : Fin (n + 1))
    (f : Cube (n + 1) → Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (jointLaw (n + 1) p hp0 hp1).conditionalProgressiveGap p (fun xy => f xy.2)
      (fun xy => (otherCoordinates i xy.1, xy.1 i)) (fun xy => xy.2 i) =
    (jointLaw (n + 1) p hp0 hp1).conditionalProgressiveGap p (fun xy => f xy.2)
      Prod.fst (fun xy => xy.2 i) := by
  unfold FiniteLaw.conditionalProgressiveGap
  apply congrArg (((jointLaw (n + 1) p hp0 hp1).map (fun xy => xy.2 i)).expect)
  funext b
  unfold FiniteLaw.progressiveGap
  have he := ((jointLaw (n + 1) p hp0 hp1).conditionOn (fun xy => xy.2 i) b).shannonInformation_equiv
    Prod.fst (splitInput i) (fun xy => FiniteLaw.bitValue (f xy.2))
  simp only [splitInput_apply] at he
  rw [he]

theorem jointLaw_split_conditionalGap_nonneg {n : ℕ} (i : Fin (n + 1))
    (f : Cube (n + 1) → Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hIH : ∀ g : Cube n → Bool, mutualInformation g p ≤ progressiveBound p (outputMean g)) :
    0 ≤ (jointLaw (n + 1) p hp0 hp1).conditionalProgressiveGap p (fun xy => f xy.2)
      (fun xy => (otherCoordinates i xy.1, xy.1 i)) (fun xy => xy.2 i) := by
  rw [jointLaw_split_conditionalProgressiveGap]
  exact jointLaw_conditionalGap_nonneg i f p hp0 hp1 hIH

theorem jointLaw_good_coordinate {n : ℕ} (hn : 2 ≤ n) (f : Cube n → Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ i : Fin n, (jointLaw n p hp0 hp1).quadraticInformation
      (fun xy => FiniteLaw.bitValue (f xy.2)) (fun xy => xy.2 i) ≤ 1 / 4 := by
  obtain ⟨i, hi⟩ := good_coordinate hn f
  refine ⟨i, ?_⟩
  change (jointLaw n p hp0 hp1).quadraticInformation (fun xy => bit (f xy.2)) (fun xy => xy.2 i) ≤ _
  rw [jointLaw_quadraticInformation_coordinate]
  exact hi

end CourtadeKumar.Spec
