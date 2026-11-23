import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

/-!
# Finite probability and quadratic information

The manuscript uses the normalization `T(C) = 4 μ (1 - μ)` for a bit
with mean `μ`.  This file implements finite probability laws directly, including
zero-mass fibres.  Conditional means on zero-mass fibres are defined to be zero
(Lean's total division); none of the expectation identities require those fibres
to have positive mass.

`c : Ω → ℝ` may be an indicator, or a conditional success probability for a
randomized bit.  The results below explicitly require `0 ≤ c ≤ 1` where needed.
-/

noncomputable section

namespace CourtadeKumar

open scoped BigOperators

/-- The quadratic (Tsallis-2) entropy of a bit, in the paper's normalization. -/
def quadraticEntropy (p : ℝ) : ℝ := 4 * p * (1 - p)

theorem quadraticEntropy_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ quadraticEntropy p := by
  unfold quadraticEntropy
  exact mul_nonneg (mul_nonneg (by norm_num) hp0) (sub_nonneg.mpr hp1)

theorem quadraticEntropy_le_one (p : ℝ) : quadraticEntropy p ≤ 1 := by
  unfold quadraticEntropy
  nlinarith [sq_nonneg (2 * p - 1)]

theorem quadraticEntropy_complement (p : ℝ) :
    quadraticEntropy (1 - p) = quadraticEntropy p := by
  unfold quadraticEntropy
  ring

theorem quadraticEntropy_eq_one_sub_sq (p : ℝ) :
    quadraticEntropy p = 1 - (2 * p - 1) ^ 2 := by
  unfold quadraticEntropy
  ring

/-- A finite probability law with real-valued masses. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  mass_sum : ∑ ω, mass ω = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- Expectation under a finite law. -/
def expect (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, μ.mass ω * f ω

@[simp] theorem expect_const (μ : FiniteLaw Ω) (r : ℝ) :
    μ.expect (fun _ => r) = r := by
  simp [expect, ← Finset.sum_mul, μ.mass_sum]

theorem expect_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω + g ω) = μ.expect f + μ.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω - g ω) = μ.expect f - μ.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_const_mul (μ : FiniteLaw Ω) (r : ℝ) (f : Ω → ℝ) :
    μ.expect (fun ω => r * f ω) = r * μ.expect f := by
  simp [expect, Finset.mul_sum, mul_left_comm]

theorem expect_mul_const (μ : FiniteLaw Ω) (f : Ω → ℝ) (r : ℝ) :
    μ.expect (fun ω => f ω * r) = μ.expect f * r := by
  simp [expect, Finset.sum_mul, mul_assoc]

theorem expect_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ μ.expect f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (μ.mass_nonneg ω) (hf ω)

theorem expect_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expect f ≤ μ.expect g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.mass_nonneg ω)

theorem expect_le_one (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ ω, f ω ≤ 1) :
    μ.expect f ≤ 1 := by
  calc
    μ.expect f ≤ μ.expect (fun _ => 1) := μ.expect_mono hf
    _ = 1 := μ.expect_const 1

/-- The finite variance identity, including atoms of zero mass. -/
theorem variance_identity (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.expect (fun ω => (f ω - μ.expect f) ^ 2) =
      μ.expect (fun ω => f ω ^ 2) - (μ.expect f) ^ 2 := by
  have h : (fun ω => (f ω - μ.expect f) ^ 2) =
      (fun ω => f ω ^ 2 - 2 * μ.expect f * f ω + (μ.expect f) ^ 2) := by
    funext ω
    ring
  rw [h, μ.expect_add, μ.expect_sub, μ.expect_const_mul, μ.expect_const]
  ring

/-- The entropy Jensen gap is four times variance, with the exact manuscript normalization. -/
theorem quadratic_gap (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    quadraticEntropy (μ.expect f) - μ.expect (fun ω => quadraticEntropy (f ω)) =
      4 * μ.expect (fun ω => (f ω - μ.expect f) ^ 2) := by
  have h : (fun ω => quadraticEntropy (f ω)) =
      (fun ω => 4 * f ω - 4 * f ω ^ 2) := by
    funext ω
    unfold quadraticEntropy
    ring
  rw [h, μ.expect_sub, μ.expect_const_mul, μ.expect_const_mul, μ.variance_identity]
  unfold quadraticEntropy
  ring

theorem quadratic_jensen (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.expect (fun ω => quadraticEntropy (f ω)) ≤ quadraticEntropy (μ.expect f) := by
  have h := μ.quadratic_gap f
  have hv : 0 ≤ μ.expect (fun ω => (f ω - μ.expect f) ^ 2) :=
    μ.expect_nonneg fun ω => sq_nonneg _
  linarith

/-- Weighted Cauchy--Schwarz in the zero-safe form used in the conditioning lemma.

The hypothesis on zero denominators is essential: it records the fact that a
constant conditional bit has zero conditional covariance.
-/
theorem cauchy_div (μ : FiniteLaw Ω) (r v : Ω → ℝ)
    (hv : ∀ ω, 0 ≤ v ω) (hz : ∀ ω, v ω = 0 → r ω = 0) :
    (μ.expect r) ^ 2 ≤ μ.expect (fun ω => r ω ^ 2 / v ω) * μ.expect v := by
  unfold expect
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro ω _
    exact mul_nonneg (μ.mass_nonneg ω) (div_nonneg (sq_nonneg _) (hv ω))
  · intro ω _
    exact mul_nonneg (μ.mass_nonneg ω) (hv ω)
  · intro ω _
    by_cases h : v ω = 0
    · simp [h, hz ω h]
    · field_simp [h]
      ring

/-- A finite mixture of probability laws on a common sample space. -/
def mixture {U : Type*} [Fintype U] (ν : FiniteLaw U) (μ : U → FiniteLaw Ω) :
    FiniteLaw Ω where
  mass ω := ν.expect (fun u => (μ u).mass ω)
  mass_nonneg ω := ν.expect_nonneg fun u => (μ u).mass_nonneg ω
  mass_sum := by
    unfold expect
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, mass_sum, mul_one]
    exact ν.mass_sum

theorem expect_mixture {U : Type*} [Fintype U] (ν : FiniteLaw U)
    (μ : U → FiniteLaw Ω) (f : Ω → ℝ) :
    (ν.mixture μ).expect f = ν.expect (fun u => (μ u).expect f) := by
  change (∑ ω, (∑ u, ν.mass u * (μ u).mass ω) * f ω) =
    ∑ u, ν.mass u * ∑ ω, (μ u).mass ω * f ω
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- Mass of an observed fibre. -/
def fibreMass (μ : FiniteLaw Ω) (z : Ω → Z) (a : Z) : ℝ :=
  ∑ ω, if z ω = a then μ.mass ω else 0

omit [Fintype Z] in
theorem fibreMass_nonneg (μ : FiniteLaw Ω) (z : Ω → Z) (a : Z) :
    0 ≤ μ.fibreMass z a := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact μ.mass_nonneg ω
  · exact le_rfl

theorem fibreMass_sum (μ : FiniteLaw Ω) (z : Ω → Z) :
    ∑ a, μ.fibreMass z a = 1 := by
  unfold fibreMass
  rw [Finset.sum_comm]
  simpa using μ.mass_sum

/-- The law of a finite observation. -/
def map (μ : FiniteLaw Ω) (z : Ω → Z) : FiniteLaw Z where
  mass := μ.fibreMass z
  mass_nonneg := μ.fibreMass_nonneg z
  mass_sum := μ.fibreMass_sum z

/-- Unnormalized conditional mean of a possibly randomized bit. -/
def fibreMoment (μ : FiniteLaw Ω) (z : Ω → Z) (c : Ω → ℝ) (a : Z) : ℝ :=
  ∑ ω, if z ω = a then μ.mass ω * c ω else 0

omit [Fintype Z] in
theorem fibreMoment_nonneg (μ : FiniteLaw Ω) (z : Ω → Z) {c : Ω → ℝ}
    (hc0 : ∀ ω, 0 ≤ c ω) (a : Z) : 0 ≤ μ.fibreMoment z c a := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact mul_nonneg (μ.mass_nonneg ω) (hc0 ω)
  · exact le_rfl

omit [Fintype Z] in
theorem fibreMoment_le_mass (μ : FiniteLaw Ω) (z : Ω → Z) {c : Ω → ℝ}
    (hc1 : ∀ ω, c ω ≤ 1) (a : Z) : μ.fibreMoment z c a ≤ μ.fibreMass z a := by
  apply Finset.sum_le_sum
  intro ω _
  split_ifs
  · simpa using mul_le_mul_of_nonneg_left (hc1 ω) (μ.mass_nonneg ω)
  · exact le_rfl

omit [Fintype Z] in
theorem fibreMoment_eq_zero_of_mass_eq_zero (μ : FiniteLaw Ω) (z : Ω → Z)
    {c : Ω → ℝ} (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1)
    (a : Z) (ha : μ.fibreMass z a = 0) : μ.fibreMoment z c a = 0 := by
  have h0 := μ.fibreMoment_nonneg z hc0 a
  have h1 := μ.fibreMoment_le_mass z hc1 a
  linarith

theorem fibreMoment_sum (μ : FiniteLaw Ω) (z : Ω → Z) (c : Ω → ℝ) :
    ∑ a, μ.fibreMoment z c a = μ.expect c := by
  unfold fibreMoment expect
  rw [Finset.sum_comm]
  simp

/-- On a zero-mass fibre this is zero.  All weighted identities remain exact. -/
def conditionalMean (μ : FiniteLaw Ω) (z : Ω → Z) (c : Ω → ℝ) (a : Z) : ℝ :=
  μ.fibreMoment z c a / μ.fibreMass z a

omit [Fintype Z] in
theorem conditionalMean_nonneg (μ : FiniteLaw Ω) (z : Ω → Z) {c : Ω → ℝ}
    (hc0 : ∀ ω, 0 ≤ c ω) (a : Z) : 0 ≤ μ.conditionalMean z c a :=
  div_nonneg (μ.fibreMoment_nonneg z hc0 a) (μ.fibreMass_nonneg z a)

omit [Fintype Z] in
theorem conditionalMean_le_one (μ : FiniteLaw Ω) (z : Ω → Z) {c : Ω → ℝ}
    (hc1 : ∀ ω, c ω ≤ 1) (a : Z) : μ.conditionalMean z c a ≤ 1 := by
  unfold conditionalMean
  by_cases ha : μ.fibreMass z a = 0
  · simp [ha]
  · exact (div_le_one (lt_of_le_of_ne (μ.fibreMass_nonneg z a) (Ne.symm ha))).2
      (μ.fibreMoment_le_mass z hc1 a)

omit [Fintype Z] in
theorem mass_mul_conditionalMean (μ : FiniteLaw Ω) (z : Ω → Z) {c : Ω → ℝ}
    (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) (a : Z) :
    μ.fibreMass z a * μ.conditionalMean z c a = μ.fibreMoment z c a := by
  unfold conditionalMean
  by_cases ha : μ.fibreMass z a = 0
  · rw [ha, zero_mul, μ.fibreMoment_eq_zero_of_mass_eq_zero z hc0 hc1 a ha]
  · field_simp [ha]

/-- Law of total expectation; no positivity assumption on individual fibres. -/
theorem total_expectation (μ : FiniteLaw Ω) (z : Ω → Z) {c : Ω → ℝ}
    (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    (μ.map z).expect (μ.conditionalMean z c) = μ.expect c := by
  unfold expect map
  simp_rw [μ.mass_mul_conditionalMean z hc0 hc1]
  exact μ.fibreMoment_sum z c

/-- Conditional quadratic entropy as an expectation over the observed law. -/
def conditionalQuadraticEntropy (μ : FiniteLaw Ω) (z : Ω → Z) (c : Ω → ℝ) : ℝ :=
  (μ.map z).expect (fun a => quadraticEntropy (μ.conditionalMean z c a))

/-- Quadratic information about the bit `c` revealed by `z`. -/
def quadraticInformation (μ : FiniteLaw Ω) (c : Ω → ℝ) (z : Ω → Z) : ℝ :=
  quadraticEntropy (μ.expect c) - μ.conditionalQuadraticEntropy z c

theorem quadraticInformation_eq_variance (μ : FiniteLaw Ω) (z : Ω → Z)
    {c : Ω → ℝ} (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    μ.quadraticInformation c z =
      4 * (μ.map z).expect (fun a => (μ.conditionalMean z c a - μ.expect c) ^ 2) := by
  have h := (μ.map z).quadratic_gap (μ.conditionalMean z c)
  rw [μ.total_expectation z hc0 hc1] at h
  exact h

theorem quadraticInformation_nonneg (μ : FiniteLaw Ω) (z : Ω → Z)
    {c : Ω → ℝ} (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    0 ≤ μ.quadraticInformation c z := by
  rw [μ.quadraticInformation_eq_variance z hc0 hc1]
  exact mul_nonneg (by norm_num) ((μ.map z).expect_nonneg fun _ => sq_nonneg _)

theorem conditionalQuadraticEntropy_nonneg (μ : FiniteLaw Ω) (z : Ω → Z)
    {c : Ω → ℝ} (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    0 ≤ μ.conditionalQuadraticEntropy z c := by
  exact (μ.map z).expect_nonneg fun a => quadraticEntropy_nonneg
    (μ.conditionalMean_nonneg z hc0 a) (μ.conditionalMean_le_one z hc1 a)

theorem quadraticInformation_le_entropy (μ : FiniteLaw Ω) (z : Ω → Z)
    {c : Ω → ℝ} (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    μ.quadraticInformation c z ≤ quadraticEntropy (μ.expect c) := by
  have h := μ.conditionalQuadraticEntropy_nonneg z hc0 hc1
  unfold quadraticInformation
  linarith

/-- Zero quadratic information is exactly the factorization of each observed
fibre's bit-success probability.  This is independence for a Boolean output. -/
theorem quadraticInformation_eq_zero_iff (μ : FiniteLaw Ω) (z : Ω → Z)
    {c : Ω → ℝ} (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    μ.quadraticInformation c z = 0 ↔
      ∀ a, μ.fibreMoment z c a = μ.fibreMass z a * μ.expect c := by
  rw [μ.quadraticInformation_eq_variance z hc0 hc1]
  constructor
  · intro h a
    have hz : (μ.map z).expect
        (fun a => (μ.conditionalMean z c a - μ.expect c) ^ 2) = 0 := by linarith
    have hall : ∀ a, μ.fibreMass z a *
        (μ.conditionalMean z c a - μ.expect c) ^ 2 = 0 := by
      intro a
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => mul_nonneg (μ.fibreMass_nonneg z a) (sq_nonneg _))).1 hz a
        (Finset.mem_univ a)
    by_cases ha : μ.fibreMass z a = 0
    · rw [μ.fibreMoment_eq_zero_of_mass_eq_zero z hc0 hc1 a ha, ha, zero_mul]
    · have hs : (μ.conditionalMean z c a - μ.expect c) ^ 2 = 0 :=
        (mul_eq_zero.mp (hall a)).resolve_left ha
      have he : μ.conditionalMean z c a = μ.expect c :=
        sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
      rw [← μ.mass_mul_conditionalMean z hc0 hc1 a, he]
  · intro h
    have hz : (μ.map z).expect
        (fun a => (μ.conditionalMean z c a - μ.expect c) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      change μ.fibreMass z a * (μ.conditionalMean z c a - μ.expect c) ^ 2 = 0
      by_cases ha : μ.fibreMass z a = 0
      · simp [ha]
      · have he : μ.conditionalMean z c a = μ.expect c := by
          unfold conditionalMean
          rw [h a]
          exact mul_div_cancel_left₀ _ ha
        simp [he]
    rw [hz, mul_zero]

end FiniteLaw
end CourtadeKumar
