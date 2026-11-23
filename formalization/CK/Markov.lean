import CK.EntropyChain

/-!
# Finite conditional independence and observation reindexing

The Markov hypothesis is a factorization of joint probabilities.  Its entropy
consequences are proved below, rather than included as assumptions.
-/

noncomputable section
namespace CourtadeKumar
namespace FiniteLaw
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]
variable {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]

omit [Fintype U] [Fintype Z] in
theorem pair_fibreMass_le_first (μ : FiniteLaw Ω) (u : Ω → U) (z : Ω → Z)
    (a : U) (b : Z) :
    μ.fibreMass (fun ω => (u ω, z ω)) (a, b) ≤ μ.fibreMass u a := by
  unfold fibreMass
  apply Finset.sum_le_sum
  intro ω _
  by_cases hu : u ω = a <;> by_cases hz : z ω = b <;> simp [hu, hz, μ.mass_nonneg]

omit [Fintype U] in
theorem sum_pair_fibreMass (μ : FiniteLaw Ω) (u : Ω → U) (z : Ω → Z) (a : U) :
    ∑ b, μ.fibreMass (fun ω => (u ω, z ω)) (a, b) = μ.fibreMass u a := by
  unfold fibreMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hu : u ω = a <;> simp [hu]

/-- `C` and `Z` are conditionally independent given `U`, written without divisions.
Only the `C=1` equations are needed because `C` is a bit. -/
def conditionallyIndependentBit (μ : FiniteLaw Ω) (c : Ω → Bool)
    (z : Ω → Z) (u : Ω → U) : Prop :=
  ∀ a b,
    μ.fibreMoment (fun ω => (u ω, z ω)) (fun ω => bitValue (c ω)) (a, b) * μ.fibreMass u a =
      μ.fibreMoment u (fun ω => bitValue (c ω)) a * μ.fibreMass (fun ω => (u ω, z ω)) (a, b)

omit [Fintype U] [Fintype Z] in
theorem conditionalMean_of_conditionalIndependence (μ : FiniteLaw Ω) (c : Ω → Bool)
    (z : Ω → Z) (u : Ω → U) (hmark : μ.conditionallyIndependentBit c z u)
    (a : U) (b : Z) (hab : μ.fibreMass (fun ω => (u ω, z ω)) (a, b) ≠ 0) :
    μ.conditionalMean (fun ω => (u ω, z ω)) (fun ω => bitValue (c ω)) (a, b) =
      μ.conditionalMean u (fun ω => bitValue (c ω)) a := by
  have hpos : 0 < μ.fibreMass (fun ω => (u ω, z ω)) (a, b) :=
    lt_of_le_of_ne (μ.fibreMass_nonneg _ _) (Ne.symm hab)
  have ha : μ.fibreMass u a ≠ 0 := ne_of_gt (lt_of_lt_of_le hpos (μ.pair_fibreMass_le_first u z a b))
  unfold conditionalMean
  exact (div_eq_div_iff hab ha).2 (hmark a b)

/-- Conditional independence makes every posterior-mean functional invariant. -/
theorem conditionalMean_function_of_conditionalIndependence (μ : FiniteLaw Ω) (c : Ω → Bool)
    (z : Ω → Z) (u : Ω → U) (hmark : μ.conditionallyIndependentBit c z u) (F : ℝ → ℝ) :
    (μ.map (fun ω => (u ω, z ω))).expect
      (fun ab => F (μ.conditionalMean (fun ω => (u ω, z ω)) (fun ω => bitValue (c ω)) ab)) =
      (μ.map u).expect (fun a => F (μ.conditionalMean u (fun ω => bitValue (c ω)) a)) := by
  change (∑ ab : U × Z, μ.fibreMass (fun ω => (u ω, z ω)) ab *
      F (μ.conditionalMean (fun ω => (u ω, z ω)) (fun ω => bitValue (c ω)) ab)) =
    ∑ a, μ.fibreMass u a * F (μ.conditionalMean u (fun ω => bitValue (c ω)) a)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ b : Z, μ.fibreMass (fun ω => (u ω, z ω)) (a, b) *
        F (μ.conditionalMean u (fun ω => bitValue (c ω)) a) := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : μ.fibreMass (fun ω => (u ω, z ω)) (a, b) = 0
      · simp [hab]
      · rw [μ.conditionalMean_of_conditionalIndependence c z u hmark a b hab]
    _ = _ := by rw [← Finset.sum_mul, μ.sum_pair_fibreMass u z a]

theorem conditionalShannonEntropy_of_conditionalIndependence (μ : FiniteLaw Ω) (c : Ω → Bool)
    (z : Ω → Z) (u : Ω → U) (hmark : μ.conditionallyIndependentBit c z u) :
    μ.conditionalShannonEntropy (fun ω => (u ω, z ω)) (fun ω => bitValue (c ω)) =
      μ.conditionalShannonEntropy u (fun ω => bitValue (c ω)) :=
  μ.conditionalMean_function_of_conditionalIndependence c z u hmark entropyBits

theorem conditionalQuadraticEntropy_of_conditionalIndependence (μ : FiniteLaw Ω) (c : Ω → Bool)
    (z : Ω → Z) (u : Ω → U) (hmark : μ.conditionallyIndependentBit c z u) :
    μ.conditionalQuadraticEntropy (fun ω => (u ω, z ω)) (fun ω => bitValue (c ω)) =
      μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) :=
  μ.conditionalMean_function_of_conditionalIndependence c z u hmark quadraticEntropy

variable {W : Type*} [Fintype W] [DecidableEq W]

omit [Fintype Z] [Fintype W] in
theorem fibreMass_comp_equiv (μ : FiniteLaw Ω) (z : Ω → Z) (e : Z ≃ W) (a : Z) :
    μ.fibreMass (fun ω => e (z ω)) (e a) = μ.fibreMass z a := by
  simp [fibreMass]

omit [Fintype Z] [Fintype W] in
theorem fibreMoment_comp_equiv (μ : FiniteLaw Ω) (z : Ω → Z) (e : Z ≃ W) (a : Z) (c : Ω → ℝ) :
    μ.fibreMoment (fun ω => e (z ω)) c (e a) = μ.fibreMoment z c a := by
  simp [fibreMoment]

omit [Fintype Z] [Fintype W] in
theorem conditionalMean_comp_equiv (μ : FiniteLaw Ω) (z : Ω → Z) (e : Z ≃ W) (a : Z)
    (c : Ω → ℝ) : μ.conditionalMean (fun ω => e (z ω)) c (e a) = μ.conditionalMean z c a := by
  unfold conditionalMean
  rw [μ.fibreMass_comp_equiv, μ.fibreMoment_comp_equiv]

theorem conditionalMean_function_equiv (μ : FiniteLaw Ω) (z : Ω → Z) (e : Z ≃ W)
    (c : Ω → ℝ) (F : ℝ → ℝ) :
    (μ.map (fun ω => e (z ω))).expect (fun w => F (μ.conditionalMean (fun ω => e (z ω)) c w)) =
      (μ.map z).expect (fun a => F (μ.conditionalMean z c a)) := by
  change (∑ w, μ.fibreMass (fun ω => e (z ω)) w *
      F (μ.conditionalMean (fun ω => e (z ω)) c w)) =
    ∑ a, μ.fibreMass z a * F (μ.conditionalMean z c a)
  rw [← e.sum_comp (fun w => μ.fibreMass (fun ω => e (z ω)) w *
    F (μ.conditionalMean (fun ω => e (z ω)) c w))]
  simp_rw [μ.fibreMass_comp_equiv, μ.conditionalMean_comp_equiv]

theorem conditionalShannonEntropy_equiv (μ : FiniteLaw Ω) (z : Ω → Z) (e : Z ≃ W)
    (c : Ω → ℝ) :
    μ.conditionalShannonEntropy (fun ω => e (z ω)) c = μ.conditionalShannonEntropy z c :=
  μ.conditionalMean_function_equiv z e c entropyBits

theorem conditionalQuadraticEntropy_equiv (μ : FiniteLaw Ω) (z : Ω → Z) (e : Z ≃ W)
    (c : Ω → ℝ) :
    μ.conditionalQuadraticEntropy (fun ω => e (z ω)) c = μ.conditionalQuadraticEntropy z c :=
  μ.conditionalMean_function_equiv z e c quadraticEntropy

theorem shannonInformation_equiv (μ : FiniteLaw Ω) (z : Ω → Z) (e : Z ≃ W)
    (c : Ω → ℝ) :
    μ.shannonInformation c (fun ω => e (z ω)) = μ.shannonInformation c z := by
  unfold shannonInformation
  rw [μ.conditionalShannonEntropy_equiv]

end FiniteLaw
end CourtadeKumar
