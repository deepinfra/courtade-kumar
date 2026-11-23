import CKLatest

/-!
Additional exact statement challenges for the paper-wide gate. The separate
original main-theorem completion challenge is unchanged. The accompanying
frozen obligation ledger additionally requires every listed proof root to
occur in the successful transitive axiom audit of all project theorems.
-/

open CourtadeKumar

example : Spec.LatestPaperTarget := latestPaper
example : Spec.ClassicalTarget := classicalCourtadeKumar
example : Spec.ThreeBitTarget := Spec.threeBit
example : Spec.PointwiseComparisonTarget := Spec.pointwiseComparison

example (μ p : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    progressiveEntropy p μ ≤ Threshold.kernelInformation μ (1 - 2 * p) :=
  Threshold.progressiveEntropy_le_kernelInformation hμ0 hμ1 hp0 hp1

example (μ p : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    progressiveEntropy p μ = Threshold.kernelInformation μ (1 - 2 * p) ↔
      μ = 0 ∨ μ = 1 / 2 ∨ μ = 1 :=
  Threshold.progressiveEntropy_eq_kernelInformation_iff hμ0 hμ1 hp0 hp1

example (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    quadraticEntropy μ = entropyBits μ ↔ μ = 0 ∨ μ = 1 / 2 ∨ μ = 1 :=
  quadraticEntropy_eq_entropyBits_iff hμ0 hμ1

#print axioms CourtadeKumar.latestPaper
#print axioms CourtadeKumar.Spec.threeBit
#print axioms CourtadeKumar.Threshold.progressiveEntropy_eq_kernelInformation_iff
#print axioms CourtadeKumar.Posterior.information_data_processing

section GeneralObservations
open Set MeasureTheory Filter CourtadeKumar.Posterior
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ν : Measure Ω} [IsProbabilityMeasure ν]

example {m₁ m₂ : MeasurableSpace Ω} (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν, f ω ∈ Icc (0 : ℝ) 1) :
    conditionalQuadraticInformation (m₀ := m₀) ν m₂ f -
        conditionalQuadraticInformation (m₀ := m₀) ν m₁ f ≤
      2 * Real.log 2 * (conditionalShannonInformation (m₀ := m₀) ν m₂ f -
        conditionalShannonInformation (m₀ := m₀) ν m₁ f) :=
  by
    letI : MeasurableSpace Ω := m₀
    exact conditional_pinsker (m₀ := m₀) (ν := ν) hm₁₂ hm₂ hf hfr

example (m n k : MeasurableSpace Ω) (f : Ω → ℝ) :
    quadraticInformationGiven (m₀ := m₀) ν m (n ⊔ k) f =
      quadraticInformationGiven (m₀ := m₀) ν m n f +
        quadraticInformationGiven (m₀ := m₀) ν (m ⊔ n) k f :=
  conditional_quadratic_chain (m₀ := m₀) (ν := ν) m n k f

example {m n : MeasurableSpace Ω} (hm : m ≤ m₀) (hn : n ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν, f ω ∈ Icc (0 : ℝ) 1)
    (hmark : MarkovFactorization (m₀ := m₀) ν m n f) :
    conditionalShannonInformation (m₀ := m₀) ν n f ≤
      conditionalShannonInformation (m₀ := m₀) ν m f ∧
    conditionalQuadraticInformation (m₀ := m₀) ν n f ≤
      conditionalQuadraticInformation (m₀ := m₀) ν m f :=
  by
    letI : MeasurableSpace Ω := m₀
    exact information_data_processing (m₀ := m₀) (ν := ν) hm hn hf hfr hmark
end GeneralObservations

section ActualComparison
open Set MeasureTheory Filter ProbabilityTheory CourtadeKumar.KernelInformation
variable {Ω U Γ : Type*} [mΩ : MeasurableSpace Ω] [mU : MeasurableSpace U]
  [Fintype Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [StandardBorelSpace Γ] [Nonempty Γ]
  {ν : Measure Ω} [IsProbabilityMeasure ν] {y : Ω → Γ} {u : Ω → U}

example [DecidableEq Γ] (hy : Measurable y) (hu : Measurable u) (a b c : Γ → Bool)
    (hind : IndepFun (fun ω => (a (y ω), b (y ω))) u ν)
    (ha : (∫ ω, FiniteLaw.bitValue (a (y ω)) ∂ν) = 1 / 2)
    (hb : (∫ ω, FiniteLaw.bitValue (b (y ω)) ∂ν) = 1 / 2)
    (hprivate : conditionalBitMarkov ν y u a b c)
    (hV : 0 < ∫ ω, quadraticEntropy
      ((ν[fun ω => FiniteLaw.bitValue (c (y ω)) | mU.comap u]) ω) ∂ν) :
    letI : IsProbabilityMeasure (ν.map u) := isProbabilityMeasure_map hu.aemeasurable
    let K := conditionalKernel ν y u
    let V := ∫ ω, quadraticEntropy
      ((ν[fun ω => FiniteLaw.bitValue (c (y ω)) | mU.comap u]) ω) ∂ν
    ∃ (K' : FiniteKernel U (Γ × Bool)) (c' : Γ × Bool → Bool),
      (∀ z, (K'.law z).map Prod.fst = K.law z) ∧
      (∀ z, (K'.law z).conditionallyIndependentBit c' Prod.fst (fun p => b p.1)) ∧
      (K'.mixture (ν.map u)).map Prod.fst = K.mixture (ν.map u) ∧
      (K'.mixture (ν.map u)).conditionallyIndependentBit c' Prod.fst (fun p => b p.1) ∧
      (K'.mixture (ν.map u)).expect (fun p => FiniteLaw.bitValue (c' p)) = 1 / 2 ∧
      (K'.mixture (ν.map u)).shannonInformation (fun p => FiniteLaw.bitValue (b p.1)) c' =
        (∫ z, (K.law z).shannonInformation (fun s => FiniteLaw.bitValue (b s)) c ∂ν.map u) / V ∧
      (∫ z, (K.law z).shannonInformation (fun s => FiniteLaw.bitValue (a s)) c ∂ν.map u) / V ≤
        (K'.mixture (ν.map u)).shannonInformation (fun p => FiniteLaw.bitValue (a p.1)) c' ∧
      (K.mixture (ν.map u)).quadraticInformation (fun s => FiniteLaw.bitValue (c s)) b / V^2 ≤
        (K'.mixture (ν.map u)).quadraticInformation
          (fun p => FiniteLaw.bitValue (c' p)) (fun p => b p.1) :=
  observation_comparison_realized hy hu a b c hind ha hb hprivate hV
end ActualComparison
