import CK.KernelInformationChain
import CK.ConditionalKernel
import CK.PosteriorChain

/-! # Conditioning inequalities for genuine arbitrary observations

All conditional laws below are mathlib regular conditional distributions of the
actual finite bits. The observation and underlying sample space are arbitrary
measurable spaces. Independence is `ProbabilityTheory.IndepFun` on the original
probability space, not a supplied information inequality.
-/

noncomputable section
namespace CourtadeKumar.KernelInformation
open Set MeasureTheory Filter ProbabilityTheory
open scoped BigOperators

variable {Ω U Γ : Type*} [mΩ : MeasurableSpace Ω] [mU : MeasurableSpace U]
  [Fintype Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [StandardBorelSpace Γ] [Nonempty Γ]
variable {ν : Measure Ω} [IsProbabilityMeasure ν] {y : Ω → Γ} {u : Ω → U}

private theorem finiteLaw_eq_of_mass {μ η : FiniteLaw Γ} (h : μ.mass = η.mass) : μ = η := by
  cases μ
  cases η
  cases h
  rfl

/-- The actual joint finite law is recovered by averaging the conditional kernel. -/
theorem conditionalKernel_mixture (hy : Measurable y) (hu : Measurable u) :
    letI : IsProbabilityMeasure (ν.map u) := isProbabilityMeasure_map hu.aemeasurable
    letI : IsProbabilityMeasure (ν.map y) := isProbabilityMeasure_map hy.aemeasurable
    (conditionalKernel ν y u).mixture (ν.map u) = finiteLawOfMeasure (ν.map y) := by
  classical
  letI : IsProbabilityMeasure (ν.map u) := isProbabilityMeasure_map hu.aemeasurable
  letI : IsProbabilityMeasure (ν.map y) := isProbabilityMeasure_map hy.aemeasurable
  have hmass : ((conditionalKernel ν y u).mixture (ν.map u)).mass =
      (finiteLawOfMeasure (ν.map y)).mass := by
    funext a
    have h := conditionalKernel_mixture_expect (ν := ν) hy hu (fun s => if s = a then (1 : ℝ) else 0)
    have h' := expect_finiteLawOfMeasure (ν.map y) (fun s => if s = a then (1 : ℝ) else 0)
    rw [integral_map hy.aemeasurable (measurable_of_countable _).aestronglyMeasurable] at h'
    have he := h.trans h'.symm
    simpa [FiniteLaw.expect, mul_ite] using he
  exact finiteLaw_eq_of_mass hmass

/-- The conditional entropy integral equals entropy of the genuine conditional expectation. -/
theorem conditionalKernel_quadraticEntropy (hy : Measurable y) (hu : Measurable u) (c : Γ → Bool) :
    (∫ z, quadraticEntropy (((conditionalKernel ν y u).law z).expect
      (fun a => FiniteLaw.bitValue (c a))) ∂ν.map u) =
    Posterior.quadraticEntropyGiven ν (mU.comap u) (fun ω => FiniteLaw.bitValue (c (y ω))) := by
  rw [integral_map hu.aemeasurable
    ((conditionalKernel ν y u).measurable_bitEntropy c).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [conditionalKernel_expect_ae (ν := ν) hy hu (fun a => FiniteLaw.bitValue (c a))]
    with ω hω
  exact congrArg quadraticEntropy hω

/-- Tsallis conditioning for actual random bits and an arbitrary observation.
The possibly biased bit is independent of the observation under the original measure. -/
theorem quadratic_conditioning_of_independent (hy : Measurable y) (hu : Measurable u)
    (b c : Γ → Bool) (hind : IndepFun (fun ω => b (y ω)) u ν) :
    letI : IsProbabilityMeasure (ν.map y) := isProbabilityMeasure_map hy.aemeasurable
    (∫ z, ((conditionalKernel ν y u).law z).quadraticInformation
      (fun a => FiniteLaw.bitValue (b a)) c ∂ν.map u) *
      Posterior.quadraticEntropyGiven ν (mU.comap u) (fun ω => FiniteLaw.bitValue (c (y ω))) ≥
    quadraticEntropy (∫ ω, FiniteLaw.bitValue (b (y ω)) ∂ν) *
      (finiteLawOfMeasure (ν.map y)).quadraticInformation (fun a => FiniteLaw.bitValue (c a)) b := by
  letI : IsProbabilityMeasure (ν.map u) := isProbabilityMeasure_map hu.aemeasurable
  letI : IsProbabilityMeasure (ν.map y) := isProbabilityMeasure_map hy.aemeasurable
  have hb := conditionalKernel_expect_of_independent (ν := ν) hy hu b hind FiniteLaw.bitValue
  have h := (conditionalKernel ν y u).quadratic_conditioning (ν.map u) b c _ hb
  rw [conditionalKernel_mixture_expect hy hu, conditionalKernel_mixture hy hu,
    conditionalKernel_quadraticEntropy hy hu] at h
  exact h

/-- Manuscript conditioning-gain lemma for actual random bits and arbitrary measurable observations. -/
theorem conditioning_gain_of_independent (hy : Measurable y) (hu : Measurable u)
    (b c : Γ → Bool) (hind : IndepFun (fun ω => b (y ω)) u ν)
    (hb : (∫ ω, FiniteLaw.bitValue (b (y ω)) ∂ν) = 1 / 2)
    (hv : 0 < Posterior.quadraticEntropyGiven ν (mU.comap u) (fun ω => FiniteLaw.bitValue (c (y ω)))) :
    letI : IsProbabilityMeasure (ν.map y) := isProbabilityMeasure_map hy.aemeasurable
    (∫ z, ((conditionalKernel ν y u).law z).shannonInformation
      (fun a => FiniteLaw.bitValue (b a)) c ∂ν.map u) -
        (finiteLawOfMeasure (ν.map y)).shannonInformation (fun a => FiniteLaw.bitValue (b a)) c ≥
      (finiteLawOfMeasure (ν.map y)).quadraticInformation (fun a => FiniteLaw.bitValue (c a)) b *
        Posterior.conditionalQuadraticInformation ν (mU.comap u) (fun ω => FiniteLaw.bitValue (c (y ω))) /
        (2 * Real.log 2 * quadraticEntropy (∫ ω, FiniteLaw.bitValue (c (y ω)) ∂ν) *
          Posterior.quadraticEntropyGiven ν (mU.comap u) (fun ω => FiniteLaw.bitValue (c (y ω)))) := by
  letI : IsProbabilityMeasure (ν.map u) := isProbabilityMeasure_map hu.aemeasurable
  letI : IsProbabilityMeasure (ν.map y) := isProbabilityMeasure_map hy.aemeasurable
  have hpos : 0 < ∫ z, quadraticEntropy (((conditionalKernel ν y u).law z).expect
      (fun a => FiniteLaw.bitValue (c a))) ∂ν.map u := by
    rw [conditionalKernel_quadraticEntropy hy hu]
    exact hv
  have h := (conditionalKernel ν y u).conditioning_gain (ν.map u) b c
    (conditionalKernel_bit_unbiased hy hu b hind hb) hpos
  rw [conditionalKernel_quadraticEntropy hy hu, conditionalKernel_mixture_expect hy hu,
    conditionalKernel_mixture hy hu] at h
  exact h

end CourtadeKumar.KernelInformation
