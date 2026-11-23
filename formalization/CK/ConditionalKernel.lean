import CK.FiniteKernel
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.ConditionalExpectation

/-!
# Finite conditional laws from genuine random variables

The observation takes values in an arbitrary measurable space. The conditional
finite law is constructed from mathlib's regular conditional distribution, and
its moments are identified with actual conditional expectations.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace CourtadeKumar.KernelInformation
open Set MeasureTheory Filter ProbabilityTheory
open scoped BigOperators

variable {Ω U Γ : Type*} [mΩ : MeasurableSpace Ω] [mU : MeasurableSpace U]
  [Fintype Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]

/-- A finite probability measure, with its actual singleton masses. -/
def finiteLawOfMeasure (μ : Measure Γ) [IsProbabilityMeasure μ] : FiniteLaw Γ where
  mass a := μ.real {a}
  mass_nonneg _ := measureReal_nonneg
  mass_sum := by
    have h := sum_measureReal_singleton (μ := μ) (Finset.univ : Finset Γ)
    simpa using h

theorem expect_finiteLawOfMeasure (μ : Measure Γ) [IsProbabilityMeasure μ] (f : Γ → ℝ) :
    (finiteLawOfMeasure μ).expect f=(∫ a,f a ∂μ) := by
  rw [integral_fintype _ Integrable.of_finite]
  simp only [FiniteLaw.expect,finiteLawOfMeasure,smul_eq_mul]

/-- A Markov kernel with finite output, represented by finite probability laws. -/
def finiteKernelOfKernel (κ : Kernel U Γ) [IsMarkovKernel κ] : FiniteKernel U Γ where
  law u := finiteLawOfMeasure (κ u)
  measurable_mass a := (Kernel.measurable_coe κ (measurableSet_singleton a)).ennreal_toReal

theorem expect_finiteKernelOfKernel (κ : Kernel U Γ) [IsMarkovKernel κ] (u : U) (f : Γ → ℝ) :
    ((finiteKernelOfKernel κ).law u).expect f=(∫ a,f a ∂κ u) :=
  expect_finiteLawOfMeasure (κ u) f

variable [StandardBorelSpace Γ] [Nonempty Γ]

/-- The genuine finite conditional law of `y` given `u`. -/
def conditionalKernel (ν : Measure Ω) [IsProbabilityMeasure ν] (y : Ω → Γ) (u : Ω → U) :
    FiniteKernel U Γ := finiteKernelOfKernel (condDistrib y u ν)

variable {ν : Measure Ω} [IsProbabilityMeasure ν] {y : Ω → Γ} {u : Ω → U}

theorem integrable_finite_observable (hy : Measurable y) (f : Γ → ℝ) :
    Integrable (fun ω => f (y ω)) ν := by
  have hi : Integrable f (ν.map y) := Integrable.of_finite
  exact (integrable_map_measure (measurable_of_countable f).aestronglyMeasurable
    hy.aemeasurable).mp hi

/-- Every moment of the conditional finite law is the corresponding actual
conditional expectation. -/
theorem conditionalKernel_expect_ae (hy : Measurable y) (hu : Measurable u) (f : Γ → ℝ) :
    (fun ω => ((conditionalKernel ν y u).law (u ω)).expect f) =ᵐ[ν]
      ν[fun ω => f (y ω)|mU.comap u] := by
  have h := condExp_ae_eq_integral_condDistrib (μ := ν) hu hy.aemeasurable
    (measurable_of_countable f).stronglyMeasurable (integrable_finite_observable (ν := ν) hy f)
  filter_upwards [h] with ω hω
  exact (expect_finiteKernelOfKernel (condDistrib y u ν) (u ω) f).trans hω.symm

/-- Averaging the genuine conditional laws recovers the original finite joint law. -/
theorem conditionalKernel_mixture_expect (hy : Measurable y) (hu : Measurable u) (f : Γ → ℝ) :
    letI : IsProbabilityMeasure (ν.map u) := isProbabilityMeasure_map hu.aemeasurable
    ((conditionalKernel ν y u).mixture (ν.map u)).expect f=(∫ ω,f (y ω) ∂ν) := by
  letI : IsProbabilityMeasure (ν.map u) := isProbabilityMeasure_map hu.aemeasurable
  rw [FiniteKernel.expect_mixture]
  rw [integral_map hu.aemeasurable
    ((conditionalKernel ν y u).measurable_expect f).aestronglyMeasurable]
  calc
    (∫ ω,((conditionalKernel ν y u).law (u ω)).expect f ∂ν)=
        ∫ ω,(ν[fun ω => f (y ω)|mU.comap u]) ω ∂ν :=
      integral_congr_ae (conditionalKernel_expect_ae hy hu f)
    _=(∫ ω,f (y ω) ∂ν) := integral_condExp hu.comap_le

/-- Independence of a finite observable and the observation makes its genuine
conditional-law mean constant almost everywhere. -/
theorem conditionalKernel_expect_of_independent
    {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype B]
    (hy : Measurable y) (hu : Measurable u) (b : Γ → B)
    (hind : IndepFun (fun ω => b (y ω)) u ν) (f : B → ℝ) :
    (fun z => ((conditionalKernel ν y u).law z).expect (fun a => f (b a))) =ᵐ[ν.map u]
      fun _ => ∫ ω,f (b (y ω)) ∂ν := by
  have hb : Measurable (fun ω => b (y ω)) := (measurable_of_countable b).comp hy
  have hf : StronglyMeasurable[MeasurableSpace.comap (fun ω => b (y ω)) inferInstance]
      (fun ω => f (b (y ω))) :=
    (measurable_of_countable f).stronglyMeasurable.comp_measurable (Measurable.of_comap_le le_rfl)
  have he := condExp_indep_eq hb.comap_le hu.comap_le hf
    ((IndepFun_iff_Indep _ _ _).mp hind)
  have hk := conditionalKernel_expect_ae (ν := ν) hy hu (fun a => f (b a))
  have hs : MeasurableSet {z | ((conditionalKernel ν y u).law z).expect (fun a => f (b a))=
      ∫ ω,f (b (y ω)) ∂ν} :=
    measurableSet_eq_fun ((conditionalKernel ν y u).measurable_expect _) measurable_const
  exact (ae_map_iff hu.aemeasurable hs).2 (hk.trans he)

/-- The unbiased bit hypothesis in the paper yields unbiased conditional laws
for almost every arbitrary observation value. -/
theorem conditionalKernel_bit_unbiased
    (hy : Measurable y) (hu : Measurable u) (b : Γ → Bool)
    (hind : IndepFun (fun ω => b (y ω)) u ν)
    (hmean : (∫ ω,FiniteLaw.bitValue (b (y ω)) ∂ν)=1/2) :
    ∀ᵐ z ∂ν.map u, ((conditionalKernel ν y u).law z).expect (fun a => FiniteLaw.bitValue (b a))=1/2 := by
  have h := conditionalKernel_expect_of_independent hy hu b hind FiniteLaw.bitValue
  simpa only [hmean] using h

end CourtadeKumar.KernelInformation
