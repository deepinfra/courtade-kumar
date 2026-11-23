import CK.ThresholdSeparation
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual uniform-resampling threshold channel

The input law is Lebesgue probability measure on `[0,1]`.  The conditional
output law keeps the input with probability `ρ` and resamples independently
from the same uniform law with probability `1−ρ`.  Threshold information is
defined by its actual posterior entropy integral and then evaluated exactly.
-/

noncomputable section
namespace CourtadeKumar.Threshold
open Set MeasureTheory ProbabilityTheory

def uniformUnit : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance uniformUnit_isProbabilityMeasure : IsProbabilityMeasure uniformUnit := by
  constructor
  simp [uniformUnit, Real.volume_Icc]

theorem uniformUnit_Iic {μ : ℝ} (_hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    uniformUnit (Iic μ) = ENNReal.ofReal μ := by
  unfold uniformUnit
  rw [Measure.restrict_apply measurableSet_Iic]
  have he : Iic μ ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) μ := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hxm, hx0, _⟩; exact ⟨hx0, hxm⟩
    · rintro ⟨hx0, hxm⟩; exact ⟨hxm, hx0, hxm.trans hμ1⟩
  rw [he, Real.volume_Icc, sub_zero]

theorem uniformUnit_Ioi {μ : ℝ} (hμ0 : 0 ≤ μ) (_hμ1 : μ ≤ 1) :
    uniformUnit (Ioi μ) = ENNReal.ofReal (1 - μ) := by
  unfold uniformUnit
  rw [Measure.restrict_apply measurableSet_Ioi]
  have he : Ioi μ ∩ Icc (0 : ℝ) 1 = Ioc μ 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨hxm, _, hx1⟩; exact ⟨hxm, hx1⟩
    · rintro ⟨hxm, hx1⟩; exact ⟨hxm, hμ0.trans hxm.le, hx1⟩
  rw [he, Real.volume_Ioc]

/-- Keep the input, or draw an independent new uniform value. -/
def resamplingKernel (ρ : ℝ) : Kernel ℝ ℝ where
  toFun x := ENNReal.ofReal ρ • Measure.dirac x + ENNReal.ofReal (1 - ρ) • uniformUnit
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs]
    exact (measurable_const.mul (measurable_one.indicator hs)).add measurable_const

theorem resamplingKernel_isMarkov {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    IsMarkovKernel (resamplingKernel ρ) := by
  constructor
  intro x
  constructor
  change (ENNReal.ofReal ρ • Measure.dirac x + ENNReal.ofReal (1 - ρ) • uniformUnit) univ = 1
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ x),
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hρ0 (sub_nonneg.mpr hρ1)]
  norm_num

/-- Conditional probability of the actual threshold event `Y≤μ`. -/
def posterior (μ ρ x : ℝ) : ℝ := (resamplingKernel ρ x).real (Iic μ)

theorem posterior_eq {μ ρ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (x : ℝ) :
    posterior μ ρ x = if x ≤ μ then ρ + (1 - ρ) * μ else (1 - ρ) * μ := by
  unfold posterior Measure.real resamplingKernel
  simp only [Kernel.coe_mk, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Iic, uniformUnit_Iic hμ0 hμ1, smul_eq_mul]
  by_cases hx : x ≤ μ
  · simp [Set.indicator_of_mem hx, ENNReal.toReal_add, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal, hρ0, sub_nonneg.mpr hρ1, hμ0, hx]
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    simp [ENNReal.toReal_mul, hρ0, sub_nonneg.mpr hρ1, hμ0]
  · simp [Set.indicator_of_not_mem hx, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal, sub_nonneg.mpr hρ1, hμ0, hx]

theorem integral_threshold_piecewise {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (a b : ℝ) :
    (∫ x, (if x ≤ μ then a else b) ∂uniformUnit) = μ * a + (1 - μ) * b := by
  change (∫ x, (Iic μ).piecewise (fun _ => a) (fun _ => b) x ∂uniformUnit) = _
  rw [integral_piecewise measurableSet_Iic (integrable_const a).integrableOn
    (integrable_const b).integrableOn]
  rw [setIntegral_const, setIntegral_const]
  simp only [compl_Iic, Measure.real, uniformUnit_Iic hμ0 hμ1, uniformUnit_Ioi hμ0 hμ1,
    ENNReal.toReal_ofReal hμ0, ENNReal.toReal_ofReal (sub_nonneg.mpr hμ1), smul_eq_mul]

theorem posterior_mem_unit {μ ρ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (x : ℝ) :
    0 ≤ posterior μ ρ x ∧ posterior μ ρ x ≤ 1 := by
  rw [posterior_eq hμ0 hμ1 hρ0 hρ1]
  have hprod := mul_nonneg (sub_nonneg.mpr hρ1) hμ0
  have hcomp := mul_nonneg (sub_nonneg.mpr hρ1) (sub_nonneg.mpr hμ1)
  split_ifs <;> constructor <;> nlinarith

theorem posterior_integrable {μ ρ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) : Integrable (posterior μ ρ) uniformUnit := by
  classical
  simp_rw [funext (posterior_eq hμ0 hμ1 hρ0 hρ1)]
  exact Integrable.piecewise measurableSet_Iic (integrable_const _).integrableOn
    (integrable_const _).integrableOn

theorem posterior_entropy_integrable {μ ρ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Integrable (fun x => entropyBits (posterior μ ρ x)) uniformUnit := by
  classical
  simp_rw [posterior_eq hμ0 hμ1 hρ0 hρ1, apply_ite entropyBits]
  exact Integrable.piecewise measurableSet_Iic (integrable_const _).integrableOn
    (integrable_const _).integrableOn

theorem integral_posterior {μ ρ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∫ x, posterior μ ρ x ∂uniformUnit) = μ := by
  simp_rw [posterior_eq hμ0 hμ1 hρ0 hρ1]
  rw [integral_threshold_piecewise hμ0 hμ1]
  ring

theorem integral_posterior_entropy {μ ρ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∫ x, entropyBits (posterior μ ρ x) ∂uniformUnit) =
      μ * entropyBits (ρ + (1 - ρ) * μ) + (1 - μ) * entropyBits ((1 - ρ) * μ) := by
  simp_rw [posterior_eq hμ0 hμ1 hρ0 hρ1, apply_ite entropyBits]
  exact integral_threshold_piecewise hμ0 hμ1 _ _

/-- Binary mutual information of the actual uniform-input resampling kernel. -/
def kernelInformation (μ ρ : ℝ) : ℝ :=
  entropyBits (∫ x, posterior μ ρ x ∂uniformUnit) -
    ∫ x, entropyBits (posterior μ ρ x) ∂uniformUnit

theorem kernelInformation_eq {μ ρ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) : kernelInformation μ ρ = information μ ρ := by
  unfold kernelInformation information
  rw [integral_posterior hμ0 hμ1 hρ0 hρ1, integral_posterior_entropy hμ0 hμ1 hρ0 hρ1]
  ring

/-- The selected output coordinate given the selected input and further observations. -/
def observedResamplingKernel {Ω : Type*} [MeasurableSpace Ω] (ρ : ℝ) : Kernel (ℝ × Ω) ℝ where
  toFun z := resamplingKernel ρ z.1
  measurable' := (resamplingKernel ρ).measurable.comp measurable_fst

theorem observedResamplingKernel_isMarkov {Ω : Type*} [MeasurableSpace Ω] {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) : IsMarkovKernel (observedResamplingKernel (Ω := Ω) ρ) := by
  constructor
  intro z
  exact (resamplingKernel_isMarkov hρ0 hρ1).isProbabilityMeasure z.1

/-- Additional independent observed coordinates have their own arbitrary probability law. -/
def kernelInformationWithObservation {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (μ ρ : ℝ) : ℝ :=
  entropyBits (∫ z : ℝ × Ω, (observedResamplingKernel ρ z).real (Iic μ) ∂uniformUnit.prod ν) -
    ∫ z : ℝ × Ω, entropyBits ((observedResamplingKernel ρ z).real (Iic μ)) ∂uniformUnit.prod ν

theorem kernelInformationWithObservation_eq {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (μ ρ : ℝ) :
    kernelInformationWithObservation ν μ ρ = kernelInformation μ ρ := by
  unfold kernelInformationWithObservation kernelInformation
  change entropyBits (∫ z : ℝ × Ω, posterior μ ρ z.1 ∂uniformUnit.prod ν) -
    (∫ z : ℝ × Ω, entropyBits (posterior μ ρ z.1) ∂uniformUnit.prod ν) = _
  rw [integral_fun_fst (posterior μ ρ), integral_fun_fst (fun x => entropyBits (posterior μ ρ x))]
  simp

/-- Manuscript `ck+vscontinuous` for the actual uniform-resampling kernel. -/
theorem progressiveEntropy_le_kernelInformation {μ p : ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    progressiveEntropy p μ ≤ kernelInformation μ (1 - 2 * p) := by
  rw [kernelInformation_eq hμ0 hμ1 (by linarith) (by linarith)]
  exact progressiveEntropy_le_thresholdInformation hμ0 hμ1 hp0 hp1

theorem progressiveEntropy_lt_kernelInformation {μ p : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hμhalf : μ ≠ 1 / 2)
    (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    progressiveEntropy p μ < kernelInformation μ (1 - 2 * p) := by
  rw [kernelInformation_eq hμ0.le hμ1.le (by linarith) (by linarith)]
  exact progressiveEntropy_lt_thresholdInformation hμ0 hμ1 hμhalf hp0 hp1

theorem progressiveEntropy_eq_kernelInformation_iff {μ p : ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    progressiveEntropy p μ = kernelInformation μ (1 - 2 * p) ↔
      μ = 0 ∨ μ = 1 / 2 ∨ μ = 1 := by
  rw [kernelInformation_eq hμ0 hμ1 (by linarith) (by linarith)]
  exact progressiveEntropy_eq_thresholdInformation_iff hμ0 hμ1 hp0 hp1

theorem progressiveEntropy_eq_kernelInformation_endpoints {μ p : ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hp : p = 0 ∨ p = 1 / 2) :
    progressiveEntropy p μ = kernelInformation μ (1 - 2 * p) := by
  have hp0 : 0 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  have hp1 : p ≤ 1 / 2 := by rcases hp with rfl | rfl <;> norm_num
  rw [kernelInformation_eq hμ0 hμ1 (by linarith) (by linarith)]
  exact progressiveEntropy_eq_thresholdInformation_endpoints μ p hp

end CourtadeKumar.Threshold
