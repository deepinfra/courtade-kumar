import CK.GapBounds
import Mathlib.Analysis.Convex.Integral

/-!
# Finite output kernels over arbitrary observation laws

Only the output alphabet is finite. The index/observation space has an arbitrary
measurable structure and an arbitrary probability measure.
-/

noncomputable section
namespace CourtadeKumar.KernelInformation
open Set MeasureTheory Filter
open scoped BigOperators

structure FiniteKernel (U Γ : Type*) [MeasurableSpace U] [Fintype Γ] where
  law : U → FiniteLaw Γ
  measurable_mass : ∀ a, Measurable (fun u => (law u).mass a)

namespace FiniteKernel

variable {U Γ Z : Type*} [MeasurableSpace U] [Fintype Γ]
variable [Fintype Z] [DecidableEq Z]

omit [Fintype Z] [DecidableEq Z] in
theorem mass_le_one (μ : FiniteLaw Γ) (a : Γ) : μ.mass a ≤ 1 := by
  classical
  calc
    μ.mass a ≤ ∑ b, μ.mass b := Finset.single_le_sum (fun b _ => μ.mass_nonneg b) (Finset.mem_univ a)
    _ = 1 := μ.mass_sum

omit [Fintype Z] [DecidableEq Z] in
theorem measurable_expect (K : FiniteKernel U Γ) (f : Γ → ℝ) :
    Measurable (fun u => (K.law u).expect f) := by
  unfold FiniteLaw.expect
  exact Finset.measurable_sum _ fun a _ => (K.measurable_mass a).mul_const (f a)

omit [Fintype Z] [DecidableEq Z] in
theorem integrable_mass (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν] (a : Γ) :
    Integrable (fun u => (K.law u).mass a) ν := by
  apply (integrable_const (1 : ℝ)).mono' (K.measurable_mass a).aestronglyMeasurable
  exact ae_of_all _ fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg ((K.law u).mass_nonneg a)]
    exact mass_le_one (K.law u) a

omit [Fintype Z] [DecidableEq Z] in
theorem integrable_expect (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν] (f : Γ → ℝ) :
    Integrable (fun u => (K.law u).expect f) ν := by
  unfold FiniteLaw.expect
  exact integrable_finset_sum _ fun a _ => (K.integrable_mass ν a).mul_const (f a)

omit [Fintype Z] [DecidableEq Z] in
def mixture (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν] : FiniteLaw Γ where
  mass a := ∫ u, (K.law u).mass a ∂ν
  mass_nonneg a := integral_nonneg fun u => (K.law u).mass_nonneg a
  mass_sum := by
    rw [← integral_finset_sum _ (fun a _ => K.integrable_mass ν a)]
    simp only [FiniteLaw.mass_sum]
    simp

omit [Fintype Z] [DecidableEq Z] in
theorem expect_mixture (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν] (f : Γ → ℝ) :
    (K.mixture ν).expect f = ∫ u, (K.law u).expect f ∂ν := by
  unfold FiniteLaw.expect mixture
  rw [integral_finset_sum _ (fun a _ => (K.integrable_mass ν a).mul_const (f a))]
  simp_rw [integral_mul_const]

omit [Fintype Z] in
theorem measurable_fibreMass (K : FiniteKernel U Γ) (z : Γ → Z) (s : Z) :
    Measurable (fun u => (K.law u).fibreMass z s) := by
  simp_rw [FiniteLaw.fibreMass_eq_expect]
  exact K.measurable_expect _

omit [Fintype Z] in
theorem measurable_fibreMoment (K : FiniteKernel U Γ) (z : Γ → Z) (f : Γ → ℝ) (s : Z) :
    Measurable (fun u => (K.law u).fibreMoment z f s) := by
  simp_rw [FiniteLaw.fibreMoment_eq_expect]
  exact K.measurable_expect _

omit [Fintype Z] in
theorem measurable_conditionalMean (K : FiniteKernel U Γ) (z : Γ → Z) (f : Γ → ℝ) (s : Z) :
    Measurable (fun u => (K.law u).conditionalMean z f s) :=
  (K.measurable_fibreMoment z f s).div (K.measurable_fibreMass z s)

omit [Fintype Z] in
theorem fibreMass_mixture (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (z : Γ → Z) (s : Z) : (K.mixture ν).fibreMass z s = ∫ u, (K.law u).fibreMass z s ∂ν := by
  simp_rw [FiniteLaw.fibreMass_eq_expect]
  exact K.expect_mixture ν _

omit [Fintype Z] in
theorem fibreMoment_mixture (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (z : Γ → Z) (f : Γ → ℝ) (s : Z) :
    (K.mixture ν).fibreMoment z f s = ∫ u, (K.law u).fibreMoment z f s ∂ν := by
  simp_rw [FiniteLaw.fibreMoment_eq_expect]
  exact K.expect_mixture ν _

omit [Fintype Z] [DecidableEq Z] in
theorem integrable_bounded (ν : Measure U) [IsProbabilityMeasure ν] {f : U → ℝ}
    (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u) (hf1 : ∀ u, f u ≤ 1) : Integrable f ν := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact ae_of_all _ fun u => by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 u)]; exact hf1 u

omit [Fintype Z] [DecidableEq Z] in
theorem measurable_bitEntropy (K : FiniteKernel U Γ) (c : Γ → Bool) :
    Measurable (fun u => quadraticEntropy ((K.law u).expect (fun a => FiniteLaw.bitValue (c a)))) := by
  unfold quadraticEntropy
  exact ((K.measurable_expect _).const_mul 4).mul (measurable_const.sub (K.measurable_expect _))

omit [Fintype Z] [DecidableEq Z] in
theorem integrable_bitEntropy (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (c : Γ → Bool) : Integrable (fun u => quadraticEntropy ((K.law u).expect (fun a => FiniteLaw.bitValue (c a)))) ν :=
  integrable_bounded ν (K.measurable_bitEntropy c) (fun u => (K.law u).bit_entropy_nonneg c)
    (fun _ => quadraticEntropy_le_one _)

theorem measurable_quadraticInformation (K : FiniteKernel U Γ) (z : Γ → Z) (c : Γ → ℝ) :
    Measurable (fun u => (K.law u).quadraticInformation c z) := by
  unfold FiniteLaw.quadraticInformation FiniteLaw.conditionalQuadraticEntropy
    FiniteLaw.expect FiniteLaw.map quadraticEntropy
  apply Measurable.sub
  · exact ((K.measurable_expect c).const_mul 4).mul (measurable_const.sub (K.measurable_expect c))
  · apply Finset.measurable_sum
    intro s _
    exact (K.measurable_fibreMass z s).mul
      (((K.measurable_conditionalMean z c s).const_mul 4).mul
        (measurable_const.sub (K.measurable_conditionalMean z c s)))

theorem integrable_quadraticInformation (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (z : Γ → Z) (c : Γ → ℝ) (hc0 : ∀ a, 0 ≤ c a) (hc1 : ∀ a, c a ≤ 1) :
    Integrable (fun u => (K.law u).quadraticInformation c z) ν :=
  integrable_bounded ν (K.measurable_quadraticInformation z c)
    (fun u => (K.law u).quadraticInformation_nonneg z hc0 hc1)
    (fun u => ((K.law u).quadraticInformation_le_entropy z hc0 hc1).trans (quadraticEntropy_le_one _))

end FiniteKernel
end CourtadeKumar.KernelInformation
