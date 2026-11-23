import CK.FiniteKernel

/-! # Measurability and integrability of finite-output kernel information -/

noncomputable section
namespace CourtadeKumar.KernelInformation.FiniteKernel
open Set MeasureTheory Filter
open scoped BigOperators

variable {U Γ Z : Type*} [MeasurableSpace U] [Fintype Γ] [Fintype Z] [DecidableEq Z]

theorem measurable_shannonInformation (K : FiniteKernel U Γ) (z : Γ → Z) (c : Γ → ℝ) :
    Measurable (fun u => (K.law u).shannonInformation c z) := by
  have hH : Measurable entropyBits := by unfold entropyBits; fun_prop
  unfold FiniteLaw.shannonInformation FiniteLaw.conditionalShannonEntropy
    FiniteLaw.expect FiniteLaw.map
  apply Measurable.sub
  · exact hH.comp (K.measurable_expect c)
  · apply Finset.measurable_sum
    intro s _
    exact (K.measurable_fibreMass z s).mul (hH.comp (K.measurable_conditionalMean z c s))

theorem integrable_shannonInformation (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (z : Γ → Z) (c : Γ → ℝ) (hc0 : ∀ a, 0 ≤ c a) (hc1 : ∀ a, c a ≤ 1) :
    Integrable (fun u => (K.law u).shannonInformation c z) ν := by
  apply integrable_bounded ν (K.measurable_shannonInformation z c)
    (fun u => (K.law u).shannonInformation_nonneg z c hc0 hc1)
  intro u
  have he : 0 ≤ (K.law u).conditionalShannonEntropy z c :=
    ((K.law u).map z).expect_nonneg fun s => entropyBits_nonneg
      ((K.law u).conditionalMean_nonneg z hc0 s) ((K.law u).conditionalMean_le_one z hc1 s)
  unfold FiniteLaw.shannonInformation
  linarith [entropyBits_le_one ((K.law u).expect c)]

omit [Fintype Z] [DecidableEq Z] in
theorem measurable_bitCovariance (K : FiniteKernel U Γ) (b c : Γ → Bool) :
    Measurable (fun u => (K.law u).bitCovariance b c) := by
  unfold FiniteLaw.bitCovariance
  exact (K.measurable_expect _).sub ((K.measurable_expect _).mul (K.measurable_expect _))

omit [Fintype Z] [DecidableEq Z] in
theorem integrable_bitCovariance (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (b c : Γ → Bool) : Integrable (fun u => (K.law u).bitCovariance b c) ν := by
  apply (integrable_const (2 : ℝ)).mono' (K.measurable_bitCovariance b c).aestronglyMeasurable
  apply ae_of_all
  intro u
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  have hb0 := (K.law u).expect_nonneg (fun a => FiniteLaw.bitValue_nonneg (b a))
  have hc0 := (K.law u).expect_nonneg (fun a => FiniteLaw.bitValue_nonneg (c a))
  have hb1 := (K.law u).expect_le_one (fun a => FiniteLaw.bitValue_le_one (b a))
  have hc1 := (K.law u).expect_le_one (fun a => FiniteLaw.bitValue_le_one (c a))
  have hbc0 := (K.law u).expect_nonneg (fun a =>
    mul_nonneg (FiniteLaw.bitValue_nonneg (b a)) (FiniteLaw.bitValue_nonneg (c a)))
  have hbc1 := (K.law u).expect_le_one (fun a =>
    mul_le_one₀ (FiniteLaw.bitValue_le_one (b a)) (FiniteLaw.bitValue_nonneg (c a))
      (FiniteLaw.bitValue_le_one (c a)))
  unfold FiniteLaw.bitCovariance
  constructor <;> nlinarith

end CourtadeKumar.KernelInformation.FiniteKernel
