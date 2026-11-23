import CK.KernelComparison

/-! # Every matching comparator for arbitrary observations

The comparator may live on a different finite probability space. Its joint
`A–B` channel agrees with the original channel, and no particular construction
of the matching bit is assumed.
-/

noncomputable section
namespace CourtadeKumar.KernelInformation.FiniteKernel
open Set MeasureTheory Filter

variable {U Γ Δ : Type*} [MeasurableSpace U] [Fintype Γ] [Fintype Δ]

private theorem binaryProfile_unbiased (d : ℝ) : Spec.binaryProfile 0 d = Spec.divergence d := by
  norm_num [Spec.binaryProfile]
  ring

/-- Universal clauses of both comparison lemmas, with arbitrary observation law
and an arbitrary matching comparator on any finite joint output alphabet. -/
theorem every_matching_comparator (K : FiniteKernel U Γ) (ν : Measure U)
    [IsProbabilityMeasure ν] (a b c : Γ → Bool) {γ : ℝ}
    (ha : ∀ᵐ u ∂ν, (K.law u).expect (fun s => FiniteLaw.bitValue (a s)) = 1 / 2)
    (hb : ∀ᵐ u ∂ν, (K.law u).expect (fun s => FiniteLaw.bitValue (b s)) = 1 / 2)
    (hchannel : ∀ᵐ u ∂ν, (K.law u).bitCorrelation a b = γ)
    (hmark : ∀ᵐ u ∂ν, (K.law u).conditionallyIndependentBit c a b)
    (hV : 0 < ∫ u, quadraticEntropy
      ((K.law u).expect (fun s => FiniteLaw.bitValue (c s))) ∂ν)
    (μ' : FiniteLaw Δ) (a' b' c' : Δ → Bool)
    (ha' : μ'.expect (fun s => FiniteLaw.bitValue (a' s)) = 1 / 2)
    (hb' : μ'.expect (fun s => FiniteLaw.bitValue (b' s)) = 1 / 2)
    (hc' : μ'.expect (fun s => FiniteLaw.bitValue (c' s)) = 1 / 2)
    (hchannel' : μ'.bitCorrelation a' b' = γ)
    (hmark' : μ'.conditionallyIndependentBit c' a' b')
    (hmatch' : μ'.shannonInformation (fun s => FiniteLaw.bitValue (b' s)) c' =
      (∫ u, (K.law u).shannonInformation (fun s => FiniteLaw.bitValue (b s)) c ∂ν) /
        (∫ u, quadraticEntropy ((K.law u).expect (fun s => FiniteLaw.bitValue (c s))) ∂ν)) :
    (∫ u, (K.law u).shannonInformation (fun s => FiniteLaw.bitValue (a s)) c ∂ν) /
        (∫ u, quadraticEntropy ((K.law u).expect (fun s => FiniteLaw.bitValue (c s))) ∂ν) ≤
      μ'.shannonInformation (fun s => FiniteLaw.bitValue (a' s)) c' ∧
    (K.mixture ν).quadraticInformation (fun s => FiniteLaw.bitValue (c s)) b /
        (∫ u, quadraticEntropy ((K.law u).expect (fun s => FiniteLaw.bitValue (c s))) ∂ν)^2 ≤
      μ'.quadraticInformation (fun s => FiniteLaw.bitValue (c' s)) b' := by
  obtain ⟨τ, hτ, hmatch, hupper, hcorr⟩ :=
    K.conditional_comparison ν a b c ha hb hchannel hmark hV
  have hbiasc' : μ'.bitBias c' = 0 := by unfold FiniteLaw.bitBias; rw [hc']; ring
  have hd1 : |μ'.bitCorrelation b' c'| ≤ 1 := by
    have h := μ'.binaryProfile_parameters_domain b' c' hb'
    simpa only [hbiasc', abs_zero, zero_add] using h
  have hI' : μ'.shannonInformation (fun s => FiniteLaw.bitValue (b' s)) c' =
      Spec.divergence |μ'.bitCorrelation b' c'| := by
    rw [μ'.shannonInformation_eq_binaryProfile b' c' hb', hbiasc', binaryProfile_unbiased,
      Spec.divergence_abs]
  have hD : Spec.divergence |μ'.bitCorrelation b' c'| = Spec.divergence τ := by
    rw [← hI', hmatch']
    apply (div_eq_iff hV.ne').mpr
    nlinarith [hmatch]
  have hd : |μ'.bitCorrelation b' c'| = τ :=
    Spec.divergence_strictMonoOn.injOn ⟨abs_nonneg _, hd1⟩ hτ hD
  have hA' : μ'.shannonInformation (fun s => FiniteLaw.bitValue (a' s)) c' =
      Spec.divergence (|γ| * τ) := by
    rw [μ'.shannonInformation_markov_profile a' b' c' ha' hb' hmark', hbiasc', binaryProfile_unbiased,
      ← Spec.divergence_abs, abs_mul, hd, hchannel']
  have hQ' : μ'.quadraticInformation (fun s => FiniteLaw.bitValue (c' s)) b' = τ^2 := by
    rw [μ'.quadraticInformation_eq_bitCorrelation b' c' hb', ← sq_abs, hd]
  constructor
  · rw [hA']
    exact (div_le_iff₀ hV).mpr (by nlinarith [hupper])
  · rw [hQ']
    exact hcorr

end CourtadeKumar.KernelInformation.FiniteKernel
