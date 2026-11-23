import CK.KernelRandomization
import CK.ComparisonMeasure

/-!
# Conditional comparison for arbitrary observation laws

These are statements about measurable kernels of actual finite joint laws, with
no finiteness assumption on the observation space. The comparison witness is a
single private BSC randomizer, with the same parameter in every conditional law.
-/

set_option maxHeartbeats 500000
noncomputable section
namespace CourtadeKumar.KernelInformation.FiniteKernel
open Set MeasureTheory Filter

variable {U Γ : Type*} [MeasurableSpace U] [Fintype Γ]

/-- The comparison parameter for actual information averaged over an arbitrary
observation law. The signed `A–B` channel is fixed almost everywhere. -/
theorem conditional_comparison (K : FiniteKernel U Γ) (ν : Measure U)
    [IsProbabilityMeasure ν] (a b c : Γ → Bool) {γ : ℝ}
    (ha : ∀ᵐ u ∂ν, (K.law u).expect (fun s => FiniteLaw.bitValue (a s)) = 1 / 2)
    (hb : ∀ᵐ u ∂ν, (K.law u).expect (fun s => FiniteLaw.bitValue (b s)) = 1 / 2)
    (hchannel : ∀ᵐ u ∂ν, (K.law u).bitCorrelation a b = γ)
    (hmark : ∀ᵐ u ∂ν, (K.law u).conditionallyIndependentBit c a b)
    (hV : 0 < ∫ u, quadraticEntropy
      ((K.law u).expect (fun s => FiniteLaw.bitValue (c s))) ∂ν) :
    ∃ τ ∈ Icc (0 : ℝ) 1,
      (∫ u, (K.law u).shannonInformation (fun s => FiniteLaw.bitValue (b s)) c ∂ν) =
        (∫ u, quadraticEntropy ((K.law u).expect (fun s => FiniteLaw.bitValue (c s))) ∂ν) *
          Spec.divergence τ ∧
      (∫ u, (K.law u).shannonInformation (fun s => FiniteLaw.bitValue (a s)) c ∂ν) ≤
        (∫ u, quadraticEntropy ((K.law u).expect (fun s => FiniteLaw.bitValue (c s))) ∂ν) *
          Spec.divergence (|γ| * τ) ∧
      (K.mixture ν).quadraticInformation (fun s => FiniteLaw.bitValue (c s)) b /
        (∫ u, quadraticEntropy ((K.law u).expect (fun s => FiniteLaw.bitValue (c s))) ∂ν)^2 ≤ τ^2 := by
  have hx : AEStronglyMeasurable (fun u => (K.law u).bitBias c) ν :=
    (((K.measurable_expect (fun s => FiniteLaw.bitValue (c s))).const_mul 2).sub_const 1).aestronglyMeasurable
  have hd : AEStronglyMeasurable (fun u => (K.law u).bitCorrelation b c) ν :=
    (K.measurable_expect _).aestronglyMeasurable
  have hdom : ∀ᵐ u ∂ν, |(K.law u).bitBias c| + |(K.law u).bitCorrelation b c| ≤ 1 :=
    hb.mono fun u hu => (K.law u).binaryProfile_parameters_domain b c hu
  have hbmean := K.mixture_unbiased ν b hb
  have hγmean := K.mixture_fixed_correlation ν a b hchannel
  have hγ1 : |γ| ≤ 1 := by
    have h := (K.mixture ν).binaryProfile_parameters_domain b a hbmean
    rw [FiniteLaw.bitCorrelation_symm, hγmean] at h
    linarith [abs_nonneg ((K.mixture ν).bitBias a)]
  have hVeq : (∫ u, quadraticEntropy ((K.law u).expect (fun s => FiniteLaw.bitValue (c s))) ∂ν) =
      ∫ u, 1 - (K.law u).bitBias c ^ 2 ∂ν := by
    apply integral_congr_ae
    exact ae_of_all _ fun u => (K.law u).quadraticEntropy_eq_bitBias c
  have hIB : (∫ u, (K.law u).shannonInformation (fun s => FiniteLaw.bitValue (b s)) c ∂ν) =
      ∫ u, Spec.binaryProfile ((K.law u).bitBias c) ((K.law u).bitCorrelation b c) ∂ν := by
    exact integral_congr_ae (hb.mono fun u hu => (K.law u).shannonInformation_eq_binaryProfile b c hu)
  have hIA : (∫ u, (K.law u).shannonInformation (fun s => FiniteLaw.bitValue (a s)) c ∂ν) =
      ∫ u, Spec.binaryProfile ((K.law u).bitBias c) (|γ| * (K.law u).bitCorrelation b c) ∂ν := by
    apply integral_congr_ae
    filter_upwards [ha, hb, hchannel, hmark] with u hau hbu hγu hmu
    rw [(K.law u).shannonInformation_markov_profile a b c hau hbu hmu,
      hγu, Spec.binaryProfile_abs_channel]
  rw [hVeq] at hV
  obtain ⟨τ, hτ, hmatch, hupper, hcorr⟩ :=
    MeasureComparison.binaryProfile_integral_comparison hx hd hdom (abs_nonneg γ) hγ1 hV
  refine ⟨τ, hτ, ?_, ?_, ?_⟩
  · simpa only [hIB, hVeq] using hmatch
  · simpa only [hIA, hVeq] using hupper
  · rw [(K.mixture ν).quadraticInformation_eq_bitCorrelation b c hbmean,
      K.bitCorrelation_mixture ν b c, hVeq]
    exact hcorr

/-- Literal comparator realization over arbitrary observations. The original
conditional law is preserved at every observation, and the witness uses the
same independent flip-noise law throughout. All information quantities below
are the actual finite marginal or integrated conditional information. -/
theorem conditional_comparison_realized (K : FiniteKernel U Γ) (ν : Measure U)
    [IsProbabilityMeasure ν] [DecidableEq Γ] (a b c : Γ → Bool) {γ : ℝ}
    (ha : ∀ᵐ u ∂ν, (K.law u).expect (fun s => FiniteLaw.bitValue (a s)) = 1 / 2)
    (hb : ∀ᵐ u ∂ν, (K.law u).expect (fun s => FiniteLaw.bitValue (b s)) = 1 / 2)
    (hchannel : ∀ᵐ u ∂ν, (K.law u).bitCorrelation a b = γ)
    (hmark : ∀ᵐ u ∂ν, (K.law u).conditionallyIndependentBit c a b)
    (hV : 0 < ∫ u, quadraticEntropy
      ((K.law u).expect (fun s => FiniteLaw.bitValue (c s))) ∂ν) :
    ∃ (K' : FiniteKernel U (Γ × Bool)) (c' : Γ × Bool → Bool),
      (∀ u, (K'.law u).map Prod.fst = K.law u) ∧
      (∀ u, (K'.law u).conditionallyIndependentBit c' Prod.fst (fun p => b p.1)) ∧
      (K'.mixture ν).map Prod.fst = K.mixture ν ∧
      (K'.mixture ν).conditionallyIndependentBit c' Prod.fst (fun p => b p.1) ∧
      (K'.mixture ν).expect (fun p => FiniteLaw.bitValue (c' p)) = 1 / 2 ∧
      (K'.mixture ν).shannonInformation (fun p => FiniteLaw.bitValue (b p.1)) c' =
        (∫ u, (K.law u).shannonInformation (fun s => FiniteLaw.bitValue (b s)) c ∂ν) /
          (∫ u, quadraticEntropy ((K.law u).expect (fun s => FiniteLaw.bitValue (c s))) ∂ν) ∧
      (∫ u, (K.law u).shannonInformation (fun s => FiniteLaw.bitValue (a s)) c ∂ν) /
          (∫ u, quadraticEntropy ((K.law u).expect (fun s => FiniteLaw.bitValue (c s))) ∂ν) ≤
        (K'.mixture ν).shannonInformation (fun p => FiniteLaw.bitValue (a p.1)) c' ∧
      (K.mixture ν).quadraticInformation (fun s => FiniteLaw.bitValue (c s)) b /
          (∫ u, quadraticEntropy ((K.law u).expect (fun s => FiniteLaw.bitValue (c s))) ∂ν)^2 ≤
        (K'.mixture ν).quadraticInformation (fun p => FiniteLaw.bitValue (c' p)) (fun p => b p.1) := by
  have hamean := K.mixture_unbiased ν a ha
  have hbmean := K.mixture_unbiased ν b hb
  have hγmean := K.mixture_fixed_correlation ν a b hchannel
  obtain ⟨τ, hτ, hmatch, hupper, hcorr⟩ :=
    K.conditional_comparison ν a b c ha hb hchannel hmark hV
  refine ⟨K.comparatorExtension τ hτ.1 hτ.2, FiniteLaw.comparatorBit b,
    K.comparatorExtension_map_fst τ hτ.1 hτ.2,
    K.comparatorExtension_markov b τ hτ.1 hτ.2, ?_⟩
  rw [K.mixture_comparatorExtension ν τ hτ.1 hτ.2]
  refine ⟨(K.mixture ν).comparatorExtension_map_fst τ hτ.1 hτ.2,
    (K.mixture ν).comparatorExtension_markov b τ hτ.1 hτ.2 id,
    (K.mixture ν).comparatorExtension_output_unbiased b τ hτ.1 hτ.2 hbmean, ?_, ?_, ?_⟩
  · rw [(K.mixture ν).comparatorExtension_shannonInformation b τ hτ.1 hτ.2 hbmean]
    apply (eq_div_iff hV.ne').mpr
    nlinarith [hmatch]
  · rw [(K.mixture ν).comparatorExtension_channel_information a b τ hτ.1 hτ.2 hamean hbmean,
      hγmean]
    exact (div_le_iff₀ hV).mpr (by nlinarith [hupper])
  · rw [(K.mixture ν).comparatorExtension_quadraticInformation b τ hτ.1 hτ.2 hbmean]
    exact hcorr

end CourtadeKumar.KernelInformation.FiniteKernel
