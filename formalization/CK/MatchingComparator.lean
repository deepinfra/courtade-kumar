import CK.BinaryProfileSemantics

/-!
# Every matching unbiased comparator satisfies both comparison inequalities

This is the universal clause of the manuscript's comparison and correlation
lemmas. Strict monotonicity of binary divergence identifies the absolute
correlation of an arbitrary matching bit with the unique matching parameter.
-/

noncomputable section
namespace CourtadeKumar
namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

private theorem binaryProfile_unbiased (d : ℝ) : Spec.binaryProfile 0 d=Spec.divergence d := by
  norm_num [Spec.binaryProfile]
  ring

/-- Universal comparison for any unbiased matching bit in the actual joint law. -/
theorem every_matching_comparator (μ : FiniteLaw Ω) (a b c c' : Ω → Bool)
    {U : Type*} [Fintype U] [DecidableEq U] (u : Ω → U)
    (hau : μ.independentUnbiasedBit a u) (hbu : μ.independentUnbiasedBit b u)
    (hchannel : ∀ s, 0 < μ.fibreMass u s →
      (μ.conditionOn u s).bitCorrelation a b=μ.bitCorrelation a b)
    (hmark : ∀ s, 0 < μ.fibreMass u s →
      (μ.conditionOn u s).conditionallyIndependentBit c a b)
    (hV : 0 < μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)))
    (hc' : μ.expect (fun ω => bitValue (c' ω))=1/2)
    (hmark' : μ.conditionallyIndependentBit c' a b)
    (hmatch' : μ.shannonInformation (fun ω => bitValue (b ω)) c' =
      μ.conditionalShannonInformation (fun ω => bitValue (b ω)) c u /
        μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω))) :
    μ.conditionalShannonInformation (fun ω => bitValue (a ω)) c u /
        μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) ≤
      μ.shannonInformation (fun ω => bitValue (a ω)) c' ∧
    μ.quadraticInformation (fun ω => bitValue (c ω)) b /
        (μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)))^2 ≤
      μ.quadraticInformation (fun ω => bitValue (c' ω)) b := by
  have ha := μ.mean_of_independentUnbiasedBit a u hau
  have hb := μ.mean_of_independentUnbiasedBit b u hbu
  have hbiasa : μ.bitBias a=0 := by unfold bitBias;rw [ha];ring
  have hbiasc' : μ.bitBias c'=0 := by unfold bitBias;rw [hc'];ring
  have hρ1 : |μ.bitCorrelation a b| ≤ 1 := by
    have h := μ.binaryProfile_parameters_domain b a hb
    rw [μ.bitCorrelation_symm b a] at h
    simpa only [hbiasa,abs_zero,zero_add] using h
  obtain ⟨τ,hτ,hmatch,hupper,hcorr⟩ := μ.conditional_comparison a b c u
    (abs_nonneg _) hρ1 hau hbu (fun s hs => by rw [hchannel s hs]) hmark hV
  have hd1 : |μ.bitCorrelation b c'| ≤ 1 := by
    have h := μ.binaryProfile_parameters_domain b c' hb
    simpa only [hbiasc',abs_zero,zero_add] using h
  have hI' : μ.shannonInformation (fun ω => bitValue (b ω)) c' =
      Spec.divergence |μ.bitCorrelation b c'| := by
    rw [μ.shannonInformation_eq_binaryProfile b c' hb,hbiasc',binaryProfile_unbiased,
      Spec.divergence_abs]
  have hD : Spec.divergence |μ.bitCorrelation b c'|=Spec.divergence τ := by
    rw [← hI',hmatch']
    apply (div_eq_iff (ne_of_gt hV)).mpr
    nlinarith [hmatch]
  have hd : |μ.bitCorrelation b c'|=τ :=
    Spec.divergence_strictMonoOn.injOn ⟨abs_nonneg _,hd1⟩ hτ hD
  have hA' : μ.shannonInformation (fun ω => bitValue (a ω)) c' =
      Spec.divergence (|μ.bitCorrelation a b| * τ) := by
    rw [μ.shannonInformation_markov_profile a b c' ha hb hmark',hbiasc',binaryProfile_unbiased,
      ← Spec.divergence_abs,abs_mul,hd]
  have hQ' : μ.quadraticInformation (fun ω => bitValue (c' ω)) b=τ^2 := by
    rw [μ.quadraticInformation_eq_bitCorrelation b c' hb,← sq_abs,hd]
  constructor
  · rw [hA']
    exact (div_le_iff₀ hV).mpr (by nlinarith [hupper])
  · rw [hQ']
    exact hcorr

end FiniteLaw
end CourtadeKumar
