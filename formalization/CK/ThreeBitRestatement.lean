import CK.ThreeBitSemantics
import CK.GapBounds

/-! The exact conditional-information restatement of the three-bit lemma,
including the zero first-channel correlation case. -/

noncomputable section
namespace CourtadeKumar.FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem three_bit_markov_information_difference (μ : FiniteLaw Ω) (a b c : Ω → Bool)
    (hmark : μ.conditionallyIndependentBit c a b) :
    μ.conditionalShannonInformation (fun ω => bitValue (a ω)) b c=
      μ.shannonInformation (fun ω => bitValue (a ω)) b-
        μ.shannonInformation (fun ω => bitValue (a ω)) c := by
  have hz : μ.conditionalShannonInformation (fun ω => bitValue (a ω)) c b=0 := by
    rw [μ.conditionalShannonInformation_symm a c b,
      μ.conditionalShannonInformation_eq_entropy_diff b a,
      μ.conditionalShannonEntropy_of_conditionalIndependence c a b hmark]
    ring
  have h₁ := μ.shannonInformation_chain b c (fun ω => bitValue (a ω))
  have h₂ := μ.shannonInformation_chain c b (fun ω => bitValue (a ω))
  have he := μ.shannonInformation_equiv (fun ω => (b ω,c ω))
    (Equiv.prodComm Bool Bool) (fun ω => bitValue (a ω))
  change μ.shannonInformation (fun ω => bitValue (a ω)) (fun ω => (c ω,b ω))=
    μ.shannonInformation (fun ω => bitValue (a ω)) (fun ω => (b ω,c ω)) at he
  linarith

/-- Literal later restatement of manuscript Lemma `three-bit`. The first
numerator is actual conditional mutual information, and zero first-channel
correlation is included. -/
theorem three_bit_information_restated (μ : FiniteLaw Ω) (a b c : Ω → Bool)
    (ha : μ.expect (fun ω => bitValue (a ω))=1/2)
    (hb : μ.expect (fun ω => bitValue (b ω))=1/2)
    (hc : μ.expect (fun ω => bitValue (c ω))=1/2)
    (hmark : μ.conditionallyIndependentBit c a b)
    (hq1 : μ.quadraticInformation (fun ω => bitValue (a ω)) b<1)
    (hσpos : 0<μ.quadraticInformation (fun ω => bitValue (b ω)) c) :
    let q := μ.quadraticInformation (fun ω => bitValue (a ω)) b
    let I := μ.shannonInformation (fun ω => bitValue (a ω)) b
    q-I ≤ μ.conditionalShannonInformation (fun ω => bitValue (a ω)) b c /
      (2*(1+(q-I)*Real.log 2/μ.conditionalQuadraticEntropy b (fun ω => bitValue (a ω))))+
      2*(q*μ.shannonInformation (fun ω => bitValue (b ω)) c-
        μ.shannonInformation (fun ω => bitValue (a ω)) c)/
        Real.sqrt (μ.quadraticInformation (fun ω => bitValue (b ω)) c) := by
  dsimp only
  rw [μ.three_bit_markov_information_difference a b c hmark]
  have hT : μ.conditionalQuadraticEntropy b (fun ω => bitValue (a ω))=
      1-μ.quadraticInformation (fun ω => bitValue (a ω)) b := by
    unfold quadraticInformation
    rw [ha]
    norm_num [quadraticEntropy]
  rw [hT]
  by_cases hq0 : μ.quadraticInformation (fun ω => bitValue (a ω)) b=0
  · have hr : μ.bitCorrelation a b=0 := by
      rw [μ.quadraticInformation_eq_bitCorrelation b a hb,μ.bitCorrelation_symm b a] at hq0
      exact sq_eq_zero_iff.mp hq0
    have hI : μ.shannonInformation (fun ω => bitValue (a ω)) b=0 := by
      rw [μ.shannonInformation_unbiased_bits a b ha hb,hr,abs_zero,Spec.divergence_zero]
    have hAC : μ.shannonInformation (fun ω => bitValue (a ω)) c=0 := by
      rw [μ.shannonInformation_unbiased_bits a c ha hc,μ.bitCorrelation_markov a b c ha hb hmark,
        hr,zero_mul,abs_zero,Spec.divergence_zero]
    simp [hq0,hI,hAC]
  · have hqpos : 0<μ.quadraticInformation (fun ω => bitValue (a ω)) b :=
      lt_of_le_of_ne (μ.quadraticInformation_nonneg b
        (fun ω => bitValue_nonneg (a ω)) (fun ω => bitValue_le_one (a ω))) (Ne.symm hq0)
    exact (μ.three_bit_information a b c ha hb hc hmark hqpos hq1 hσpos).le

end CourtadeKumar.FiniteLaw
