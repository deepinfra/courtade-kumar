import CK.ScalarThreeBit
import CK.BinaryProfileSemantics
import CK.GapAlgebra

/-! The three-bit scalar theorem stated for actual finite joint distributions. -/

noncomputable section
namespace CourtadeKumar.FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem shannonInformation_unbiased_bits (μ : FiniteLaw Ω) (b c : Ω → Bool)
    (hb : μ.expect (fun ω => bitValue (b ω)) = 1 / 2)
    (hc : μ.expect (fun ω => bitValue (c ω)) = 1 / 2) :
    μ.shannonInformation (fun ω => bitValue (b ω)) c =
      Spec.divergence |μ.bitCorrelation b c| := by
  have hx : μ.bitBias c = 0 := by unfold bitBias; rw [hc]; ring
  rw [μ.shannonInformation_eq_binaryProfile b c hb, hx, Spec.divergence_abs]
  norm_num [Spec.binaryProfile]
  ring

theorem bitCorrelation_abs_le_one (μ : FiniteLaw Ω) (b c : Ω → Bool)
    (hb : μ.expect (fun ω => bitValue (b ω)) = 1 / 2) :
    |μ.bitCorrelation b c| ≤ 1 := by
  have h := μ.binaryProfile_parameters_domain b c hb
  linarith [abs_nonneg (μ.bitBias c)]

/-- Manuscript Lemma `three-bit` for literal unbiased bits and an actual Markov
probability factorization. The strict scalar result supplies a strict version
of the paper's non-strict conclusion. -/
theorem three_bit_information (μ : FiniteLaw Ω) (a b c : Ω → Bool)
    (ha : μ.expect (fun ω => bitValue (a ω)) = 1 / 2)
    (hb : μ.expect (fun ω => bitValue (b ω)) = 1 / 2)
    (hc : μ.expect (fun ω => bitValue (c ω)) = 1 / 2)
    (hmark : μ.conditionallyIndependentBit c a b)
    (hq0 : 0 < μ.quadraticInformation (fun ω => bitValue (a ω)) b)
    (hq1 : μ.quadraticInformation (fun ω => bitValue (a ω)) b < 1)
    (hσpos : 0 < μ.quadraticInformation (fun ω => bitValue (b ω)) c) :
    let q := μ.quadraticInformation (fun ω => bitValue (a ω)) b
    let I := μ.shannonInformation (fun ω => bitValue (a ω)) b
    let J := q - I
    J < (I - μ.shannonInformation (fun ω => bitValue (a ω)) c) /
        (2 * (1 + alphaCoefficient q J (Real.log 2))) +
      2 * (q * μ.shannonInformation (fun ω => bitValue (b ω)) c -
        μ.shannonInformation (fun ω => bitValue (a ω)) c) /
          Real.sqrt (μ.quadraticInformation (fun ω => bitValue (b ω)) c) := by
  let ρ := |μ.bitCorrelation a b|
  let σ := |μ.bitCorrelation b c|
  have hρq : ρ ^ 2 = μ.quadraticInformation (fun ω => bitValue (a ω)) b := by
    rw [μ.quadraticInformation_eq_bitCorrelation b a hb, μ.bitCorrelation_symm b a]
    exact sq_abs _
  have hσq : σ ^ 2 = μ.quadraticInformation (fun ω => bitValue (b ω)) c := by
    rw [μ.quadraticInformation_eq_bitCorrelation c b hc, μ.bitCorrelation_symm c b]
    exact sq_abs _
  have hρnonneg : 0 ≤ ρ := abs_nonneg _
  have hσnonneg : 0 ≤ σ := abs_nonneg _
  have hρ0 : 0 < ρ := by nlinarith
  have hρ1 : ρ < 1 := by nlinarith
  have hσ0 : 0 < σ := by nlinarith
  have hσ1 : σ ≤ 1 := μ.bitCorrelation_abs_le_one b c hb
  have hI : Spec.divergence ρ = μ.shannonInformation (fun ω => bitValue (a ω)) b :=
    (μ.shannonInformation_unbiased_bits a b ha hb).symm
  have hBC : Spec.divergence σ = μ.shannonInformation (fun ω => bitValue (b ω)) c :=
    (μ.shannonInformation_unbiased_bits b c hb hc).symm
  have hAC : Spec.divergence (ρ * σ) = μ.shannonInformation (fun ω => bitValue (a ω)) c := by
    rw [μ.shannonInformation_unbiased_bits a c ha hc, μ.bitCorrelation_markov a b c ha hb hmark]
    dsimp [ρ, σ]
    rw [abs_mul]
  have hsqrt : Real.sqrt (μ.quadraticInformation (fun ω => bitValue (b ω)) c) = σ := by
    rw [← hσq, Real.sqrt_sq_eq_abs, abs_of_nonneg hσnonneg]
  have h := Spec.threeBit ρ σ hρ0 hρ1 hσ0 hσ1
  rw [hρq, hI, hBC, hAC] at h
  dsimp only
  rw [hsqrt]
  exact h

end CourtadeKumar.FiniteLaw
