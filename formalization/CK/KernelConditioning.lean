import CK.KernelInformationBasic
import CK.PosteriorMeasure

/-! # Conditioning inequalities over arbitrary measurable observation laws -/

noncomputable section
namespace CourtadeKumar.KernelInformation
open Set MeasureTheory Filter

variable {U : Type*} [MeasurableSpace U] {ν : Measure U} [IsProbabilityMeasure ν]

/-- Integral Cauchy--Schwarz in the zero-safe covariance/variance form. -/
theorem integral_cauchy_div {r v : U → ℝ}
    (hr : Integrable r ν) (hv : Integrable v ν)
    (hq : Integrable (fun u => r u ^ 2 / v u) ν)
    (hv0 : ∀ᵐ u ∂ν, 0 ≤ v u) (hz : ∀ᵐ u ∂ν, v u = 0 → r u = 0) :
    (∫ u, r u ∂ν) ^ 2 ≤ (∫ u, r u ^ 2 / v u ∂ν) * (∫ u, v u ∂ν) := by
  have hV0 : 0 ≤ ∫ u, v u ∂ν := integral_nonneg_of_ae hv0
  by_cases hV : (∫ u, v u ∂ν) = 0
  · have hzero := (integral_eq_zero_iff_of_nonneg_ae hv0 hv).mp hV
    have hrzero : r =ᵐ[ν] 0 := by
      filter_upwards [hzero, hz] with u hu hz
      exact hz hu
    rw [integral_congr_ae hrzero]
    simp [hV]
  · let a := (∫ u, r u ∂ν) / (∫ u, v u ∂ν)
    have ha : (∫ u, r u ∂ν) = a * (∫ u, v u ∂ν) := by
      dsimp [a]
      field_simp
    have hnonneg : ∀ᵐ u ∂ν, 0 ≤ r u ^ 2 / v u - 2 * a * r u + a ^ 2 * v u := by
      filter_upwards [hv0, hz] with u hvu hzu
      by_cases hvu0 : v u = 0
      · simp [hvu0, hzu hvu0]
      · have he : r u ^ 2 / v u - 2 * a * r u + a ^ 2 * v u = (r u - a * v u) ^ 2 / v u := by
          field_simp
          ring
        rw [he]
        exact div_nonneg (sq_nonneg _) hvu
    have h := integral_nonneg_of_ae hnonneg
    rw [integral_add (f := fun u => r u ^ 2 / v u - 2 * a * r u) (g := fun u => a ^ 2 * v u)
      (hq.sub (hr.const_mul (2 * a))) (hv.const_mul (a ^ 2)),
      integral_sub (f := fun u => r u ^ 2 / v u) (g := fun u => 2 * a * r u)
        hq (hr.const_mul (2 * a)), integral_const_mul, integral_const_mul] at h
    rw [ha] at h ⊢
    have hm := mul_nonneg h hV0
    nlinarith

namespace FiniteKernel
variable {Γ : Type*} [Fintype Γ]

theorem covariance_mixture (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (b c : Γ → Bool) (β : ℝ) (hb : ∀ᵐ u ∂ν, (K.law u).expect (fun a => FiniteLaw.bitValue (b a)) = β) :
    (K.mixture ν).bitCovariance b c = ∫ u, (K.law u).bitCovariance b c ∂ν := by
  have hmean : (K.mixture ν).expect (fun a => FiniteLaw.bitValue (b a)) = β := by
    rw [K.expect_mixture, integral_congr_ae hb]
    simp
  have he : (fun u => (K.law u).bitCovariance b c) =ᵐ[ν]
      (fun u => (K.law u).expect (fun a => FiniteLaw.bitValue (b a) * FiniteLaw.bitValue (c a)) -
        β * (K.law u).expect (fun a => FiniteLaw.bitValue (c a))) := by
    filter_upwards [hb] with u hu
    simp [FiniteLaw.bitCovariance, hu]
  rw [integral_congr_ae he]
  unfold FiniteLaw.bitCovariance
  rw [hmean, K.expect_mixture, K.expect_mixture]
  rw [integral_sub (K.integrable_expect ν _)
    ((K.integrable_expect ν _).const_mul β), integral_const_mul]

theorem covariance_div_integrable (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (b c : Γ → Bool) :
    Integrable (fun u => (K.law u).bitCovariance b c ^ 2 /
      quadraticEntropy ((K.law u).expect (fun a => FiniteLaw.bitValue (c a)))) ν := by
  apply integrable_bounded ν ((K.measurable_bitCovariance b c).pow_const 2 |>.div (K.measurable_bitEntropy c))
  · intro u
    exact div_nonneg (sq_nonneg _) ((K.law u).bit_entropy_nonneg c)
  · intro u
    have h := (K.law u).covariance_div_le_information b c
    have h1 := (K.law u).quadraticInformation_le_entropy c
      (fun a => FiniteLaw.bitValue_nonneg (b a)) (fun a => FiniteLaw.bitValue_le_one (b a))
    have h2 := quadraticEntropy_le_one ((K.law u).expect (fun a => FiniteLaw.bitValue (b a)))
    nlinarith

/-- `item:tsallis-conditioning`, with no finite-support restriction on the observation law. -/
theorem quadratic_conditioning (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (b c : Γ → Bool) (β : ℝ) (hb : ∀ᵐ u ∂ν, (K.law u).expect (fun a => FiniteLaw.bitValue (b a)) = β) :
    (∫ u, (K.law u).quadraticInformation (fun a => FiniteLaw.bitValue (b a)) c ∂ν) *
      (∫ u, quadraticEntropy ((K.law u).expect (fun a => FiniteLaw.bitValue (c a))) ∂ν) ≥
      quadraticEntropy ((K.mixture ν).expect (fun a => FiniteLaw.bitValue (b a))) *
        (K.mixture ν).quadraticInformation (fun a => FiniteLaw.bitValue (c a)) b := by
  let r : U → ℝ := fun u => (K.law u).bitCovariance b c
  let v : U → ℝ := fun u => quadraticEntropy ((K.law u).expect (fun a => FiniteLaw.bitValue (c a)))
  have hCS := integral_cauchy_div (K.integrable_bitCovariance ν b c) (K.integrable_bitEntropy ν c)
    (K.covariance_div_integrable ν b c) (ae_of_all _ fun u => (K.law u).bit_entropy_nonneg c)
    (ae_of_all _ fun u => (K.law u).bitCovariance_eq_zero_of_entropy_eq_zero b c)
  have hupper : 16 * (∫ u, r u ^ 2 / v u ∂ν) ≤
      ∫ u, (K.law u).quadraticInformation (fun a => FiniteLaw.bitValue (b a)) c ∂ν := by
    rw [← integral_const_mul]
    exact integral_mono ((K.covariance_div_integrable ν b c).const_mul 16)
      (K.integrable_quadraticInformation ν c _ (fun a => FiniteLaw.bitValue_nonneg (b a))
        (fun a => FiniteLaw.bitValue_le_one (b a)))
      (fun u => (K.law u).covariance_div_le_information b c)
  have hv : 0 ≤ ∫ u, v u ∂ν := integral_nonneg fun u => (K.law u).bit_entropy_nonneg c
  have hupper' := mul_le_mul_of_nonneg_right hupper hv
  rw [(K.mixture ν).binary_covariance_identity b c, K.covariance_mixture ν b c β hb]
  change 16 * (∫ u, r u ∂ν) ^ 2 ≤ _
  change (∫ u, r u ∂ν) ^ 2 ≤ (∫ u, r u ^ 2 / v u ∂ν) * (∫ u, v u ∂ν) at hCS
  nlinarith

end FiniteKernel
end CourtadeKumar.KernelInformation
