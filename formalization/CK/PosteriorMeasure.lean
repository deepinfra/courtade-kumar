import CK.BiasDivergence
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Binary information for arbitrary posterior probability laws

There is no finite-support assumption in this module. On an arbitrary
probability space, an almost-everywhere `[0,1]`-valued posterior is sufficient:
measurability implies every integrability condition used below. The final
conditional-expectation statements instantiate the posterior with an actual
conditional expectation and prove its range and tower identity.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace CourtadeKumar
namespace Posterior
open Set MeasureTheory Filter

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]

/-- Shannon information as the entropy gap of a posterior probability. -/
def shannonGap (q : Ω → ℝ) : ℝ :=
  entropyBits (∫ ω,q ω ∂ν)-(∫ ω,entropyBits (q ω) ∂ν)

/-- Quadratic information as the quadratic entropy gap of a posterior probability. -/
def quadraticGap (q : Ω → ℝ) : ℝ :=
  quadraticEntropy (∫ ω,q ω ∂ν)-(∫ ω,quadraticEntropy (q ω) ∂ν)

variable {ν}

/-- Compact range proves integrability of every continuous posterior functional. -/
theorem integrable_comp {q : Ω → ℝ} (hq : AEStronglyMeasurable q ν)
    (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1) {F : ℝ → ℝ} (hF : Continuous F) :
    Integrable (fun ω => F (q ω)) ν := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF.continuousOn
  apply (integrable_const C).mono' (hF.comp_aestronglyMeasurable hq)
  filter_upwards [hqr] with ω hω
  exact hC (q ω) hω

theorem integrable_posterior {q : Ω → ℝ} (hq : AEStronglyMeasurable q ν)
    (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1) : Integrable q ν :=
  integrable_comp hq hqr continuous_id

theorem mean_mem_unit {q : Ω → ℝ} (hq : AEStronglyMeasurable q ν)
    (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1) : (∫ ω,q ω ∂ν) ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact integral_nonneg_of_ae (hqr.mono fun _ h => h.1)
  · have h := integral_mono_ae (integrable_posterior hq hqr) (integrable_const (1:ℝ))
      (hqr.mono fun _ h => h.2)
    simpa using h

private theorem continuous_entropyBits : Continuous entropyBits := by unfold entropyBits;fun_prop
private theorem continuous_quadraticEntropy : Continuous quadraticEntropy := by unfold quadraticEntropy;fun_prop
private theorem continuous_entropyCorrection : Continuous entropyCurvatureCorrection := by
  unfold entropyCurvatureCorrection
  fun_prop

/-- The conditional Shannon/Tsallis entropy sandwich for arbitrary posterior laws. -/
theorem entropy_sandwich {q : Ω → ℝ} (hq : AEStronglyMeasurable q ν)
    (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1) :
    (∫ ω,quadraticEntropy (q ω) ∂ν) ≤ (∫ ω,entropyBits (q ω) ∂ν) ∧
    (∫ ω,entropyBits (q ω) ∂ν) ≤ (1+(∫ ω,quadraticEntropy (q ω) ∂ν))/2 := by
  have hQ := integrable_comp hq hqr continuous_quadraticEntropy
  have hH := integrable_comp hq hqr continuous_entropyBits
  constructor
  · apply integral_mono_ae hQ hH
    filter_upwards [hqr] with ω hω
    exact quadratic_le_entropyBits hω.1 hω.2
  · have hupper : Integrable (fun ω => (1+quadraticEntropy (q ω))/2) ν :=
      ((integrable_const (1:ℝ)).add hQ).div_const 2
    have h := integral_mono_ae hH hupper (hqr.mono fun ω hω =>
      entropyBits_le_quadratic_upper hω.1 hω.2)
    rw [integral_div,integral_add (integrable_const (1:ℝ)) hQ] at h
    simpa using h

/-- Jensen implies nonnegative Shannon information for every posterior probability law. -/
theorem shannonGap_nonneg {q : Ω → ℝ} (hq : AEStronglyMeasurable q ν)
    (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1) : 0 ≤ shannonGap ν q := by
  have h := Real.strictConcave_binEntropy.concaveOn.le_map_integral
    Real.binEntropy_continuous.continuousOn isClosed_Icc hqr
    (integrable_posterior hq hqr) (integrable_comp hq hqr Real.binEntropy_continuous)
  unfold shannonGap entropyBits
  rw [integral_div]
  exact sub_nonneg.mpr (div_le_div_of_nonneg_right h log_two_pos.le)

/-- Exact variance formula; no discrete or finite-support hypothesis is present. -/
theorem variance_identity {q : Ω → ℝ} (hq : AEStronglyMeasurable q ν)
    (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1) :
    (∫ ω,(q ω-(∫ η,q η ∂ν))^2 ∂ν) =
      (∫ ω,(q ω)^2 ∂ν)-(∫ ω,q ω ∂ν)^2 := by
  let m := ∫ ω,q ω ∂ν
  have hi := integrable_posterior hq hqr
  have hsq := integrable_comp hq hqr (continuous_pow 2)
  have heq : (fun ω => (q ω-m)^2)=(fun ω => (q ω)^2-(2*m)*q ω+m^2) := by
    funext ω
    ring
  change (∫ ω,(q ω-m)^2 ∂ν)=(∫ ω,(q ω)^2 ∂ν)-m^2
  rw [heq,integral_add (f := fun ω => (q ω)^2-(2*m)*q ω) (g := fun _ => m^2)
    (hsq.sub (hi.const_mul (2*m))) (integrable_const (m^2)),
    integral_sub hsq (hi.const_mul (2*m)),integral_const_mul]
  simp only [integral_const,measureReal_univ_eq_one,one_smul]
  dsimp [m]
  ring

/-- Quadratic information equals four times posterior variance. -/
theorem quadraticGap_eq_variance {q : Ω → ℝ} (hq : AEStronglyMeasurable q ν)
    (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1) :
    quadraticGap ν q=4*(∫ ω,(q ω-(∫ η,q η ∂ν))^2 ∂ν) := by
  have hi := integrable_posterior hq hqr
  have hsq := integrable_comp hq hqr (continuous_pow 2)
  have heq : (fun ω => quadraticEntropy (q ω))=(fun ω => 4*q ω-4*(q ω)^2) := by
    funext ω
    unfold quadraticEntropy
    ring
  rw [variance_identity hq hqr]
  unfold quadraticGap
  rw [heq,integral_sub (hi.const_mul 4) (hsq.const_mul 4),integral_const_mul,integral_const_mul]
  unfold quadraticEntropy
  ring

theorem quadraticGap_nonneg {q : Ω → ℝ} (hq : AEStronglyMeasurable q ν)
    (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1) : 0 ≤ quadraticGap ν q := by
  rw [quadraticGap_eq_variance hq hqr]
  exact mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)

private theorem natural_entropy_gap {q : Ω → ℝ} :
    Real.binEntropy (∫ ω,q ω ∂ν)-(∫ ω,Real.binEntropy (q ω) ∂ν)=
      Real.log 2*shannonGap ν q := by
  unfold shannonGap entropyBits
  rw [integral_div]
  field_simp [ne_of_gt log_two_pos]

/-- Pinsker comparison for arbitrary posterior distributions. -/
theorem quadraticGap_le_shannonGap {q : Ω → ℝ} (hq : AEStronglyMeasurable q ν)
    (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1) :
    quadraticGap ν q ≤ 2*Real.log 2*shannonGap ν q := by
  have hH := integrable_comp hq hqr Real.binEntropy_continuous
  have hsq := integrable_comp hq hqr (continuous_pow 2)
  have h := entropyCurvatureCorrection_concave.le_map_integral
    continuous_entropyCorrection.continuousOn isClosed_Icc hqr
    (integrable_posterior hq hqr) (integrable_comp hq hqr continuous_entropyCorrection)
  unfold entropyCurvatureCorrection at h
  rw [integral_add hH (hsq.const_mul 2),integral_const_mul] at h
  rw [quadraticGap_eq_variance hq hqr,variance_identity hq hqr]
  have he := natural_entropy_gap (ν := ν) (q := q)
  nlinarith

/-- Unbiased binary input has the reverse Shannon/quadratic comparison. -/
theorem shannonGap_le_quadraticGap_of_unbiased {q : Ω → ℝ} (hq : AEStronglyMeasurable q ν)
    (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1) (hmean : (∫ ω,q ω ∂ν)=1/2) :
    shannonGap ν q ≤ quadraticGap ν q := by
  have h := (entropy_sandwich hq hqr).1
  unfold shannonGap quadraticGap
  rw [hmean,entropyBits_half]
  rw [show quadraticEntropy (1/2)=1 by norm_num [quadraticEntropy]]
  linarith

/-- The exact Bernoulli divergence integral equals the Shannon entropy gap. -/
theorem integral_binaryDivergenceNats {q : Ω → ℝ} (hq : AEStronglyMeasurable q ν)
    (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1) :
    (∫ ω,binaryDivergenceNats (q ω) (∫ η,q η ∂ν) ∂ν)=Real.log 2*shannonGap ν q := by
  let m := ∫ ω,q ω ∂ν
  have hi := integrable_posterior hq hqr
  have hH := integrable_comp hq hqr Real.binEntropy_continuous
  change (∫ ω,Real.binEntropy m-Real.binEntropy (q ω)+
    (q ω-m)*(Real.log (1-m)-Real.log m) ∂ν)=Real.log 2*shannonGap ν q
  rw [integral_add
    (f := fun ω => Real.binEntropy m-Real.binEntropy (q ω))
    (g := fun ω => (q ω-m)*(Real.log (1-m)-Real.log m))
    ((integrable_const _).sub hH) ((hi.sub (integrable_const _)).mul_const _),
    integral_sub (integrable_const _) hH,integral_mul_const,
    integral_sub hi (integrable_const _)]
  simp only [integral_const,measureReal_univ_eq_one,one_smul]
  dsimp [m]
  simp only [sub_self,zero_mul,add_zero]
  exact natural_entropy_gap

/-- The paper's sharp bias-dependent upper comparison for arbitrary posterior laws. -/
theorem shannonGap_le_biasCoefficient {q : Ω → ℝ} (hq : AEStronglyMeasurable q ν)
    (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1)
    (hm0 : 0 < ∫ ω,q ω ∂ν) (hm1 : (∫ ω,q ω ∂ν) < 1) :
    shannonGap ν q ≤ biasCoefficient (∫ ω,q ω ∂ν)/Real.log 2*quadraticGap ν q := by
  let m := ∫ ω,q ω ∂ν
  have hD : Integrable (fun ω => binaryDivergenceNats (q ω) m) ν :=
    integrable_comp hq hqr (F := fun x => binaryDivergenceNats x m)
      (by unfold binaryDivergenceNats;fun_prop)
  have hV : Integrable (fun ω => (q ω-m)^2) ν :=
    integrable_comp hq hqr (F := fun x => (x-m)^2) (by fun_prop)
  have h := integral_mono_ae hD (hV.const_mul (4*biasCoefficient m))
    (hqr.mono fun ω hω => binaryDivergenceNats_le_biasCoefficient hω.1 hω.2 hm0 hm1)
  rw [integral_binaryDivergenceNats hq hqr,integral_const_mul] at h
  rw [quadraticGap_eq_variance hq hqr]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ log_two_pos).mpr
  dsimp [m] at h ⊢
  nlinarith

/-- Actual Shannon information associated with a conditioning sigma-algebra. -/
def conditionalShannonInformation (ν : Measure Ω) (m : MeasurableSpace Ω) (f : Ω → ℝ) : ℝ :=
  entropyBits (∫ ω,f ω ∂ν)-(∫ ω,entropyBits ((ν[f|m]) ω) ∂ν)

/-- Actual quadratic information associated with a conditioning sigma-algebra. -/
def conditionalQuadraticInformation (ν : Measure Ω) (m : MeasurableSpace Ω) (f : Ω → ℝ) : ℝ :=
  quadraticEntropy (∫ ω,f ω ∂ν)-(∫ ω,quadraticEntropy ((ν[f|m]) ω) ∂ν)

/-- The posterior's range, measurability and tower identity are consequences of conditional expectation. -/
theorem conditional_posterior {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1) :
    AEStronglyMeasurable[m₀] (ν[f|m]) ν ∧
    (∀ᵐ ω ∂ν,(ν[f|m]) ω ∈ Icc (0:ℝ) 1) ∧
    (∫ ω,(ν[f|m]) ω ∂ν)=(∫ ω,f ω ∂ν) := by
  letI : MeasurableSpace Ω := m₀
  have hce : AEStronglyMeasurable[m₀] (ν[f|m]) ν :=
    (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
  have hl : ∀ᵐ ω ∂ν,0 ≤ (ν[f|m]) ω := condExp_nonneg (hfr.mono fun _ h => h.1)
  have hu := condExp_mono (m := m) (integrable_posterior hf hfr) (integrable_const (1:ℝ))
    (hfr.mono fun _ h => h.2)
  rw [condExp_const hm (1:ℝ)] at hu
  refine ⟨hce,?_,integral_condExp hm⟩
  filter_upwards [hl,hu] with ω hω0 hω1
  exact ⟨hω0,hω1⟩

/-- Nested conditioning has the actual almost-everywhere tower property. -/
theorem posterior_tower {m₁ m₂ : MeasurableSpace Ω} (hm₁₂ : m₁ ≤ m₂)
    (hm₂ : m₂ ≤ m₀) (f : Ω → ℝ) :
    ν[ν[f|m₂]|m₁] =ᵐ[ν] ν[f|m₁] := condExp_condExp_of_le hm₁₂ hm₂

private theorem conditionalInformation_eq_gap {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1) :
    conditionalShannonInformation (m₀ := m₀) ν m f=shannonGap (m₀ := m₀) ν (ν[f|m]) ∧
    conditionalQuadraticInformation (m₀ := m₀) ν m f=quadraticGap (m₀ := m₀) ν (ν[f|m]) := by
  letI : MeasurableSpace Ω := m₀
  have ht := (conditional_posterior hm hf hfr).2.2
  simp only [conditionalShannonInformation,conditionalQuadraticInformation,shannonGap,quadraticGap,ht,
    and_self]

/-- The conditional entropy sandwich for an arbitrary conditioning sigma-algebra. -/
theorem conditional_entropy_sandwich {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1) :
    (∫ ω,quadraticEntropy ((ν[f|m]) ω) ∂ν) ≤ (∫ ω,entropyBits ((ν[f|m]) ω) ∂ν) ∧
    (∫ ω,entropyBits ((ν[f|m]) ω) ∂ν) ≤
      (1+(∫ ω,quadraticEntropy ((ν[f|m]) ω) ∂ν))/2 := by
  letI : MeasurableSpace Ω := m₀
  have hp := conditional_posterior hm hf hfr
  exact entropy_sandwich hp.1 hp.2.1

/-- Nonnegativity and Pinsker for arbitrary observations, with posterior assumptions discharged. -/
theorem conditional_information_bounds {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1) :
    0 ≤ conditionalShannonInformation (m₀ := m₀) ν m f ∧
    0 ≤ conditionalQuadraticInformation (m₀ := m₀) ν m f ∧
    conditionalQuadraticInformation (m₀ := m₀) ν m f ≤
      2*Real.log 2*conditionalShannonInformation (m₀ := m₀) ν m f := by
  letI : MeasurableSpace Ω := m₀
  have hp := conditional_posterior hm hf hfr
  have he := conditionalInformation_eq_gap hm hf hfr
  rw [he.1,he.2]
  exact ⟨shannonGap_nonneg hp.1 hp.2.1,quadraticGap_nonneg hp.1 hp.2.1,
    quadraticGap_le_shannonGap hp.1 hp.2.1⟩

/-- Unbiased reverse comparison for a genuine conditional expectation. -/
theorem conditional_information_unbiased {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1) (hmean : (∫ ω,f ω ∂ν)=1/2) :
    conditionalShannonInformation (m₀ := m₀) ν m f ≤ conditionalQuadraticInformation (m₀ := m₀) ν m f := by
  letI : MeasurableSpace Ω := m₀
  have hp := conditional_posterior hm hf hfr
  have he := conditionalInformation_eq_gap hm hf hfr
  rw [he.1,he.2]
  exact shannonGap_le_quadraticGap_of_unbiased hp.1 hp.2.1 (hp.2.2.trans hmean)

/-- Sharp bias-dependent comparison for arbitrary observations. -/
theorem conditional_information_bias_bound {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1)
    (hm0 : 0 < ∫ ω,f ω ∂ν) (hm1 : (∫ ω,f ω ∂ν) < 1) :
    conditionalShannonInformation (m₀ := m₀) ν m f ≤
      biasCoefficient (∫ ω,f ω ∂ν)/Real.log 2*conditionalQuadraticInformation (m₀ := m₀) ν m f := by
  letI : MeasurableSpace Ω := m₀
  have hp := conditional_posterior hm hf hfr
  have he := conditionalInformation_eq_gap hm hf hfr
  rw [he.1,he.2]
  have h := shannonGap_le_biasCoefficient hp.1 hp.2.1 (by rwa [hp.2.2]) (by rwa [hp.2.2])
  simpa only [hp.2.2] using h

/-- Observation form: the observed variable may take values in any measurable space. -/
theorem observation_information_bounds {Z : Type*} [MeasurableSpace Z]
    {Y : Ω → Z} (hY : Measurable Y) {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1) :
    0 ≤ conditionalShannonInformation (m₀ := m₀) ν (MeasurableSpace.comap Y inferInstance) f ∧
    0 ≤ conditionalQuadraticInformation (m₀ := m₀) ν (MeasurableSpace.comap Y inferInstance) f ∧
    conditionalQuadraticInformation (m₀ := m₀) ν (MeasurableSpace.comap Y inferInstance) f ≤
      2*Real.log 2*conditionalShannonInformation (m₀ := m₀) ν (MeasurableSpace.comap Y inferInstance) f :=
  conditional_information_bounds hY.comap_le hf hfr

end Posterior
end CourtadeKumar
