import CK.PosteriorMeasure
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.ConditionalExpectation

/-!
# Chain rules and conditioning for arbitrary measurable observations

Conditional entropy is defined from the actual conditional expectation. Jensen
under a sub-sigma-algebra is proved by disintegrating the real posterior; the
conditioning space itself is arbitrary. No finite-support hypothesis is used.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
noncomputable section
namespace CourtadeKumar.Posterior
open Set MeasureTheory Filter ProbabilityTheory

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- An actual conditional distribution of a bounded posterior remains in its
range, for almost every conditioning value. -/
theorem condDistrib_posterior_range {Z : Type*} [mZ : MeasurableSpace Z]
    {u : Ω → Z} (hu : Measurable u) {q : Ω → ℝ} (hq : Measurable q)
    (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1) :
    ∀ᵐ ω ∂ν, ∀ᵐ x ∂condDistrib q u ν (u ω), x ∈ Icc (0:ℝ) 1 := by
  have he := condDistrib_ae_eq_condExp (μ := ν) (s := Icc (0:ℝ) 1) hu hq measurableSet_Icc
  have hi : (q ⁻¹' Icc (0:ℝ) 1).indicator (fun _ : Ω => (1:ℝ)) =ᵐ[ν]
      fun _ => 1 := by
    filter_upwards [hqr] with ω hω
    change (q ⁻¹' Icc (0:ℝ) 1).indicator (fun _ : Ω => (1:ℝ)) ω=1
    rw [Set.indicator_of_mem (show ω ∈ q ⁻¹' Icc (0:ℝ) 1 from hω)]
  have he' := he.trans (condExp_congr_ae (m := mZ.comap u) hi)
  rw [condExp_const hu.comap_le (1:ℝ)] at he'
  filter_upwards [he'] with ω hω
  apply (mem_ae_iff_prob_eq_one measurableSet_Icc).2
  apply (ENNReal.toReal_eq_toReal (measure_ne_top _ _) ENNReal.one_ne_top).1
  simpa only [measureReal_def,ENNReal.toReal_one] using hω

/-- Conditional Jensen on `[0,1]`, proved using a regular conditional law of
the real posterior. The observation type need not be standard Borel. -/
theorem conditional_jensen_concave_observation {Z : Type*} [mZ : MeasurableSpace Z]
    {u : Ω → Z} (hu : Measurable u) {q : Ω → ℝ} (hq : Measurable q)
    (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1) {F : ℝ → ℝ}
    (hF : Continuous F) (hFc : ConcaveOn ℝ (Icc (0:ℝ) 1) F) :
    ν[fun ω => F (q ω)|mZ.comap u] ≤ᵐ[ν]
      fun ω => F ((ν[q|mZ.comap u]) ω) := by
  have hqi := integrable_posterior hq.aestronglyMeasurable hqr
  have hFi := integrable_comp hq.aestronglyMeasurable hqr hF
  have hqce := condExp_ae_eq_integral_condDistrib' hu hqi
  have hFce := condExp_ae_eq_integral_condDistrib hu hq.aemeasurable hF.stronglyMeasurable hFi
  have hr := condDistrib_posterior_range hu hq hqr
  filter_upwards [hr,hqce,hFce] with ω hω hqω hFω
  rw [hqω,hFω]
  exact hFc.le_map_integral hF.continuousOn isClosed_Icc hω
    (integrable_posterior measurable_id.aestronglyMeasurable hω)
    (integrable_comp measurable_id.aestronglyMeasurable hω hF)

/-- Conditional Jensen for any sub-sigma-algebra of the original space. -/
theorem conditional_jensen_concave {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {q : Ω → ℝ} (hq : Measurable[m₀] q) (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1)
    {F : ℝ → ℝ} (hF : Continuous F) (hFc : ConcaveOn ℝ (Icc (0:ℝ) 1) F) :
    ν[fun ω => F (q ω)|m] ≤ᵐ[ν] fun ω => F ((ν[q|m]) ω) := by
  letI : MeasurableSpace Ω := m₀
  have hid : @Measurable Ω Ω m₀ m id := hm
  simpa only [MeasurableSpace.comap_id] using
    (conditional_jensen_concave_observation (mZ := m) hid hq hqr hF hFc)

/-- Integrated conditional Jensen, with integrability proved from the compact
posterior range. -/
theorem integral_concave_condExp_ge {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {q : Ω → ℝ} (hq : Measurable[m₀] q) (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1)
    {F : ℝ → ℝ} (hF : Continuous F) (hFc : ConcaveOn ℝ (Icc (0:ℝ) 1) F) :
    (∫ ω,F (q ω) ∂ν) ≤ (∫ ω,F ((ν[q|m]) ω) ∂ν) := by
  letI : MeasurableSpace Ω := m₀
  have hp := conditional_posterior hm hq.aestronglyMeasurable hqr
  have h := integral_mono_ae integrable_condExp (integrable_comp hp.1 hp.2.1 hF)
    (conditional_jensen_concave hm hq hqr hF hFc)
  rwa [integral_condExp hm] at h

/-- More observation decreases every continuous concave posterior functional. -/
theorem integral_concave_posterior_antitone {m₁ m₂ : MeasurableSpace Ω}
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1)
    {F : ℝ → ℝ} (hF : Continuous F) (hFc : ConcaveOn ℝ (Icc (0:ℝ) 1) F) :
    (∫ ω,F ((ν[f|m₂]) ω) ∂ν) ≤ (∫ ω,F ((ν[f|m₁]) ω) ∂ν) := by
  letI : MeasurableSpace Ω := m₀
  have hp := conditional_posterior hm₂ hf hfr
  have h := integral_concave_condExp_ge (hm₁₂.trans hm₂)
    (stronglyMeasurable_condExp.mono hm₂).measurable hp.2.1 hF hFc
  have he := integral_congr_ae ((posterior_tower (ν := ν) hm₁₂ hm₂ f).fun_comp F)
  exact h.trans_eq he

/-- Conditional Shannon entropy given an arbitrary sigma-algebra. -/
def shannonEntropyGiven (ν : Measure Ω) (m : MeasurableSpace Ω) (f : Ω → ℝ) : ℝ :=
  ∫ ω,entropyBits ((ν[f|m]) ω) ∂ν

/-- Conditional quadratic entropy given an arbitrary sigma-algebra. -/
def quadraticEntropyGiven (ν : Measure Ω) (m : MeasurableSpace Ω) (f : Ω → ℝ) : ℝ :=
  ∫ ω,quadraticEntropy ((ν[f|m]) ω) ∂ν

/-- Information acquired from `n`, after observing `m`. -/
def shannonInformationGiven (ν : Measure Ω) (m n : MeasurableSpace Ω) (f : Ω → ℝ) : ℝ :=
  shannonEntropyGiven (m₀ := m₀) ν m f-shannonEntropyGiven (m₀ := m₀) ν (m ⊔ n) f

/-- Quadratic information acquired from `n`, after observing `m`. -/
def quadraticInformationGiven (ν : Measure Ω) (m n : MeasurableSpace Ω) (f : Ω → ℝ) : ℝ :=
  quadraticEntropyGiven (m₀ := m₀) ν m f-quadraticEntropyGiven (m₀ := m₀) ν (m ⊔ n) f

omit [IsProbabilityMeasure ν] in
/-- The Shannon chain rule uses the actual joined observation sigma-algebra. -/
theorem shannon_chain (m n : MeasurableSpace Ω) (f : Ω → ℝ) :
    conditionalShannonInformation (m₀ := m₀) ν (m ⊔ n) f=
      conditionalShannonInformation (m₀ := m₀) ν m f+
        shannonInformationGiven (m₀ := m₀) ν m n f := by
  unfold conditionalShannonInformation shannonInformationGiven shannonEntropyGiven
  ring

omit [IsProbabilityMeasure ν] in
/-- The quadratic chain rule holds for arbitrary measurable observations. -/
theorem quadratic_chain (m n : MeasurableSpace Ω) (f : Ω → ℝ) :
    conditionalQuadraticInformation (m₀ := m₀) ν (m ⊔ n) f=
      conditionalQuadraticInformation (m₀ := m₀) ν m f+
        quadraticInformationGiven (m₀ := m₀) ν m n f := by
  unfold conditionalQuadraticInformation quadraticInformationGiven quadraticEntropyGiven
  ring

omit [IsProbabilityMeasure ν] in
theorem conditional_shannon_chain (m n k : MeasurableSpace Ω) (f : Ω → ℝ) :
    shannonInformationGiven (m₀ := m₀) ν m (n ⊔ k) f=
      shannonInformationGiven (m₀ := m₀) ν m n f+
        shannonInformationGiven (m₀ := m₀) ν (m ⊔ n) k f := by
  unfold shannonInformationGiven
  rw [sup_assoc]
  ring

omit [IsProbabilityMeasure ν] in
theorem conditional_quadratic_chain (m n k : MeasurableSpace Ω) (f : Ω → ℝ) :
    quadraticInformationGiven (m₀ := m₀) ν m (n ⊔ k) f=
      quadraticInformationGiven (m₀ := m₀) ν m n f+
        quadraticInformationGiven (m₀ := m₀) ν (m ⊔ n) k f := by
  unfold quadraticInformationGiven
  rw [sup_assoc]
  ring

private theorem continuous_entropyBits : Continuous entropyBits := by unfold entropyBits;fun_prop
private theorem continuous_quadraticEntropy : Continuous quadraticEntropy := by
  unfold quadraticEntropy
  fun_prop

/-- Shannon information is monotone under refinement of the observed sigma-algebra. -/
theorem shannonInformation_mono {m₁ m₂ : MeasurableSpace Ω}
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1) :
    conditionalShannonInformation (m₀ := m₀) ν m₁ f ≤
      conditionalShannonInformation (m₀ := m₀) ν m₂ f := by
  letI : MeasurableSpace Ω := m₀
  have h := integral_concave_posterior_antitone hm₁₂ hm₂ hf hfr
    Real.binEntropy_continuous Real.strictConcave_binEntropy.concaveOn
  unfold conditionalShannonInformation entropyBits
  rw [integral_div,integral_div]
  exact sub_le_sub_left (div_le_div_of_nonneg_right h log_two_pos.le) _

private theorem integral_quadraticEntropy {q : Ω → ℝ}
    (hq : AEStronglyMeasurable q ν) (hqr : ∀ᵐ ω ∂ν,q ω ∈ Icc (0:ℝ) 1) :
    (∫ ω,quadraticEntropy (q ω) ∂ν)=4*(∫ ω,q ω ∂ν)-4*(∫ ω,(q ω)^2 ∂ν) := by
  have hi := integrable_posterior hq hqr
  have hsq := integrable_comp hq hqr (continuous_pow 2)
  have heq : (fun ω => quadraticEntropy (q ω))=(fun ω => 4*q ω-4*(q ω)^2) := by
    funext ω
    unfold quadraticEntropy
    ring
  rw [heq,integral_sub (hi.const_mul 4) (hsq.const_mul 4),integral_const_mul,integral_const_mul]

/-- Orthogonality of a posterior refinement to its coarser posterior, proved
from the actual conditional-expectation pull-out and tower laws. -/
theorem posterior_cross_moment {m₁ m₂ : MeasurableSpace Ω}
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1) :
    (∫ ω,(ν[f|m₁]) ω*(ν[f|m₂]) ω ∂ν)=(∫ ω,((ν[f|m₁]) ω)^2 ∂ν) := by
  letI : MeasurableSpace Ω := m₀
  have hp₁ := conditional_posterior (hm₁₂.trans hm₂) hf hfr
  have hbound : ∀ᵐ ω ∂ν, ‖(ν[f|m₁]) ω‖ ≤ (1:ℝ) := hp₁.2.1.mono fun ω hω => by
    rw [Real.norm_eq_abs,abs_of_nonneg hω.1]
    exact hω.2
  have he := condExp_stronglyMeasurable_mul_of_bound (hm₁₂.trans hm₂)
    (f := ν[f|m₁]) (g := ν[f|m₂]) stronglyMeasurable_condExp integrable_condExp 1 hbound
  have ht := posterior_tower (ν := ν) hm₁₂ hm₂ f
  calc
    (∫ ω,(ν[f|m₁]) ω*(ν[f|m₂]) ω ∂ν) =
        ∫ ω,(ν[(ν[f|m₁])*(ν[f|m₂])|m₁]) ω ∂ν := (integral_condExp (hm₁₂.trans hm₂)).symm
    _ = ∫ ω,((ν[f|m₁]) ω)^2 ∂ν := by
      apply integral_congr_ae
      filter_upwards [he,ht] with ω hω hωt
      simpa only [Pi.mul_apply,hωt,pow_two] using hω

/-- The gain from a finer observation is exactly four times the squared
posterior update, including all zero-probability and endpoint cases. -/
theorem quadraticInformation_difference {m₁ m₂ : MeasurableSpace Ω}
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1) :
    conditionalQuadraticInformation (m₀ := m₀) ν m₂ f-
        conditionalQuadraticInformation (m₀ := m₀) ν m₁ f=
      4*(∫ ω,((ν[f|m₂]) ω-(ν[f|m₁]) ω)^2 ∂ν) := by
  letI : MeasurableSpace Ω := m₀
  have hp₁ := conditional_posterior (hm₁₂.trans hm₂) hf hfr
  have hp₂ := conditional_posterior hm₂ hf hfr
  have hs₁ := integrable_comp hp₁.1 hp₁.2.1 (continuous_pow 2)
  have hs₂ := integrable_comp hp₂.1 hp₂.2.1 (continuous_pow 2)
  have hbound : ∀ᵐ ω ∂ν, ‖(ν[f|m₁]) ω‖ ≤ (1:ℝ) := hp₁.2.1.mono fun ω hω => by
    rw [Real.norm_eq_abs,abs_of_nonneg hω.1]
    exact hω.2
  have hmul : Integrable (fun ω => (ν[f|m₁]) ω*(ν[f|m₂]) ω) ν :=
    integrable_condExp.bdd_mul' hp₁.1 hbound
  have hex : (fun ω => ((ν[f|m₂]) ω-(ν[f|m₁]) ω)^2)=
      (fun ω => ((ν[f|m₂]) ω)^2-2*((ν[f|m₁]) ω*(ν[f|m₂]) ω)+((ν[f|m₁]) ω)^2) := by
    funext ω
    ring
  unfold conditionalQuadraticInformation
  rw [integral_quadraticEntropy hp₁.1 hp₁.2.1,integral_quadraticEntropy hp₂.1 hp₂.2.1,
    hp₁.2.2,hp₂.2.2,hex,
    integral_add (f := fun ω => ((ν[f|m₂]) ω)^2-2*((ν[f|m₁]) ω*(ν[f|m₂]) ω))
      (g := fun ω => ((ν[f|m₁]) ω)^2) (hs₂.sub (hmul.const_mul 2)) hs₁,
    integral_sub (f := fun ω => ((ν[f|m₂]) ω)^2)
      (g := fun ω => 2*((ν[f|m₁]) ω*(ν[f|m₂]) ω)) hs₂ (hmul.const_mul 2),integral_const_mul,
    posterior_cross_moment hm₁₂ hm₂ hf hfr]
  ring

theorem quadraticInformation_mono {m₁ m₂ : MeasurableSpace Ω}
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1) :
    conditionalQuadraticInformation (m₀ := m₀) ν m₁ f ≤
      conditionalQuadraticInformation (m₀ := m₀) ν m₂ f := by
  letI : MeasurableSpace Ω := m₀
  have h := quadraticInformation_difference hm₁₂ hm₂ hf hfr
  have hn : 0 ≤ 4*(∫ ω,((ν[f|m₂]) ω-(ν[f|m₁]) ω)^2 ∂ν) :=
    mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)
  linarith

/-- Pinsker's comparison also holds for the information added after an arbitrary
existing observation. Both conditional expectations are the actual ones. -/
theorem conditional_pinsker {m₁ m₂ : MeasurableSpace Ω}
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1) :
    conditionalQuadraticInformation (m₀ := m₀) ν m₂ f-
        conditionalQuadraticInformation (m₀ := m₀) ν m₁ f ≤
      2*Real.log 2*(conditionalShannonInformation (m₀ := m₀) ν m₂ f-
        conditionalShannonInformation (m₀ := m₀) ν m₁ f) := by
  letI : MeasurableSpace Ω := m₀
  have hp₁ := conditional_posterior (hm₁₂.trans hm₂) hf hfr
  have hp₂ := conditional_posterior hm₂ hf hfr
  have hH₁ := integrable_comp hp₁.1 hp₁.2.1 Real.binEntropy_continuous
  have hH₂ := integrable_comp hp₂.1 hp₂.2.1 Real.binEntropy_continuous
  have hs₁ := integrable_comp hp₁.1 hp₁.2.1 (continuous_pow 2)
  have hs₂ := integrable_comp hp₂.1 hp₂.2.1 (continuous_pow 2)
  have h := integral_concave_posterior_antitone hm₁₂ hm₂ hf hfr
    (F := entropyCurvatureCorrection) (by unfold entropyCurvatureCorrection;fun_prop)
    entropyCurvatureCorrection_concave
  unfold entropyCurvatureCorrection at h
  rw [integral_add hH₁ (hs₁.const_mul 2),integral_add hH₂ (hs₂.const_mul 2),
    integral_const_mul,integral_const_mul] at h
  unfold conditionalQuadraticInformation conditionalShannonInformation
  rw [integral_quadraticEntropy hp₁.1 hp₁.2.1,integral_quadraticEntropy hp₂.1 hp₂.2.1,
    hp₁.2.2,hp₂.2.2]
  unfold entropyBits
  rw [integral_div,integral_div]
  have hL : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  have he : 2*Real.log 2*((Real.binEntropy (∫ ω,f ω ∂ν)/Real.log 2-
      (∫ ω,Real.binEntropy ((ν[f|m₂]) ω) ∂ν)/Real.log 2)-
      (Real.binEntropy (∫ ω,f ω ∂ν)/Real.log 2-
      (∫ ω,Real.binEntropy ((ν[f|m₁]) ω) ∂ν)/Real.log 2))=
      2*((∫ ω,Real.binEntropy ((ν[f|m₁]) ω) ∂ν)-
        (∫ ω,Real.binEntropy ((ν[f|m₂]) ω) ∂ν)) := by field_simp;ring
  rw [he]
  linarith

/-- Conditional Shannon and quadratic information are nonnegative and satisfy
the manuscript's conditional Pinsker comparison, for arbitrary observation fields. -/
theorem informationGiven_bounds {m n : MeasurableSpace Ω} (hm : m ≤ m₀) (hn : n ≤ m₀)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f ν)
    (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1) :
    0 ≤ shannonInformationGiven (m₀ := m₀) ν m n f ∧
    0 ≤ quadraticInformationGiven (m₀ := m₀) ν m n f ∧
    quadraticInformationGiven (m₀ := m₀) ν m n f ≤
      2*Real.log 2*shannonInformationGiven (m₀ := m₀) ν m n f := by
  letI : MeasurableSpace Ω := m₀
  have hS := shannonInformation_mono le_sup_left (sup_le hm hn) hf hfr
  have hQ := quadraticInformation_mono le_sup_left (sup_le hm hn) hf hfr
  have hP := conditional_pinsker le_sup_left (sup_le hm hn) hf hfr
  rw [shannon_chain m n f] at hS hP
  rw [quadratic_chain m n f] at hQ hP
  exact ⟨by linarith,by linarith,by simpa only [add_sub_cancel_left] using hP⟩

/-- Exact conditional quadratic-information identity for arbitrary observations. -/
theorem quadraticInformationGiven_eq_update {m n : MeasurableSpace Ω}
    (hm : m ≤ m₀) (hn : n ≤ m₀) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable[m₀] f ν) (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1) :
    quadraticInformationGiven (m₀ := m₀) ν m n f=
      4*(∫ ω,((ν[f|m ⊔ n]) ω-(ν[f|m]) ω)^2 ∂ν) := by
  letI : MeasurableSpace Ω := m₀
  have h := quadraticInformation_difference le_sup_left (sup_le hm hn) hf hfr
  rw [quadratic_chain m n f] at h
  simpa only [add_sub_cancel_left] using h

/-- Conditional quadratic information is at most the remaining conditional entropy. -/
theorem quadraticInformationGiven_le_entropy {m n : MeasurableSpace Ω}
    (hm : m ≤ m₀) (hn : n ≤ m₀) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable[m₀] f ν) (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1) :
    quadraticInformationGiven (m₀ := m₀) ν m n f ≤
      quadraticEntropyGiven (m₀ := m₀) ν m f := by
  letI : MeasurableSpace Ω := m₀
  have hp := conditional_posterior (sup_le hm hn) hf hfr
  have h : 0 ≤ ∫ ω,quadraticEntropy ((ν[f|m ⊔ n]) ω) ∂ν :=
    integral_nonneg_of_ae (hp.2.1.mono fun ω hω => quadraticEntropy_nonneg hω.1 hω.2)
  unfold quadraticInformationGiven quadraticEntropyGiven
  linarith

/-- The unbiased reverse comparison remains valid conditionally whenever the
binary input is unbiased after the original observation. -/
theorem informationGiven_unbiased {m n : MeasurableSpace Ω}
    (hm : m ≤ m₀) (hn : n ≤ m₀) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable[m₀] f ν) (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1)
    (hbase : ν[f|m] =ᵐ[ν] fun _ => (1:ℝ)/2) :
    shannonInformationGiven (m₀ := m₀) ν m n f ≤
      quadraticInformationGiven (m₀ := m₀) ν m n f := by
  letI : MeasurableSpace Ω := m₀
  have hp := conditional_posterior (sup_le hm hn) hf hfr
  have hH : (∫ ω,entropyBits ((ν[f|m]) ω) ∂ν)=1 := by
    calc
      (∫ ω,entropyBits ((ν[f|m]) ω) ∂ν)=(∫ _ : Ω,entropyBits (1/2) ∂ν) :=
        integral_congr_ae (hbase.fun_comp entropyBits)
      _=1 := by rw [entropyBits_half];simp
  have hT : (∫ ω,quadraticEntropy ((ν[f|m]) ω) ∂ν)=1 := by
    calc
      (∫ ω,quadraticEntropy ((ν[f|m]) ω) ∂ν)=(∫ _ : Ω,quadraticEntropy (1/2) ∂ν) :=
        integral_congr_ae (hbase.fun_comp quadraticEntropy)
      _=1 := by norm_num [quadraticEntropy]
  have h := (entropy_sandwich hp.1 hp.2.1).1
  unfold shannonInformationGiven quadraticInformationGiven shannonEntropyGiven quadraticEntropyGiven
  rw [hH,hT]
  linarith

end CourtadeKumar.Posterior
