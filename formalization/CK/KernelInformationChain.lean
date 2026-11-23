import CK.KernelConditioning
import CK.ComparisonMeasure

/-! # Shannon conditioning gain for arbitrary observation laws -/

noncomputable section
namespace CourtadeKumar.KernelInformation
open Set MeasureTheory Filter
open scoped BigOperators

variable {U : Type*} [MeasurableSpace U] {ν : Measure U} [IsProbabilityMeasure ν]

private theorem entropy_gap_convex :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun x => quadraticEntropy x - 2 * Real.log 2 * entropyBits x) := by
  have he (x : ℝ) : quadraticEntropy x - 2 * Real.log 2 * entropyBits x =
      4 * x - 2 * entropyCurvatureCorrection x := by
    unfold quadraticEntropy entropyBits entropyCurvatureCorrection
    field_simp [ne_of_gt log_two_pos]
    ring
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := entropyCurvatureCorrection_concave.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  simp only [he]
  nlinarith only [h]

/-- Strong entropy concavity with an arbitrary nonnegative measurable weight. -/
theorem weighted_entropy_gap_comparison {w r : U → ℝ}
    (hw : Measurable w) (hr : Measurable r)
    (hwr : ∀ u, w u ∈ Icc (0 : ℝ) 1)
    (hrr : ∀ u, 0 ≤ r u ∧ r u ≤ w u) :
    (∫ u, w u ∂ν) * quadraticEntropy ((∫ u, r u ∂ν) / (∫ u, w u ∂ν)) -
      (∫ u, w u * quadraticEntropy (r u / w u) ∂ν) ≤
    2 * Real.log 2 * ((∫ u, w u ∂ν) * entropyBits ((∫ u, r u ∂ν) / (∫ u, w u ∂ν)) -
      (∫ u, w u * entropyBits (r u / w u) ∂ν)) := by
  have hwi := FiniteKernel.integrable_bounded ν hw (fun u => (hwr u).1) (fun u => (hwr u).2)
  have hqr : ∀ u, r u / w u ∈ Icc (0 : ℝ) 1 := by
    intro u
    constructor
    · exact div_nonneg (hrr u).1 (hwr u).1
    · by_cases hz : w u = 0
      · simp [hz]
      · exact (div_le_one (lt_of_le_of_ne (hwr u).1 (Ne.symm hz))).mpr (hrr u).2
  have hQm : Measurable (fun u => quadraticEntropy (r u / w u)) := by
    have hc : Continuous quadraticEntropy := by unfold quadraticEntropy; fun_prop
    exact hc.measurable.comp (hr.div hw)
  have hHm : Measurable (fun u => entropyBits (r u / w u)) := by
    have hc : Continuous entropyBits := by unfold entropyBits; fun_prop
    exact hc.measurable.comp (hr.div hw)
  have hQi : Integrable (fun u => w u * quadraticEntropy (r u / w u)) ν := by
    apply FiniteKernel.integrable_bounded ν (hw.mul hQm)
    · intro u
      exact mul_nonneg (hwr u).1 (quadraticEntropy_nonneg (hqr u).1 (hqr u).2)
    · intro u
      exact mul_le_one₀ (hwr u).2 (quadraticEntropy_nonneg (hqr u).1 (hqr u).2)
        (quadraticEntropy_le_one _)
  have hHi : Integrable (fun u => w u * entropyBits (r u / w u)) ν := by
    apply FiniteKernel.integrable_bounded ν (hw.mul hHm)
    · intro u
      exact mul_nonneg (hwr u).1 (entropyBits_nonneg (hqr u).1 (hqr u).2)
    · intro u
      exact mul_le_one₀ (hwr u).2 (entropyBits_nonneg (hqr u).1 (hqr u).2)
        (entropyBits_le_one _)
  by_cases hz : (∫ u, w u ∂ν) = 0
  · have hzero := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun u => (hwr u).1) hwi).mp hz
    have hQ : (∫ u, w u * quadraticEntropy (r u / w u) ∂ν) = 0 := by
      calc
        _ = ∫ u, (0 : ℝ) ∂ν := integral_congr_ae (hzero.mono fun u hu => by simp [hu])
        _ = 0 := by simp
    have hH : (∫ u, w u * entropyBits (r u / w u) ∂ν) = 0 := by
      calc
        _ = ∫ u, (0 : ℝ) ∂ν := integral_congr_ae (hzero.mono fun u hu => by simp [hu])
        _ = 0 := by simp
    simp [hz, hQ, hH]
  · have hpos : 0 < ∫ u, w u ∂ν := lt_of_le_of_ne
      (integral_nonneg fun u => (hwr u).1) (Ne.symm hz)
    have hc : Continuous (fun x => quadraticEntropy x - 2 * Real.log 2 * entropyBits x) := by
      unfold quadraticEntropy entropyBits
      fun_prop
    have h := MeasureComparison.weighted_convex_jensen_unit hw.aestronglyMeasurable
      hr.aestronglyMeasurable (ae_of_all _ hwr) (ae_of_all _ hrr) hpos hc entropy_gap_convex
    have he : (fun u => w u * (quadraticEntropy (r u / w u) - 2 * Real.log 2 * entropyBits (r u / w u))) =
        (fun u => w u * quadraticEntropy (r u / w u) - 2 * Real.log 2 * (w u * entropyBits (r u / w u))) := by
      funext u
      ring
    rw [he, integral_sub (f := fun u => w u * quadraticEntropy (r u / w u))
      (g := fun u => 2 * Real.log 2 * (w u * entropyBits (r u / w u)))
      hQi (hHi.const_mul _), integral_const_mul] at h
    nlinarith only [h]

namespace FiniteKernel
variable {Γ Z : Type*} [Fintype Γ] [Fintype Z] [DecidableEq Z]

/-- Continuous functionals of posterior means, with their actual fibre weights, are integrable. -/
theorem integrable_fibre_comp (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (z : Γ → Z) (c : Γ → ℝ) (hc0 : ∀ a, 0 ≤ c a) (hc1 : ∀ a, c a ≤ 1)
    (s : Z) {F : ℝ → ℝ} (hF : Continuous F) :
    Integrable (fun u => (K.law u).fibreMass z s * F ((K.law u).conditionalMean z c s)) ν := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hF.continuousOn
  apply (integrable_const C).mono'
    ((K.measurable_fibreMass z s).mul
      (hF.measurable.comp (K.measurable_conditionalMean z c s))).aestronglyMeasurable
  apply ae_of_all
  intro u
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ((K.law u).fibreMass_nonneg z s)]
  calc
    _ ≤ 1 * ‖F ((K.law u).conditionalMean z c s)‖ :=
      mul_le_mul_of_nonneg_right (mass_le_one ((K.law u).map z) s) (norm_nonneg _)
    _ ≤ C := by
      simpa only [one_mul] using (hC _
        ⟨(K.law u).conditionalMean_nonneg z hc0 s, (K.law u).conditionalMean_le_one z hc1 s⟩)

theorem integrable_conditionalShannonEntropy (K : FiniteKernel U Γ) (ν : Measure U)
    [IsProbabilityMeasure ν] (z : Γ → Z) (c : Γ → ℝ)
    (hc0 : ∀ a, 0 ≤ c a) (hc1 : ∀ a, c a ≤ 1) :
    Integrable (fun u => (K.law u).conditionalShannonEntropy z c) ν := by
  unfold FiniteLaw.conditionalShannonEntropy FiniteLaw.expect FiniteLaw.map
  apply integrable_finset_sum
  intro s _
  exact K.integrable_fibre_comp ν z c hc0 hc1 s (by unfold entropyBits; fun_prop)

theorem integrable_conditionalQuadraticEntropy (K : FiniteKernel U Γ) (ν : Measure U)
    [IsProbabilityMeasure ν] (z : Γ → Z) (c : Γ → ℝ)
    (hc0 : ∀ a, 0 ≤ c a) (hc1 : ∀ a, c a ≤ 1) :
    Integrable (fun u => (K.law u).conditionalQuadraticEntropy z c) ν := by
  unfold FiniteLaw.conditionalQuadraticEntropy FiniteLaw.expect FiniteLaw.map
  apply integrable_finset_sum
  intro s _
  exact K.integrable_fibre_comp ν z c hc0 hc1 s (by unfold quadraticEntropy; fun_prop)

/-- The exact posterior mixture comparison on each finite observed fibre. -/
theorem fibre_mixture_gap_comparison (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (z : Γ → Z) (c : Γ → ℝ) (hc0 : ∀ a, 0 ≤ c a) (hc1 : ∀ a, c a ≤ 1) (s : Z) :
    (K.mixture ν).fibreMass z s * quadraticEntropy ((K.mixture ν).conditionalMean z c s) -
      (∫ u, (K.law u).fibreMass z s * quadraticEntropy ((K.law u).conditionalMean z c s) ∂ν) ≤
    2 * Real.log 2 * ((K.mixture ν).fibreMass z s * entropyBits ((K.mixture ν).conditionalMean z c s) -
      (∫ u, (K.law u).fibreMass z s * entropyBits ((K.law u).conditionalMean z c s) ∂ν)) := by
  unfold FiniteLaw.conditionalMean
  rw [K.fibreMass_mixture, K.fibreMoment_mixture]
  exact weighted_entropy_gap_comparison (K.measurable_fibreMass z s) (K.measurable_fibreMoment z c s)
    (fun u => ⟨(K.law u).fibreMass_nonneg z s, mass_le_one ((K.law u).map z) s⟩)
    (fun u => ⟨(K.law u).fibreMoment_nonneg z hc0 s, (K.law u).fibreMoment_le_mass z hc1 s⟩)

/-- Strong entropy concavity after summing all finite observed fibres. -/
theorem conditional_mixture_gap_comparison (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (z : Γ → Z) (c : Γ → ℝ) (hc0 : ∀ a, 0 ≤ c a) (hc1 : ∀ a, c a ≤ 1) :
    (K.mixture ν).conditionalQuadraticEntropy z c -
        (∫ u, (K.law u).conditionalQuadraticEntropy z c ∂ν) ≤
      2 * Real.log 2 * ((K.mixture ν).conditionalShannonEntropy z c -
        (∫ u, (K.law u).conditionalShannonEntropy z c ∂ν)) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun s _ => K.fibre_mixture_gap_comparison ν z c hc0 hc1 s)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  rw [← integral_finset_sum _ (fun s _ => K.integrable_fibre_comp ν z c hc0 hc1 s
    (show Continuous quadraticEntropy by unfold quadraticEntropy; fun_prop)),
    ← integral_finset_sum _ (fun s _ => K.integrable_fibre_comp ν z c hc0 hc1 s
      (show Continuous entropyBits by unfold entropyBits; fun_prop))] at h
  exact h

theorem shannonInformation_mixture_gap (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (z : Γ → Z) (c : Γ → ℝ) (hc0 : ∀ a, 0 ≤ c a) (hc1 : ∀ a, c a ≤ 1)
    (β : ℝ) (hb : ∀ᵐ u ∂ν, (K.law u).expect c = β) :
    (∫ u, (K.law u).shannonInformation c z ∂ν) - (K.mixture ν).shannonInformation c z =
      (K.mixture ν).conditionalShannonEntropy z c -
        (∫ u, (K.law u).conditionalShannonEntropy z c ∂ν) := by
  have hmean : (K.mixture ν).expect c = β := by
    rw [K.expect_mixture, integral_congr_ae hb]
    simp
  have he : (fun u => (K.law u).shannonInformation c z) =ᵐ[ν]
      (fun u => entropyBits β - (K.law u).conditionalShannonEntropy z c) := by
    filter_upwards [hb] with u hu
    simp only [FiniteLaw.shannonInformation, hu]
  rw [integral_congr_ae he, integral_sub (integrable_const _) (K.integrable_conditionalShannonEntropy ν z c hc0 hc1)]
  simp only [FiniteLaw.shannonInformation, hmean, integral_const, measureReal_univ_eq_one, one_smul]
  ring

theorem quadraticInformation_mixture_gap (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (z : Γ → Z) (c : Γ → ℝ) (hc0 : ∀ a, 0 ≤ c a) (hc1 : ∀ a, c a ≤ 1)
    (β : ℝ) (hb : ∀ᵐ u ∂ν, (K.law u).expect c = β) :
    (∫ u, (K.law u).quadraticInformation c z ∂ν) - (K.mixture ν).quadraticInformation c z =
      (K.mixture ν).conditionalQuadraticEntropy z c -
        (∫ u, (K.law u).conditionalQuadraticEntropy z c ∂ν) := by
  have hmean : (K.mixture ν).expect c = β := by
    rw [K.expect_mixture, integral_congr_ae hb]
    simp
  have he : (fun u => (K.law u).quadraticInformation c z) =ᵐ[ν]
      (fun u => quadraticEntropy β - (K.law u).conditionalQuadraticEntropy z c) := by
    filter_upwards [hb] with u hu
    simp only [FiniteLaw.quadraticInformation, hu]
  rw [integral_congr_ae he, integral_sub (integrable_const _) (K.integrable_conditionalQuadraticEntropy ν z c hc0 hc1)]
  simp only [FiniteLaw.quadraticInformation, hmean, integral_const, measureReal_univ_eq_one, one_smul]
  ring

/-- Pinsker for the gain from exposing an arbitrary observation law. -/
theorem information_mixture_gain_comparison (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (z : Γ → Z) (c : Γ → ℝ) (hc0 : ∀ a, 0 ≤ c a) (hc1 : ∀ a, c a ≤ 1)
    (β : ℝ) (hb : ∀ᵐ u ∂ν, (K.law u).expect c = β) :
    (∫ u, (K.law u).quadraticInformation c z ∂ν) - (K.mixture ν).quadraticInformation c z ≤
      2 * Real.log 2 * ((∫ u, (K.law u).shannonInformation c z ∂ν) -
        (K.mixture ν).shannonInformation c z) := by
  rw [K.shannonInformation_mixture_gap ν z c hc0 hc1 β hb,
    K.quadraticInformation_mixture_gap ν z c hc0 hc1 β hb]
  exact K.conditional_mixture_gap_comparison ν z c hc0 hc1

omit [Fintype Z] [DecidableEq Z] in
theorem mixture_quadratic_entropy_le (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (c : Γ → ℝ) (hc0 : ∀ a, 0 ≤ c a) (hc1 : ∀ a, c a ≤ 1) :
    (∫ u, quadraticEntropy ((K.law u).expect c) ∂ν) ≤ quadraticEntropy ((K.mixture ν).expect c) := by
  have h := Posterior.quadraticGap_nonneg (K.measurable_expect c).aestronglyMeasurable
    (ae_of_all ν fun u => ⟨(K.law u).expect_nonneg hc0, (K.law u).expect_le_one hc1⟩)
  unfold Posterior.quadraticGap at h
  rw [K.expect_mixture]
  linarith only [h]

private theorem conditioning_gain_algebra (A D b V v L G : ℝ)
    (hV : 0 < V) (hv : 0 < v) (hL : 0 < L)
    (hcov : V * D = b) (hcond : b ≤ A * v) (hpin : A - D ≤ L * G) :
    b * (V - v) / (L * V * v) ≤ G := by
  apply (div_le_iff₀ (mul_pos (mul_pos hL hV) hv)).2
  have h1 := mul_le_mul_of_nonneg_right hpin (mul_nonneg hV.le hv.le)
  have h2 := mul_le_mul_of_nonneg_right hcond hV.le
  have h3 := congrArg (fun x => x * v) hcov
  nlinarith

omit [Fintype Z] [DecidableEq Z] in
/-- Manuscript `lem:conditioning-gain` for arbitrary measurable observation laws.
The finite output consists only of the bits; the conditioning index has no finite-support assumption. -/
theorem conditioning_gain (K : FiniteKernel U Γ) (ν : Measure U) [IsProbabilityMeasure ν]
    (b c : Γ → Bool) (hb : ∀ᵐ u ∂ν, (K.law u).expect (fun a => FiniteLaw.bitValue (b a)) = 1 / 2)
    (hv : 0 < ∫ u, quadraticEntropy ((K.law u).expect (fun a => FiniteLaw.bitValue (c a))) ∂ν) :
    (∫ u, (K.law u).shannonInformation (fun a => FiniteLaw.bitValue (b a)) c ∂ν) -
        (K.mixture ν).shannonInformation (fun a => FiniteLaw.bitValue (b a)) c ≥
      (K.mixture ν).quadraticInformation (fun a => FiniteLaw.bitValue (c a)) b *
        (quadraticEntropy ((K.mixture ν).expect (fun a => FiniteLaw.bitValue (c a))) -
          (∫ u, quadraticEntropy ((K.law u).expect (fun a => FiniteLaw.bitValue (c a))) ∂ν)) /
        (2 * Real.log 2 * quadraticEntropy ((K.mixture ν).expect (fun a => FiniteLaw.bitValue (c a))) *
          (∫ u, quadraticEntropy ((K.law u).expect (fun a => FiniteLaw.bitValue (c a))) ∂ν)) := by
  have hmean : (K.mixture ν).expect (fun a => FiniteLaw.bitValue (b a)) = 1 / 2 := by
    rw [K.expect_mixture, integral_congr_ae hb]
    simp
  have hT : quadraticEntropy ((K.mixture ν).expect (fun a => FiniteLaw.bitValue (b a))) = 1 := by
    rw [hmean]
    norm_num [quadraticEntropy]
  have hV := K.mixture_quadratic_entropy_le ν (fun a => FiniteLaw.bitValue (c a))
    (fun a => FiniteLaw.bitValue_nonneg (c a)) (fun a => FiniteLaw.bitValue_le_one (c a))
  have hVpos : 0 < quadraticEntropy ((K.mixture ν).expect (fun a => FiniteLaw.bitValue (c a))) :=
    lt_of_lt_of_le hv hV
  have hcov := (K.mixture ν).binary_quadratic_symmetry b c
  rw [hT, one_mul] at hcov
  have hcond := K.quadratic_conditioning ν b c (1 / 2) hb
  rw [hT, one_mul] at hcond
  have hpin := K.information_mixture_gain_comparison ν c (fun a => FiniteLaw.bitValue (b a))
    (fun a => FiniteLaw.bitValue_nonneg (b a)) (fun a => FiniteLaw.bitValue_le_one (b a)) (1 / 2) hb
  exact conditioning_gain_algebra _ _ _ _ _ _ _ hVpos hv
    (mul_pos (by norm_num) log_two_pos) hcov hcond hpin

end FiniteKernel
end CourtadeKumar.KernelInformation
