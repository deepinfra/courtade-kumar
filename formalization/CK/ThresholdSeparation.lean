import CK.ComparisonConcavity
import CK.BiasDivergence

/-!
The continuous-threshold comparison in `lem:ck+vscontinuous`.
The information function is the exact two-region conditional-entropy formula.
-/

noncomputable section
namespace CourtadeKumar.Threshold
open Set MeasureTheory

def information (μ ρ : ℝ) : ℝ :=
  entropyBits μ - μ * entropyBits (ρ + (1 - ρ) * μ) -
    (1 - μ) * entropyBits ((1 - ρ) * μ)

def remainder (μ ρ : ℝ) : ℝ :=
  information μ ρ - quadraticEntropy μ * Spec.divergence ρ

/-- A smooth expression for the remainder, obtained by cancelling the two
singular entropy derivatives before taking the endpoint `ρ=1`. -/
def smoothRemainder (μ ρ : ℝ) : ℝ :=
  (μ * ((μ + (1 - μ) * ρ) * Real.log (μ + (1 - μ) * ρ) -
      (μ + (1 - μ) * ρ) * Real.log μ) +
    (1 - μ) * (((1 - μ) + μ * ρ) * Real.log ((1 - μ) + μ * ρ) -
      ((1 - μ) + μ * ρ) * Real.log (1 - μ)) -
    2 * μ * (1 - μ) * ((1 + ρ) * Real.log (1 + ρ))) / Real.log 2

theorem continuous_remainder (μ : ℝ) : Continuous (remainder μ) := by
  unfold remainder information entropyBits quadraticEntropy Spec.divergence Spec.entropy
  fun_prop

theorem continuous_smoothRemainder (μ : ℝ) : Continuous (smoothRemainder μ) := by
  unfold smoothRemainder
  fun_prop

theorem remainder_eq_smooth_interior {μ ρ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    remainder μ ρ = smoothRemainder μ ρ := by
  have hν : 1 - μ ≠ 0 := ne_of_gt (by linarith)
  have hr : 1 - ρ ≠ 0 := ne_of_gt (by linarith)
  have hrp : 1 + ρ ≠ 0 := ne_of_gt (by linarith)
  unfold remainder information entropyBits quadraticEntropy Spec.divergence Spec.entropy
    smoothRemainder
  simp_rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog]
  rw [show ρ + (1 - ρ) * μ = μ + (1 - μ) * ρ by ring,
    show 1 - (μ + (1 - μ) * ρ) = (1 - μ) * (1 - ρ) by ring,
    show (1 - ρ) * μ = μ * (1 - ρ) by ring,
    show 1 - μ * (1 - ρ) = (1 - μ) + μ * ρ by ring,
    show 1 - (1 + ρ) / 2 = (1 - ρ) / 2 by ring,
    Real.log_mul hν hr, Real.log_mul hμ0.ne' hr,
    Real.log_div hrp (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hr (by norm_num : (2 : ℝ) ≠ 0)]
  field_simp [log_two_pos.ne']
  ring

theorem remainder_eq_smooth {μ ρ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    remainder μ ρ = smoothRemainder μ ρ := by
  have he : EqOn (remainder μ) (smoothRemainder μ) (Ioo (0 : ℝ) 1) :=
    fun _ h => remainder_eq_smooth_interior hμ0 hμ1 h.1 h.2
  have hcl := he.closure (continuous_remainder μ) (continuous_smoothRemainder μ)
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hcl
  exact hcl hρ

@[simp] theorem remainder_zero (μ : ℝ) : remainder μ 0 = 0 := by
  simp only [remainder, information, zero_add, sub_zero, one_mul,
    Spec.divergence_zero, mul_zero]
  ring

@[simp] theorem remainder_one (μ : ℝ) : remainder μ 1 = entropyBits μ - quadraticEntropy μ := by
  simp [remainder, information]

@[simp] theorem information_zero (ρ : ℝ) : information 0 ρ = 0 := by
  simp [information]

@[simp] theorem information_one (ρ : ℝ) : information 1 ρ = 0 := by
  simp [information]

theorem information_half (ρ : ℝ) : information (1 / 2) ρ = Spec.divergence ρ := by
  unfold information
  rw [show ρ + (1 - ρ) * (1 / 2) = (1 + ρ) / 2 by ring,
    show (1 - ρ) * (1 / 2) = 1 - (1 + ρ) / 2 by ring,
    entropyBits_complement, entropyBits_half]
  change _ = 1 - entropyBits ((1 + ρ) / 2)
  ring

def slope (μ ρ : ℝ) : ℝ :=
  μ * (1 - μ) * (Real.log (μ + (1 - μ) * ρ) + Real.log ((1 - μ) + μ * ρ) -
    Real.log μ - Real.log (1 - μ) - 2 * Real.log (1 + ρ)) / Real.log 2

def curvature (μ ρ : ℝ) : ℝ :=
  μ * (1 - μ) * (1 - 2 * μ) ^ 2 * (1 - ρ) /
    (Real.log 2 * (1 + ρ) * (μ + (1 - μ) * ρ) * ((1 - μ) + μ * ρ))

private theorem positive_arguments {μ ρ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hρ : 0 ≤ ρ) :
    0 < μ + (1 - μ) * ρ ∧ 0 < (1 - μ) + μ * ρ ∧ 0 < 1 + ρ := by
  exact ⟨add_pos_of_pos_of_nonneg hμ0 (mul_nonneg (by linarith) hρ),
    add_pos_of_pos_of_nonneg (by linarith) (mul_nonneg hμ0.le hρ), by linarith⟩

theorem smoothRemainder_deriv {μ ρ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hρ : 0 ≤ ρ) :
    HasDerivAt (smoothRemainder μ) (slope μ ρ) ρ := by
  have hp := positive_arguments hμ0 hμ1 hρ
  have ha : HasDerivAt (fun r : ℝ => μ + (1 - μ) * r) (1 - μ) ρ := by
    simpa using ((hasDerivAt_id ρ).const_mul (1 - μ)).const_add μ
  have hc : HasDerivAt (fun r : ℝ => (1 - μ) + μ * r) μ ρ := by
    simpa using ((hasDerivAt_id ρ).const_mul μ).const_add (1 - μ)
  have hr : HasDerivAt (fun r : ℝ => 1 + r) 1 ρ := by
    simpa using (hasDerivAt_id ρ).const_add 1
  have hA := ((Real.hasDerivAt_mul_log hp.1.ne').comp ρ ha).sub (ha.mul_const (Real.log μ))
  have hC := ((Real.hasDerivAt_mul_log hp.2.1.ne').comp ρ hc).sub
    (hc.mul_const (Real.log (1 - μ)))
  have hR := (Real.hasDerivAt_mul_log hp.2.2.ne').comp ρ hr
  convert (((hA.const_mul μ).add (hC.const_mul (1 - μ))).sub
    (hR.const_mul (2 * μ * (1 - μ)))).div_const (Real.log 2) using 1
  unfold slope
  ring

theorem slope_deriv {μ ρ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hρ : 0 ≤ ρ) :
    HasDerivAt (slope μ) (curvature μ ρ) ρ := by
  have hp := positive_arguments hμ0 hμ1 hρ
  have ha : HasDerivAt (fun r : ℝ => μ + (1 - μ) * r) (1 - μ) ρ := by
    simpa using ((hasDerivAt_id ρ).const_mul (1 - μ)).const_add μ
  have hc : HasDerivAt (fun r : ℝ => (1 - μ) + μ * r) μ ρ := by
    simpa using ((hasDerivAt_id ρ).const_mul μ).const_add (1 - μ)
  have hr : HasDerivAt (fun r : ℝ => 1 + r) 1 ρ := by
    simpa using (hasDerivAt_id ρ).const_add 1
  have hlog := ((((ha.log hp.1.ne').add (hc.log hp.2.1.ne')).sub_const (Real.log μ)).sub_const
    (Real.log (1 - μ))).sub ((hr.log hp.2.2.ne').const_mul 2)
  convert (hlog.const_mul (μ * (1 - μ))).div_const (Real.log 2) using 1
  unfold curvature
  field_simp [hp.1.ne', hp.2.1.ne', hp.2.2.ne', log_two_pos.ne']
  ring

@[simp] theorem slope_zero (μ : ℝ) : slope μ 0 = 0 := by
  simp [slope]

private theorem curvature_denominator_pos {μ ρ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hρ : 0 ≤ ρ) :
    0 < Real.log 2 * (1 + ρ) * (μ + (1 - μ) * ρ) * ((1 - μ) + μ * ρ) := by
  have hp := positive_arguments hμ0 hμ1 hρ
  exact mul_pos (mul_pos (mul_pos log_two_pos hp.2.2) hp.1) hp.2.1

theorem curvature_continuousOn {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    ContinuousOn (curvature μ) (Ici 0) := by
  unfold curvature
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro r hr
    exact (curvature_denominator_pos hμ0 hμ1 hr).ne'

/-- The exact rational second derivative stated in the manuscript. -/
theorem curvature_eq_paper {μ ρ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hρ : 0 ≤ ρ) :
    curvature μ ρ = quadraticEntropy μ * (1 - quadraticEntropy μ) * (1 - ρ) /
      (Real.log 2 * (1 + ρ) * (4 * ρ + quadraticEntropy μ * (1 - ρ) ^ 2)) := by
  have he : 4 * ρ + quadraticEntropy μ * (1 - ρ) ^ 2 =
      4 * (μ + (1 - μ) * ρ) * ((1 - μ) + μ * ρ) := by
    unfold quadraticEntropy
    ring
  rw [he]
  unfold curvature quadraticEntropy
  have hp := positive_arguments hμ0 hμ1 hρ
  field_simp [hp.1.ne', hp.2.1.ne', hp.2.2.ne', log_two_pos.ne']
  ring

theorem curvature_strictAntiOn {μ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hμhalf : μ ≠ 1 / 2) :
    StrictAntiOn (curvature μ) (Icc (0 : ℝ) 1) := by
  intro r hr s hs hrs
  have hpr := positive_arguments hμ0 hμ1 hr.1
  have hps := positive_arguments hμ0 hμ1 hs.1
  have hDr := curvature_denominator_pos hμ0 hμ1 hr.1
  have hDs := curvature_denominator_pos hμ0 hμ1 hs.1
  have hN : 0 < μ * (1 - μ) * (1 - 2 * μ) ^ 2 := by
    apply mul_pos (mul_pos hμ0 (by linarith))
    exact sq_pos_of_ne_zero (by intro h; apply hμhalf; linarith)
  have hA : μ + (1 - μ) * r ≤ μ + (1 - μ) * s := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - μ) (sub_nonneg.mpr hrs.le)]
  have hC : (1 - μ) + μ * r ≤ (1 - μ) + μ * s := by nlinarith
  have hD : Real.log 2 * (1 + r) * (μ + (1 - μ) * r) * ((1 - μ) + μ * r) ≤
      Real.log 2 * (1 + s) * (μ + (1 - μ) * s) * ((1 - μ) + μ * s) := by
    apply mul_le_mul
    · apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith : 1 + r ≤ 1 + s) log_two_pos.le
      · exact hA
      · exact hpr.1.le
      · exact (mul_pos log_two_pos hps.2.2).le
    · exact hC
    · exact hpr.2.1.le
    · exact (mul_pos (mul_pos log_two_pos hps.2.2) hps.1).le
  unfold curvature
  calc
    _ ≤ μ * (1 - μ) * (1 - 2 * μ) ^ 2 * (1 - s) /
        (Real.log 2 * (1 + r) * (μ + (1 - μ) * r) * ((1 - μ) + μ * r)) := by
      apply (div_le_div_iff₀ hDs hDr).mpr
      exact mul_le_mul_of_nonneg_left hD (mul_nonneg hN.le (sub_nonneg.mpr hs.2))
    _ < _ := (div_lt_div_iff_of_pos_right hDr).mpr
      (mul_lt_mul_of_pos_left (by linarith : 1 - s < 1 - r) hN)

@[simp] theorem smoothRemainder_zero (μ : ℝ) : smoothRemainder μ 0 = 0 := by
  simp [smoothRemainder]

private theorem taylor_primitive_deriv {μ ρ t : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hρ : 0 ≤ ρ) (ht : 0 ≤ t) :
    HasDerivAt (fun z : ℝ =>
      (1 - z) * ρ * slope μ (ρ * z) + smoothRemainder μ (ρ * z))
      (ρ ^ 2 * ((1 - t) * curvature μ (ρ * t))) t := by
  have hlin : HasDerivAt (fun z : ℝ => ρ * z) ρ t := by
    simpa using (hasDerivAt_id t).const_mul ρ
  have hs := (slope_deriv hμ0 hμ1 (mul_nonneg hρ ht)).comp t hlin
  have hF := (smoothRemainder_deriv hμ0 hμ1 (mul_nonneg hρ ht)).comp t hlin
  convert ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const ρ).mul hs).add hF using 1
  simp only [id_eq, zero_sub, neg_mul, Function.comp_apply]
  ring

private theorem weighted_curvature_continuousOn {μ ρ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hρ : 0 ≤ ρ) :
    ContinuousOn (fun t : ℝ => (1 - t) * curvature μ (ρ * t)) (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.mul
  · fun_prop
  · apply (curvature_continuousOn hμ0 hμ1).comp
      (continuous_const.mul continuous_id).continuousOn
    intro t ht
    exact mul_nonneg hρ ht.1

/-- Exact second-order integral representation, including `ρ=0` and `ρ=1`. -/
theorem remainder_taylor_integral {μ ρ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    remainder μ ρ = ρ ^ 2 *
      (∫ t : ℝ in (0 : ℝ)..1, (1 - t) * curvature μ (ρ * t)) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => taylor_primitive_deriv hμ0 hμ1 hρ.1 (by simpa using ht.1))
    (((weighted_curvature_continuousOn hμ0 hμ1 hρ.1).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)).const_mul (ρ ^ 2))
  rw [intervalIntegral.integral_const_mul] at h
  simp only [sub_self, zero_mul, zero_add, mul_zero, slope_zero,
    smoothRemainder_zero, add_zero, sub_zero, mul_one] at h
  rw [remainder_eq_smooth hμ0 hμ1 hρ]
  exact h.symm

theorem weighted_curvature_integral_strict {μ ρ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hμhalf : μ ≠ 1 / 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∫ t : ℝ in (0 : ℝ)..1, (1 - t) * curvature μ t) <
      ∫ t : ℝ in (0 : ℝ)..1, (1 - t) * curvature μ (ρ * t) := by
  have hanti := curvature_strictAntiOn hμ0 hμ1 hμhalf
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0 : ℝ) < 1)
    (by simpa using weighted_curvature_continuousOn hμ0 hμ1 (by norm_num : (0 : ℝ) ≤ 1))
    (weighted_curvature_continuousOn hμ0 hμ1 hρ0.le)
  · intro t ht
    have hρt : ρ * t ≤ t := mul_le_of_le_one_left ht.1.le hρ1.le
    exact mul_le_mul_of_nonneg_left
      (hanti.antitoneOn ⟨mul_nonneg hρ0.le ht.1.le, hρt.trans ht.2⟩ ⟨ht.1.le, ht.2⟩ hρt)
      (sub_nonneg.mpr ht.2)
  · refine ⟨1 / 2, by norm_num, ?_⟩
    apply mul_lt_mul_of_pos_left
    · apply hanti
      · constructor <;> nlinarith
      · norm_num
      · nlinarith
    · norm_num

theorem remainder_strict_scaling {μ ρ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hμhalf : μ ≠ 1 / 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ρ ^ 2 * (entropyBits μ - quadraticEntropy μ) < remainder μ ρ := by
  have hInt := weighted_curvature_integral_strict hμ0 hμ1 hμhalf hρ0 hρ1
  have h1 := remainder_taylor_integral hμ0 hμ1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  simp only [remainder_one, one_pow, one_mul] at h1
  rw [remainder_taylor_integral hμ0 hμ1 ⟨hρ0.le, hρ1.le⟩, h1]
  exact mul_lt_mul_of_pos_left hInt (sq_pos_of_pos hρ0)

def bound (μ ρ : ℝ) : ℝ :=
  ρ ^ 2 * entropyBits μ - (ρ ^ 2 - Spec.divergence ρ) * quadraticEntropy μ

/-- Strict threshold separation for every interior biased, nonconstant threshold. -/
theorem bound_lt_information {μ ρ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hμhalf : μ ≠ 1 / 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : bound μ ρ < information μ ρ := by
  have h := remainder_strict_scaling hμ0 hμ1 hμhalf hρ0 hρ1
  unfold bound remainder at *
  nlinarith

@[simp] theorem bound_zero (ρ : ℝ) : bound 0 ρ = information 0 ρ := by
  simp [bound, quadraticEntropy]

@[simp] theorem bound_one (ρ : ℝ) : bound 1 ρ = information 1 ρ := by
  simp [bound, quadraticEntropy]

theorem bound_half (ρ : ℝ) : bound (1 / 2) ρ = information (1 / 2) ρ := by
  rw [information_half]
  norm_num [bound, quadraticEntropy]

@[simp] theorem bound_noise_zero (μ : ℝ) : bound μ 0 = information μ 0 := by
  simp [bound, information]
  ring

@[simp] theorem bound_noise_one (μ : ℝ) : bound μ 1 = information μ 1 := by
  simp [bound, information]

theorem bound_le_information {μ ρ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    bound μ ρ ≤ information μ ρ := by
  by_cases hz : μ = 0
  · subst μ; exact (bound_zero ρ).le
  by_cases ho : μ = 1
  · subst μ; exact (bound_one ρ).le
  by_cases hh : μ = 1 / 2
  · subst μ; exact (bound_half ρ).le
  by_cases hrz : ρ = 0
  · subst ρ; exact (bound_noise_zero μ).le
  by_cases hro : ρ = 1
  · subst ρ; exact (bound_noise_one μ).le
  exact (bound_lt_information (lt_of_le_of_ne hμ0 (Ne.symm hz))
    (lt_of_le_of_ne hμ1 ho) hh (lt_of_le_of_ne hρ0 (Ne.symm hrz))
    (lt_of_le_of_ne hρ1 hro)).le

/-- Exact equality classification for an interior noise correlation. -/
theorem bound_eq_information_iff {μ ρ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    bound μ ρ = information μ ρ ↔ μ = 0 ∨ μ = 1 / 2 ∨ μ = 1 := by
  constructor
  · intro he
    by_contra hn
    have hz : μ ≠ 0 := fun h => hn (Or.inl h)
    have hh : μ ≠ 1 / 2 := fun h => hn (Or.inr (Or.inl h))
    have ho : μ ≠ 1 := fun h => hn (Or.inr (Or.inr h))
    have hlt := bound_lt_information (lt_of_le_of_ne hμ0 (Ne.symm hz))
      (lt_of_le_of_ne hμ1 ho) hh hρ0 hρ1
    exact hlt.ne he
  · rintro (rfl | rfl | rfl)
    · exact bound_zero ρ
    · exact bound_half ρ
    · exact bound_one ρ

theorem bound_eq_progressiveEntropy (μ p : ℝ) :
    bound μ (1 - 2 * p) = progressiveEntropy p μ := by
  have hD : Spec.divergence (1 - 2 * p) = noiseInformation p := by
    unfold Spec.divergence Spec.entropy noiseInformation entropyBits
    rw [show (1 + (1 - 2 * p)) / 2 = 1 - p by ring, Real.binEntropy_one_sub]
  rw [bound, hD]
  rfl

/-- The non-strict scalar content of manuscript Lemma `ck+vscontinuous`. -/
theorem progressiveEntropy_le_thresholdInformation {μ p : ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    progressiveEntropy p μ ≤ information μ (1 - 2 * p) := by
  rw [← bound_eq_progressiveEntropy]
  exact bound_le_information hμ0 hμ1 (by linarith) (by linarith)

theorem progressiveEntropy_lt_thresholdInformation {μ p : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hμhalf : μ ≠ 1 / 2)
    (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    progressiveEntropy p μ < information μ (1 - 2 * p) := by
  rw [← bound_eq_progressiveEntropy]
  exact bound_lt_information hμ0 hμ1 hμhalf (by linarith) (by linarith)

/-- Equality classification in the exact noise parameter used by the manuscript. -/
theorem progressiveEntropy_eq_thresholdInformation_iff {μ p : ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    progressiveEntropy p μ = information μ (1 - 2 * p) ↔
      μ = 0 ∨ μ = 1 / 2 ∨ μ = 1 := by
  rw [← bound_eq_progressiveEntropy]
  exact bound_eq_information_iff hμ0 hμ1 (by linarith) (by linarith)

theorem progressiveEntropy_eq_thresholdInformation_endpoints (μ p : ℝ)
    (hp : p = 0 ∨ p = 1 / 2) : progressiveEntropy p μ = information μ (1 - 2 * p) := by
  rw [← bound_eq_progressiveEntropy]
  rcases hp with rfl | rfl
  · simp
  · convert bound_noise_zero μ using 1 <;> norm_num

end CourtadeKumar.Threshold
