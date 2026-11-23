import CK.ComparisonAveraging
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Conditional comparison for arbitrary measurable observation laws. -/

set_option maxHeartbeats 300000
noncomputable section
namespace CourtadeKumar.MeasureComparison
open Set MeasureTheory Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem integrable_comp_Icc {ν : Measure Ω} [IsFiniteMeasure ν]
    {q : Ω → ℝ} (hq : AEStronglyMeasurable q ν) {a b : ℝ}
    (hqr : ∀ᵐ ω ∂ν, q ω ∈ Icc a b) {F : ℝ → ℝ} (hF : Continuous F) :
    Integrable (fun ω => F (q ω)) ν := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF.continuousOn
  apply (integrable_const C).mono' (hF.comp_aestronglyMeasurable hq)
  filter_upwards [hqr] with ω hω
  exact hC (q ω) hω

theorem weighted_convex_jensen_interval {v d : Ω → ℝ} {a b : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b)
    (hv : AEStronglyMeasurable v μ) (hd : AEStronglyMeasurable d μ)
    (hvr : ∀ᵐ ω ∂μ, v ω ∈ Icc (0 : ℝ) 1)
    (hdv : ∀ᵐ ω ∂μ, a * v ω ≤ d ω ∧ d ω ≤ b * v ω)
    (hV : 0 < ∫ ω, v ω ∂μ) {F : ℝ → ℝ}
    (hFc : Continuous F) (hF : ConvexOn ℝ (Icc a b) F) :
    (∫ ω, v ω ∂μ) * F ((∫ ω, d ω ∂μ) / (∫ ω, v ω ∂μ)) ≤
      ∫ ω, v ω * F (d ω / v ω) ∂μ := by
  let ν := μ.withDensity (fun ω => ENNReal.ofReal (v ω))
  have hvi : Integrable v μ := integrable_comp_Icc hv hvr continuous_id
  have hνmass : ν univ = ENNReal.ofReal (∫ ω, v ω ∂μ) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hvi (hvr.mono fun _ h => h.1)).symm
  haveI : IsFiniteMeasure ν := ⟨by rw [hνmass]; exact ENNReal.ofReal_lt_top⟩
  haveI : NeZero ν := ⟨by
    intro hz
    have he : ν univ = 0 := by rw [hz]; simp
    rw [hνmass, ENNReal.ofReal_eq_zero] at he
    linarith⟩
  have hνac : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hq : AEStronglyMeasurable (fun ω => d ω / v ω) ν :=
    (hd.aemeasurable.div hv.aemeasurable).aestronglyMeasurable.mono_ac hνac
  have hqr : ∀ᵐ ω ∂ν, d ω / v ω ∈ Icc a b := by
    apply hνac.ae_le
    filter_upwards [hvr, hdv] with ω hωv hωd
    by_cases hz : v ω = 0
    · simp [hz, ha, hb]
    · have hv0 := lt_of_le_of_ne hωv.1 (Ne.symm hz)
      exact ⟨(le_div_iff₀ hv0).mpr hωd.1, (div_le_iff₀ hv0).mpr hωd.2⟩
  have hqi : Integrable (fun ω => d ω / v ω) ν :=
    integrable_comp_Icc (ν := ν) (q := fun ω => d ω / v ω) (a := a) (b := b) (F := id) hq hqr continuous_id
  have hFqi : Integrable (fun ω => F (d ω / v ω)) ν :=
    integrable_comp_Icc (ν := ν) (q := fun ω => d ω / v ω) (a := a) (b := b) (F := F) hq hqr hFc
  have hintegral (g : Ω → ℝ) :
      (∫ ω, g ω ∂ν) = ∫ ω, v ω * g ω ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hv.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hvr] with ω hω
    simp only [ENNReal.toReal_ofReal hω.1, smul_eq_mul]
  have hcancel : (∫ ω, d ω / v ω ∂ν) = ∫ ω, d ω ∂μ := by
    rw [hintegral]
    apply integral_congr_ae
    filter_upwards [hvr, hdv] with ω hωv hωd
    by_cases hz : v ω = 0
    · have hd0 : d ω = 0 := by
        have hzero := hωd
        simp only [hz, mul_zero] at hzero
        exact le_antisymm hzero.2 hzero.1
      simp [hz, hd0]
    · field_simp
  have hνreal : ν.real univ = ∫ ω, v ω ∂μ := by
    rw [measureReal_def, hνmass, ENNReal.toReal_ofReal hV.le]
  have h := hF.map_average_le hFc.continuousOn isClosed_Icc hqr hqi hFqi
  rw [average_eq, average_eq, hνreal, hcancel, hintegral, smul_eq_mul, smul_eq_mul] at h
  have h' := mul_le_mul_of_nonneg_left h hV.le
  simpa only [← div_eq_inv_mul, mul_div_cancel₀ _ hV.ne'] using h'

/-- Entropy-weighted Jensen on the unit interval, with all zero-weight fibres retained. -/
theorem weighted_convex_jensen_unit {v d : Ω → ℝ}
    (hv : AEStronglyMeasurable v μ) (hd : AEStronglyMeasurable d μ)
    (hvr : ∀ᵐ ω ∂μ, v ω ∈ Icc (0 : ℝ) 1)
    (hdv : ∀ᵐ ω ∂μ, 0 ≤ d ω ∧ d ω ≤ v ω)
    (hV : 0 < ∫ ω, v ω ∂μ) {F : ℝ → ℝ}
    (hFc : Continuous F) (hF : ConvexOn ℝ (Icc (0 : ℝ) 1) F) :
    (∫ ω, v ω ∂μ) * F ((∫ ω, d ω ∂μ) / (∫ ω, v ω ∂μ)) ≤
      ∫ ω, v ω * F (d ω / v ω) ∂μ :=
  weighted_convex_jensen_interval (by norm_num) (by norm_num) hv hd hvr
    (by simpa only [zero_mul, one_mul] using hdv) hV hFc hF

/-- Signed entropy-weighted Jensen, used for the averaged correlation bound. -/
theorem weighted_convex_jensen {v d : Ω → ℝ}
    (hv : AEStronglyMeasurable v μ) (hd : AEStronglyMeasurable d μ)
    (hvr : ∀ᵐ ω ∂μ, v ω ∈ Icc (0 : ℝ) 1)
    (hdv : ∀ᵐ ω ∂μ, |d ω| ≤ v ω)
    (hV : 0 < ∫ ω, v ω ∂μ) {F : ℝ → ℝ}
    (hFc : Continuous F) (hF : ConvexOn ℝ (Icc (-1 : ℝ) 1) F) :
    (∫ ω, v ω ∂μ) * F ((∫ ω, d ω ∂μ) / (∫ ω, v ω ∂μ)) ≤
      ∫ ω, v ω * F (d ω / v ω) ∂μ :=
  weighted_convex_jensen_interval (by norm_num) (by norm_num) hv hd hvr
    (by filter_upwards [hdv] with ω hω; simpa only [neg_one_mul, one_mul] using abs_le.mp hω)
    hV hFc hF

omit [IsProbabilityMeasure μ] in
private theorem profile_measurable {x d : Ω → ℝ}
    (hx : AEStronglyMeasurable x μ) (hd : AEStronglyMeasurable d μ) :
    AEStronglyMeasurable (fun ω => Spec.binaryProfile (x ω) (d ω)) μ := by
  unfold Spec.binaryProfile
  exact ((aestronglyMeasurable_const.add hx).aemeasurable.div_const 2).aestronglyMeasurable.mul
    (Spec.continuous_divergence.comp_aestronglyMeasurable
      (hd.aemeasurable.div (aemeasurable_const.add hx.aemeasurable)).aestronglyMeasurable) |>.add
    (((aestronglyMeasurable_const.sub hx).aemeasurable.div_const 2).aestronglyMeasurable.mul
      (Spec.continuous_divergence.comp_aestronglyMeasurable
        (hd.aemeasurable.div (aemeasurable_const.sub hx.aemeasurable)).aestronglyMeasurable))

private theorem profile_integrable {x d : Ω → ℝ}
    (hx : AEStronglyMeasurable x μ) (hd : AEStronglyMeasurable d μ)
    (hxd : ∀ᵐ ω ∂μ, |x ω| + |d ω| ≤ 1) :
    Integrable (fun ω => Spec.binaryProfile (x ω) (d ω)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (profile_measurable hx hd)
  filter_upwards [hxd] with ω hω
  have h := Spec.binaryProfile_closed_domain hω
  rw [Real.norm_eq_abs, abs_of_nonneg h.2.1]
  nlinarith [sq_nonneg (x ω)]

omit [IsProbabilityMeasure μ] in
private theorem variance_range {x d : Ω → ℝ}
    (hxd : ∀ᵐ ω ∂μ, |x ω| + |d ω| ≤ 1) :
    ∀ᵐ ω ∂μ, 1 - x ω ^ 2 ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [hxd] with ω hω
  exact ⟨(Spec.binaryProfile_closed_domain hω).1, by nlinarith [sq_nonneg (x ω)]⟩

/-- The lower entropy-weighted comparison, with no finite-support hypothesis. -/
theorem binaryProfile_integral_lower {x d : Ω → ℝ}
    (hx : AEStronglyMeasurable x μ) (hd : AEStronglyMeasurable d μ)
    (hxd : ∀ᵐ ω ∂μ, |x ω| + |d ω| ≤ 1)
    (hV : 0 < ∫ ω, 1 - x ω ^ 2 ∂μ) :
    (∫ ω, 1 - x ω ^ 2 ∂μ) * Spec.divergence
      ((∫ ω, d ω ∂μ) / (∫ ω, 1 - x ω ^ 2 ∂μ)) ≤
        ∫ ω, Spec.binaryProfile (x ω) (d ω) ∂μ := by
  have hv : AEStronglyMeasurable (fun ω => 1 - x ω ^ 2) μ :=
    aestronglyMeasurable_const.sub (hx.pow 2)
  have hvr := variance_range hxd
  have hdv : ∀ᵐ ω ∂μ, |d ω| ≤ 1 - x ω ^ 2 :=
    hxd.mono fun _ h => (Spec.binaryProfile_closed_domain h).2.2.2.1
  have hi := profile_integrable hx hd hxd
  have hqm : AEStronglyMeasurable
      (fun ω => (1 - x ω ^ 2) * Spec.divergence (d ω / (1 - x ω ^ 2))) μ :=
    hv.mul (Spec.continuous_divergence.comp_aestronglyMeasurable
      (hd.aemeasurable.div hv.aemeasurable).aestronglyMeasurable)
  have hqbound : ∀ᵐ ω ∂μ, 0 ≤ (1 - x ω ^ 2) * Spec.divergence (d ω / (1 - x ω ^ 2)) ∧
      (1 - x ω ^ 2) * Spec.divergence (d ω / (1 - x ω ^ 2)) ≤
        Spec.binaryProfile (x ω) (d ω) := by
    filter_upwards [hxd] with ω hω
    have h := Spec.binaryProfile_closed_domain hω
    exact ⟨mul_nonneg h.1 (Spec.divergence_nonneg _), h.2.2.2.2⟩
  have hqi : Integrable
      (fun ω => (1 - x ω ^ 2) * Spec.divergence (d ω / (1 - x ω ^ 2))) μ := by
    apply hi.mono' hqm
    filter_upwards [hqbound] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2
  exact (weighted_convex_jensen hv hd hvr hdv hV
    Spec.continuous_divergence Spec.divergence_convex).trans
      (integral_mono_ae hqi hi (hqbound.mono fun _ h => h.2))

/-- Supporting lines integrate the upper comparison for arbitrary observation laws. -/
theorem binaryProfile_integral_upper {x d : Ω → ℝ} {ρ τ : ℝ}
    (hx : AEStronglyMeasurable x μ) (hd : AEStronglyMeasurable d μ)
    (hxd : ∀ᵐ ω ∂μ, |x ω| + |d ω| ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hmatch : (∫ ω, Spec.binaryProfile (x ω) (d ω) ∂μ) =
      (∫ ω, 1 - x ω ^ 2 ∂μ) * Spec.divergence τ) :
    (∫ ω, Spec.binaryProfile (x ω) (ρ * d ω) ∂μ) ≤
      (∫ ω, 1 - x ω ^ 2 ∂μ) * Spec.divergence (ρ * τ) := by
  obtain ⟨c, hc⟩ := Spec.exists_comparison_support hρ0 hρ1 hτ
  have hxdρ : ∀ᵐ ω ∂μ, |x ω| + |ρ * d ω| ≤ 1 := by
    filter_upwards [hxd] with ω hω
    rw [abs_mul, abs_of_nonneg hρ0]
    nlinarith [abs_nonneg (d ω)]
  have hi := profile_integrable hx hd hxd
  have hv : Integrable (fun ω => 1 - x ω ^ 2) μ := integrable_comp_Icc
    (aestronglyMeasurable_const.sub (hx.pow 2)) (variance_range hxd) continuous_id
  have hiρ := profile_integrable hx (hd.const_mul ρ) hxdρ
  have hpoint : ∀ᵐ ω ∂μ, Spec.binaryProfile (x ω) (ρ * d ω) ≤
      (1 - x ω ^ 2) * Spec.divergence (ρ * τ) +
        c * (Spec.binaryProfile (x ω) (d ω) - (1 - x ω ^ 2) * Spec.divergence τ) := by
    filter_upwards [hxd] with ω hω
    have hh := Spec.binaryProfile_closed_domain hω
    by_cases hz : 1 - x ω ^ 2 = 0
    · have hd0 : d ω = 0 := abs_eq_zero.mp (by simpa [hz] using hh.2.2.2.1)
      simp [hd0, hz]
    · have hv0 : 0 < 1 - x ω ^ 2 := lt_of_le_of_ne hh.1 (Ne.symm hz)
      have hr : Spec.binaryProfile (x ω) (d ω) / (1 - x ω ^ 2) ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hh.2.1 hv0.le, (div_le_one hv0).mpr hh.2.2.1⟩
      have hs := Spec.matchingParameter_spec hr
      have hxa : |x ω| < 1 := by
        have ha : |x ω| ≤ 1 := by linarith [abs_nonneg (d ω)]
        apply lt_of_le_of_ne ha
        intro he
        have hx2 : x ω ^ 2 = 1 := by nlinarith [sq_abs (x ω)]
        exact hz (by rw [hx2]; ring)
      have hu := Spec.binaryProfile_matched_domination hρ0 hρ1 hxa
        hω hs.1 hs.2
      have hsupp := mul_le_mul_of_nonneg_left (hc _ hs.1) hv0.le
      rw [hs.2] at hsupp
      have hcancel : (1 - x ω ^ 2) * (Spec.binaryProfile (x ω) (d ω) / (1 - x ω ^ 2)) =
          Spec.binaryProfile (x ω) (d ω) := by field_simp
      apply hu.trans
      calc
        _ ≤ (1 - x ω ^ 2) * (Spec.divergence (ρ * τ) +
            c * (Spec.binaryProfile (x ω) (d ω) / (1 - x ω ^ 2) - Spec.divergence τ)) := hsupp
        _ = _ := by
          calc
            _ = (1 - x ω ^ 2) * Spec.divergence (ρ * τ) +
                c * ((1 - x ω ^ 2) * (Spec.binaryProfile (x ω) (d ω) / (1 - x ω ^ 2)) -
                  (1 - x ω ^ 2) * Spec.divergence τ) := by ring
            _ = _ := by rw [hcancel]
  have h := integral_mono_ae hiρ
    ((hv.mul_const _).add ((hi.sub (hv.mul_const _)).const_mul c)) hpoint
  change (∫ ω, Spec.binaryProfile (x ω) (ρ * d ω) ∂μ) ≤
    ∫ ω, (1 - x ω ^ 2) * Spec.divergence (ρ * τ) +
      c * (Spec.binaryProfile (x ω) (d ω) - (1 - x ω ^ 2) * Spec.divergence τ) ∂μ at h
  rw [integral_add (f := fun ω => (1 - x ω ^ 2) * Spec.divergence (ρ * τ))
      (g := fun ω => c * (Spec.binaryProfile (x ω) (d ω) - (1 - x ω ^ 2) * Spec.divergence τ))
      (hv.mul_const _) ((hi.sub (hv.mul_const _)).const_mul c),
    integral_const_mul, integral_sub hi (hv.mul_const _), integral_mul_const,
    integral_mul_const, hmatch] at h
  simpa using h

/-- The complete matching-parameter comparison for an arbitrary probability law. -/
theorem binaryProfile_integral_comparison {x d : Ω → ℝ} {ρ : ℝ}
    (hx : AEStronglyMeasurable x μ) (hd : AEStronglyMeasurable d μ)
    (hxd : ∀ᵐ ω ∂μ, |x ω| + |d ω| ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hV : 0 < ∫ ω, 1 - x ω ^ 2 ∂μ) :
    ∃ τ ∈ Icc (0 : ℝ) 1,
      (∫ ω, Spec.binaryProfile (x ω) (d ω) ∂μ) =
        (∫ ω, 1 - x ω ^ 2 ∂μ) * Spec.divergence τ ∧
      (∫ ω, Spec.binaryProfile (x ω) (ρ * d ω) ∂μ) ≤
        (∫ ω, 1 - x ω ^ 2 ∂μ) * Spec.divergence (ρ * τ) ∧
      (∫ ω, d ω ∂μ)^2 / (∫ ω, 1 - x ω ^ 2 ∂μ)^2 ≤ τ^2 := by
  have hi := profile_integrable hx hd hxd
  have hv : Integrable (fun ω => 1 - x ω ^ 2) μ := integrable_comp_Icc
    (aestronglyMeasurable_const.sub (hx.pow 2)) (variance_range hxd) continuous_id
  have hI0 : 0 ≤ ∫ ω, Spec.binaryProfile (x ω) (d ω) ∂μ :=
    integral_nonneg_of_ae (hxd.mono fun _ h => (Spec.binaryProfile_closed_domain h).2.1)
  have hIV : (∫ ω, Spec.binaryProfile (x ω) (d ω) ∂μ) ≤ ∫ ω, 1 - x ω ^ 2 ∂μ :=
    integral_mono_ae hi hv (hxd.mono fun _ h => (Spec.binaryProfile_closed_domain h).2.2.1)
  obtain ⟨τ, hτ, _⟩ := Spec.existsUnique_matching_parameter
    (div_nonneg hI0 hV.le) ((div_le_one hV).mpr hIV)
  have hmatch : (∫ ω, Spec.binaryProfile (x ω) (d ω) ∂μ) =
      (∫ ω, 1 - x ω ^ 2 ∂μ) * Spec.divergence τ := by
    rw [hτ.2]
    field_simp
  refine ⟨τ, hτ.1, hmatch, binaryProfile_integral_upper hx hd hxd hρ0 hρ1 hτ.1 hmatch, ?_⟩
  have hdv : ∀ᵐ ω ∂μ, |d ω| ≤ 1 - x ω ^ 2 :=
    hxd.mono fun _ h => (Spec.binaryProfile_closed_domain h).2.2.2.1
  have hdi : Integrable d μ := by
    apply hv.mono' hd
    simpa only [Real.norm_eq_abs] using hdv
  have hdV : |∫ ω, d ω ∂μ| ≤ ∫ ω, 1 - x ω ^ 2 ∂μ :=
    (norm_integral_le_integral_norm _).trans
      (integral_mono_ae hdi.norm hv (by simpa only [Real.norm_eq_abs] using hdv))
  exact Spec.matched_correlation_bound hV hdV hτ.1 hτ.2
    (binaryProfile_integral_lower hx hd hxd hV)

end CourtadeKumar.MeasureComparison
