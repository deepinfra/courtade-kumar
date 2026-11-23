import CK.Matching
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Function

/-!
The unbiased comparison channel as a concave function of input information.
The proof uses supporting lines, with all endpoint cases included.
-/

noncomputable section
namespace CourtadeKumar.Spec

def comparisonLogRatio (t : ℝ) : ℝ := Real.log (1 + t) - Real.log (1 - t)

@[simp] theorem comparisonLogRatio_zero : comparisonLogRatio 0 = 0 := by
  simp [comparisonLogRatio]

theorem hasDerivAt_comparisonLogRatio {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) :
    HasDerivAt comparisonLogRatio (2 / (1 - t ^ 2)) t := by
  have hp : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hm : 1 - t ≠ 0 := ne_of_gt (by linarith)
  have hd : 1 - t ^ 2 ≠ 0 := by
    have : (1 + t) * (1 - t) ≠ 0 := mul_ne_zero hp hm
    nlinarith
  convert (((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).log hp).sub
    (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).log hm) using 1
  simp only [id_eq, zero_add, zero_sub, neg_div, sub_neg_eq_add]
  field_simp [hp, hm, hd]
  ring

theorem comparisonLogRatio_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < comparisonLogRatio t := by
  unfold comparisonLogRatio
  exact sub_pos.mpr (Real.log_lt_log (by linarith) (by linarith))

theorem comparisonLogRatio_two_mul_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    2 * t ≤ comparisonLogRatio t := by
  have hd (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) :
      HasDerivAt (fun y => comparisonLogRatio y - 2 * y)
        (2 / (1 - x ^ 2) - 2) x := by
    convert (hasDerivAt_comparisonLogRatio (by linarith [hx.1]) hx.2).sub
      ((hasDerivAt_id x).const_mul 2) using 1
    simp
  have hm : MonotoneOn (fun y => comparisonLogRatio y - 2 * y) (Set.Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    · intro x hx
      exact (hd x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      have hx' := interior_subset hx
      have hden : 0 < 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
      apply sub_nonneg.mpr
      apply (le_div_iff₀ hden).mpr
      nlinarith [sq_nonneg x]
  have h := hm (by simp) ⟨ht0, ht1⟩ ht0
  simpa using h

def comparisonAux (t : ℝ) : ℝ := (1 - t ^ 2) * comparisonLogRatio t / t

theorem hasDerivAt_comparisonAux {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt comparisonAux
      (2 / t - (1 + t ^ 2) * comparisonLogRatio t / t ^ 2) t := by
  have hd : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith)
  convert (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)).mul
    (hasDerivAt_comparisonLogRatio (by linarith) ht1)).div
      (hasDerivAt_id t) ht0.ne' using 1
  simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one, zero_sub]
  field_simp [ht0.ne', hd]
  ring

theorem comparisonAux_antitone : AntitoneOn comparisonAux (Set.Ioo (0 : ℝ) 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo 0 1)
    (fun t ht => (hasDerivAt_comparisonAux ht.1 ht.2).continuousAt.continuousWithinAt)
  · intro t ht
    have ht' := interior_subset ht
    exact (hasDerivAt_comparisonAux ht'.1 ht'.2).hasDerivWithinAt
  · intro t ht
    have ht' := interior_subset ht
    have hL := comparisonLogRatio_two_mul_le ht'.1.le ht'.2
    have hmul := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 1 + t ^ 2)
    have htsq : 0 < t ^ 2 := sq_pos_of_pos ht'.1
    apply sub_nonpos.mpr
    apply (le_div_iff₀ htsq).mpr
    have hcancel : 2 / t * t ^ 2 = 2 * t := by field_simp [ht'.1.ne']; ring
    rw [hcancel]
    nlinarith [mul_nonneg ht'.1.le (sq_nonneg t)]

def comparisonSlope (ρ t : ℝ) : ℝ :=
  ρ * comparisonLogRatio (ρ * t) / comparisonLogRatio t

theorem hasDerivAt_comparisonSlope {ρ t : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (comparisonSlope ρ)
      (2 * ρ * (ρ * comparisonLogRatio t / (1 - (ρ * t) ^ 2) -
        comparisonLogRatio (ρ * t) / (1 - t ^ 2)) / comparisonLogRatio t ^ 2) t := by
  have hρt0 : 0 < ρ * t := mul_pos hρ0 ht0
  have hρt1 : ρ * t < 1 := lt_of_le_of_lt (mul_le_of_le_one_left ht0.le hρ1) ht1
  have hD : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith)
  have hDρ : 1 - (ρ * t) ^ 2 ≠ 0 := ne_of_gt (by nlinarith)
  have hL : comparisonLogRatio t ≠ 0 := (comparisonLogRatio_pos ht0 ht1).ne'
  convert (((hasDerivAt_comparisonLogRatio (by linarith : -1 < ρ * t) hρt1).comp t
      ((hasDerivAt_id t).const_mul ρ)).const_mul ρ).div
    (hasDerivAt_comparisonLogRatio (by linarith) ht1) hL using 1
  simp only [id_eq, mul_one]
  field_simp [hL, hD, hDρ]
  ring

theorem comparisonSlope_antitone {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    AntitoneOn (comparisonSlope ρ) (Set.Ioo (0 : ℝ) 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo 0 1)
    (fun t ht => (hasDerivAt_comparisonSlope hρ0 hρ1 ht.1 ht.2).continuousAt.continuousWithinAt)
  · intro t ht
    have ht' := interior_subset ht
    exact (hasDerivAt_comparisonSlope hρ0 hρ1 ht'.1 ht'.2).hasDerivWithinAt
  · intro t ht
    have ht' := interior_subset ht
    have hρt0 : 0 < ρ * t := mul_pos hρ0 ht'.1
    have hρtle : ρ * t ≤ t := mul_le_of_le_one_left ht'.1.le hρ1
    have hρt1 : ρ * t < 1 := lt_of_le_of_lt hρtle ht'.2
    have hD : 0 < 1 - t ^ 2 := by nlinarith [ht'.1, ht'.2]
    have hDρ : 0 < 1 - (ρ * t) ^ 2 := by nlinarith
    have hK := comparisonAux_antitone ⟨hρt0, hρt1⟩ ht' hρtle
    unfold comparisonAux at hK
    have hK' := (div_le_div_iff₀ ht'.1 hρt0).mp hK
    have hnum : ρ * comparisonLogRatio t * (1 - t ^ 2) ≤
        comparisonLogRatio (ρ * t) * (1 - (ρ * t) ^ 2) := by
      apply (mul_le_mul_left ht'.1).mp
      nlinarith [hK']
    have hquot : ρ * comparisonLogRatio t / (1 - (ρ * t) ^ 2) ≤
        comparisonLogRatio (ρ * t) / (1 - t ^ 2) :=
      (div_le_div_iff₀ hDρ hD).mpr hnum
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hquot))
      (sq_nonneg _)

theorem hasDerivAt_divergence {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) :
    HasDerivAt divergence (comparisonLogRatio t / (2 * Real.log 2)) t := by
  have hp : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hm : 1 - t ≠ 0 := ne_of_gt (by linarith)
  have hhalf0 : (1 + t) / 2 ≠ 0 := by positivity
  have hhalf1 : (1 + t) / 2 ≠ 1 := by linarith
  have h := (hasDerivAt_const t (1 : ℝ)).sub
    (((Real.hasDerivAt_binEntropy hhalf0 hhalf1).comp t
      (((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).div_const 2)).div_const
        (Real.log 2))
  convert h using 1
  simp only [id_eq, zero_add, one_div, zero_sub]
  rw [show (1 - (1 + t) / 2 : ℝ) = (1 - t) / 2 by ring,
    Real.log_div hm (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hp (by norm_num : (2 : ℝ) ≠ 0)]
  unfold comparisonLogRatio
  ring

theorem hasDerivAt_comparison_support_function {ρ τ t : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun y => divergence (ρ * y) - comparisonSlope ρ τ * divergence y)
      (comparisonLogRatio t / (2 * Real.log 2) *
        (comparisonSlope ρ t - comparisonSlope ρ τ)) t := by
  have hρt0 : 0 < ρ * t := mul_pos hρ0 ht0
  have hρt1 : ρ * t < 1 := lt_of_le_of_lt (mul_le_of_le_one_left ht0.le hρ1) ht1
  convert ((hasDerivAt_divergence (by linarith : -1 < ρ * t) hρt1).comp t
    ((hasDerivAt_id t).const_mul ρ)).sub
    ((hasDerivAt_divergence (by linarith) ht1).const_mul (comparisonSlope ρ τ)) using 1
  simp only [id_eq, mul_one]
  rw [show comparisonSlope ρ t = ρ * comparisonLogRatio (ρ * t) / comparisonLogRatio t
    from rfl]
  field_simp [(comparisonLogRatio_pos ht0 ht1).ne', log_two_pos.ne']
  ring

theorem comparison_support_interior {ρ τ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    divergence (ρ * t) ≤ divergence (ρ * τ) +
      comparisonSlope ρ τ * (divergence t - divergence τ) := by
  let g : ℝ → ℝ := fun y => divergence (ρ * y) - comparisonSlope ρ τ * divergence y
  have hg : Continuous g :=
    (continuous_divergence.comp (continuous_const.mul continuous_id)).sub
      (continuous_const.mul continuous_divergence)
  have hleft : MonotoneOn g (Set.Icc 0 τ) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 τ) hg.continuousOn
    · intro y hy
      have hy' : y ∈ Set.Ioo 0 τ := by simpa only [interior_Icc] using hy
      exact (hasDerivAt_comparison_support_function hρ0 hρ1 hy'.1
        (hy'.2.trans hτ1)).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Set.Ioo 0 τ := by simpa only [interior_Icc] using hy
      exact mul_nonneg
        (div_nonneg (comparisonLogRatio_pos hy'.1 (hy'.2.trans hτ1)).le
          (mul_pos (by norm_num) log_two_pos).le)
        (sub_nonneg.mpr (comparisonSlope_antitone hρ0 hρ1
          ⟨hy'.1, hy'.2.trans hτ1⟩ ⟨hτ0, hτ1⟩ hy'.2.le))
  have hright : AntitoneOn g (Set.Icc τ 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc τ 1) hg.continuousOn
    · intro y hy
      have hy' : y ∈ Set.Ioo τ 1 := by simpa only [interior_Icc] using hy
      exact (hasDerivAt_comparison_support_function hρ0 hρ1
        (hτ0.trans hy'.1) hy'.2).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Set.Ioo τ 1 := by simpa only [interior_Icc] using hy
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (comparisonLogRatio_pos (hτ0.trans hy'.1) hy'.2).le
          (mul_pos (by norm_num) log_two_pos).le)
        (sub_nonpos.mpr (comparisonSlope_antitone hρ0 hρ1
          ⟨hτ0, hτ1⟩ ⟨hτ0.trans hy'.1, hy'.2⟩ hy'.1.le))
  have hmax : g t ≤ g τ := by
    rcases le_total t τ with h | h
    · exact hleft ⟨ht.1, h⟩ ⟨hτ0.le, le_rfl⟩ h
    · exact hright ⟨le_rfl, hτ1.le⟩ ⟨h, ht.2⟩ h
  dsimp [g] at hmax
  linarith

/-- Every matching parameter, including the two endpoints, has an affine upper support. -/
theorem exists_comparison_support {ρ τ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hτ : τ ∈ Set.Icc 0 1) :
    ∃ c : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      divergence (ρ * t) ≤ divergence (ρ * τ) + c * (divergence t - divergence τ) := by
  by_cases hρ : ρ = 0
  · subst ρ
    exact ⟨0, by simp⟩
  by_cases hτ0 : τ = 0
  · subst τ
    refine ⟨ρ ^ 2, fun t ht => ?_⟩
    simpa using divergence_scaling hρ0 hρ1 (by linarith [ht.1] : -1 ≤ t) ht.2
  by_cases hτ1 : τ = 1
  · subst τ
    refine ⟨0, fun t ht => ?_⟩
    simp only [mul_one, zero_mul, add_zero]
    exact divergence_strictMonoOn.monotoneOn
      ⟨mul_nonneg hρ0 ht.1, (mul_le_of_le_one_right hρ0 ht.2).trans hρ1⟩
      ⟨hρ0, hρ1⟩ (mul_le_of_le_one_right hρ0 ht.2)
  exact ⟨comparisonSlope ρ τ, fun _ ht => comparison_support_interior
    (lt_of_le_of_ne hρ0 (Ne.symm hρ)) hρ1
    (lt_of_le_of_ne hτ.1 (Ne.symm hτ0)) (lt_of_le_of_ne hτ.2 hτ1) ht⟩

/-- The unique unbiased correlation parameter for a prescribed information in `[0,1]`.
Outside this interval, the definition takes the harmless total value zero. -/
def matchingParameter (r : ℝ) : ℝ :=
  if hr : r ∈ Set.Icc (0 : ℝ) 1 then
    Classical.choose (existsUnique_matching_parameter hr.1 hr.2).exists
  else 0

theorem matchingParameter_spec {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    matchingParameter r ∈ Set.Icc (0 : ℝ) 1 ∧ divergence (matchingParameter r) = r := by
  simp only [matchingParameter, dif_pos hr]
  exact Classical.choose_spec (existsUnique_matching_parameter hr.1 hr.2).exists

theorem divergence_mem_unit {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    divergence t ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨divergence_nonneg t, ?_⟩
  have h := divergence_strictMonoOn.monotoneOn ht (by simp) ht.2
  simpa using h

@[simp] theorem matchingParameter_divergence {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    matchingParameter (divergence t) = t := by
  have hs := matchingParameter_spec (divergence_mem_unit ht)
  exact divergence_strictMonoOn.injOn hs.1 ht hs.2

theorem matchingParameter_monotone : MonotoneOn matchingParameter (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hsx := matchingParameter_spec hx
  have hsy := matchingParameter_spec hy
  by_contra hn
  have hlt := divergence_strictMonoOn hsy.1 hsx.1 (lt_of_not_ge hn)
  rw [hsx.2, hsy.2] at hlt
  linarith

/-- The manuscript's comparison function: `Fρ(D(t)) = D(ρt)`. -/
def comparisonMap (ρ r : ℝ) : ℝ := divergence (ρ * matchingParameter r)

@[simp] theorem comparisonMap_divergence (ρ : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    comparisonMap ρ (divergence t) = divergence (ρ * t) := by
  simp [comparisonMap, matchingParameter_divergence ht]

theorem comparisonMap_monotone {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    MonotoneOn (comparisonMap ρ) (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hsx := matchingParameter_spec hx
  have hsy := matchingParameter_spec hy
  unfold comparisonMap
  apply divergence_strictMonoOn.monotoneOn
  · exact ⟨mul_nonneg hρ0 hsx.1.1,
      (mul_le_of_le_one_right hρ0 hsx.1.2).trans hρ1⟩
  · exact ⟨mul_nonneg hρ0 hsy.1.1,
      (mul_le_of_le_one_right hρ0 hsy.1.2).trans hρ1⟩
  · exact mul_le_mul_of_nonneg_left (matchingParameter_monotone hx hy hxy) hρ0

/-- Concavity of the actual comparison function, uniformly for `ρ ∈ [0,1]`.
This includes both information endpoints without differentiating the inverse there. -/
theorem comparisonMap_concave {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (comparisonMap ρ) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  let z := a * x + b * y
  have hz : z ∈ Set.Icc (0 : ℝ) 1 := (convex_Icc 0 1) hx hy ha hb hab
  have hsx := matchingParameter_spec hx
  have hsy := matchingParameter_spec hy
  have hsz := matchingParameter_spec hz
  obtain ⟨c, hc⟩ := exists_comparison_support hρ0 hρ1 hsz.1
  have hcx := hc _ hsx.1
  have hcy := hc _ hsy.1
  rw [hsx.2, hsz.2] at hcx
  rw [hsy.2, hsz.2] at hcy
  change a * divergence (ρ * matchingParameter x) +
    b * divergence (ρ * matchingParameter y) ≤ divergence (ρ * matchingParameter z)
  calc
    _ ≤ a * (divergence (ρ * matchingParameter z) + c * (x - z)) +
        b * (divergence (ρ * matchingParameter z) + c * (y - z)) :=
      add_le_add (mul_le_mul_of_nonneg_left hcx ha) (mul_le_mul_of_nonneg_left hcy hb)
    _ = (a + b) * divergence (ρ * matchingParameter z) +
        c * (a * x + b * y - (a + b) * z) := by ring
    _ = divergence (ρ * matchingParameter z) := by rw [hab]; dsimp [z]; ring

/-- A concrete increasing concave map with the matching identity required by
Lemma `comparison-calculus` of the pinned manuscript. -/
theorem exists_concave_comparisonMap {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∃ F : ℝ → ℝ, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) F ∧
      MonotoneOn F (Set.Icc (0 : ℝ) 1) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, F (divergence t) = divergence (ρ * t) := by
  exact ⟨comparisonMap ρ, comparisonMap_concave hρ0 hρ1,
    comparisonMap_monotone hρ0 hρ1, fun _ ht => comparisonMap_divergence ρ ht⟩

end CourtadeKumar.Spec
