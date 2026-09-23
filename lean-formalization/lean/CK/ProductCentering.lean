import CK.Curvature

/-!
# Layer B4: product centering (`ProductCenteringGoal`)

The manuscript's Lemma [lem:product]: moving a posterior pair away from symmetry
cannot decrease the mixing gain `K` or the product `K·M`.  Both are proved by
`ν`-monotonicity with derivative identities whose signs come from the curvature
inequality (`curvature_identity`): the `z`-derivative of `Q(ν,z)·L(ν,z)` is
`curvatureGap |ν-z| (ν+z) / 4 ≥ 0`.  The `ν`-space functions contain only `eta`,
which is continuous everywhere, so the `ν+t = 1` boundary needs no limit
argument.
-/
noncomputable section
namespace CK

/-- The manuscript's `L_z = -∂_ν Q(ν,z)`. -/
def Lpair (nu z : ℝ) : ℝ := (atanhLog (nu + z) + atanhLog (nu - z)) / 2

/-! ## Parity under absolute value -/

theorem eta_abs (s : ℝ) : eta |s| = eta s := by
  rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  exact eta_even s

theorem curvature_abs (s : ℝ) : curvature |s| = curvature s := by
  rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  exact curvature_even s

theorem atanhLog_sq_abs (s : ℝ) : atanhLog |s| ^ 2 = atanhLog s ^ 2 := by
  rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  rw [atanhLog_neg]
  ring

/-! ## Basic facts about `pairEntropy` and `Lpair` -/

theorem pairEntropy_zero_left (z : ℝ) : pairEntropy 0 z = eta z := by
  unfold pairEntropy
  rw [show (0 + z : ℝ) = z by ring, show (0 - z : ℝ) = -z by ring, eta_even]
  ring

theorem pairEntropy_nonneg {nu z : ℝ} (h1 : -1 ≤ nu + z) (h2 : nu + z ≤ 1)
    (h3 : -1 ≤ nu - z) (h4 : nu - z ≤ 1) : 0 ≤ pairEntropy nu z := by
  unfold pairEntropy
  have := eta_nonneg h1 h2
  have := eta_nonneg h3 h4
  linarith

theorem pairEntropy_pos {nu z : ℝ} (h1 : -1 < nu + z) (h2 : nu + z < 1)
    (h3 : -1 ≤ nu - z) (h4 : nu - z ≤ 1) : 0 < pairEntropy nu z := by
  unfold pairEntropy
  have := eta_pos h1 h2
  have := eta_nonneg h3 h4
  linarith

theorem Lpair_nonneg {nu z : ℝ} (hnu : 0 ≤ nu) (hz : 0 ≤ z) (hsum : nu + z < 1) :
    0 ≤ Lpair nu z := by
  unfold Lpair
  rw [show (nu - z : ℝ) = -(z - nu) by ring, atanhLog_neg]
  have := atanhLog_mono (r := z - nu) (s := nu + z) (by linarith) (by linarith) hsum
  linarith

theorem continuous_pairEntropy_nu (z : ℝ) : Continuous fun w : ℝ => pairEntropy w z := by
  unfold pairEntropy
  apply Continuous.div_const
  exact (continuous_eta.comp (continuous_id.add continuous_const)).add
    (continuous_eta.comp (continuous_id.sub continuous_const))

/-! ## Derivatives -/

theorem hasDerivAt_pairEntropy_nu {nu z : ℝ} (hz : 0 ≤ z)
    (h1 : nu + z < 1) (h2 : -1 < nu - z) :
    HasDerivAt (fun w : ℝ => pairEntropy w z) (-Lpair nu z) nu := by
  have he1 : HasDerivAt (fun w : ℝ => eta (w + z)) (-atanhLog (nu + z)) nu := by
    simpa using (hasDerivAt_eta (by linarith) h1).comp nu ((hasDerivAt_id nu).add_const z)
  have he2 : HasDerivAt (fun w : ℝ => eta (w - z)) (-atanhLog (nu - z)) nu := by
    simpa using (hasDerivAt_eta h2 (by linarith)).comp nu ((hasDerivAt_id nu).sub_const z)
  have := (he1.add he2).div_const 2
  convert this using 1
  unfold Lpair
  ring

theorem hasDerivAt_pairEntropy_z {nu z : ℝ} (hz : 0 ≤ z)
    (h1 : nu + z < 1) (h2 : -1 < nu - z) :
    HasDerivAt (fun w : ℝ => pairEntropy nu w)
      ((atanhLog (nu - z) - atanhLog (nu + z)) / 2) z := by
  have he1 : HasDerivAt (fun w : ℝ => eta (nu + w)) (-atanhLog (nu + z)) z := by
    simpa using (hasDerivAt_eta (by linarith) h1).comp z ((hasDerivAt_id z).const_add nu)
  have he2 : HasDerivAt (fun w : ℝ => eta (nu - w)) (-atanhLog (nu - z) * (0 - 1)) z := by
    have hin : HasDerivAt (fun w : ℝ => nu - w) (0 - 1) z :=
      (hasDerivAt_const z nu).sub (hasDerivAt_id z)
    exact (hasDerivAt_eta h2 (by linarith)).comp z hin
  have := (he1.add he2).div_const 2
  convert this using 1
  ring

theorem hasDerivAt_Lpair_z {nu z : ℝ} (hz : 0 ≤ z)
    (h1 : nu + z < 1) (h2 : -1 < nu - z) :
    HasDerivAt (fun w : ℝ => Lpair nu w)
      ((curvature (nu + z) - curvature (nu - z)) / 2) z := by
  have ha1 : HasDerivAt (fun w : ℝ => atanhLog (nu + w)) (curvature (nu + z)) z := by
    simpa using (hasDerivAt_atanhLog (by linarith) h1).comp z ((hasDerivAt_id z).const_add nu)
  have ha2 : HasDerivAt (fun w : ℝ => atanhLog (nu - w)) (curvature (nu - z) * (0 - 1)) z := by
    have hin : HasDerivAt (fun w : ℝ => nu - w) (0 - 1) z :=
      (hasDerivAt_const z nu).sub (hasDerivAt_id z)
    exact (hasDerivAt_atanhLog h2 (by linarith)).comp z hin
  have := (ha1.add ha2).div_const 2
  convert this using 1
  ring

/-! ## Monotonicity in `z` -/

theorem Lpair_le {nu r t : ℝ} (hnu : 0 ≤ nu) (hr : 0 ≤ r) (hrt : r ≤ t)
    (hsum : nu + t < 1) : Lpair nu r ≤ Lpair nu t := by
  have hmono : MonotoneOn (fun w : ℝ => Lpair nu w) (Set.Icc r t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro z hz
      exact (hasDerivAt_Lpair_z (nu := nu) (le_trans hr hz.1) (by linarith [hz.2])
        (by linarith [hz.2, le_trans hr hz.1])).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro z hz
      exact (hasDerivAt_Lpair_z (nu := nu) (le_trans hr (le_of_lt hz.1)) (by linarith [hz.2])
        (by linarith [hz.2, le_trans hr (le_of_lt hz.1)])).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro z hz
      have hz0 : 0 ≤ z := le_trans hr (le_of_lt hz.1)
      rw [(hasDerivAt_Lpair_z (nu := nu) hz0 (by linarith [hz.2]) (by linarith [hz.2, hz0])).deriv]
      have habs : curvature (nu - z) = curvature |nu - z| := (curvature_abs _).symm
      rw [habs]
      have h1 : |nu - z| ≤ nu + z := abs_le.mpr ⟨by linarith, by linarith⟩
      have := curvature_mono (abs_nonneg (nu - z)) h1 (by linarith [hz.2])
      linarith
  exact hmono ⟨le_refl r, hrt⟩ ⟨hrt, le_refl t⟩ hrt

theorem pairEntropy_mul_Lpair_le {nu r t : ℝ} (hnu : 0 ≤ nu) (hr : 0 ≤ r) (hrt : r ≤ t)
    (hsum : nu + t < 1) :
    pairEntropy nu r * Lpair nu r ≤ pairEntropy nu t * Lpair nu t := by
  have hmono : MonotoneOn (fun w : ℝ => pairEntropy nu w * Lpair nu w) (Set.Icc r t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro z hz
      have hz0 : 0 ≤ z := le_trans hr hz.1
      exact ((hasDerivAt_pairEntropy_z (nu := nu) hz0 (by linarith [hz.2]) (by linarith [hz.2, hz0])).mul
        (hasDerivAt_Lpair_z (nu := nu) hz0 (by linarith [hz.2]) (by linarith [hz.2, hz0]))).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro z hz
      have hz0 : 0 ≤ z := le_trans hr (le_of_lt hz.1)
      exact ((hasDerivAt_pairEntropy_z (nu := nu) hz0 (by linarith [hz.2]) (by linarith [hz.2, hz0])).mul
        (hasDerivAt_Lpair_z (nu := nu) hz0 (by linarith [hz.2]) (by linarith [hz.2, hz0]))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro z hz
      have hz0 : 0 ≤ z := le_trans hr (le_of_lt hz.1)
      have hd := (hasDerivAt_pairEntropy_z (nu := nu) hz0 (by linarith [hz.2]) (by linarith [hz.2, hz0])).mul
        (hasDerivAt_Lpair_z (nu := nu) hz0 (by linarith [hz.2]) (by linarith [hz.2, hz0]))
      rw [hd.deriv]
      have hgap := curvature_identity |nu - z| (nu + z) (abs_nonneg _)
        (abs_le.mpr ⟨by linarith, by linarith⟩) (by linarith [hz.2])
      have hkey : (atanhLog (nu - z) - atanhLog (nu + z)) / 2 * Lpair nu z
          + pairEntropy nu z * ((curvature (nu + z) - curvature (nu - z)) / 2)
          = curvatureGap |nu - z| (nu + z) / 4 := by
        unfold curvatureGap Lpair pairEntropy
        rw [eta_abs, curvature_abs, atanhLog_sq_abs]
        ring
      rw [hkey]
      linarith
  exact hmono ⟨le_refl r, hrt⟩ ⟨hrt, le_refl t⟩ hrt

/-! ## Product centering -/

theorem product_centering : ProductCenteringGoal := by
  intro p nu t hp0 hp1 hnu0 ht0 hsum
  show eta ((1 - 2 * p) * t) - eta t ≤ pairEntropy nu ((1 - 2 * p) * t) - pairEntropy nu t ∧
    (eta ((1 - 2 * p) * t) - eta t) * eta ((1 - 2 * p) * t)
      ≤ (pairEntropy nu ((1 - 2 * p) * t) - pairEntropy nu t) * pairEntropy nu ((1 - 2 * p) * t)
  set r : ℝ := (1 - 2 * p) * t with hrdef
  have hρ0 : (0 : ℝ) < 1 - 2 * p := by linarith
  have hρ1 : (1 - 2 * p : ℝ) < 1 := by linarith
  have hr0 : 0 ≤ r := by positivity
  have hrt : r ≤ t := by nlinarith
  -- trivial case t = 0
  rcases eq_or_lt_of_le ht0 with rfl | ht0'
  · have hr : r = 0 := by rw [hrdef]; ring
    rw [hr]
    exact ⟨by simp, by simp⟩
  -- trivial case nu = 0
  rcases eq_or_lt_of_le hnu0 with rfl | hnu0'
  · rw [pairEntropy_zero_left, pairEntropy_zero_left]
    exact ⟨le_refl _, le_refl _⟩
  -- main case: 0 < nu, 0 < t, hence t < 1
  have ht1 : t < 1 := by linarith
  have hrt' : r < t := by nlinarith
  -- K is nondecreasing in nu on [0, nu]
  have hKmono : MonotoneOn (fun w : ℝ => pairEntropy w r - pairEntropy w t)
      (Set.Icc 0 nu) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact ((continuous_pairEntropy_nu r).sub (continuous_pairEntropy_nu t)).continuousOn
    · rw [interior_Icc]
      intro w hw
      exact ((hasDerivAt_pairEntropy_nu (nu := w) hr0 (by nlinarith [hw.2]) (by nlinarith [hw.1])).sub
        (hasDerivAt_pairEntropy_nu (nu := w) ht0 (by nlinarith [hw.2]) (by nlinarith [hw.1]))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro w hw
      rw [((hasDerivAt_pairEntropy_nu (nu := w) hr0 (by nlinarith [hw.2]) (by nlinarith [hw.1])).sub
        (hasDerivAt_pairEntropy_nu (nu := w) ht0 (by nlinarith [hw.2]) (by nlinarith [hw.1]))).deriv]
      have := Lpair_le (nu := w) (le_of_lt hw.1) hr0 hrt (by nlinarith [hw.2])
      linarith
  -- K*M is nondecreasing in nu on [0, nu]
  have hNmono : MonotoneOn (fun w : ℝ =>
      (pairEntropy w r - pairEntropy w t) * pairEntropy w r) (Set.Icc 0 nu) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact (((continuous_pairEntropy_nu r).sub (continuous_pairEntropy_nu t)).mul
        (continuous_pairEntropy_nu r)).continuousOn
    · rw [interior_Icc]
      intro w hw
      exact (((hasDerivAt_pairEntropy_nu (nu := w) hr0 (by nlinarith [hw.2]) (by nlinarith [hw.1])).sub
        (hasDerivAt_pairEntropy_nu (nu := w) ht0 (by nlinarith [hw.2]) (by nlinarith [hw.1]))).mul
        (hasDerivAt_pairEntropy_nu (nu := w) hr0 (by nlinarith [hw.2]) (by nlinarith [hw.1]))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro w hw
      have hda := (hasDerivAt_pairEntropy_nu (nu := w) hr0 (by nlinarith [hw.2]) (by nlinarith [hw.1])).sub
        (hasDerivAt_pairEntropy_nu (nu := w) ht0 (by nlinarith [hw.2]) (by nlinarith [hw.1]))
      have hdb := hasDerivAt_pairEntropy_nu (nu := w) hr0 (by nlinarith [hw.2]) (by nlinarith [hw.1])
      rw [(hda.mul hdb).deriv]
      -- signs at the interior point w
      have hw0 : 0 < w := hw.1
      have hwt : w + t < 1 := by nlinarith [hw.2]
      have hQt_pos : 0 < pairEntropy w t :=
        pairEntropy_pos (by linarith) hwt (by linarith) (by linarith)
      have hQr0 : 0 ≤ pairEntropy w r :=
        pairEntropy_nonneg (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
      have hLr0 : 0 ≤ Lpair w r := Lpair_nonneg (le_of_lt hw0) hr0 (by nlinarith)
      have hJL := pairEntropy_mul_Lpair_le (nu := w) (le_of_lt hw0) hr0 hrt hwt
      have hLt := Lpair_le (nu := w) (le_of_lt hw0) hr0 hrt hwt
      -- Qt * derivative = Qr*(Qt*Lt - Qr*Lr) + (Qr - Qt)^2 * Lr ≥ 0, and Qt > 0
      set Qr := pairEntropy w r
      set Qt := pairEntropy w t
      set Lr := Lpair w r
      set Lt := Lpair w t
      have hkey : Qt * ((Lpair w t - Lpair w r) * Qr + (Qr - Qt) * -Lpair w r)
          = Qr * (Qt * Lt - Qr * Lr) + (Qr - Qt) ^ 2 * Lr := by ring
      have hrhs : 0 ≤ Qr * (Qt * Lt - Qr * Lr) + (Qr - Qt) ^ 2 * Lr := by
        apply add_nonneg
        · exact mul_nonneg hQr0 (by linarith)
        · exact mul_nonneg (sq_nonneg _) hLr0
      nlinarith [hkey, hrhs, hQt_pos]
  -- evaluate at the endpoints
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) nu := ⟨le_refl 0, le_of_lt hnu0'⟩
  have hmemn : nu ∈ Set.Icc (0 : ℝ) nu := ⟨le_of_lt hnu0', le_refl nu⟩
  have h1 : eta r - eta t ≤ pairEntropy nu r - pairEntropy nu t := by
    have := hKmono hmem0 hmemn (le_of_lt hnu0')
    simpa [pairEntropy_zero_left] using this
  have h2 : (eta r - eta t) * eta r
      ≤ (pairEntropy nu r - pairEntropy nu t) * pairEntropy nu r := by
    have := hNmono hmem0 hmemn (le_of_lt hnu0')
    simpa [pairEntropy_zero_left] using this
  exact ⟨h1, h2⟩

end CK
