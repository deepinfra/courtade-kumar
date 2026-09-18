import CK.Pinsker
import CK.AnalyticTargets

/-!
# Layer B1/B2: calculus of `eta`, `atanhLog`, `curvature`

`eta u = binaryEntropy ((1+u)/2)` has `eta' = -atanhLog` and `atanhLog' = curvature`
on `(-1, 1)`; parity, sign, monotonicity, and the quadratic entropy defect
`kappa u >= u^2/2` (the manuscript's eq:entropyfacts, from `CK.pinsker`).
-/
noncomputable section
namespace CK

/-! ## Values and parity -/

theorem atanhLog_zero : atanhLog 0 = 0 := by
  unfold atanhLog; norm_num

theorem atanhLog_neg (u : ℝ) : atanhLog (-u) = -atanhLog u := by
  unfold atanhLog
  rw [show (1 + -u : ℝ) = 1 - u by ring, show (1 - -u : ℝ) = 1 + u by ring]
  ring

theorem curvature_even (u : ℝ) : curvature (-u) = curvature u := by
  unfold curvature
  rw [show (-u) ^ 2 = u ^ 2 by ring]

theorem eta_even (u : ℝ) : eta (-u) = eta u := by
  unfold eta
  rw [show ((1 + -u) / 2 : ℝ) = 1 - (1 + u) / 2 by ring, binaryEntropy_symm]

theorem eta_zero : eta 0 = Real.log 2 := by
  unfold eta
  rw [binaryEntropy_eq_binEntropy, show ((1 + 0) / 2 : ℝ) = 1 / 2 by norm_num, binEntropy_half]

theorem eta_one : eta 1 = 0 := by
  unfold eta
  rw [show ((1 + 1) / 2 : ℝ) = 1 by norm_num, binaryEntropy_one]

theorem kappa_zero : kappa 0 = 0 := by
  unfold kappa; rw [eta_zero]; ring

/-! ## Signs and monotonicity of `atanhLog` -/

theorem atanhLog_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : 0 ≤ atanhLog u := by
  unfold atanhLog
  have h := Real.log_le_log (by linarith : (0:ℝ) < 1 - u) (by linarith : 1 - u ≤ 1 + u)
  linarith

theorem atanhLog_mono {r s : ℝ} (hr : -1 < r) (hrs : r ≤ s) (hs : s < 1) :
    atanhLog r ≤ atanhLog s := by
  unfold atanhLog
  have h1 := Real.log_le_log (by linarith : (0:ℝ) < 1 + r) (by linarith : 1 + r ≤ 1 + s)
  have h2 := Real.log_le_log (by linarith : (0:ℝ) < 1 - s) (by linarith : 1 - s ≤ 1 - r)
  linarith

theorem le_atanhLog {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : u ≤ atanhLog u := by
  unfold atanhLog
  have := two_mul_le_log_sub_log u hu0 hu1
  linarith

/-! ## Signs of `eta` and `curvature` -/

theorem eta_nonneg {u : ℝ} (hu0 : -1 ≤ u) (hu1 : u ≤ 1) : 0 ≤ eta u :=
  binaryEntropy_nonneg' (by linarith) (by linarith)

theorem eta_pos {u : ℝ} (hu0 : -1 < u) (hu1 : u < 1) : 0 < eta u := by
  unfold eta
  rw [binaryEntropy_eq_binEntropy]
  exact Real.binEntropy_pos (by linarith) (by linarith)

theorem curvature_pos {u : ℝ} (hu0 : -1 < u) (hu1 : u < 1) : 0 < curvature u := by
  unfold curvature
  have h : 0 < 1 - u ^ 2 := by nlinarith
  exact div_pos one_pos h

theorem one_le_curvature {u : ℝ} (hu0 : -1 < u) (hu1 : u < 1) : 1 ≤ curvature u := by
  unfold curvature
  have h1 : 0 < 1 - u ^ 2 := by nlinarith
  rw [le_div_iff₀ h1]
  nlinarith

theorem curvature_mono {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s) (hs : s < 1) :
    curvature r ≤ curvature s := by
  unfold curvature
  have h1 : 0 < 1 - s ^ 2 := by nlinarith
  have h2 : 0 < 1 - r ^ 2 := by nlinarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith

/-! ## Continuity -/

theorem continuous_binaryEntropy : Continuous binaryEntropy := by
  rw [binaryEntropy_eq_binEntropy]
  exact Real.binEntropy_continuous

theorem continuous_eta : Continuous eta := by
  unfold eta
  exact continuous_binaryEntropy.comp (by continuity)

/-! ## Derivatives -/

theorem hasDerivAt_binaryEntropy {p : ℝ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    HasDerivAt binaryEntropy (Real.log (1 - p) - Real.log p) p := by
  rw [binaryEntropy_eq_binEntropy]
  exact Real.hasDerivAt_binEntropy hp0 hp1

theorem hasDerivAt_eta {u : ℝ} (hu0 : -1 < u) (hu1 : u < 1) :
    HasDerivAt eta (-atanhLog u) u := by
  have hin : HasDerivAt (fun v : ℝ => (1 + v) / 2) (1 / 2) u := by
    simpa using ((hasDerivAt_id u).const_add 1).div_const 2
  have hb := hasDerivAt_binaryEntropy (p := (1 + u) / 2)
    (ne_of_gt (by linarith)) (ne_of_lt (by linarith))
  have hc := hb.comp u hin
  convert hc using 1
  rw [show (1 - (1 + u) / 2 : ℝ) = (1 - u) / 2 by ring,
    Real.log_div (by linarith : (1 - u : ℝ) ≠ 0) (by norm_num),
    Real.log_div (by linarith : (1 + u : ℝ) ≠ 0) (by norm_num)]
  unfold atanhLog
  ring

theorem hasDerivAt_atanhLog {u : ℝ} (hu0 : -1 < u) (hu1 : u < 1) :
    HasDerivAt atanhLog (curvature u) u := by
  have h1 : HasDerivAt (fun v : ℝ => Real.log (1 + v)) ((1 + u)⁻¹) u := by
    have hi : HasDerivAt (fun v : ℝ => 1 + v) 1 u := by
      simpa using (hasDerivAt_id u).const_add 1
    simpa using (Real.hasDerivAt_log (by linarith : (1 + u : ℝ) ≠ 0)).comp u hi
  have h2 : HasDerivAt (fun v : ℝ => Real.log (1 - v)) (-(1 - u)⁻¹) u := by
    have hi : HasDerivAt (fun v : ℝ => 1 - v) (0 - 1) u :=
      (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)
    have := (Real.hasDerivAt_log (by linarith : (1 - u : ℝ) ≠ 0)).comp u hi
    simpa using this
  have hd := (h1.sub h2).div_const 2
  convert hd using 1
  unfold curvature
  have hne1 : (1 + u : ℝ) ≠ 0 := by linarith
  have hne2 : (1 - u : ℝ) ≠ 0 := by linarith
  have hne : (1 - u ^ 2 : ℝ) ≠ 0 := by nlinarith
  field_simp
  ring

/-! ## Monotonicity of `eta` and the quadratic defect -/

theorem eta_antitoneOn : AntitoneOn eta (Set.Icc (0 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1) continuous_eta.continuousOn
  · rw [interior_Icc]
    intro x hx
    exact (hasDerivAt_eta (by linarith [hx.1]) hx.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    rw [(hasDerivAt_eta (by linarith [hx.1]) hx.2).deriv]
    have := atanhLog_nonneg (le_of_lt hx.1) hx.2
    linarith

theorem eta_le_eta {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ 1) : eta s ≤ eta r :=
  eta_antitoneOn ⟨hr, le_trans hrs hs⟩ ⟨le_trans hr hrs, hs⟩ hrs

theorem eta_le_log_two {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : eta u ≤ Real.log 2 := by
  have := eta_le_eta (le_refl 0) hu0 hu1
  rw [eta_zero] at this
  exact this

theorem kappa_ge_half_sq {u : ℝ} (hu0 : -1 ≤ u) (hu1 : u ≤ 1) : u ^ 2 / 2 ≤ kappa u := by
  unfold kappa eta
  have h := pinsker ((1 + u) / 2) (by linarith) (by linarith)
  have e : (2 * ((1 + u) / 2) - 1) ^ 2 = u ^ 2 := by ring
  rw [e] at h
  linarith

theorem hasDerivAt_curvature {u : ℝ} (hu0 : -1 < u) (hu1 : u < 1) :
    HasDerivAt curvature (2 * u / (1 - u ^ 2) ^ 2) u := by
  have hne : (1 - u ^ 2 : ℝ) ≠ 0 := by nlinarith
  have h1 : HasDerivAt (fun v : ℝ => 1 - v ^ 2) (0 - (2 : ℕ) * u ^ (2 - 1)) u :=
    (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_pow 2 u)
  have := (hasDerivAt_const u (1 : ℝ)).div h1 hne
  convert this using 1
  field_simp

end CK
