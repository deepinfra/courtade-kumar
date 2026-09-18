import CK.GainBounds
import CK.Constants

/-!
# The strict anchor at `ρ = 3/5` (eq:anchorcomparison, app:anchor)

We prove `StrictAnchorGoal`: for all `t ∈ [0,1]`,
`(39/40) · psi (3/5) t ≤ eta t`, where `psi ρ t = (1-t)(1+t-ρ²)`.

The proof follows app:anchor:
* Case A (`1/3 ≤ t < 1`): put `y = (1-t)/2 ∈ (0,1/3]`; write `eta t = h(y)` and use
  `-(1-y) ln(1-y) ≥ y - y²/2 - y³/4` together with `-ln y + c y ≥ 1 + ln c` for `c = 199/60`.
* Case B (`t = 1`): both sides vanish.
* Case C (`0 ≤ t ≤ 1/3`): `D t = eta t - (39/40) psi (3/5) t` is antitone on `[0,1/3]`
  because `D'` is monotone there with `D'(1/3) < 0`; and `D(1/3) > 0` by `comb_log3`.
-/
noncomputable section
namespace CK

/-! ## Values at `t = 1/3` -/

/-- `atanh(1/3) = (ln 2)/2`. -/
theorem atanhLog_third : atanhLog (1 / 3) = Real.log 2 / 2 := by
  unfold atanhLog
  rw [show (1 + 1 / 3 : ℝ) = 4 / 3 by norm_num, show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num,
    ← Real.log_div (x := 4 / 3) (y := 2 / 3) (by norm_num) (by norm_num)]
  norm_num

/-- `eta (1/3) = h(2/3) = ln 3 - (2/3) ln 2`. -/
theorem eta_third : eta (1 / 3) = Real.log 3 - (2 / 3) * Real.log 2 := by
  unfold eta binaryEntropy
  rw [show ((1 + 1 / 3) / 2 : ℝ) = 2 / 3 by norm_num, show (1 - 2 / 3 : ℝ) = 1 / 3 by norm_num,
    Real.log_div (x := 2) (y := 3) (by norm_num) (by norm_num),
    Real.log_div (x := 1) (y := 3) (by norm_num) (by norm_num), Real.log_one]
  ring

/-! ## Case C: the defect `D` and its derivative -/

/-- The anchor defect `D t = eta t - (39/40) psi (3/5) t` (app:anchor). -/
def anchorD (t : ℝ) : ℝ := eta t - (39 / 40 : ℝ) * psi (3 / 5) t

/-- `D'(t) = -atanh t + (39/20) t - 351/1000`. -/
def anchorD' (t : ℝ) : ℝ := -atanhLog t + (39 / 20 : ℝ) * t - 351 / 1000

theorem hasDerivAt_anchorD {t : ℝ} (h0 : -1 < t) (h1 : t < 1) :
    HasDerivAt anchorD (anchorD' t) t := by
  have hE := hasDerivAt_eta h0 h1
  have hP : HasDerivAt (fun v : ℝ => psi (3 / 5) v)
      ((0 - 1) * (1 + t - (3 / 5 : ℝ) ^ 2) + (1 - t) * (0 + 1 - 0)) t := by
    unfold psi
    exact ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul
      (((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).sub (hasDerivAt_const t _))
  have hD : HasDerivAt (fun v : ℝ => eta v - (39 / 40 : ℝ) * psi (3 / 5) v)
      (-atanhLog t - (39 / 40 : ℝ) *
        ((0 - 1) * (1 + t - (3 / 5 : ℝ) ^ 2) + (1 - t) * (0 + 1 - 0))) t :=
    hE.sub (hP.const_mul _)
  exact hD.congr_deriv (by unfold anchorD'; ring)

theorem hasDerivAt_anchorD' {t : ℝ} (h0 : -1 < t) (h1 : t < 1) :
    HasDerivAt anchorD' (-curvature t + 39 / 20) t := by
  have hA := hasDerivAt_atanhLog h0 h1
  have hD : HasDerivAt (fun v : ℝ => -atanhLog v + (39 / 20 : ℝ) * v - 351 / 1000)
      (-curvature t + (39 / 20 : ℝ) * 1 - 0) t :=
    (hA.neg.add ((hasDerivAt_id t).const_mul _)).sub (hasDerivAt_const t _)
  exact hD.congr_deriv (by ring)

/-- `D'` is monotone on `[0,1/3]`: its derivative `39/20 - curvature t ≥ 39/20 - 9/8 > 0`. -/
theorem anchorD'_monotoneOn : MonotoneOn anchorD' (Set.Icc (0 : ℝ) (1 / 3)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro v hv
    exact (hasDerivAt_anchorD' (by linarith [hv.1]) (by linarith [hv.2])).continuousAt.continuousWithinAt
  · rw [interior_Icc]
    intro v hv
    exact (hasDerivAt_anchorD' (by linarith [hv.1]) (by linarith [hv.2])).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro v hv
    rw [(hasDerivAt_anchorD' (by linarith [hv.1]) (by linarith [hv.2])).deriv]
    have hc : curvature v ≤ 9 / 8 := by
      unfold curvature
      rw [div_le_iff₀ (by nlinarith [hv.1, hv.2])]
      nlinarith [hv.1, hv.2]
    linarith

/-- `D'(1/3) = -(ln 2)/2 + 299/1000 < 0`. -/
theorem anchorD'_third_neg : anchorD' (1 / 3) < 0 := by
  unfold anchorD'
  rw [atanhLog_third]
  have := AppF.row_log_q2_lo
  linarith

/-- `D` is antitone on `[0,1/3]` since `D' ≤ D'(1/3) < 0` there. -/
theorem anchorD_antitoneOn : AntitoneOn anchorD (Set.Icc (0 : ℝ) (1 / 3)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro v hv
    exact (hasDerivAt_anchorD (by linarith [hv.1]) (by linarith [hv.2])).continuousAt.continuousWithinAt
  · rw [interior_Icc]
    intro v hv
    exact (hasDerivAt_anchorD (by linarith [hv.1]) (by linarith [hv.2])).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro v hv
    rw [(hasDerivAt_anchorD (by linarith [hv.1]) (by linarith [hv.2])).deriv]
    have hm := anchorD'_monotoneOn ⟨hv.1.le, hv.2.le⟩ ⟨by norm_num, le_refl _⟩ hv.2.le
    have := anchorD'_third_neg
    linarith

/-- `D(1/3) = ln 3 - (2/3) ln 2 - 949/1500 > 0` (`comb_log3`). -/
theorem anchorD_third_pos : 0 < anchorD (1 / 3) := by
  unfold anchorD psi
  rw [eta_third]
  have := AppF.comb_log3
  norm_num
  linarith

/-- Case C of app:anchor: `0 ≤ t ≤ 1/3`. -/
theorem anchor_caseC {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 3) :
    (39 / 40 : ℝ) * psi (3 / 5) t ≤ eta t := by
  have h := anchorD_antitoneOn ⟨ht0, ht1⟩ ⟨by norm_num, le_refl _⟩ ht1
  have h2 := anchorD_third_pos
  unfold anchorD at h h2
  linarith

/-! ## Case A: `1/3 ≤ t < 1` via `y = (1-t)/2` -/

/-- Case A of app:anchor: `1/3 ≤ t < 1`. -/
theorem anchor_caseA {t : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t < 1) :
    (39 / 40 : ℝ) * psi (3 / 5) t ≤ eta t := by
  set y : ℝ := (1 - t) / 2 with hy
  have hy0 : 0 < y := by rw [hy]; linarith
  have hy1 : y ≤ 1 / 3 := by rw [hy]; linarith
  have heta : eta t = -y * Real.log y - (1 - y) * Real.log (1 - y) := by
    unfold eta
    rw [show ((1 + t) / 2 : ℝ) = 1 - y by rw [hy]; ring, binaryEntropy_symm]
    rfl
  have hpsi : psi (3 / 5) t = 2 * y * (41 / 25 - 2 * y) := by
    unfold psi; rw [hy]; ring
  -- `-(1-y) ln(1-y) ≥ y - y²/2 - y³/4`
  have hB := neg_log_one_sub_ge' hy0.le (by linarith : y ≤ 1 / 2)
  have hB' : y - y ^ 2 / 2 - y ^ 3 / 4 ≤ -(1 - y) * Real.log (1 - y) := by
    have h1y : (0 : ℝ) < 1 - y := by linarith
    rw [div_le_iff₀ h1y] at hB
    linarith
  -- `-ln y + c y ≥ 1 + ln c` with `c = 199/60`
  have hlog : 1 + Real.log (199 / 60) ≤ -Real.log y + (199 / 60) * y := by
    have h1 := Real.log_le_sub_one_of_pos (x := 199 / 60 * y) (by positivity)
    have h2 := Real.log_mul (by norm_num : (199 / 60 : ℝ) ≠ 0) (ne_of_gt hy0)
    linarith
  have hc := AppF.row_log_q199_60_lo
  have hy2 : y ^ 2 / 4 ≤ y / 12 := by nlinarith
  have hy3 : y ^ 3 / 4 ≤ y ^ 2 / 12 := by nlinarith
  have key : 0 ≤ y * (-Real.log y + (199 / 60) * y + 1 - 1599 / 500) := by
    apply mul_nonneg hy0.le
    linarith
  rw [heta, hpsi]
  nlinarith [key, hB', hy3]

/-! ## The strict anchor -/

/-- eq:anchorcomparison / app:anchor: `(39/40) psi (3/5) t ≤ eta t` on `[0,1]`. -/
theorem strict_anchor : StrictAnchorGoal := by
  intro t ht0 ht1
  rcases lt_or_le t (1 / 3) with h | h
  · exact anchor_caseC ht0 h.le
  · rcases lt_or_eq_of_le ht1 with h1 | h1
    · exact anchor_caseA h h1
    · rw [h1]
      unfold psi
      rw [eta_one]
      norm_num

end CK
