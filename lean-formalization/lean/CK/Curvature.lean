import CK.EtaDeriv

/-!
# Layer B3: the curvature inequality (`CurvatureGoal`)

The manuscript's identity (eq:curvaturepositive) is an FTC evaluation of the
explicit primitive `psiCurv`: on `[x, y]`,

  `psiCurv x y u = -(u²-x²)(y²-u²)·atanhLog u / (2(1-x²)(1-y²)u)
                   - (curvature x + curvature y - 2 curvature u)·eta u - atanhLog u²`

whose derivative is the manuscript integrand pulled back to the `u`-coordinate:
nonnegative, by `atanhLog u ≥ u` and concavity of `wAux u = 2u·eta u - (1-u²)·atanhLog u`.
`psiCurv y - psiCurv x = curvatureGap x y`, so monotonicity gives the sign — no
integration theory required.
-/
noncomputable section
namespace CK

/-! ## The concave auxiliary `w` -/

def wAux (u : ℝ) : ℝ := 2 * u * eta u - (1 - u ^ 2) * atanhLog u

theorem wAux_zero : wAux 0 = 0 := by
  unfold wAux
  rw [atanhLog_zero]
  ring

theorem wAux_one : wAux 1 = 0 := by
  unfold wAux
  rw [eta_one]
  ring

theorem continuous_wAux : Continuous wAux := by
  have e : wAux = fun u : ℝ =>
      2 * u * eta u - ((1 - u) / 2 * ((1 + u) * Real.log (1 + u))
        - (1 + u) / 2 * ((1 - u) * Real.log (1 - u))) := by
    funext u
    unfold wAux atanhLog
    ring
  rw [e]
  refine Continuous.sub ((continuous_const.mul continuous_id).mul continuous_eta) (Continuous.sub ?_ ?_)
  · exact ((continuous_const.sub continuous_id).div_const 2).mul
      (Real.continuous_mul_log.comp (continuous_const.add continuous_id))
  · exact ((continuous_const.add continuous_id).div_const 2).mul
      (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))

theorem hasDerivAt_wAux {u : ℝ} (hu0 : -1 < u) (hu1 : u < 1) :
    HasDerivAt wAux (2 * eta u - 1) u := by
  have hne : (1 - u ^ 2 : ℝ) ≠ 0 := by nlinarith
  have hE := hasDerivAt_eta hu0 hu1
  have hA := hasDerivAt_atanhLog hu0 hu1
  have h1 : HasDerivAt (fun v : ℝ => 2 * v * eta v)
      ((2 * 1) * eta u + 2 * u * -atanhLog u) u := by
    have hid : HasDerivAt (fun v : ℝ => 2 * v) (2 * 1) u := (hasDerivAt_id u).const_mul 2
    exact hid.mul hE
  have h2 : HasDerivAt (fun v : ℝ => (1 - v ^ 2) * atanhLog v)
      ((0 - (2 : ℕ) * u ^ (2 - 1)) * atanhLog u + (1 - u ^ 2) * curvature u) u := by
    have hq : HasDerivAt (fun v : ℝ => 1 - v ^ 2) (0 - (2 : ℕ) * u ^ (2 - 1)) u :=
      (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_pow 2 u)
    exact hq.mul hA
  have := h1.sub h2
  convert this using 1
  unfold curvature
  field_simp
  ring

theorem wAux_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ wAux u := by
  rcases le_or_lt (1 / 2) (eta u) with hcase | hcase
  · -- `2*eta ≥ 1` up to `u`: `wAux` is nondecreasing on `[0, u]`
    have hmono : MonotoneOn wAux (Set.Icc 0 u) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) continuous_wAux.continuousOn
      · rw [interior_Icc]
        intro v hv
        exact (hasDerivAt_wAux (by linarith [hv.1]) (by linarith [hv.2])).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro v hv
        rw [(hasDerivAt_wAux (by linarith [hv.1]) (by linarith [hv.2])).deriv]
        have := eta_le_eta (le_of_lt hv.1) (le_of_lt hv.2) hu1
        linarith
    have := hmono ⟨le_refl 0, hu0⟩ ⟨hu0, le_refl u⟩ hu0
    rw [wAux_zero] at this
    exact this
  · -- `2*eta < 1` from `u` on: `wAux` is nonincreasing on `[u, 1]`
    have hanti : AntitoneOn wAux (Set.Icc u 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) continuous_wAux.continuousOn
      · rw [interior_Icc]
        intro v hv
        exact (hasDerivAt_wAux (by linarith [hv.1]) (by linarith [hv.2])).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro v hv
        rw [(hasDerivAt_wAux (by linarith [hv.1]) (by linarith [hv.2])).deriv]
        have := eta_le_eta hu0 (le_of_lt hv.1) (le_of_lt hv.2)
        linarith
    have := hanti ⟨le_refl u, hu1⟩ ⟨hu1, le_refl 1⟩ hu1
    rw [wAux_one] at this
    exact this

/-! ## The primitive of the curvature-defect integrand -/

def psiCurv (x y u : ℝ) : ℝ :=
  -((u ^ 2 - x ^ 2) * (y ^ 2 - u ^ 2) * atanhLog u / (2 * (1 - x ^ 2) * (1 - y ^ 2) * u))
    - (curvature x + curvature y - 2 * curvature u) * eta u - atanhLog u ^ 2

def psiCurvDeriv (x y u : ℝ) : ℝ :=
  (u ^ 2 - x ^ 2) * (y ^ 2 - u ^ 2) * ((1 + 3 * u ^ 2) * atanhLog u - u)
      / (2 * u ^ 2 * (1 - u ^ 2) * (1 - x ^ 2) * (1 - y ^ 2))
    + 2 * wAux u / (1 - u ^ 2) ^ 2

theorem hasDerivAt_psiCurv {x y u : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (psiCurv x y) (psiCurvDeriv x y u) u := by
  have hu0' : (-1 : ℝ) < u := by linarith
  have hA := hasDerivAt_atanhLog hu0' hu1
  have hE := hasDerivAt_eta hu0' hu1
  have hK := hasDerivAt_curvature hu0' hu1
  have hcx : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  have hcy : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  have hcu : (0 : ℝ) < 1 - u ^ 2 := by nlinarith
  have hP1 : HasDerivAt (fun v : ℝ => v ^ 2 - x ^ 2) (((2 : ℕ) : ℝ) * u ^ (2 - 1)) u :=
    (hasDerivAt_pow 2 u).sub_const _
  have hP2 : HasDerivAt (fun v : ℝ => y ^ 2 - v ^ 2) (-(((2 : ℕ) : ℝ) * u ^ (2 - 1))) u :=
    (hasDerivAt_pow 2 u).const_sub _
  have hnum := (hP1.mul hP2).mul hA
  have hden : HasDerivAt (fun v : ℝ => 2 * (1 - x ^ 2) * (1 - y ^ 2) * v)
      (2 * (1 - x ^ 2) * (1 - y ^ 2) * 1) u :=
    (hasDerivAt_id u).const_mul _
  have hdenne : 2 * (1 - x ^ 2) * (1 - y ^ 2) * u ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (mul_pos two_pos hcx) hcy) hu0)
  have hfrac := hnum.div hden hdenne
  have hmid := ((hK.const_mul 2).const_sub (curvature x + curvature y)).mul hE
  have hsq := hA.pow 2
  have hall := (hfrac.neg.sub hmid).sub hsq
  convert hall using 1
  unfold psiCurvDeriv wAux curvature
  push_cast
  norm_num
  field_simp
  ring

theorem psiCurvDeriv_nonneg {x y u : ℝ} (hx0 : 0 ≤ x) (hxu : x ≤ u) (huy : u ≤ y)
    (hy1 : y < 1) (hu0 : 0 < u) : 0 ≤ psiCurvDeriv x y u := by
  have hu1 : u < 1 := lt_of_le_of_lt huy hy1
  have hx1 : x < 1 := lt_of_le_of_lt hxu hu1
  have hcx : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  have hcy : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  have hcu : (0 : ℝ) < 1 - u ^ 2 := by nlinarith
  unfold psiCurvDeriv
  apply add_nonneg
  · apply div_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      · nlinarith
      · nlinarith
      · have h1 := le_atanhLog (le_of_lt hu0) hu1
        have h2 := atanhLog_nonneg (le_of_lt hu0) hu1
        nlinarith
    · have : (0 : ℝ) < 2 * u ^ 2 * (1 - u ^ 2) * (1 - x ^ 2) * (1 - y ^ 2) := by
        apply mul_pos (mul_pos (mul_pos _ hcu) hcx) hcy
        positivity
      linarith
  · apply div_nonneg
    · have := wAux_nonneg (le_of_lt hu0) (le_of_lt hu1)
      linarith
    · positivity

/-! ## The `x = 0` boundary: the same primitive, with the removable factor cancelled -/

def psiCurv0 (y u : ℝ) : ℝ :=
  -(u * (y ^ 2 - u ^ 2) * atanhLog u / (2 * (1 - y ^ 2)))
    - (curvature 0 + curvature y - 2 * curvature u) * eta u - atanhLog u ^ 2

theorem psiCurv_zero_eq {y : ℝ} (hy : (1 - y ^ 2 : ℝ) ≠ 0) : psiCurv 0 y = psiCurv0 y := by
  funext u
  unfold psiCurv psiCurv0
  by_cases hu : u = 0
  · subst hu
    rw [atanhLog_zero]
    norm_num
  · field_simp
    ring

theorem psiCurv0_continuousAt {y u : ℝ} (hu0 : -1 < u) (hu1 : u < 1) :
    ContinuousAt (psiCurv0 y) u := by
  have hA : ContinuousAt atanhLog u := (hasDerivAt_atanhLog hu0 hu1).continuousAt
  have hK : ContinuousAt curvature u := (hasDerivAt_curvature hu0 hu1).continuousAt
  unfold psiCurv0
  apply ContinuousAt.sub
  apply ContinuousAt.sub
  · apply ContinuousAt.neg
    apply ContinuousAt.div_const
    exact (continuousAt_id.mul (continuous_const.sub (continuous_pow 2)).continuousAt).mul hA
  · exact (continuousAt_const.sub (continuousAt_const.mul hK)).mul continuous_eta.continuousAt
  · exact hA.pow 2

/-! ## The curvature inequality -/

theorem curvature_identity : CurvatureGoal := by
  intro x y hx0 hxy hy1
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · have h : curvatureGap x x = 0 := by unfold curvatureGap; ring
    rw [h]
  have hy0 : 0 < y := lt_of_le_of_lt hx0 hlt
  have hx1 : x < 1 := lt_trans hlt hy1
  have hcy : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  rcases eq_or_lt_of_le hx0 with rfl | hx0'
  · -- x = 0
    have heq := psiCurv_zero_eq (y := y) hcy.ne'
    have hmono : MonotoneOn (psiCurv0 y) (Set.Icc 0 y) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · intro u hu
        exact (psiCurv0_continuousAt (by linarith [hu.1]) (by linarith [hu.2])).continuousWithinAt
      · rw [interior_Icc]
        intro u hu
        have h := hasDerivAt_psiCurv (x := 0) (y := y) (le_refl 0) (by norm_num)
          (le_of_lt hy0) hy1 hu.1 (by linarith [hu.2])
        rw [heq] at h
        exact h.differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro u hu
        have h := hasDerivAt_psiCurv (x := 0) (y := y) (le_refl 0) (by norm_num)
          (le_of_lt hy0) hy1 hu.1 (by linarith [hu.2])
        rw [heq] at h
        rw [h.deriv]
        exact psiCurvDeriv_nonneg (le_refl 0) (le_of_lt hu.1) (le_of_lt hu.2) hy1 hu.1
    have hle := hmono ⟨le_refl 0, le_of_lt hy0⟩ ⟨le_of_lt hy0, le_refl y⟩ (le_of_lt hy0)
    have hgap : curvatureGap 0 y = psiCurv0 y y - psiCurv0 y 0 := by
      unfold curvatureGap psiCurv0
      rw [atanhLog_zero]
      ring
    rw [hgap]
    linarith
  · -- 0 < x
    have hmono : MonotoneOn (psiCurv x y) (Set.Icc x y) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · intro u hu
        exact (hasDerivAt_psiCurv (le_of_lt hx0') hx1 (le_of_lt hy0) hy1
          (lt_of_lt_of_le hx0' hu.1) (lt_of_le_of_lt hu.2 hy1)).continuousAt.continuousWithinAt
      · rw [interior_Icc]
        intro u hu
        exact (hasDerivAt_psiCurv (le_of_lt hx0') hx1 (le_of_lt hy0) hy1
          (lt_trans hx0' hu.1) (lt_trans hu.2 hy1)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro u hu
        rw [(hasDerivAt_psiCurv (le_of_lt hx0') hx1 (le_of_lt hy0) hy1
          (lt_trans hx0' hu.1) (lt_trans hu.2 hy1)).deriv]
        exact psiCurvDeriv_nonneg hx0 (le_of_lt hu.1) (le_of_lt hu.2) hy1 (lt_trans hx0' hu.1)
    have hle := hmono ⟨le_refl x, le_of_lt hlt⟩ ⟨le_of_lt hlt, le_refl y⟩ (le_of_lt hlt)
    have hgap : curvatureGap x y = psiCurv x y y - psiCurv x y x := by
      unfold curvatureGap psiCurv
      ring
    rw [hgap]
    linarith

end CK
