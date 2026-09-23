import CK.GainBounds
import CK.Constants

/-!
# Layer C, part 2: the entropy comparison on the correlation interval

Manuscript eq:comparison, Lemma lem:comparison, app:comparisons.

* `envelope_of_criterion` (eq:lambdacriterion): if `5/32 < λ` and
  `log(4λ - 5/8) + 2 - 2λ(2 - ρ²) ≥ 0`, then `λ·psi ρ t ≤ eta t` on `[0,1]`.
* `lambdaReq_le_lambdaBar` (eq:lambdabar): the required coefficient
  `eta ρ / ((1-ρ)Λ_ρ)` is at most `λ̄(ρ) = (log(2/(1-ρ)) + 3/4 + ρ/4) / (2Λ_ρ)`.
* `lambdaBar_convexOn`: `λ̄` is convex on `[3/5, 9/10]`.
* `entropy_comparison` (`EntropyComparisonGoal`): the four knots
  `ρ = 3/5, 3/4, 17/20, 9/10` of app:comparisons, the piecewise-linear majorant of `λ̄`
  through them, concavity of `log`, and the three cubic Bernstein certificates.
-/
noncomputable section
namespace CK

/-! ## The envelope criterion (eq:lambdacriterion) -/

/-- eq:lambdacriterion ⇒ envelope: if `5/32 < λ` and
`log(4λ − 5/8) + 2 − 2λ(2 − ρ²) ≥ 0` then `λ·psi ρ t ≤ eta t` on `[0,1]`. -/
theorem envelope_of_criterion {ρ lam : ℝ} (_hρ0 : 0 ≤ ρ) (_hρ1 : ρ ≤ 1) (hlam : 5 / 32 < lam)
    (hcrit : 0 ≤ Real.log (4 * lam - 5 / 8) + 2 - 2 * lam * (2 - ρ ^ 2)) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → lam * psi ρ t ≤ eta t := by
  intro t ht0 ht1
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · rw [h1, eta_one]
    unfold psi
    simp
  have hy0 : 0 < (1 - t) / 2 := by linarith
  have hy1 : (1 - t) / 2 ≤ 1 / 2 := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (1 - t) / 2 := ⟨_, rfl⟩
  rw [← hy] at hy0 hy1
  have heta : eta t = -y * Real.log y - (1 - y) * Real.log (1 - y) := by
    unfold eta
    rw [show (1 + t) / 2 = 1 - y by rw [hy]; ring, binaryEntropy_symm]
    rfl
  have hpsi : psi ρ t = 2 * y * (2 - ρ ^ 2 - 2 * y) := by
    unfold psi
    rw [hy]
    ring
  have h1y : 0 < 1 - y := by linarith
  have hB := neg_log_one_sub_ge' hy0.le hy1
  rw [div_le_iff₀ h1y] at hB
  have hB' : y - y ^ 2 / 2 - y ^ 3 / 4 ≤ -(1 - y) * Real.log (1 - y) := by linarith
  have hc : 0 < 4 * lam - 5 / 8 := by linarith
  have hlog : Real.log ((4 * lam - 5 / 8) * y) ≤ (4 * lam - 5 / 8) * y - 1 :=
    Real.log_le_sub_one_of_pos (mul_pos hc hy0)
  rw [Real.log_mul hc.ne' hy0.ne'] at hlog
  have hy3 : y ^ 3 / 4 ≤ y ^ 2 / 8 := by
    nlinarith [mul_nonneg (sq_nonneg y) (sub_nonneg.2 hy1)]
  have hkey : 0 ≤ y * (-Real.log y + 1 + (4 * lam - 5 / 8) * y - 2 * lam * (2 - ρ ^ 2)) := by
    apply mul_nonneg hy0.le
    linarith
  rw [heta, hpsi]
  nlinarith [hkey, hB', hy3]

/-! ## The required coefficient is at most `λ̄` (eq:lambdabar) -/

theorem one_le_lambdaDenom {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : 1 ≤ lambdaDenom ρ := by
  unfold lambdaDenom
  nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), sq_nonneg ρ]

/-- eq:lambdabar: the required coefficient is at most
`λ̄(ρ) = (log(2/(1−ρ)) + 3/4 + ρ/4)/(2Λ_ρ)`. -/
theorem lambdaReq_le_lambdaBar {ρ : ℝ} (h0 : 3 / 5 ≤ ρ) (h1 : ρ ≤ 9 / 10) :
    eta ρ / ((1 - ρ) * lambdaDenom ρ) ≤
      (Real.log (2 / (1 - ρ)) + 3 / 4 + ρ / 4) / (2 * lambdaDenom ρ) := by
  have hΛ : 1 ≤ lambdaDenom ρ := one_le_lambdaDenom (by linarith) (by linarith)
  have h1ρ : 0 < 1 - ρ := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (1 - ρ) / 2 := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; linarith
  have hy1 : y < 1 := by rw [hy]; linarith
  have heta : eta ρ = -y * Real.log y - (1 - y) * Real.log (1 - y) := by
    unfold eta
    rw [show (1 + ρ) / 2 = 1 - y by rw [hy]; ring, binaryEntropy_symm]
    rfl
  have hB := neg_log_one_sub_le hy0.le hy1
  rw [le_div_iff₀ (by linarith)] at hB
  have hlog : Real.log (2 / (1 - ρ)) = -Real.log y := by
    rw [hy, show (2 : ℝ) / (1 - ρ) = ((1 - ρ) / 2)⁻¹ by rw [inv_div], Real.log_inv]
  have hbound : eta ρ ≤ y * (Real.log (2 / (1 - ρ)) + 3 / 4 + ρ / 4) := by
    rw [heta, hlog]
    have hρ' : ρ / 4 = 1 / 4 - y / 2 := by rw [hy]; ring
    rw [hρ']
    nlinarith [hB]
  have hΛ2 : (0 : ℝ) ≤ 2 * lambdaDenom ρ := by linarith
  have h := mul_le_mul_of_nonneg_right hbound hΛ2
  have e : y * (Real.log (2 / (1 - ρ)) + 3 / 4 + ρ / 4) * (2 * lambdaDenom ρ)
      = (Real.log (2 / (1 - ρ)) + 3 / 4 + ρ / 4) * ((1 - ρ) * lambdaDenom ρ) := by
    rw [hy]
    ring
  rw [div_le_div_iff₀ (mul_pos h1ρ (by linarith)) (by linarith)]
  linarith [h, e]

/-! ## `λ̄` and its convexity on `[3/5, 9/10]` (app:comparisons) -/

/-- eq:lambdabar: `λ̄(ρ) = (log(2/(1−ρ)) + 3/4 + ρ/4)/(2Λ_ρ)`. -/
def lambdaBar (ρ : ℝ) : ℝ := (Real.log (2 / (1 - ρ)) + 3 / 4 + ρ / 4) / (2 * lambdaDenom ρ)

/-- The numerator `N(ρ) = log(2/(1−ρ)) + 3/4 + ρ/4` of `λ̄`. -/
def lbNum (ρ : ℝ) : ℝ := Real.log (2 / (1 - ρ)) + 3 / 4 + ρ / 4

theorem lbNum_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) : 0 ≤ lbNum ρ := by
  unfold lbNum
  have : 0 ≤ Real.log (2 / (1 - ρ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith)]
    linarith
  linarith

theorem hasDerivAt_lambdaDenom (ρ : ℝ) : HasDerivAt lambdaDenom (1 - (31 / 20) * ρ) ρ := by
  have h : HasDerivAt (fun v : ℝ => 1 + v - (31 / 40 : ℝ) * v ^ 2)
      (0 + 1 - (31 / 40 : ℝ) * ((2 : ℕ) * ρ ^ (2 - 1))) ρ :=
    ((hasDerivAt_const ρ (1 : ℝ)).add (hasDerivAt_id ρ)).sub
      ((hasDerivAt_pow 2 ρ).const_mul (31 / 40 : ℝ))
  exact h.congr_deriv (by norm_num; ring)

theorem hasDerivAt_lbNum {ρ : ℝ} (hρ : ρ < 1) : HasDerivAt lbNum (1 / (1 - ρ) + 1 / 4) ρ := by
  have hne : (1 - ρ : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < 1 - ρ).ne'
  have hsub : HasDerivAt (fun v : ℝ => 1 - v) (0 - 1) ρ :=
    (hasDerivAt_const ρ (1 : ℝ)).sub (hasDerivAt_id ρ)
  have hdiv : HasDerivAt (fun v : ℝ => 2 / (1 - v))
      ((0 * (1 - ρ) - 2 * (0 - 1)) / (1 - ρ) ^ 2) ρ :=
    (hasDerivAt_const ρ (2 : ℝ)).div hsub hne
  have hlog : HasDerivAt (fun v : ℝ => Real.log (2 / (1 - v)))
      (((0 * (1 - ρ) - 2 * (0 - 1)) / (1 - ρ) ^ 2) / (2 / (1 - ρ))) ρ :=
    hdiv.log (div_ne_zero two_ne_zero hne)
  have hlin : HasDerivAt (fun v : ℝ => v / 4) (1 / 4) ρ := (hasDerivAt_id ρ).div_const 4
  have h := (hlog.add_const (3 / 4)).add hlin
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `λ̄'` in quotient-rule form. -/
def lambdaBarD1 (ρ : ℝ) : ℝ :=
  ((1 / (1 - ρ) + 1 / 4) * (2 * lambdaDenom ρ) - lbNum ρ * (2 * (1 - (31 / 20) * ρ))) /
    (2 * lambdaDenom ρ) ^ 2

theorem hasDerivAt_lambdaBar {ρ : ℝ} (hρ : ρ < 1) (hΛ : lambdaDenom ρ ≠ 0) :
    HasDerivAt lambdaBar (lambdaBarD1 ρ) ρ := by
  have hd : HasDerivAt (fun v : ℝ => 2 * lambdaDenom v) (2 * (1 - (31 / 20) * ρ)) ρ :=
    (hasDerivAt_lambdaDenom ρ).const_mul 2
  exact (hasDerivAt_lbNum hρ).div hd (mul_ne_zero two_ne_zero hΛ)

/-- `λ̄''`: the quotient rule applied to `lambdaBarD1`. -/
def lambdaBarD2 (ρ : ℝ) : ℝ :=
  (((1 / (1 - ρ)) ^ 2 * (2 * lambdaDenom ρ) + (31 / 10) * lbNum ρ) * (2 * lambdaDenom ρ) ^ 2 -
      ((1 / (1 - ρ) + 1 / 4) * (2 * lambdaDenom ρ) - lbNum ρ * (2 * (1 - (31 / 20) * ρ))) *
        (2 * (2 * lambdaDenom ρ) * (2 * (1 - (31 / 20) * ρ)))) /
    ((2 * lambdaDenom ρ) ^ 2) ^ 2

theorem hasDerivAt_lambdaBarD1 {ρ : ℝ} (hρ : ρ < 1) (hΛ : lambdaDenom ρ ≠ 0) :
    HasDerivAt lambdaBarD1 (lambdaBarD2 ρ) ρ := by
  have hne : (1 - ρ : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < 1 - ρ).ne'
  have hsub : HasDerivAt (fun v : ℝ => 1 - v) (0 - 1) ρ :=
    (hasDerivAt_const ρ (1 : ℝ)).sub (hasDerivAt_id ρ)
  have hw : HasDerivAt (fun v : ℝ => 1 / (1 - v))
      ((0 * (1 - ρ) - 1 * (0 - 1)) / (1 - ρ) ^ 2) ρ :=
    (hasDerivAt_const ρ (1 : ℝ)).div hsub hne
  have hw' := hw.add_const (1 / 4)
  have hd : HasDerivAt (fun v : ℝ => 2 * lambdaDenom v) (2 * (1 - (31 / 20) * ρ)) ρ :=
    (hasDerivAt_lambdaDenom ρ).const_mul 2
  have hL : HasDerivAt (fun v : ℝ => 2 * (1 - (31 / 20) * v)) (2 * (0 - (31 / 20) * 1)) ρ :=
    ((hasDerivAt_const ρ (1 : ℝ)).sub ((hasDerivAt_id ρ).const_mul (31 / 20))).const_mul 2
  have hU := (hw'.mul hd).sub ((hasDerivAt_lbNum hρ).mul hL)
  have hV : HasDerivAt (fun v : ℝ => (2 * lambdaDenom v) ^ 2)
      (2 * (2 * lambdaDenom ρ) * (2 * (1 - (31 / 20) * ρ))) ρ :=
    (hd.pow 2).congr_deriv (by norm_num)
  have hne2 : (2 * lambdaDenom ρ) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero two_ne_zero hΛ)
  have h := hU.div hV hne2
  refine h.congr_deriv ?_
  unfold lambdaBarD2
  field_simp
  ring

/-- Sign of the numerator of `λ̄''` (app:comparisons), with `w = 1/(1−ρ)`, `N = lbNum ρ`,
`Λ = Λ_ρ`, `Λ' = 1 − (31/20)ρ`: the expression equals `8Λ·[w²Λ² + (31/20)NΛ − 2(w+1/4)ΛΛ' + 2NΛ'²]`. -/
theorem D2_numer_nonneg {ρ w N Λ Λ' : ℝ} (hρ0 : 3 / 5 ≤ ρ) (hρ1 : ρ ≤ 9 / 10)
    (hw : w * (1 - ρ) = 1) (hN : 0 ≤ N)
    (hΛ : Λ = 1 + ρ - (31 / 40) * ρ ^ 2) (hΛ' : Λ' = 1 - (31 / 20) * ρ) :
    0 ≤ (w ^ 2 * (2 * Λ) + (31 / 10) * N) * (2 * Λ) ^ 2 -
      ((w + 1 / 4) * (2 * Λ) - N * (2 * Λ')) * (2 * (2 * Λ) * (2 * Λ')) := by
  have hΛ54 : 5 / 4 ≤ Λ := by
    rw [hΛ]
    nlinarith [mul_nonneg (sub_nonneg.2 hρ0) (sub_nonneg.2 hρ1)]
  have h1ρ : 0 < 1 - ρ := by linarith
  have hwpos : 0 < w := by nlinarith [hw, h1ρ]
  have hw52 : 5 / 2 ≤ w := by nlinarith [mul_nonneg hwpos.le (sub_nonneg.2 hρ0)]
  have t2 : 0 ≤ (31 / 20) * N * Λ := mul_nonneg (mul_nonneg (by norm_num) hN) (by linarith)
  have t4 : 0 ≤ 2 * N * Λ' ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hN) (sq_nonneg _)
  have hE : 0 ≤ w ^ 2 * Λ ^ 2 + (31 / 20) * N * Λ - 2 * (w + 1 / 4) * Λ * Λ' + 2 * N * Λ' ^ 2 := by
    rcases le_or_lt Λ' 0 with hneg | hpos
    · have t1 : 0 ≤ w ^ 2 * Λ ^ 2 := by positivity
      have t3 : 0 ≤ 2 * (w + 1 / 4) * Λ * (-Λ') :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      nlinarith [t1, t2, t3, t4]
    · have hρ' : ρ < 20 / 31 := by rw [hΛ'] at hpos; linarith
      have hwub : w < 31 / 11 := by nlinarith [mul_lt_mul_of_pos_left hρ' hwpos]
      have hΛ'ub : Λ' ≤ 7 / 100 := by rw [hΛ']; linarith
      have hA : 0 ≤ w ^ 2 * Λ - 2 * (w + 1 / 4) * Λ' := by
        have hw2 : 25 / 4 ≤ w ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 hw52) (by linarith : (0 : ℝ) ≤ w + 5 / 2)]
        have hh1 : 25 / 4 * (5 / 4) ≤ w ^ 2 * Λ :=
          mul_le_mul hw2 hΛ54 (by norm_num) (by positivity)
        have hh2 : 2 * (w + 1 / 4) * Λ' ≤ 2 * (31 / 11 + 1 / 4) * (7 / 100) :=
          mul_le_mul (by linarith) hΛ'ub hpos.le (by norm_num)
        linarith
      have t5 : 0 ≤ Λ * (w ^ 2 * Λ - 2 * (w + 1 / 4) * Λ') := mul_nonneg (by linarith) hA
      nlinarith [t2, t4, t5]
  have e : (w ^ 2 * (2 * Λ) + (31 / 10) * N) * (2 * Λ) ^ 2 -
      ((w + 1 / 4) * (2 * Λ) - N * (2 * Λ')) * (2 * (2 * Λ) * (2 * Λ'))
      = 8 * Λ * (w ^ 2 * Λ ^ 2 + (31 / 20) * N * Λ - 2 * (w + 1 / 4) * Λ * Λ' + 2 * N * Λ' ^ 2) := by
    ring
  rw [e]
  exact mul_nonneg (by linarith) hE

theorem lambdaBarD2_nonneg {ρ : ℝ} (h0 : 3 / 5 ≤ ρ) (h1 : ρ ≤ 9 / 10) : 0 ≤ lambdaBarD2 ρ := by
  unfold lambdaBarD2
  refine div_nonneg ?_ (by positivity)
  exact D2_numer_nonneg h0 h1 (one_div_mul_cancel (by linarith : (0 : ℝ) < 1 - ρ).ne')
    (lbNum_nonneg (by linarith) (by linarith)) rfl rfl

/-- app:comparisons: `λ̄` is convex on `[3/5, 9/10]`. -/
theorem lambdaBar_convexOn : ConvexOn ℝ (Set.Icc (3 / 5 : ℝ) (9 / 10)) lambdaBar := by
  have hΛne : ∀ x : ℝ, 3 / 5 ≤ x → x ≤ 9 / 10 → lambdaDenom x ≠ 0 := fun x hx0 hx1 =>
    (lt_of_lt_of_le one_pos (one_le_lambdaDenom (by linarith) (by linarith))).ne'
  apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _)
  · intro x hx
    exact (hasDerivAt_lambdaBar (by linarith [hx.2])
      (hΛne x hx.1 hx.2)).continuousAt.continuousWithinAt
  · rw [interior_Icc]
    intro x hx
    exact (hasDerivAt_lambdaBar (by linarith [hx.2])
      (hΛne x hx.1.le hx.2.le)).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    have hmono : MonotoneOn lambdaBarD1 (Set.Ioo (3 / 5 : ℝ) (9 / 10)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ioo _ _)
      · intro x hx
        exact (hasDerivAt_lambdaBarD1 (by linarith [hx.2])
          (hΛne x hx.1.le hx.2.le)).continuousAt.continuousWithinAt
      · rw [interior_Ioo]
        intro x hx
        exact (hasDerivAt_lambdaBarD1 (by linarith [hx.2])
          (hΛne x hx.1.le hx.2.le)).differentiableAt.differentiableWithinAt
      · rw [interior_Ioo]
        intro x hx
        rw [(hasDerivAt_lambdaBarD1 (by linarith [hx.2]) (hΛne x hx.1.le hx.2.le)).deriv]
        exact lambdaBarD2_nonneg hx.1.le hx.2.le
    intro a ha b hb hab
    rw [(hasDerivAt_lambdaBar (by linarith [ha.2]) (hΛne a ha.1.le ha.2.le)).deriv,
      (hasDerivAt_lambdaBar (by linarith [hb.2]) (hΛne b hb.1.le hb.2.le)).deriv]
    exact hmono ha hb hab

/-! ## The knots `ρ_j = 3/5, 3/4, 17/20, 9/10` (app:comparisons, App. F rows) -/

theorem lambdaBar_lt_knot0 : lambdaBar (3 / 5) < 19 / 20 := by
  have k := AppF.knot_rho_3_5
  unfold lambdaBar lambdaDenom
  rw [div_lt_iff₀ (by norm_num)]
  linarith

theorem lambdaBar_lt_knot1 : lambdaBar (3 / 4) < 287 / 250 := by
  have k := AppF.knot_rho_3_4
  unfold lambdaBar lambdaDenom
  rw [div_lt_iff₀ (by norm_num)]
  linarith

theorem lambdaBar_lt_knot2 : lambdaBar (17 / 20) < 1377 / 1000 := by
  have k := AppF.knot_rho_17_20
  unfold lambdaBar lambdaDenom
  rw [div_lt_iff₀ (by norm_num)]
  linarith

theorem lambdaBar_lt_knot3 : lambdaBar (9 / 10) < 1561 / 1000 := by
  have k := AppF.knot_rho_9_10
  unfold lambdaBar lambdaDenom
  rw [div_lt_iff₀ (by norm_num)]
  linarith

theorem s_knot0 : (11553 / 10000 : ℝ) ≤ Real.log (4 * (19 / 20) - 5 / 8) := by
  rw [show (4 * (19 / 20 : ℝ) - 5 / 8) = 127 / 40 by norm_num]
  exact AppF.row_log_q127_40_lo.le

theorem s_knot1 : (689 / 500 : ℝ) ≤ Real.log (4 * (287 / 250) - 5 / 8) := by
  rw [show (4 * (287 / 250 : ℝ) - 5 / 8) = 3967 / 1000 by norm_num]
  exact AppF.row_log_q3967_1000_lo.le

theorem s_knot2 : (15857 / 10000 : ℝ) ≤ Real.log (4 * (1377 / 1000) - 5 / 8) := by
  rw [show (4 * (1377 / 1000 : ℝ) - 5 / 8) = 4883 / 1000 by norm_num]
  exact AppF.row_log_q4883_1000_lo.le

theorem s_knot3 : (17261 / 10000 : ℝ) ≤ Real.log (4 * (1561 / 1000) - 5 / 8) := by
  rw [show (4 * (1561 / 1000 : ℝ) - 5 / 8) = 5619 / 1000 by norm_num]
  exact AppF.row_log_q5619_1000_lo.le

/-- Bernstein certificate on `[3/5, 3/4]`: coefficients
`393/10000, 829/75000, 1249/60000, 31/400`. -/
theorem cubic0 (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ (1 - z) * (11553 / 10000) + z * (689 / 500) + 2 -
      2 * ((1 - z) * (19 / 20) + z * (287 / 250)) * (2 - ((1 - z) * (3 / 5) + z * (3 / 4)) ^ 2) := by
  have h1z : 0 ≤ 1 - z := by linarith
  nlinarith [pow_nonneg h1z 3, mul_nonneg hz0 (pow_nonneg h1z 2),
    mul_nonneg (pow_nonneg hz0 2) h1z, pow_nonneg hz0 3]

/-- Bernstein certificate on `[3/4, 17/20]`: coefficients
`31/400, 1683/40000, 11161/300000, 13493/200000`. -/
theorem cubic1 (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ (1 - z) * (689 / 500) + z * (15857 / 10000) + 2 -
      2 * ((1 - z) * (287 / 250) + z * (1377 / 1000)) *
        (2 - ((1 - z) * (3 / 4) + z * (17 / 20)) ^ 2) := by
  have h1z : 0 ≤ 1 - z := by linarith
  nlinarith [pow_nonneg h1z 3, mul_nonneg hz0 (pow_nonneg h1z 2),
    mul_nonneg (pow_nonneg hz0 2) h1z, pow_nonneg hz0 3]

/-- Bernstein certificate on `[17/20, 9/10]`: coefficients
`13493/200000, 21353/600000, 493/30000, 273/25000`. -/
theorem cubic2 (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ (1 - z) * (15857 / 10000) + z * (17261 / 10000) + 2 -
      2 * ((1 - z) * (1377 / 1000) + z * (1561 / 1000)) *
        (2 - ((1 - z) * (17 / 20) + z * (9 / 10)) ^ 2) := by
  have h1z : 0 ≤ 1 - z := by linarith
  nlinarith [pow_nonneg h1z 3, mul_nonneg hz0 (pow_nonneg h1z 2),
    mul_nonneg (pow_nonneg hz0 2) h1z, pow_nonneg hz0 3]

/-- One segment `[ρ0, ρ1]` of app:comparisons: with `λ` affine through `(ρ0, l0)`, `(ρ1, l1)`,
convexity of `λ̄` gives `λ̄(ρ) ≤ λ`, and concavity of `log` plus the cubic certificate give
the criterion eq:lambdacriterion at `λ`. -/
theorem segment_criterion {ρ0 ρ1 l0 l1 s0 s1 ρ : ℝ} (hρ0 : ρ0 ≤ ρ) (hρ1 : ρ ≤ ρ1)
    (hlt : ρ0 < ρ1) (hseg0 : 3 / 5 ≤ ρ0) (hseg1 : ρ1 ≤ 9 / 10)
    (hl0 : 5 / 32 < l0) (hl1 : 5 / 32 < l1)
    (hs0 : s0 ≤ Real.log (4 * l0 - 5 / 8)) (hs1 : s1 ≤ Real.log (4 * l1 - 5 / 8))
    (hb0 : lambdaBar ρ0 ≤ l0) (hb1 : lambdaBar ρ1 ≤ l1)
    (hP : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      0 ≤ (1 - z) * s0 + z * s1 + 2 -
        2 * ((1 - z) * l0 + z * l1) * (2 - ((1 - z) * ρ0 + z * ρ1) ^ 2)) :
    ∃ lam : ℝ, lambdaBar ρ ≤ lam ∧ 5 / 32 < lam ∧
      0 ≤ Real.log (4 * lam - 5 / 8) + 2 - 2 * lam * (2 - ρ ^ 2) := by
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = (ρ - ρ0) / (ρ1 - ρ0) := ⟨_, rfl⟩
  have hd : 0 < ρ1 - ρ0 := by linarith
  have hd' : ρ1 - ρ0 ≠ 0 := hd.ne'
  have hz0 : 0 ≤ z := by rw [hz]; exact div_nonneg (by linarith) hd.le
  have hz1 : z ≤ 1 := by rw [hz, div_le_one hd]; linarith
  have h1z : 0 ≤ 1 - z := by linarith
  have hρ : ρ = (1 - z) * ρ0 + z * ρ1 := by
    rw [hz]
    field_simp
    ring
  refine ⟨(1 - z) * l0 + z * l1, ?_, ?_, ?_⟩
  · have hx0 : ρ0 ∈ Set.Icc (3 / 5 : ℝ) (9 / 10) := ⟨hseg0, by linarith⟩
    have hx1 : ρ1 ∈ Set.Icc (3 / 5 : ℝ) (9 / 10) := ⟨by linarith, hseg1⟩
    have hc := lambdaBar_convexOn.2 hx0 hx1 h1z hz0 (by ring)
    simp only [smul_eq_mul] at hc
    rw [← hρ] at hc
    calc lambdaBar ρ ≤ (1 - z) * lambdaBar ρ0 + z * lambdaBar ρ1 := hc
      _ ≤ (1 - z) * l0 + z * l1 :=
        add_le_add (mul_le_mul_of_nonneg_left hb0 h1z) (mul_le_mul_of_nonneg_left hb1 hz0)
  · rcases le_total l0 l1 with h | h
    · nlinarith [mul_nonneg hz0 (sub_nonneg.2 h)]
    · nlinarith [mul_nonneg h1z (sub_nonneg.2 h)]
  · have hx0 : 4 * l0 - 5 / 8 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.2 (by linarith)
    have hx1 : 4 * l1 - 5 / 8 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.2 (by linarith)
    have hconc := strictConcaveOn_log_Ioi.concaveOn.2 hx0 hx1 h1z hz0 (by ring)
    simp only [smul_eq_mul] at hconc
    have heq : (1 - z) * (4 * l0 - 5 / 8) + z * (4 * l1 - 5 / 8) =
        4 * ((1 - z) * l0 + z * l1) - 5 / 8 := by ring
    rw [heq] at hconc
    have hP' := hP z hz0 hz1
    rw [← hρ] at hP'
    have e0 := mul_le_mul_of_nonneg_left hs0 h1z
    have e1 := mul_le_mul_of_nonneg_left hs1 hz0
    linarith

/-! ## The comparison (eq:comparison, Lemma lem:comparison) -/

/-- eq:comparison: for `3/5 ≤ ρ ≤ 9/10` and `0 ≤ t ≤ 1`,
`eta ρ / ((1−ρ)Λ_ρ) · psi ρ t ≤ eta t`. -/
theorem entropy_comparison : EntropyComparisonGoal := by
  intro ρ t h0 h1 ht0 ht1
  have hknot : ∃ lam : ℝ, lambdaBar ρ ≤ lam ∧ 5 / 32 < lam ∧
      0 ≤ Real.log (4 * lam - 5 / 8) + 2 - 2 * lam * (2 - ρ ^ 2) := by
    rcases le_or_lt ρ (3 / 4) with hA | hA
    · exact segment_criterion h0 hA (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) s_knot0 s_knot1 lambdaBar_lt_knot0.le lambdaBar_lt_knot1.le cubic0
    · rcases le_or_lt ρ (17 / 20) with hB | hB
      · exact segment_criterion hA.le hB (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) s_knot1 s_knot2 lambdaBar_lt_knot1.le lambdaBar_lt_knot2.le cubic1
      · exact segment_criterion hB.le h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) s_knot2 s_knot3 lambdaBar_lt_knot2.le lambdaBar_lt_knot3.le cubic2
  obtain ⟨lam, hreq, hlam, hcrit⟩ := hknot
  have henv := envelope_of_criterion (by linarith) (by linarith) hlam hcrit t ht0 ht1
  have hpsi : 0 ≤ psi ρ t := by
    unfold psi
    apply mul_nonneg (by linarith)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ρ) (sub_nonneg.2 h1)]
  have hreq' : eta ρ / ((1 - ρ) * lambdaDenom ρ) ≤ lam :=
    le_trans (lambdaReq_le_lambdaBar h0 h1) hreq
  calc eta ρ / ((1 - ρ) * lambdaDenom ρ) * psi ρ t ≤ lam * psi ρ t :=
        mul_le_mul_of_nonneg_right hreq' hpsi
    _ ≤ eta t := henv

end CK
