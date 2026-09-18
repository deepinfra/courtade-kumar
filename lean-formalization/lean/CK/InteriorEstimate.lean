import CK.GainBounds
import CK.Constants

/-!
# Layer C, part 2: the interior centered estimate (eq:interiorproduct, app:interior)

`K₀M₀ − ℓ² ≥ (1999/1250000)·p·t²` for `0 < t ≤ 22/25`, `0 < p ≤ 1/20`, where
`K₀ = eta((1-2p)t) − eta t`, `M₀ = eta((1-2p)t)`, `ℓ = h(p)·t`.

Route (app:interior): with `c(t) = 2·atanhLog((19/20)t) = ln((1+(19/20)t)/(1−(19/20)t))`,
* `gain_integral` + monotonicity of `atanhLog` give `K₀ ≥ p t c(t)`;
* `h(p) ≤ p(ln(1/p)+1)` (`binaryEntropy_le_mul`) bounds `ℓ²`;
* the table bound `(c/t)·eta t + c²/20 ≥ 4/5` on `(0, 22/25]` (five interval cases, using the
  rational rows of `CK.AppF`);
* the noise profile `ψ(p) = p(ln(1/p)+1)² − p c²` is nondecreasing on `(0, 1/20]`, so the
  worst case is `p = 1/20`.
-/
noncomputable section
namespace CK

/-! ## The manuscript's `c(t)` -/

/-- `c(t) = ln((1+(19/20)t)/(1−(19/20)t)) = 2·atanhLog((19/20)t)`. -/
def cInt (t : ℝ) : ℝ := 2 * atanhLog (19 / 20 * t)

theorem cInt_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : 0 ≤ cInt t := by
  unfold cInt
  have := atanhLog_nonneg (u := 19 / 20 * t) (by linarith) (by linarith)
  linarith

theorem cInt_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) : cInt s ≤ cInt t := by
  unfold cInt
  have := atanhLog_mono (r := 19 / 20 * s) (s := 19 / 20 * t) (by linarith) (by linarith)
    (by linarith)
  linarith

/-- `c(t) ≥ (19/10) t`, from `atanhLog u ≥ u`. -/
theorem cInt_ge_lin {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : 19 / 10 * t ≤ cInt t := by
  unfold cInt
  have := le_atanhLog (u := 19 / 20 * t) (by linarith) (by linarith)
  linarith

/-- `c(t)/t` is nondecreasing: `t·c(s) ≤ s·c(t)` for `0 < s ≤ t < 1`. -/
theorem cInt_div_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < 1) :
    t * cInt s ≤ s * cInt t := by
  unfold cInt
  have h := atanhLog_div_le (a := 19 / 20 * s) (b := 19 / 20 * t) (by positivity) (by linarith)
    (by linarith)
  have ht0 : 0 < t := lt_of_lt_of_le hs hst
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at h
  linarith

theorem cInt_eq_log {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    cInt t = Real.log ((1 + 19 / 20 * t) / (1 - 19 / 20 * t)) := by
  unfold cInt atanhLog
  rw [Real.log_div (by linarith : (1 + 19 / 20 * t : ℝ) ≠ 0)
    (by linarith : (1 - 19 / 20 * t : ℝ) ≠ 0)]
  ring

theorem cInt_half : cInt (1 / 2) = Real.log (59 / 21) := by
  rw [cInt_eq_log (by norm_num) (by norm_num)]
  norm_num

theorem cInt_3_4 : cInt (3 / 4) = Real.log (137 / 23) := by
  rw [cInt_eq_log (by norm_num) (by norm_num)]
  norm_num

theorem cInt_4_5 : cInt (4 / 5) = Real.log (22 / 3) := by
  rw [cInt_eq_log (by norm_num) (by norm_num)]
  norm_num

theorem cInt_21_25 : cInt (21 / 25) = Real.log (899 / 101) := by
  rw [cInt_eq_log (by norm_num) (by norm_num)]
  norm_num

theorem cInt_22_25 : cInt (22 / 25) = Real.log (459 / 41) := by
  rw [cInt_eq_log (by norm_num) (by norm_num)]
  norm_num

/-! ## `eta` at the knots, as entropies of small rationals -/

theorem eta_half : eta (1 / 2) = binaryEntropy (1 / 4) := by
  unfold eta
  rw [show ((1 + 1 / 2) / 2 : ℝ) = 1 - 1 / 4 by norm_num, binaryEntropy_symm]

theorem eta_3_4 : eta (3 / 4) = binaryEntropy (1 / 8) := by
  unfold eta
  rw [show ((1 + 3 / 4) / 2 : ℝ) = 1 - 1 / 8 by norm_num, binaryEntropy_symm]

theorem eta_4_5 : eta (4 / 5) = binaryEntropy (1 / 10) := by
  unfold eta
  rw [show ((1 + 4 / 5) / 2 : ℝ) = 1 - 1 / 10 by norm_num, binaryEntropy_symm]

theorem eta_21_25 : eta (21 / 25) = binaryEntropy (2 / 25) := by
  unfold eta
  rw [show ((1 + 21 / 25) / 2 : ℝ) = 1 - 2 / 25 by norm_num, binaryEntropy_symm]

theorem eta_22_25 : eta (22 / 25) = binaryEntropy (3 / 50) := by
  unfold eta
  rw [show ((1 + 22 / 25) / 2 : ℝ) = 1 - 3 / 50 by norm_num, binaryEntropy_symm]

/-! ## The table bound `T(t) = (c/t)·eta t + c²/20 ≥ 4/5` on `(0, 22/25]` (multiplied by `t`) -/

theorem table_bound {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 22 / 25) :
    4 / 5 * t ≤ cInt t * eta t + t * cInt t ^ 2 / 20 := by
  have ht1' : t < 1 := by linarith
  have hc0 : 0 ≤ cInt t := cInt_nonneg ht0.le ht1'
  rcases le_or_lt t (1 / 2) with h1 | h1
  · -- (0, 1/2]: c ≥ (19/10)t, eta ≥ 11/20
    have hcJ := cInt_ge_lin ht0.le ht1'
    have hJ : 11 / 20 ≤ eta t := by
      have := eta_le_eta ht0.le h1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
      rw [eta_half] at this
      linarith [AppF.row_h_1_4_lo]
    nlinarith [mul_le_mul_of_nonneg_left hJ hc0,
      mul_le_mul_of_nonneg_right hcJ (by norm_num : (0 : ℝ) ≤ 11 / 20),
      mul_nonneg ht0.le (sq_nonneg (cInt t))]
  rcases le_or_lt t (3 / 4) with h2 | h2
  · -- [1/2, 3/4]: c ≥ 2t, c ≥ 1, eta ≥ 3/8
    have hc : 1 ≤ cInt t := by
      have := cInt_mono (by norm_num : (0 : ℝ) ≤ 1 / 2) h1.le ht1'
      rw [cInt_half] at this
      linarith [AppF.row_log_q59_21_lo]
    have hcJ : 2 * t ≤ cInt t := by
      have := cInt_div_mono (by norm_num : (0 : ℝ) < 1 / 2) h1.le ht1'
      rw [cInt_half] at this
      nlinarith [mul_le_mul_of_nonneg_left (le_of_lt AppF.row_log_q59_21_lo) ht0.le]
    have hJ : 3 / 8 ≤ eta t := by
      have := eta_le_eta ht0.le h2 (by norm_num : (3 / 4 : ℝ) ≤ 1)
      rw [eta_3_4] at this
      linarith [AppF.row_h_1_8_lo]
    nlinarith [mul_le_mul_of_nonneg_left hJ hc0,
      mul_le_mul_of_nonneg_right hcJ (by norm_num : (0 : ℝ) ≤ 3 / 8),
      mul_le_mul_of_nonneg_left (mul_le_mul hc hc (by norm_num) hc0) ht0.le]
  rcases le_or_lt t (4 / 5) with h3 | h3
  · -- [3/4, 4/5]: c ≥ (7/3)t, c ≥ 7/4, eta ≥ 8/25
    have hc : 7 / 4 ≤ cInt t := by
      have := cInt_mono (by norm_num : (0 : ℝ) ≤ 3 / 4) h2.le ht1'
      rw [cInt_3_4] at this
      linarith [AppF.row_log_q137_23_lo]
    have hcJ : 7 / 3 * t ≤ cInt t := by
      have := cInt_div_mono (by norm_num : (0 : ℝ) < 3 / 4) h2.le ht1'
      rw [cInt_3_4] at this
      nlinarith [mul_le_mul_of_nonneg_left (le_of_lt AppF.row_log_q137_23_lo) ht0.le]
    have hJ : 8 / 25 ≤ eta t := by
      have := eta_le_eta ht0.le h3 (by norm_num : (4 / 5 : ℝ) ≤ 1)
      rw [eta_4_5] at this
      linarith [AppF.row_h_1_10_lo]
    nlinarith [mul_le_mul_of_nonneg_left hJ hc0,
      mul_le_mul_of_nonneg_right hcJ (by norm_num : (0 : ℝ) ≤ 8 / 25),
      mul_le_mul_of_nonneg_left (mul_le_mul hc hc (by norm_num) hc0) ht0.le]
  rcases le_or_lt t (21 / 25) with h4 | h4
  · -- [4/5, 21/25]: c ≥ (39/16)t, c ≥ 39/20, eta ≥ 11/40
    have hc : 39 / 20 ≤ cInt t := by
      have := cInt_mono (by norm_num : (0 : ℝ) ≤ 4 / 5) h3.le ht1'
      rw [cInt_4_5] at this
      linarith [AppF.row_log_q22_3_lo]
    have hcJ : 39 / 16 * t ≤ cInt t := by
      have := cInt_div_mono (by norm_num : (0 : ℝ) < 4 / 5) h3.le ht1'
      rw [cInt_4_5] at this
      nlinarith [mul_le_mul_of_nonneg_left (le_of_lt AppF.row_log_q22_3_lo) ht0.le]
    have hJ : 11 / 40 ≤ eta t := by
      have := eta_le_eta ht0.le h4 (by norm_num : (21 / 25 : ℝ) ≤ 1)
      rw [eta_21_25] at this
      linarith [AppF.row_h_2_25_lo]
    nlinarith [mul_le_mul_of_nonneg_left hJ hc0,
      mul_le_mul_of_nonneg_right hcJ (by norm_num : (0 : ℝ) ≤ 11 / 40),
      mul_le_mul_of_nonneg_left (mul_le_mul hc hc (by norm_num) hc0) ht0.le]
  · -- [21/25, 22/25]: c ≥ (325/126)t, c ≥ 13/6, eta ≥ 9/40
    have hc : 13 / 6 ≤ cInt t := by
      have := cInt_mono (by norm_num : (0 : ℝ) ≤ 21 / 25) h4.le ht1'
      rw [cInt_21_25] at this
      linarith [AppF.row_log_q899_101_lo]
    have hcJ : 325 / 126 * t ≤ cInt t := by
      have := cInt_div_mono (by norm_num : (0 : ℝ) < 21 / 25) h4.le ht1'
      rw [cInt_21_25] at this
      nlinarith [mul_le_mul_of_nonneg_left (le_of_lt AppF.row_log_q899_101_lo) ht0.le]
    have hJ : 9 / 40 ≤ eta t := by
      have := eta_le_eta ht0.le ht1 (by norm_num : (22 / 25 : ℝ) ≤ 1)
      rw [eta_22_25] at this
      linarith [AppF.row_h_3_50_lo]
    nlinarith [mul_le_mul_of_nonneg_left hJ hc0,
      mul_le_mul_of_nonneg_right hcJ (by norm_num : (0 : ℝ) ≤ 9 / 40),
      mul_le_mul_of_nonneg_left (mul_le_mul hc hc (by norm_num) hc0) ht0.le]

/-! ## The noise profile `ψ(p) = p(ln(1/p)+1)² − p c²` is nondecreasing on `(0, 1/20]` -/

theorem hasDerivAt_psiInt (c : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y * (1 - Real.log y) ^ 2 - y * c ^ 2)
      (Real.log x ^ 2 - 1 - c ^ 2) x := by
  have hl : HasDerivAt (fun y : ℝ => 1 - Real.log y) (0 - x⁻¹) x :=
    (hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_log hx.ne')
  have h1 : HasDerivAt (fun y : ℝ => y * (1 - Real.log y) ^ 2)
      (1 * (1 - Real.log x) ^ 2
        + x * (((2 : ℕ) : ℝ) * (1 - Real.log x) ^ (2 - 1) * (0 - x⁻¹))) x :=
    (hasDerivAt_id x).mul (hl.pow 2)
  have h2 : HasDerivAt (fun y : ℝ => y * c ^ 2) (1 * c ^ 2) x :=
    (hasDerivAt_id x).mul_const _
  have := h1.sub h2
  convert this using 1
  push_cast
  norm_num
  field_simp
  ring

/-- `ψ(p) ≤ ψ(1/20)` for `0 < p ≤ 1/20` and `0 ≤ c ≤ 5/2` (written with `ln(1/p) = −ln p`). -/
theorem psi_mono {c p : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 5 / 2) (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) :
    p * (1 - Real.log p) ^ 2 - p * c ^ 2 ≤ 1 / 20 * (1 + Real.log 20) ^ 2 - c ^ 2 / 20 := by
  have hmono : MonotoneOn (fun x : ℝ => x * (1 - Real.log x) ^ 2 - x * c ^ 2)
      (Set.Icc p (1 / 20)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hp0 hx.1
      exact (hasDerivAt_psiInt c hx0).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro x hx
      have hx0 : 0 < x := lt_trans hp0 hx.1
      exact (hasDerivAt_psiInt c hx0).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hx0 : 0 < x := lt_trans hp0 hx.1
      rw [(hasDerivAt_psiInt c hx0).deriv]
      have hlog : Real.log x ≤ -Real.log 20 := by
        have := Real.log_le_log hx0 (le_of_lt hx.2)
        rwa [one_div, Real.log_inv] at this
      have h20 := AppF.row_log_q20_lo
      have hneg : 299 / 100 ≤ -Real.log x := by linarith
      nlinarith [mul_le_mul hneg hneg (by norm_num) (by linarith),
        mul_le_mul hc hc hc0 (by norm_num)]
  have h := hmono ⟨le_refl p, hp1⟩ ⟨hp1, le_refl _⟩ hp1
  simp only at h
  have e : Real.log (1 / 20 : ℝ) = -Real.log 20 := by rw [one_div, Real.log_inv]
  rw [e] at h
  linarith

/-! ## The interior centered estimate -/

/-- eq:interiorproduct: K₀M₀ − ℓ² ≥ (1999/1250000) p t² for 0 < t ≤ 22/25, 0 < p ≤ 1/20. -/
theorem interior_product {p t : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht0 : 0 < t)
    (ht1 : t ≤ 22 / 25) :
    1999 / 1250000 * p * t ^ 2 ≤
      (eta ((1 - 2 * p) * t) - eta t) * eta ((1 - 2 * p) * t) - (binaryEntropy p * t) ^ 2 := by
  have ht1' : t < 1 := by linarith
  have hpt : 0 ≤ p * t := by positivity
  have hpt2 : 0 ≤ p * t ^ 2 := by positivity
  -- Step 1: `K₀ ≥ p t c(t)`, and `c(t) ≥ 0`
  have hc0 : 0 ≤ cInt t := cInt_nonneg ht0.le ht1'
  have hK : p * t * cInt t ≤ eta ((1 - 2 * p) * t) - eta t := by
    have hg := gain_integral hp0 (by linarith) ht0 ht1'
    have hm := atanhLog_mono (r := 19 / 20 * t) (s := (1 - p) * t) (by linarith)
      (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 20 - p) ht0.le])
      (by nlinarith [mul_pos hp0 ht0])
    unfold cInt
    nlinarith [mul_le_mul_of_nonneg_left hm hpt]
  -- Step 2: `J₀ ≥ 0`, so `K₀M₀ ≥ (p t c)(p t c + J₀)`
  have hJ0 : 0 ≤ eta t := eta_nonneg (by linarith) ht1'.le
  have hptc : 0 ≤ p * t * cInt t := mul_nonneg hpt hc0
  have hKM : (p * t * cInt t) * (p * t * cInt t + eta t) ≤
      (eta ((1 - 2 * p) * t) - eta t) * ((eta ((1 - 2 * p) * t) - eta t) + eta t) :=
    mul_le_mul hK (by linarith) (by linarith) (by linarith)
  -- Step 3: `ℓ = h(p) t ≤ p t (ln(1/p) + 1)`
  have hℓ : binaryEntropy p ≤ p * (1 - Real.log p) := by
    have := binaryEntropy_le_mul hp0 (by linarith)
    rw [one_div, Real.log_inv] at this
    linarith
  have hℓ0 : 0 ≤ binaryEntropy p := binaryEntropy_nonneg' hp0.le (by linarith)
  have hℓ2 : (binaryEntropy p * t) ^ 2 ≤ (p * t * (1 - Real.log p)) ^ 2 := by
    have h1 : binaryEntropy p * t ≤ p * (1 - Real.log p) * t :=
      mul_le_mul_of_nonneg_right hℓ ht0.le
    have h0 : 0 ≤ binaryEntropy p * t := mul_nonneg hℓ0 ht0.le
    nlinarith [mul_le_mul h1 h1 h0 (le_trans h0 h1)]
  -- Step 4: the table bound
  have hT := table_bound ht0 ht1
  -- Step 5: worst noise `p = 1/20`, using `c(t) ≤ c(22/25) = ln(459/41) < 5/2`
  have hcle : cInt t ≤ 5 / 2 := by
    have := cInt_mono ht0.le ht1 (by norm_num : (22 / 25 : ℝ) < 1)
    rw [cInt_22_25] at this
    linarith [AppF.row_log_q459_41_hi]
  have hpsi := psi_mono hc0 hcle hp0 hp1
  -- Step 6: assemble, with `ln 20 < 749/250`
  have h20 := AppF.row_log_q20_hi
  have h20' : 0 ≤ 1 + Real.log 20 := by linarith [AppF.row_log_q20_lo]
  have h5 : (1 + Real.log 20) ^ 2 ≤ (999 / 250) ^ 2 := by nlinarith
  nlinarith [hKM, hℓ2, mul_le_mul_of_nonneg_left hpsi hpt2, mul_le_mul_of_nonneg_left hT hpt,
    mul_le_mul_of_nonneg_left h5 hpt2]

end CK
