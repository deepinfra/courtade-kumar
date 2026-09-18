import CK.EndpointCommon

/-!
# Endpoint regime `ε ≤ p` (manuscript app:rsmall, eq:endpointinterval, eq:gaindominance)

Setting: `0 < p ≤ 1/20`, `22/25 ≤ t < 1`, `ε = (1-t)/2 ≤ p`, `r = ε/p ∈ (0,1]`,
`L = log(1/p) ≥ 299/100`, `u_ε = log(1/ε) = L - log r`,
`α = L - log(1+2r) + 3/5`, `β = u_ε + 19/20`, `A = α + rβ`, `𝒬(d) = α + A d² - 2(L+1) d`.

* `endpoint_interval` : `q₀(d) ≥ (23/3600) p t` for `0 ≤ d ≤ 1/2` (eq:endpointinterval)
* `gain_dominance`    : `K₀ ≥ M₀/3` (eq:gaindominance)
-/
noncomputable section
namespace CK

/-- `log(1/ε) = log(1/p) - log r` with `ε = (1-t)/2`, `r = ε/p` (app:rsmall). -/
theorem log_inv_eps_eq {p t : ℝ} (hp0 : 0 < p) (ht1 : t < 1) :
    Real.log (1 / ((1 - t) / 2)) = Real.log (1 / p) - Real.log ((1 - t) / 2 / p) := by
  have he : 0 < (1 - t) / 2 := by linarith
  rw [Real.log_div one_ne_zero he.ne', Real.log_div one_ne_zero hp0.ne',
    Real.log_div he.ne' hp0.ne']
  ring

/-- `-r log r ≤ 1 - r` for `r > 0` (from `log(1/r) ≤ 1/r - 1`). -/
theorem neg_mul_log_le {r : ℝ} (hr0 : 0 < r) : -r * Real.log r ≤ 1 - r := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hr0)
  rw [Real.log_inv] at h
  have h2 := mul_le_mul_of_nonneg_left h hr0.le
  have h3 : r * (r⁻¹ - 1) = 1 - r := by
    rw [mul_sub, mul_inv_cancel₀ hr0.ne', mul_one]
  rw [h3] at h2
  linarith

/-- Tangent bound at `3`: `log(1+2r) ≤ log 3 + (2/3)(r-1)` for `r > 0`. -/
theorem log_one_add_two_mul_le_tangent {r : ℝ} (hr0 : 0 < r) :
    Real.log (1 + 2 * r) ≤ Real.log 3 + 2 / 3 * (r - 1) := by
  have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < 1 + 2 * r)
    (by norm_num : (0 : ℝ) < 3))
  rw [Real.log_div (by linarith : (0 : ℝ) < 1 + 2 * r).ne' (by norm_num : (3 : ℝ) ≠ 0)] at h
  linarith

/-- `1 ≤ -log r` for `0 < r ≤ 1/3` (since `log(1/r) ≥ log 3 > 13/12`). -/
theorem one_le_neg_log_of_le_third {r : ℝ} (hr0 : 0 < r) (hr3 : r ≤ 1 / 3) :
    1 ≤ -Real.log r := by
  have h3 : (3 : ℝ) ≤ 1 / r := by
    rw [le_div_iff₀ hr0]
    linarith
  have h := Real.log_le_log (by norm_num) h3
  rw [one_div, Real.log_inv] at h
  linarith [AppF.row_log_q3_lo]

/-- Pure-real core of eq:endpointinterval: `𝒬(d) ≥ 23/3600` on `[0, 1/2]` given the
elementary bounds on `r`, `L`, `log r`, `log(1+2r)` (app:rsmall). -/
theorem Q_ge_bound {r L lr l3 d : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hL : 299 / 100 ≤ L)
    (hlr0 : lr ≤ 0) (hlr1 : -r * lr ≤ 1 - r) (hl3_0 : 0 ≤ l3) (hl3_1 : l3 < 11 / 10)
    (hl3_2r : l3 ≤ 2 * r) (hl3_tan : l3 ≤ 11 / 10 + 2 / 3 * (r - 1))
    (hlr_case : r ≤ 1 / 3 → 1 ≤ -lr) (hd : d ≤ 1 / 2) :
    23 / 3600 ≤ (L - l3 + 3 / 5) + ((L - l3 + 3 / 5) + r * ((L - lr) + 19 / 20)) * d ^ 2
      - 2 * (L + 1) * d := by
  -- A = α + rβ ≥ 0
  have hβ : 0 ≤ (L - lr) + 19 / 20 := by linarith
  have hrβ : 0 ≤ r * ((L - lr) + 19 / 20) := mul_nonneg hr0.le hβ
  have hA : 0 ≤ (L - l3 + 3 / 5) + r * ((L - lr) + 19 / 20) := by linarith
  -- A ≤ 2(L+1)
  have hA2 : (L - l3 + 3 / 5) + r * ((L - lr) + 19 / 20) ≤ 2 * (L + 1) := by
    have h1 : 299 / 100 * (1 - r) ≤ L * (1 - r) := mul_le_mul_of_nonneg_right hL (by linarith)
    nlinarith [h1, hlr1, hl3_0]
  -- 𝒬(d) ≥ 𝒬(1/2) on [0, 1/2]
  have hstep : (L - l3 + 3 / 5) + ((L - l3 + 3 / 5) + r * ((L - lr) + 19 / 20)) * (1 / 2) ^ 2
      - 2 * (L + 1) * (1 / 2)
      ≤ (L - l3 + 3 / 5) + ((L - l3 + 3 / 5) + r * ((L - lr) + 19 / 20)) * d ^ 2
      - 2 * (L + 1) * d := by
    have h1 : 0 ≤ 1 / 2 - d := by linarith
    have h2 : 0 ≤ ((L - l3 + 3 / 5) + r * ((L - lr) + 19 / 20)) * (1 / 2 - d) :=
      mul_nonneg hA h1
    have h3 : 0 ≤ (1 / 2 - d) * ((2 * (L + 1) - ((L - l3 + 3 / 5) + r * ((L - lr) + 19 / 20)))
        + ((L - l3 + 3 / 5) + r * ((L - lr) + 19 / 20)) * (1 / 2 - d)) :=
      mul_nonneg h1 (by linarith)
    nlinarith [h3]
  -- 𝒬(1/2) ≥ 23/3600
  have hhalf : 23 / 3600 ≤ (L - l3 + 3 / 5)
      + ((L - l3 + 3 / 5) + r * ((L - lr) + 19 / 20)) * (1 / 2) ^ 2 - 2 * (L + 1) * (1 / 2) := by
    have h1 : (1 + r) * (299 / 100) ≤ (1 + r) * L :=
      mul_le_mul_of_nonneg_left hL (by linarith)
    rcases le_or_lt r (1 / 3) with hr3 | hr3
    · have h2 := hlr_case hr3
      have h3 : r * 1 ≤ r * (-lr) := mul_le_mul_of_nonneg_left h2 hr0.le
      nlinarith [h1, h3, hl3_2r]
    · have h3 : 0 ≤ r * (-lr) := mul_nonneg hr0.le (by linarith)
      nlinarith [h1, h3, hl3_tan]
  linarith [hstep, hhalf]

/-- eq:endpointinterval: q₀(d) ≥ (23/3600) p t for 0 ≤ d ≤ 1/2 when ε ≤ p. -/
theorem endpoint_interval {p t d : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht : 22 / 25 ≤ t) (ht1 : t < 1)
    (hr : (1 - t) / 2 ≤ p) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2) :
    23 / 3600 * p * t ≤ (eta ((1 - 2 * p) * t) - eta t) + eta ((1 - 2 * p) * t) * d ^ 2
      - 2 * (binaryEntropy p * t) * d := by
  have hQ := q0_ge_Q hp0 hp1 ht ht1 hd0
  rw [log_inv_eps_eq hp0 ht1] at hQ
  have hr0 : 0 < (1 - t) / 2 / p := div_pos (by linarith) hp0
  have hr1 : (1 - t) / 2 / p ≤ 1 := by
    rw [div_le_one hp0]
    exact hr
  have hL := log_inv_ge hp0 hp1
  have hlr0 : Real.log ((1 - t) / 2 / p) ≤ 0 := Real.log_nonpos hr0.le hr1
  have hlr1 := neg_mul_log_le hr0
  have hl3_0 : 0 ≤ Real.log (1 + 2 * ((1 - t) / 2 / p)) := Real.log_nonneg (by linarith)
  have hl3_1 : Real.log (1 + 2 * ((1 - t) / 2 / p)) < 11 / 10 :=
    lt_of_le_of_lt (Real.log_le_log (by linarith) (by linarith)) AppF.row_log_q3_hi
  have hl3_2r : Real.log (1 + 2 * ((1 - t) / 2 / p)) ≤ 2 * ((1 - t) / 2 / p) := by
    have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + 2 * ((1 - t) / 2 / p))
    linarith
  have hl3_tan : Real.log (1 + 2 * ((1 - t) / 2 / p)) ≤ 11 / 10 + 2 / 3 * ((1 - t) / 2 / p - 1) := by
    have h := log_one_add_two_mul_le_tangent hr0
    linarith [AppF.row_log_q3_hi]
  have hlr_case : (1 - t) / 2 / p ≤ 1 / 3 → 1 ≤ -Real.log ((1 - t) / 2 / p) :=
    fun h => one_le_neg_log_of_le_third hr0 h
  have hpoly := Q_ge_bound hr0 hr1 hL hlr0 hlr1 hl3_0 hl3_1 hl3_2r hl3_tan hlr_case hd
  have hpt : 0 < p * t := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hpoly hpt.le
  linarith [hQ, hmul]

/-- eq:gaindominance: K₀ ≥ M₀/3 when ε ≤ p. -/
theorem gain_dominance {p t : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht : 22 / 25 ≤ t) (ht1 : t < 1)
    (hr : (1 - t) / 2 ≤ p) :
    eta ((1 - 2 * p) * t) / 3 ≤ eta ((1 - 2 * p) * t) - eta t := by
  have hK := K0_ge_alpha hp0 hp1 ht ht1
  have hL := log_inv_ge hp0 hp1
  have hr0 : 0 < (1 - t) / 2 / p := div_pos (by linarith) hp0
  have hr1 : (1 - t) / 2 / p ≤ 1 := by
    rw [div_le_one hp0]
    exact hr
  have hl3 : Real.log (1 + 2 * ((1 - t) / 2 / p)) < 11 / 10 :=
    lt_of_le_of_lt (Real.log_le_log (by linarith) (by linarith)) AppF.row_log_q3_hi
  -- J₀ = η(t) = h(ε) ≤ h(p) ≤ p (L + 1)
  have hJ : eta t ≤ p * (Real.log (1 / p) + 1) := by
    rw [eta_eq_binaryEntropy_eps]
    exact le_trans (binaryEntropy_mono_half (by linarith) hr (by linarith))
      (binaryEntropy_le_mul hp0 (by linarith))
  -- K₀ ≥ p t α ≥ (9/10) p α ≥ (9/10) p (L - 1/2)
  have hα : 0 ≤ Real.log (1 / p) - Real.log (1 + 2 * ((1 - t) / 2 / p)) + 3 / 5 := by linarith
  have hpα : 0 ≤ p * (Real.log (1 / p) - Real.log (1 + 2 * ((1 - t) / 2 / p)) + 3 / 5) :=
    mul_nonneg hp0.le hα
  have h1 : 0 ≤ p * (Real.log (1 / p) - Real.log (1 + 2 * ((1 - t) / 2 / p)) + 3 / 5)
      * (t - 9 / 10) :=
    mul_nonneg hpα (by linarith)
  have h2 : p * (Real.log (1 / p) - 1 / 2)
      ≤ p * (Real.log (1 / p) - Real.log (1 + 2 * ((1 - t) / 2 / p)) + 3 / 5) :=
    mul_le_mul_of_nonneg_left (by linarith) hp0.le
  have h3 : p * (299 / 100) ≤ p * Real.log (1 / p) := mul_le_mul_of_nonneg_left hL hp0.le
  linarith [hK, hJ, h1, h2, h3]

end CK
