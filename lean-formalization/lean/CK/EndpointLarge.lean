import CK.EndpointCommon
import CK.Algebra

/-!
# Endpoint regime `p ≤ ε` (manuscript app:rlarge, app:normalized, eq:R, eq:relative-positive)

Setting: `0 < p ≤ 1/20`, `22/25 ≤ t < 1`, `p ≤ ε = (1-t)/2 ≤ 3/50`, `r = ε/p ≥ 1`,
`u = log(1/ε) ≥ log(50/3) > 14/5`, `L = log(1/p) = u + log r ≥ 299/100`,
`a_* = u - 1/2 + (r-1)/(3r) = u - 1/6 - 1/(3r)`, `β = u + 19/20`, `B_* = a_* + rβ`,
`z_* = u + log r + 1 = L + 1`, `κ = 453/40000`.

* `alpha_ge`        : eq:astar, `α ≥ a_*`.
* `gfun`, `hasDerivAt_gfun`, `gfun_deriv_nonneg`, `gfun_monotone` : for fixed `u`, the map
  `r ↦ Ψ(u,r) = (a_* - κ)(a_* + rβ) - z_*²` is monotone on `[r₀, ∞)` for `r₀ ≥ 1`.
* `gfun_one_nonneg`, `gfun_exp_nonneg`, `core_psi` : `Ψ(u, r) ≥ 0` on the domain
  `u ≥ 14/5`, `r ≥ 1`, `u + log r ≥ 299/100`.
* `endpoint_assemble` : abstract assembly of the two conclusions from the bounds.
* `endpoint_normalized` : app:normalized, the target statement.
-/
noncomputable section
namespace CK

/-- eq:astar: `α = (u + log r) - log(1 + 2r) + 3/5 ≥ a_* = u - 1/6 - 1/(3r)` for `r ≥ 1`. -/
theorem alpha_ge (u r : ℝ) (hr : 1 ≤ r) :
    u - 1 / 6 - 1 / 3 * r⁻¹ ≤ u + Real.log r - Real.log (1 + 2 * r) + 3 / 5 := by
  have hr0 : 0 < r := by linarith
  have hx : 0 < (1 + 2 * r) / (3 * r) := by positivity
  have hprod : 3 * r * ((1 + 2 * r) / (3 * r)) = 1 + 2 * r := by
    field_simp
  have h1 : Real.log (1 + 2 * r) = Real.log 3 + Real.log r + Real.log ((1 + 2 * r) / (3 * r)) := by
    rw [← Real.log_mul (by norm_num) hr0.ne', ← Real.log_mul (by positivity) hx.ne', hprod]
  have h2 := Real.log_le_sub_one_of_pos hx
  have h3 : (1 + 2 * r) / (3 * r) = 2 / 3 + 1 / 3 * r⁻¹ := by
    field_simp
    ring
  linarith [AppF.row_log_q3_hi, h1, h2, h3]

/-- `Ψ(u, r) = (a_* - κ)(a_* + rβ) - (u + log r + 1)²` with `a_* = u - 1/6 - 1/(3r)`,
`β = u + 19/20`, `κ = 453/40000`. -/
def gfun (u r : ℝ) : ℝ :=
  (u - 1 / 6 - 1 / 3 * r⁻¹ - 453 / 40000) * (u - 1 / 6 - 1 / 3 * r⁻¹ + r * (u + 19 / 20))
    - (u + Real.log r + 1) ^ 2

/-- Derivative of `Ψ(u, ·)` at `r > 0`. -/
theorem hasDerivAt_gfun (u r : ℝ) (hr : 0 < r) :
    HasDerivAt (gfun u)
      (1 / 3 * (r ^ 2)⁻¹ * (u - 1 / 6 - 1 / 3 * r⁻¹ + r * (u + 19 / 20))
        + (u - 1 / 6 - 1 / 3 * r⁻¹ - 453 / 40000) * (1 / 3 * (r ^ 2)⁻¹ + (u + 19 / 20))
        - 2 * (u + Real.log r + 1) * r⁻¹) r := by
  have h1 : HasDerivAt (fun x : ℝ => u - 1 / 6 - 1 / 3 * x⁻¹ - 453 / 40000)
      (1 / 3 * (r ^ 2)⁻¹) r := by
    have := (((hasDerivAt_inv hr.ne').const_mul (1 / 3 : ℝ)).const_sub (u - 1 / 6)).sub_const
      (453 / 40000 : ℝ)
    convert this using 1
    ring
  have h2 : HasDerivAt (fun x : ℝ => u - 1 / 6 - 1 / 3 * x⁻¹ + x * (u + 19 / 20))
      (1 / 3 * (r ^ 2)⁻¹ + (u + 19 / 20)) r := by
    have := (((hasDerivAt_inv hr.ne').const_mul (1 / 3 : ℝ)).const_sub (u - 1 / 6)).add
      ((hasDerivAt_id r).mul_const (u + 19 / 20))
    convert this using 1
    ring
  have h3 : HasDerivAt (fun x : ℝ => (u + Real.log x + 1) ^ 2)
      (2 * (u + Real.log r + 1) * r⁻¹) r := by
    have := (((Real.hasDerivAt_log hr.ne').const_add u).add_const 1).pow (n := 2)
    convert this using 1
    norm_num
  have := (h1.mul h2).sub h3
  unfold gfun
  convert this using 1

/-- Sign of the derivative: `Ψ'(u, r) ≥ 0` for `u ≥ 14/5`, `r ≥ 1`. -/
theorem gfun_deriv_nonneg (u x : ℝ) (hu : 14 / 5 ≤ u) (hx : 1 ≤ x) :
    0 ≤ 1 / 3 * (x ^ 2)⁻¹ * (u - 1 / 6 - 1 / 3 * x⁻¹ + x * (u + 19 / 20))
        + (u - 1 / 6 - 1 / 3 * x⁻¹ - 453 / 40000) * (1 / 3 * (x ^ 2)⁻¹ + (u + 19 / 20))
        - 2 * (u + Real.log x + 1) * x⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have hs1 : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
  have hsq : 0 ≤ (x ^ 2)⁻¹ := by positivity
  have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
  have hxs : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0.ne'
  have ha : u - 1 / 2 ≤ u - 1 / 6 - 1 / 3 * x⁻¹ := by linarith
  have h3 : (u + Real.log x + 1) * x⁻¹ ≤ u + 1 := by
    have hlin : u + Real.log x + 1 ≤ (u + 1) * x := by nlinarith
    calc (u + Real.log x + 1) * x⁻¹ ≤ (u + 1) * x * x⁻¹ :=
          mul_le_mul_of_nonneg_right hlin hs0.le
      _ = u + 1 := by rw [mul_assoc, hxs, mul_one]
  have h1 : 0 ≤ 1 / 3 * (x ^ 2)⁻¹ * (u - 1 / 6 - 1 / 3 * x⁻¹ + x * (u + 19 / 20)) := by
    apply mul_nonneg (by positivity)
    nlinarith [mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ u + 19 / 20)]
  have h2 : (u - 1 / 6 - 1 / 3 * x⁻¹ - 453 / 40000) * (u + 19 / 20) ≤
      (u - 1 / 6 - 1 / 3 * x⁻¹ - 453 / 40000) * (1 / 3 * (x ^ 2)⁻¹ + (u + 19 / 20)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  have h4 : 0 ≤ (u - 1 / 2 - 453 / 40000) * (u + 19 / 20) - 2 * (u + 1) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u - 14 / 5) (by linarith : (0 : ℝ) ≤ u - 14 / 5)]
  have h5 : (u - 1 / 2 - 453 / 40000) * (u + 19 / 20) ≤
      (u - 1 / 6 - 1 / 3 * x⁻¹ - 453 / 40000) * (u + 19 / 20) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith [h1, h2, h3, h4, h5]

/-- For `u ≥ 14/5` and `r₀ ≥ 1`, `Ψ(u, ·)` is monotone on `[r₀, ∞)`. -/
theorem gfun_monotone (u r₀ : ℝ) (hu : 14 / 5 ≤ u) (hr₀ : 1 ≤ r₀) :
    MonotoneOn (gfun u) (Set.Ici r₀) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici r₀)
  · intro x hx
    have hx0 : 0 < x := by linarith [Set.mem_Ici.mp hx]
    exact (hasDerivAt_gfun u x hx0).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    intro x hx
    have hx0 : 0 < x := by linarith [Set.mem_Ioi.mp hx]
    exact (hasDerivAt_gfun u x hx0).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx
    have hx1 : 1 ≤ x := by linarith [Set.mem_Ioi.mp hx]
    have hx0 : 0 < x := by linarith
    rw [(hasDerivAt_gfun u x hx0).deriv]
    exact gfun_deriv_nonneg u x hu hx1

/-- Case `u ≥ 299/100`: `Ψ(u, 1) ≥ 0`. -/
theorem gfun_one_nonneg (u : ℝ) (hu : 299 / 100 ≤ u) : 0 ≤ gfun u 1 := by
  unfold gfun
  rw [Real.log_one, inv_one]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u - 299 / 100)
    (by linarith : (0 : ℝ) ≤ u - 299 / 100)]

/-- Case `14/5 ≤ u = 299/100 - v < 299/100`: `Ψ(u, exp v) ≥ 0` for `0 < v ≤ 19/100`. -/
theorem gfun_exp_nonneg (v : ℝ) (hv0 : 0 < v) (hv1 : v ≤ 19 / 100) :
    0 ≤ gfun (299 / 100 - v) (Real.exp v) := by
  unfold gfun
  rw [Real.log_exp]
  have hE := Real.add_one_le_exp v
  have hE' := Real.add_one_le_exp (-v)
  rw [Real.exp_neg] at hE'
  have hEpos : 0 < Real.exp v := Real.exp_pos v
  set E := Real.exp v with hE_def
  have hs0 : 0 < E⁻¹ := inv_pos.mpr hEpos
  have hv5 : 0 ≤ v * (1 / 5 - v) := mul_nonneg hv0.le (by linarith)
  -- `E⁻¹ ≤ 1 - 5v/6`
  have hs_ub : E⁻¹ ≤ 1 - 5 * v / 6 := by
    have h1 : E⁻¹ * (v + 1) ≤ 1 := by
      calc E⁻¹ * (v + 1) ≤ E⁻¹ * E := mul_le_mul_of_nonneg_left hE hs0.le
        _ = 1 := inv_mul_cancel₀ hEpos.ne'
    have h2 : E⁻¹ * (v + 1) ≤ (1 - 5 * v / 6) * (v + 1) := by nlinarith [h1, hv5]
    exact le_of_mul_le_mul_right h2 (by linarith)
  -- `E ≤ 5/4`
  have hE_ub : E ≤ 5 / 4 := by
    have h1 : E * (1 - v) ≤ 1 := by
      calc E * (1 - v) ≤ E * E⁻¹ := mul_le_mul_of_nonneg_left (by linarith) hEpos.le
        _ = 1 := mul_inv_cancel₀ hEpos.ne'
    nlinarith [mul_nonneg hEpos.le (by linarith : (0 : ℝ) ≤ 19 / 100 - v)]
  -- lower bounds
  have ha_lb : 249 / 100 - 13 * v / 18 ≤ 299 / 100 - v - 1 / 6 - 1 / 3 * E⁻¹ := by linarith
  have hEb : (v + 1) * (197 / 50 - v) ≤ E * (299 / 100 - v + 19 / 20) := by
    have h : 299 / 100 - v + 19 / 20 = 197 / 50 - v := by ring
    rw [h]
    exact mul_le_mul_of_nonneg_right hE (by linarith)
  have hB_lb : 643 / 100 + 454 * v / 225 ≤
      299 / 100 - v - 1 / 6 - 1 / 3 * E⁻¹ + E * (299 / 100 - v + 19 / 20) := by
    nlinarith [ha_lb, hEb, hv5]
  have hprod : (249 / 100 - 13 * v / 18) * (643 / 100 + 454 * v / 225) ≤
      (299 / 100 - v - 1 / 6 - 1 / 3 * E⁻¹) *
        (299 / 100 - v - 1 / 6 - 1 / 3 * E⁻¹ + E * (299 / 100 - v + 19 / 20)) :=
    mul_le_mul ha_lb hB_lb (by linarith) (by linarith)
  have hid := Algebra.endpoint_polynomial_identity v
  have hmar := Algebra.endpoint_polynomial_margin v hv0.le (by linarith)
  -- upper bound `B_* ≤ 8`
  have hB_ub : 299 / 100 - v - 1 / 6 - 1 / 3 * E⁻¹ + E * (299 / 100 - v + 19 / 20) ≤ 8 := by
    have h1 : E * (299 / 100 - v + 19 / 20) ≤ 5 / 4 * (197 / 50) :=
      mul_le_mul hE_ub (by linarith) (by linarith) (by norm_num)
    linarith [hs0]
  have hz : (299 / 100 - v + v + 1) ^ 2 = (399 / 100 : ℝ) ^ 2 := by ring
  rw [hz]
  nlinarith [hprod, hid, hmar, hB_ub]

/-- Core inequality (eq:R): `(u + log r + 1)² ≤ (a_* - κ)(a_* + rβ)` on the domain
`u ≥ 14/5`, `r ≥ 1`, `u + log r ≥ 299/100`. -/
theorem core_psi (u r : ℝ) (hu : 14 / 5 ≤ u) (hr : 1 ≤ r)
    (hc : 299 / 100 ≤ u + Real.log r) :
    (u + Real.log r + 1) ^ 2 ≤
      (u - 1 / 6 - 1 / 3 * r⁻¹ - 453 / 40000) * (u - 1 / 6 - 1 / 3 * r⁻¹ + r * (u + 19 / 20)) := by
  suffices h : 0 ≤ gfun u r by
    unfold gfun at h
    linarith
  rcases le_or_lt (299 / 100) u with huc | huc
  · have hmono := gfun_monotone u 1 hu le_rfl
    have h1 : gfun u 1 ≤ gfun u r := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hr) hr
    linarith [gfun_one_nonneg u huc]
  · obtain ⟨v, hv⟩ : ∃ v : ℝ, u = 299 / 100 - v := ⟨299 / 100 - u, by ring⟩
    subst hv
    have hv0 : 0 < v := by linarith
    have hv1 : v ≤ 19 / 100 := by linarith
    have hE1 : 1 ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
    have hrE : Real.exp v ≤ r := by
      have hlr : v ≤ Real.log r := by linarith
      calc Real.exp v ≤ Real.exp (Real.log r) := Real.exp_le_exp.mpr hlr
        _ = r := Real.exp_log (by linarith)
    have hmono := gfun_monotone (299 / 100 - v) (Real.exp v) hu hE1
    have h1 : gfun (299 / 100 - v) (Real.exp v) ≤ gfun (299 / 100 - v) r :=
      hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hrE) hrE
    linarith [gfun_exp_nonneg v hv0 hv1]

/-- Abstract assembly (eq:relative-positive): from `K ≥ p t x`, `M ≥ p t y`, `0 ≤ l ≤ p t z`
and `z² ≤ (x - κ) y` we get `K M - l² ≥ 0` and `(K M - l²)/M ≥ κ p t`. -/
theorem endpoint_assemble {p t K M l x y z : ℝ} (hp : 0 < p) (ht : 0 < t)
    (hK : p * t * x ≤ K) (hM : p * t * y ≤ M) (hl0 : 0 ≤ l) (hlz : l ≤ p * t * z)
    (hx : 453 / 40000 ≤ x) (hy : 0 < y)
    (hpsi : z ^ 2 ≤ (x - 453 / 40000) * y) :
    0 ≤ K * M - l ^ 2 ∧ 453 / 40000 * p * t ≤ (K * M - l ^ 2) / M := by
  have hpt : 0 < p * t := mul_pos hp ht
  have hM0 : 0 < M := lt_of_lt_of_le (mul_pos hpt hy) hM
  have hl2 : l ^ 2 ≤ (p * t * z) ^ 2 := pow_le_pow_left₀ hl0 hlz 2
  have hKx : p * t * (453 / 40000) ≤ p * t * x := mul_le_mul_of_nonneg_left hx hpt.le
  have hK' : 0 ≤ K - 453 / 40000 * p * t := by linarith
  have hkey : (p * t * z) ^ 2 ≤ (K - 453 / 40000 * p * t) * M := by
    calc (p * t * z) ^ 2 = (p * t) ^ 2 * z ^ 2 := by ring
      _ ≤ (p * t) ^ 2 * ((x - 453 / 40000) * y) :=
          mul_le_mul_of_nonneg_left hpsi (by positivity)
      _ = (p * t * (x - 453 / 40000)) * (p * t * y) := by ring
      _ ≤ (K - 453 / 40000 * p * t) * M := by
          apply mul_le_mul _ hM (by positivity) hK'
          linarith
  have hkM : 0 ≤ 453 / 40000 * p * t * M := by positivity
  constructor
  · linarith [hl2, hkey, hkM]
  · rw [le_div_iff₀ hM0]
    linarith [hl2, hkey]

/-- app:normalized: for p ≤ ε ≤ 3/50, the centered numerator K₀M₀ − ℓ² is nonnegative and K₀ − ℓ²/M₀ ≥ (453/40000) p t. -/
theorem endpoint_normalized {p t : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht : 22 / 25 ≤ t) (ht1 : t < 1)
    (hr : p ≤ (1 - t) / 2) :
    0 ≤ (eta ((1 - 2 * p) * t) - eta t) * eta ((1 - 2 * p) * t) - (binaryEntropy p * t) ^ 2 ∧
    453 / 40000 * p * t ≤
      ((eta ((1 - 2 * p) * t) - eta t) * eta ((1 - 2 * p) * t) - (binaryEntropy p * t) ^ 2)
        / eta ((1 - 2 * p) * t) := by
  have ht0 : 0 < t := by linarith
  have hpt : 0 < p * t := mul_pos hp0 ht0
  have hK := K0_ge_alpha hp0 hp1 ht ht1
  have hM := M0_ge hp0 hp1 ht ht1
  have hl := ell_le hp0 hp1 ht0.le
  have hl0 : 0 ≤ binaryEntropy p * t :=
    mul_nonneg (binaryEntropy_nonneg' hp0.le (by linarith)) ht0.le
  have hLc := log_inv_ge hp0 hp1
  have he0 : 0 < (1 - t) / 2 := by linarith
  have hr1 : 1 ≤ (1 - t) / 2 / p := by
    rw [le_div_iff₀ hp0]
    linarith
  have hr0 : 0 < (1 - t) / 2 / p := by positivity
  have hu : 14 / 5 ≤ Real.log (1 / ((1 - t) / 2)) := by
    have h1 : (50 / 3 : ℝ) ≤ 1 / ((1 - t) / 2) := by
      rw [le_div_iff₀ he0]
      linarith
    have h2 := Real.log_le_log (by norm_num) h1
    linarith [AppF.row_log_q50_3_lo]
  have hL : Real.log (1 / p) =
      Real.log (1 / ((1 - t) / 2)) + Real.log ((1 - t) / 2 / p) := by
    have h1t : (1 - t) ≠ 0 := (by linarith : (0 : ℝ) < 1 - t).ne'
    rw [← Real.log_mul (by positivity) hr0.ne']
    congr 1
    field_simp
  have hc : 299 / 100 ≤ Real.log (1 / ((1 - t) / 2)) + Real.log ((1 - t) / 2 / p) := by
    rw [← hL]
    exact hLc
  have halpha := alpha_ge (Real.log (1 / ((1 - t) / 2))) ((1 - t) / 2 / p) hr1
  have hpsi := core_psi _ _ hu hr1 hc
  rw [hL] at hK hM hl
  set u := Real.log (1 / ((1 - t) / 2)) with hu_def
  set r := (1 - t) / 2 / p with hr_def
  have hs1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hrb : 0 ≤ r * (u + 19 / 20) := mul_nonneg hr0.le (by linarith)
  have hKa : p * t * (u - 1 / 6 - 1 / 3 * r⁻¹) ≤ eta ((1 - 2 * p) * t) - eta t :=
    le_trans (mul_le_mul_of_nonneg_left halpha hpt.le) hK
  have hMB : p * t * (u - 1 / 6 - 1 / 3 * r⁻¹ + r * (u + 19 / 20)) ≤ eta ((1 - 2 * p) * t) :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) hpt.le) hM
  have hx : 453 / 40000 ≤ u - 1 / 6 - 1 / 3 * r⁻¹ := by linarith
  have hy : 0 < u - 1 / 6 - 1 / 3 * r⁻¹ + r * (u + 19 / 20) := by linarith
  exact endpoint_assemble hp0 ht0 hKa hMB hl0 hl hx hy hpsi

end CK
