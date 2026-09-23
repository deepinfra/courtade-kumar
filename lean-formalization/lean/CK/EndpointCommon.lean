import CK.GainBounds
import CK.Constants

/-!
# Shared endpoint bounds (manuscript app:endpoint, eq:alphabeta, eq:endquad)

Setting: `0 < p ≤ 1/20`, `22/25 ≤ t < 1`; `ε = (1-t)/2 ∈ (0, 3/50]`, `r = ε/p`,
`L = log(1/p)`, `u_ε = log(1/ε)`, `α = L - log(1+2r) + 3/5`, `β = u_ε + 19/20`.

* `K0_ge_alpha`  : `K₀ = η(ρt) - η(t) ≥ p t α`          (eq:alphabeta, first part)
* `J0_ge_rbeta`  : `J₀ = η(t) ≥ p t r β`                  (eq:alphabeta, second part)
* `M0_ge`        : `M₀ = η(ρt) ≥ p t (α + r β)`
* `ell_le`       : `ℓ = h(p) t ≤ p t (L + 1)`
* `q0_ge_Q`      : `q₀(d) = K₀ + M₀ d² - 2 ℓ d ≥ p t 𝒬(d)`  (eq:endquad)

All statements are written with explicit expressions (no `let`) so that downstream
files can rewrite with them directly.
-/
noncomputable section
namespace CK

/-- `η(t) = h((1-t)/2)`, by the symmetry `h(1-x) = h(x)`. -/
theorem eta_eq_binaryEntropy_eps (t : ℝ) : eta t = binaryEntropy ((1 - t) / 2) := by
  unfold eta
  have h : (1 + t) / 2 = 1 - (1 - t) / 2 := by ring
  rw [h, binaryEntropy_symm]

/-- `L = log(1/p) ≥ log 20 > 299/100` for `0 < p ≤ 1/20` (app:endpoint). -/
theorem log_inv_ge {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) : 299 / 100 ≤ Real.log (1 / p) := by
  have h20 : (20 : ℝ) ≤ 1 / p := by
    rw [le_div_iff₀ hp0]
    linarith
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 20) h20
  linarith [AppF.row_log_q20_lo]

/-- `h` is monotone on `[0, 1/2]`. -/
theorem binaryEntropy_mono_half {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    binaryEntropy a ≤ binaryEntropy b := by
  rw [binaryEntropy_eq_binEntropy]
  have hb' : b ≤ 2⁻¹ := by rw [← one_div]; exact hb
  exact Real.binEntropy_strictMonoOn.monotoneOn ⟨ha, le_trans hab hb'⟩
    ⟨le_trans ha hab, hb'⟩ hab

/-- `p ≤ h(p)` for `0 < p ≤ 1/20`: `h(p) ≥ p log(1/p) ≥ (299/100) p`. -/
theorem le_binaryEntropy_of_small {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) :
    p ≤ binaryEntropy p := by
  unfold binaryEntropy
  have hL := log_inv_ge hp0 hp1
  rw [Real.log_div one_ne_zero (ne_of_gt hp0), Real.log_one] at hL
  have h2 : Real.log (1 - p) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h3 : 0 ≤ -(1 - p) * Real.log (1 - p) := by nlinarith
  have h4 : p * (299 / 100) ≤ p * (0 - Real.log p) := mul_le_mul_of_nonneg_left hL hp0.le
  nlinarith [h3, h4]

/-- h(ε) ≥ ε (log(1/ε) + 19/20) for 0 < ε ≤ 3/50 (eq:entropyremainder with 𝓑(ε) ≥ 9691/10000 > 19/20). -/
theorem binaryEntropy_ge_eps {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 3 / 50) :
    e * (Real.log (1 / e) + 19 / 20) ≤ binaryEntropy e := by
  unfold binaryEntropy
  rw [Real.log_div one_ne_zero (ne_of_gt he0), Real.log_one]
  have h1 := neg_log_one_sub_ge' (le_of_lt he0) (by linarith : e ≤ 1 / 2)
  have h1e : 0 < 1 - e := by linarith
  have h2 : e - e ^ 2 / 2 - e ^ 3 / 4 ≤ -(1 - e) * Real.log (1 - e) := by
    have hmul := mul_le_mul_of_nonneg_left h1 h1e.le
    have hc : (1 - e) * ((e - e ^ 2 / 2 - e ^ 3 / 4) / (1 - e)) = e - e ^ 2 / 2 - e ^ 3 / 4 := by
      field_simp
      ring
    rw [hc] at hmul
    linarith
  have h3 : 0 ≤ 1 / 20 - e / 2 - e ^ 2 / 4 := by nlinarith
  have h4 : 0 ≤ e * (1 / 20 - e / 2 - e ^ 2 / 4) := mul_nonneg he0.le h3
  nlinarith [h2, h4]

/-- eq:alphabeta (first part): K₀ ≥ p t α. -/
theorem K0_ge_alpha {p t : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht : 22 / 25 ≤ t) (ht1 : t < 1) :
    p * t * (Real.log (1 / p) - Real.log (1 + 2 * ((1 - t) / 2 / p)) + 3 / 5) ≤
      eta ((1 - 2 * p) * t) - eta t := by
  have hg := gain_integral hp0 (by linarith) (by linarith) ht1
  unfold atanhLog at hg
  have hpt : 0 < p * t := by nlinarith
  have hm0 : 209 / 250 ≤ (1 - p) * t := by nlinarith
  have hm1 : (1 - p) * t < 1 := by nlinarith
  -- numerator: log(1 + (1-p)t) ≥ log(459/250) > 3/5
  have hnum : 3 / 5 ≤ Real.log (1 + (1 - p) * t) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 459 / 250)
      (by linarith : (459 / 250 : ℝ) ≤ 1 + (1 - p) * t)
    linarith [AppF.row_log_q459_250_lo]
  -- denominator: 1 - (1-p)t ≤ p (1 + 2r) with r = (1-t)/2/p
  have hr : 0 ≤ (1 - t) / 2 / p := by
    apply div_nonneg _ hp0.le
    linarith
  have hden : 1 - (1 - p) * t ≤ p * (1 + 2 * ((1 - t) / 2 / p)) := by
    have hc : p * (1 + 2 * ((1 - t) / 2 / p)) = p + (1 - t) := by
      field_simp
      ring
    rw [hc]
    nlinarith
  have hden0 : 0 < 1 - (1 - p) * t := by linarith
  have hlogden : Real.log (1 - (1 - p) * t) ≤
      Real.log p + Real.log (1 + 2 * ((1 - t) / 2 / p)) := by
    rw [← Real.log_mul hp0.ne' (ne_of_gt (by linarith))]
    exact Real.log_le_log hden0 hden
  have hLp : Real.log (1 / p) = -Real.log p := by
    rw [Real.log_div one_ne_zero hp0.ne', Real.log_one]
    ring
  rw [hLp]
  have key : -Real.log p - Real.log (1 + 2 * ((1 - t) / 2 / p)) + 3 / 5 ≤
      Real.log (1 + (1 - p) * t) - Real.log (1 - (1 - p) * t) := by linarith
  calc p * t * (-Real.log p - Real.log (1 + 2 * ((1 - t) / 2 / p)) + 3 / 5)
      ≤ p * t * (Real.log (1 + (1 - p) * t) - Real.log (1 - (1 - p) * t)) :=
        mul_le_mul_of_nonneg_left key hpt.le
    _ = 2 * p * t * ((Real.log (1 + (1 - p) * t) - Real.log (1 - (1 - p) * t)) / 2) := by ring
    _ ≤ eta ((1 - 2 * p) * t) - eta t := hg

/-- eq:alphabeta (second part): J₀ = eta t ≥ p t r β. -/
theorem J0_ge_rbeta {p t : ℝ} (hp0 : 0 < p) (ht : 22 / 25 ≤ t) (ht1 : t < 1) :
    p * t * ((1 - t) / 2 / p) * (Real.log (1 / ((1 - t) / 2)) + 19 / 20) ≤ eta t := by
  rw [eta_eq_binaryEntropy_eps]
  have he0 : 0 < (1 - t) / 2 := by linarith
  have he1 : (1 - t) / 2 ≤ 3 / 50 := by linarith
  have hB := binaryEntropy_ge_eps he0 he1
  have hbr : 0 ≤ Real.log (1 / ((1 - t) / 2)) + 19 / 20 := by
    have h1 : (1 : ℝ) ≤ 1 / ((1 - t) / 2) := one_le_one_div he0 (by linarith)
    linarith [Real.log_nonneg h1]
  have hpt : p * t * ((1 - t) / 2 / p) = t * ((1 - t) / 2) := by
    field_simp
    ring
  rw [hpt]
  have h1t : 0 ≤ 1 - t := by linarith
  nlinarith [mul_nonneg (mul_nonneg he0.le hbr) h1t, hB]

/-- M₀ ≥ p t (α + r β). -/
theorem M0_ge {p t : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht : 22 / 25 ≤ t) (ht1 : t < 1) :
    p * t * ((Real.log (1 / p) - Real.log (1 + 2 * ((1 - t) / 2 / p)) + 3 / 5)
      + ((1 - t) / 2 / p) * (Real.log (1 / ((1 - t) / 2)) + 19 / 20)) ≤ eta ((1 - 2 * p) * t) := by
  have h1 := K0_ge_alpha hp0 hp1 ht ht1
  have h2 := J0_ge_rbeta hp0 ht ht1
  nlinarith [h1, h2]

/-- ℓ = h(p) t ≤ p t (L + 1). -/
theorem ell_le {p t : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht0 : 0 ≤ t) :
    binaryEntropy p * t ≤ p * t * (Real.log (1 / p) + 1) := by
  have h := binaryEntropy_le_mul hp0 (by linarith)
  calc binaryEntropy p * t ≤ p * (Real.log (1 / p) + 1) * t := mul_le_mul_of_nonneg_right h ht0
    _ = p * t * (Real.log (1 / p) + 1) := by ring

/-- eq:endquad: for d ≥ 0, q₀(d) ≥ p t 𝒬(d) with 𝒬(d) = α + (α + rβ) d² − 2(L+1) d. -/
theorem q0_ge_Q {p t d : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht : 22 / 25 ≤ t) (ht1 : t < 1)
    (hd : 0 ≤ d) :
    p * t * ((Real.log (1 / p) - Real.log (1 + 2 * ((1 - t) / 2 / p)) + 3 / 5)
      + ((Real.log (1 / p) - Real.log (1 + 2 * ((1 - t) / 2 / p)) + 3 / 5)
          + ((1 - t) / 2 / p) * (Real.log (1 / ((1 - t) / 2)) + 19 / 20)) * d ^ 2
      - 2 * (Real.log (1 / p) + 1) * d)
    ≤ (eta ((1 - 2 * p) * t) - eta t) + eta ((1 - 2 * p) * t) * d ^ 2
      - 2 * (binaryEntropy p * t) * d := by
  have hK := K0_ge_alpha hp0 hp1 ht ht1
  have hM := M0_ge hp0 hp1 ht ht1
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hl := ell_le hp0 hp1 ht0
  nlinarith [hK, mul_le_mul_of_nonneg_right hM (sq_nonneg d), mul_le_mul_of_nonneg_right hl hd]

end CK
