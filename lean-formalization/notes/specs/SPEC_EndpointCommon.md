# TASK: CK/EndpointCommon.lean — shared endpoint bounds (manuscript app:endpoint, eq:alphabeta, eq:endquad)

Imports: `import CK.GainBounds` and `import CK.Constants`.
Setting: 0 < p ≤ 1/20, 22/25 ≤ t < 1. Manuscript: ε = (1−t)/2 (so 0 < ε ≤ 3/50), r = ε/p, L = log(1/p), u_e = log(1/ε),
α = L − log(1+2r) + 3/5, β = u_e + 19/20. Write everything with explicit expressions (no `let`), exactly as below,
so downstream files can `have := K0_ge_alpha …` and rewrite.

## TARGETS (exact statements)
```lean
theorem eta_eq_binaryEntropy_eps (t : ℝ) : eta t = binaryEntropy ((1 - t) / 2)
theorem log_inv_ge {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) : 299 / 100 ≤ Real.log (1 / p)
theorem binaryEntropy_mono_half {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    binaryEntropy a ≤ binaryEntropy b
theorem le_binaryEntropy_of_small {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) : p ≤ binaryEntropy p
/-- h(ε) ≥ ε (log(1/ε) + 19/20) for 0 < ε ≤ 3/50 (eq:entropyremainder with 𝓑(ε) ≥ 9691/10000 > 19/20). -/
theorem binaryEntropy_ge_eps {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 3 / 50) :
    e * (Real.log (1 / e) + 19 / 20) ≤ binaryEntropy e
/-- eq:alphabeta (first part): K₀ ≥ p t α. -/
theorem K0_ge_alpha {p t : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht : 22 / 25 ≤ t) (ht1 : t < 1) :
    p * t * (Real.log (1 / p) - Real.log (1 + 2 * ((1 - t) / 2 / p)) + 3 / 5) ≤ eta ((1 - 2 * p) * t) - eta t
/-- eq:alphabeta (second part): J₀ = eta t ≥ p t r β. -/
theorem J0_ge_rbeta {p t : ℝ} (hp0 : 0 < p) (ht : 22 / 25 ≤ t) (ht1 : t < 1) :
    p * t * ((1 - t) / 2 / p) * (Real.log (1 / ((1 - t) / 2)) + 19 / 20) ≤ eta t
/-- M₀ ≥ p t (α + r β). -/
theorem M0_ge {p t : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht : 22 / 25 ≤ t) (ht1 : t < 1) :
    p * t * ((Real.log (1 / p) - Real.log (1 + 2 * ((1 - t) / 2 / p)) + 3 / 5)
      + ((1 - t) / 2 / p) * (Real.log (1 / ((1 - t) / 2)) + 19 / 20)) ≤ eta ((1 - 2 * p) * t)
/-- ℓ = h(p) t ≤ p t (L + 1). -/
theorem ell_le {p t : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht0 : 0 ≤ t) :
    binaryEntropy p * t ≤ p * t * (Real.log (1 / p) + 1)
/-- eq:endquad: for d ≥ 0, q₀(d) ≥ p t 𝒬(d) with 𝒬(d) = α + (α + rβ) d² − 2(L+1) d. -/
theorem q0_ge_Q {p t d : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht : 22 / 25 ≤ t) (ht1 : t < 1) (hd : 0 ≤ d) :
    p * t * ((Real.log (1 / p) - Real.log (1 + 2 * ((1 - t) / 2 / p)) + 3 / 5)
      + ((Real.log (1 / p) - Real.log (1 + 2 * ((1 - t) / 2 / p)) + 3 / 5)
          + ((1 - t) / 2 / p) * (Real.log (1 / ((1 - t) / 2)) + 19 / 20)) * d ^ 2
      - 2 * (Real.log (1 / p) + 1) * d)
    ≤ (eta ((1 - 2 * p) * t) - eta t) + eta ((1 - 2 * p) * t) * d ^ 2 - 2 * (binaryEntropy p * t) * d
```
## Proof notes
- eta_eq_binaryEntropy_eps: eta t = h((1+t)/2) = h(1 − (1−t)/2) = h((1−t)/2) by `binaryEntropy_symm`.
- log_inv_ge: 1/p ≥ 20 so log(1/p) ≥ log 20 > 299/100 (`Real.log_le_log`, `AppF.row_log_q20_lo`).
- binaryEntropy_mono_half: `binaryEntropy_eq_binaryEntropy` + `Real.binEntropy_strictMonoOn.monotoneOn` (Icc 0 2⁻¹), or via eta antitone + evenness.
- le_binaryEntropy_of_small: h(p) = p log(1/p) + (−(1−p)log(1−p)) ≥ p log(1/p) ≥ p·(299/100) ≥ p; second term ≥ 0 by `neg_log_one_sub_ge` (or `Real.log_nonpos`).
- binaryEntropy_ge_eps: −(1−e)log(1−e) ≥ e − e²/2 − e³/4 = e(1 − e/2 − e²/4) (`neg_log_one_sub_ge'`, e ≤ 1/2), and 1 − e/2 − e²/4 ≥ 19/20 for e ≤ 3/50.
- K0_ge_alpha: `gain_integral` (needs p < 1/2, 0 < t < 1): K₀ ≥ 2pt·atanhLog((1−p)t) = pt[log(1+(1−p)t) − log(1−(1−p)t)].
  Numerator ≥ 459/250 (since (1−p)t ≥ (19/20)(22/25) = 209/250) so log ≥ 3/5 (`row_log_q459_250_lo`, `Real.log_le_log`).
  Denominator: 1 − (1−p)t = p + 2(1−p)·(1−t)/2 ≤ p + (1−t) = p(1 + 2r) where r = (1−t)/2/p (because p·(1−t) ≥ 0); it is > 0.
  Hence −log(1−(1−p)t) ≥ −log(p(1+2r)) = log(1/p) − log(1+2r) (`Real.log_mul`, log(1/p) = −log p via `Real.log_div`/`Real.log_inv`).
- J0_ge_rbeta: eta t = h(ε) with ε = (1−t)/2 ∈ (0, 3/50]; h(ε) ≥ ε(log(1/ε) + 19/20) ≥ t·ε(log(1/ε)+19/20) since 0 < t ≤ 1 and the bracket is ≥ 0
  (log(1/ε) ≥ log(50/3) > 0); and p·t·(ε/p) = t·ε (`field_simp`).
- M0_ge: eta(ρt) = K₀ + J₀; add K0_ge_alpha and J0_ge_rbeta.
- ell_le: `binaryEntropy_le_mul` times t ≥ 0.
- q0_ge_Q: q₀(d) = K₀ + M₀d² − 2ℓd; use K₀ ≥ ptα, M₀ ≥ pt(α+rβ) with d² ≥ 0, ℓ ≤ pt(L+1) with d ≥ 0; `nlinarith [mul_le_mul_of_nonneg_right hM (sq_nonneg d), mul_le_mul_of_nonneg_right hl hd]`.
