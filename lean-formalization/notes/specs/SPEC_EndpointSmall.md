# TASK: CK/EndpointSmall.lean — endpoint regime ε ≤ p (manuscript app:rsmall, eq:endpointinterval, eq:gaindominance)

Imports: `import CK.EndpointCommon` (read it: `K0_ge_alpha`, `J0_ge_rbeta`, `M0_ge`, `ell_le`, `q0_ge_Q`, `log_inv_ge`, `binaryEntropy_mono_half`, `eta_eq_binaryEntropy_eps`).
Setting: 0 < p ≤ 1/20, 22/25 ≤ t < 1, ε = (1−t)/2 ≤ p, r = ε/p ∈ (0,1], L = log(1/p) ≥ 299/100, u_e = log(1/ε) = L − log r (ε = p·r ⇒ log(1/ε) = log(1/p) − log r; note log r ≤ 0).
α = L − log(1+2r) + 3/5, β = u_e + 19/20, A = α + rβ, 𝒬(d) = α + A d² − 2(L+1) d.

## TARGETS (exact statements)
```lean
/-- eq:endpointinterval: q₀(d) ≥ (23/3600) p t for 0 ≤ d ≤ 1/2 when ε ≤ p. -/
theorem endpoint_interval {p t d : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht : 22 / 25 ≤ t) (ht1 : t < 1)
    (hr : (1 - t) / 2 ≤ p) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2) :
    23 / 3600 * p * t ≤ (eta ((1 - 2 * p) * t) - eta t) + eta ((1 - 2 * p) * t) * d ^ 2
      - 2 * (binaryEntropy p * t) * d
/-- eq:gaindominance: K₀ ≥ M₀/3 when ε ≤ p. -/
theorem gain_dominance {p t : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht : 22 / 25 ≤ t) (ht1 : t < 1)
    (hr : (1 - t) / 2 ≤ p) :
    eta ((1 - 2 * p) * t) / 3 ≤ eta ((1 - 2 * p) * t) - eta t
```
## Proof plan
endpoint_interval:
1. `q0_ge_Q` gives q₀(d) ≥ p t 𝒬(d). It remains to show 𝒬(d) ≥ 23/3600 on [0, 1/2].
2. A − 2(L+1) < 0. Indeed A − 2(L+1) = −(1−r)L − log(1+2r) − r·log r + (19/20) r − 7/5 (substitute u_e = L − log r and expand).
   Bounds: (1−r) ≥ 0 and L ≥ 299/100 ⇒ −(1−r)L ≤ −(299/100)(1−r); −r log r ≤ 1 − r (from log(1/r) ≤ 1/r − 1, `Real.log_le_sub_one_of_pos`, `Real.log_inv`);
   log(1+2r) ≥ 0 (`Real.log_nonneg`). Hence A − 2(L+1) ≤ −(199/100)(1−r) + (19/20)r − 7/5 ≤ 19/20 − 7/5 < 0.
3. 𝒬(d) ≥ 𝒬(1/2) for 0 ≤ d ≤ 1/2: 𝒬(d) − 𝒬(1/2) = (d − 1/2)·[A(d + 1/2) − 2(L+1)] and both factors are ≤ 0
   (A ≥ 0: α ≥ 299/100 − 11/10 + 3/5 > 0 using log(1+2r) ≤ log 3 < 11/10 (`Real.log_le_log`, `AppF.row_log_q3_hi`); rβ ≥ 0 since u_e ≥ L > 0). `nlinarith`.
4. 𝒬(1/2) = (5/4)α + rβ/4 − L − 1 = (1+r)L/4 − (5/4)log(1+2r) − (r/4)log r + (19/80)r − 1/4  (with u_e = L − log r; check by `ring` after `rw`).
   Case r ≤ 1/3: log(1+2r) ≤ 2r (`Real.log_le_sub_one_of_pos`), −log r ≥ log 3 ≥ 13/12 > 1 (r ≤ 1/3 ⇒ 1/r ≥ 3; `AppF.row_log_q3_lo`), L ≥ 299/100 and 1 + r ≥ 0:
     𝒬(1/2) ≥ (1+r)(299/400) − (5/2)r + r/4 + (19/80)r − 1/4 = 199/400 − (253/200) r ≥ 199/400 − 253/600 = 91/1200 ≥ 23/3600.
   Case 1/3 ≤ r ≤ 1: log(1+2r) ≤ log 3 + (2/3)(r−1) < 11/10 + (2/3)(r−1) (tangent at 3: log((1+2r)/3) ≤ (1+2r)/3 − 1), and −r log r ≥ 0:
     𝒬(1/2) ≥ (1+r)(299/400) − (5/4)(11/10 + (2/3)(r−1)) + (19/80) r − 1/4 = −53/1200 + (91/600) r ≥ −53/1200 + 91/1800 = 23/3600.
5. Chain: q₀(d) ≥ p t 𝒬(d) ≥ p t 𝒬(1/2) ≥ p t·23/3600 (p t > 0).
gain_dominance:
- K₀ ≥ p t α ≥ p t (L − 11/10 + 3/5) = p t (L − 1/2) (log(1+2r) ≤ log 3 < 11/10 as r ≤ 1), and t ≥ 9/10 (ε ≤ p ≤ 1/20 ⇒ t = 1 − 2ε ≥ 9/10), L − 1/2 ≥ 0 ⇒ K₀ ≥ (9/10) p (L − 1/2).
- J₀ = eta t = h(ε) ≤ h(p) ≤ p(L+1)  (`eta_eq_binaryEntropy_eps`, `binaryEntropy_mono_half` with ε ≤ p ≤ 1/2, `binaryEntropy_le_mul`).
- 2K₀ − J₀ ≥ (9/5)p(L − 1/2) − p(L+1) = p[(4/5)L − 19/10] ≥ p[(4/5)(299/100) − 19/10] > 0. So J₀ ≤ 2K₀, i.e. M₀ = J₀ + K₀ ≤ 3K₀, i.e. M₀/3 ≤ K₀.
