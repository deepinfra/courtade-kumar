# TASK: CK/EndpointLarge.lean — endpoint regime p ≤ ε (manuscript app:rlarge, app:normalized, eq:R, eq:relative-positive)

Imports: `import CK.EndpointCommon` (read it), `import CK.Algebra` (has `Algebra.endpoint_polynomial_identity`, `Algebra.endpoint_polynomial_margin`).
Setting: 0 < p ≤ 1/20, 22/25 ≤ t < 1, p ≤ ε = (1−t)/2 ≤ 3/50, r = ε/p ≥ 1, u = log(1/ε) ≥ log(50/3) > 14/5 (`AppF.row_log_q50_3_lo`), L = log(1/p) = u + log r ≥ c := 299/100 (`log_inv_ge`),
a_* = u − 1/2 + (r−1)/(3r), β = u + 19/20, B_* = a_* + rβ, z_* = u + log r + 1 (= L + 1), κ := 453/40000.

## TARGET (exact statement)
```lean
/-- app:normalized: for p ≤ ε ≤ 3/50, the centered numerator K₀M₀ − ℓ² is nonnegative and K₀ − ℓ²/M₀ ≥ (453/40000) p t. -/
theorem endpoint_normalized {p t : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht : 22 / 25 ≤ t) (ht1 : t < 1)
    (hr : p ≤ (1 - t) / 2) :
    0 ≤ (eta ((1 - 2 * p) * t) - eta t) * eta ((1 - 2 * p) * t) - (binaryEntropy p * t) ^ 2 ∧
    453 / 40000 * p * t ≤
      ((eta ((1 - 2 * p) * t) - eta t) * eta ((1 - 2 * p) * t) - (binaryEntropy p * t) ^ 2)
        / eta ((1 - 2 * p) * t)
```
## Proof plan
1. (eq:astar) α ≥ a_*: log(1+2r) = log r + log(2 + 1/r) (1 + 2r = r(2 + 1/r)); log(2 + 1/r) = log 3 + log(1 − (r−1)/(3r)) ≤ log 3 − (r−1)/(3r) ≤ 11/10 − (r−1)/(3r)
   (`Real.log_mul`, `Real.log_le_sub_one_of_pos` on (2r+1)/(3r) > 0, `AppF.row_log_q3_hi`). With L = u + log r: α = L − log(1+2r) + 3/5 ≥ u − 11/10 + (r−1)/(3r) + 3/5 = a_*.
   (log(1/p) = log(1/ε) + log r because 1/p = r·(1/ε).)
2. K₀ ≥ p t a_* (`K0_ge_alpha` + step 1), M₀ ≥ p t B_* (`M0_ge`, rβ ≥ 0), 0 ≤ ℓ ≤ p t z_* (`ell_le`; ℓ ≥ 0 since h(p) ≥ 0, t > 0). a_* ≥ u − 1/2 > 0, β > 0, B_* > 0, z_* > 0.
3. Core: Ψ(u, r) := (a_* − κ)(a_* + rβ) − z_*² ≥ 0 on the domain u ≥ 14/5, r ≥ 1, u + log r ≥ c.
   (3a) Fix u. g(r) := (a_*(r) − κ)(a_*(r) + rβ) − (u + log r + 1)² with a_*(r) = u − 1/2 + (r−1)/(3r) = u − 1/2 + 1/3 − 1/(3r).
        HasDerivAt g at r > 0: g'(r) = (1/(3r²))·(2a_* − κ + rβ) + (a_* − κ)β − 2(u + log r + 1)/r.
        For r ≥ 1: first term ≥ 0 (2a_* − κ + rβ ≥ 0); (u + log r + 1)/r ≤ u + 1 (log r ≤ r − 1 ⇒ u + log r + 1 ≤ u + r ≤ r(u+1));
        so g'(r) ≥ (a_* − κ)β − 2(u+1) ≥ (u − 1/2 − κ)(u + 19/20) − 2(u+1) ≥ 0 for u ≥ 14/5 (`nlinarith [mul_nonneg (u − 14/5 ≥ 0) …]`; value ≈ 0.98 at u = 14/5).
        Hence g is MonotoneOn [r₀, r₁] for any 1 ≤ r₀ ≤ r₁ (`monotoneOn_of_deriv_nonneg`; continuity/differentiability of log and 1/r on r > 0).
   (3b) Case u ≥ c: r ≥ 1 = r₀. g(1) = (u − 1/2 − κ)(2u + 9/20) − (u+1)² = u² − (51/20)u − 49/40 − κ(2u + 9/20) ≥ 0 for u ≥ 299/100 (`nlinarith`; ≈ 0.0178 at u = c and increasing).
   (3c) Case 14/5 ≤ u < c: v := c − u ∈ (0, 19/100], r₀ := Real.exp v ≥ 1 (`Real.one_le_exp`/`Real.add_one_le_exp`). From u + log r ≥ c: log r ≥ v ⇒ r ≥ exp v (`Real.exp_le_exp`, `Real.exp_log`). So g(r) ≥ g(r₀).
        At r₀: log r₀ = v (`Real.log_exp`), z_* = u + v + 1 = c + 1 = 399/100.
        a_*(r₀) = u − 1/2 + (1 − exp(−v))/3 ≥ c − v − 1/2 + v/(3(1+v)) ≥ 249/100 − (13/18) v   [exp(−v) ≤ 1/(1+v) since 1 + v ≤ exp v; v/(1+v) ≥ v/(6/5) as 1 + v ≤ 6/5].
        exp(v)·β = exp(v)(c − v + 19/20) ≥ (1+v)(197/50 − v) ≥ 197/50 + (137/50) v   [v² ≤ v/5].
        So a_*(a_* + r₀β) − z_*² ≥ (249/100 − 13v/18)(249/100 − 13v/18 + 197/50 + 137v/50) − (399/100)² = (249/100 − 13v/18)(643/100 + 454v/225) − (399/100)²
        = 453/5000 + (17117/45000)v − (2951/2025)v² ≥ 453/5000 + (36013/405000) v   (`Algebra.endpoint_polynomial_identity`, `Algebra.endpoint_polynomial_margin`; both factors are ≥ 0 so the product of lower bounds is a lower bound).
        Also B_*(r₀) = a_* + r₀β < 8: a_* < u − 1/2 + 1/3 < c − 1/6 < 3; β ≤ c + 19/20 < 4; r₀ = exp v ≤ 1/(1 − v) ≤ 5/4 (from exp(−v) ≥ 1 − v, i.e. `Real.add_one_le_exp (-v)`).
        Therefore g(r₀) = [a_*(a_* + r₀β) − z_*²] − κ B_*(r₀) ≥ 453/5000 + (36013/405000)v − 8κ = (36013/405000) v ≥ 0 (8κ = 453/5000).
   (Then Ψ(u,r) = g(r) ≥ g(r₀) ≥ 0 in both cases.)
4. Assemble. R := a_*B_* − z_*² = Ψ + κB_* ≥ κ B_* ≥ 0.
   K₀M₀ − ℓ² ≥ (p t a_*)(p t B_*) − (p t z_*)² = p²t² R ≥ 0  (products of nonnegative lower bounds; 0 ≤ ℓ ≤ p t z_* ⇒ ℓ² ≤ (p t z_*)²).
   (K₀M₀ − ℓ²)/M₀ = K₀ − ℓ²/M₀ ≥ p t a_* − (p t z_*)²/(p t B_*) = p t (a_* − z_*²/B_*) = p t Ψ/B_* + p t κ ≥ p t κ   (M₀ ≥ p t B_* > 0 ⇒ ℓ²/M₀ ≤ (p t z_*)²/(p t B_*); `div_le_div`, `sub_div`, `field_simp`).
