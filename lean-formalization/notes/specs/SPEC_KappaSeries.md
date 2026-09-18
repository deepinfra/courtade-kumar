# TASK: CK/KappaSeries.lean — the power series of κ (manuscript eq:series) and κ(θu) ≤ θ²κ(u) (eq:entropyfacts)

Imports: `import CK.GainBounds`.
Recall kappa u = log 2 − eta u, eta u = binaryEntropy((1+u)/2), atanhLog u = (log(1+u) − log(1−u))/2.

## TARGETS (exact statements)
```lean
/-- eq:series: κ(u) = Σ_{j≥1} u^{2j}/(2j(2j−1)) for |u| < 1 (index j = n+1). -/
theorem hasSum_kappa {u : ℝ} (hu : |u| < 1) :
    HasSum (fun n : ℕ => u ^ (2 * (n + 1)) / ((2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1))) (kappa u)
theorem kappa_ge_partial {u : ℝ} (hu : |u| < 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, u ^ (2 * (n + 1)) / ((2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1)) ≤ kappa u
theorem kappa_even (u : ℝ) : kappa (-u) = kappa u
theorem kappa_one : kappa 1 = Real.log 2
theorem kappa_nonneg {u : ℝ} (hu0 : -1 ≤ u) (hu1 : u ≤ 1) : 0 ≤ kappa u
theorem continuous_kappa : Continuous kappa
/-- eq:entropyfacts: κ(θu) ≤ θ² κ(u) for 0 ≤ θ ≤ 1, −1 ≤ u ≤ 1. -/
theorem kappa_scaling {θ u : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hu0 : -1 ≤ u) (hu1 : u ≤ 1) :
    kappa (θ * u) ≤ θ ^ 2 * kappa u
```
## Proof notes
- Closed form: kappa u = ((1+u)·log(1+u) + (1−u)·log(1−u))/2 for −1 < u < 1 (unfold; log((1+u)/2) = log(1+u) − log 2 via `Real.log_div`; `ring`).
  And (1+u)log(1+u) + (1−u)log(1−u) = [log(1+u) + log(1−u)] + u[log(1+u) − log(1−u)] = log(1 − u²) + 2u·atanhLog u
  (`Real.log_mul`: log(1+u) + log(1−u) = log((1+u)(1−u)) = log(1−u²)).
- Series: `Real.hasSum_pow_div_log_of_abs_lt_one (x := u^2)` gives Σ (u²)^(n+1)/(n+1) = −log(1−u²);
  `Real.hasSum_log_sub_log_of_abs_lt_one` gives Σ 2·(1/(2k+1))·u^(2k+1) = log(1+u) − log(1−u); multiply by u (`HasSum.mul_left`).
  Termwise: u^{2n+2}[2/(2n+1) − 1/(n+1)] = u^{2n+2}/((2n+1)(n+1)); halve. Match the target term with `funext` + `field_simp; ring`
  (note `u ^ (2*(n+1))` vs `(u^2)^(n+1)` vs `u^(2n+1)*u`: use `pow_mul`, `pow_succ`). Use `HasSum.add`, `HasSum.sub`, `HasSum.mul_left`, then `HasSum` congruence (`HasSum.congr`-style via `(funext …) ▸` or `convert … using 1`).
- kappa_ge_partial: `sum_le_hasSum` with nonnegative terms (even powers, positive denominators).
- kappa_scaling for |u| < 1: `hasSum_le` between `hasSum_kappa (θu)` (|θu| < 1) and `(hasSum_kappa u).mul_left (θ^2)`, termwise
  (θu)^{2(n+1)} = θ^{2(n+1)}·u^{2(n+1)} ≤ θ²·u^{2(n+1)} because θ^{2(n+1)} ≤ θ² (θ ∈ [0,1], `pow_le_pow_of_le_one`) and u^{2(n+1)} ≥ 0 (`even_two_mul`/`pow_bit0_nonneg`, or write as (u^2)^(n+1)).
  For u = ±1 (only u = 1 needed by evenness): both sides are continuous in u (`continuous_kappa`), so pass to the limit u → 1⁻ from the strict case
  (e.g. `le_of_tendsto_of_tendsto'` with `tendsto_nhdsWithin_of_tendsto_nhds` on `Set.Iio 1` and `eventually` from `Filter.eventually_of_mem self_mem_nhdsWithin`),
  or any other valid argument (e.g. compare with the explicit statement at u=1: kappa θ ≤ θ² log 2, which follows from `sum_le_hasSum`-style
  bounds and `kappa_ge_partial`-type inequalities … but the limit argument is the direct route). θ = 1 or θ = 0 are trivial (`kappa_zero` exists in EtaDeriv.lean as `kappa_zero : kappa 0 = 0`).
- continuous_kappa: `continuous_const.sub continuous_eta`.
