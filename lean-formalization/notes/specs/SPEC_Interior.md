# TASK: CK/InteriorEstimate.lean — the interior centered estimate (manuscript eq:interiorproduct, app:interior)

Imports: `import CK.GainBounds` and `import CK.Constants`.

## TARGET (exact statement)
```lean
/-- eq:interiorproduct: K₀M₀ − ℓ² ≥ (1999/1250000) p t² for 0 < t ≤ 22/25, 0 < p ≤ 1/20. -/
theorem interior_product {p t : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (ht0 : 0 < t) (ht1 : t ≤ 22 / 25) :
    1999 / 1250000 * p * t ^ 2 ≤
      (eta ((1 - 2 * p) * t) - eta t) * eta ((1 - 2 * p) * t) - (binaryEntropy p * t) ^ 2
```
Dictionary: K₀ = eta((1-2p)t) − eta t, M₀ = eta((1-2p)t), J₀ = eta t, ℓ = binaryEntropy p · t, L = log(1/p).

## Proof plan (all steps verified by hand; follow it or find an equivalent valid route)
1. Let c(t) := 2·atanhLog((19/20)·t)  (the manuscript's c(t) = ln((1+(19/20)t)/(1−(19/20)t)); note 2·atanhLog u = log(1+u) − log(1−u)).
   `gain_integral` gives K₀ ≥ 2pt·atanhLog((1−p)t); since (19/20)t ≤ (1−p)t < 1, `atanhLog_mono` gives K₀ ≥ p t c(t). Also c(t) ≥ 0.
2. J₀ = eta t ≥ 0 (`eta_nonneg`), M₀ = J₀ + K₀ (definitional: eta(ρt) = (eta(ρt) − eta t) + eta t), so
   K₀·M₀ ≥ (p t c)·(eta t + p t c) = p t² [ (c/t)·eta t + p c² ].
3. ℓ = h(p)t ≤ p t (L+1) with L = log(1/p) (`binaryEntropy_le_mul`), so ℓ² ≤ p² t² (L+1)².  L ≥ log 20 > 299/100 (`Real.log_le_log`, `AppF.row_log_q20_lo`).
4. Table bound T(t) := (c(t)/t)·eta t + c(t)²/20 ≥ 4/5 on (0, 22/25], by five interval cases. Monotonicity tools:
   c(t)/t is nondecreasing in t (c(t)/t = (19/10)·atanhLog((19/20)t)/((19/20)t); use `atanhLog_div_le`),
   eta is nonincreasing on [0,1] (`eta_le_eta`), c is nondecreasing (`atanhLog_mono`), c ≥ 0.
   Evaluate: c(1/2) = log(59/21) > 1 (`row_log_q59_21_lo`), c(3/4) = log(137/23) > 7/4 (`row_log_q137_23_lo`),
   c(4/5) = log(22/3) > 39/20 (`row_log_q22_3_lo`), c(21/25) = log(899/101) > 13/6 (`row_log_q899_101_lo`),
   c(22/25) = log(459/41) < 5/2 (`row_log_q459_41_hi`).  (Identity: 2·atanhLog(19/40) = log(59/40) − log(21/40) = log(59/21) by `Real.log_div`.)
   eta(1/2) = h(3/4) = h(1/4) > 11/20 (`binaryEntropy_symm`, `row_h_1_4_lo`); eta(3/4) = h(1/8) > 3/8; eta(4/5) = h(1/10) > 8/25;
   eta(21/25) = h(2/25) > 11/40; eta(22/25) = h(3/50) > 9/40.
   Rows:  (0,1/2]: c/t ≥ 19/10 (from `le_atanhLog`: atanhLog u ≥ u), eta ≥ 11/20, c ≥ 0 → 209/200 ≥ 4/5.
          [1/2,3/4]: c/t ≥ 2·c(1/2) ≥ 2, eta ≥ 3/8, c ≥ 1 → 2·3/8 + 1/20 = 4/5 (equality; the inputs are strict so fine).
          [3/4,4/5]: c/t ≥ (4/3)c(3/4) ≥ 7/3, eta ≥ 8/25, c ≥ 7/4 → 56/75 + 49/320 > 4/5.
          [4/5,21/25]: c/t ≥ (5/4)c(4/5) ≥ 39/16, eta ≥ 11/40, c ≥ 39/20 → 429/640 + 1521/8000 > 4/5.
          [21/25,22/25]: c/t ≥ (25/21)c(21/25) ≥ 325/126, eta ≥ 9/40, c ≥ 13/6 → 2925/5040 + 169/720 > 4/5.
5. Worst noise is p = 1/20: with ψ(p) := p(log(1/p)+1)² − p c², show ψ(p) ≤ ψ(1/20) for 0 < p ≤ 1/20 by
   `monotoneOn_of_deriv_nonneg` on [p, 1/20]: d/dp [p(log(1/p)+1)²] = (log(1/p)+1)² − 2(log(1/p)+1) = (log(1/p))² − 1,
   so ψ' = (log(1/p))² − 1 − c² ≥ (299/100)² − 1 − (5/2)² > 0 (c ≤ c(22/25) < 5/2). (`Real.hasDerivAt_log`, chain rule; log(1/p) = −log p.)
6. Assemble: K₀M₀ − ℓ² ≥ p t²[(c/t)eta t + p c² − p(L+1)²] = p t²[(c/t)eta t − ψ(p)] ≥ p t²[(c/t)eta t − ψ(1/20)]
   = p t²[T(t) − (log 20 + 1)²/20] ≥ p t²[4/5 − (999/250)²/20] = p t² · 1999/1250000, using log 20 < 749/250 (`row_log_q20_hi`)
   and `norm_num` for 4/5 − (999/250)²/20 = 1999/1250000.
Feed `nlinarith` explicit products (e.g. `mul_nonneg`, `mul_le_mul`) — the assembly is a chain of products of nonnegative lower bounds.
