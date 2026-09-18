# TASK: CK/ScalarMixing.lean — Theorem thm:linear-mixing (Lemma 2.1) and the low-noise branch (manuscript Sec. 3.6 proof of Theorem lem:mixing, Cor. cor:low)

Imports: `import CK.InteriorEstimate`, `import CK.EndpointSmall`, `import CK.EndpointLarge`, `import CK.Bridge`, `import CK.Transfer`, `import CK.Pinsker`, `import CK.Constants`.
Read: CK/Definitions.lean (`ScalarMixingClaim`, `LinearScalarMixingClaim`, `lowNoiseCK`, `scalarSlack`), CK/Transfer.lean (`transfer_product`, `transfer_gain`, `transfer_relative` — exact hypothesis forms),
CK/Bridge.lean (`scalarSlack_eq`, `nu_add_t_le_one`, `abs_sub_eq_one_cases`, `scalarSlack_nonneg_of_eq`, `scalarSlack_endpoints`), CK/InteriorEstimate.lean (`interior_product`),
CK/EndpointSmall.lean (`endpoint_interval`, `gain_dominance`), CK/EndpointLarge.lean (`endpoint_normalized`), CK/Pinsker.lean (`lowNoiseCK_of_scalar : ScalarMixingClaim → lowNoiseCK`), CK/Algebra.lean (`Algebra.linear_margin_dominates`).

## TARGETS (exact statements)
```lean
/-- Theorem thm:linear-mixing (v11 eq:mixing): the p/500 two-posterior mixing inequality. -/
theorem linear_scalar_mixing : LinearScalarMixingClaim
/-- v9.1 Lemma 2.1 (p²/25), implied by the linear version on p ≤ 1/20. -/
theorem scalar_mixing : ScalarMixingClaim
/-- Corollary cor:low: the Courtade–Kumar bound for 0 ≤ p ≤ 1/20. -/
theorem lowNoise_proved : lowNoiseCK
```
## Proof plan
linear_scalar_mixing: `intro p a b d hp0 hp1 ha0 ha1 hb0 hb1 hd0 hd1`. Put t := |a − b| (0 ≤ t ≤ 1, `abs_sub_le_iff`), ν := |a + b − 1|, ν + t ≤ 1 (`nu_add_t_le_one`).
`rw [scalarSlack_eq]`; note (a − b)² = t² (`sq_abs`). Also p < 1/2 (from p ≤ 1/20), so the Transfer lemmas apply with ρ = 1 − 2p.
- Case t = 0: then a = b (`abs_eq_zero`, `sub_eq_zero`); the claim is p/500·0 ≤ scalarSlack p d a a ≥ 0 (`scalarSlack_nonneg_of_eq`; rewrite back with `scalarSlack_eq` or handle before rewriting).
- Case t = 1: `abs_sub_eq_one_cases` gives (a,b) = (0,1) or (1,0); `scalarSlack_endpoints` gives slack ≥ p/4 ≥ p/500 = p/500·1².
- Case 0 < t < 1:
  * Sub-case t ≤ 22/25: `interior_product` gives g := 1999/1250000·p·t² ≤ K₀M₀ − ℓ² with ℓ = binaryEntropy p * t. `transfer_product` (with l := binaryEntropy p * t, g as above, hg0 : 0 ≤ g) gives
    g / log 2 ≤ q(d) in exactly the pairEntropy form of `scalarSlack_eq`. Then g/log 2 ≥ g/(7/10) (`AppF.row_log_q2_hi`, `div_le_div_of_nonneg_left`) and (1999/1250000)(10/7) ≥ 1/500 (`norm_num`), so p/500·t² ≤ g/log 2.
  * Sub-case t > 22/25, ε := (1−t)/2 ≤ p: `gain_dominance` gives M₀/3 ≤ K₀, hence (1/2)²·M₀ ≤ K₀ (M₀ ≥ 0: `eta_nonneg`); `transfer_gain` with D = 1/2 gives q₀(d) ≤ q(d);
    `endpoint_interval` gives 23/3600·p·t ≤ q₀(d); and 23/3600·p·t ≥ p/500·t² since t ≤ 1 (`nlinarith`).
  * Sub-case t > 22/25, p ≤ ε: `endpoint_normalized` gives 0 ≤ K₀M₀ − ℓ² and 453/40000·p·t ≤ (K₀M₀ − ℓ²)/M₀; `transfer_relative` gives (K₀M₀ − ℓ²)/M₀ ≤ q(d); and 453/40000·p·t ≥ p/500·t².
  Make sure the expressions match syntactically (e.g. `(1 - 2 * p) * t` vs `(1 - 2 * p) * |a - b|` after `set t := |a - b| with ht`): use `set`/`rw` carefully; `convert … using 2` with `ring_nf` if needed.
scalar_mixing: from linear_scalar_mixing and `Algebra.linear_margin_dominates` (p²/25 ≤ p/500 for 0 ≤ p ≤ 1/20) times (a−b)² ≥ 0.
lowNoise_proved := lowNoiseCK_of_scalar scalar_mixing.
