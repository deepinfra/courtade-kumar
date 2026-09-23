# TASK: CK/LargeCoordinate.lean — Lemma lem:largecoordinate (a dominant coordinate), at the last coordinate

Imports: `import CK.InfoContraction` (`conditionalEntropy_ge_conditional`), `import CK.LargeCoordScalar` (`large_coord_scalar`, `U_le_U_zero`), `import CK.NoiseOperator` (`binaryEntropy_mean_eq`), `import CK.Fourier`, `import CK.EtaDeriv`, `import CK.SmallGap` (`mean_nonneg`, `mean_le_one`, `gapLast`).

## TARGETS (exact statements)
```lean
/-- Output complement: information is unchanged, section means are complemented. -/
theorem information_compl {n : ℕ} (f : BooleanFunction n) (p : ℝ) : information (fun x => !(f x)) p = information f p
theorem mean_compl {n : ℕ} (f : BooleanFunction n) : mean (fun x => !(f x)) = 1 - mean f
/-- Lemma lem:largecoordinate at the last coordinate: if |μ₁ − μ₀| ≥ 13/20 and ρ ≤ 9/10 then I(f(X);Y) ≤ log 2 − h(p). -/
theorem large_coordinate_last {n : ℕ} (f : BooleanFunction (n + 1)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (hρ : 1 - 2 * p ≤ 9 / 10) (hb : 13 / 20 ≤ |mean (sectionLast f true) - mean (sectionLast f false)|) :
    information f p ≤ Real.log 2 - binaryEntropy p
```
## Proof plan
- information_compl: indicator (!b) = 1 − indicator b; posterior (compl f) p y = 1 − posterior f p y (row sums `kernel_row_sum`); h(1 − x) = h(x) (`binaryEntropy_symm`); mean (compl f) = 1 − mean f; so both terms of `information` are unchanged.
- large_coordinate_last: WLOG b := μ₁ − μ₀ ≥ 13/20 (if b ≤ −13/20, replace f by its complement: sections complement too (`sectionLast` of the complement is the complement of the section, definitional), b ↦ −b, information unchanged).
  Notation ρ = 1 − 2p, μ = mean f = (μ₁ + μ₀)/2 (`mean_snoc`), m = 2μ − 1 = μ₁ + μ₀ − 1, so |m| + b ≤ 1 (μ's in [0,1]: `mean_nonneg`, `mean_le_one`), 0 ≤ b ≤ 1.
  1. σ := avg (fun w => if sectionLast f true w = sectionLast f false w then 0 else h(p)) = h(p) · avg (fun w => |indicator (sectionLast f true w) − indicator (sectionLast f false w)|) ≥ h(p)·|avg (…)| = h(p)·|μ₁ − μ₀| = h(p) b
     (pointwise: the indicator difference has absolute value 1 exactly when the sections differ; `abs_avg_le_avg_abs`, `avg_sub`, `avg_const_mul`, h(p) ≥ 0).
  2. `conditionalEntropy_ge_conditional`: H(f|Y) ≥ (1−ρ²)·pairEntropy m (ρb) + ρ²·σ ≥ (1−ρ²)·pairEntropy m (ρb) + ρ² b h(p).
  3. information f p = h(μ) − H(f|Y) = eta m − H(f|Y) (`binaryEntropy_mean_eq` or directly h(μ) = eta(2μ−1)) ≤ eta m − (1−ρ²) pairEntropy m (ρb) − ρ² b h(p).
  4. `U_le_U_zero` (with hmb : |m| + b ≤ 1): eta m − (1−ρ²) pairEntropy m (ρb) ≤ eta 0 − (1−ρ²) pairEntropy 0 (ρb) = log 2 − (1−ρ²) eta(ρb) (`eta_zero`, `pairEntropy_zero_left`).
  5. h(p) = eta ρ (eta(1−2p) = h(1−p) = h(p), `binaryEntropy_symm`). `large_coord_scalar` (0 ≤ ρ ≤ 9/10, 13/20 ≤ b ≤ 1): (1 − bρ²) eta ρ ≤ (1−ρ²) eta(ρb), i.e. eta ρ ≤ (1−ρ²)eta(ρb) + ρ²b·eta ρ.
     So information ≤ log 2 − (1−ρ²)eta(ρb) − ρ²b eta ρ ≤ log 2 − eta ρ = log 2 − h(p).
