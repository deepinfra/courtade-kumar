# TASK: CK/NoiseOperator.lean — the noise operator T_ρ, its spectral action, the posterior link, the cancellation and energy inequalities (manuscript Sec. 6.1, Lemma lem:energy, Prop prop:certificate hypothesis)

Imports: `import CK.Fourier` (read it fully: chi, fourierCoeff, weight, signOf, plancherel, parseval, sum_weight, weight_zero/one, fourierCoeff_empty, avg_signOf …), `import CK.Semantics`, `import CK.EtaDeriv`.
Definitions: `psi rho t := (1 - t) * (1 + t - rho ^ 2)` (AnalyticTargets.lean), `posterior f p y = ∑ x, kernel p y x * indicator (f x)`.

## DEFINITION (exact)
```lean
def noiseOp {n : ℕ} (p : ℝ) (F : Cube n → ℝ) (y : Cube n) : ℝ := ∑ x, kernel p y x * F x
```
## TARGETS (exact statements; `n` implicit, `F : Cube n → ℝ`, `f : BooleanFunction n`)
```lean
theorem noiseOp_chi (p : ℝ) (S : Finset (Fin n)) (y : Cube n) : noiseOp p (chi S) y = (1 - 2 * p) ^ S.card * chi S y
theorem noiseOp_add (p : ℝ) (F G : Cube n → ℝ) : noiseOp p (fun x => F x + G x) = fun y => noiseOp p F y + noiseOp p G y
theorem noiseOp_const_mul (p c : ℝ) (F : Cube n → ℝ) : noiseOp p (fun x => c * F x) = fun y => c * noiseOp p F y
theorem noiseOp_eq_sum (p : ℝ) (F : Cube n → ℝ) (y : Cube n) :
    noiseOp p F y = ∑ S : Finset (Fin n), (1 - 2 * p) ^ S.card * fourierCoeff F S * chi S y
theorem fourierCoeff_noiseOp (p : ℝ) (F : Cube n → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (noiseOp p F) S = (1 - 2 * p) ^ S.card * fourierCoeff F S
theorem posterior_eq_noiseOp (f : BooleanFunction n) (p : ℝ) (y : Cube n) :
    posterior f p y = (1 + noiseOp p (signOf f) y) / 2
theorem abs_noiseOp_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : Cube n → ℝ) (hF : ∀ x, |F x| ≤ 1) (y : Cube n) :
    |noiseOp p F y| ≤ 1
theorem binaryEntropy_mean_eq (f : BooleanFunction n) : binaryEntropy (mean f) = eta (avg (signOf f))
theorem conditionalEntropy_eq_avg_eta (f : BooleanFunction n) (p : ℝ) :
    conditionalEntropy f p = avg (fun y => eta (noiseOp p (signOf f) y))
theorem conditionalEntropy_eq_avg_eta_abs (f : BooleanFunction n) (p : ℝ) :
    conditionalEntropy f p = avg (fun y => eta |noiseOp p (signOf f) y|)
/-- eq:cancellation: E G² − ρ² E(F G) = Σ_k (ρ^{2k} − ρ^{k+2}) W_k(F), G = T_ρ F. -/
theorem cancellation (p : ℝ) (F : Cube n → ℝ) :
    avg (fun x => noiseOp p F x ^ 2) - (1 - 2 * p) ^ 2 * avg (fun x => F x * noiseOp p F x)
      = ∑ k ∈ Finset.range (n + 1), ((1 - 2 * p) ^ (2 * k) - (1 - 2 * p) ^ (k + 2)) * weight F k
/-- Lemma lem:energy with a free cap Ω: if m² + W₁(F) ≤ Ω then E ψ_ρ(|G|) ≥ (1−ρ)(Λ_Ω − Γ m²), with ρ = 1 − 2p ∈ [0,1],
    Λ_Ω = 1 + ρ − Ωρ², Γ = 1 + ρ − ρ², m = E F, F = signOf f. -/
theorem energy_lower_bound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (f : BooleanFunction n) (Ω : ℝ)
    (hcap : (avg (signOf f)) ^ 2 + weight (signOf f) 1 ≤ Ω) :
    (1 - (1 - 2 * p)) * ((1 + (1 - 2 * p) - Ω * (1 - 2 * p) ^ 2)
        - (1 + (1 - 2 * p) - (1 - 2 * p) ^ 2) * (avg (signOf f)) ^ 2)
      ≤ avg (fun y => psi (1 - 2 * p) |noiseOp p (signOf f) y|)
```
## Proof hints
- noiseOp_chi: Σ_x ∏_i k_i(y i, x i) ∏_{i∈S} sign(x i) = ∏_i Σ_b [k(y i, b)·(sign b)^{[i∈S]}] (`Fintype.prod_sum`); the factor is (1−p)sign(y i) + p·sign(!y i) = (1−2p)·sign(y i) for i ∈ S and 1 otherwise (`bool_sum_kernel_factor`).
- noiseOp_eq_sum: expand F by `fourier_expansion`, push noiseOp through the finite sum (linearity) and use noiseOp_chi. fourierCoeff_noiseOp: from noiseOp_eq_sum and orthonormality (`chi_orthonormal`), or from `kernel_symm` + Fubini.
- posterior_eq_noiseOp: indicator (f x) = (1 + signOf f x)/2 (`signOf_eq`), row sums (`kernel_row_sum`).
- abs_noiseOp_le_one: triangle inequality with kernel ≥ 0 and row sum 1 (`Finset.abs_sum_le_sum_abs`, `kernel_nonneg`, `kernel_row_sum`).
- conditionalEntropy: h(posterior) = h((1+G)/2) = eta G by definition of eta; then eta |G| = eta G by `eta_abs` (ProductCentering.lean).
- binaryEntropy_mean_eq: mean f = (1 + avg (signOf f))/2 (`avg_signOf`).
- cancellation: E G² = Σ_S Ĝ(S)² = Σ_S ρ^{2|S|} F̂(S)² (parseval, fourierCoeff_noiseOp); E(FG) = Σ_S F̂(S)Ĝ(S) = Σ_S ρ^{|S|}F̂(S)² (plancherel); regroup by |S| = k as in `sum_weight` (`Finset.sum_fiberwise_of_maps_to`).
- energy_lower_bound: with R = |G|, psi ρ R = 1 − ρ² + ρ²R − R² (R² = G²: `sq_abs`); E psi = 1 − ρ² + ρ² E|G| − E G². From cancellation, E G² = ρ² E(FG) + (1−ρ²)W₀ + ρ²(1−ρ)W₁ + 0·W₂ + Σ_{k≥3}(ρ^{2k} − ρ^{k+2})W_k
  with W₀ = m² (`weight_zero`), and for k ≥ 3, ρ ∈ [0,1]: ρ^{2k} − ρ^{k+2} ≤ 0 (`pow_le_pow_of_le_one`), W_k ≥ 0 (`weight_nonneg`); so E G² ≤ ρ² E(FG) + (1−ρ²)m² + ρ²(1−ρ)W₁.
  Also F·G ≤ |G| pointwise (|F| = 1: `abs_signOf`), so E(FG) ≤ E|G| (`avg_le_avg`), and W₁ ≤ Ω − m² (hcap). Combine: E psi ≥ 1 − ρ² − (1−ρ²)m² − ρ²(1−ρ)(Ω − m²) = (1−ρ)[(1 + ρ − Ωρ²) − (1 + ρ − ρ²)m²] (`ring`/`nlinarith`).
  Handle the sum over k ∈ range (n+1) by splitting off k = 0, 1, 2 (`Finset.sum_range_succ'` / `Finset.range_eq_Ico`, or bound termwise: for k ≥ 3 the coefficient is ≤ 0, for k = 2 it is 0).
