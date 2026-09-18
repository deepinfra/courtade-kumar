# TASK: CK/MiddleHigh.lean — Propositions prop:middle and prop:high (the remainder class under the Fourier cap)

Imports: `import CK.NoiseOperator` (energy_lower_bound, conditionalEntropy_eq_avg_eta_abs, abs_noiseOp_le_one, binaryEntropy_mean_eq, abs_signOf), `import CK.Comparison` (entropy_comparison), `import CK.Anchor` (strict_anchor),
`import CK.InfoContraction` (information_degrade), `import CK.KappaSeries`, `import CK.Constants`.
Definitions: `psi`, `lambdaDenom`, `EntropyComparisonGoal`, `StrictAnchorGoal` in AnalyticTargets.lean.

## TARGETS (exact statements)
```lean
/-- Prop prop:middle: under the cap m² + W₁ ≤ 31/40, the CK bound holds for 3/5 ≤ ρ ≤ 9/10. -/
theorem middle_range {n : ℕ} (f : BooleanFunction n) {p : ℝ} (hρ0 : 3 / 5 ≤ 1 - 2 * p) (hρ1 : 1 - 2 * p ≤ 9 / 10)
    (hcap : (avg (signOf f)) ^ 2 + weight (signOf f) 1 ≤ 31 / 40) :
    information f p ≤ Real.log 2 - binaryEntropy p
/-- Prop prop:high: under the cap, the CK bound holds for 0 ≤ ρ ≤ 3/5. -/
theorem high_noise {n : ℕ} (f : BooleanFunction n) {p : ℝ} (hρ0 : 0 ≤ 1 - 2 * p) (hρ1 : 1 - 2 * p ≤ 3 / 5)
    (hcap : (avg (signOf f)) ^ 2 + weight (signOf f) 1 ≤ 31 / 40) :
    information f p ≤ Real.log 2 - binaryEntropy p
```
## Proof plan
Notation ρ = 1 − 2p, m = avg (signOf f), G = noiseOp p (signOf f), R y = |G y| ∈ [0,1] (`abs_noiseOp_le_one` with |signOf| = 1), Λ = lambdaDenom ρ = 1 + ρ − (31/40)ρ², Γ = 1 + ρ − ρ².
middle_range (p = (1−ρ)/2 ∈ [1/20, 1/5]):
 1. H(f|Y) = avg_y eta(R y) (`conditionalEntropy_eq_avg_eta_abs`) ≥ λ·avg_y psi ρ (R y) where λ := eta ρ/((1−ρ)Λ) (pointwise `entropy_comparison` at t = R y, then `avg_le_avg`, `avg_const_mul`).
 2. avg psi ρ R ≥ (1−ρ)(Λ − Γ m²) (`energy_lower_bound` with Ω = 31/40; note its statement is written with `1 - 2*p` and the explicit polynomials — match with `lambdaDenom`). λ ≥ 0.
    So H(f|Y) ≥ λ(1−ρ)(Λ − Γm²) = eta ρ·(1 − Γm²/Λ) (Λ > 0, 1 − ρ > 0).
 3. H(f(X)) = h(mean f) = eta m ≤ log 2 − m²/2 (`binaryEntropy_mean_eq`, `kappa_ge_half_sq`).
 4. information = eta m − H(f|Y) ≤ log 2 − eta ρ + m²[eta ρ·Γ/Λ − 1/2]. The bracket is ≤ 0:
    eta ρ ≤ eta(3/5) (`eta_le_eta`) ≤ log 2 − 9/50 (`kappa_ge_half_sq`) < 13/25 (`AppF.row_log_q2_hi`), and Γ/Λ ≤ 1240/1321 for ρ ≥ 3/5
    (equivalent to 1321ρ² ≥ 360(1 + ρ − (31/40)ρ²)·… — just prove Γ·1321 ≤ 1240·Λ as a polynomial inequality in ρ on [3/5, 9/10] by `nlinarith`), and (13/25)(1240/1321) < 1/2.
    Hence information ≤ log 2 − eta ρ = log 2 − h(p) (eta(1−2p) = h(p), `binaryEntropy_symm`).
high_noise: ρ₀ := 3/5, p₀ := 1/5.
 1. At p₀: H(f|Y₀) = avg eta(R₀) ≥ (39/40) avg psi (3/5) (R₀) (`strict_anchor` pointwise) ≥ (39/40)(2/5)(1321/1000 − (31/25)m²) (`energy_lower_bound` at p = 1/5, Ω = 31/40: Λ = 1321/1000, Γ = 31/25).
    information f (1/5) ≤ log 2 − m²/2 − (39/40)(2/5)(1321/1000) + (39/40)(2/5)(31/25)m² ≤ U₀ := log 2 − (39/40)(2/5)(1321/1000) since (39/40)(2/5)(31/25) = 1209/2500 < 1/2. U₀ < 9/50 (`AppF.comb_log2`).
 2. If ρ = 0 (p = 1/2): information f (1/2) ≤ 0² · … via `information_degrade` with p₀ = 1/5: ((1−2p)/(1−2p₀))² = 0; and log 2 − h(1/2) = 0 (h(1/2) = log 2: `binEntropy_half`/`eta_zero`); need information f (1/5) ≥ 0? Not needed: 0·x = 0. Actually information_degrade gives information f p ≤ θ²·information f p₀ with θ = ρ/ρ₀, so information f p ≤ (ρ/(3/5))²·(9/50) = ρ²/2 ≤ kappa ρ = log 2 − h(p) — this needs information f p₀ ≤ 9/50 AND θ² ≥ 0, fine for all ρ ∈ [0, 3/5] uniformly (p ≥ 1/5 ⇔ ρ ≤ 3/5).
 3. Conclude with `kappa_ge_half_sq`: ρ²/2 ≤ kappa ρ = log 2 − eta ρ = log 2 − h(p).
