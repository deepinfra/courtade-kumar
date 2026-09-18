# TASK: CK/LargeBias.lean — Lemma lem:bias (large output bias)

Imports: `import CK.InfoContraction`, `import CK.NoiseOperator` (for `binaryEntropy_mean_eq`), `import CK.Constants`, `import CK.EtaDeriv`.
## TARGET (exact statement)
```lean
/-- Lemma lem:bias: if |m| ≥ 13/20 then I(f(X);Y) ≤ κ(ρ) = log 2 − h(p), for every 0 ≤ p ≤ 1/2. -/
theorem large_bias {n : ℕ} (f : BooleanFunction n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (hm : 13 / 20 ≤ |avg (signOf f)|) :
    information f p ≤ Real.log 2 - binaryEntropy p
```
## Proof
information f p ≤ ρ²·h(mean f) (`information_le_contraction`); h(mean f) = eta m with m = avg (signOf f) (`binaryEntropy_mean_eq`); eta m = log 2 − kappa m ≤ log 2 − m²/2 (`kappa_ge_half_sq`, |m| ≤ 1 since mean ∈ [0,1]) ≤ 7/10 − (13/20)²/2 = 391/800 < 1/2 (`AppF.row_log_q2_hi`, m² ≥ 169/400).
So information ≤ ρ²/2 ≤ kappa ρ (`kappa_ge_half_sq` with ρ = 1 − 2p ∈ [0,1]) = log 2 − eta(1 − 2p) = log 2 − h(p) (eta(1−2p) = h((2−2p)/2) = h(1−p) = h(p), `binaryEntropy_symm`).
