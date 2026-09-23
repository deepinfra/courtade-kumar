# TASK: CK/Bridge.lean — the (a,b) ↔ (ν,t) coordinate bridge and the trivial regimes t = 0, t = 1 (manuscript Sec. 3.1, proof of Thm lem:mixing last paragraph)

Imports: `import CK.Transfer`, `import CK.EntropyBounds`, `import CK.Constants`.
Dictionary: t = |a − b|, ν = |a + b − 1|, ρ = 1 − 2p; J = pairEntropy ν t, M = pairEntropy ν (ρt), K = M − J, ℓ = h(p)·t.

## TARGETS (exact statements)
```lean
theorem binaryEntropy_eq_eta (a : ℝ) : binaryEntropy a = eta (2 * a - 1)
theorem half_sum_entropy_eq (a b : ℝ) :
    (binaryEntropy a + binaryEntropy b) / 2 = pairEntropy |a + b - 1| |a - b|
theorem mixedEntropy_eq (p a b : ℝ) :
    mixedEntropy p a b = pairEntropy |a + b - 1| ((1 - 2 * p) * |a - b|)
theorem scalarSlack_eq (p d a b : ℝ) :
    scalarSlack p d a b =
      (pairEntropy |a + b - 1| ((1 - 2 * p) * |a - b|) - pairEntropy |a + b - 1| |a - b|)
        + pairEntropy |a + b - 1| ((1 - 2 * p) * |a - b|) * d ^ 2
        - 2 * (binaryEntropy p * |a - b|) * d
theorem nu_add_t_le_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |a + b - 1| + |a - b| ≤ 1
theorem abs_sub_eq_one_cases {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (h : |a - b| = 1) : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)
/-- t = 0: the slack is d² h(a) ≥ 0. -/
theorem scalarSlack_nonneg_of_eq {p d a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 0 ≤ scalarSlack p d a a
/-- t = 1: the slack is h(p)(1−d)² ≥ h(p)/4 ≥ p/4. -/
theorem scalarSlack_endpoints {p d : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2) :
    p / 4 ≤ scalarSlack p d 0 1 ∧ p / 4 ≤ scalarSlack p d 1 0
theorem le_binaryEntropy_of_small' {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) : p ≤ binaryEntropy p
```
## Proof notes
- binaryEntropy a = eta(2a−1) since eta u = h((1+u)/2) and (1+(2a−1))/2 = a.
- With s = a+b−1, u = a−b: 2a−1 = s+u, 2b−1 = s−u. `eta` is even (`eta_even`). pairEntropy |s| |u| = (eta(|s|+|u|) + eta(|s|−|u|))/2.
  Case on the signs of s and u (`abs_of_nonneg`/`abs_of_neg`, `rcases le_or_lt 0 s`): in each case {s+u, s−u} = ±{|s|+|u|, |s|−|u|} and evenness closes it.
- mixedEntropy: 2((1−p)a + pb) − 1 = s + (1−2p)u and 2(pa + (1−p)b) − 1 = s − (1−2p)u; same case analysis with (1−2p)|u| = |(1−2p)u| only when 1−2p ≥ 0 —
  to avoid a sign assumption on p, note pairEntropy ν z is even in z (pairEntropy ν (−z) = pairEntropy ν z by commutativity of the sum), so handle the
  sign of u directly: pairEntropy |s| ((1−2p)|u|) = pairEntropy |s| ((1−2p)u) when u ≥ 0, and = pairEntropy |s| (−(1−2p)u) = pairEntropy |s| ((1−2p)u) when u < 0.
- scalarSlack_eq: unfold `scalarSlack`, rewrite with the two identities; `ring`.
- nu_add_t_le_one and abs_sub_eq_one_cases: case splits on the abs, `linarith`.
- scalarSlack p d a a = (1+d²)h(a) − h(a) − 0 = d² h(a) ≥ 0 (`binaryEntropy_nonneg'`, mixedEntropy p a a = h(a) since (1−p)a + pa = a).
- scalarSlack p d 0 1: mixedEntropy p 0 1 = (h(p) + h(1−p))/2 = h(p) (`binaryEntropy_symm`); h 0 = h 1 = 0 (`entropy_zero`, `entropy_one`); |0−1| = 1;
  so slack = (1+d²)h(p) − 2d·h(p) = h(p)(1−d)² ≥ h(p)/4 (d ≤ 1/2) ≥ p/4 (h(p) ≥ p: h(p) ≥ p log(1/p) ≥ p log 20 ≥ p, using `row_log_q20_lo`, and −(1−p)log(1−p) ≥ 0).
