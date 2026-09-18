# TASK: CK/InfoContraction.lean — Lemma lem:contraction in posterior form and its three applications (manuscript Lemma 5.1; eq:conditionalcontraction; the degradation step of Prop prop:high)

Imports: `import CK.Deficit` (read it: `ent`, `IsDist`, `noisy`, `deficit`, `noisy_add`, `noisy_smul`, `deficit_noisy_le`), `import CK.Sections`, `import CK.Bridge` (for `binaryEntropy_eq_eta`), `import CK.Semantics`.
Recall: `posterior f p y = ∑ x, kernel p y x * indicator (f x)`, `posterior_snoc`, `posterior_mean : avg (posterior f p) = mean f`, `posterior_nonneg`, `posterior_le_one`, `conditionalEntropy f p = avg (fun y => binaryEntropy (posterior f p y))`, `information f p = binaryEntropy (mean f) − conditionalEntropy f p`, `mean_snoc`, `avg_snoc`, `kernel_row_sum`, `kernel_symm`, `kernel_snoc`.

## DEFINITION (exact)
```lean
/-- Posterior-form information: for π : Cube k → [0,1] (π u = P(Z = 1 | U = u), U uniform), I(Z;U) = h(E π) − E h(π). -/
def infoP {k : ℕ} (π : Cube k → ℝ) : ℝ := binaryEntropy (avg π) - avg (fun u => binaryEntropy (π u))
```
## TARGETS (exact statements)
```lean
theorem avg_noisy {k : ℕ} {p : ℝ} (π : Cube k → ℝ) : avg (noisy p π) = avg π
/-- Lemma lem:contraction, posterior form: I(Z; U_θ) ≤ θ² I(Z; U) with θ = 1 − 2p. -/
theorem infoP_noisy_le {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) {π : Cube k → ℝ}
    (h0 : ∀ u, 0 ≤ π u) (h1 : ∀ u, π u ≤ 1) :
    infoP (noisy p π) ≤ (1 - 2 * p) ^ 2 * infoP π
theorem posterior_eq_noisy {n : ℕ} (f : BooleanFunction n) (p : ℝ) : posterior f p = noisy p (fun x => indicator (f x))
/-- U1 (used by Lemma lem:bias): I(f(X);Y) ≤ ρ² H(f(X)). -/
theorem information_le_contraction {n : ℕ} (f : BooleanFunction n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    information f p ≤ (1 - 2 * p) ^ 2 * binaryEntropy (mean f)
/-- BSC composition: BSC(p₀) followed by BSC(p') is BSC(p₀ + p' − 2p₀p'). (NB: the name `kernel_comp` is already taken in CK/Relabel.lean for the permutation lemma.) -/
theorem kernel_compose {n : ℕ} (p0 p' : ℝ) (y x : Cube n) :
    (∑ z : Cube n, kernel p' y z * kernel p0 z x) = kernel (p0 + p' - 2 * p0 * p') y x
theorem noisy_noisy {k : ℕ} (p0 p' : ℝ) (π : Cube k → ℝ) : noisy p' (noisy p0 π) = noisy (p0 + p' - 2 * p0 * p') π
/-- U3 (degradation, used by Prop prop:high): for 0 ≤ p₀ ≤ p ≤ 1/2, p₀ < 1/2: I(f;Y_p) ≤ ((1−2p)/(1−2p₀))² I(f;Y_{p₀}). -/
theorem information_degrade {n : ℕ} (f : BooleanFunction n) {p0 p : ℝ} (hp0 : 0 ≤ p0) (hp0' : p0 < 1 / 2)
    (hpp : p0 ≤ p) (hp1 : p ≤ 1 / 2) :
    information f p ≤ ((1 - 2 * p) / (1 - 2 * p0)) ^ 2 * information f p0
/-- U2 (eq:conditionalcontraction at the last coordinate, used by Lemma lem:largecoordinate):
    H(f|Y) ≥ (1−ρ²) H(f|Y_last) + ρ² H(f|X',Y_last), with H(f|Y_last) = Q(m, ρb) and H(f|X',Y_last) = σ h(p). -/
theorem conditionalEntropy_ge_conditional {n : ℕ} (f : BooleanFunction (n + 1)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (1 - (1 - 2 * p) ^ 2) * pairEntropy (2 * mean f - 1)
        ((1 - 2 * p) * (mean (sectionLast f true) - mean (sectionLast f false)))
      + (1 - 2 * p) ^ 2 * avg (fun w => if sectionLast f true w = sectionLast f false w then (0 : ℝ) else binaryEntropy p)
    ≤ conditionalEntropy f p
```
## Proof plan
- avg_noisy: swap sums, Σ_w kernel p w u = 1 (`kernel_symm` + `kernel_row_sum`).
- infoP_noisy_le: μ := avg π ∈ [0,1]. If μ = 0 then π ≡ 0 (nonneg terms summing to 0), noisy π ≡ 0, both sides 0. If μ = 1 then π ≡ 1 (1 − π ≥ 0 sums to 0), noisy π ≡ 1 (row sums), both sides 0.
  Otherwise 0 < μ < 1. Define q₁ u := π u / (2^k μ), q₀ u := (1 − π u)/(2^k (1 − μ)); both `IsDist` (sums: Σ π = 2^k μ by definition of avg).
  KEY IDENTITY (prove as a lemma for any π with values in [0,1] and 0 < avg π < 1): μ·deficit q₁ + (1−μ)·deficit q₀ = infoP π.
  [Real.negMulLog_mul with x = π u, y = 1/(2^k μ): negMulLog(π u · y) = y·negMulLog(π u) + π u · negMulLog y; sum over u; Σ_u π u = 2^k μ; negMulLog y = −y·log y = y(k log 2 + log μ) (`Real.log_inv`, `Real.log_mul`, `Real.log_pow`);
   so μ·ent q₁ = avg (negMulLog ∘ π) + μ(k log 2 + log μ); likewise (1−μ)·ent q₀ = avg (negMulLog ∘ (1−π)) + (1−μ)(k log 2 + log(1−μ));
   adding: avg (h ∘ π) + k log 2 − h(μ) (h x = negMulLog x + negMulLog (1−x)); so μ deficit q₁ + (1−μ) deficit q₀ = k log 2 − [avg(h∘π) + k log 2 − h(μ)] = h(μ) − avg(h∘π).]
  Apply the identity to π and to noisy π (avg (noisy π) = μ; noisy p q₁ = (noisy π)/(2^kμ), noisy p q₀ = (1 − noisy π)/(2^k(1−μ)) by `noisy_smul`, `noisy_add` and noisy of the constant 1 is 1 (row sums)).
  Then `deficit_noisy_le` for q₁ and q₀, multiply by μ ≥ 0 and 1 − μ ≥ 0, add.
- posterior_eq_noisy: `funext`, unfold, `rfl` or `simp [posterior, noisy]`.
- information_le_contraction: apply infoP_noisy_le to π = indicator ∘ f (values in {0,1}); avg π = mean f; avg (h ∘ π) = 0 (h 0 = h 1 = 0: `entropy_zero`, `entropy_one`); noisy π = posterior; so infoP (noisy π) = information f p.
- kernel_compose: product structure: Σ_z ∏_i k'(y i, z i) ∏_i k₀(z i, x i) = ∏_i Σ_b k'(y i, b) k₀(b, x i) (`Fintype.prod_sum`/`Finset.prod_univ_sum` after merging the two products with `Finset.prod_mul_distrib`), and the one-bit composition: (1−p')(1−p₀) + p'p₀ = 1 − (p₀ + p' − 2p₀p') when y i = x i, and (1−p')p₀ + p'(1−p₀) = p₀ + p' − 2p₀p' otherwise (case on Bool values, `ring`).
- noisy_noisy: unfold, swap sums, `Finset.mul_sum`, kernel_compose.
- information_degrade: put p' := (p − p₀)/(1 − 2p₀) ∈ [0, 1/2] (1 − 2p' = (1−2p)/(1−2p₀)); then p₀ + p' − 2p₀p' = p (`field_simp; ring`). Apply infoP_noisy_le with π := posterior f p₀ (values in [0,1]) and noise p':
  noisy p' (posterior f p₀) = noisy p' (noisy p₀ (indicator∘f)) = noisy p (indicator∘f) = posterior f p; infoP (posterior f p₀) = information f p₀ (avg posterior = mean f: `posterior_mean`); infoP (posterior f p) = information f p.
- conditionalEntropy_ge_conditional: for each s : Bool let π_s w := (1−p)·indicator (sectionLast f s w) + p·indicator (sectionLast f (!s) w) (values in [0,1]).
  noisy p π_s w = posterior f p (Fin.snoc w s) (`posterior_snoc` + `noisy_add`/`noisy_smul` + `posterior_eq_noisy`); avg π_s = (1−p)·mean (sectionLast f s) + p·mean (sectionLast f (!s)) (`avg_add`, `avg_const_mul`);
  avg (h ∘ π_s) = avg (fun w => if sectionLast f true w = sectionLast f false w then 0 else h p) (pointwise: cases on the two Bool values; h((1−p)) = h(p) by `binaryEntropy_symm`, h 0 = h 1 = 0);
  infoP_noisy_le: h(avg π_s) − avg_w h(posterior f p (snoc w s)) ≤ ρ²[h(avg π_s) − σ h(p)], i.e. avg_w h(posterior (snoc w s)) ≥ (1−ρ²) h(avg π_s) + ρ² σ h(p).
  conditionalEntropy f p = (avg_w h(posterior (snoc w true)) + avg_w h(posterior (snoc w false)))/2 (`avg_snoc`), and
  (h(avg π_true) + h(avg π_false))/2 = pairEntropy (2·mean f − 1) (ρ b): with μ₁ = mean (sectionLast f true), μ₀ = mean (sectionLast f false), mean f = (μ₁ + μ₀)/2 (`mean_snoc`), m = μ₁ + μ₀ − 1, b = μ₁ − μ₀:
  h((1−p)μ₁ + pμ₀) = eta(2((1−p)μ₁ + pμ₀) − 1) = eta(m + ρb) and h((1−p)μ₀ + pμ₁) = eta(m − ρb) (`binaryEntropy_eq_eta`, `ring_nf`). Average the two inequalities.
