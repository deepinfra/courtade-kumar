# TASK: CK/Deficit.lean — entropy-deficit contraction under BSC noise (the engine behind manuscript Lemma lem:contraction)

Imports: `import CK.KappaSeries` (for `kappa_scaling`), `import CK.Sections` (for `kernel_snoc`, `avg_snoc`, `Fin.snocEquiv` usage), `import CK.AvgLemmas`.
Mathlib: `Real.negMulLog`, `Real.negMulLog_mul : negMulLog (x*y) = y*negMulLog x + x*negMulLog y`, `Real.negMulLog_nonneg`, `Real.concaveOn_negMulLog : ConcaveOn ℝ (Set.Ici 0) negMulLog`, `ConcaveOn.le_map_sum`.

## DEFINITIONS (exact)
```lean
/-- Shannon entropy (nats) of a nonnegative vector on a finite type. -/
def ent {α : Type*} [Fintype α] (q : α → ℝ) : ℝ := ∑ a, Real.negMulLog (q a)
/-- Probability vector. -/
structure IsDist {α : Type*} [Fintype α] (q : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ q a
  sum_one : ∑ a, q a = 1
/-- Push-forward of a distribution on the cube through the product BSC with flip probability p. -/
def noisy {k : ℕ} (p : ℝ) (q : Cube k → ℝ) (w : Cube k) : ℝ := ∑ u, kernel p w u * q u
/-- Entropy deficit relative to the uniform distribution on Cube k. -/
def deficit {k : ℕ} (q : Cube k → ℝ) : ℝ := k * Real.log 2 - ent q
```
## TARGETS (exact statements)
```lean
theorem noisy_isDist {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q : Cube k → ℝ} (hq : IsDist q) : IsDist (noisy p q)
theorem noisy_add {k : ℕ} (p : ℝ) (q q' : Cube k → ℝ) : noisy p (fun u => q u + q' u) = fun w => noisy p q w + noisy p q' w
theorem noisy_smul {k : ℕ} (p c : ℝ) (q : Cube k → ℝ) : noisy p (fun u => c * q u) = fun w => c * noisy p q w
theorem ent_nonneg {α : Type*} [Fintype α] {q : α → ℝ} (hq : IsDist q) : 0 ≤ ent q
/-- concavity of entropy for finite mixtures -/
theorem ent_mixture_ge {α β : Type*} [Fintype α] [Fintype β] (lam : β → ℝ) (hl0 : ∀ b, 0 ≤ lam b) (hl1 : ∑ b, lam b = 1)
    (q : β → α → ℝ) (hq : ∀ b a, 0 ≤ q b a) :
    ∑ b, lam b * ent (q b) ≤ ent (fun a => ∑ b, lam b * q b a)
/-- one-bit deficit: for the distribution (r, 1−r) on Bool the deficit is kappa (2r−1). -/
theorem deficit_bool (r : ℝ) : Real.log 2 - (Real.negMulLog r + Real.negMulLog (1 - r)) = kappa (2 * r - 1)
/-- THE MAIN THEOREM: BSC noise contracts the deficit by (1 − 2p)². -/
theorem deficit_noisy_le {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) {q : Cube k → ℝ} (hq : IsDist q) :
    deficit (noisy p q) ≤ (1 - 2 * p) ^ 2 * deficit q
```
## Proof plan (induction on k)
Notation for q on Cube (k+1): marginal `marg q s := ∑ w, q (Fin.snoc w s)` (s : Bool), conditional `cond q s w := if marg q s = 0 then 0 else q (Fin.snoc w s) / marg q s`.
Useful: `marg q s = 0 → ∀ w, q (Fin.snoc w s) = 0` for q ≥ 0 (`Finset.sum_eq_zero_iff_of_nonneg`). Sums over Cube (k+1) split with `Fintype.sum_equiv (Fin.snocEquiv fun _ => Bool)` then `Fintype.sum_prod_type`, `Fintype.sum_bool` (see `posterior_snoc` in Sections.lean).
(a) Chain rule: ent q = ent (marg q) + ∑ s, marg q s * ent (cond q s)  (for q ≥ 0). Use `Real.negMulLog_mul` on q (snoc w s) = marg q s * cond q s w, and Σ_w cond q s w = 1 when marg q s ≠ 0.
(b) Hence deficit q = (log 2 − ent (marg q)) + ∑ s, marg q s * deficit (cond q s) when IsDist q (uses Σ_s marg q s = 1 and (k+1)·log 2 = log 2 + k·log 2).
(c) Structure of noisy: with k1 b s := if b = s then 1 − p else p (the one-bit kernel), `kernel_snoc` gives
    noisy p q (Fin.snoc w b) = ∑ s, k1 b s * marg q s * noisy p (cond q s) w   (when marg q s = 0 both the true term and the formula vanish).
    So marg (noisy p q) b = ∑ s, k1 b s * marg q s, and when marg (noisy p q) b ≠ 0:
    cond (noisy p q) b = noisy p (fun w => ∑ s, lam b s * cond q s w) with lam b s := k1 b s * marg q s / marg (noisy p q) b ≥ 0, Σ_s lam b s = 1  (`noisy_add`/`noisy_smul`).
(d) One-bit step: log 2 − ent (marg (noisy p q)) ≤ (1−2p)² (log 2 − ent (marg q)):
    with r := marg q true (so marg q false = 1 − r), marg (noisy q) true = (1−p) r + p(1−r) =: r', and 2r' − 1 = (1−2p)(2r − 1);
    `deficit_bool` turns both sides into kappa; apply `kappa_scaling` with θ = 1 − 2p ∈ [0,1], u = 2r − 1 ∈ [−1,1].
    (ent on Bool: `Fintype.sum_bool`; note `deficit_bool` is the identity log 2 − binaryEntropy r = kappa(2r−1) written with negMulLog; binaryEntropy r = negMulLog r + negMulLog (1−r) by unfolding.)
(e) Induction step: deficit (noisy q) = (log 2 − ent (marg (noisy q))) + ∑_b marg (noisy q) b * deficit (cond (noisy q) b)
    ≤ (1−2p)²(log 2 − ent (marg q)) + ∑_b marg (noisy q) b * (1−2p)² * deficit (mix b)          [IH on mix b := fun w => Σ_s lam b s * cond q s w, an IsDist when marg (noisy q) b ≠ 0; terms with marg (noisy q) b = 0 vanish]
    ≤ (1−2p)² [(log 2 − ent (marg q)) + ∑_b marg (noisy q) b * ∑_s lam b s * deficit (cond q s)]   [concavity `ent_mixture_ge`: deficit (mix) ≤ Σ_s lam b s * deficit (cond q s), using Σ lam = 1]
    = (1−2p)² [(log 2 − ent (marg q)) + ∑_s marg q s * deficit (cond q s)]                         [Σ_b marg (noisy q) b * lam b s = marg q s * Σ_b k1 b s = marg q s]
    = (1−2p)² deficit q.
Base case k = 0: Cube 0 has one element (`Unique`/`Fintype.sum_unique`), IsDist forces q = 1 there, noisy p q = q (kernel p w u = 1 empty product), ent q = negMulLog 1 = 0, deficit = 0.
Zero cases are the main nuisance: keep `cond` with the `if`, and prove small lemmas `cond_isDist (h : marg q s ≠ 0)`, `sum_cond`, etc. Also export helper lemmas (`ent_chain`, `marg`, `cond`, `noisy_snoc`) — later files reuse `ent`, `IsDist`, `noisy`, `deficit`, `noisy_add`, `noisy_smul`, `deficit_noisy_le`.
