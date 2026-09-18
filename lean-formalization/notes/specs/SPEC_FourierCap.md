# TASK: CK/FourierCap.lean — antipodal bound, the balanced first-level estimate, and the bias-inclusive Fourier cap (manuscript Lemma lem:antipodal, Lemma lem:balancedcap, Prop prop:cap)

Imports: `import CK.Fourier` (read fully), `import CK.SignSum` (`signSum`, `avg_signSum`, `capped_sign_sum`), `import CK.Relabel` (`relabel`, `avg_comp`, `mean_relabel`), `import CK.Algebra` (`Algebra.section_bound`), `import CK.AvgLemmas`.

## TARGETS (exact statements)
```lean
/-- Fourier coefficients of a relabelled function: singleton coefficients are permuted. -/
theorem fourierCoeff_comp_perm_singleton {n : ℕ} (σ : Equiv.Perm (Fin n)) (F : Cube n → ℝ) (j : Fin n) :
    fourierCoeff (fun x => F (x ∘ σ)) {j} = fourierCoeff F {σ.symm j}
theorem weight_one_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (F : Cube n → ℝ) :
    weight (fun x => F (x ∘ σ)) 1 = weight F 1
/-- Lemma lem:antipodal (consequence): for an indicator g = 1_f with mean a, W₁(g) ≤ a/2 and W₁(g) ≤ (1−a)/2. -/
theorem weight_one_indicator_le {n : ℕ} (f : BooleanFunction n) :
    weight (fun x => indicator (f x)) 1 ≤ mean f / 2 ∧ weight (fun x => indicator (f x)) 1 ≤ (1 - mean f) / 2
/-- Lemma lem:balancedcap: a balanced indicator with all |E(g X_i)| ≤ 13/40 has W₁(g) ≤ 31/160. -/
theorem balanced_first_level {n : ℕ} (f : BooleanFunction n) (hbal : mean f = 1 / 2)
    (hcoef : ∀ i, |fourierCoeff (fun x => indicator (f x)) {i}| ≤ 13 / 40) :
    weight (fun x => indicator (f x)) 1 ≤ 31 / 160
/-- The balancing lift F♯(x,z) = z·F(zx), encoded on Cube (n+1) with z the last coordinate. -/
def lift {n : ℕ} (f : BooleanFunction n) : BooleanFunction (n + 1) :=
  fun y => decide (f (fun i => decide (y (Fin.castSucc i) = y (Fin.last n))) = y (Fin.last n))
/-- Prop prop:cap: |m| ≤ 13/20 and all |b_i| ≤ 13/20 imply m² + W₁(F) ≤ 31/40. -/
theorem bias_inclusive_cap {n : ℕ} (f : BooleanFunction n) (hm : |avg (signOf f)| ≤ 13 / 20)
    (hb : ∀ i, |fourierCoeff (signOf f) {i}| ≤ 13 / 20) :
    (avg (signOf f)) ^ 2 + weight (signOf f) 1 ≤ 31 / 40
```
## Proof plan
- fourierCoeff_comp_perm_singleton: chi {j} x = sign (x j) = sign ((x ∘ σ) (σ.symm j)); so the average is avg (fun x => G (x ∘ σ)) with G y := F y * sign (y (σ.symm j)); `avg_comp`. weight_one_comp_perm: `weight_one` + reindex the sum by σ.symm (`Equiv.sum_comp`).
- weight_one_indicator_le: let g := indicator ∘ f, a := mean f = avg g. g_odd x := (g x − g (negCube x))/2. `fourierCoeff_comp_negCube` gives fourierCoeff g_odd S = (1 − (−1)^{|S|})/2 · ĝ(S), which is ĝ(S) for |S| = 1.
  `parseval` for g_odd: avg g_odd² = Σ_S ĝ_odd(S)² ≥ Σ_{|S|=1} ĝ_odd(S)² = W₁(g) (drop the other nonnegative terms: `Finset.sum_le_sum_of_subset_of_nonneg` or sum over the filter ≤ full sum).
  avg g_odd² = (1/4)avg (g − g∘neg)² = (1/4)[avg g² + avg (g∘neg)² − 2 avg (g · g∘neg)] = (1/4)[a + a − 2·avg(g·g∘neg)] ≤ a/2 (g² = g: `indicator_square`; `avg_comp_negCube`; g·g∘neg ≥ 0).
  For (1 − a)/2: apply the same to the complement f' := fun x => !(f x): indicator (f' x) = 1 − indicator (f x); singleton coefficients of the complement are the negatives (`fourierCoeff_add`/`fourierCoeff_const_mul`/`fourierCoeff_const` with S = {i} ≠ ∅), so W₁ is the same; mean f' = 1 − a.
- balanced_first_level: g := indicator ∘ f, c_i := ĝ({i}), w := W₁(g) = Σ c_i² (`weight_one`). Split: either (A) ∀ i, |c_i| ≤ 7/40, or (B) ∃ i, 7/40 < |c_i| (≤ 13/40).
  (A): by contradiction suppose w > 31/160. Let L x := signSum c x = Σ_i c_i sign (x i). avg (g · L) = Σ_i c_i · avg (g · sign(x i)) = Σ_i c_i ĝ({i}) = w (linearity: `Finset.mul_sum`, `avg` of a finite sum — prove a small lemma `avg_finset_sum`; chi {i} x = sign (x i)).
      Pointwise g·L ≤ (L + |L|)/2 (0 ≤ g ≤ 1: if L ≥ 0 then gL ≤ L = (L+|L|)/2; if L < 0 then gL ≤ 0 = (L+|L|)/2). So w ≤ (avg L + avg |L|)/2 = avg|L|/2 (`avg_signSum`).
      Normalize: s := Real.sqrt w > 0, a_i := c_i / s; Σ a_i² = 1; |a_i| ≤ (7/40)/s ≤ 2/5 because s² = w > 31/160 ≥ (7/16)²; hence (`capped_sign_sum`) avg |signSum a| ≤ 7/8, and signSum c x = s · signSum a x, so avg |L| = s · 7/8 at most.
      Then w ≤ (7/16) s = (7/16)√w ⇒ √w ≤ 7/16 ⇒ w ≤ 49/256 < 31/160: contradiction.
  (B): n = k + 1 necessarily (Fin n nonempty): `cases n` (n = 0: Fin 0 is empty, contradiction with ∃ i). Let σ := Equiv.swap i (Fin.last k) and g' := relabel σ f (= fun x => f (x ∘ σ)); indicator ∘ g' = (indicator ∘ f) ∘ (· ∘ σ).
      By `fourierCoeff_comp_perm_singleton`, the singleton coefficients of g' are those of g permuted (σ is an involution: σ.symm = σ), in particular ĝ'({last}) = ĝ({i}) =: c with |c| = β ∈ (7/40, 13/40], and W₁(g') = W₁(g) (`weight_one_comp_perm`), mean g' = 1/2 (`mean_relabel`).
      Now work with g' on Cube (k+1): sections g'_s := indicator ∘ sectionLast g' s with means μ_s; μ_true + μ_false = 1 (`mean_snoc`, balance) and μ_true − μ_false = 2c (`fourierCoeff_singleton_last` for signOf g', `fourierCoeff_indicator` with S = {last} ≠ ∅, `signOf_eq`). So min(μ_s, 1 − μ_s) = 1/2 − |c| for both s.
      For j = castSucc j': ĝ'({castSucc j'}) = (ĝ'_true({j'}) + ĝ'_false({j'}))/2 (`fourierCoeff_castSucc_image` with S = {j'}; (indicator ∘ g') (snoc w s) = indicator (sectionLast g' s w) by definition).
      Hence Σ_{j'} ĝ'({castSucc j'})² ≤ Σ_{j'} (ĝ'_true({j'})² + ĝ'_false({j'})²)/2 ((x+y)²/4 ≤ (x²+y²)/2) = (W₁(g'_true) + W₁(g'_false))/2 ≤ (1/2 − |c|)/2 (`weight_one_indicator_le` on each section).
      So w = c² + Σ_{j'} ĝ'({castSucc j'})² (`weight_one` + `Fin.sum_univ_castSucc`) ≤ β² + (1/2 − β)/2 ≤ 309/1600 (`Algebra.section_bound` with 7/40 ≤ β ≤ 13/40) < 31/160.
- bias_inclusive_cap: F := signOf f, m := avg F, b_i := F̂({i}). Let F♯ := signOf (lift f). Facts (prove each; all via `avg_snoc`, `avg_comp_negCube`, `Fin.snoc_castSucc`, `Fin.snoc_last`, `Bool.decide_eq_true`, cases on the last bit):
  F♯ (Fin.snoc w s) = sign s * F (if s then w else negCube w)  [decide (x = true) = x, decide (x = false) = !x, and sign (decide (a = b)) = sign a * sign b];
  avg F♯ = 0 (so mean (lift f) = 1/2 by `avg_signOf`); fourierCoeff F♯ {Fin.last n} = m; fourierCoeff F♯ {Fin.castSucc i} = b_i (use `avg_comp_negCube` and (negCube w) i = !(w i), sign (!b) = −sign b).
  Then `fourierCoeff_indicator` gives the indicator coefficients of lift f: m/2 and b_i/2, all ≤ 13/40 in absolute value; `balanced_first_level` gives W₁(indicator ∘ lift f) ≤ 31/160;
  W₁(indicator ∘ lift f) = W₁(F♯)/4 (`weight_one`, `fourierCoeff_indicator` on singletons) and W₁(F♯) = m² + Σ_i b_i² (`weight_one`, `Fin.sum_univ_castSucc`) = m² + W₁(F) (`weight_one` for F). Conclude m² + W₁(F) ≤ 31/40.
