# TASK: CK/SignSum.lean — moments of a weighted sign sum and the capped sign-sum estimate (manuscript Lemma lem:rademacher, App. D)

Imports: `import CK.Algebra`, `import CK.Sections`, `import CK.AvgLemmas` (read Algebra.lean: `Algebra.majorant`, `majorant_absolute : |x| ≤ majorant x`; Sections.lean: `avg_snoc`; AvgLemmas.lean: `avg_add`, `avg_const_mul`, `avg_of_unique`).

## DEFINITIONS (exact)
```lean
def signSum {n : ℕ} (a : Fin n → ℝ) (x : Cube n) : ℝ := ∑ i, a i * sign (x i)
def pw {n : ℕ} (a : Fin n → ℝ) (k : ℕ) : ℝ := ∑ i, a i ^ k
```
## TARGETS (exact statements; `n` implicit, `a : Fin n → ℝ`)
```lean
theorem avg_signSum_sq (a) : avg (fun x => signSum a x ^ 2) = pw a 2
theorem avg_signSum_pow4 (a) : avg (fun x => signSum a x ^ 4) = 3 * pw a 2 ^ 2 - 2 * pw a 4
theorem avg_signSum_pow6 (a) : avg (fun x => signSum a x ^ 6) = 15 * pw a 2 ^ 3 - 30 * pw a 2 * pw a 4 + 16 * pw a 6
theorem avg_signSum_pow8 (a) : avg (fun x => signSum a x ^ 8) =
    105 * pw a 2 ^ 4 - 420 * pw a 2 ^ 2 * pw a 4 + 140 * pw a 4 ^ 2 + 448 * pw a 2 * pw a 6 - 272 * pw a 8
theorem avg_signSum_pow10 (a) : avg (fun x => signSum a x ^ 10) =
    945 * pw a 2 ^ 5 - 6300 * pw a 2 ^ 3 * pw a 4 + 6300 * pw a 2 * pw a 4 ^ 2 + 10080 * pw a 2 ^ 2 * pw a 6
      - 6720 * pw a 4 * pw a 6 - 12240 * pw a 2 * pw a 8 + 7936 * pw a 10
theorem avg_signSum (a) : avg (fun x => signSum a x) = 0
/-- Lemma lem:rademacher: Σ a_i² = 1 and max|a_i| ≤ 2/5 imply E|R| ≤ 7/8. -/
theorem capped_sign_sum (a : Fin n → ℝ) (hnorm : ∑ i, a i ^ 2 = 1) (hcap : ∀ i, |a i| ≤ 2 / 5) :
    avg (fun x => |signSum a x|) ≤ 7 / 8
```
## Proof plan
- Induction on n via `Fin.snoc`: signSum (Fin.snoc a c) (Fin.snoc x s) = signSum a x + c * sign s (`Fin.sum_univ_castSucc`, `Fin.snoc_castSucc`, `Fin.snoc_last`);
  pw (Fin.snoc a c) k = pw a k + c ^ k; avg over Cube (n+1) splits via `avg_snoc` (Sections.lean) into the average of the two last-coordinate values.
  For the induction it is cleanest to prove one statement `moments (a) : avg(R²) = … ∧ avg(R⁴) = … ∧ avg(R⁶) = … ∧ avg(R⁸) = … ∧ avg(R¹⁰) = …`
  together with the odd moments `avg R = avg R³ = avg R⁵ = avg R⁷ = avg R⁹ = 0` (needed in the step), by induction on n, using
  (R + cσ)^k expanded (σ² = 1, `sign_square` in Definitions.lean) and averaged over σ ∈ {1, −1}: avg_σ (R + cσ)^k = Σ_{j even} C(k,j) c^j R^{k−j} for even k
  (odd-j terms cancel between σ = ±1). Concretely: ((R+c)^k + (R−c)^k)/2. Then each identity in the step is a polynomial identity in R-moments of the smaller
  cube and c, closed by `ring`/`linear_combination` after rewriting with the IH and linearity of avg (`avg_add`, `avg_const_mul`, avg of const).
  Base n = 0: signSum = 0, pw = 0, avg of a constant on Cube 0 is the constant (`avg_of_unique` or `Fintype.sum_unique`).
  (An alternative is to prove a general one-step recursion for arbitrary k with `add_pow`; either is fine.)
- Every `a : Fin (n+1) → ℝ` equals `Fin.snoc (fun i => a (Fin.castSucc i)) (a (Fin.last n))` (`Fin.snoc_init_self` / `Fin.snoc_castSucc`), so the induction covers all a.
- capped_sign_sum: pointwise |R| ≤ majorant R (`Algebra.majorant_absolute`), so avg|R| ≤ avg (majorant ∘ R) (`avg_le_avg` in AvgLemmas).
  Unfold `Algebra.majorant`, use linearity to get avg(majorant ∘ R) = (4336·M10 − 117880·M8 + 1187295·M6 − 5572600·M4 + 15433465·M2 + 2903076)/12862500 with the moment
  formulas and pw a 2 = 1 (hnorm). With t = pw a 4, u = pw a 6, v = pw a 8, w = pw a 10 this equals
  (5406800 t² − 14568960 t u − 1140425 t + 4946680 u − 10504640 v + 17205248 w + 5574143)/6431250 (check by `ring`/`linear_combination`).
  Bounds from the cap: 0 ≤ t ≤ (4/25)·pw a 2 = 4/25, 0 ≤ u ≤ (4/25) t, 0 ≤ v ≤ (4/25) u, 0 ≤ w ≤ (4/25) v (termwise: a_i^{k+2} = a_i² · a_i^k ≤ (4/25) a_i^k for even k, `Finset.sum_le_sum`).
  Conclude ≤ 7/8: `nlinarith` with the products (4/25 − t)·t ≥ 0 etc.; the manuscript's route: coefficient of w positive ⇒ w ≤ (4/25)v ⇒ −10504640 v + 17205248 w ≤ 0;
  coefficient of u ≥ 4946680 − 14568960·(4/25) > 0 ⇒ replace u by (4/25)t; the resulting quadratic Q(t) = (15378832 t² − 1744781 t + 27870715)/32156250 is convex,
  Q(0) < 7/8 and Q(4/25) < 7/8, hence Q ≤ 7/8 on [0, 4/25] (convex ⇒ below the chord: Q(t) ≤ max(Q(0),Q(4/25)); prove via nlinarith with t(4/25 − t) ≥ 0).
