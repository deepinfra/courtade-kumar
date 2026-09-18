# COMMON RULES FOR EVERY LEAN TASK (read fully before starting)

## Project
- Lean 4.19.0 + mathlib (pinned, olean cache present). Project root: `~/ck_lean` (= /Users/dimiter/ck_lean).
- Environment for every command: `export PATH="$HOME/.elan/bin:$PATH"; cd ~/ck_lean`.
- Existing modules (all compiled, all kernel-checked, only standard axioms): CK/Definitions.lean, CK/Algebra.lean,
  CK/Induction.lean, CK/AnalyticTargets.lean, CK/Semantics.lean, CK/Sections.lean, CK/Relabel.lean, CK/SmallGap.lean,
  CK/AvgLemmas.lean, CK/ProfileInduction.lean, CK/EntropyBounds.lean, CK/Pinsker.lean, CK/LogEnclosure.lean,
  CK/Constants.lean (namespace CK.AppF: rational log/entropy bounds), CK/EtaDeriv.lean, CK/Curvature.lean,
  CK/ProductCentering.lean, CK/Transfer.lean, CK/GainBounds.lean.  READ the ones your task builds on; reuse their lemmas.
- Key definitions (CK/Definitions.lean, CK/AnalyticTargets.lean), all in `namespace CK`, `noncomputable section`:
  `Cube n := Fin n → Bool`, `BooleanFunction n := Cube n → Bool`, `indicator b := if b then 1 else 0`,
  `sign b := if b then 1 else -1`, `avg v := (∑ x, v x) / 2^n`, `kernel p y x := ∏ i, if y i = x i then 1-p else p`,
  `binaryEntropy p := -p*log p - (1-p)*log(1-p)`, `eta u := binaryEntropy ((1+u)/2)`, `kappa u := log 2 - eta u`,
  `mean f := avg (indicator ∘ f)`, `posterior f p y := ∑ x, kernel p y x * indicator (f x)`,
  `conditionalEntropy f p := avg (fun y => binaryEntropy (posterior f p y))`,
  `information f p := binaryEntropy (mean f) - conditionalEntropy f p`,
  `mixedEntropy p a b := (binaryEntropy ((1-p)*a+p*b) + binaryEntropy (p*a+(1-p)*b))/2`,
  `scalarSlack p d a b := (1+d^2)*mixedEntropy p a b - (binaryEntropy a + binaryEntropy b)/2 - 2*d*binaryEntropy p*|a-b|`,
  `atanhLog u := (log(1+u) - log(1-u))/2`, `curvature u := 1/(1-u^2)`, `pairEntropy nu z := (eta (nu+z) + eta (nu-z))/2`,
  `psi rho t := (1-t)*(1+t-rho^2)`, `lambdaDenom rho := 1 + rho - (31/40)*rho^2`,
  `Lpair nu z := (atanhLog (nu+z) + atanhLog (nu-z))/2` (ProductCentering.lean).
  Manuscript dictionary: rho = 1-2p; J0 = eta t; M0 = eta (rho*t); K0 = M0 - J0; h = binaryEntropy; ℓ = h(p)*t.

## Hard rules (the verification gate enforces these; violating any of them makes your work worthless)
1. NO `sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`, `decide := true` on Props, or any option that skips the kernel.
   Every declaration must depend only on `propext`, `Classical.choice`, `Quot.sound`.
2. DO NOT modify any existing file under ~/ck_lean (especially CK/Definitions.lean, CKF2/Spec.lean, lean-toolchain,
   lakefile.lean, lake-manifest.json). If you need a variant of an existing lemma, prove it in your own file.
3. DO NOT run `lake build`, `lake update`, `lake exe cache`, or anything that writes to `.lake`. Other agents work
   concurrently. Type-check your file ONLY with:  `lake env lean <path-to-your-file.lean>`   (5–90 s per run).
   Do not run several `lean` processes at once.
4. Your file must compile with ZERO errors AND ZERO warnings (the gate rejects warnings: unused variables → rename to `_x`
   or use them; unused `have` → remove; deprecated lemma → use the new name; `simp` "unused simp args" → prune).
5. The TARGET STATEMENTS given in your spec must be proved EXACTLY as stated (same hypotheses, same conclusion, up to
   trivially equivalent syntax). Never weaken a target to make it provable. If a proof route in the spec doesn't work,
   find another valid route to the SAME statement. Auxiliary lemmas may be stated however you like.
6. Prove everything from scratch or from existing kernel-checked lemmas. Do not state helper "facts" as hypotheses of the
   target theorems.
7. Work in a scratch copy first (e.g. `/private/tmp/claude-501/-Users-dimiter/bbf75097-b8aa-4c7d-a9eb-d3f829b6d13e/scratchpad/<Name>.lean`),
   compile it with `lake env lean` from `~/ck_lean` (the path can be absolute), and only when it compiles cleanly copy it
   to `~/ck_lean/CK/<Name>.lean`. Any file left in `~/ck_lean/CK/` MUST compile cleanly and contain no sorry — the gate
   scans every file there. If you fail, leave nothing in ~/ck_lean/CK/ and report precisely what is missing.
8. Before finishing, append temporarily `#print axioms CK.<each main theorem>` at the end of the file, run
   `lake env lean` once more, confirm each prints exactly `[propext, Classical.choice, Quot.sound]`, then REMOVE those
   lines and re-run once more to make sure the final file compiles cleanly. Report the axiom output in your final answer.

## Style / API hints (mathlib as of this pin)
- Imports: start with `import CK.<the deepest existing module you need>` (e.g. `import CK.GainBounds`, `import CK.Constants`);
  those transitively import everything below. Add specific `import Mathlib.…` lines only if needed.
- Header: `noncomputable section` / `namespace CK` / `open scoped BigOperators` … / `end CK`.
- Calculus pattern used throughout the project (copy it): `monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuity) (differentiability on interior) (deriv sign on interior)` with
  `rw [interior_Icc]`, `HasDerivAt` built by `.mul/.add/.sub/.div/.comp/.const_mul/.pow`, then `rw [h.deriv]`.
  Also `antitoneOn_of_deriv_nonpos`, `MonotoneOn.convexOn_of_deriv`, `AntitoneOn.concaveOn_of_deriv`,
  `convexOn_of_deriv2_nonneg`, `concaveOn_of_deriv2_nonpos` (Mathlib/Analysis/Convex/Deriv.lean).
- Existing calculus: `hasDerivAt_eta`, `hasDerivAt_atanhLog`, `hasDerivAt_curvature`, `hasDerivAt_binaryEntropy`,
  `continuous_eta`, `continuous_binaryEntropy`, `eta_even`, `eta_zero`, `eta_one`, `eta_le_eta` (eta antitone on [0,1]),
  `eta_nonneg`, `eta_pos`, `eta_le_log_two`, `le_atanhLog` (u ≤ atanh u), `atanhLog_nonneg`, `atanhLog_mono`,
  `atanhLog_le_mul_curvature` (atanh u ≤ u/(1-u²)), `atanhLog_div_le` (atanh u/u monotone), `curvature_mono`,
  `kappa_ge_half_sq` (u²/2 ≤ kappa u), `pinsker`, `binaryEntropy_symm` (h(1-x)=h(x)), `binaryEntropy_nonneg'`,
  `binaryEntropy_eq_binEntropy` (CK.binaryEntropy = Real.binEntropy), `binaryEntropy_le_mul` (h p ≤ p(log(1/p)+1)),
  `gain_integral` (2pt·atanhLog((1-p)t) ≤ eta(ρt) - eta t), `neg_log_one_sub_ge` (s ≤ -log(1-s)),
  `neg_log_one_sub_le` (-log(1-s) ≤ (s - s²/2)/(1-s)), `neg_log_one_sub_ge'` ((s-s²/2-s³/4)/(1-s) ≤ -log(1-s), s ≤ 1/2),
  `pairEntropy_le_eta`, `pairEntropy_pos`, `pairEntropy_zero_left`, `Lpair_le`, `product_centering`,
  `transfer_product`, `transfer_gain`, `transfer_relative` (read CK/Transfer.lean for exact forms).
- Numeric constants (CK/Constants.lean, namespace CK.AppF): `log_q2 : 0.6931471802… < log 2 ∧ log 2 < 0.693147180561`,
  similarly `log_q3, log_q20, log_q50_3, log_q459_250, log_q59_21, log_q137_23, log_q22_3, log_q899_101, log_q459_41,
  log_q199_60, log_q127_40, log_q3967_1000, log_q4883_1000, log_q5619_1000, log_q5, log_q8, log_q40_3, log_q4, log_q7,
  log_q10, log_q9, log_q25, log_q23, log_q50, log_q47, log_q19` (each a two-sided bracket on a 10^-12 grid), the
  manuscript rows `row_log_q20_lo : 299/100 < log 20`, `row_log_q20_hi : log 20 < 749/250`, `row_log_q3_hi : log 3 < 11/10`,
  `row_log_q2_hi : log 2 < 7/10`, `row_log_q459_250_lo : 3/5 < log(459/250)`, `row_log_q59_21_lo`, `row_log_q137_23_lo`,
  `row_log_q22_3_lo`, `row_log_q899_101_lo`, `row_log_q459_41_hi : log(459/41) < 5/2`, `row_log_q199_60_lo`,
  `row_log_q127_40_lo`, …; entropy rows `row_h_1_4_lo : 11/20 < binaryEntropy (1/4)`, `row_h_1_8_lo : 3/8 < h(1/8)`,
  `row_h_1_10_lo : 8/25 < h(1/10)`, `row_h_2_25_lo : 11/40 < h(2/25)`, `row_h_3_50_lo : 9/40 < h(3/50)`,
  `row_h_1_5_lo : 1/2 < h(1/5)`, `row_h_1_20_hi : h(1/20) < 1/5`; `knot_rho_3_5, knot_rho_3_4, knot_rho_17_20, knot_rho_9_10`;
  `comb_log3 : 949/1500 < log 3 - (2/3) log 2`, `comb_log2 : log 2 - (39/40)(2/5)(1321/1000) < 9/50`.
  If you need a NEW rational log bound, derive it the same way: `logEnclosure_proved 12 v …` gives
  `logPartial 12 v ≤ log v ≤ logPartial 12 v + logTail 12 v` for 1 ≤ v ≤ 2, evaluate with
  `norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]`, and split `log (2^k * v) = k*log 2 + log v`.
  (Look at how `log_q3` is proved in CK/Constants.lean.) For h(r/s) at rationals: `s*h(r/s) = s log s - r log r - (s-r) log(s-r)`.
- Mathlib names verified to exist at this pin: `Real.negMulLog`, `Real.negMulLog_mul : negMulLog (x*y) = y*negMulLog x + x*negMulLog y`,
  `Real.negMulLog_nonneg`, `Real.concaveOn_negMulLog : ConcaveOn ℝ (Set.Ici 0) negMulLog`, `ConcaveOn.le_map_sum`,
  `ConvexOn.map_sum_le`, `Real.binEntropy_strictMonoOn : StrictMonoOn binEntropy (Icc 0 2⁻¹)`, `Real.strictConcave_binEntropy`,
  `Real.hasSum_pow_div_log_of_abs_lt_one : |x|<1 → HasSum (fun n => x^(n+1)/(n+1)) (-log(1-x))`,
  `Real.hasSum_log_sub_log_of_abs_lt_one : |x|<1 → HasSum (fun k => 2*(1/(2k+1))*x^(2k+1)) (log(1+x) - log(1-x))`,
  `HasSum.mul_left`, `HasSum.add`, `HasSum.sub`, `hasSum_le`, `sum_le_hasSum`, `hasSum_nat_add_iff`, `HasSum.tsum_eq`,
  `Real.add_one_le_exp`, `Real.log_le_sub_one_of_pos`, `Real.log_le_log`, `Real.log_lt_log`, `Real.log_div`, `Real.log_mul`,
  `Real.log_pow`, `Real.log_inv`, `Real.exp_log`, `Real.log_exp`, `strictConcaveOn_log_Ioi`, `Real.log_nonneg`,
  `Finset.prod_one_add : ∏ i ∈ s, (1 + f i) = ∑ t ∈ s.powerset, ∏ i ∈ t, f i`, `Fintype.prod_sum`, `Finset.prod_univ_sum`,
  `Finset.sum_comm`, `Finset.mul_sum`, `Finset.sum_mul`, `Finset.sum_add_distrib`, `Fin.snocEquiv`, `Fin.consEquiv`,
  `Fin.insertNthEquiv`, `Fin.prod_univ_castSucc`, `Fin.sum_univ_castSucc`, `Fintype.sum_equiv`, `Fintype.sum_prod_type`,
  `Fintype.sum_bool`, `Fin.snoc_castSucc`, `Fin.snoc_last`.
  When unsure of a name or signature, grep mathlib: `grep -rn "theorem NAME\|lemma NAME" ~/ck_lean/.lake/packages/mathlib/Mathlib`.
- Tactics that carry most of the weight here: `nlinarith [facts]`, `linarith`, `positivity`, `field_simp`, `ring`, `norm_num`,
  `gcongr`, `push_cast`. For inequalities with products of known-sign factors, feed `nlinarith` explicit product hints
  such as `mul_nonneg ha hb`, `mul_pos`, `sq_nonneg (x - y)`.
- Write docstrings citing the manuscript label (e.g. `eq:interiorproduct`, `app:rsmall`).

## Reporting (your final message is machine-read)
Return: the file path you installed (or "none"), the exact names and statements of the main theorems, the `#print axioms`
output for each, the compile command you ran last and its (empty) output, and any deviations/caveats. If incomplete, list
exactly which target statements are missing and why.
