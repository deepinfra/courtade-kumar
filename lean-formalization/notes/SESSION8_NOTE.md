# Session 8 note (17 Sept 2026) — the formalization is complete

## Headline
`CK.courtadeKumar_proved : CK.CourtadeKumar` is now a kernel-checked Lean 4 theorem, and the frozen
challenge `CKF2.exactTargetAccepted : CKF2.Spec.Target` (the independently spelled-out finite-sum
statement in `CKF2/Spec.lean`, definitionally equal to `CK.CourtadeKumar`) compiles from it.

- Full gate: `verify_kernel.py --mode full` → `EXACT_CK_TARGET_ACCEPTED_BY_LEAN_AXIOMS_AUDITED`
  (gate_full/RESULT.json; proof artifact sha256 ea9e5112…7253). Trusted inputs (CK/Definitions.lean,
  CKF2/Spec.lean, lean-toolchain, CompletionGate.lean.template, DECLARATIONS.json) hash-verified unchanged
  since session 5. 42 source files pass the hygiene scan (no sorry/admit/axiom/native_decide/ofReduceBool).
- Axioms: `CKF2.exactTargetAccepted`, `CK.courtadeKumar_proved`, `CK.complementary_proved`,
  `CK.lowNoise_proved`, `CK.scalar_mixing`, `CK.linear_scalar_mixing` each depend on exactly
  `[propext, Classical.choice, Quot.sound]`. Extended audit: 605 declarations across all 40 CK modules +
  CKF2.Spec; every one depends only on a subset of those three (extended_audit/extended_axioms.log; 0 errors,
  0 warnings).
- Independent kernel replay: lean4checker (tag v4.19.0, relinked with the system clang because of the Darwin 25
  dyld SG_READ_ONLY issue, see lean4checker/sysclang.sh) replayed all 41 modules (39 CK modules imported by
  CK.lean, CKF2.Spec, F2CompletionGate) through a fresh kernel: 0 failures (lean4checker/lean4checker_replay.log).
  mathlib itself was not replayed (`--fresh` not used); its oleans are the prebuilt cache for the pinned rev.
- Toolchain: Lean 4.19.0 (elan), mathlib rev c44e0c8ee63ca166450922a373c7409c5d26b00b (lake-manifest.json unchanged).

## What was proved this session (20 new modules, ~4550 lines; every target statement fixed in advance in specs/)
Layer C — Lemma 2.1 (v11 Theorem thm:linear-mixing, p/500 margin):
- CK/InteriorEstimate.lean: `interior_product` (eq:interiorproduct, 0 < t ≤ 22/25) — gain integral, five-interval table, worst noise at p = 1/20.
- CK/EndpointCommon.lean: eq:alphabeta bounds (`K0_ge_alpha`, `J0_ge_rbeta`, `M0_ge`, `ell_le`, `q0_ge_Q`).
- CK/EndpointSmall.lean: `endpoint_interval` (eq:endpointinterval, ε ≤ p, 0 ≤ d ≤ 1/2), `gain_dominance` (K0 ≥ M0/3).
- CK/EndpointLarge.lean: `endpoint_normalized` (app:normalized, p ≤ ε: nonnegative numerator and K0 − ℓ²/M0 ≥ (453/40000) p t).
- CK/Bridge.lean: the (a,b) ↔ (ν,t) coordinate bridge (`scalarSlack_eq` etc.) and the t = 0, t = 1 regimes.
- CK/ScalarMixing.lean: `linear_scalar_mixing : LinearScalarMixingClaim`, `scalar_mixing : ScalarMixingClaim`,
  `lowNoise_proved : lowNoiseCK` (Corollary cor:low, via the session-7 `lowNoiseCK_of_scalar`).
Complementary branch (Sections 5–6):
- CK/KappaSeries.lean: eq:series (`hasSum_kappa`) and `kappa_scaling` (κ(θu) ≤ θ²κ(u)).
- CK/Fourier.lean: characters, coefficients, Parseval/Plancherel, weights, section/negation lemmas.
- CK/NoiseOperator.lean: T_ρ χ_S = ρ^{|S|} χ_S, posterior = (1+T_ρF)/2, H(f|Y) = E η(|T_ρF|),
  eq:cancellation, and the energy inequality of Lemma lem:energy with a free cap Ω (`energy_lower_bound`).
- CK/SignSum.lean: even moments of Σ a_i X_i up to order 10 (all n) and Lemma lem:rademacher (`capped_sign_sum`, E|R| ≤ 7/8).
- CK/FourierCap.lean: antipodal bound W₁(g) ≤ min(a,1−a)/2, Lemma lem:balancedcap (`balanced_first_level`),
  the balancing lift and Prop prop:cap (`bias_inclusive_cap`, m² + W₁ ≤ 31/40).
- CK/Deficit.lean: finite Shannon entropy on the cube, chain rule, concavity, and the deficit contraction
  `deficit_noisy_le` (BSC noise contracts k ln2 − H by (1−2p)²) — the engine of Lemma lem:contraction.
- CK/InfoContraction.lean: Lemma lem:contraction in posterior form (`infoP_noisy_le`), U1 `information_le_contraction`
  (I ≤ ρ² H(f)), BSC composition and U3 `information_degrade`, U2 `conditionalEntropy_ge_conditional` (eq:conditionalcontraction).
- CK/LargeCoordScalar.lean: eq:largecoordscalar (`large_coord_scalar`, via the κ-series, termwise) and App. B.1 concavity (`U_le_U_zero`).
- CK/Anchor.lean: `strict_anchor : StrictAnchorGoal` (eq:anchorcomparison at ρ = 3/5).
- CK/Comparison.lean: `entropy_comparison : EntropyComparisonGoal` (eq:comparison on 3/5 ≤ ρ ≤ 9/10; criterion lemma,
  λ̄ bound, convexity of λ̄, four knots, Bernstein cubics).
- CK/LargeBias.lean: Lemma lem:bias (`large_bias`). CK/LargeCoordinate.lean: Lemma lem:largecoordinate (`large_coordinate_last`).
- CK/MiddleHigh.lean: Prop prop:middle (`middle_range`) and Prop prop:high (`high_noise`, anchor + degradation).
- CK/Complementary.lean: `complementary_proved : complementaryCK` (three-class split), and
  `courtadeKumar_proved : CourtadeKumar := assemble_conditional lowNoise_proved complementary_proved`.

## Method
Each module was written by an independent agent against a fixed specification (specs/SPEC_*.md: exact target
statements + a proof plan derived from the v11 manuscript, with every constant re-checked numerically before
launch), compiled with `lake env lean` to zero errors/warnings, and then independently re-verified by a separate
agent (recompile, forbidden-token scan, `#print axioms`, hypothesis-by-hypothesis statement comparison against
the spec, trusted-hash check). Two cross-file name clashes (`avg_const`, `binaryEntropy_eq_eta_rho`) were
renamed at integration; nothing else was edited by hand. Orchestration journals are in workflow_journals/.

## What this does and does not establish (read carefully)
- It establishes: the proposition `CKF2.Spec.Target` — for every n : ℕ, every f : (Fin n → Bool) → Bool and every
  real p with 0 ≤ p ≤ 1/2, entropy(outputMean f) − average_y entropy(outputPosterior f p y) ≤ log 2 − entropy p,
  with channel p y x = ∏ᵢ (1−p if yᵢ = xᵢ else p), outputPosterior f p y = Σₓ channel p y x · 1[f x],
  entropy x = −x log x − (1−x) log(1−x) (nats; Lean's log 0 = 0 gives the usual 0·log 0 = 0) — is a theorem of
  Lean 4 + mathlib from propext, Classical.choice, Quot.sound. That proposition is the Courtade–Kumar inequality
  for uniform input and a memoryless BSC (the posterior formula is the Bayes posterior because Y is uniform).
- It does NOT establish anything outside the trusted base: the Lean kernel and elaborator (4.19.0), the mathlib
  olean cache for the pinned revision (not replayed with lean4checker --fresh), the hardware/OS, and the human
  reading of the ~50-line CKF2/Spec.lean + CK/Definitions.lean as "the conjecture". No claim of journal
  acceptance or community review is made. The manuscript's stability results (Section 7) were not formalized;
  only Theorem thm:main.
- The formalization tracks manuscript v11 (17 Sept 2026). The separate "full proof candidate" draft of the same
  date uses a different centered reduction (with a documented counterexample to its own auxiliary function at
  p = 43/2000); nothing from that draft was used.

## Layout
gate_full/ (full-mode gate: RESULT.json, build/axioms/full_ck_gate logs, manifest), gate_partial/ (partial gate on the
final tree), extended_audit/ (ExtendedAxiomAudit.lean + log), lean4checker/ (replay log + relink wrapper),
new_lean_files/ (every CK/*.lean, CKF2/Spec.lean, F2CompletionGate.lean as compiled), specs/ (task specifications),
workflow_journals/, CK.lean, CKF2.lean, lakefile.lean, lake-manifest.json, lean-toolchain, verify_kernel.py,
TRUSTED_INPUT_HASHES.json, DECLARATIONS.json, CompletionGate.lean.template, OBLIGATIONS.json, SHA256SUMS.txt.
Build tree: ~/ck_lean (with mathlib oleans); gate harness: ~/ck_f2 (`python3 verify_kernel.py --mode full --output <new dir>`).
