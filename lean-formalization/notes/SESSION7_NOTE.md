# Session 7 note (17 Sept 2026)

## Environment change — the blocker of sessions 1–6 is gone
Host: 10-core arm64 macOS (24 GB), Lean 4.19.0 (elan), mathlib v4.19.0 pinned at
rev c44e0c8ee63ca166450922a373c7409c5d26b00b per the inherited lake-manifest.json.
`lake exe cache get` now works: 6311 prebuilt oleans (4.7 GB) downloaded in minutes.
No mathlib module was compiled from source. One macOS-specific fix was needed:
the `cache` executable linked by the bundled lld lacks the SG_READ_ONLY flag on
__DATA_CONST and is killed by the Darwin 25 dyld; relinking it with the system
clang (`LEAN_CC` pointed at a wrapper adding the toolchain's lib path for -lgmp)
resolves it. Toolchain binaries themselves are unaffected.

## New kernel-checked results this session

### Layer B (added later in session 7) — the analytic core of Lemma 2.1
5. `CK.curvature_identity : CurvatureGoal` (CK/Curvature.lean): the manuscript's
   curvature inequality (eq:curvaturepositive). Proved integral-free: the
   manuscript's integral is an FTC evaluation of the explicit primitive `psiCurv`,
   shown monotone on [x,y]; the integrand signs come from `atanhLog u >= u` and
   concavity of `wAux = 2u*eta - (1-u^2)*atanhLog` (zero endpoints, w'' = -2*atanhLog).
   The x = 0 boundary is an exact removable-singularity rewrite (Lean's 0/0 = 0
   junk value coincides with the continuous extension), no limit arguments.
6. `CK.product_centering : ProductCenteringGoal` (CK/ProductCentering.lean):
   Lemma [lem:product], K >= K0 and K*M >= K0*M0. The z-derivative of Q*L is
   curvatureGap|nu-z|(nu+z)/4 >= 0 by (5); K and K*M are then nondecreasing in nu.
   The nu+t = 1 boundary needs no limits: the nu-space functions contain only eta,
   which is continuous everywhere.
7. `CK.transfer_product`, `CK.transfer_gain`, `CK.transfer_relative`
   (CK/Transfer.lean): Lemma [lem:transfer] plus the retained-denominator
   transfer eq:relative-transfer (added after adversarial review flagged it as
   consumed by centered-estimate regime 3), plus `CK.pairEntropy_le_eta` (M <= M0).
8. CK/GainBounds.lean (start of layer C): `CK.gain_integral` (eq:gainintegral,
   integral-free — `Lpair_le` is exactly the midpoint-Jensen step), `atanhLog u/u`
   monotonicity, the eq:Bbounds entropy-remainder bounds as log inequalities, and
   `binaryEntropy_le_mul` (h(p) <= p(ln(1/p)+1)).
9. CK/EtaDeriv.lean: the calculus layer B1/B2 — eta' = -atanhLog,
   atanhLog' = curvature, parity, monotonicity, continuity, and
   `CK.kappa_ge_half_sq` (eq:entropyfacts) from `CK.pinsker`.

### Earlier in session 7
1. `CK.pinsker` (CK/Pinsker.lean): binaryEntropy mu <= Real.log 2 - (2*mu-1)^2/2
   on [0,1] — the manuscript's kappa(u) >= u^2/2 step. Proof as drafted in session 6
   (monotoneOn_of_deriv_nonneg + first atanh term); two tactic-level fixes.
2. `CK.lowNoiseCK_of_scalar : ScalarMixingClaim -> lowNoiseCK` (CK/Pinsker.lean):
   the low-noise branch is now conditional on Lemma 2.1 ALONE.
3. `CK.logEnclosure_proved : LogEnclosureGoal` (CK/LogEnclosure.lean): the
   Appendix E/F series enclosure logPartial N v <= log v <= logPartial N v + logTail N v
   on [1,2]. One tactic-level fix (explicit `(hasSum_nat_add_iff (f := ...) N).mpr`).
4. `CK.AppF.*` (CK/Constants.lean, NEW, 62 declarations): every rational comparison
   of the constants appendix discharged from logEnclosure_proved at N = 12 with the
   splitting log(2^k r) = k log 2 + log r: 27 two-sided log brackets (10^-12 grid),
   the 15 manuscript log rows, the 4 lambda-bar knot inequalities, the 7
   binary-entropy rows, 2 combined and 3 rational comparisons. Generated
   programmatically; every emitted bound re-verified in exact rational arithmetic
   (Fractions) before emission. Layer F of OBLIGATIONS.json is closed.

## Verification state
- F2 partial gate: PASSED (PARTIAL_MODULE_BUILD_AND_AXIOM_AUDIT_PASSED), 22 source
  files, 0 warnings, 32 pinned declarations with axioms exactly
  [propext, Classical.choice, Quot.sound] (gate_run/RESULT.json). Trusted-input
  hashes: the session-5 repinned set (Definitions.lean import narrowing documented).
- Extended audit: 266 declarations across all 20 CK modules + CKF2.Spec; every one
  depends on exactly [propext, Classical.choice, Quot.sound]
  (extended_audit/extended_axioms.log). sorry/admit/axiom/native_decide: none
  (gate hygiene scan).
- Regression: all 82 session-5/6 declarations replay unchanged.

## Statement-fidelity review (adversarial, 3 independent reviewers + critic)
All three reviewers returned FAITHFUL. Material notes:
- ScalarMixingClaim is v10 Lemma 2.1 verbatim (p^2/25 remainder) and is implied by
  v11's thm:linear-mixing (p/500 remainder, equality at p = 1/20): the conditional
  chain is stated in the safe (weaker-hypothesis) direction. v11's exact form is
  carried separately as LinearScalarMixingClaim. Docstring citations still say
  "v9.1 Lemma 2.1" / "Appendix G" (cosmetic, should be refreshed to v11 labels).
- binaryEntropy's junk values at {0,1} equal the intended limits (Real.log 0 = 0);
  no vacuity or junk-value exploit on [0,1].
- The enclosure matches v11 Appendix E (app:constants) term-for-term, including the
  v = 2 endpoint. The Lean file titles it "Appendix F" (naming drift only).
- Version caveat: the 2026-09-17 "full proof candidate" tex diverges from v11
  (threshold 43/2000 instead of 1/20; a documented internal counterexample at
  p = 43/2000 in its own low-noise reduction). The Lean development tracks v11.
  If that draft supersedes v11, no current manuscript proves ScalarMixingClaim on
  the full p <= 1/20 range.

## What remains (unchanged in kind, reduced in size)
NOT proved: ScalarMixingClaim (Lemma 2.1: the C-layer centered estimates C1-C5
and their assembly; layer B is now fully proved), the complementary branch
(layers D, E), CK.courtadeKumar_proved, the full F2 gate.
`CK.courtadeKumar_proved` does not exist. The honest label on this package is:
low-noise branch conditional on Lemma 2.1 alone; complementary branch not started;
constants appendix fully kernel-checked.

Critical path next: the Appendix app:centered estimates C1-C5, the
(nu,t) <-> (a,b) coordinate bridge, and their assembly into CK.scalar_mixing.
Layer B and the AppF constants those estimates consume are in place.

## Layout
- gate_run/            fresh gate output (RESULT.json, build.log, axioms.log, manifest)
- extended_audit/      ExtendedAxiomAudit.lean + full #print axioms log (196 decls)
- new_lean_files/      CK.lean, Pinsker.lean, LogEnclosure.lean, Constants.lean as compiled
- diffs/               unified diffs vs the session-6 drafts (2 tactic fixes + imports)
- OBLIGATIONS.json     updated table (F1 closed; G1 sharpened; blocker resolved)
- lake-manifest.json, lean-toolchain   exact pins used

Build tree: ~/ck_lean (project + mathlib olean cache); gate harness: ~/ck_f2.
