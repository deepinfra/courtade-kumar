# Lean 4 formalization of the Courtade–Kumar inequality (manuscript v11 route)

This directory contains a complete, kernel-checked Lean 4 formalization of the proof of the
Courtade–Kumar inequality given in *Entropy mixing and stability under Boolean noise*
(D. Kramer, reader and reuse edition v11, 17 September 2026; PDF and wrapper `.tex` at the repository root, section sources in `manuscript/src/`).

**Claim, precisely.** The Lean proposition `CKF2.Spec.Target` (file `lean/CKF2/Spec.lean`, ~50 lines,
frozen since session 5 and hash-pinned by the gate) is

```lean
def Target : Prop :=
  ∀ (n : ℕ) (f : BitVector n → Bool) (p : ℝ),
    0 ≤ p → p ≤ 1 / 2 → retainedInformation f p ≤ Real.log 2 - entropy p
```

with `BitVector n := Fin n → Bool`, `channel p y x := ∏ i, if y i = x i then 1 - p else p`,
`outputPosterior f p y := ∑ x, channel p y x * bitValue (f x)`,
`retainedInformation f p := entropy (outputMean f) - average (fun y => entropy (outputPosterior f p y))`,
`entropy x := -x * log x - (1 - x) * log (1 - x)` (natural logarithm; Lean's `log 0 = 0` gives the
usual `0 log 0 = 0`). For uniform input `X` on `{0,1}^n` and `Y` obtained by independent bit flips with
probability `p`, `outputPosterior f p y` is the Bayes posterior `P(f(X) = 1 | Y = y)` (because `Y` is
uniform), so `Target` says `I(f(X); Y) ≤ ln 2 − h(p)` for every `n`, every Boolean `f` and every
`p ∈ [0, 1/2]`: the Courtade–Kumar inequality in nats.

The theorem `CKF2.exactTargetAccepted : CKF2.Spec.Target` is proved by `CK.courtadeKumar_proved`
(`lean/CK/Complementary.lean`), which is `assemble_conditional lowNoise_proved complementary_proved`.

## Verification status (18 Sept 2026)

| Check | Result |
|---|---|
| `gate/verify_kernel.py --mode full` | `EXACT_CK_TARGET_ACCEPTED_BY_LEAN_AXIOMS_AUDITED` (`gate/results/gate_full/RESULT.json`) |
| Axioms of `CKF2.exactTargetAccepted` | `[propext, Classical.choice, Quot.sound]` |
| Extended audit, all 605 project declarations | each depends only on a subset of those three axioms (`verification/extended_axioms.log`) |
| Static hygiene, all 42 source files | no `sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`, `skipKernelTC` |
| Independent kernel replay (lean4checker v4.19.0), 41 project modules | 0 failures (`verification/lean4checker_replay.log`); mathlib itself not replayed |
| Trusted inputs (`Definitions.lean`, `Spec.lean`, `lean-toolchain`, gate template, declaration list) | SHA-256 unchanged since session 5 (`gate/TRUSTED_INPUT_HASHES.json`) |
| Toolchain | Lean 4.19.0, mathlib rev `c44e0c8ee63ca166450922a373c7409c5d26b00b` (`lean/lake-manifest.json`) |
| Final adversarial review (statement semantics, trust base, proof architecture, completeness critic) | 4 × SOUND (`notes/FINAL_REVIEW.md`); the critic re-replayed all 43 modules / 942 constants and recompiled modules from source to byte-identical oleans |

## Reproduce

```sh
# Lean 4.19.0 via elan; from this directory:
cd lean
lake exe cache get          # prebuilt mathlib oleans for the pinned revision (~4.7 GB)
lake build CK CKF2          # builds every module (minutes)
cd ../gate
python3 verify_kernel.py --mode full --output ./results/my_run --timeout 1800
# expected: "status": "EXACT_CK_TARGET_ACCEPTED_BY_LEAN_AXIOMS_AUDITED"
```

`gate/lean` is a symlink to `../lean`; the gate hashes the trusted inputs, rejects any forbidden token in
any source file, builds the project, audits the 32 inherited declarations, and in full mode compiles the
frozen `CompletionGate.lean.template` (which only does `exact CK.courtadeKumar_proved`) and prints its axioms.

Independent replay: build [lean4checker](https://github.com/leanprover/lean4checker) at tag `v4.19.0`
and run `lake env lean4checker <Module>` from `lean/` for each module listed in `lean/CK.lean`, plus
`CKF2.Spec` and `F2CompletionGate` (on macOS 26 the binary must be relinked with the system clang, see
`verification/sysclang.sh`). `lean4checker --fresh` (replaying mathlib too) was not run.

## What a skeptical referee should still ask for (from the critic)

1. A tagged commit with CI on a fresh runner: `lake exe cache get`, a real `lake build`, the gate, `#print axioms`,
   and lean4checker over every project module.
2. One `lean4checker --fresh F2CompletionGate` run (or a mathlib rebuild from source) to remove the prebuilt-olean
   assumption, which is the largest residual.
3. An independent human expert's sign-off on `lean/CKF2/Spec.lean` and `lean/CK/Definitions.lean` (about 50 lines).

## What is trusted

The Lean 4.19.0 kernel and elaborator; the mathlib olean cache for the pinned revision; the machine; and the
human reading of `lean/CKF2/Spec.lean` together with `lean/CK/Definitions.lean` as the conjecture stated
above. Nothing else: every other file is checked by the kernel. No claim of journal acceptance or community
review is made here. The manuscript's Section 7 (stability) was not formalized.

## Layout

- `lean/` — the Lean project. `CK/Definitions.lean` (model and target), `CK/AnalyticTargets.lean` (goal
  statements), and 38 proof modules; `CKF2/Spec.lean` (independent spelling of the target);
  `F2CompletionGate.lean` (the gate's challenge, as compiled); `ExtendedAxiomAudit.lean`.
- `gate/` — fail-closed verification harness and the two final runs (`results/gate_full`, `results/gate_partial`).
- `verification/` — extended axiom audit log, lean4checker replay log, relink wrapper.
- `notes/SESSION8_NOTE.md` — what was proved in the final session, module by module, with manuscript labels;
  `notes/OBLIGATIONS.json` — the obligation table (every layer closed); `notes/FINAL_REVIEW.md` — the final
  adversarial review; `notes/specs/` — the fixed target statements and proof plans each module was written
  against; `notes/SESSION7_NOTE.md` — the state before the final session.
- `manuscript/src/` — the v11 LaTeX section sources (the PDFs live at the repository root) and `manuscript/EQUATION_CROSSWALK.md`.
- `orchestration/` — machine-readable journals of the agent runs that produced and re-verified each module.

## Correspondence with the manuscript

| Manuscript | Lean |
|---|---|
| Lemma 2.2 (small-gap coordinate), Lemma 2.3 (posterior mixtures), Prop. 2.4 (restriction–mixing) | `CK/SmallGap.lean`, `CK/Sections.lean`, `CK/ProfileInduction.lean` |
| Theorem thm:linear-mixing / Lemma 2.1 | `CK.linear_scalar_mixing`, `CK.scalar_mixing` (`CK/ScalarMixing.lean`) |
| Lemma lem:product, curvature inequality, Lemma lem:transfer | `CK/Curvature.lean`, `CK/ProductCentering.lean`, `CK/Transfer.lean` |
| Appendix A centered estimates | `CK/InteriorEstimate.lean`, `CK/EndpointCommon.lean`, `CK/EndpointSmall.lean`, `CK/EndpointLarge.lean` |
| Corollary cor:low | `CK.lowNoise_proved` |
| Lemma lem:contraction | `CK/Deficit.lean` (`deficit_noisy_le`), `CK/InfoContraction.lean` (`infoP_noisy_le`) |
| Lemma lem:bias, Lemma lem:largecoordinate (+ App. B) | `CK/LargeBias.lean`, `CK/LargeCoordinate.lean`, `CK/LargeCoordScalar.lean` |
| Lemma lem:antipodal, Lemma lem:rademacher (+ App. D), Lemma lem:balancedcap, Prop. prop:cap | `CK/FourierCap.lean`, `CK/SignSum.lean` |
| Sec. 6.1 spectral identities, Lemma lem:energy | `CK/Fourier.lean`, `CK/NoiseOperator.lean` |
| Lemma lem:comparison (App. E), strict anchor | `CK/Comparison.lean`, `CK/Anchor.lean` |
| Prop. prop:middle, Prop. prop:high | `CK/MiddleHigh.lean` |
| Sec. 6.6 proof of Theorem thm:main | `CK.complementary_proved`, `CK.courtadeKumar_proved` (`CK/Complementary.lean`) |
| Appendix F rational constants | `CK/LogEnclosure.lean`, `CK/Constants.lean` |

## Known cosmetic issue

Header comments in a few early files (`CK/Definitions.lean`, `CK/Algebra.lean`, `CK/AnalyticTargets.lean`,
`CK/Induction.lean`, `CK/Semantics.lean`, `gate/CompletionGate.lean.template`) still say "uncompiled draft" /
"expected to fail": they were written before a Lean toolchain was available. They have no logical effect and
were deliberately left untouched so that the verified files match the gate's hash manifest and the audit logs
byte-for-byte (`Definitions.lean` and the gate template are hash-pinned trusted inputs).

## Provenance

The mathematics is the manuscript's. The Lean development was produced across eight sessions by Claude
(Anthropic) under the manuscript author's direction: each module was written against a fixed specification
(`notes/specs/`), compiled to zero errors and zero warnings, and re-verified by an independent agent
(recompilation, forbidden-token scan, `#print axioms`, statement comparison against the specification,
trusted-hash check) before integration. No proof-relevant file was edited by hand except two lemma renames
to resolve cross-module name clashes.
