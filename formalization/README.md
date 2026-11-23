# Lean formalization of the latest manuscript

**Complete for all active named theorem and lemma conclusions of the latest
manuscript.** The full paper gate passed with
`ALL_ACTIVE_PAPER_RESULTS_KERNEL_CHECKED`; both
`latest_main_theorem_verified` and `all_paper_results_verified` are true.

This project follows *On the most informative Boolean function under noise*,
by Dimiter Kramer and Mert Saglam, at repository commit
`45ad4866a41e04722f2cfcef4129a1050e59d3ca` (November 20, 2026).
The latest manuscript-changing commit is
`0eb4756ce4ebd6daa803d77035cc6a60bfd70e5a`; the later main commit adds slides.
The source, PDF and slides are unchanged in the parent directory.

## Proved main theorem

For every natural dimension, every Boolean function, and every BSC parameter
`0 ≤ p ≤ 1`, the development proves both inequalities

\[
I(f(Y);X)\le Q(f(Y))\le 1-H(p),\qquad
Q(C)=qH(C)-(q-I_p)\,4\mu(1-\mu),
\]

where `q=(1−2p)²`, `I_p=1−H(p)`, `μ=P(C=1)`, and entropy is in **bits**.

[`CK/Spec.lean`](CK/Spec.lean) independently specifies the finite uniform cube,
product channel, posterior, information and exact proposition
`CourtadeKumar.Spec.LatestPaperTarget`. It assumes no information inequality.
[`CK/Latest.lean`](CK/Latest.lean) proves
`CourtadeKumar.latestPaper : CourtadeKumar.Spec.LatestPaperTarget`.
The classical cap and three-bit scalar target are separate propositions, so
proving one cannot silently satisfy another.

## Build and verify

The project pins Lean `v4.19.0` and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b` in checked configuration.
With elan, git and Python 3 installed, run from this directory:

```sh
git submodule update --init --recursive
lake exe cache get
lake build CKLatest
python3 scripts/verify.py --mode full --scope paper
```

The final successful run covers **69 CK source modules, 1,016 audited theorem
declarations, and 1,173 safe declarations**. It covers all **15 active primary
theorem/lemma labels** and **54 required proof roots**. The theorem count includes
private and generated proof helpers; it is not a count of paper claims. Every
input hash remained unchanged throughout verification.

Only `propext`, `Classical.choice`, and `Quot.sound` are accepted as transitive
axioms. Source placeholders, custom axioms, unsafe code and `native_decide` are
rejected. Compiler-generated unsafe implementation artifacts are listed
separately; they are not admitted as proof dependencies.

Both `--mode partial` and `--mode full` actually attempt the original exact
main-theorem completion challenge. The default `--scope main` preserves that
check. `--scope paper` additionally requires the reviewed obligation ledger to
cover every active named theorem/lemma label and every listed proof root to
occur in the successful theorem audit, then runs exact additional statement
challenges for the scalar, continuous and general-observation results.

Reports are written to `verification/latest/` by default; `--output` selects a
separate checkpoint. Each run invalidates an old result before checking,
records the input hashes, and rejects the run if an input changes during it.
The paper ledger and both completion challenges are hash-pinned.
`work/` is reserved for experiments and excluded from the build and version
control. Unfinished proof terms do not enter the checked project.

Earlier checkpoints, including a failed preflight caused by typeclass inference
in the added statement challenge, remain as history. They are superseded by
[`verification/final-paper/`](verification/final-paper/).

## Completed mathematics and scope

[`PAPER_CROSSWALK.md`](PAPER_CROSSWALK.md) maps manuscript labels to exact Lean
names and explains every scope distinction. The development includes:

- The stronger progressive-entropy bound, its classical consequence, all base
  dimensions, zero-mass fibres, degenerate outputs and all noise endpoints.
- The good coordinate on the actual Boolean cube, the quantitative induction
  multiplier, both gap estimates and the final dimension induction.
- The complete three-bit scalar inequality and its actual-information
  statements, including the later zero-correlation restatement.
- The closed divergence series, its exact equality cases, the comparison map's
  concavity, both pointwise bounds and the full conditional comparison.
- The explicit private-randomness comparison bit and both conclusions for
  every matching unbiased bit.
- Sharp biased divergence/information bounds, all six Tsallis-property clauses,
  conditioning gain, chain rules, conditional Pinsker and data processing.
- The continuous-threshold appendix for an actual uniform Lebesgue probability
  and resampling Markov kernel, including strictness, complete equality cases
  and independence of extra observed coordinates.

The arbitrary-observation preliminary results use actual conditional
expectations on arbitrary probability spaces, with boundedness and
measurability proving all needed integrability. The comparison and conditioning
results use measurable kernels constructed from actual regular conditional
finite joint laws. Independence and conditional probability factorization
supply the probabilistic hypotheses; no information inequality is assumed.
The finite output alphabet encodes the tuple of bits and does not restrict the
observation alphabet or its support.

Conditional quantities in the kernel statements follow the paper's definition
as averages under conditional laws. The crosswalk records their precise
relationship to the separate conditional-expectation API. No unproved equality
between two APIs is used to discharge a proof obligation.

The scalar rescaling proof uses finite geometric inequalities and an integral
covariance comparison in place of the manuscript's hyperbolic-integral route.
It proves the same infinite-series inequality with all convergence and endpoint
obligations discharged. Completion means the active named mathematical
conclusions and specified reductions, not a transcription of every displayed
intermediate calculation by the identical argument.

The continuous maximization statement is explicitly a **conjecture**, and the
older quadratic exposition inside `\iffalse` is inactive. Neither is included
in the proved-theorem claim.

## Earlier branch

The existing `lean-formalization` branch at
`a42afce1b0d2c2c2f05d5845478faa1570c14e63` uses an earlier Fourier proof and a
different specification. A fresh unchanged-source rebuild accepted
`CKF2.exactTargetAccepted : CKF2.Spec.Target`, using only the same standard
axioms. Its full gate and literal extended audit passed; the latter contains
611 print commands covering 606 distinct names.

That older theorem proves the classical cap. It is separate from the stronger
progressive-entropy theorem proved here. Its records remain under
[`verification/legacy_replay/`](verification/legacy_replay/), with separate
source-fidelity records. No legacy status is used as evidence of latest-paper
completion.

## Evidence and presentation

- [`verification/final-paper/result.json`](verification/final-paper/result.json):
  successful full paper gate, audited coverage and unchanged input hashes.
- [`verification/final-paper/paper-completion.log`](verification/final-paper/paper-completion.log):
  acceptance of the additional exact statement challenges.
- [`verification/PAPER_SCOPE_REVIEW.md`](verification/PAPER_SCOPE_REVIEW.md):
  explicit source-to-statement review and the meaning of the completion flag.
- [`verification/INDEPENDENT_REVIEW.md`](verification/INDEPENDENT_REVIEW.md):
  independent main, probability and gate reviews.
- [`verification/independent_main/Audit.lean`](verification/independent_main/Audit.lean):
  raw finite-sum restatement of the main theorem, with enforced axiom checks.
- [`paper-manifest.json`](paper-manifest.json): manuscript/PDF/macro hashes.
- [`specification-manifest.json`](specification-manifest.json): pinned target,
  compiler/dependency configuration, gates and obligation ledger.
- [`paper-obligations.json`](paper-obligations.json): active conclusions and
  their required proof roots.
- [`PRESENTATION.md`](PRESENTATION.md): precise presentation statement and
  verification summary.
- [`AGENTS.md`](AGENTS.md): proof-development contract.

The manuscript and slides remain unchanged. All work is on a dedicated
formalization branch; merging into main remains a separate decision.
