# Lean formalization of the latest manuscript

**Status: active development; the latest stronger main theorem is not yet proved.**

This project follows *On the most informative Boolean function under noise*,
by Dimiter Kramer and Mert Saglam, at repository commit
`45ad4866a41e04722f2cfcef4129a1050e59d3ca` (main, November 20, 2026).
The latest manuscript-changing commit is
`0eb4756ce4ebd6daa803d77035cc6a60bfd70e5a`; the later main commit adds slides.
The source and PDF are the unchanged files in the parent directory.

## Exact goal

For every dimension, every Boolean function, and every BSC parameter
`0 ≤ p ≤ 1`, prove both inequalities

\[
I(f(Y);X)\le Q(f(Y))\le 1-H(p),\qquad
Q(C)=qH(C)-(q-I_p)\,4\mu(1-\mu),
\]

where `q=(1−2p)²`, `I_p=1−H(p)`, `μ=P(C=1)`, and entropy is in **bits**.

[`CK/Spec.lean`](CK/Spec.lean) independently spells out the finite uniform
cube, product channel, posterior, information, and the exact proposition
`CourtadeKumar.Spec.LatestPaperTarget`. It does not assume an information
inequality. The final theorem must be named `CourtadeKumar.latestPaper` and
inhabit precisely that proposition. The classical cap and three-bit scalar
target are separate propositions, so proving one cannot silently satisfy another.

## Build and verify

The project pins Lean `v4.19.0` and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b` in the checked configuration.
With elan, git, and Python 3 installed, run from this directory:

```sh
git submodule update --init --recursive
lake exe cache get
lake build CKLatest
python3 scripts/verify.py --mode partial
python3 scripts/verify.py --mode full
```

The partial gate builds every imported project module, checks source and
specification hashes, and audits transitive axioms of every safe project
declaration selected by source module, including private proof helpers.
Only `propext`, `Classical.choice`, and `Quot.sound` are accepted.
Source-level placeholders, custom axioms, unsafe code, and `native_decide`
are rejected. Compiler-generated unsafe implementation artifacts are listed
separately; they are not admitted as proof dependencies.

Both modes actually attempt the exact completion challenge. **Full mode
currently exits with code 2 because the latest main theorem is absent.**
A successful partial build must not be described as a complete formalization.
The report also keeps `all_paper_results_verified` false: the main theorem
alone would not certify every appendix result.

Reports are written to `verification/latest/` by default; `--output` selects
a separate checkpoint. Each run invalidates any old result before checking,
records the input hashes, and rejects a run if those inputs change during it.
`work/` is reserved for uncompiled experiments and is excluded from the build
and version control. Unfinished proof terms do not enter the checked project.

## Completed components and remaining work

See [`PAPER_CROSSWALK.md`](PAPER_CROSSWALK.md) for the correspondence to manuscript
labels, theorem names, and the scope of each result. The completed development
includes the cap `Q(C) ≤ I_p`, the good coordinate on the actual Boolean cube,
finite probability and posterior laws, Shannon/Tsallis estimates, the strengthened
conditioning gain, complete pointwise comparison, comparison-map concavity,
and substantial scalar-series arguments. Conditional comparison, the complete
three-bit argument, probabilistic gap assembly, and final cube induction are
still being connected.

The finite probability layer makes all zero-mass conventions explicit. Its
results cover the finite observations needed by the Boolean-cube theorem.
They are not represented as proofs for arbitrary measurable observation spaces.
The continuous maximization statement in the introduction is a **conjecture**;
formalizing the paper does not mean claiming that conjecture has been proved.

## Earlier branch

The existing `lean-formalization` branch at
`a42afce1b0d2c2c2f05d5845478faa1570c14e63` uses an earlier Fourier proof and a
different theorem specification. A fresh unchanged-source rebuild accepted
`CKF2.exactTargetAccepted : CKF2.Spec.Target`, with only the same three standard
axioms. Its full gate and the literal extended audit passed; the latter contains
611 print commands covering 606 distinct names.

The old theorem proves the classical information cap, not the stronger
progressive-entropy theorem above. Its verification records are preserved under
[`verification/legacy_replay/`](verification/legacy_replay/), with separate
source-fidelity records. No legacy status is used as evidence that the latest
target is complete.

## Provenance and review

- [`paper-manifest.json`](paper-manifest.json): manuscript/PDF/macro hashes and
  upstream commits.
- [`specification-manifest.json`](specification-manifest.json): frozen target,
  compiler/dependency configuration, and reviewed gates.
- [`verification/checkpoint-5/result.json`](verification/checkpoint-5/result.json):
  a completed build and audit, followed by the deliberately unsatisfied full
  completion challenge (exit 2); subsequent proofs require a later run.
- [`AGENTS.md`](AGENTS.md): the proof-development contract.

The manuscript is not edited by this project. Changes live on a dedicated
formalization branch; merging into main is a separate decision.
