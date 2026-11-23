# Verified statement for the presentation

## What has been proved in Lean

The latest Kramer–Sağlam manuscript, *On the most informative Boolean function
under noise*, now has a Lean 4 formalization covering its stronger main theorem,
all active named theorem and lemma conclusions, and the specified scalar series
reductions. The formalization is pinned to the November 20, 2026 manuscript.

For uniform `X∈{0,1}ⁿ`, an independent binary symmetric noise channel producing
`Y`, and any Boolean function `f`, set `C=f(Y)`, `μ=P(C=1)`,
`q=(1−2p)²`, and `I_p=1−H(p)`. With Shannon entropy in bits,

\[
I(C;X)\le qH(C)-(q-I_p)\,4\mu(1-\mu)\le I_p.
\]

The quantifiers include every natural dimension, every Boolean function and
all real `p∈[0,1]`. The proved declaration is:

```lean
CourtadeKumar.latestPaper : CourtadeKumar.Spec.LatestPaperTarget
```

The target independently specifies the uniform cube, product channel,
conditional output probabilities and information through finite sums.

## What supports the verification claim

The final paper gate returned `ALL_ACTIVE_PAPER_RESULTS_KERNEL_CHECKED` with
both completion flags true. It built all 69 CK source modules, audited 1,016
theorem declarations and 1,173 safe declarations, covered every one of the 15
active named theorem/lemma labels, and checked all 54 required proof roots.
The declaration count includes private/generated proof helpers.

The only permitted transitive logical axioms are Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. No proof placeholders, new
mathematical axioms, unsafe source proofs or `native_decide` are permitted.
Every recorded input hash was unchanged during the final run.

A separate check restated the main theorem directly as raw finite sums,
products, indicators and binary entropy, then proved that statement and checked
its axioms. Additional exact challenges cover the arbitrary-observation
conditional Pinsker and chain rules, Markov data processing, the actual private
comparison-bit construction and the continuous threshold comparison.

## Scope worth stating precisely

The result includes the actual stronger progressive-entropy theorem. The older
repository proof of the classical cap is separate and is not the evidence for
this claim. The preliminary and comparison results include arbitrary measurable
observations; the finite alphabet in their kernels only encodes the tuple of
bits.

The continuous-threshold inequality, strictness and equality cases are proved
for the actual uniform-resampling kernel. The manuscript's broader continuous
optimization statement remains a conjecture and is not claimed as a theorem.
One scalar rescaling argument is formalized by an alternative proof of the same
inequality. This is a formalization of the mathematical conclusions, not a claim
that every intermediate display has been transcribed by the identical route.

## Where to point readers

- Main statement and proof: `CK/Spec.lean`, `CK/Latest.lean`.
- Paper-to-Lean correspondence: `PAPER_CROSSWALK.md`.
- Complete run: `verification/final-paper/result.json`.
- Scope review: `verification/PAPER_SCOPE_REVIEW.md`.
- Reproduce: `python3 scripts/verify.py --mode full --scope paper`, after
  installing the pinned Lean/mathlib dependencies as described in `README.md`.
