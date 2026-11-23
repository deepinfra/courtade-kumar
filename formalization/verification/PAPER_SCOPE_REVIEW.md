# Final paper-scope review

## Reviewed object

The unchanged manuscript at repository commit
`45ad4866a41e04722f2cfcef4129a1050e59d3ca`, with its latest manuscript change at
`0eb4756ce4ebd6daa803d77035cc6a60bfd70e5a`, has **15 active primary named theorem
and lemma labels**. The reviewed ledger in `paper-obligations.json` covers all
15, with two further entries for the closed divergence series/equality cases
and the scalar tail-rescaling/common-exponent argument.

The scalar/comparison and probability workstreams separately reviewed the
source-to-statement correspondence. The probability workstream also reviewed
the verification implementation without changing it. The recovery/review
workstream independently checked the main theorem after restating it as raw
finite sums and reviewed the final general-observation and gate scope.
These are separate review passes in this development, not a claim of external
human certification or verification by a second proof-assistant kernel.

## Scope conclusions

- The main theorem has every natural dimension, every Boolean function, and
  the full closed BSC parameter interval. Entropy is in bits. Both inequalities
  in the stronger progressive-entropy result are proved.
- The quantitative induction lemma supplies an actual nonnegative multiplier
  and does not assume nonnegativity of the conditional gap.
- The three-bit theorem has an exact strict scalar target and an actual
  Shannon/Tsallis information form. Its later conditional-information
  restatement also includes zero first-channel correlation.
- Comparison existence uses an explicit private BSC randomizer. Both comparison
  inequalities also hold for every matching unbiased comparison bit.
- General observations are not restricted to finite or countable alphabets.
  The finite alphabet in the kernel statements encodes the joint tuple of
  bits. Genuine regular conditional distributions, expectation identities,
  independence, and probability-factorization Markov assumptions supply the
  corresponding finite conditional laws.
- The general conditioning-gain theorem has exactly the manuscript's ratio
  and normalization. Its assumptions are actual independence, the context's
  unbiasedness, and positive conditional Tsallis entropy.
- General chain rules, conditional Pinsker, entropy bounds and Markov data
  processing are proved for actual conditional expectations. Data processing
  derives posterior sufficiency from event factorization. The optional adapter
  to mathlib's `CondIndepFun` carries that predicate's standard-Borel assumption;
  the underlying event-factorization theorem has no such restriction.
- The continuous appendix uses an actual uniform Lebesgue probability measure
  and resampling Markov kernel, with the full strictness and equality
  classification and independent extra observed coordinates.

The paper defines conditional quantities as averages under conditional laws.
The comparison and conditioning kernels implement that definition. No unproved
identification of their integrated Shannon information with the separate
`Posterior.shannonInformationGiven` API is claimed or used to discharge a proof
obligation. Their conditional-law moments and the relevant posterior entropy
quantities have explicit bridges to actual conditional expectations.

The continuous maximization conjecture is not asserted as a theorem. The old
quadratic exposition inside `\iffalse` is inactive. An alternative proof of a
scalar rescaling inequality proves the same result without reproducing every
hyperbolic-integral calculation from the manuscript.

## Verification contract

The original `CK/Spec.lean` and `scripts/CompletionGate.lean` are unchanged.
The additional `--scope paper` mode requires the reviewed ledger to cover every
active named theorem/lemma label, requires every listed proof root to occur
among the successfully audited theorem declarations, and runs extra exact
statement challenges. The additional challenges explicitly include the general
conditional Pinsker and chain identities, Markov data processing, and actual
arbitrary-observation comparison construction.

The ledger, extra challenge and verification implementation are hash-pinned in
`specification-manifest.json` and included in before/after input snapshots.
Any changed input clears both completion flags and fails the run. Missing
labels, open obligations, absent proof roots, an incomplete scope review, or a
failed statement challenge prevent paper-wide success.

`all_paper_results_verified` means that this reviewed active-result scope has
passed those checks. Source-to-statement correspondence is an explicit review
responsibility; the script does not purport to automatically prove equivalence
between TeX prose and Lean propositions. The authoritative final run is
`verification/final-paper/result.json`.
