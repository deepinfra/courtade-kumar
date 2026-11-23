# Independent review of the latest-paper formalization

## Conclusion and scope

The independently stated main target agrees with the stronger theorem in the
November 20 manuscript. At the review update of 2026-11-23 02:22 UTC, the exact latest main theorem
has passed the full completion gate. `CourtadeKumar.latestPaper` has type
`Spec.LatestPaperTarget` with no scalar, probabilistic, or analytic premise.
The full gate reports `LATEST_MAIN_THEOREM_KERNEL_CHECKED`, checks every
project module in its recorded snapshot, and reports no changed input hashes
or unexpected axioms. The scalar prerequisite has been proved as
`Spec.threeBit` and supplied to the complete cube induction.

An additional independent check restated the result directly in raw finite
sums, with the indicator, product channel, entropy normalization, and both
inequalities expanded rather than hidden behind `LatestPaperTarget`.
`IndependentReview.rawFiniteSumTarget` compiled, and enforced transitive axiom
checks for it, `latestPaper`, `threeBit`, and `classicalCourtadeKumar` all
accepted exactly the permitted set. Evidence is in
`verification/independent_main/Audit.lean`, `audit.log`, and `result.json`.

This establishes the main theorem, not an automatic assertion that every
auxiliary statement in the paper has been formalized in its most general
wording. The continuous threshold and general-observation scope are tracked
separately. The auxiliary update below records the additional checked work
through 2026-11-23 02:40 UTC; it does not retroactively add those modules to the
earlier main-theorem snapshot.

This review concerns the manuscript at repository commit
`45ad4866a41e04722f2cfcef4129a1050e59d3ca` and the new `formalization/` project.
It also independently replayed the older formalization at
`a42afce1b0d2c2c2f05d5845478faa1570c14e63`. The older proof and the current
proof are distinct mathematical deliverables.

## 1. Statement correspondence

### Main target

`CK/Spec.lean` defines `LatestPaperTarget` for every natural dimension, every
Boolean function `f : (Fin n → Bool) → Bool`, and every real `p` with
`0 ≤ p ≤ 1`. This matches Theorem `thm:ck+` in `introduction.tex`, including
the full noise interval. Dimension zero adds a harmless constant-output case.

The entropy is `Real.binEntropy p / Real.log 2`, so the normalization is in
bits. The channel is the product of factors `1 − p` on equal coordinates
and `p` on unequal coordinates. `outputPosterior f p x` is the finite-sum
formula for `Pr[f(Y)=1 | X=x]`. The unconditional mean is the uniform mean
of `f(Y)`, because the product channel preserves the uniform law. Thus the
specified mutual information is `h(E f(Y)) − E h(Pr[f(Y)=1 | X])`.

The progressive bound is exactly

`q h(μ) − (q − Ip) 4 μ (1 − μ)`,

where `q=(1−2p)^2` and `Ip=1−h(p)`. Both inequalities in the manuscript's
main theorem are required. The target is not just the classical cap.

The function output is deterministic. This agrees with the manuscript's
main proof, whose one-coordinate base case lists constants, the coordinate,
and its negation. Randomized comparison bits are represented by their BSC correlation parameter.
The formal library now proves the parameter matching, profile information
identities, conditional comparison, and correlation bound. The explicit probability-space realization has also been supplied in
`RandomizedComparator.lean`: an independent-noise extension preserves the old
marginal, gives the intended conditional channel, proves unbiasedness and
information identities, and realizes the conditional comparison conclusions.

### Analytic subtargets

`ThreeBitTarget` agrees with the strict scalar inequality
`three-bit-scalar-target` for `0<ρ<1` and `0<σ≤1`. The omitted `ρ=0` case
belongs to the non-strict Markov-chain statement and must be restored by an
endpoint lemma when the scalar theorem is used.

`PointwiseComparisonTarget` has the correct profile
`ell(x,d)`, variance `1−x²`, matching equation, scaled comparison inequality,
and lower correlation bound from `remaining-proofs.tex`. Its restrictions
`|x|<1` and `|x|+|d|≤1` are the nonconstant, feasible joint-bit domain. It
does not itself assert concavity of the comparison map or its conditional
Jensen extension.

## 2. Checked progress and remaining correspondence obligations

| Manuscript component | Current formal content | Remaining qualification |
|---|---|---|
| Product binary symmetric channel | `jointLaw`, exact information/specification bridge, coordinate product factorization, conditional restrictions | Literal finite product-channel model, including zero channel probabilities |
| `Q(C) ≤ Ip` | `progressiveBound_le_capacity`, full probability/noise interval | Complete right-hand inequality |
| Good-coordinate lemma | `good_coordinate` and `jointLaw_good_coordinate` | Actual independent uniform cube coordinates; dimensions 0 and 1 use separate exact bases |
| Quadratic and Shannon information | Null-safe finite laws; `PosteriorMeasure`, `PosteriorChain`, and `PosteriorMarkov` extend entropy bounds, chains, conditional Pinsker and data processing to actual conditional expectations | Arbitrary probability spaces and observation sigma-algebras are covered by the event-factorization form; the direct mathlib `CondIndepFun` wrapper inherits its standard-Borel source assumption |
| Sharp bias comparison | `shannonInformation_le_biasCoefficient` and `quadratic_mul_biasCoefficient` | Derived from the actual binary-divergence Taylor integral and sharp endpoint coefficient |
| Profile comparison | `pointwiseComparison`, `comparisonMap_concave`, `binaryProfile_average_comparison` | Actual matching map and actual profile, with constant conditional bits included |
| Conditional comparison | `conditional_comparison` | Literal conditional laws and Markov probability factorization; no information inequality supplied as a premise |
| Induction step | `induction_step_of_threeBit`, with proved `Spec.threeBit` supplied in the final theorem | Every analytic and probabilistic prerequisite is discharged in `latestPaper` |
| Degenerate cases | `QI=0 ⇒ SI=0`, `v=0 ⇒ b=0`, direct `p=0,1` cases, direct correlation-zero case | These close the domains excluded by the nondegenerate scalar inequality |
| Cube induction | `latest_of_threeBit`, instantiated by `Spec.threeBit` | No extra hypothesis on dimension, Boolean function, bias, or noise beyond the independent specification |
| Scalar analysis | `Spec.threeBit : ThreeBitTarget`, with the tail series, rescaling, means and countable Jensen assembled | The strict comparison includes `σ=1`; the induction handles `σ=0` and noise endpoints separately |
| Continuous threshold appendix | `ThresholdSeparation.lean` proves the exact scalar formula, actual derivatives/Taylor integral, strict separation and equality classification; `ThresholdModel.lean` supplies the actual uniform-resampling kernel and entropy integral | Includes arbitrary additional independent observed coordinates; the continuous optimization conjecture remains excluded |
| Full theorem | `CourtadeKumar.latestPaper : Spec.LatestPaperTarget` | Full main gate passed; independent expanded-sum statement and axiom audit also passed |

Conditional algebra lemmas are useful progress, but should be reported with
their premises. In particular, `classical_of_latest` is only the logical
implication from the stronger theorem to the classical theorem.

The appendix's continuous-threshold comparison, its strict equality
classification, and any general measurable-variable versions of the
preliminary lemmas need their own entries in an all-paper obligation ledger.
The continuous optimization conjecture is a conjecture, not an obligation to
prove a claim made as a theorem.

## 3. Fresh replay of the older proof

The frozen older full gate was actually executed in this environment with
Lean 4.19.0 and mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

- `legacy_replay/RESULT.json` reports
  `EXACT_CK_TARGET_ACCEPTED_BY_LEAN_AXIOMS_AUDITED`.
- The full gate completed successfully in 148.115 seconds.
- `CKF2.exactTargetAccepted` has only `propext`, `Classical.choice`, and
  `Quot.sound` as transitive axioms.
- `legacy_source_fidelity.json` records no source changes before/after replay.
- The literal extended axiom-print file completed successfully in 273.315
  seconds. It contains 611 commands covering 606 distinct names; the old
  README's count is stale. No unexpected axiom occurred.
- A shared-state traversal of those same 611 roots also completed successfully
  in 4.044 seconds. It establishes an allowed-axiom upper bound for every root,
  rather than claiming a minimal exact axiom set separately for each root.

The older target uses nats and `0≤p≤1/2`. Its finite-sum semantics represent
the classical Courtade–Kumar inequality. Converting units and extending the
noise interval by complement symmetry are separate straightforward bridges.
This replay does not establish the new progressive-entropy theorem.

## 4. Is the stronger bound a shortcut consequence of the older bound?

For balanced outputs, yes: `h(μ)=4μ(1−μ)=1`, so `Q=Ip`. Constants and the
noise endpoints are also degenerate cases. These cases can reuse the older
result or direct entropy identities once their definitions are bridged.

For biased outputs and interior noise, the old CK cap and the standard
strong data-processing bound applied to the same function do not suffice.
For example, take `p=μ=1/4`. Direct calculation gives

| Quantity | Value |
|---|---:|
| `H=h(1/4)` | 0.8112781244591329 |
| `q` | 0.25 |
| `Ip=1−H` | 0.1887218755408671 |
| `T` | 0.75 |
| `qH` | 0.2028195311147832 |
| `Q=9/16−H/2` | 0.1568609377704336 |

The scalar value `I=0.17` satisfies both `I≤Ip` and `I≤qH`, but not `I≤Q`.
This is a countermodel to deriving the stronger estimate from those two
scalar inequalities alone. It is **not** a Boolean-function counterexample
to the manuscript, and it does not rule out a more elaborate reduction using
additional Boolean constructions and the universal old theorem.

The old low-noise profile estimate `I≤H−T h(p)` is also weaker than the new
bound by exactly `(1−q)(H−T)`, which is nonnegative. Thus it cannot simply be
substituted for the current induction hypothesis. The older posterior-form
SDPI in `CK.InfoContraction` may still be reusable as infrastructure, after
module names and mathematical definitions have been bridged and rechecked.

The numerical example was checked independently with high-precision mpmath,
ordinary floating-point logarithms, and the exact algebraic identity for `Q`.

## 5. Gate review and trust boundary

The exact completion challenge requires an inhabitant of
`Spec.LatestPaperTarget`. Its intended success condition is appropriate.
The main target and the all-paper completion status are correctly separate:
proving the main theorem would not by itself establish every auxiliary result.

The following assurance issues were identified in the first reviewed gate
and communicated for correction:

1. The axiom-audit source was not hash-pinned, although its output was trusted
   to certify admissible axioms.
2. Source scanning and hashing used a nonrecursive `CK/*.lean` glob while
   Lake's source scope was recursive.
3. Reusing an output directory could leave an earlier success JSON behind
   after an early exception or interruption, before the new result was saved.
4. Inputs were checked only before compilation, allowing concurrent source
   edits to invalidate attribution of the final result to the recorded hashes.
5. The manuscript manifest omitted included mathematical macro files under
   `definitions/`.

These were provenance and fail-closed-verification concerns, not evidence that
any mathematical theorem was false. Inspection of the current `verify.py`,
`AxiomAudit.lean`, and `specification-manifest.json` confirms corrections 1–4:
the audit and gate are hash-pinned; source discovery is recursive; every run
first replaces its report with `RUNNING_NOT_VERIFIED`; and both successful and
failed completed runs recheck all input hashes. The paper manifest now also
includes mathematical macro inputs. In addition, the gate compares the exact
set of imported audited project modules against the recursive source inventory,
so an unimported new source module cannot escape the audit. The audit includes
private helpers by defining module and checks the cumulative transitive axiom
union after every safe root. The completion challenge still demands a term of
the unchanged `Spec.LatestPaperTarget`.

A code-review pass through `CubeInduction.lean`, `CubeMarkov.lean`, and
`InductionStep.lean` found no new mathematical premise concealed in the cube
reduction. In particular, the induction hypothesis is applied to the two
literal coordinate restrictions; the chosen coordinate satisfies the actual
quarter-information bound; local and global Markov facts are proved from the
product density; negative channel correlation is handled by its absolute
value; and the scalar parameter satisfies its strict positivity hypotheses
only in the branch where those hypotheses are proved. This review is not a
substitute for the final build and axiom audit.

### Compiler-generated unsafe artifacts

Inspecting Lean's metadata showed `FiniteLaw.map` is safe and has only the
three permitted axioms. Its `_cstage*` and `_elambda_1` implementation helpers
are marked unsafe by the compiler. Those helpers are not logical theorem
roots. Excluding compiler-marked unsafe artifacts from the root list is
appropriate **provided every theorem and every safe project declaration is
still audited transitively** and source-level unsafe declarations remain
forbidden. No helper axiom should be added to the allowed axiom set.

Selecting roots by their defining module (`CK.*` and `CKLatest`), rather than
only by the public namespace, also includes private proof helpers. A tested
shared-state audit of the reviewed snapshot covered 330 safe declarations,
including 266 theorem declarations and generated/private proof helpers, and
excluded 138 unsafe compiler artifacts. Its transitive axiom union was exactly
the permitted three. These are snapshot implementation counts, not a count of
paper lemmas or a percentage of mathematical completion.

The shared traversal uses the standard `Lean.CollectAxioms.collect` against
the checked kernel environment, carrying its visited set between roots. If
the cumulative union contains only permitted axioms, then every audited
root's transitive axiom set is a subset of that union. Per-root records must
say `AXIOMS_SUBSET_OF`, not falsely claim the union is each root's minimal set.

The assurance boundary includes the pinned Lean toolchain and official
mathlib precompiled artifacts. Mathlib was not independently rebuilt or
replayed from source in this review. This review also does not certify future
edits absent another fresh build, source check, and axiom audit.

## 6. Main verification evidence and remaining paper scope

The recorded main-theorem gate built `CKLatest` in 60.806 seconds, audited its
project declarations in 6.294 seconds, and accepted the exact completion term
in 3.634 seconds. Its snapshot includes 742 theorem declarations and 855 safe
declarations; 206 unsafe compiler implementation artifacts were explicitly
listed and excluded as roots. The source-module coverage, paper hashes,
specification hashes and before/after source hashes all matched. These counts
include generated and helper declarations; they do not count paper lemmas.

The independent raw finite-sum target check completed in 10.558 seconds and
recorded unchanged source hashes for `Spec`, `Latest`, `CubeInduction`,
`ScalarThreeBit` and its own audit source. Every checked target had only
`propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Inspection
of `Latest.lean` confirms that `Spec.latest_of_threeBit Spec.threeBit` supplies
the actual scalar theorem, rather than assuming it.

The comparison-map proof uses the decreasing derivative ratio
`ρ L(ρt)/L(t)`, with `L(t)=log(1+t)−log(1−t)`. Supporting lines cover the
information endpoints. The continuous-threshold scalar proof separately
cancels the entropy singularities into a smooth logarithmic expression,
proves its actual second derivative and Taylor integral on the closed noise
interval, and deduces strict comparison and all stated equality cases.

The explicit randomized comparison-bit realization has been compiled in
`RandomizedComparator.lean`. At the earlier main-gate checkpoint the remaining
scope checks concerned the literal uniform-resampling threshold semantics and
the extension of auxiliary observed-variable lemmas beyond finite laws. Those
subsequent developments are reviewed below. The continuous maximization
conjecture remains excluded from proof claims.
Subsequent full-gate snapshots must include newly promoted auxiliary files;
the initial main gate should not be represented as having audited later edits.

## 7. Auxiliary scope review through 02:40 UTC

The actual continuous threshold model is now supplied. `uniformUnit` is
Lebesgue measure restricted to `[0,1]`, proved to be a probability measure.
`resamplingKernel` is the mixture `ρ δ_x + (1−ρ) uniformUnit`. The threshold
posterior is its actual mass of `(-∞,μ]`, its mean and entropy integral are
evaluated, and `kernelInformation_eq` identifies the scalar information used
in the calculus proof. The inequality, strict interior comparison, complete
equality classification, and closed-noise endpoint identities therefore hold
for this literal continuous resampling model. The product-observation wrapper
proves that adding independent observed coordinates leaves the information
unchanged.

The quantitative induction theorem supplies `∃ λ ≥ 0, Δ/(1+λ) ≤ g` without
assuming `Δ≥0`. Its endpoint and zero-information branches choose a concrete
valid multiplier, and the nondegenerate branch supplies the paper's multiplier
from proved bounds. The scalar prerequisite is the proved `Spec.threeBit`.
This establishes the literal quantitative claim in addition to the implication
`Δ≥0 → g≥0` used to close the main induction.

The randomized comparison construction preserves the original finite marginal
and uses independent bit noise. `MatchingComparator.every_matching_comparator`
also proves the manuscript's universal clause. The requirement that the signed
conditional `A–B` correlation equal its unconditional value is faithful to
joint independence of `(A,B)` and `U`: with unbiased conditional marginals,
that correlation determines all four joint cell probabilities. A fixed absolute
correlation alone would allow signs to cancel across observations and would
not justify the same unconditional comparator. The arbitrary-observation
construction uses the same fixed-channel principle with measurable finite
kernels and almost-everywhere hypotheses.

`PosteriorMeasure` proves posterior bounds, the variance identity, Shannon and
quadratic comparisons, and the sharp bias bound on arbitrary probability
spaces. `PosteriorChain` defines conditional entropy using actual conditional
expectation, proves chain rules on joined sigma-algebras, proves conditional
Jensen by disintegrating the real posterior, and derives conditional Pinsker,
nonnegativity, the upper entropy bound, the unbiased reverse bound, and the
squared posterior-update identity. These statements have no finite observation
or finite-support assumption.

`PosteriorMarkov` derives posterior sufficiency from conditional factorization
against every measurable event of the last observation. Its pi-system proof
extends equality of set integrals from intersections to the full joined
sigma-algebra, after which uniqueness of conditional expectation applies.
Both Shannon and quadratic data processing follow. The hypothesis is the
conditional-independence event criterion for a binary input; neither posterior
sufficiency nor an information inequality is supplied as a premise. A direct
wrapper from mathlib's `CondIndepFun` is also proved. Mathlib places a
standard-Borel assumption on the original space in that definition; the
underlying event-factorization theorem has no such assumption.

`ConditionalKernel` constructs a genuine finite conditional law from
`condDistrib`. Every finite moment is identified with its actual conditional
expectation. Averaging conditional laws recovers the original observable
integral, and genuine independence makes the conditional observable moments
constant almost everywhere. `ObservationComparison` derives the required
fixed conditional channel from actual joint independence, and its four-cell
conditional-probability equations express private randomness given `(B,U)`
without assuming an information comparison. The finite conditional laws then
satisfy the Markov factorization needed by the comparison proof.

`ThreeBitRestatement.three_bit_information_restated` additionally includes
zero first-channel correlation and uses the literal conditional-information
numerator and conditional-quadratic-entropy denominator in the later
restatement. Its `q=0` case is proved directly; its positive case follows from
the strict actual three-bit theorem.

An independent transitive audit of ten principal auxiliary declarations passed
in 17.017 seconds at 02:38:16 UTC, with unchanged recorded source hashes and
only `propext`, `Classical.choice`, and `Quot.sound`. Evidence is in
`verification/independent_probability/`. It covers conditional Jensen,
conditional Pinsker, both data-processing APIs, the actual conditional-kernel
bridge, threshold equality classification, the universal finite comparator,
and the quantitative induction theorem. That ten-root snapshot predates the
later restatement and later arbitrary-observation wrappers, which must appear
in the final full gate.

## 8. Frozen paper-wide gate review

The reviewed `--scope paper` path preserves the independent main target and
requires a reviewed obligation ledger, every referenced proof root among the
audited theorem declarations, no open obligations, coverage of active named
theorem/lemma labels, and additional exact statement challenges. It scans every
manifested TeX file, removes the inactive `iffalse` block, and finds labels
inside the named theorem environments. For this frozen manuscript there are
15 active named theorem/lemma labels. The two inactive lemmas and the explicit
continuous optimization conjecture are correctly excluded. The later
three-bit restatement is additionally represented in the ledger.

The obligation ledger and `scripts/PaperCompletionGate.lean` are now included
in the trusted manifest and therefore in the before/after hash check. The extra
challenge includes exact arbitrary-observation conditional Pinsker, conditional
chain, data processing, and actual conditional-law comparator statements, in
addition to main/scalar/threshold challenges. The original main-theorem
success remains a separate status. A missing proof root, a source change during
the run, an undeclared axiom, or a failed exact challenge prevents paper-wide
success.

The checked ledger contains 17 obligations and 54 distinct required proof
roots, covering the 15 active named results and the two additional series
reductions. The source-to-statement review checks the actual hypotheses,
normalization, parameter domains, null cases, and quantifiers; theorem-name
presence alone would not establish that correspondence. The paper-wide scope
is all active named theorem and lemma conclusions, plus the listed series
reductions. It permits alternate proofs of the same conclusions and does not
claim that every displayed intermediate calculation follows the manuscript's
identical derivation.

The final frozen full paper gate has now passed with status
`ALL_ACTIVE_PAPER_RESULTS_KERNEL_CHECKED`; both the main-theorem and paper-wide
verification flags are true. `verification/final-paper/result.json` records
69 `CK` modules, 1,016 audited theorem declarations, 1,173 safe declarations,
and 223 explicitly excluded compiler implementation artifacts. All 54 required
proof roots were audited, all 15 active named theorem/lemma labels were covered,
every exact completion challenge passed, and no input hash changed during the
run. This supports completion of the reviewed paper-wide scope stated above.
The pinned Lean compiler and official mathlib precompiled artifacts remain
within the stated trust boundary.
