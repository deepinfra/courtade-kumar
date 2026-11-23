# Independent review of the latest-paper formalization

## Conclusion and scope

The independently stated main target agrees with the stronger theorem in the
November 20 manuscript. At the review update of 2026-11-23 02:14 UTC, the compiled theorem
`Spec.latest_of_threeBit` reduces the exact complete main target to the single
independently stated analytic proposition `Spec.ThreeBitTarget`. All finite-law
comparison, sharp bias, conditional-channel, good-coordinate, base-case and
dimension-induction dependencies have been discharged. The scalar prerequisite
was still being completed at this checkpoint, so this update does **not** claim
a closed proof of the main target. The current full-gate report must determine
whether a subsequent run has discharged that prerequisite. Every-result
completion remains distinct from main-theorem completion.

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
identities, conditional comparison, and correlation bound. A separate explicit
probability-space realization of a comparison bit is not needed for the cube
proof, but is relevant if every auxiliary lemma is required in the paper's
random-variable wording.

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
| Quadratic and Shannon information | Null-safe finite laws, chain rules, symmetry, covariance, independence criterion, conditioning gain | Finite observations suffice for the main theorem; arbitrary measurable observations remain a wider scope |
| Sharp bias comparison | `shannonInformation_le_biasCoefficient` and `quadratic_mul_biasCoefficient` | Derived from the actual binary-divergence Taylor integral and sharp endpoint coefficient |
| Profile comparison | `pointwiseComparison`, `comparisonMap_concave`, `binaryProfile_average_comparison` | Actual matching map and actual profile, with constant conditional bits included |
| Conditional comparison | `conditional_comparison` | Literal conditional laws and Markov probability factorization; no information inequality supplied as a premise |
| Induction step | `induction_step_of_threeBit` | Sole analytic prerequisite is the explicit `ThreeBitTarget`; all probability and bias bounds discharged |
| Degenerate cases | `QI=0 ⇒ SI=0`, `v=0 ⇒ b=0`, direct `p=0,1` cases, direct correlation-zero case | These close the domains excluded by the nondegenerate scalar inequality |
| Cube induction | `latest_of_threeBit : ThreeBitTarget → LatestPaperTarget` | Every finite-law assumption is discharged by the actual product law, with no extra hypotheses on the Boolean function |
| Scalar analysis | All-index coefficient bounds, endpoint sums, tail rescaling and mean identities | Final Jensen/three-bit assembly was still in progress at this checkpoint |
| Continuous threshold appendix | Exact scalar formula and derivative proof identified | Strict comparison, equality classification and continuous threshold semantics remain separate obligations |
| Full theorem | Exact independent proposition and completion challenge | Main completion requires a proof of the scalar prerequisite and a fresh successful full gate |

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

## 6. Concrete remaining frontier at this checkpoint

The main-theorem frontier is now the final scalar three-bit assembly. The
comparison function and all finite-law induction connections described in the
initial review have been completed and compiled. The comparison-map proof uses
the decreasing derivative ratio `ρ L(ρt)/L(t)`, where
`L(t)=log(1+t)−log(1−t)`. Its supporting-line proof covers the information
endpoints without differentiating an inverse at those endpoints.

After the scalar target is discharged, the exact main theorem should be built
and audited through the unchanged completion gate. Separate all-paper tasks
include the continuous threshold separation and equality classification,
explicit probability-space realization of comparison bits if required in the
paper's wording, and any intended extension from finite observations to the
paper's unrestricted observed random variables. The continuous maximization
conjecture must remain marked as a conjecture and excluded from proof claims.

This document contains a chronological review update: future success must be
supported by its own fresh result JSON and source hashes. It does not predict
or certify the result of a future gate run.
