# Independent review of the latest-paper formalization

## Conclusion and scope

The independently stated main target agrees with the stronger theorem in the
November 20 manuscript. The current checked library establishes substantial
parts of its proof, including the entire right-hand inequality
`Q(C) ≤ 1 − h(p)`. It does **not yet establish** the left-hand inequality
`I(C;X) ≤ Q(C)`, the main target, or every result in the paper. A successful
partial build must therefore remain a partial verification result.

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
and its negation. Randomized comparison bits are separate constructions in
the argument; their existence and information identities still require proof.

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
| Product binary symmetric channel | Row and column sums, symmetry, nonnegative masses, posterior range, uniform-law preservation | These finite semantics are correct; the induction still needs its conditional-channel decomposition |
| `Q(C) ≤ Ip` | `progressiveBound_le_capacity`, with all probability/noise hypotheses discharged | This is the right-hand half of the main theorem |
| Good-coordinate lemma | `Spec.good_coordinate`, including explicit cube-coordinate independence and agreement with `Spec.average` | The lemma itself is established on the actual Boolean cube |
| Quadratic information | Finite laws, null-fibre handling, total expectation, variance formula, nonnegativity, covariance identities | General arbitrary-random-variable formulations in the paper are not supplied by a finite-law library alone |
| Quadratic conditioning | `FiniteLaw.quadratic_conditioning` under explicit finite-mixture independence | Correct finite form; the full Shannon conditioning-gain argument still needs chain-rule/semantic assembly |
| Shannon–quadratic comparisons | Strong concavity, Jensen comparisons, Pinsker normalization and unbiased reverse comparison | This does not yet prove the separate bias-sensitive upper comparison |
| Bias coefficient | Positivity and `T(C)c(μ)≤1` | `I(C;U)≤c(μ)T(C;U)/ln 2` is a separate analytic obligation |
| Induction cancellation | `induction_gap_nondegenerate` verifies the coefficient algebra | First and second information-gap bounds and the three-bit inequality are explicit premises, not discharged conclusions |
| Scalar coefficient estimate | All-index convolution bound and strictness for indices at least two | These are genuine quantified results, not just numerical samples |
| Final scalar barrier | Strict bound for the actual convergent tail series | Tail rescaling, mean/Jensen reductions, and the link to the three-bit target remain separate obligations |
| Comparison construction | Bounds on the explicit profile and a series single-crossing principle; additional matching work is in progress | The weighted-profile domination, comparison-map concavity, and conditional randomized-bit construction must be assembled |
| Full theorem | Exact independent proposition and completion challenge | No proof of `LatestPaperTarget` was present at the reviewed checkpoint |

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

These are provenance and fail-closed-verification concerns, not evidence that
any currently checked mathematical theorem is false. Final verification
should pin the audit, recursively account for source files, mark a run as
unverified before starting, recheck the source snapshot at the end, and include
the mathematical TeX inputs. The final gate and manifest revisions must be
consulted to determine which listed corrections have been incorporated.

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

## 6. Concrete next frontier

The next major comparison obligation is a concave map `Fρ` on `[0,1]` with
`Fρ(f(t))=f(ρt)`, followed by the weighted Jensen construction and its zero-mass
cases. A promising derivative proof avoids termwise differentiation of an
infinite double series: with `L(t)=log(1+t)−log(1−t)`, the derivative ratio is
`ρ L(ρt)/L(t)`. Its monotonicity follows from the fact that
`(1−t²)L(t)/t` decreases on `(0,1)`, using `L(t)≥2t`. Supporting-line
inequalities can then prove concavity without demanding inverse-function
calculus at the endpoints.

In parallel, finish the tail-rescaling inequality and the Jensen/mean bridge
for the actual scalar series. Then discharge the bias-sensitive information
upper bound, the Shannon gap identities, and the finite conditional-channel
induction. These connections, rather than more isolated numerical checks,
are what turn the checked components into a proof of the latest target.
