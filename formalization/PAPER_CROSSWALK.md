# Manuscript obligations and checked correspondence

Source: `45ad4866a41e04722f2cfcef4129a1050e59d3ca`; latest manuscript change:
`0eb4756ce4ebd6daa803d77035cc6a60bfd70e5a` (November 20, 2026).

The exact finite-cube main theorem is proved by
`CourtadeKumar.latestPaper : CourtadeKumar.Spec.LatestPaperTarget`.
Its classical consequence is
`CourtadeKumar.classicalCourtadeKumar : CourtadeKumar.Spec.ClassicalTarget`.
The fresh complete build and transitive axiom audit passed with status
`LATEST_MAIN_THEOREM_KERNEL_CHECKED`; see `verification/main-theorem/`.
The final scalar theorem and both main declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. Staged wrappers below are distinguished
from declarations already included in that complete gate.

## Main theorem and actual probability model

| Paper obligation | Lean correspondence | Current scope |
|---|---|---|
| `thm:ck+`, both inequalities | `CourtadeKumar.latestPaper` in `CK/Latest.lean` | **Proved.** Exact independently specified target; every `n : ℕ`, every `Cube n → Bool`, and every real `p∈[0,1]`. No remaining mathematical hypotheses. |
| Classical Courtade–Kumar bound | `CourtadeKumar.classicalCourtadeKumar` | **Proved.** Exact `Spec.ClassicalTarget`, as a corollary of the stronger theorem. |
| `lem:ck+to_ck` and the second main inequality | `progressiveEntropy_le_noiseInformation`, `Spec.progressiveBound_le_capacity` | Proved for the actual cube mean and the full closed noise interval. |
| Entropy and channel definitions | `CK/Spec.lean`, `CK/Channel.lean` | Independently fixed finite sums with base-two entropy; channel normalization, posterior bounds, symmetry and mean preservation proved. |
| Literal finite probability model | `Spec.jointLaw`, `jointLaw_shannonInformation`, `jointLaw_progressiveGap` in `CK/CubeSplit.lean` | Joint mass is `channel p x y / 2^n`; its information and gap equal the separately defined specification quantities. |
| `lem:good-coordinate` | `Spec.good_coordinate`, `Spec.jointLaw_good_coordinate` | Proved on the actual uniform cube for `n≥2`; coordinate independence is proved by explicit flip bijections and transferred to the joint channel law. |
| `lem:conditioning-gain` | `FiniteLaw.conditioning_gain_joint` | Proved for an arbitrary finite joint law, unbiased `B` independent of finite `U`, and positive `T(C\mid U)`. Every quantity in its ratio is the actual finite-law quantity. |
| `lem:gap-first` | `FiniteLaw.gap_first_of_comparison` in `CK/GapBounds.lean` | Actual gap identity, Markov removal and conditioning gain are proved dependencies. Its matching/comparison prerequisites are supplied in the final induction step. |
| `lem:gap-second` | `FiniteLaw.gap_second_of_comparison_and_bias` | Actual Shannon chain rule and conditional entropy sandwich are proved dependencies. Its comparison and sharp bias prerequisites are supplied in the final induction step. |
| `eq:gap-combined` and multiplier estimates | `CK/GapAlgebra.lean` | Exact cancellation and coefficient algebra, instantiated with actual probability quantities in `CK/InductionStep.lean`. |
| `lem:ind-step`, implication needed for the main theorem | `FiniteLaw.induction_step_of_threeBit` | Finite-law theorem, including zero coordinate information, zero conditional variance and all noise endpoints. Its only analytic premise is supplied by the proved `Spec.threeBit`. |
| `lem:ind-step`, literal quantitative `∃λ≥0` statement | `FiniteLaw.quantitative_induction_step` in `CK/QuantitativeInduction.lean` | Proved with the actual finite-law gaps and `Δ/(1+λ)≤g`; no nonnegativity assumption on `Δ`. |
| Actual coordinate independence and Markov properties | `jointLaw_independentUnbiased_input`, `jointLaw_independentUnbiased_output`, `jointLaw_markov`, `jointLaw_conditionOn_markov`, `jointLaw_conditionOn_correlation` in `CK/CubeMarkov.lean` | Derived from the product density. Conditional coordinate correlation is exactly `1−2p` on every residual-input fibre. |
| Coordinate restriction and the induction hypothesis | `joinCoordinate`, `restrictCoordinate`, `jointLaw_conditionalProgressiveGap`, `jointLaw_split_conditionalGap_nonneg` | Any chosen coordinate is removed by an explicit equivalence; the conditional gap equals the average of the two literal lower-dimensional restriction gaps. |
| Base dimensions, constants and noise endpoints | `target_dimension_zero`, `target_dimension_one`, `target_constant`, `target_noise_endpoints` in `CK/ChannelEndpoints.lean` | Exact specification equalities. Noise complementation is also proved. |
| Final dimension induction | `Spec.cube_induction_step_of_threeBit`, `Spec.latest_of_threeBit` in `CK/CubeInduction.lean`; `latestPaper` | Induction on the actual Boolean-cube dimension. All probability/base hypotheses are discharged; the scalar premise is supplied in `CK/Latest.lean`. |

## Active probability and comparison lemmas

| Paper obligation | Lean correspondence | Current scope |
|---|---|---|
| `item:tsallis-bounds` | `quadraticInformation_eq_variance`, `conditionalQuadraticInformation_nonneg`, `conditionalQuadraticInformation_le_entropy`, `conditional_entropy_sandwich` | Proved for finite laws, including all actual conditional averages; wrappers are in `CK/TsallisProperties.lean`. |
| `item:tsallis-chain` | `conditionalQuadraticInformation_chain`, `quadraticInformation_data_processing` in `CK/TsallisProperties.lean` | Exact finite-law conditional chain and bit Markov data processing, from proved entropy towers and probability factorization. |
| `item:tsallis-shannon` | `conditionalQuadraticInformation_le_shannonInformation`, `conditionalShannonInformation_le_quadraticInformation_of_unbiased` in `CK/TsallisProperties.lean` | Both actual conditional averaged comparisons proved, with base-two normalization and conditional unbiasedness required for the reverse comparison. |
| `item:tsallis-bits` | `binary_quadratic_symmetry`, covariance/agreement identities in `CK/GoodCoordinate.lean`; correlation identities in `CK/BinaryProfileSemantics.lean` | Proved for two bits, including degenerate marginals and the squared agreement/correlation identity for an unbiased observed bit. |
| `item:tsallis-conditioning` | `FiniteLaw.quadratic_conditioning_joint` in `CK/TsallisProperties.lean` | Proved on the original finite joint law for a possibly biased bit independent of `U`; no unbiasedness assumption. |
| `item:tsallis-noise` | `noiseGap_bounds` | Proved for every `p∈[0,1]`. |
| Shannon chain and symmetry | `shannonInformation_chain`, `shannonInformation_symm`, `conditionalShannonInformation_symm` | Proved from probability masses and binary entropy's perspective identity. |
| Disintegration and null fibres | `conditionOn`, `mixture_conditionOn`, `conditionOn_mean_tower`, conditional entropy towers | The original law is reconstructed exactly. Null observations have a normalized fallback law and zero weight in every conditional average. |
| Finite pushforward semantics | `CK/MapLaws.lean` | Expectation, masses, moments, conditional entropy and information commute with the actual pushforward law. |
| `lem:biased-comparison`, both conclusions | `FiniteLaw.shannonInformation_le_biasCoefficient` in `CK/BiasDivergence.lean`, `quadratic_mul_biasCoefficient` in `CK/BiasCoefficient.lean` | Proved for every nonconstant bit and finite observation, using the paper's actual piecewise coefficient. |
| `lem:binary-divergence-comparison` | `binaryDivergenceNats_eq_kl`, `binaryDivergenceBits_bounds` in `CK/BinaryDivergenceBounds.lean` | Conventional KL identification and both exact bit-normalized bounds proved, including the endpoint values of the first probability and complementary reference means. |
| `lem:comparison-calculus`, pointwise estimates | `Spec.pointwiseComparison` in `CK/ProfileSeries.lean`; closed-domain results in `CK/ComparisonAveraging.lean` | Matching, domination and lower-profile bound proved from the actual divergence series, with deterministic conditional fibres handled by the closed-domain wrappers. |
| Comparison-map concavity and monotonicity | `comparisonMap_concave`, `comparisonMap_monotone`, `comparisonMap_divergence` | Proved for the actual map on `[0,1]`, including endpoints. |
| Actual conditional information/profile identities | `shannonInformation_eq_binaryProfile`, `shannonInformation_markov_profile`, `conditionalShannonInformation_eq_binaryProfile` | Exact finite-law statements from Bayes' rule and binary Markov probability factorization. |
| `lem:comparison`, normalized matching and domination | `FiniteLaw.conditional_comparison` | Proved for the actual conditional information quantities. Produces `τ∈[0,1]` with exact matching and domination; literal randomized-bit realization on an extended probability space is being added separately. |
| `lem:comparison-correlation` | Final conjunct of `FiniteLaw.conditional_comparison` | Conditional averaging proves `T(C;B)/T(C\mid U)^2≤τ²`; the actual randomized comparison-bit realization is tracked with the preceding row. |

## Scalar proof and separate appendix obligations

| Paper obligation | Lean correspondence | Current scope |
|---|---|---|
| `lem:three-bit`, strict scalar target | `Spec.threeBit : Spec.ThreeBitTarget` in `CK/ScalarThreeBit.lean` | **Proved.** Exact independently stated strict inequality for `0<ρ<1`, `0<σ≤1`, including `σ=1`. |
| Scalar weighted means and exponent | `CK/ScalarMeans.lean`, `CK/ScalarParameters.lean` | Both mean comparisons, summability, positivity and correspondence with the actual `α_p` are proved. |
| `eq:scalar-rescaled-order` | `Scalar.tail_rescaling` in `CK/ScalarRescaling.lean` | Proved for the actual infinite tail series, every positive tail index and `0<σ≤1`. |
| First Jensen reduction | `Scalar.first_gap_jensen` | Countable Jensen and the integrated exponential derivative series; sum/integral exchanges justified. |
| Second Jensen reduction | `Scalar.second_gap_jensen` | Actual tail rescaling and weighted exponential Jensen, with summability established. |
| Rational/log certificates | `CK/ScalarCertificates.lean` | Exact small-index rational margins, logarithm interval and polynomial tangent barrier. |
| Tail integrals and all-index coefficient bound | `CK/ScalarTails.lean`, `CK/ScalarIntegral.lean` | Integral representations, positivity and convolution comparison for every index. |
| Infinite-series barrier and final assembly | `tail_series_barrier`, `scalar_barrier_assembly`, `three_bit_nats`, `Spec.threeBit` | Both Jensen bounds evaluated at one proved exponent, followed by explicit conversion from natural-log divergence to bits. |
| `eq:binary-divergence-series` | `Scalar.hasSum_divergenceNats_closed`, `Spec.hasSum_divergence_closed` | Actual convergent series on the full closed interval `[-1,1]`. |
| `lem:ck+vscontinuous` | `Threshold.progressiveEntropy_le_kernelInformation`, `_lt_kernelInformation`, `_eq_kernelInformation_iff`, `_eq_kernelInformation_endpoints` in `CK/ThresholdModel.lean` | Proved for the actual uniform-input measurable resampling Markov kernel. Threshold posterior mean and entropy are evaluated by Lebesgue integrals. Strictness and the complete equality classification are inherited from `CK/ThresholdSeparation.lean`. |
| Independent extra continuous input coordinates | `Threshold.observedResamplingKernel`, `kernelInformationWithObservation_eq` | Any additional independent observed coordinates, with an arbitrary probability law, leave the selected threshold information unchanged. This includes the remaining coordinates of the continuous product-cube setup. |
| `conj:continuous` | Conjecture | Explicitly excluded from proved theorem claims. |

## Scope and interpretation

The main theorem has exactly the manuscript's Boolean-cube scope. Its auxiliary
probability library uses arbitrary normalized probability weights on a **finite
sample space** and **finite observation alphabets**. This covers every variable
used in the finite-cube proof. It is not a claim that the preliminary statements
have been extended to arbitrary measurable observations on general probability
spaces.

Independence and Markov assumptions are expressed by actual probability
factorization. The cube proof derives them from the product channel. The
zero-probability fallback in `conditionOn` changes no weighted quantity.

The older quadratic exposition inside `\iffalse` in `information.tex` is inactive
source material, and is not counted as an active lemma. A conditional reduction
is distinguished from the theorem supplying its premises. Declaration counts
measure code, not a percentage of the paper.
