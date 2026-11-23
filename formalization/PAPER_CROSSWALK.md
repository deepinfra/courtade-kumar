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
`Classical.choice`, and `Quot.sound`. The expanded paper gate also passed with
`ALL_ACTIVE_PAPER_RESULTS_KERNEL_CHECKED`; see `verification/final-paper/`.
Both completion flags are true. The frozen ledger covers all 15 active primary
theorem/lemma labels and 54 audited proof roots.

## Main theorem and actual probability model

| Paper obligation | Lean correspondence | Current scope |
|---|---|---|
| `thm:ck+`, both inequalities | `CourtadeKumar.latestPaper` in `CK/Latest.lean` | **Proved.** Exact independently specified target; every `n : ℕ`, every `Cube n → Bool`, and every real `p∈[0,1]`. No remaining mathematical hypotheses. |
| Classical Courtade–Kumar bound | `CourtadeKumar.classicalCourtadeKumar` | **Proved.** Exact `Spec.ClassicalTarget`, as a corollary of the stronger theorem. |
| `lem:ck+to_ck` and the second main inequality | `progressiveEntropy_le_noiseInformation`, `Spec.progressiveBound_le_capacity` | Proved for the actual cube mean and the full closed noise interval. |
| Entropy and channel definitions | `CK/Spec.lean`, `CK/Channel.lean` | Independently fixed finite sums with base-two entropy; channel normalization, posterior bounds, symmetry and mean preservation proved. |
| Literal finite probability model | `Spec.jointLaw`, `jointLaw_shannonInformation`, `jointLaw_progressiveGap` in `CK/CubeSplit.lean` | Joint mass is `channel p x y / 2^n`; its information and gap equal the separately defined specification quantities. |
| `lem:good-coordinate` | `Spec.good_coordinate`, `Spec.jointLaw_good_coordinate` | Proved on the actual uniform cube for `n≥2`; coordinate independence is proved by explicit flip bijections and transferred to the joint channel law. |
| `lem:conditioning-gain` | `FiniteLaw.conditioning_gain_joint`; `KernelInformation.conditioning_gain_of_independent` in `CK/ObservationConditioning.lean` | Proved for arbitrary underlying probability spaces and measurable observations. The wrapper uses genuine independence of `B` and `U`, the context's unbiasedness, positive actual posterior Tsallis entropy, and the actual conditional-law Shannon average. |
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
| `item:tsallis-bounds` | Finite wrappers in `CK/TsallisProperties.lean`; `Posterior.informationGiven_bounds`, `quadraticInformationGiven_le_entropy`, `conditional_entropy_sandwich` | Proved for arbitrary probability spaces and arbitrary observation sigma algebras. Conditional posteriors are actual conditional expectations; integrability, interval bounds, and entropy nonnegativity are proved. |
| `item:tsallis-chain` | `Posterior.conditional_quadratic_chain`; `Posterior.information_data_processing`, `binary_information_data_processing` in `CK/PosteriorMarkov.lean` | Conditional chain and data processing hold for arbitrary observation sigma algebras. Data processing is derived from genuine event-factorization Markov independence. The separate adapter accepting mathlib `CondIndepFun` carries mathlib's standard-Borel hypothesis on the original space; the underlying event-factorization theorem has no such restriction. |
| `item:tsallis-shannon` | `Posterior.informationGiven_bounds`, `Posterior.informationGiven_unbiased` in `CK/PosteriorChain.lean` | Both comparisons proved for arbitrary observation sigma algebras with base-two normalization. The reverse comparison uses an unbiased conditional posterior; genuine independence supplies that posterior through `conditionalKernel_expect_of_independent` / conditional-expectation independence. |
| `item:tsallis-bits` | `binary_quadratic_symmetry`, covariance/agreement identities in `CK/GoodCoordinate.lean`; correlation identities in `CK/BinaryProfileSemantics.lean` | Proved for two bits, including degenerate marginals and the squared agreement/correlation identity for an unbiased observed bit. |
| `item:tsallis-conditioning` | `FiniteKernel.quadratic_conditioning`; `KernelInformation.quadratic_conditioning_of_independent` in `CK/ObservationConditioning.lean` | Proved for actual random bits on arbitrary probability spaces with arbitrary observations; the bit may be biased. The wrapper derives constant conditional mean from genuine `IndepFun`, reconstructs the original finite joint law, and uses actual conditional-expectation entropy. |
| `item:tsallis-noise` | `noiseGap_bounds` | Proved for every `p∈[0,1]`. |
| Shannon chain and symmetry | `shannonInformation_chain`, `shannonInformation_symm`, `conditionalShannonInformation_symm` | Proved from probability masses and binary entropy's perspective identity. |
| Disintegration and null fibres | Finite `conditionOn` / `mixture_conditionOn`; `conditionalKernel`, `conditionalKernel_expect_ae`, `conditionalKernel_mixture_expect` in `CK/ConditionalKernel.lean` | For arbitrary observations, the kernel is constructed from mathlib's actual regular conditional distribution of the finite joint output. Its moments equal genuine conditional expectations and its mixture recovers the original joint law. Null fibres change no integrated quantity. |
| Finite pushforward semantics | `CK/MapLaws.lean` | Expectation, masses, moments, conditional entropy and information commute with the actual pushforward law. |
| `lem:biased-comparison`, both conclusions | `Posterior.conditional_information_bias_bound` in `CK/PosteriorMeasure.lean`; `quadratic_mul_biasCoefficient` in `CK/BiasCoefficient.lean` | Proved for every nonconstant bit and every measurable observation on an arbitrary probability space, using the paper's actual piecewise coefficient. The information bound follows by integrating the proved pointwise divergence bound; no information comparison is assumed. |
| `lem:binary-divergence-comparison` | `binaryDivergenceNats_eq_kl`, `binaryDivergenceBits_bounds` in `CK/BinaryDivergenceBounds.lean` | Conventional KL identification and both exact bit-normalized bounds proved, including the endpoint values of the first probability and complementary reference means. |
| `lem:comparison-calculus`, pointwise estimates | `Spec.pointwiseComparison` in `CK/ProfileSeries.lean`; closed-domain results in `CK/ComparisonAveraging.lean` | Matching, domination and lower-profile bound proved from the actual divergence series, with deterministic conditional fibres handled by the closed-domain wrappers. |
| Comparison-map concavity and monotonicity | `comparisonMap_concave`, `comparisonMap_monotone`, `comparisonMap_divergence` | Proved for the actual map on `[0,1]`, including endpoints. |
| Actual conditional information/profile identities | `shannonInformation_eq_binaryProfile`, `shannonInformation_markov_profile`; `FiniteKernel.conditional_comparison` | Exact identities from Bayes' rule and probability factorization, applied almost everywhere to genuine conditional finite joint laws. All resulting conditional quantities are integrated over the arbitrary observation law. |
| `lem:comparison`, existence and universal domination | `FiniteKernel.conditional_comparison_realized` in `CK/KernelComparison.lean`; `FiniteKernel.every_matching_comparator` in `CK/KernelMatchingComparator.lean`; `observation_comparison_realized` in `CK/ObservationComparison.lean` | Arbitrary measurable observation. The witness adjoins the same independent private BSC bit in every fibre, preserves all original conditional laws and their marginal, and realizes the exact Shannon match. The universal theorem applies to every unbiased matching comparator with the same original channel, even on a different finite joint output alphabet. |
| `lem:comparison-correlation` | Final conjuncts of `FiniteKernel.conditional_comparison_realized` and `FiniteKernel.every_matching_comparator` | Proved for arbitrary observations and actual comparator information: `T(C;B)/T(C\mid U)^2≤T(C′;B)`. Strict monotonicity of divergence identifies the absolute correlation of every matching comparator. |

## Scalar proof and separate appendix obligations

| Paper obligation | Lean correspondence | Current scope |
|---|---|---|
| `lem:three-bit`, scalar and actual-bit statements | `Spec.threeBit : Spec.ThreeBitTarget`; `FiniteLaw.three_bit_information` in `CK/ThreeBitSemantics.lean`; `three_bit_information_restated` in `CK/ThreeBitRestatement.lean` | **Proved.** The strict scalar result covers `0<ρ<1`, `0<σ≤1`, including `σ=1`. The actual-bit theorem derives every scalar parameter and information identity from an unbiased Markov joint law; it proves a strict form of the paper's non-strict conclusion. |
| Scalar weighted means and exponent | `CK/ScalarMeans.lean`, `CK/ScalarParameters.lean` | Both mean comparisons, summability, positivity and correspondence with the actual `α_p` are proved. |
| `eq:scalar-rescaled-order` | `Scalar.tail_rescaling` in `CK/ScalarRescaling.lean` | Proved for the actual infinite tail series, every positive tail index and `0<σ≤1`. |
| First Jensen reduction | `Scalar.first_gap_jensen` | Countable Jensen and the integrated exponential derivative series; sum/integral exchanges justified. |
| Second Jensen reduction | `Scalar.second_gap_jensen` | Actual tail rescaling and weighted exponential Jensen, with summability established. |
| Rational/log certificates | `CK/ScalarCertificates.lean` | Exact small-index rational margins, logarithm interval and polynomial tangent barrier. |
| Tail integrals and all-index coefficient bound | `CK/ScalarTails.lean`, `CK/ScalarIntegral.lean` | Integral representations, positivity and convolution comparison for every index. |
| Infinite-series barrier and final assembly | `tail_series_barrier`, `scalar_barrier_assembly`, `three_bit_nats`, `Spec.threeBit` | Both Jensen bounds evaluated at one proved exponent, followed by explicit conversion from natural-log divergence to bits. |
| `eq:binary-divergence-series` and entropy equality cases | `Scalar.hasSum_divergenceNats_closed`, `Spec.hasSum_divergence_closed`; `Spec.divergence_eq_square_iff`, `quadraticEntropy_eq_entropyBits_iff` in `CK/EntropyEquality.lean` | Actual convergent series on the full closed interval `[-1,1]`; equality `f(t)=t²` exactly at `t∈{−1,0,1}`, equivalently `T(μ)=H(μ)` exactly at `μ∈{0,1/2,1}`. |
| `lem:ck+vscontinuous` | `Threshold.progressiveEntropy_le_kernelInformation`, `_lt_kernelInformation`, `_eq_kernelInformation_iff`, `_eq_kernelInformation_endpoints` in `CK/ThresholdModel.lean` | Proved for the actual uniform-input measurable resampling Markov kernel. Threshold posterior mean and entropy are evaluated by Lebesgue integrals. Strictness and the complete equality classification are inherited from `CK/ThresholdSeparation.lean`. |
| Independent extra continuous input coordinates | `Threshold.observedResamplingKernel`, `kernelInformationWithObservation_eq` | Any additional independent observed coordinates, with an arbitrary probability law, leave the selected threshold information unchanged. This includes the remaining coordinates of the continuous product-cube setup. |
| `conj:continuous` | Conjecture | Explicitly excluded from proved theorem claims. |

## General-observation completion roots

| Required scope | Checked declaration or module | Semantic basis |
|---|---|---|
| Arbitrary observation posterior entropy and information | `CK/PosteriorMeasure.lean` | Actual conditional expectations; posterior range, mean preservation, integrability, entropy sandwich, Pinsker, and sharp bias comparison are proved. |
| Conditional chain, bounds and reverse unbiased comparison | `CK/PosteriorChain.lean` | Nested observation sigma algebras, actual conditional Jensen, and conditional expectation tower. |
| General Markov data processing | `Posterior.information_data_processing` | Event/moment probability factorization implies posterior sufficiency, which implies both Shannon and quadratic data processing. |
| Genuine conditional finite laws | `KernelInformation.conditionalKernel`, `conditionalKernel_expect_ae`, `conditionalKernel_mixture` | Mathlib regular conditional distribution; original finite-output moments and marginal law recovered. |
| Arbitrary-observation comparison existence | `KernelInformation.observation_comparison_realized` | Genuine joint `IndepFun` of `(A,B)` and `U`; genuine conditional probability factorization; explicit common private BSC extension. |
| Every matching comparison bit | `FiniteKernel.every_matching_comparator` | Arbitrary matching comparator and exact signed original channel; both information inequalities follow from strict divergence monotonicity. |
| Arbitrary-observation Tsallis conditioning | `KernelInformation.quadratic_conditioning_of_independent` | Genuine independence; integral Cauchy–Schwarz applied to actual conditional covariances. |
| Arbitrary-observation Shannon conditioning gain | `KernelInformation.conditioning_gain_of_independent` | Actual conditional-law entropy and information, the proved integral Tsallis conditioning bound, and the proved conditional Pinsker comparison. |

## General-observation semantic audit

The finite alphabet in `FiniteKernel U Γ` is the **joint output alphabet of the
bits**, not the observation alphabet. For three bits one may take `Γ=Bool³`;
every original probability space maps measurably to this finite alphabet.
The observation space `U` has an arbitrary measurable structure and its law is
an arbitrary probability measure. No countability, discreteness, finite support,
or standard-Borel hypothesis is imposed on `U`. The standard-Borel hypothesis
needed to construct `conditionalKernel` is on the finite output `Γ`.

`CK/ConditionalKernel.lean` constructs these kernels from the actual regular
conditional distribution. `conditionalKernel_expect_ae` identifies their moments
with genuine conditional expectations, and `conditionalKernel_mixture_expect`
recovers every original finite observable's integral. In
`CK/ObservationComparison.lean`, actual joint independence of `(A,B)` and `U`
yields both unbiased conditional bits and the **signed** fixed channel.
The private-randomness premise is conditional probability factorization of the
four joint bit cells, stated with actual conditional expectations.
`conditionalKernel_markov_ae` proves the corresponding conditional-law Markov
property. It is not an assumed information inequality or scalar comparison.

The paper explicitly defines conditional entropy and information as averages
under conditional laws. The comparison and conditioning kernels implement that
definition literally. The separate `Posterior` modules also formalize arbitrary
observation sigma algebras using conditional expectations, proving chain rules,
conditional Pinsker, variance identities, and sharp bias bounds in that model.
No equality between the integrated finite-kernel Shannon information and the
separate `Posterior.shannonInformationGiven` representation is claimed unless
an explicit bridge theorem establishes it. That API identification is not needed
for the paper's conditional-law definition or the finite-cube main theorem.

The main theorem retains exactly the independently specified Boolean-cube scope,
including dimension zero and all channel endpoints. Its proof derives all
coordinate independence and Markov properties from the explicit product law.
Auxiliary gap bounds may take named comparison conclusions as premises; the
final induction theorem supplies those premises from the proved comparison,
bias, and scalar theorems. They are not residual axioms of the main result.

The older quadratic exposition inside `\iffalse` in `information.tex` is inactive
source material, and is not counted as an active lemma. The continuous-cube
conjecture is likewise excluded from proved-theorem claims. Declaration counts
measure code, not a percentage of the paper.
