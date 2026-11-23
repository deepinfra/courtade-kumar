# Manuscript obligations and checked correspondence

Source: `45ad4866a41e04722f2cfcef4129a1050e59d3ca`.
This ledger separates proved Lean statements from remaining mathematical and
semantic connections. Declaration counts measure code, not a percentage of the
paper proved. A conditional assembly lemma does not discharge its hypotheses.

| Paper obligation | Lean correspondence | Current scope |
|---|---|---|
| `thm:ck+`, first inequality | `Spec.LatestPaperTarget` | **Open.** No `latestPaper` theorem is present. |
| `thm:ck+`, second inequality; `lem:ck+to_ck` | `progressiveEntropy_le_noiseInformation`, `Spec.progressiveBound_le_capacity` | Proved, full `p∈[0,1]`, with actual cube mean. |
| Entropy and channel definitions | `CK/Spec.lean`, `CK/Channel.lean` | Exact finite definitions; channel sums, posterior bounds and mean proved. |
| `item:tsallis-bounds` | `CK/FiniteProbability.lean`, `CK/Shannon.lean` | Finite laws; nonnegativity, variance and conditional entropy sandwich proved. |
| `item:tsallis-chain` | `CK/EntropyChain.lean`, `CK/Markov.lean` | Finite Shannon/quadratic chain rules and entropy invariance under explicit Markov factorization proved; final data-processing wrapper tracked separately. |
| `item:tsallis-shannon` | `quadratic_gap_le_shannonGap`, `quadraticInformation_le_shannonInformation`, `shannonInformation_le_quadraticInformation_of_unbiased` | Proved for actual finite laws, with base-two normalization. |
| `item:tsallis-bits` | `binary_quadratic_symmetry` and agreement/covariance identities in `CK/GoodCoordinate.lean` | Proved, including degenerate bits. |
| `item:tsallis-conditioning` | `FiniteLaw.quadratic_conditioning` | Proved for finite mixtures with the independence hypothesis explicit. |
| `item:tsallis-noise` | `noiseGap_bounds` | Proved for every `p∈[0,1]`. |
| `lem:biased-comparison`, coefficient bound | `quadratic_mul_biasCoefficient` | Proved for the actual piecewise coefficient. |
| `lem:biased-comparison`, information bound | full biased divergence/information inequality | **Open.** Coefficient positivity alone does not prove it. |
| `lem:good-coordinate` | `Spec.good_coordinate` | Proved on the actual uniform Boolean cube for `n≥2`; coordinate independence discharged. |
| `lem:conditioning-gain` | `FiniteLaw.conditioning_gain`, `FiniteLaw.conditioning_gain_joint` | Proved for actual finite joint laws; posterior reconstruction and all entropy gains established. |
| `lem:comparison-calculus`, pointwise estimates | `Spec.pointwiseComparison : Spec.PointwiseComparisonTarget` in `CK/ProfileSeries.lean` | Complete pointwise matching, domination, and lower profile bound proved, including boundary cases. |
| `lem:comparison-calculus`, comparison-map concavity | `comparisonMap_concave`, `comparisonMap_monotone`, `comparisonMap_divergence` | Proved for the actual map on `[0,1]`, including noise and input endpoints. |
| `lem:comparison` | conditional comparison/Jensen assembly | **Open.** Pointwise comparison and concavity are proved; finite conditional assembly is being connected. |
| `lem:comparison-correlation` | `Spec.matched_correlation_bound` | Scalar monotonicity implication proved; actual conditional lower-profile averaging remains to be connected. |
| `lem:gap-first` | probabilistic gap assembly | **Open.** Requires actual entropy identities and comparison results. |
| `lem:gap-second` | probabilistic gap assembly | **Open.** Requires comparison and the biased information bound. |
| `eq:gap-combined` and multiplier estimates | `CK/GapAlgebra.lean` | Cancellation and coefficient algebra proved; both gap inequalities remain explicit hypotheses. |
| `lem:three-bit`, scalar target | `Spec.ThreeBitTarget` | **Open.** Strict target is fixed independently. |
| Scalar rational/log bounds | `CK/ScalarCertificates.lean` | Exact finite margins and final polynomial barrier proved. |
| Scalar tail integral and all-index coefficient inequality | `CK/ScalarTails.lean` | Integral representation, positivity, and convolution inequality for every index proved. |
| Actual scalar tails and final tail barrier | `CK/ScalarSeries.lean` | Summability and strict barrier proved for the infinite series. |
| Scalar mean ordering and normalization | `CK/ScalarMeans.lean` | Both mean comparisons, summability, and alpha/divergence correspondence proved. |
| `eq:scalar-rescaled-order` | rescaled-tail analysis | **Open.** This is a substantive remaining analytic step. |
| Three-bit Jensen reductions | scalar assembly | **Open.** Actual means alone do not complete this reduction. |
| `lem:ind-step` | `induction_gap_nondegenerate` | Algebraic reduction proved conditionally; full probability theorem open. |
| Final dimension induction | coordinate splitting and semantic bridge | **Open.** Must reduce the actual product-channel function to `n−1` dimensions. |
| `lem:binary-divergence-comparison` | binary divergence analytic development | Lower estimates and unbiased upper estimates proved; full biased sharp bound open. |
| `eq:binary-divergence-series` | `Scalar.hasSum_divergenceNats_closed`, `Spec.hasSum_divergence_closed` | Actual convergent power series proved on the entire closed interval `[-1,1]`. |
| `lem:ck+vscontinuous` | continuous threshold separation | **Open.** Distinct from the finite-cube main theorem. |
| `conj:continuous` | optional proposition encoding | Conjecture, explicitly excluded from claimed theorems. |

The earlier quadratic exposition inside `\iffalse` in `information.tex` is
inactive source material; it is not silently counted as an active manuscript
lemma. Manuscript labels and mathematical expressions, rather than old file
names or old branch claims, determine the current obligations.
