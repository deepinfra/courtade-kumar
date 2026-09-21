# Explaining the argument without the transcript

These are preparation notes, not a script that establishes personal mastery or a substitute for checking the proof. The references are stable source labels; use the manuscript or equation crosswalk for printed locations. Explain the steps in your own words and work the examples without relying on the conversation.

## Begin with a precise claim

The input is an arbitrary finite number of **independent fair bits**. A deterministic Boolean rule chooses one output bit before independent symmetric noise is added. A coordinate keeps ln2 - h(p) nats of information about the entire noisy vector. The paper's main claim is that no Boolean rule keeps more. It is about the entire vector, not the sum of information about the individual noisy coordinates.

The proposed stability estimate says more: at a fixed nontrivial noise level, a rule with almost the same information must agree with a coordinate, possibly complemented, on almost every input. Its coefficient is independent of dimension, but not sharp and not uniform away from zero at the noise endpoints.

## Low-noise questions

### Why not induct only over balanced functions?

Restriction does not preserve balance. Work the AND example: one child has mean zero, the other mean 1/2, and the parent mean is 1/4. The quantity V(mu)=4mu(1-mu) gives average child factor 1/2 and parent factor 3/4. The missing 1/4 is the square of the section-mean gap. The variance identity is elementary; the entropy estimate recovering that loss is not.

### Why may the proof require d <= 1/2?

The proof selects its splitting coordinate. If b_i=E(F X_i), then any two absolute coefficients sum to at most E|sigma_i X_i+sigma_j X_j|=1. They cannot both exceed 1/2. For n>=2 a suitable coordinate therefore exists. Constants and all one-bit functions are base cases, not applications of the selection statement.

### What is random, and what is fixed?

The section means and their gap d are fixed by f and the coordinate. A(W), B(W) are posterior probabilities after observing the **same** remaining noisy coordinates. They are not independent. Their observed separation can vary while d stays fixed. Bayes supplies the two p-mixtures, and the tower property supplies E|A-B|>=d. Two-bit parity is the test: d=0, but the posterior separation is rho.

### Where does the actual induction close?

Under a scalar estimate with coefficient c, the children give c(V-d^2), mixing contributes at least 2cd^2 to the right side, and the factor 1+d^2 remains on the left. The parent conclusion follows because c(V+d^2) >= c(1+d^2)V. The difference is cd^2(1-V), not an unspecified positive error. Explain why c>=0 and V<=1 are used, and why c<=h(p) is needed for the one-bit base case.

### Why center KM rather than M?

The scalar gap is K+Md^2-2 ell d. Completing the square leaves (KM-ell^2)/M. Post-mixing entropy M actually decreases as the pair moves away from symmetry, so pretending it is minimized at the center is wrong. The increase of K compensates in the product KM. A nonnegative product margin controls all real d; the endpoint region instead uses the restricted d interval and a separate gain-dominance condition.

### Where is the difficult analysis?

It lies in the entropy-curvature comparison and in the full-domain centered estimates, including endpoints. The change v=1/(1-u^2) is chosen because this is minus the second derivative of eta. The resulting g is convex and satisfies g+vg'>=0. The curvature difference becomes an integral of nonnegative terms; it then controls the midpoint derivative of KM. It is necessary to reconstruct that chain, not merely repeat that “symmetry should help.”

## Complementary-noise questions

### Why split by output bias and a coordinate coefficient?

Large output bias already limits available output entropy; contraction finishes. A large coordinate coefficient permits a direct conditional comparison with that coordinate. Only the remainder class needs a bound on constant-plus-linear Fourier mass. The three classes cover every function, with harmless boundary overlap. At 13/20, the enlarged direct-coordinate class still satisfies its scalar endpoint comparison.

### What is the purpose of the balancing lift?

F-sharp(x,z)=zF(zx) is balanced. Its first-level coefficients consist of the original b_i and the additional coefficient m. Thus a balanced first-level bound controls m^2+W1(F). The lift is not claimed to preserve mutual information; it is used only for this geometric estimate.

### Why does the energy proof subtract rho^2 E(FG)?

On Fourier degree k the resulting coefficient is rho^(2k)-rho^(k+2). It is zero at k=2 and nonpositive for k>=3. This removes a hard uncontrolled-tail problem with the right sign. FG must use the same uniform argument. Using F(X)G(Y) at the channel endpoints produces a different spectral expression.

### Why is the strict anchor needed?

The target changes with noise. Merely contracting I<=kappa(rho0) gives (rho/rho0)^2 kappa(rho0), which exceeds kappa(rho) for 0<rho<rho0. The anchor is therefore proved below rho0^2/2. After contraction it remains below rho^2/2<=kappa(rho). This is a logical requirement, not a decorative numerical tightening.

## Quantitative and reuse questions

### Why does the second induction avoid dimension loss?

Track only the degree-two mass T_i involving the selected coordinate. The average child high-degree mass is E(F)-T_i. The squared posterior difference contains d^2+rho^2 T_i. In the induction those T_i terms cancel exactly. A lower bound using the smallest eigenvalue of the entire noise operator would lose rho^(2(n-1)); the targeted bookkeeping does not.

### What should another researcher be able to take away?

A free-coefficient restriction--mixing criterion; product centering over the full open noise interval; a Fourier-cap/entropy-envelope certificate with separate balanced and bias conditions; and a quantified recovery statement. For p=1/4, an information gap <=10^-6 nats gives distance <=1/125 using the stronger piecewise coefficient. The upper continuity bound D<=h(delta) gives the converse direction qualitatively. None is an efficient learning theorem or an extension to biased inputs/asymmetric noise.

### What would falsify the claimed proof, and what would not?

A wrong sign, an uncovered parameter value, or a scalar assertion false within its stated domain would affect the relevant proof branch. A failure of a stronger inequality outside its domain is not such a defect. A polynomial verifier timing out is not a mathematical counterexample. A successful sample check is not an all-domain proof. Finding the standard antipodal inequality in earlier literature does not refute the theorem, but failing to credit that fact would be an attribution problem.

## Stop points for an honest discussion

Do not substitute a report's verdict for a derivation. It is acceptable to say “I can explain the reduction; I still need to reconstruct this analytic estimate.” Record the exact proposition and pending question. The ambition is an explanation that survives questions, not fluency that conceals what has not yet been understood.
