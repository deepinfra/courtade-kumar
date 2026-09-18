# TASK: CK/Comparison.lean — the entropy comparison on the correlation interval (manuscript eq:comparison, Lemma lem:comparison, app:comparisons)

Imports: `import CK.GainBounds`, `import CK.Constants`.
Definitions (CK/AnalyticTargets.lean): `psi rho t := (1 - t) * (1 + t - rho ^ 2)`, `lambdaDenom rho := 1 + rho - (31 / 40) * rho ^ 2`,
`EntropyComparisonGoal : Prop := ∀ rho t : ℝ, 3 / 5 ≤ rho → rho ≤ 9 / 10 → 0 ≤ t → t ≤ 1 → eta rho / ((1 - rho) * lambdaDenom rho) * psi rho t ≤ eta t`.

## TARGET (exact statement)
```lean
theorem entropy_comparison : EntropyComparisonGoal
```
Recommended intermediate lemmas (names are yours to choose; statements must be at least this strong):
```lean
/-- eq:lambdacriterion ⇒ envelope: if 5/32 < λ and log(4λ − 5/8) + 2 − 2λ(2 − ρ²) ≥ 0 then λ·psi ρ t ≤ eta t on [0,1]. -/
theorem envelope_of_criterion {ρ lam : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hlam : 5 / 32 < lam)
    (hcrit : 0 ≤ Real.log (4 * lam - 5 / 8) + 2 - 2 * lam * (2 - ρ ^ 2)) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → lam * psi ρ t ≤ eta t
/-- eq:lambdabar: the required coefficient is at most λ̄(ρ) = (log(2/(1−ρ)) + 3/4 + ρ/4)/(2Λ_ρ). -/
theorem lambdaReq_le_lambdaBar {ρ : ℝ} (h0 : 3 / 5 ≤ ρ) (h1 : ρ ≤ 9 / 10) :
    eta ρ / ((1 - ρ) * lambdaDenom ρ) ≤ (Real.log (2 / (1 - ρ)) + 3 / 4 + ρ / 4) / (2 * lambdaDenom ρ)
def lambdaBar (ρ : ℝ) : ℝ := (Real.log (2 / (1 - ρ)) + 3 / 4 + ρ / 4) / (2 * lambdaDenom ρ)
theorem lambdaBar_convexOn : ConvexOn ℝ (Set.Icc (3 / 5 : ℝ) (9 / 10)) lambdaBar
```
## Proof plan (app:comparisons)
(i) envelope_of_criterion: t = 1 trivial (psi ρ 1 = 0, eta 1 = 0). For t < 1, y := (1−t)/2 ∈ (0, 1/2]; eta t = h(y) = y log(1/y) + (−(1−y)log(1−y))
    ≥ y log(1/y) + y(1 − y/2 − y²/4) ≥ y[−log y + 1 − 5y/8]  (`neg_log_one_sub_ge'`; y²/4 ≤ y/8 for y ≤ 1/2).
    psi ρ t = 2y(2 − ρ² − 2y). So eta t − λ psi ≥ y[−log y + 1 + (4λ − 5/8) y − 2λ(2 − ρ²)] ≥ y[log(4λ − 5/8) + 2 − 2λ(2−ρ²)] ≥ 0,
    using −log y + c y ≥ 1 + log c for c = 4λ − 5/8 > 0 (`Real.log_le_sub_one_of_pos` on c·y, `Real.log_mul`).
(ii) lambdaReq_le_lambdaBar: eta ρ = h(y_ρ), y_ρ = (1−ρ)/2 ∈ [1/20, 1/5] (`binaryEntropy_symm`); h(y) = y log(1/y) − (1−y)log(1−y) ≤ y log(1/y) + (y − y²/2)
    (`neg_log_one_sub_le`: −log(1−y) ≤ (y − y²/2)/(1−y)); so eta ρ ≤ y[log(1/y) + 1 − y/2]; (1−ρ)Λ = 2yΛ > 0; log(1/y) = log(2/(1−ρ));
    1 − y/2 = 1 − (1−ρ)/4 = 3/4 + ρ/4. `div_le_div_iff`, `gcongr`.  lambdaDenom ρ ≥ 1 on [0,1] (1 + ρ − (31/40)ρ² ≥ 1 + ρ − ρ² ≥ 1).
(iii) lambdaBar_convexOn on [3/5, 9/10]. N(ρ) := log 2 − log(1−ρ) + 3/4 + ρ/4 (note log(2/(1−ρ)) = log 2 − log(1−ρ)), Λ := lambdaDenom.
    N' = 1/(1−ρ) + 1/4 > 0, N'' = 1/(1−ρ)² > 0, Λ' = 1 − (31/20)ρ, Λ'' = −31/20, N > 0, Λ > 0.
    λ̄ = N/(2Λ), λ̄' = (N'Λ − NΛ')/(2Λ²), λ̄'' = [N''Λ² − 2N'ΛΛ' + 2N(Λ')² − NΛΛ'']/(2Λ³).
    Numerator sign: if Λ' ≤ 0 (ρ ≥ 20/31) every term is ≥ 0. If Λ' > 0 then ρ < 20/31, so Λ' ≤ 7/100, N' < 13/4, N'' ≥ 25/4, Λ > 5/4, hence
    N''Λ² − 2N'ΛΛ' = Λ(N''Λ − 2N'Λ') > 0 and the other two terms are ≥ 0.
    Route: `MonotoneOn.convexOn_of_deriv (convex_Icc _ _) (continuousOn) (differentiableOn interior) (monotoneOn (deriv lambdaBar) interior)` where you establish
    `HasDerivAt lambdaBar (D1 ρ) ρ` with explicit D1 (then `deriv lambdaBar = D1` on the interior via `HasDerivAt.deriv`), and show D1 monotone on the interior
    by `monotoneOn_of_deriv_nonneg` with `HasDerivAt D1 (D2 ρ) ρ`, D2 ≥ 0 by the case analysis (clear denominators with `div_nonneg`, then `nlinarith`/`positivity`).
    Alternatively `convexOn_of_deriv2_nonneg`. Any valid route to `lambdaBar_convexOn` is acceptable.
(iv) Knots ρ_j = 3/5, 3/4, 17/20, 9/10; λ_j = 19/20, 287/250, 1377/1000, 1561/1000; s_j = 11553/10000, 689/500, 15857/10000, 17261/10000.
    From CK/Constants.lean: `AppF.knot_rho_3_5 : log(2/(1−3/5)) < 2·lambdaDenom(3/5)·(19/20) − 3/4 − (3/5)/4` (and knot_rho_3_4, knot_rho_17_20, knot_rho_9_10 — read their exact
    statements; they are written with the explicit polynomial `1 + ρ − (31/40)ρ^2`), which give λ̄(ρ_j) < λ_j; and `row_log_q127_40_lo : 11553/10000 < log(127/40)`,
    `row_log_q3967_1000_lo : 689/500 < log(3967/1000)`, `row_log_q4883_1000_lo`, `row_log_q5619_1000_lo` give s_j < log(4λ_j − 5/8) (4·19/20 − 5/8 = 127/40, etc.).
    On [ρ_j, ρ_{j+1}] write ρ = (1−z)ρ_j + zρ_{j+1}, z ∈ [0,1], and λ := (1−z)λ_j + zλ_{j+1}. Then
    (a) λ̄(ρ) ≤ (1−z)λ̄(ρ_j) + zλ̄(ρ_{j+1}) ≤ λ (convexity: `lambdaBar_convexOn.2` with weights 1−z, z), so eta ρ/((1−ρ)Λ) ≤ λ;
    (b) criterion at λ: log(4λ − 5/8) ≥ (1−z)log(4λ_j − 5/8) + z log(4λ_{j+1} − 5/8) (concavity of log: `strictConcaveOn_log_Ioi.concaveOn.2`) ≥ (1−z)s_j + z s_{j+1};
        so criterion ≥ P_j(z) := (1−z)s_j + z s_{j+1} + 2 − 2λ(2 − ρ²) with ρ, λ affine in z — a cubic in z. Bernstein form
        P_j(z) = c_{j0}(1−z)³ + 3c_{j1}z(1−z)² + 3c_{j2}z²(1−z) + c_{j3}z³ with positive coefficients
        j=0: [393/10000, 829/75000, 1249/60000, 31/400]; j=1: [31/400, 1683/40000, 11161/300000, 13493/200000]; j=2: [13493/200000, 21353/600000, 493/30000, 273/25000]
        (verify by `ring_nf`/`linear_combination`; if a coefficient does not match exactly, recompute it — or simply prove P_j(z) ≥ 0 on [0,1] with `nlinarith` using hints
        `mul_nonneg hz (sub_nonneg.2 hz1)`, `pow_nonneg`, etc.). Then λ > 5/32 obviously.
    (c) conclude with envelope_of_criterion and psi ρ t ≥ 0 (both factors ≥ 0 on [0,1]).
(v) entropy_comparison: given ρ ∈ [3/5, 9/10], pick the interval, set z, apply (a),(b),(c): eta ρ/((1−ρ)Λ)·psi ≤ λ·psi ≤ eta t.
