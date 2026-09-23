# TASK: CK/Anchor.lean — the strict anchor at ρ = 3/5 (manuscript eq:anchorcomparison, app:anchor)

Imports: `import CK.GainBounds`, `import CK.Constants`.
Definitions in CK/AnalyticTargets.lean: `psi rho t := (1 - t) * (1 + t - rho ^ 2)`,
`StrictAnchorGoal : Prop := ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (39 / 40 : ℝ) * psi (3 / 5) t ≤ eta t`.

## TARGET (exact statement)
```lean
theorem strict_anchor : StrictAnchorGoal
```
## Proof plan (app:anchor)
Case A: 1/3 ≤ t < 1. Put y = (1 − t)/2 ∈ (0, 1/3]. eta t = h(y) (`binaryEntropy_symm`), h(y) = y·log(1/y) + (−(1−y)log(1−y)),
  and −(1−y)log(1−y) ≥ y − y²/2 − y³/4 = y(1 − y/2 − y²/4) ≥ y(1 − 7y/12) for y ≤ 1/3 (`neg_log_one_sub_ge'`; y²/4 ≤ y/12).
  psi (3/5) t = 2y(2 − 2y − 9/25) = 2y(41/25 − 2y). Hence
  eta t − (39/40)psi ≥ y[−log y + 1 − 7y/12 − (39/20)(41/25 − 2y)] = y[−log y + (199/60)y − 599/500 − 1 + 2 − … ] — concretely
  = y[−log y + (199/60)·y + 1 − 1599/500].  Use −log y + c·y ≥ 1 + log c with c = 199/60 (from `Real.log_le_sub_one_of_pos` applied to c·y:
  log(cy) ≤ cy − 1 and log(cy) = log c + log y). So the bracket ≥ 2 + log(199/60) − 1599/500 = log(199/60) − 599/500 > 0 (`AppF.row_log_q199_60_lo`).
  Multiply by y > 0.
Case B: t = 1: psi (3/5) 1 = 0 and eta 1 = 0 (`eta_one`).
Case C: 0 ≤ t ≤ 1/3. Let D t := eta t − (39/40)·psi (3/5) t. HasDerivAt D (−atanhLog t + (39/20)·t − 351/1000) t on (−1,1)
  (`hasDerivAt_eta`; psi is a polynomial; d/dt psi = −(1+t−ρ²) + (1−t) = ρ² − 2t with ρ² = 9/25; (39/40)(9/25) = 351/1000).
  D' has derivative −curvature t + 39/20 (`hasDerivAt_atanhLog`), which is ≥ 0 on [0,1/3] since curvature t = 1/(1−t²) ≤ 9/8 there.
  So D' is monotone on [0,1/3] (`monotoneOn_of_deriv_nonneg`), and D'(1/3) = −atanhLog(1/3) + 13/20 − 351/1000 = −(log 2)/2 + 299/1000 < 0
  because atanhLog(1/3) = (log(4/3) − log(2/3))/2 = (log 2)/2 (`Real.log_div`, or directly log(4/3) − log(2/3) = log 2) and log 2 > 56/81 (`row_log_q2_lo`).
  Hence D' ≤ 0 on [0,1/3], so D is antitone there (`antitoneOn_of_deriv_nonpos`), so D t ≥ D(1/3).
  D(1/3) = eta(1/3) − (39/40)·psi(3/5)(1/3) = (log 3 − (2/3)log 2) − 949/1500 > 0 (`AppF.comb_log3`).
  [eta(1/3) = h(2/3) = h(1/3) = −(1/3)log(1/3) − (2/3)log(2/3) = log 3 − (2/3)log 2 (`Real.log_div`); psi(3/5)(1/3) = (2/3)(4/3 − 9/25) = 146/225; (39/40)(146/225) = 949/1500 — check with `norm_num`.]
