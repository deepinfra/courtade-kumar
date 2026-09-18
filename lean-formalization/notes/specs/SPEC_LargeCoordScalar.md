# TASK: CK/LargeCoordScalar.lean — the large-coordinate scalar facts (manuscript eq:largecoordscalar, App. B.1–B.2)

Imports: `import CK.KappaSeries` (read it: `hasSum_kappa`, `kappa_ge_partial`, `kappa_even`, `continuous_kappa`), `import CK.Constants`, `import CK.ProductCentering` (pairEntropy lemmas).
Recall eta u = log 2 − kappa u; `pairEntropy m z = (eta (m+z) + eta (m−z))/2`; `curvature u = 1/(1−u²)`; `hasDerivAt_eta : HasDerivAt eta (−atanhLog u) u`; `hasDerivAt_atanhLog : HasDerivAt atanhLog (curvature u) u` (both for −1 < u < 1).

## TARGETS (exact statements)
```lean
/-- eq:largecoordscalar: (1 − bρ²) η(ρ) ≤ (1 − ρ²) η(ρb) for 13/20 ≤ b ≤ 1, 0 ≤ ρ ≤ 9/10. -/
theorem large_coord_scalar {ρ b : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 9 / 10) (hb0 : 13 / 20 ≤ b) (hb1 : b ≤ 1) :
    (1 - b * ρ ^ 2) * eta ρ ≤ (1 - ρ ^ 2) * eta (ρ * b)
/-- App B.1: m ↦ η(m) − (1−ρ²)·Q(m, ρb) is even and concave on |m| ≤ 1 − b, hence maximal at m = 0. -/
theorem U_le_U_zero {ρ b m : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hb0 : 0 ≤ b) (hmb : |m| + b ≤ 1) :
    eta m - (1 - ρ ^ 2) * pairEntropy m (ρ * b) ≤ eta 0 - (1 - ρ ^ 2) * pairEntropy 0 (ρ * b)
theorem concaveOn_eta : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) eta
```
## Proof plan
A. concaveOn_eta: eta is continuous on [−1,1], differentiable on (−1,1) with derivative −atanhLog, which is antitone (atanhLog_mono) ⇒ `AntitoneOn.concaveOn_of_deriv`
   (or `concaveOn_of_deriv2_nonpos` with eta'' = −curvature ≤ 0).
B. large_coord_scalar.
   B1 (reduce to b = 13/20 by concavity in b): for fixed ρ, with s := (b − 13/20)/(7/20) ∈ [0,1], ρb = (1−s)(13ρ/20) + sρ, so by concavity of eta on [−1,1]:
      eta(ρb) ≥ (1−s) eta(13ρ/20) + s eta(ρ). Then (1−ρ²)eta(ρb) − (1 − bρ²)eta ρ ≥ (1−s)[(1−ρ²)eta(13ρ/20) − (1 − (13/20)ρ²) eta ρ] + s[(1−ρ²)eta ρ − (1−ρ²) eta ρ]
      = (1−s)·φ(ρ), using 1 − bρ² = (1−s)(1 − (13/20)ρ²) + s(1 − ρ²). So it suffices that φ(ρ) := (1 − ρ²)eta(13ρ/20) − (1 − (13/20)ρ²) eta ρ ≥ 0 on [0, 9/10].
   B2 (φ ≥ 0 by the κ-series). Put c := 13/20, a_j := 1/(2j(2j−1)). With eta = log 2 − kappa:
      φ(ρ) = −(1−c) ρ² log 2 + (1 − cρ²) kappa ρ − (1 − ρ²) kappa(cρ).
      For 0 ≤ ρ < 1, `hasSum_kappa` at ρ and at cρ, and HasSum algebra (`HasSum.mul_left`, `HasSum.sub`, index shift `hasSum_nat_add_iff`), give
      φ(ρ) = Σ_{j≥1} C_j ρ^{2j} with C_1 = a_1(1 − c²) − (1−c) log 2 and, for j ≥ 2, C_j = a_j(1 − c^{2j}) − c·a_{j−1}(1 − c^{2j−3}).
      [Coefficient bookkeeping: (1 − cρ²)Σ_j a_jρ^{2j} = Σ_j a_jρ^{2j} − Σ_j c a_j ρ^{2j+2}; (1−ρ²)Σ_j a_j c^{2j}ρ^{2j} = Σ_j a_jc^{2j}ρ^{2j} − Σ_j a_j c^{2j}ρ^{2j+2}.]
      You do NOT need an exact HasSum for φ: it suffices to show φ(ρ) ≥ Σ_{j=1}^{5} C_j ρ^{2j}, i.e. that the tail Σ_{j≥6} C_j ρ^{2j} is ≥ 0, because C_j ≥ 0 for j ≥ 6:
      a_j(1 − c^{2j}) ≥ c a_{j−1}(1 − c^{2j−3}) ⇐ (1 − c^{12})·(2j−2)(2j−3) ≥ c·2j(2j−1)  ⇐ (994/1000)(2j−2)(2j−3) ≥ (13/20)·2j(2j−1) for j ≥ 6 (true: 1720j² − 10800j + 7455 ≥ 0 for j ≥ 6; also 1 − c^{12} ≥ 994/1000 by norm_num).
      Recommended concrete route: write kappa ρ = Σ_{j<5}(…) + tail₁, kappa(cρ) = Σ_{j<5}(…) + tail₂ via `hasSum_nat_add_iff` (peel 5 terms), and bound the combination of tails termwise with `hasSum_le`
      (or: prove HasSum for the tail combination and apply `HasSum.nonneg`-style `hasSum_le` against the zero series). Any correct route is fine.
      Then with x := ρ² ∈ [0, 81/100]: P(x) := C_1 + C_2x + C_3x² + C_4x³ + C_5x⁴; C_2..C_5 are explicit negative rationals so P is decreasing in x and
      P(x) ≥ P(81/100) = C_1 + (explicit rational ≈ −0.04327) > 0 because C_1 = (7/20)(33/40 − log 2) > (7/20)(33/40 − 0.693147180561) ≈ 0.04615 (`AppF.log_q2`). Hence φ(ρ) ≥ ρ² P(ρ²) ≥ 0.
      (ρ = 0 is trivial; ρ ≤ 9/10 < 1 so the series applies everywhere needed.)
C. U_le_U_zero. V(m) := eta m − (1−ρ²)·pairEntropy m (ρb). V is even (`eta_even`; pairEntropy (−m) z = pairEntropy m z by eta_even and add_comm).
   If 1 − b = 0 then m = 0, trivial. Otherwise V is concave on I := Icc (−(1−b)) (1−b): continuous on I, differentiable on the interior with
   V'(m) = −atanhLog m + (1−ρ²)(atanhLog(m+ρb) + atanhLog(m−ρb))/2, and V' has derivative V''(m) = −curvature m + (1−ρ²)(curvature(m+ρb) + curvature(m−ρb))/2 ≤ 0 on the interior
   (interior points have |m| < 1 − b so |m ± ρb| < 1). Sign of V'': with k(u) = 1/(1−u²),
   k(m) − (1−ρ²)(k(m+ρb) + k(m−ρb))/2 = ρ² D₀ / [(1−m²)(1−(m+ρb)²)(1−(m−ρb)²)],  D₀ = (1−m²)² − b²[1 + 3m² + ρ²(1−m²)] + ρ²b⁴  (verify by `field_simp; ring`),
   and D₀ ≥ 0 on |m| + b ≤ 1: by evenness in m take m ≥ 0, put z := (1−m)² − b² ≥ 0; then D₀ = 2m(1−m)³(1−ρ²) + z[(1−ρ²)(1+3m²) + 4ρ²m] + ρ² z² (check by `ring`), each term ≥ 0.
   Use `concaveOn_of_deriv2_nonpos` (or `AntitoneOn.concaveOn_of_deriv` with V' antitone via `antitoneOn_of_deriv_nonpos`). Then concavity + evenness:
   V(0) = V((1/2)m + (1/2)(−m)) ≥ (1/2)V(m) + (1/2)V(−m) = V(m).
