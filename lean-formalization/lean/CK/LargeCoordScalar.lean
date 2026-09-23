import CK.KappaSeries
import CK.Constants
import CK.ProductCentering

/-!
# The large-coordinate scalar facts (manuscript eq:largecoordscalar, App. B.1–B.2)

* `concaveOn_eta`: `eta` is concave on `[-1, 1]` (its derivative `-atanhLog` is antitone).
* `large_coord_scalar` (eq:largecoordscalar): `(1 - bρ²) η(ρ) ≤ (1 - ρ²) η(ρb)` for
  `13/20 ≤ b ≤ 1`, `0 ≤ ρ ≤ 9/10`.  Concavity of `eta` reduces it to the endpoint
  `b = 13/20`, where the `kappa` series (eq:series) turns the claim into a polynomial
  inequality in `ρ²` plus the rational bracket `AppF.log_q2` on `log 2`.
* `U_le_U_zero` (App. B.1): `m ↦ η(m) - (1-ρ²) Q(m, ρb)` is even and concave on
  `|m| ≤ 1 - b`, hence maximal at `m = 0`.  The second derivative is
  `-ρ² D₀ / [(1-m²)(1-(m+ρb)²)(1-(m-ρb)²)]` with `D₀ ≥ 0` (App. B.2).
-/
noncomputable section
namespace CK
open scoped BigOperators

/-! ## Concavity of `eta` on `[-1, 1]` -/

theorem concaveOn_eta : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) eta := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _) continuous_eta.continuousOn
  · rw [interior_Icc]
    intro x hx
    exact (hasDerivAt_eta hx.1 hx.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx y hy hxy
    rw [(hasDerivAt_eta hx.1 hx.2).deriv, (hasDerivAt_eta hy.1 hy.2).deriv]
    have := atanhLog_mono hx.1 hxy hy.2
    linarith

/-! ## The endpoint `b = 13/20` via the `kappa` series (App. B.2) -/

/-- Each term of the series for `(1 - cρ²) κ(ρ) - (1 - ρ²) κ(cρ)` is nonnegative (`c = 13/20`). -/
theorem kappa_comb_term_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (n : ℕ) :
    0 ≤ (1 - 13 / 20 * ρ ^ 2) *
          (ρ ^ (2 * (n + 1)) / ((2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1)))
        - (1 - ρ ^ 2) *
          ((ρ * (13 / 20)) ^ (2 * (n + 1)) / ((2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1))) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hD : 0 < (2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1) := by
    apply mul_pos <;> linarith
  have hck : (13 / 20 : ℝ) ^ (2 * (n + 1)) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hck0 : (0 : ℝ) ≤ (13 / 20 : ℝ) ^ (2 * (n + 1)) := by positivity
  have hpk : 0 ≤ ρ ^ (2 * (n + 1)) := pow_nonneg hρ0 _
  have h1ρ : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  have e : (1 - 13 / 20 * ρ ^ 2) *
          (ρ ^ (2 * (n + 1)) / ((2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1)))
        - (1 - ρ ^ 2) *
          ((ρ * (13 / 20)) ^ (2 * (n + 1)) / ((2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1)))
      = ρ ^ (2 * (n + 1)) * ((1 - 13 / 20 * ρ ^ 2) - (1 - ρ ^ 2) * (13 / 20) ^ (2 * (n + 1)))
          / ((2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1)) := by
    rw [mul_pow]; ring
  rw [e]
  apply div_nonneg _ hD.le
  apply mul_nonneg hpk
  nlinarith [mul_le_mul_of_nonneg_left hck h1ρ]

/-- The polynomial inequality behind App. B.2: six terms of the series dominate
`(7/20) ρ² · 0.693147180561 ≥ (7/20) ρ² log 2` on `[0, 9/10]`. -/
theorem kappa_comb_partial_bound {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 9 / 10) :
    7 / 20 * (693147180561 / 1000000000000) * ρ ^ 2 ≤
      ∑ n ∈ Finset.range 6, ((1 - 13 / 20 * ρ ^ 2) *
          (ρ ^ (2 * (n + 1)) / ((2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1)))
        - (1 - ρ ^ 2) *
          ((ρ * (13 / 20)) ^ (2 * (n + 1)) / ((2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1)))) := by
  have hp : ∀ k : ℕ, ρ ^ k ≤ (9 / 10) ^ k := fun k => pow_le_pow_left₀ hρ0 hρ1 k
  have hp0 : ∀ k : ℕ, 0 ≤ ρ ^ k := fun k => pow_nonneg hρ0 k
  have h2 := hp 2
  have h4 := hp 4
  have h6 := hp 6
  have h8 := hp 8
  have h10 := hp 10
  have h12 := hp 12
  have h14 := hp 14
  norm_num at h2 h4 h6 h8 h10 h12 h14
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [mul_pow]
  nlinarith [hp0 2, hp0 4, hp0 6, hp0 8, hp0 10, hp0 12, hp0 14]

/-- App. B.2, φ(ρ) ≥ 0: `(1 - (13/20) ρ²) η(ρ) ≤ (1 - ρ²) η(13ρ/20)` on `[0, 9/10]`. -/
theorem large_coord_scalar_endpoint {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 9 / 10) :
    (1 - 13 / 20 * ρ ^ 2) * eta ρ ≤ (1 - ρ ^ 2) * eta (ρ * (13 / 20)) := by
  have hρ : |ρ| < 1 := by rw [abs_of_nonneg hρ0]; linarith
  have hcρ : |ρ * (13 / 20)| < 1 := by
    rw [abs_of_nonneg (by positivity)]; linarith
  have hS := ((hasSum_kappa hρ).mul_left (1 - 13 / 20 * ρ ^ 2)).sub
    ((hasSum_kappa hcρ).mul_left (1 - ρ ^ 2))
  have hpart := sum_le_hasSum (Finset.range 6)
    (fun n _ => kappa_comb_term_nonneg hρ0 (by linarith) n) hS
  have hkey := kappa_comb_partial_bound hρ0 hρ1
  have hlog := AppF.log_q2.2
  have hL : 7 / 20 * ρ ^ 2 * Real.log 2 ≤ 7 / 20 * ρ ^ 2 * (693147180561 / 1000000000000) :=
    mul_le_mul_of_nonneg_left hlog.le (by positivity)
  unfold kappa at hpart
  nlinarith [hpart, hkey, hL]

/-! ## eq:largecoordscalar -/

/-- eq:largecoordscalar: (1 − bρ²) η(ρ) ≤ (1 − ρ²) η(ρb) for 13/20 ≤ b ≤ 1, 0 ≤ ρ ≤ 9/10. -/
theorem large_coord_scalar {ρ b : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 9 / 10) (hb0 : 13 / 20 ≤ b) (hb1 : b ≤ 1) :
    (1 - b * ρ ^ 2) * eta ρ ≤ (1 - ρ ^ 2) * eta (ρ * b) := by
  obtain ⟨s, rfl⟩ : ∃ s : ℝ, b = 13 / 20 + 7 / 20 * s := ⟨(b - 13 / 20) / (7 / 20), by ring⟩
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 1 := by linarith
  have hφ := large_coord_scalar_endpoint hρ0 hρ1
  have hx : ρ * (13 / 20) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
  have hy : ρ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hconc := concaveOn_eta.2 hx hy (by linarith : (0 : ℝ) ≤ 1 - s) hs0
    (by ring : (1 - s) + s = 1)
  simp only [smul_eq_mul] at hconc
  rw [show (1 - s) * (ρ * (13 / 20)) + s * ρ = ρ * (13 / 20 + 7 / 20 * s) by ring] at hconc
  have h1ρ : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hconc h1ρ,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - s) (sub_nonneg.mpr hφ)]

/-! ## App. B.1: the centered function `U(m)` is even and concave -/

theorem pairEntropy_neg_left (m z : ℝ) : pairEntropy (-m) z = pairEntropy m z := by
  unfold pairEntropy
  rw [show (-m + z : ℝ) = -(m - z) by ring, show (-m - z : ℝ) = -(m + z) by ring,
    eta_even, eta_even]
  ring

theorem hasDerivAt_Lpair_nu {nu z : ℝ} (h1 : -1 < nu + z) (h2 : nu + z < 1)
    (h3 : -1 < nu - z) (h4 : nu - z < 1) :
    HasDerivAt (fun w : ℝ => Lpair w z) ((curvature (nu + z) + curvature (nu - z)) / 2) nu := by
  have ha1 : HasDerivAt (fun w : ℝ => atanhLog (w + z)) (curvature (nu + z)) nu := by
    simpa using (hasDerivAt_atanhLog h1 h2).comp nu ((hasDerivAt_id nu).add_const z)
  have ha2 : HasDerivAt (fun w : ℝ => atanhLog (w - z)) (curvature (nu - z)) nu := by
    simpa using (hasDerivAt_atanhLog h3 h4).comp nu ((hasDerivAt_id nu).sub_const z)
  exact (ha1.add ha2).div_const 2

/-- The numerator `D₀` of App. B.2. -/
def D0 (m ρ b : ℝ) : ℝ :=
  (1 - m ^ 2) ^ 2 - b ^ 2 * (1 + 3 * m ^ 2 + ρ ^ 2 * (1 - m ^ 2)) + ρ ^ 2 * b ^ 4

theorem D0_abs (m ρ b : ℝ) : D0 |m| ρ b = D0 m ρ b := by
  unfold D0; rw [sq_abs]

theorem D0_eq (m ρ b : ℝ) :
    D0 m ρ b = 2 * m * (1 - m) ^ 3 * (1 - ρ ^ 2)
      + ((1 - m) ^ 2 - b ^ 2) * ((1 - ρ ^ 2) * (1 + 3 * m ^ 2) + 4 * ρ ^ 2 * m)
      + ρ ^ 2 * ((1 - m) ^ 2 - b ^ 2) ^ 2 := by
  unfold D0; ring

theorem D0_nonneg {m ρ b : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hb0 : 0 ≤ b)
    (hmb : |m| + b ≤ 1) : 0 ≤ D0 m ρ b := by
  have hm0 : 0 ≤ |m| := abs_nonneg m
  have hm1 : |m| ≤ 1 := by linarith
  have hz : 0 ≤ (1 - |m|) ^ 2 - b ^ 2 := by nlinarith
  have h1ρ : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  rw [← D0_abs, D0_eq]
  have h3 : 0 ≤ (1 - |m|) ^ 3 := pow_nonneg (by linarith) 3
  have hA := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm0) h3) h1ρ
  have hB := mul_nonneg hz (add_nonneg (mul_nonneg h1ρ (by positivity : (0 : ℝ) ≤ 1 + 3 * |m| ^ 2))
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg ρ)) hm0))
  have hC := mul_nonneg (sq_nonneg ρ) (sq_nonneg ((1 - |m|) ^ 2 - b ^ 2))
  linarith

/-- The curvature combination as a single fraction with numerator `ρ² D₀` (App. B.2). -/
theorem curvature_comb_eq {m ρ b : ℝ} (hA : 1 - m ^ 2 ≠ 0) (hB : 1 - (m + ρ * b) ^ 2 ≠ 0)
    (hC : 1 - (m - ρ * b) ^ 2 ≠ 0) :
    curvature m - (1 - ρ ^ 2) * ((curvature (m + ρ * b) + curvature (m - ρ * b)) / 2)
      = ρ ^ 2 * D0 m ρ b / ((1 - m ^ 2) * (1 - (m + ρ * b) ^ 2) * (1 - (m - ρ * b) ^ 2)) := by
  unfold curvature D0
  field_simp
  ring

/-- App B.1: m ↦ η(m) − (1−ρ²)·Q(m, ρb) is even and concave on |m| ≤ 1 − b, hence maximal at m = 0. -/
theorem U_le_U_zero {ρ b m : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hb0 : 0 ≤ b) (hmb : |m| + b ≤ 1) :
    eta m - (1 - ρ ^ 2) * pairEntropy m (ρ * b) ≤ eta 0 - (1 - ρ ^ 2) * pairEntropy 0 (ρ * b) := by
  have hm0 : 0 ≤ |m| := abs_nonneg m
  rcases eq_or_lt_of_le (show b ≤ 1 by linarith) with hb1 | hb1
  · -- `b = 1` forces `m = 0`
    have hm : m = 0 := abs_nonpos_iff.mp (by linarith)
    subst hm
    exact le_refl _
  · have hd0 : 0 < 1 - b := by linarith
    have hz0 : 0 ≤ ρ * b := mul_nonneg hρ0 hb0
    have hzb : ρ * b ≤ b := by nlinarith
    have hconc : ConcaveOn ℝ (Set.Icc (-(1 - b)) (1 - b))
        (fun w : ℝ => eta w - (1 - ρ ^ 2) * pairEntropy w (ρ * b)) := by
      apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
        (f' := fun w => -atanhLog w + (1 - ρ ^ 2) * Lpair w (ρ * b))
        (f'' := fun w => -curvature w
          + (1 - ρ ^ 2) * ((curvature (w + ρ * b) + curvature (w - ρ * b)) / 2))
      · exact (continuous_eta.sub
          (continuous_const.mul (continuous_pairEntropy_nu (ρ * b)))).continuousOn
      · rw [interior_Icc]
        intro w hw
        have h1 : -1 < w := by linarith [hw.1]
        have h2 : w < 1 := by linarith [hw.2]
        have h3 : w + ρ * b < 1 := by linarith [hw.2]
        have h4 : -1 < w - ρ * b := by linarith [hw.1]
        refine (((hasDerivAt_eta h1 h2).sub
          ((hasDerivAt_pairEntropy_nu hz0 h3 h4).const_mul (1 - ρ ^ 2))).congr_deriv
            ?_).hasDerivWithinAt
        ring
      · rw [interior_Icc]
        intro w hw
        have h1 : -1 < w := by linarith [hw.1]
        have h2 : w < 1 := by linarith [hw.2]
        have h3 : w + ρ * b < 1 := by linarith [hw.2]
        have h4 : -1 < w - ρ * b := by linarith [hw.1]
        have h5 : -1 < w + ρ * b := by linarith
        have h6 : w - ρ * b < 1 := by linarith
        exact ((hasDerivAt_atanhLog h1 h2).neg.add
          ((hasDerivAt_Lpair_nu h5 h3 h4 h6).const_mul (1 - ρ ^ 2))).hasDerivWithinAt
      · rw [interior_Icc]
        intro w hw
        have h1 : -1 < w := by linarith [hw.1]
        have h2 : w < 1 := by linarith [hw.2]
        have h3 : w + ρ * b < 1 := by linarith [hw.2]
        have h4 : -1 < w - ρ * b := by linarith [hw.1]
        have h5 : -1 < w + ρ * b := by linarith
        have h6 : w - ρ * b < 1 := by linarith
        have hA : 0 < 1 - w ^ 2 := by nlinarith
        have hB : 0 < 1 - (w + ρ * b) ^ 2 := by nlinarith
        have hC : 0 < 1 - (w - ρ * b) ^ 2 := by nlinarith
        have hkey := curvature_comb_eq (m := w) (ρ := ρ) (b := b) hA.ne' hB.ne' hC.ne'
        have hwabs : |w| < 1 - b := abs_lt.mpr ⟨hw.1, hw.2⟩
        have hD := D0_nonneg (m := w) hρ0 hρ1 hb0 (by linarith)
        have hfrac : 0 ≤ ρ ^ 2 * D0 w ρ b
            / ((1 - w ^ 2) * (1 - (w + ρ * b) ^ 2) * (1 - (w - ρ * b) ^ 2)) :=
          div_nonneg (mul_nonneg (sq_nonneg ρ) hD) (by positivity)
        show -curvature w
          + (1 - ρ ^ 2) * ((curvature (w + ρ * b) + curvature (w - ρ * b)) / 2) ≤ 0
        linarith
    have hm := abs_le.mp (show |m| ≤ 1 - b by linarith)
    have hmI : m ∈ Set.Icc (-(1 - b)) (1 - b) := ⟨hm.1, hm.2⟩
    have hnegmI : -m ∈ Set.Icc (-(1 - b)) (1 - b) := ⟨by linarith [hm.2], by linarith [hm.1]⟩
    have h := hconc.2 hmI hnegmI (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    simp only [smul_eq_mul] at h
    rw [show (1 / 2 : ℝ) * m + 1 / 2 * -m = 0 by ring, eta_even, pairEntropy_neg_left] at h
    linarith

end CK
