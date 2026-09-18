import CK.ProductCentering

/-!
# Layer B5: the two transfer rules (manuscript Lemma [lem:transfer])

Purely algebraic consequences of product centering: with
`K₀ = η(ρt) - η(t)`, `M₀ = η(ρt)`, `K = Q(ν,ρt) - Q(ν,t)`, `M = Q(ν,ρt)`,

* `transfer_product`: `K₀M₀ - ℓ² ≥ γ ≥ 0` forces `q(d) ≥ γ/ln 2` for every real `d`;
* `transfer_gain`: `K₀ ≥ D²M₀` forces `q(d) ≥ q₀(d)` for `0 ≤ d ≤ D`;
* `pairEntropy_le_eta`: the concavity comparison `M ≤ M₀` behind the relative
  transfer (eq:relative-transfer).
-/
noncomputable section
namespace CK

/-! ## Abstract algebraic cores -/

theorem transfer_product_alg {K M K0 M0 l g : ℝ}
    (hKM : K0 * M0 ≤ K * M) (hM : 0 < M) (hM2 : M ≤ Real.log 2)
    (hg0 : 0 ≤ g) (hg : g ≤ K0 * M0 - l ^ 2) (d : ℝ) :
    g / Real.log 2 ≤ K + M * d ^ 2 - 2 * l * d := by
  have hlog : 0 < Real.log 2 := lt_of_lt_of_le hM hM2
  have key : K + M * d ^ 2 - 2 * l * d = M * (d - l / M) ^ 2 + (K * M - l ^ 2) / M := by
    field_simp
    ring
  rw [key]
  have h1 : g / Real.log 2 ≤ g / M := div_le_div_of_nonneg_left hg0 hM hM2
  have h2 : g / M ≤ (K * M - l ^ 2) / M := by
    rw [div_le_div_iff₀ hM hM]
    nlinarith
  have h3 : 0 ≤ M * (d - l / M) ^ 2 := by positivity
  linarith

theorem transfer_gain_alg {K M K0 M0 D d : ℝ}
    (hKM : K0 * M0 ≤ K * M) (hKK0 : K0 ≤ K) (hM : 0 < M)
    (hD : D ^ 2 * M0 ≤ K0) (hd0 : 0 ≤ d) (hdD : d ≤ D) :
    K0 + M0 * d ^ 2 ≤ K + M * d ^ 2 := by
  have hdsq : d ^ 2 ≤ D ^ 2 := by nlinarith
  rcases le_or_lt M0 M with hle | hlt
  · nlinarith [sq_nonneg d]
  · -- M < M0 : use (K - K0)·M ≥ K0·(M0 - M) ≥ d²M·(M0 - M)
    have h1 : K0 * (M0 - M) ≤ (K - K0) * M := by nlinarith
    have h2 : d ^ 2 * M ≤ K0 := by nlinarith
    have h3 : d ^ 2 * M * (M0 - M) ≤ K0 * (M0 - M) := by nlinarith
    nlinarith

/-! ## Positivity and upper bound for the mixed entropy -/

theorem eta_le_log_two' {u : ℝ} (hu : -1 ≤ u) (hu1 : u ≤ 1) : eta u ≤ Real.log 2 := by
  rw [← eta_abs]
  exact eta_le_log_two (abs_nonneg u) (abs_le.mpr ⟨hu, hu1⟩)

theorem pairEntropy_le_log_two {nu z : ℝ} (h1 : -1 ≤ nu + z) (h2 : nu + z ≤ 1)
    (h3 : -1 ≤ nu - z) (h4 : nu - z ≤ 1) : pairEntropy nu z ≤ Real.log 2 := by
  unfold pairEntropy
  have := eta_le_log_two' h1 h2
  have := eta_le_log_two' h3 h4
  linarith

/-- Concavity comparison: the mixed entropy is maximal at the symmetric pair. -/
theorem pairEntropy_le_eta {nu z : ℝ} (hnu : 0 ≤ nu) (hz : 0 ≤ z) (hsum : nu + z ≤ 1) :
    pairEntropy nu z ≤ eta z := by
  rcases eq_or_lt_of_le hnu with rfl | hnu'
  · rw [pairEntropy_zero_left]
  have hz1 : z < 1 := by linarith
  have hmono : MonotoneOn (fun w : ℝ => eta z - pairEntropy w z) (Set.Icc 0 nu) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact (continuous_const.sub (continuous_pairEntropy_nu z)).continuousOn
    · rw [interior_Icc]
      intro w hw
      exact ((hasDerivAt_const w (eta z)).sub
        (hasDerivAt_pairEntropy_nu (nu := w) hz (by nlinarith [hw.2]) (by nlinarith [hw.1]))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro w hw
      rw [((hasDerivAt_const w (eta z)).sub
        (hasDerivAt_pairEntropy_nu (nu := w) hz (by nlinarith [hw.2]) (by nlinarith [hw.1]))).deriv]
      have := Lpair_nonneg (le_of_lt hw.1) hz (by nlinarith [hw.2])
      linarith
  have h' : eta z - pairEntropy 0 z ≤ eta z - pairEntropy nu z :=
    hmono ⟨le_refl 0, le_of_lt hnu'⟩ ⟨le_of_lt hnu', le_refl nu⟩ (le_of_lt hnu')
  rw [pairEntropy_zero_left] at h'
  linarith

/-! ## The transfer rules in centered coordinates -/

theorem transfer_product {p t nu l g : ℝ} (hp0 : 0 < p) (hp1 : p < 1 / 2)
    (ht0 : 0 < t) (ht1 : t < 1) (hnu : 0 ≤ nu) (hsum : nu + t ≤ 1)
    (hg0 : 0 ≤ g)
    (hg : g ≤ (eta ((1 - 2 * p) * t) - eta t) * eta ((1 - 2 * p) * t) - l ^ 2) (d : ℝ) :
    g / Real.log 2 ≤ (pairEntropy nu ((1 - 2 * p) * t) - pairEntropy nu t)
      + pairEntropy nu ((1 - 2 * p) * t) * d ^ 2 - 2 * l * d := by
  set r : ℝ := (1 - 2 * p) * t with hrdef
  have hr0 : 0 ≤ r := by
    rw [hrdef]; exact mul_nonneg (by linarith) (le_of_lt ht0)
  have hrt : r < t := by nlinarith
  have hnur : nu + r < 1 := by nlinarith
  have hpc := product_centering p nu t hp0 hp1 hnu (le_of_lt ht0) hsum
  have hM : 0 < pairEntropy nu r :=
    pairEntropy_pos (by linarith) hnur (by linarith) (by linarith)
  have hM2 : pairEntropy nu r ≤ Real.log 2 :=
    pairEntropy_le_log_two (by linarith) (by linarith) (by linarith) (by linarith)
  exact transfer_product_alg hpc.2 hM hM2 hg0 hg d

theorem transfer_gain {p t nu D d l : ℝ} (hp0 : 0 < p) (hp1 : p < 1 / 2)
    (ht0 : 0 < t) (ht1 : t < 1) (hnu : 0 ≤ nu) (hsum : nu + t ≤ 1)
    (hD : D ^ 2 * eta ((1 - 2 * p) * t) ≤ eta ((1 - 2 * p) * t) - eta t)
    (hd0 : 0 ≤ d) (hdD : d ≤ D) :
    (eta ((1 - 2 * p) * t) - eta t) + eta ((1 - 2 * p) * t) * d ^ 2 - 2 * l * d
      ≤ (pairEntropy nu ((1 - 2 * p) * t) - pairEntropy nu t)
        + pairEntropy nu ((1 - 2 * p) * t) * d ^ 2 - 2 * l * d := by
  set r : ℝ := (1 - 2 * p) * t with hrdef
  have hr0 : 0 ≤ r := by
    rw [hrdef]; exact mul_nonneg (by linarith) (le_of_lt ht0)
  have hrt : r < t := by nlinarith
  have hnur : nu + r < 1 := by nlinarith
  have hpc := product_centering p nu t hp0 hp1 hnu (le_of_lt ht0) hsum
  have hM : 0 < pairEntropy nu r :=
    pairEntropy_pos (by linarith) hnur (by linarith) (by linarith)
  have := transfer_gain_alg hpc.2 hpc.1 hM hD hd0 hdD
  linarith

/-- The retained-denominator transfer (eq:relative-transfer): with a nonnegative
centered numerator, `q(d) ≥ (K₀M₀ - ℓ²)/M₀`. -/
theorem transfer_relative_alg {K M K0 M0 l : ℝ}
    (hKM : K0 * M0 ≤ K * M) (hM : 0 < M) (hMM0 : M ≤ M0)
    (hnum : 0 ≤ K0 * M0 - l ^ 2) (d : ℝ) :
    (K0 * M0 - l ^ 2) / M0 ≤ K + M * d ^ 2 - 2 * l * d := by
  have key : K + M * d ^ 2 - 2 * l * d = M * (d - l / M) ^ 2 + (K * M - l ^ 2) / M := by
    field_simp
    ring
  rw [key]
  have h1 : (K0 * M0 - l ^ 2) / M0 ≤ (K0 * M0 - l ^ 2) / M :=
    div_le_div_of_nonneg_left hnum hM hMM0
  have h2 : (K0 * M0 - l ^ 2) / M ≤ (K * M - l ^ 2) / M := by
    rw [div_le_div_iff₀ hM hM]
    nlinarith
  have h3 : 0 ≤ M * (d - l / M) ^ 2 := by positivity
  linarith

theorem transfer_relative {p t nu l d : ℝ} (hp0 : 0 < p) (hp1 : p < 1 / 2)
    (ht0 : 0 < t) (ht1 : t < 1) (hnu : 0 ≤ nu) (hsum : nu + t ≤ 1)
    (hnum : 0 ≤ (eta ((1 - 2 * p) * t) - eta t) * eta ((1 - 2 * p) * t) - l ^ 2) :
    ((eta ((1 - 2 * p) * t) - eta t) * eta ((1 - 2 * p) * t) - l ^ 2) / eta ((1 - 2 * p) * t)
      ≤ (pairEntropy nu ((1 - 2 * p) * t) - pairEntropy nu t)
        + pairEntropy nu ((1 - 2 * p) * t) * d ^ 2 - 2 * l * d := by
  set r : ℝ := (1 - 2 * p) * t with hrdef
  have hr0 : 0 ≤ r := by
    rw [hrdef]; exact mul_nonneg (by linarith) (le_of_lt ht0)
  have hrt : r < t := by nlinarith
  have hnur : nu + r < 1 := by nlinarith
  have hpc := product_centering p nu t hp0 hp1 hnu (le_of_lt ht0) hsum
  have hM : 0 < pairEntropy nu r :=
    pairEntropy_pos (by linarith) hnur (by linarith) (by linarith)
  have hMM0 : pairEntropy nu r ≤ eta r := pairEntropy_le_eta hnu hr0 (by linarith)
  exact transfer_relative_alg hpc.2 hM hMM0 hnum d

end CK
