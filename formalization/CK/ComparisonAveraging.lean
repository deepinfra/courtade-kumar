import CK.ComparisonConcavity
import CK.ProfileSeries
import CK.InformationChain

/-! Finite conditional comparison, with zero conditional variance allowed. -/

noncomputable section
namespace CourtadeKumar
open scoped BigOperators

namespace Spec

@[simp] theorem binaryProfile_zero_correlation (x : ℝ) : binaryProfile x 0 = 0 := by
  simp [binaryProfile]

theorem binaryProfile_closed_domain {x d : ℝ} (hxd : |x| + |d| ≤ 1) :
    0 ≤ 1 - x ^ 2 ∧ 0 ≤ binaryProfile x d ∧
      binaryProfile x d ≤ 1 - x ^ 2 ∧ |d| ≤ 1 - x ^ 2 ∧
      (1 - x ^ 2) * divergence (d / (1 - x ^ 2)) ≤ binaryProfile x d := by
  have hx : |x| ≤ 1 := by linarith [abs_nonneg d]
  have hd : |d| ≤ 1 - x ^ 2 := by
    have hm := mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hx)
    nlinarith [sq_abs x]
  rcases lt_or_eq_of_le hx with hx | hx
  · exact ⟨(binaryProfile_domain hx hxd).1.le,
      binaryProfile_nonneg hx, binaryProfile_le_variance hx hxd, hd,
      binaryProfile_lower hx hxd⟩
  · have hd0 : d = 0 := abs_eq_zero.mp (by linarith [abs_nonneg d])
    have hx2 : x ^ 2 = 1 := by nlinarith [sq_abs x]
    simp [hd0, hx2]

theorem binaryProfile_comparisonMap_bound {ρ x d : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hxd : |x| + |d| ≤ 1) :
    binaryProfile x (ρ * d) ≤ (1 - x ^ 2) *
      comparisonMap ρ (binaryProfile x d / (1 - x ^ 2)) := by
  have hx : |x| ≤ 1 := by linarith [abs_nonneg d]
  rcases lt_or_eq_of_le hx with hx | hx
  · have hV := (binaryProfile_domain hx hxd).1
    have hr : binaryProfile x d / (1 - x ^ 2) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (binaryProfile_nonneg hx) hV.le,
        (div_le_one hV).mpr (binaryProfile_le_variance hx hxd)⟩
    have hs := matchingParameter_spec hr
    exact binaryProfile_matched_domination hρ0 hρ1 hx hxd hs.1 hs.2
  · have hd0 : d = 0 := abs_eq_zero.mp (by linarith [abs_nonneg d])
    have hx2 : x ^ 2 = 1 := by nlinarith [sq_abs x]
    simp [hd0, hx2]

theorem divergence_convex : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) divergence := by
  refine ⟨convex_Icc (-1) 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hmx : (1 + x) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hmy : (1 + y) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have h := Real.strictConcave_binEntropy.concaveOn.2 hmx hmy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have he : (1 + (a * x + b * y)) / 2 = a * ((1 + x) / 2) + b * ((1 + y) / 2) := by
    nlinarith
  have hh := div_le_div_of_nonneg_right h log_two_pos.le
  unfold divergence entropy
  rw [he]
  rw [add_div, mul_div_assoc, mul_div_assoc] at hh
  nlinarith

end Spec

namespace FiniteLaw
variable {U : Type*} [Fintype U]

theorem concave_jensen (μ : FiniteLaw U) {f : ℝ → ℝ} {s : Set ℝ}
    (hf : ConcaveOn ℝ s f) (r : U → ℝ) (hr : ∀ u, r u ∈ s) :
    μ.expect (fun u => f (r u)) ≤ f (μ.expect r) := by
  exact hf.le_map_sum (t := Finset.univ) (w := μ.mass) (p := r)
    (fun u _ => μ.mass_nonneg u) μ.mass_sum (fun u _ => hr u)

theorem convex_jensen (μ : FiniteLaw U) {f : ℝ → ℝ} {s : Set ℝ}
    (hf : ConvexOn ℝ s f) (r : U → ℝ) (hr : ∀ u, r u ∈ s) :
    f (μ.expect r) ≤ μ.expect (fun u => f (r u)) := by
  exact hf.map_sum_le (t := Finset.univ) (w := μ.mass) (p := r)
    (fun u _ => μ.mass_nonneg u) μ.mass_sum (fun u _ => hr u)

/-- Weighted Jensen with the manuscript's entropy weights; zero-weight fibres
are retained, and the quotient there has Lean's total value zero. -/
theorem entropyWeighted_concave_jensen (μ : FiniteLaw U) (v I : U → ℝ)
    (hv : ∀ u, 0 ≤ v u) (hI0 : ∀ u, 0 ≤ I u) (hIv : ∀ u, I u ≤ v u)
    (hV : 0 < μ.expect v) {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f) :
    μ.expect (fun u => v u * f (I u / v u)) ≤
      μ.expect v * f (μ.expect I / μ.expect v) := by
  let ν := μ.reweight v hv hV
  have hr (u : U) : I u / v u ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (hI0 u) (hv u), ?_⟩
    by_cases hz : v u = 0
    · simp [hz]
    · exact (div_le_one (lt_of_le_of_ne (hv u) (Ne.symm hz))).mpr (hIv u)
  have hcancel (u : U) : v u * (I u / v u) = I u := by
    by_cases hz : v u = 0
    · have hIz : I u = 0 := by linarith [hI0 u, hIv u]
      simp [hz, hIz]
    · field_simp [hz]
  have hmean : ν.expect (fun u => I u / v u) = μ.expect I / μ.expect v := by
    rw [expect_reweight]
    simp_rw [hcancel]
  have h := mul_le_mul_of_nonneg_left (ν.concave_jensen hf _ hr) hV.le
  rw [hmean] at h
  change μ.expect v * (μ.reweight v hv hV).expect (fun u => f (I u / v u)) ≤ _ at h
  rw [expect_mul_reweight] at h
  exact h

/-- Signed form of entropy-weighted Jensen, used for the correlation lower bound. -/
theorem entropyWeighted_convex_jensen (μ : FiniteLaw U) (v d : U → ℝ)
    (hv : ∀ u, 0 ≤ v u) (hdv : ∀ u, |d u| ≤ v u)
    (hV : 0 < μ.expect v) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) f) :
    μ.expect v * f (μ.expect d / μ.expect v) ≤
      μ.expect (fun u => v u * f (d u / v u)) := by
  let ν := μ.reweight v hv hV
  have hr (u : U) : d u / v u ∈ Set.Icc (-1 : ℝ) 1 := by
    apply abs_le.mp
    rw [abs_div, abs_of_nonneg (hv u)]
    by_cases hz : v u = 0
    · simp [hz]
    · exact (div_le_one (lt_of_le_of_ne (hv u) (Ne.symm hz))).mpr (hdv u)
  have hcancel (u : U) : v u * (d u / v u) = d u := by
    by_cases hz : v u = 0
    · have hdz : d u = 0 := abs_eq_zero.mp (by linarith [hdv u, abs_nonneg (d u)])
      simp [hz, hdz]
    · field_simp [hz]
  have hmean : ν.expect (fun u => d u / v u) = μ.expect d / μ.expect v := by
    rw [expect_reweight]
    simp_rw [hcancel]
  have h := mul_le_mul_of_nonneg_left (ν.convex_jensen hf _ hr) hV.le
  rw [hmean] at h
  change _ ≤ μ.expect v * (μ.reweight v hv hV).expect (fun u => f (d u / v u)) at h
  rw [expect_mul_reweight] at h
  exact h

theorem abs_expect_le_expect (μ : FiniteLaw U) (d v : U → ℝ)
    (hdv : ∀ u, |d u| ≤ v u) : |μ.expect d| ≤ μ.expect v := by
  apply abs_le.mpr
  constructor
  · have h := μ.expect_nonneg (f := fun u => d u + v u)
      (fun u => by
        change 0 ≤ d u + v u
        linarith [(abs_le.mp (hdv u)).1])
    rw [μ.expect_add] at h
    linarith
  · exact μ.expect_mono (fun u => (abs_le.mp (hdv u)).2)

/-- Upper conditional comparison for the actual biased binary profile, including
constant conditional bits. The law `μ` is the law of the conditioning variable. -/
theorem binaryProfile_average_upper (μ : FiniteLaw U) (x d : U → ℝ)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hxd : ∀ u, |x u| + |d u| ≤ 1)
    (hV : 0 < μ.expect (fun u => 1 - x u ^ 2)) :
    μ.expect (fun u => Spec.binaryProfile (x u) (ρ * d u)) ≤
      μ.expect (fun u => 1 - x u ^ 2) * Spec.comparisonMap ρ
        (μ.expect (fun u => Spec.binaryProfile (x u) (d u)) /
          μ.expect (fun u => 1 - x u ^ 2)) := by
  have hf (u : U) := Spec.binaryProfile_closed_domain (hxd u)
  calc
    _ ≤ μ.expect (fun u => (1 - x u ^ 2) * Spec.comparisonMap ρ
        (Spec.binaryProfile (x u) (d u) / (1 - x u ^ 2))) :=
      μ.expect_mono (fun u => Spec.binaryProfile_comparisonMap_bound hρ0 hρ1 (hxd u))
    _ ≤ _ := μ.entropyWeighted_concave_jensen _ _
      (fun u => (hf u).1) (fun u => (hf u).2.1) (fun u => (hf u).2.2.1)
      hV (Spec.comparisonMap_concave hρ0 hρ1)

/-- Lower conditional comparison, with the signed averaged correlation. -/
theorem binaryProfile_average_lower (μ : FiniteLaw U) (x d : U → ℝ)
    (hxd : ∀ u, |x u| + |d u| ≤ 1)
    (hV : 0 < μ.expect (fun u => 1 - x u ^ 2)) :
    μ.expect (fun u => 1 - x u ^ 2) * Spec.divergence
      (μ.expect d / μ.expect (fun u => 1 - x u ^ 2)) ≤
      μ.expect (fun u => Spec.binaryProfile (x u) (d u)) := by
  have hf (u : U) := Spec.binaryProfile_closed_domain (hxd u)
  calc
    _ ≤ μ.expect (fun u => (1 - x u ^ 2) * Spec.divergence (d u / (1 - x u ^ 2))) :=
      μ.entropyWeighted_convex_jensen _ _
        (fun u => (hf u).1) (fun u => (hf u).2.2.2.1) hV Spec.divergence_convex
    _ ≤ _ := μ.expect_mono (fun u => (hf u).2.2.2.2)

/-- Finite-profile forms of manuscript Lemmas `comparison` and
`comparison-correlation`, with a common matching channel and all zero fibres kept. -/
theorem binaryProfile_average_comparison (μ : FiniteLaw U) (x d : U → ℝ)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hxd : ∀ u, |x u| + |d u| ≤ 1)
    (hV : 0 < μ.expect (fun u => 1 - x u ^ 2)) :
    ∃ τ ∈ Set.Icc (0 : ℝ) 1,
      μ.expect (fun u => Spec.binaryProfile (x u) (d u)) =
        μ.expect (fun u => 1 - x u ^ 2) * Spec.divergence τ ∧
      μ.expect (fun u => Spec.binaryProfile (x u) (ρ * d u)) ≤
        μ.expect (fun u => 1 - x u ^ 2) * Spec.divergence (ρ * τ) ∧
      (μ.expect d) ^ 2 / (μ.expect (fun u => 1 - x u ^ 2)) ^ 2 ≤ τ ^ 2 := by
  have hf (u : U) := Spec.binaryProfile_closed_domain (hxd u)
  have hI0 : 0 ≤ μ.expect (fun u => Spec.binaryProfile (x u) (d u)) :=
    μ.expect_nonneg (fun u => (hf u).2.1)
  have hIV : μ.expect (fun u => Spec.binaryProfile (x u) (d u)) ≤
      μ.expect (fun u => 1 - x u ^ 2) :=
    μ.expect_mono (fun u => (hf u).2.2.1)
  obtain ⟨τ, hτ, _⟩ := Spec.existsUnique_matching_parameter
    (div_nonneg hI0 hV.le) ((div_le_one hV).mpr hIV)
  refine ⟨τ, hτ.1, ?_, ?_, ?_⟩
  · rw [hτ.2]
    field_simp [hV.ne']
  · have h := μ.binaryProfile_average_upper x d hρ0 hρ1 hxd hV
    rw [← hτ.2, Spec.comparisonMap_divergence ρ hτ.1] at h
    exact h
  · exact Spec.matched_correlation_bound hV
      (μ.abs_expect_le_expect d _ (fun u => (hf u).2.2.2.1)) hτ.1 hτ.2
      (μ.binaryProfile_average_lower x d hxd hV)

end FiniteLaw
end CourtadeKumar
