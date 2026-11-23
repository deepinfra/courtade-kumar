import CK.Comparison
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace CourtadeKumar.Spec

@[simp] theorem divergence_zero : divergence 0 = 0 := by
  change 1 - entropyBits ((1 + 0) / 2) = 0
  rw [add_zero, entropyBits_half]
  norm_num

@[simp] theorem divergence_one : divergence 1 = 1 := by
  norm_num [divergence, entropy]

@[simp] theorem divergence_even (t : ℝ) : divergence (-t) = divergence t := by
  simp only [divergence_eq_divergenceNats, divergenceNats_even]

theorem divergence_abs (t : ℝ) : divergence |t| = divergence t := by
  rcases le_or_lt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg ht, divergence_even]

theorem continuous_divergence : Continuous divergence := by
  unfold divergence entropy
  fun_prop

theorem divergence_strictMonoOn : StrictMonoOn divergence (Set.Icc 0 1) := by
  intro a ha b hb hab
  have ha' : (1 + a) / 2 ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
    constructor <;> norm_num at * <;> linarith [ha.1, ha.2]
  have hb' : (1 + b) / 2 ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
    constructor <;> norm_num at * <;> linarith [hb.1, hb.2]
  have h := Real.binEntropy_strictAntiOn ha' hb' (by linarith : (1 + a) / 2 < (1 + b) / 2)
  have hd := div_lt_div_of_pos_right h log_two_pos
  unfold divergence entropy
  linarith

/-- A unique unbiased comparison channel realizes every normalized information in `[0,1]`. -/
theorem existsUnique_matching_parameter {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃! t : ℝ, t ∈ Set.Icc 0 1 ∧ divergence t = r := by
  have himage := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    continuous_divergence.continuousOn
  have hr : r ∈ Set.Icc (divergence 0) (divergence 1) := by
    simpa using And.intro hr0 hr1
  rcases himage hr with ⟨t, ht, heq⟩
  refine ⟨t, ⟨ht, heq⟩, ?_⟩
  intro u hu
  exact divergence_strictMonoOn.injOn hu.1 ht (hu.2.trans heq.symm)

/-- The matching part of `comparison-calculus`; domination remains a separate result. -/
theorem exists_pointwise_matching_parameter {x d : ℝ}
    (hx : |x| < 1) (hxd : |x| + |d| ≤ 1) :
    ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧
      binaryProfile x d = (1 - x ^ 2) * divergence t := by
  have hV := (binaryProfile_domain hx hxd).1
  have h0 : 0 ≤ binaryProfile x d / (1 - x ^ 2) :=
    div_nonneg (binaryProfile_nonneg hx) hV.le
  have h1 : binaryProfile x d / (1 - x ^ 2) ≤ 1 :=
    (div_le_one hV).mpr (binaryProfile_le_variance hx hxd)
  rcases existsUnique_matching_parameter h0 h1 with ⟨t, ht, _⟩
  refine ⟨t, ht.1, ?_⟩
  rw [ht.2]
  field_simp [hV.ne']

/-- Correlation comparison after the lower information estimate has been established. -/
theorem matched_correlation_bound {v d t I : ℝ}
    (hv : 0 < v) (hd : |d| ≤ v) (ht : t ∈ Set.Icc 0 1)
    (hmatch : divergence t = I / v)
    (hlower : v * divergence (d / v) ≤ I) :
    d ^ 2 / v ^ 2 ≤ t ^ 2 := by
  have hdv : |d / v| ≤ 1 := by
    rw [abs_div, abs_of_pos hv]
    exact (div_le_one hv).mpr hd
  have hlower' : divergence |d / v| ≤ divergence t := by
    rw [divergence_abs, hmatch]
    exact (le_div_iff₀ hv).mpr (by simpa [mul_comm] using hlower)
  have horder : |d / v| ≤ t := by
    by_contra hn
    have hlt : t < |d / v| := lt_of_not_ge hn
    have h := divergence_strictMonoOn ht ⟨abs_nonneg _, hdv⟩ hlt
    linarith
  have h := mul_self_le_mul_self (abs_nonneg (d / v)) horder
  simpa [← sq, sq_abs, div_pow] using h

end CourtadeKumar.Spec
