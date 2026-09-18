import CK.SmallGap
import CK.AvgLemmas
import CK.Induction

/-!
# Proposition 2.4 in the Boolean model, conditional on the scalar lemma

`lowNoiseProfile_of_scalar` : `ScalarMixingClaim → LowNoiseProfileClaim`.
The scalar two-posterior inequality (Lemma 2.1) is taken as a hypothesis;
everything else (sectioning, small-gap coordinate, relabelling, averaging,
base cases, the induction itself) is proved here.
-/
noncomputable section
namespace CK
open scoped BigOperators
open Finset

theorem avg_linear3 {n : ℕ} (a b c : ℝ) (u v w : Cube n → ℝ) :
    avg (fun x => a * u x + b * v x + c * w x) = a * avg u + b * avg v + c * avg w := by
  unfold avg
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

/-- Base case `n = 0`: a constant function has zero variance profile. -/
theorem profile_zero (f : BooleanFunction 0) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    varianceProfile (mean f) * binaryEntropy p ≤ conditionalEntropy f p := by
  have hV : varianceProfile (mean f) = 0 := by
    rw [mean_zero]; unfold varianceProfile indicator; cases f default <;> simp
  rw [hV, zero_mul]
  exact conditionalEntropy_nonneg f p hp0 hp1

theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  unfold binaryEntropy; simp

theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  unfold binaryEntropy; simp

/-- Base case `n = 1`: constants give `0 ≤ H`, the two coordinate functions give `h(p) = H`. -/
theorem profile_one (f : BooleanFunction 1) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    varianceProfile (mean f) * binaryEntropy p ≤ conditionalEntropy f p := by
  have hH := conditionalEntropy_snoc (n := 0) f p
  have hm := mean_snoc (n := 0) f
  rw [hH, avg_of_unique, hm, mean_zero, mean_zero, posterior_zero, posterior_zero]
  have hnn := binaryEntropy_nonneg' hp0 hp1
  unfold varianceProfile indicator
  rcases sectionLast f true default with _ | _ <;> rcases sectionLast f false default with _ | _
  · simp [binaryEntropy_zero]
  · norm_num [binaryEntropy_symm]
  · norm_num [binaryEntropy_symm]
  · simp [binaryEntropy_one]

/-- The induction step, given the scalar lemma: the data required by
`abstract_profile_induction`. -/
theorem profile_step_of_scalar (hS : ScalarMixingClaim) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1 / 20)
    (n : ℕ) (f : BooleanFunction (n + 2)) :
    ∃ (f0 f1 : BooleanFunction (n + 1)) (d e J : ℝ),
      0 ≤ d ∧ d ≤ 1 / 2 ∧ d ≤ e ∧
      (varianceProfile (mean f0) + varianceProfile (mean f1)) / 2 =
        varianceProfile (mean f) - d ^ 2 ∧
      (conditionalEntropy f0 p + conditionalEntropy f1 p) / 2 ≤ J ∧
      J + 2 * d * binaryEntropy p * e ≤ (1 + d ^ 2) * conditionalEntropy f p := by
  obtain ⟨σ, hσ⟩ := exists_small_gap f
  have hp01 : p ≤ 1 := by linarith
  have hd0 : 0 ≤ gapLast (relabel σ f) := abs_nonneg _
  refine ⟨sectionLast (relabel σ f) true, sectionLast (relabel σ f) false, gapLast (relabel σ f),
    avg (fun w => |posterior (sectionLast (relabel σ f) true) p w -
                   posterior (sectionLast (relabel σ f) false) p w|),
    (conditionalEntropy (sectionLast (relabel σ f) true) p +
      conditionalEntropy (sectionLast (relabel σ f) false) p) / 2,
    hd0, hσ, ?_, ?_, le_refl _, ?_⟩
  · unfold gapLast
    rw [← posterior_mean (sectionLast (relabel σ f) true) p,
      ← posterior_mean (sectionLast (relabel σ f) false) p, ← avg_sub]
    exact abs_avg_le_avg_abs _
  · rw [← mean_relabel σ f, mean_snoc (relabel σ f), Algebra.variance_restriction]
    unfold gapLast
    rw [sq_abs]
    ring
  · rw [← conditionalEntropy_relabel σ f p, conditionalEntropy_snoc (relabel σ f) p]
    have key : ∀ w : Cube (n + 1),
        (1 / 2 : ℝ) * binaryEntropy (posterior (sectionLast (relabel σ f) true) p w)
          + (1 / 2 : ℝ) * binaryEntropy (posterior (sectionLast (relabel σ f) false) p w)
          + (2 * gapLast (relabel σ f) * binaryEntropy p) *
              |posterior (sectionLast (relabel σ f) true) p w -
               posterior (sectionLast (relabel σ f) false) p w|
        ≤ (1 + gapLast (relabel σ f) ^ 2) *
            ((binaryEntropy ((1 - p) * posterior (sectionLast (relabel σ f) true) p w
                + p * posterior (sectionLast (relabel σ f) false) p w)
              + binaryEntropy ((1 - p) * posterior (sectionLast (relabel σ f) false) p w
                + p * posterior (sectionLast (relabel σ f) true) p w)) / 2) := by
      intro w
      have h := hS p (posterior (sectionLast (relabel σ f) true) p w)
        (posterior (sectionLast (relabel σ f) false) p w) (gapLast (relabel σ f)) hp0 hp1
        (posterior_nonneg _ p hp0.le hp01 w) (posterior_le_one _ p hp0.le hp01 w)
        (posterior_nonneg _ p hp0.le hp01 w) (posterior_le_one _ p hp0.le hp01 w) hd0 hσ
      unfold scalarSlack mixedEntropy at h
      have hsq : 0 ≤ p ^ 2 / 25 * (posterior (sectionLast (relabel σ f) true) p w -
          posterior (sectionLast (relabel σ f) false) p w) ^ 2 := by positivity
      have hc : p * posterior (sectionLast (relabel σ f) true) p w
          + (1 - p) * posterior (sectionLast (relabel σ f) false) p w
          = (1 - p) * posterior (sectionLast (relabel σ f) false) p w
          + p * posterior (sectionLast (relabel σ f) true) p w := by ring
      rw [hc] at h
      linarith
    have hav := avg_le_avg key
    rw [avg_linear3, avg_const_mul] at hav
    unfold conditionalEntropy
    linarith

/-- Proposition 2.4, conditional on Lemma 2.1: the variance profile bound for all
`n`, all Boolean `f`, and all `0 ≤ p ≤ 1/20`. -/
theorem lowNoiseProfile_of_scalar (hS : ScalarMixingClaim) : LowNoiseProfileClaim := by
  intro n f p hp0 hp1
  rcases eq_or_lt_of_le hp0 with hp | hp
  · rw [← hp, binaryEntropy_zero, mul_zero]
    exact conditionalEntropy_nonneg f 0 le_rfl (by norm_num)
  · exact abstract_profile_induction (fun k => BooleanFunction k)
      (fun k g => varianceProfile (mean g)) (fun k g => conditionalEntropy g p)
      (binaryEntropy p) (binaryEntropy_nonneg' hp0 (by linarith))
      (fun k g => (Algebra.variance_range _ (mean_nonneg g) (mean_le_one g)).2)
      (fun g => profile_zero g p hp0 (by linarith))
      (fun g => profile_one g p hp0 (by linarith))
      (fun k g => profile_step_of_scalar hS p hp hp1 k g) n f

end CK
