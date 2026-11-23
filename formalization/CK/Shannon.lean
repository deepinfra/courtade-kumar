import CK.Entropy
import CK.FiniteProbability
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Deriv

/-!
# Finite Shannon information and the Shannon--Tsallis comparisons

The quadratic lower bound on information is obtained by strong concavity of
binary entropy. This proves the probabilistic comparison directly, without
assuming a binary-divergence bound as an axiom.
-/

noncomputable section
namespace CourtadeKumar
open scoped BigOperators

def entropyCurvatureCorrection (x : ℝ) : ℝ := Real.binEntropy x + 2 * x ^ 2

theorem entropyCurvatureCorrection_deriv {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt entropyCurvatureCorrection
      (Real.log (1 - x) - Real.log x + 4 * x) x := by
  have h := (Real.hasDerivAt_binEntropy hx0.ne' hx1.ne).add
    (((hasDerivAt_id x).pow 2).const_mul 2)
  convert h using 1
  simp [entropyCurvatureCorrection]
  ring

theorem entropyCurvatureCorrection_second {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y : ℝ => Real.log (1 - y) - Real.log y + 4 * y)
      (4 - 1 / (1 - x) - 1 / x) x := by
  have h1 := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).log
    (by linarith : 1 - x ≠ 0)
  have h2 := Real.hasDerivAt_log hx0.ne'
  have h := (h1.sub h2).add ((hasDerivAt_id x).const_mul 4)
  convert h using 1
  simp only [id_eq]
  ring

/-- Binary entropy is strongly concave, with curvature at most `-4` in nats. -/
theorem entropyCurvatureCorrection_concave :
    ConcaveOn ℝ (Set.Icc 0 1) entropyCurvatureCorrection := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (0 : ℝ) 1)
    (f' := fun x => Real.log (1 - x) - Real.log x + 4 * x)
    (f'' := fun x => 4 - 1 / (1 - x) - 1 / x)
  · unfold entropyCurvatureCorrection
    fun_prop
  · intro x hx
    rw [interior_Icc] at hx
    exact (entropyCurvatureCorrection_deriv hx.1 hx.2).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (entropyCurvatureCorrection_second hx.1 hx.2).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 := hx.1
    have hx1 := hx.2
    have hpos : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
    have heq : 4 - 1 / (1 - x) - 1 / x =
        -(2 * x - 1) ^ 2 / (x * (1 - x)) := by
      field_simp [hx0.ne', ne_of_gt (sub_pos.mpr hx1)]
      ring
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hpos.le

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

/-- Jensen gap of binary Shannon entropy for a random conditional mean. -/
def shannonGap (μ : FiniteLaw Ω) (c : Ω → ℝ) : ℝ :=
  entropyBits (μ.expect c) - μ.expect (fun ω => entropyBits (c ω))

theorem expect_div_const (μ : FiniteLaw Ω) (f : Ω → ℝ) (r : ℝ) :
    μ.expect (fun ω => f ω / r) = μ.expect f / r := by
  simp [expect, div_eq_mul_inv, Finset.sum_mul, mul_assoc]

theorem expect_binEntropy (μ : FiniteLaw Ω) (c : Ω → ℝ) :
    μ.expect (fun ω => Real.binEntropy (c ω)) =
      Real.log 2 * μ.expect (fun ω => entropyBits (c ω)) := by
  simp only [entropyBits, expect_div_const]
  field_simp [ne_of_gt log_two_pos]

theorem shannonGap_nonneg (μ : FiniteLaw Ω) (c : Ω → ℝ)
    (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) : 0 ≤ μ.shannonGap c := by
  have h := Real.strictConcave_binEntropy.concaveOn.le_map_sum
    (t := Finset.univ) (w := μ.mass) (p := c)
    (fun ω _ => μ.mass_nonneg ω) μ.mass_sum (fun ω _ => ⟨hc0 ω, hc1 ω⟩)
  simp only [smul_eq_mul] at h
  change μ.expect (fun ω => Real.binEntropy (c ω)) ≤ Real.binEntropy (μ.expect c) at h
  unfold shannonGap entropyBits
  rw [expect_div_const]
  exact sub_nonneg.mpr (div_le_div_of_nonneg_right h log_two_pos.le)

/-- Pinsker comparison in the normalization of Lemma `tsallis-properties` (iii). -/
theorem quadratic_gap_le_shannonGap (μ : FiniteLaw Ω) (c : Ω → ℝ)
    (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    quadraticEntropy (μ.expect c) - μ.expect (fun ω => quadraticEntropy (c ω)) ≤
      2 * Real.log 2 * μ.shannonGap c := by
  have h := entropyCurvatureCorrection_concave.le_map_sum
    (t := Finset.univ) (w := μ.mass) (p := c)
    (fun ω _ => μ.mass_nonneg ω) μ.mass_sum (fun ω _ => ⟨hc0 ω, hc1 ω⟩)
  simp only [smul_eq_mul] at h
  change μ.expect (fun ω => entropyCurvatureCorrection (c ω)) ≤
    entropyCurvatureCorrection (μ.expect c) at h
  unfold entropyCurvatureCorrection at h
  rw [expect_add, expect_const_mul, expect_binEntropy] at h
  have he : Real.binEntropy (μ.expect c) = Real.log 2 * entropyBits (μ.expect c) := by
    unfold entropyBits
    field_simp [ne_of_gt log_two_pos]
  rw [he] at h
  rw [quadratic_gap, variance_identity]
  unfold shannonGap
  nlinarith

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

def conditionalShannonEntropy (μ : FiniteLaw Ω) (z : Ω → Z) (c : Ω → ℝ) : ℝ :=
  (μ.map z).expect (fun a => entropyBits (μ.conditionalMean z c a))

def shannonInformation (μ : FiniteLaw Ω) (c : Ω → ℝ) (z : Ω → Z) : ℝ :=
  entropyBits (μ.expect c) - μ.conditionalShannonEntropy z c

theorem conditional_entropy_sandwich (μ : FiniteLaw Ω) (z : Ω → Z) (c : Ω → ℝ)
    (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    μ.conditionalQuadraticEntropy z c ≤ μ.conditionalShannonEntropy z c ∧
    μ.conditionalShannonEntropy z c ≤ (1 + μ.conditionalQuadraticEntropy z c) / 2 := by
  have hc0' := μ.conditionalMean_nonneg z hc0
  have hc1' := μ.conditionalMean_le_one z hc1
  constructor
  · exact (μ.map z).expect_mono (fun a => quadratic_le_entropyBits (hc0' a) (hc1' a))
  · have h := (μ.map z).expect_mono
      (fun a => entropyBits_le_quadratic_upper (hc0' a) (hc1' a))
    simpa [conditionalShannonEntropy, conditionalQuadraticEntropy, quadraticEntropy,
      expect_div_const, expect_add] using h

theorem shannonInformation_nonneg (μ : FiniteLaw Ω) (z : Ω → Z) (c : Ω → ℝ)
    (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    0 ≤ μ.shannonInformation c z := by
  have h := (μ.map z).shannonGap_nonneg (μ.conditionalMean z c)
    (μ.conditionalMean_nonneg z hc0) (μ.conditionalMean_le_one z hc1)
  simpa [shannonGap, shannonInformation, conditionalShannonEntropy,
    μ.total_expectation z hc0 hc1] using h

theorem quadraticInformation_le_shannonInformation (μ : FiniteLaw Ω)
    (z : Ω → Z) (c : Ω → ℝ)
    (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    μ.quadraticInformation c z ≤ 2 * Real.log 2 * μ.shannonInformation c z := by
  have h := (μ.map z).quadratic_gap_le_shannonGap (μ.conditionalMean z c)
    (μ.conditionalMean_nonneg z hc0) (μ.conditionalMean_le_one z hc1)
  simpa [shannonGap, shannonInformation, quadraticInformation,
    conditionalShannonEntropy, conditionalQuadraticEntropy,
    μ.total_expectation z hc0 hc1] using h

/-- The reverse comparison applies to an unbiased first bit. -/
theorem shannonInformation_le_quadraticInformation_of_unbiased
    (μ : FiniteLaw Ω) (z : Ω → Z) (c : Ω → ℝ)
    (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1)
    (hmean : μ.expect c = 1 / 2) :
    μ.shannonInformation c z ≤ μ.quadraticInformation c z := by
  have h := (μ.conditional_entropy_sandwich z c hc0 hc1).1
  unfold shannonInformation quadraticInformation
  rw [hmean, entropyBits_half]
  norm_num [quadraticEntropy]
  linarith

end FiniteLaw
end CourtadeKumar
