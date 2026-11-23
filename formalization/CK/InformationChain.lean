import CK.Conditioning
import CK.Shannon

/-!
# Finite posterior mixtures and the conditioning gain

Conditional laws are represented as an explicit finite mixture.  Posterior
mixtures after an observation are genuine normalized probability laws.  This
lets strong concavity prove the Shannon conditioning gain without taking a
chain rule or the target inequality as an additional premise.
-/

noncomputable section
namespace CourtadeKumar
namespace FiniteLaw

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- Reweight a finite law by a nonnegative likelihood of positive expectation. -/
def reweight (μ : FiniteLaw Ω) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hpos : 0 < μ.expect w) : FiniteLaw Ω where
  mass ω := μ.mass ω * w ω / μ.expect w
  mass_nonneg ω := div_nonneg (mul_nonneg (μ.mass_nonneg ω) (hw ω)) hpos.le
  mass_sum := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ hpos.ne'

theorem expect_reweight (μ : FiniteLaw Ω) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hpos : 0 < μ.expect w) (f : Ω → ℝ) :
    (μ.reweight w hw hpos).expect f = μ.expect (fun ω => w ω * f ω) / μ.expect w := by
  change (∑ ω, (μ.mass ω * w ω / μ.expect w) * f ω) =
    (∑ ω, μ.mass ω * (w ω * f ω)) / μ.expect w
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expect_mul_reweight (μ : FiniteLaw Ω) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hpos : 0 < μ.expect w) (f : Ω → ℝ) :
    μ.expect w * (μ.reweight w hw hpos).expect f = μ.expect (fun ω => w ω * f ω) := by
  rw [μ.expect_reweight w hw hpos f]
  field_simp [hpos.ne']

/-- A zero-likelihood event has zero weighted contribution for every integrand. -/
theorem expect_mul_eq_zero_of_expect_eq_zero (μ : FiniteLaw Ω) (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hz : μ.expect w = 0) (f : Ω → ℝ) :
    μ.expect (fun ω => w ω * f ω) = 0 := by
  have hm : ∀ ω, μ.mass ω * w ω = 0 := by
    intro ω
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun ω _ => mul_nonneg (μ.mass_nonneg ω) (hw ω))).1 hz ω (Finset.mem_univ ω)
  unfold expect
  apply Finset.sum_eq_zero
  intro ω _
  rw [← mul_assoc, hm ω, zero_mul]

theorem expect_sum {A : Type*} [Fintype A] (μ : FiniteLaw Ω) (f : Ω → A → ℝ) :
    μ.expect (fun ω => ∑ a, f ω a) = ∑ a, μ.expect (fun ω => f ω a) := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]

variable {Z : Type*} [DecidableEq Z]

theorem fibreMass_eq_expect (μ : FiniteLaw Ω) (z : Ω → Z) (a : Z) :
    μ.fibreMass z a = μ.expect (fun ω => if z ω = a then 1 else 0) := by
  simp [fibreMass, expect, mul_ite]

theorem fibreMoment_eq_expect (μ : FiniteLaw Ω) (z : Ω → Z) (c : Ω → ℝ) (a : Z) :
    μ.fibreMoment z c a = μ.expect (fun ω => if z ω = a then c ω else 0) := by
  simp [fibreMoment, expect, mul_ite]

variable {U : Type*} [Fintype U]

theorem mixture_fibreMass (ν : FiniteLaw U) (μ : U → FiniteLaw Ω)
    (z : Ω → Z) (a : Z) :
    (ν.mixture μ).fibreMass z a = ν.expect (fun u => (μ u).fibreMass z a) := by
  rw [fibreMass_eq_expect, ν.expect_mixture μ]
  congr 1
  funext u
  exact ((μ u).fibreMass_eq_expect z a).symm

theorem mixture_fibreMoment (ν : FiniteLaw U) (μ : U → FiniteLaw Ω)
    (z : Ω → Z) (c : Ω → ℝ) (a : Z) :
    (ν.mixture μ).fibreMoment z c a = ν.expect (fun u => (μ u).fibreMoment z c a) := by
  rw [fibreMoment_eq_expect, ν.expect_mixture μ]
  congr 1
  funext u
  exact ((μ u).fibreMoment_eq_expect z c a).symm

/-- The conditional mean under a mixture is the mean under the posterior mixture. -/
theorem posterior_mixture_mean (ν : FiniteLaw U) (μ : U → FiniteLaw Ω)
    (z : Ω → Z) (c : Ω → ℝ) (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1)
    (a : Z) (hpos : 0 < ν.expect (fun u => (μ u).fibreMass z a)) :
    (ν.reweight (fun u => (μ u).fibreMass z a)
      (fun u => (μ u).fibreMass_nonneg z a) hpos).expect
        (fun u => (μ u).conditionalMean z c a) =
      (ν.mixture μ).conditionalMean z c a := by
  rw [ν.expect_reweight]
  simp_rw [(μ _).mass_mul_conditionalMean z hc0 hc1 a]
  unfold conditionalMean
  rw [ν.mixture_fibreMoment, ν.mixture_fibreMass]

/-- Strong entropy concavity on one observed fibre, including zero-mass fibres. -/
theorem fibre_mixture_gap_comparison (ν : FiniteLaw U) (μ : U → FiniteLaw Ω)
    (z : Ω → Z) (c : Ω → ℝ) (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1)
    (a : Z) :
    (ν.mixture μ).fibreMass z a * quadraticEntropy ((ν.mixture μ).conditionalMean z c a) -
        ν.expect (fun u => (μ u).fibreMass z a * quadraticEntropy ((μ u).conditionalMean z c a)) ≤
      2 * Real.log 2 *
        ((ν.mixture μ).fibreMass z a * entropyBits ((ν.mixture μ).conditionalMean z c a) -
          ν.expect (fun u => (μ u).fibreMass z a * entropyBits ((μ u).conditionalMean z c a))) := by
  let w : U → ℝ := fun u => (μ u).fibreMass z a
  let p : U → ℝ := fun u => (μ u).conditionalMean z c a
  have hw : ∀ u, 0 ≤ w u := fun u => (μ u).fibreMass_nonneg z a
  have hm : (ν.mixture μ).fibreMass z a = ν.expect w := ν.mixture_fibreMass μ z a
  by_cases hz : ν.expect w = 0
  · have hQ := ν.expect_mul_eq_zero_of_expect_eq_zero w hw hz (fun u => quadraticEntropy (p u))
    have hH := ν.expect_mul_eq_zero_of_expect_eq_zero w hw hz (fun u => entropyBits (p u))
    simp_rw [hm]
    change ν.expect w * quadraticEntropy ((ν.mixture μ).conditionalMean z c a) -
        ν.expect (fun u => w u * quadraticEntropy (p u)) ≤
      2 * Real.log 2 * (ν.expect w * entropyBits ((ν.mixture μ).conditionalMean z c a) -
        ν.expect (fun u => w u * entropyBits (p u)))
    rw [hz, hQ, hH]
    norm_num
  · have hpos : 0 < ν.expect w := lt_of_le_of_ne (ν.expect_nonneg hw) (Ne.symm hz)
    let κ := ν.reweight w hw hpos
    have hmean : κ.expect p = (ν.mixture μ).conditionalMean z c a :=
      ν.posterior_mixture_mean μ z c hc0 hc1 a hpos
    have hQ : (ν.mixture μ).fibreMass z a * κ.expect (fun u => quadraticEntropy (p u)) =
        ν.expect (fun u => w u * quadraticEntropy (p u)) := by
      rw [hm]
      exact ν.expect_mul_reweight w hw hpos _
    have hH : (ν.mixture μ).fibreMass z a * κ.expect (fun u => entropyBits (p u)) =
        ν.expect (fun u => w u * entropyBits (p u)) := by
      rw [hm]
      exact ν.expect_mul_reweight w hw hpos _
    have hj := κ.quadratic_gap_le_shannonGap p
      (fun u => (μ u).conditionalMean_nonneg z hc0 a)
      (fun u => (μ u).conditionalMean_le_one z hc1 a)
    calc
      _ = (ν.mixture μ).fibreMass z a *
          (quadraticEntropy (κ.expect p) - κ.expect (fun u => quadraticEntropy (p u))) := by
            rw [hmean]
            rw [mul_sub, hQ]
      _ ≤ (ν.mixture μ).fibreMass z a * (2 * Real.log 2 * κ.shannonGap p) :=
        mul_le_mul_of_nonneg_left hj ((ν.mixture μ).fibreMass_nonneg z a)
      _ = _ := by
        unfold shannonGap
        rw [hmean]
        rw [← hH]
        ring

variable [Fintype Z]

/-- Strong-concavity comparison after averaging all observed fibres. -/
theorem conditional_mixture_gap_comparison (ν : FiniteLaw U) (μ : U → FiniteLaw Ω)
    (z : Ω → Z) (c : Ω → ℝ) (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    (ν.mixture μ).conditionalQuadraticEntropy z c -
        ν.expect (fun u => (μ u).conditionalQuadraticEntropy z c) ≤
      2 * Real.log 2 * ((ν.mixture μ).conditionalShannonEntropy z c -
        ν.expect (fun u => (μ u).conditionalShannonEntropy z c)) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun a _ => ν.fibre_mixture_gap_comparison μ z c hc0 hc1 a)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← expect_sum] at h
  exact h

theorem shannonInformation_mixture_gap (ν : FiniteLaw U) (μ : U → FiniteLaw Ω)
    (z : Ω → Z) (c : Ω → ℝ) (β : ℝ)
    (hcmean : ∀ u, (μ u).expect c = β) :
    ν.expect (fun u => (μ u).shannonInformation c z) - (ν.mixture μ).shannonInformation c z =
      (ν.mixture μ).conditionalShannonEntropy z c -
        ν.expect (fun u => (μ u).conditionalShannonEntropy z c) := by
  have hm : (ν.mixture μ).expect c = β := by
    rw [ν.expect_mixture μ]
    simp_rw [hcmean]
    exact ν.expect_const β
  unfold shannonInformation
  simp_rw [hcmean, hm]
  rw [ν.expect_sub, ν.expect_const]
  ring

theorem quadraticInformation_mixture_gap (ν : FiniteLaw U) (μ : U → FiniteLaw Ω)
    (z : Ω → Z) (c : Ω → ℝ) (β : ℝ)
    (hcmean : ∀ u, (μ u).expect c = β) :
    ν.expect (fun u => (μ u).quadraticInformation c z) - (ν.mixture μ).quadraticInformation c z =
      (ν.mixture μ).conditionalQuadraticEntropy z c -
        ν.expect (fun u => (μ u).conditionalQuadraticEntropy z c) := by
  have hm : (ν.mixture μ).expect c = β := by
    rw [ν.expect_mixture μ]
    simp_rw [hcmean]
    exact ν.expect_const β
  unfold quadraticInformation
  simp_rw [hcmean, hm]
  rw [ν.expect_sub, ν.expect_const]
  ring

/-- Pinsker comparison for the increase of information after exposing a mixture index.
The unchanged first-bit mean is the required independence condition. -/
theorem information_mixture_gain_comparison (ν : FiniteLaw U) (μ : U → FiniteLaw Ω)
    (z : Ω → Z) (c : Ω → ℝ) (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1)
    (β : ℝ) (hcmean : ∀ u, (μ u).expect c = β) :
    ν.expect (fun u => (μ u).quadraticInformation c z) - (ν.mixture μ).quadraticInformation c z ≤
      2 * Real.log 2 * (ν.expect (fun u => (μ u).shannonInformation c z) -
        (ν.mixture μ).shannonInformation c z) := by
  rw [ν.quadraticInformation_mixture_gap μ z c β hcmean,
    ν.shannonInformation_mixture_gap μ z c β hcmean]
  exact ν.conditional_mixture_gap_comparison μ z c hc0 hc1

theorem mixture_quadratic_entropy_le (ν : FiniteLaw U) (μ : U → FiniteLaw Ω)
    (c : Ω → ℝ) :
    ν.expect (fun u => quadraticEntropy ((μ u).expect c)) ≤
      quadraticEntropy ((ν.mixture μ).expect c) := by
  rw [ν.expect_mixture μ]
  exact ν.quadratic_jensen (fun u => (μ u).expect c)

private theorem conditioning_gain_algebra (A D b V v K G : ℝ)
    (hV : 0 < V) (hv : 0 < v) (hK : 0 < K)
    (hcov : V * D = b) (hcond : b ≤ A * v) (hpin : A - D ≤ K * G) :
    b * (V - v) / (K * V * v) ≤ G := by
  apply (div_le_iff₀ (mul_pos (mul_pos hK hV) hv)).2
  have h1 := mul_le_mul_of_nonneg_right hpin (mul_nonneg hV.le hv.le)
  have h2 := mul_le_mul_of_nonneg_right hcond hV.le
  have h3 := congrArg (fun x => x * v) hcov
  nlinarith

/-- Manuscript Lemma `conditioning-gain` for explicit finite conditional laws.

Write `M = ν.mixture μ`, `V = T_M(C)` and `v = E_U T(C | U)`.
The numerator is `T_M(C; B) (V - v)`, and `V - v` is precisely the quadratic
information exposed by the mixture index `U`.  The conclusion is obtained from
actual posterior laws and entropy concavity; no chain identity is a hypothesis.
-/
theorem conditioning_gain (ν : FiniteLaw U) (μ : U → FiniteLaw Ω)
    (b c : Ω → Bool)
    (hb : ∀ u, (μ u).expect (fun ω => bitValue (b ω)) = 1 / 2)
    (hv : 0 < ν.expect (fun u => quadraticEntropy ((μ u).expect (fun ω => bitValue (c ω))))) :
    ν.expect (fun u => (μ u).shannonInformation (fun ω => bitValue (b ω)) c) -
        (ν.mixture μ).shannonInformation (fun ω => bitValue (b ω)) c ≥
      (ν.mixture μ).quadraticInformation (fun ω => bitValue (c ω)) b *
        (quadraticEntropy ((ν.mixture μ).expect (fun ω => bitValue (c ω))) -
          ν.expect (fun u => quadraticEntropy ((μ u).expect (fun ω => bitValue (c ω))))) /
        (2 * Real.log 2 * quadraticEntropy ((ν.mixture μ).expect (fun ω => bitValue (c ω))) *
          ν.expect (fun u => quadraticEntropy ((μ u).expect (fun ω => bitValue (c ω))))) := by
  have hmean : (ν.mixture μ).expect (fun ω => bitValue (b ω)) = 1 / 2 := by
    rw [ν.expect_mixture μ]
    simp_rw [hb]
    exact ν.expect_const (1 / 2)
  have hT : quadraticEntropy ((ν.mixture μ).expect (fun ω => bitValue (b ω))) = 1 := by
    rw [hmean]
    norm_num [quadraticEntropy]
  have hV := ν.mixture_quadratic_entropy_le μ (fun ω => bitValue (c ω))
  have hVpos : 0 < quadraticEntropy ((ν.mixture μ).expect (fun ω => bitValue (c ω))) :=
    lt_of_lt_of_le hv hV
  have hcov := (ν.mixture μ).binary_quadratic_symmetry b c
  rw [hT, one_mul] at hcov
  have hcond := ν.quadratic_conditioning μ b c (1 / 2) hb
  rw [hT, one_mul] at hcond
  have hpin := ν.information_mixture_gain_comparison μ c (fun ω => bitValue (b ω))
    (fun ω => bitValue_nonneg (b ω)) (fun ω => bitValue_le_one (b ω)) (1 / 2) hb
  exact conditioning_gain_algebra _ _ _ _ _ _ _ hVpos hv
    (mul_pos (by norm_num) log_two_pos) hcov hcond hpin

end FiniteLaw
end CourtadeKumar
