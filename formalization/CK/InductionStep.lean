import CK.BinaryProfileSemantics
import CK.GapBounds
import CK.GapAlgebra
import CK.BiasCoefficient
import CK.BiasDivergence

/-! Assembly of the finite-law induction step, with degenerate coordinates kept. -/

noncomputable section
namespace CourtadeKumar
namespace FiniteLaw
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]
variable {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]

theorem shannonInformation_eq_zero_of_quadraticInformation_eq_zero
    (μ : FiniteLaw Ω) (z : Ω → Z) (c : Ω → ℝ)
    (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1)
    (hz : μ.quadraticInformation c z = 0) : μ.shannonInformation c z = 0 := by
  have hfactor := (μ.quadraticInformation_eq_zero_iff z hc0 hc1).mp hz
  have hpost (s : Z) (hs : μ.fibreMass z s ≠ 0) :
      μ.conditionalMean z c s = μ.expect c := by
    unfold conditionalMean
    rw [hfactor s]
    exact mul_div_cancel_left₀ _ hs
  have hH : μ.conditionalShannonEntropy z c = entropyBits (μ.expect c) := by
    calc
      _ = (μ.map z).expect (fun _ => entropyBits (μ.expect c)) := by
        unfold conditionalShannonEntropy expect
        apply Finset.sum_congr rfl
        intro s _
        change μ.fibreMass z s * entropyBits (μ.conditionalMean z c s) =
          μ.fibreMass z s * entropyBits (μ.expect c)
        by_cases hs : μ.fibreMass z s = 0
        · simp [hs]
        · rw [hpost s hs]
      _ = _ := (μ.map z).expect_const _
  unfold shannonInformation
  rw [hH, sub_self]

theorem conditionalShannonInformation_nonneg (μ : FiniteLaw Ω)
    (u : Ω → U) (z : Ω → Z) (c : Ω → ℝ)
    (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    0 ≤ μ.conditionalShannonInformation c z u :=
  (μ.map u).expect_nonneg fun s => (μ.conditionOn u s).shannonInformation_nonneg z c hc0 hc1

theorem progressiveGap_ge_conditional_of_zero_coordinate (μ : FiniteLaw Ω) (p : ℝ)
    (b c : Ω → Bool) (x : Ω → Z)
    (hb : μ.quadraticInformation (fun ω => bitValue (c ω)) b = 0) :
    μ.conditionalProgressiveGap p c x b ≤ μ.progressiveGap p c x := by
  have hSI := μ.shannonInformation_eq_zero_of_quadraticInformation_eq_zero b _
    (fun ω => bitValue_nonneg (c ω)) (fun ω => bitValue_le_one (c ω)) hb
  rw [← μ.shannonInformation_symm b c] at hSI
  have hid := μ.progressiveGap_difference p c b x
  rw [hb, hSI, mul_zero, mul_zero, sub_zero, sub_zero] at hid
  have hnonneg := μ.conditionalShannonInformation_nonneg x b _
    (fun ω => bitValue_nonneg (c ω)) (fun ω => bitValue_le_one (c ω))
  linarith

theorem coordinate_information_zero_of_conditionalEntropy_zero (μ : FiniteLaw Ω)
    (b c : Ω → Bool) (u : Ω → U) (hbu : μ.independentUnbiasedBit b u)
    (hv : μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) = 0) :
    μ.quadraticInformation (fun ω => bitValue (c ω)) b = 0 := by
  have h := (μ.map u).quadratic_conditioning (fun s => μ.conditionOn u s) b c (1 / 2)
    (μ.conditionOn_mean_of_independentUnbiasedBit b u hbu)
  rw [μ.conditionOn_quadraticEntropy_tower, μ.mixture_conditionOn, hv,
    μ.mean_of_independentUnbiasedBit b u hbu] at h
  norm_num [quadraticEntropy] at h
  have hnonneg := μ.quadraticInformation_nonneg b
    (fun ω => bitValue_nonneg (c ω)) (fun ω => bitValue_le_one (c ω))
  linarith

theorem conditionalEntropy_pos_of_coordinate_information_pos (μ : FiniteLaw Ω)
    (b c : Ω → Bool) (u : Ω → U) (hbu : μ.independentUnbiasedBit b u)
    (hb : 0 < μ.quadraticInformation (fun ω => bitValue (c ω)) b) :
    0 < μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) := by
  have hv := μ.conditionalQuadraticEntropy_nonneg u
    (fun ω => bitValue_nonneg (c ω)) (fun ω => bitValue_le_one (c ω))
  apply lt_of_le_of_ne hv
  intro hz
  have h := μ.coordinate_information_zero_of_conditionalEntropy_zero b c u hbu hz.symm
  linarith

end FiniteLaw

namespace Spec

theorem divergence_abs_noise (p : ℝ) :
    divergence |1 - 2 * p| = noiseInformation p := by
  rw [divergence_abs]
  unfold divergence entropy noiseInformation entropyBits
  rw [show (1 + (1 - 2 * p)) / 2 = 1 - p by ring, Real.binEntropy_one_sub]

end Spec

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The actual finite-law induction step. The only analytic prerequisite left
as an argument is the separately stated three-bit theorem. All comparison,
bias, and conditioning estimates are proved dependencies. Noise endpoints,
zero conditional variance, and zero coordinate information are included. -/
theorem induction_step_of_threeBit (hthree : Spec.ThreeBitTarget)
    (μ : FiniteLaw Ω) (p : ℝ) (a b c : Ω → Bool) (u : Ω → U)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hau : μ.independentUnbiasedBit a u) (hbu : μ.independentUnbiasedBit b u)
    (hchannel : ∀ s, 0 < μ.fibreMass u s →
      |(μ.conditionOn u s).bitCorrelation a b| = |1 - 2 * p|)
    (hmark : ∀ s, 0 < μ.fibreMass u s →
      (μ.conditionOn u s).conditionallyIndependentBit c a b)
    (hglobalMarkov : μ.conditionallyIndependentBit c a (fun ω => (u ω, b ω)))
    (hgood : μ.quadraticInformation (fun ω => bitValue (c ω)) b ≤ 1 / 4)
    (hconditional : 0 ≤ μ.conditionalProgressiveGap p c (fun ω => (u ω, a ω)) b) :
    0 ≤ μ.progressiveGap p c (fun ω => (u ω, a ω)) := by
  have hc0 (ω : Ω) := bitValue_nonneg (c ω)
  have hc1 (ω : Ω) := bitValue_le_one (c ω)
  have hnonneg := μ.conditionalShannonInformation_nonneg (fun ω => (u ω, a ω)) b _ hc0 hc1
  by_cases hpz : p = 0
  · subst p
    have hid := μ.progressiveGap_difference 0 c b (fun ω => (u ω, a ω))
    norm_num [noiseCorrelationSq, noiseGap, noiseInformation] at hid
    linarith
  by_cases hpo : p = 1
  · subst p
    have hid := μ.progressiveGap_difference 1 c b (fun ω => (u ω, a ω))
    norm_num [noiseCorrelationSq, noiseGap, noiseInformation] at hid
    linarith
  have hp0' : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
  have hp1' : p < 1 := lt_of_le_of_ne hp1 hpo
  by_cases hbzero : μ.quadraticInformation (fun ω => bitValue (c ω)) b = 0
  · exact hconditional.trans (μ.progressiveGap_ge_conditional_of_zero_coordinate
      p b c (fun ω => (u ω, a ω)) hbzero)
  let bI := μ.quadraticInformation (fun ω => bitValue (c ω)) b
  let uI := μ.quadraticInformation (fun ω => bitValue (c ω)) u
  let mC := μ.expect (fun ω => bitValue (c ω))
  let V := quadraticEntropy mC
  let v := μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω))
  let q := noiseCorrelationSq p
  let J := noiseGap p
  let ρ := |1 - 2 * p|
  let L := Real.log 2
  let k := biasCoefficient mC
  let g := μ.progressiveGap p c (fun ω => (u ω, a ω))
  let Δ := μ.conditionalProgressiveGap p c (fun ω => (u ω, a ω)) b
  have hΔ : 0 ≤ Δ := hconditional
  have hbI : 0 < bI := lt_of_le_of_ne (μ.quadraticInformation_nonneg b hc0 hc1)
    (Ne.symm hbzero)
  have huI : 0 ≤ uI := μ.quadraticInformation_nonneg u hc0 hc1
  have hbIV : bI ≤ V := μ.quadraticInformation_le_entropy b hc0 hc1
  have hV : 0 < V := hbI.trans_le hbIV
  have hV1 : V ≤ 1 := quadraticEntropy_le_one _
  have hm0 : 0 < mC := by
    have hm := μ.expect_nonneg hc0
    dsimp [V, quadraticEntropy] at hV
    by_contra hn
    have he : mC = 0 := by exact le_antisymm (le_of_not_gt hn) hm
    simp [he] at hV
  have hm1 : mC < 1 := by
    have hm := μ.expect_le_one hc1
    dsimp [V, quadraticEntropy] at hV
    by_contra hn
    have he : mC = 1 := by exact le_antisymm hm (le_of_not_gt hn)
    simp [he] at hV
  have hv : 0 < v := μ.conditionalEntropy_pos_of_coordinate_information_pos b c u hbu hbI
  have hq : q < 1 := by
    dsimp [q, noiseCorrelationSq]
    nlinarith [mul_pos hp0' (sub_pos.mpr hp1')]
  have hJ : 0 ≤ J := (noiseGap_bounds hp0 hp1).1
  have hρ0 : 0 ≤ ρ := abs_nonneg _
  have hρ1 : ρ < 1 := by
    apply abs_lt.mpr
    constructor <;> linarith
  have hρq : ρ ^ 2 = q := by dsimp [ρ, q, noiseCorrelationSq]; exact sq_abs _
  have hρI : Spec.divergence ρ = noiseInformation p := Spec.divergence_abs_noise p
  obtain ⟨τ, hτ, hmatch, hcomp, hcorr⟩ := μ.conditional_comparison a b c u
    hρ0 hρ1.le hau hbu hchannel hmark hv
  let R := q * Spec.divergence τ - Spec.divergence (ρ * τ)
  let S := noiseInformation p - Spec.divergence (ρ * τ)
  have hR : 0 ≤ R := by
    have h := Spec.divergence_scaling hρ0 hρ1.le (by linarith [hτ.1] : -1 ≤ τ) hτ.2
    rw [hρq] at h
    exact sub_nonneg.mpr h
  have hS : 0 ≤ S := by
    have hρτ : ρ * τ ≤ ρ := mul_le_of_le_one_right hρ0 hτ.2
    have h := Spec.divergence_strictMonoOn.monotoneOn
      ⟨mul_nonneg hρ0 hτ.1, hρτ.trans hρ1.le⟩ ⟨hρ0, hρ1.le⟩ hρτ
    rw [hρI] at h
    exact sub_nonneg.mpr h
  have hfirst : Δ + v * R + (1 - q) * bI / (2 * L * V * v) * uI - J * bI ≤ g := by
    have h := μ.gap_first_of_comparison p (Spec.divergence τ) (Spec.divergence (ρ * τ))
      a b c u hp0 hp1 hbu hglobalMarkov hv hmatch hcomp
    change Δ + v * R + (1 - q) * bI * uI / (2 * L * V * v) - J * bI ≤ g at h
    convert h using 1
    ring
  by_cases hρzero : ρ = 0
  · have hJzero : J = 0 := by
      have hqzero : q = 0 := by simpa [hρzero] using hρq.symm
      have hIzero : noiseInformation p = 0 := by simpa [hρzero] using hρI.symm
      change q - noiseInformation p = 0
      rw [hqzero, hIzero, sub_self]
    have hterm : 0 ≤ (1 - q) * bI / (2 * L * V * v) * uI :=
      mul_nonneg (div_nonneg (mul_nonneg (sub_nonneg.mpr hq.le) hbI.le)
        (by dsimp [L]; positivity)) huI
    rw [hJzero, zero_mul, sub_zero] at hfirst
    have hVR := mul_nonneg hv.le hR
    exact (add_nonneg (add_nonneg hΔ hVR) hterm).trans hfirst
  have hρpos : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hρzero)
  have hcorr' : bI ≤ v ^ 2 * τ ^ 2 := by
    have h := (div_le_iff₀ (sq_pos_of_pos hv)).mp hcorr
    simpa [mul_comm] using h
  have hτne : τ ≠ 0 := by
    intro hτzero
    have hz := hcorr'
    rw [hτzero] at hz
    norm_num at hz
    linarith
  have hτpos : 0 < τ := lt_of_le_of_ne hτ.1 (Ne.symm hτne)
  have hbias := μ.shannonInformation_le_biasCoefficient u _ hc0 hc1 hm0 hm1
  have hsecond : v * S - ((1 - q) * k / L + J) * uI ≤ g :=
    μ.gap_second_of_comparison_and_bias p (Spec.divergence (ρ * τ)) k a c u hp0 hp1 hcomp hbias
  have hk : 0 < k := biasCoefficient_pos hm0 hm1
  have hα : 0 ≤ alphaCoefficient q J L := alphaCoefficient_nonneg hq hJ log_two_pos.le
  have hkα : 0 < k + alphaCoefficient q J L := by linarith
  have hVk : V * k ≤ 1 := quadratic_mul_biasCoefficient hm0 hm1
  have hthree' : J ≤ S / (2 * (1 + alphaCoefficient q J L)) + 2 * R / τ := by
    have ht := (hthree ρ τ hρpos hρ1 hτpos hτ.2).le
    rw [hρq, hρI] at ht
    exact ht
  have hgap := induction_gap_nondegenerate hq hJ log_two_pos hbI.le hgood
    hV hV1 hv hkα hVk hτpos hR hS hcorr' hfirst hsecond hthree'
  exact gap_nonneg_of_conditional (gapMultiplier_nonneg hbI.le hV hv hkα) hconditional hgap

end FiniteLaw
end CourtadeKumar
