import CK.Latest

/-! The literal quantitative induction-step lemma, with its multiplier witness. -/
noncomputable section
namespace CourtadeKumar.FiniteLaw
variable {Ω U : Type*} [Fintype Ω] [Fintype U] [DecidableEq U]

theorem quantitative_induction_step
    (μ : FiniteLaw Ω) (p : ℝ) (a b c : Ω → Bool) (u : Ω → U)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hau : μ.independentUnbiasedBit a u) (hbu : μ.independentUnbiasedBit b u)
    (hchannel : ∀ s, 0 < μ.fibreMass u s →
      |(μ.conditionOn u s).bitCorrelation a b| = |1 - 2 * p|)
    (hmark : ∀ s, 0 < μ.fibreMass u s →
      (μ.conditionOn u s).conditionallyIndependentBit c a b)
    (hglobalMarkov : μ.conditionallyIndependentBit c a (fun ω => (u ω, b ω)))
    (hgood : μ.quadraticInformation (fun ω => bitValue (c ω)) b ≤ 1 / 4) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      μ.conditionalProgressiveGap p c (fun ω => (u ω, a ω)) b / (1 + lam) ≤
        μ.progressiveGap p c (fun ω => (u ω, a ω)) := by
  have hthree := Spec.threeBit
  have hc0 (ω : Ω) := bitValue_nonneg (c ω)
  have hc1 (ω : Ω) := bitValue_le_one (c ω)
  have hnonneg := μ.conditionalShannonInformation_nonneg (fun ω => (u ω, a ω)) b _ hc0 hc1
  by_cases hpz : p = 0
  · subst p
    have hid := μ.progressiveGap_difference 0 c b (fun ω => (u ω, a ω))
    norm_num [noiseCorrelationSq, noiseGap, noiseInformation] at hid
    refine ⟨0, by norm_num, ?_⟩
    simp only [add_zero, div_one]
    linarith
  by_cases hpo : p = 1
  · subst p
    have hid := μ.progressiveGap_difference 1 c b (fun ω => (u ω, a ω))
    norm_num [noiseCorrelationSq, noiseGap, noiseInformation] at hid
    refine ⟨0, by norm_num, ?_⟩
    simp only [add_zero, div_one]
    linarith
  have hp0' : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
  have hp1' : p < 1 := lt_of_le_of_ne hp1 hpo
  by_cases hbzero : μ.quadraticInformation (fun ω => bitValue (c ω)) b = 0
  · refine ⟨0, by norm_num, ?_⟩
    simpa only [add_zero, div_one] using μ.progressiveGap_ge_conditional_of_zero_coordinate
      p b c (fun ω => (u ω, a ω)) hbzero
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
    refine ⟨0, by norm_num, ?_⟩
    simp only [add_zero, div_one]
    change Δ ≤ g
    calc
      Δ ≤ Δ + v * R := le_add_of_nonneg_right hVR
      _ ≤ Δ + v * R + (1 - q) * bI / (2 * L * V * v) * uI :=
        le_add_of_nonneg_right hterm
      _ ≤ g := hfirst
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
  exact ⟨gapMultiplier bI V v k (alphaCoefficient q J L),
    gapMultiplier_nonneg hbI.le hV hv hkα, hgap⟩


end CourtadeKumar.FiniteLaw
