import CK.Markov

/-!
# Probabilistic gap bounds in the manuscript

Theorems here use the actual finite-law information quantities.  Remaining
comparison and biased-information estimates are explicitly identified as their
own prerequisites rather than replaced with the desired gap conclusion.
-/

noncomputable section
namespace CourtadeKumar
namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]
variable {U : Type*} [Fintype U] [DecidableEq U]

def progressiveGap {Z : Type*} [Fintype Z] [DecidableEq Z]
    (μ : FiniteLaw Ω) (p : ℝ) (c : Ω → Bool) (z : Ω → Z) : ℝ :=
  progressiveEntropy p (μ.expect (fun ω => bitValue (c ω))) -
    μ.shannonInformation (fun ω => bitValue (c ω)) z

def conditionalProgressiveGap {Z : Type*} [Fintype Z] [DecidableEq Z]
    (μ : FiniteLaw Ω) (p : ℝ) (c : Ω → Bool) (z : Ω → Z) (u : Ω → U) : ℝ :=
  (μ.map u).expect (fun s => (μ.conditionOn u s).progressiveGap p c z)

theorem conditionalProgressiveEntropy_eq (μ : FiniteLaw Ω) (p : ℝ)
    (c : Ω → Bool) (u : Ω → U) :
    (μ.map u).expect (fun s => progressiveEntropy p ((μ.conditionOn u s).expect (fun ω => bitValue (c ω)))) =
      noiseCorrelationSq p * μ.conditionalShannonEntropy u (fun ω => bitValue (c ω)) -
        noiseGap p * μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) := by
  unfold progressiveEntropy
  rw [(μ.map u).expect_sub, (μ.map u).expect_const_mul, (μ.map u).expect_const_mul,
    μ.conditionOn_shannonEntropy_tower u]
  change _ - noiseGap p * (μ.map u).expect
      (fun s => quadraticEntropy ((μ.conditionOn u s).expect (fun ω => bitValue (c ω)))) = _
  rw [μ.conditionOn_quadraticEntropy_tower]

theorem conditionalProgressiveGap_eq {Z : Type*} [Fintype Z] [DecidableEq Z]
    (μ : FiniteLaw Ω) (p : ℝ) (c : Ω → Bool) (z : Ω → Z) (u : Ω → U) :
    μ.conditionalProgressiveGap p c z u =
      noiseCorrelationSq p * μ.conditionalShannonEntropy u (fun ω => bitValue (c ω)) -
        noiseGap p * μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) -
          μ.conditionalShannonInformation (fun ω => bitValue (c ω)) z u := by
  unfold conditionalProgressiveGap progressiveGap
  rw [(μ.map u).expect_sub, μ.conditionalProgressiveEntropy_eq]
  rfl

theorem conditionalShannonInformation_eq_entropy_diff {Z : Type*} [Fintype Z] [DecidableEq Z]
    (μ : FiniteLaw Ω) (u : Ω → U) (z : Ω → Z) (c : Ω → ℝ) :
    μ.conditionalShannonInformation c z u =
      μ.conditionalShannonEntropy u c - μ.conditionalShannonEntropy (fun ω => (u ω, z ω)) c := by
  unfold conditionalShannonInformation shannonInformation
  rw [(μ.map u).expect_sub, μ.conditionOn_shannonEntropy_tower,
    μ.conditionalShannonEntropy_tower]

/-- The unconditional/conditional progressive-gap identity used before `gap-first`. -/
theorem progressiveGap_difference {Z : Type*} [Fintype Z] [DecidableEq Z]
    (μ : FiniteLaw Ω) (p : ℝ) (c b : Ω → Bool) (x : Ω → Z) :
    μ.progressiveGap p c x - μ.conditionalProgressiveGap p c x b =
      μ.conditionalShannonInformation (fun ω => bitValue (c ω)) b x -
        (1 - noiseCorrelationSq p) * μ.shannonInformation (fun ω => bitValue (b ω)) c -
          noiseGap p * μ.quadraticInformation (fun ω => bitValue (c ω)) b := by
  have hswap := μ.conditionalShannonEntropy_equiv (fun ω => (b ω, x ω))
    (Equiv.prodComm Bool Z) (fun ω => bitValue (c ω))
  change μ.conditionalShannonEntropy (fun ω => (x ω, b ω)) (fun ω => bitValue (c ω)) =
    μ.conditionalShannonEntropy (fun ω => (b ω, x ω)) (fun ω => bitValue (c ω)) at hswap
  rw [μ.conditionalProgressiveGap_eq, μ.shannonInformation_symm b c,
    μ.conditionalShannonInformation_eq_entropy_diff x b,
    μ.conditionalShannonInformation_eq_entropy_diff b x]
  unfold progressiveGap progressiveEntropy shannonInformation quadraticInformation quadraticEntropy
  rw [hswap]
  ring

/-- The channel Markov factorization removes `A` after `(U,B)` has been observed. -/
theorem conditionalInformation_Markov_difference (μ : FiniteLaw Ω)
    (a b c : Ω → Bool) (u : Ω → U)
    (hmark : μ.conditionallyIndependentBit c a (fun ω => (u ω, b ω))) :
    μ.conditionalShannonInformation (fun ω => bitValue (c ω)) b (fun ω => (u ω, a ω)) =
      μ.conditionalShannonInformation (fun ω => bitValue (b ω)) c u -
        μ.conditionalShannonInformation (fun ω => bitValue (a ω)) c u := by
  let e : ((U × Bool) × Bool) ≃ ((U × Bool) × Bool) :=
    { toFun := fun v => ((v.1.1, v.2), v.1.2)
      invFun := fun v => ((v.1.1, v.2), v.1.2)
      left_inv := by rintro ⟨⟨x, y⟩, z⟩; rfl
      right_inv := by rintro ⟨⟨x, y⟩, z⟩; rfl }
  have hswap := μ.conditionalShannonEntropy_equiv (fun ω => ((u ω, a ω), b ω)) e
    (fun ω => bitValue (c ω))
  change μ.conditionalShannonEntropy (fun ω => ((u ω, b ω), a ω)) (fun ω => bitValue (c ω)) =
    μ.conditionalShannonEntropy (fun ω => ((u ω, a ω), b ω)) (fun ω => bitValue (c ω)) at hswap
  have hH := μ.conditionalShannonEntropy_of_conditionalIndependence c a
    (fun ω => (u ω, b ω)) hmark
  rw [μ.conditionalShannonInformation_symm b c u, μ.conditionalShannonInformation_symm a c u,
    μ.conditionalShannonInformation_eq_entropy_diff,
    μ.conditionalShannonInformation_eq_entropy_diff,
    μ.conditionalShannonInformation_eq_entropy_diff]
  rw [← hswap, hH]
  ring

/-- Lemma `gap-first` from its comparison-bit matching and domination estimates.
Independence, the Markov step, and conditioning gain are actual proved dependencies. -/
theorem gap_first_of_comparison (μ : FiniteLaw Ω) (p r m : ℝ)
    (a b c : Ω → Bool) (u : Ω → U) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbu : μ.independentUnbiasedBit b u)
    (hmark : μ.conditionallyIndependentBit c a (fun ω => (u ω, b ω)))
    (hv : 0 < μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)))
    (hmatch : μ.conditionalShannonInformation (fun ω => bitValue (b ω)) c u =
      μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) * r)
    (hcomparison : μ.conditionalShannonInformation (fun ω => bitValue (a ω)) c u ≤
      μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) * m) :
    μ.conditionalProgressiveGap p c (fun ω => (u ω, a ω)) b +
      μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) * (noiseCorrelationSq p * r - m) +
      (1 - noiseCorrelationSq p) * μ.quadraticInformation (fun ω => bitValue (c ω)) b *
        μ.quadraticInformation (fun ω => bitValue (c ω)) u /
        (2 * Real.log 2 * quadraticEntropy (μ.expect (fun ω => bitValue (c ω))) *
          μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω))) -
      noiseGap p * μ.quadraticInformation (fun ω => bitValue (c ω)) b ≤
      μ.progressiveGap p c (fun ω => (u ω, a ω)) := by
  have hq1 : noiseCorrelationSq p ≤ 1 := by
    unfold noiseCorrelationSq
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1)]
  have hid := μ.progressiveGap_difference p c b (fun ω => (u ω, a ω))
  rw [μ.conditionalInformation_Markov_difference a b c u hmark, hmatch] at hid
  have hgain := μ.conditioning_gain_joint b c u hbu hv
  have hgain' := mul_le_mul_of_nonneg_left hgain (sub_nonneg.mpr hq1)
  rw [hmatch] at hgain'
  simp only [div_eq_mul_inv] at hgain' ⊢
  nlinarith

/-- Lemma `gap-second` after the preceding comparison and biased-information
lemmas have supplied their numerical bounds.  The chain rule and entropy
sandwich are proved dependencies, not hypotheses. -/
theorem gap_second_of_comparison_and_bias (μ : FiniteLaw Ω) (p m k : ℝ)
    (a c : Ω → Bool) (u : Ω → U) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcomparison : μ.conditionalShannonInformation (fun ω => bitValue (a ω)) c u ≤
      μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) * m)
    (hbias : μ.shannonInformation (fun ω => bitValue (c ω)) u ≤
      k / Real.log 2 * μ.quadraticInformation (fun ω => bitValue (c ω)) u) :
    μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) * (noiseInformation p - m) -
      ((1 - noiseCorrelationSq p) * k / Real.log 2 + noiseGap p) *
        μ.quadraticInformation (fun ω => bitValue (c ω)) u ≤
      μ.progressiveGap p c (fun ω => (u ω, a ω)) := by
  have hq0 : 0 ≤ noiseCorrelationSq p := sq_nonneg _
  have hq1 : noiseCorrelationSq p ≤ 1 := by
    unfold noiseCorrelationSq
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1)]
  have hchain := μ.shannonInformation_chain u a (fun ω => bitValue (c ω))
  rw [μ.conditionalShannonInformation_symm c a u] at hchain
  have hupper : μ.shannonInformation (fun ω => bitValue (c ω)) (fun ω => (u ω, a ω)) ≤
      μ.shannonInformation (fun ω => bitValue (c ω)) u +
        μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) * m := by
    rw [hchain]
    linarith
  have hsand := (μ.conditional_entropy_sandwich u (fun ω => bitValue (c ω))
    (fun ω => bitValue_nonneg (c ω)) (fun ω => bitValue_le_one (c ω))).1
  have hsand' := mul_nonneg hq0 (sub_nonneg.mpr hsand)
  have hbias' := mul_le_mul_of_nonneg_left hbias (sub_nonneg.mpr hq1)
  unfold progressiveGap progressiveEntropy noiseGap
  unfold shannonInformation at hupper hbias' ⊢
  unfold quadraticInformation at hbias' ⊢
  unfold quadraticEntropy at hbias' ⊢
  simp only [div_eq_mul_inv] at hbias' ⊢
  nlinarith

end FiniteLaw
end CourtadeKumar
