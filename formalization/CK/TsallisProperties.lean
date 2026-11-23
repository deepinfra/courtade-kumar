import CK.InductionStep

/-!
# The finite-law Tsallis properties from the preliminaries

The six parts of `lem:tsallis-properties` use bits on an arbitrary finite
probability space and arbitrary finite observations.  Conditional quantities
refer to the actual disintegration of the original law, including null fibres.
-/

noncomputable section
namespace CourtadeKumar.FiniteLaw

variable {Ω : Type*} [Fintype Ω]
variable {U Z W : Type*} [Fintype U] [Fintype Z] [Fintype W]
  [DecidableEq U] [DecidableEq Z] [DecidableEq W]

omit [Fintype W] [DecidableEq W] in
theorem conditionalQuadraticInformation_nonneg (μ : FiniteLaw Ω) (u : Ω → U) (z : Ω → Z)
    (c : Ω → ℝ) (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    0 ≤ μ.conditionalQuadraticInformation c z u :=
  (μ.map u).expect_nonneg fun s => (μ.conditionOn u s).quadraticInformation_nonneg z hc0 hc1

omit [Fintype W] [DecidableEq W] in
theorem conditionalQuadraticInformation_le_entropy (μ : FiniteLaw Ω) (u : Ω → U) (z : Ω → Z)
    (c : Ω → ℝ) (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    μ.conditionalQuadraticInformation c z u ≤ μ.conditionalQuadraticEntropy u c := by
  unfold conditionalQuadraticInformation
  calc
    _ ≤ (μ.map u).expect (fun s => quadraticEntropy ((μ.conditionOn u s).expect c)) :=
      (μ.map u).expect_mono fun s => (μ.conditionOn u s).quadraticInformation_le_entropy z hc0 hc1
    _ = _ := μ.conditionOn_quadraticEntropy_tower u c

omit [Fintype W] [DecidableEq W] in
theorem conditionalQuadraticInformation_eq_entropy_diff (μ : FiniteLaw Ω) (u : Ω → U)
    (z : Ω → Z) (c : Ω → ℝ) :
    μ.conditionalQuadraticInformation c z u =
      μ.conditionalQuadraticEntropy u c - μ.conditionalQuadraticEntropy (fun ω => (u ω, z ω)) c := by
  unfold conditionalQuadraticInformation quadraticInformation
  rw [(μ.map u).expect_sub, μ.conditionOn_quadraticEntropy_tower, μ.conditionalQuadraticEntropy_tower]

theorem conditionalQuadraticInformation_chain (μ : FiniteLaw Ω) (u : Ω → U)
    (z : Ω → Z) (w : Ω → W) (c : Ω → ℝ) :
    μ.conditionalQuadraticInformation c (fun ω => (z ω, w ω)) u =
      μ.conditionalQuadraticInformation c z u +
        μ.conditionalQuadraticInformation c w (fun ω => (u ω, z ω)) := by
  simp only [conditionalQuadraticInformation_eq_entropy_diff]
  have he := μ.conditionalQuadraticEntropy_equiv (fun ω => ((u ω, z ω), w ω))
    (Equiv.prodAssoc U Z W) c
  change μ.conditionalQuadraticEntropy (fun ω => (u ω, (z ω, w ω))) c =
    μ.conditionalQuadraticEntropy (fun ω => ((u ω, z ω), w ω)) c at he
  rw [he]
  ring

omit [Fintype U] [DecidableEq U] in
theorem quadraticInformation_data_processing (μ : FiniteLaw Ω) (c : Ω → Bool)
    (z : Ω → Z) (w : Ω → W) (hmark : μ.conditionallyIndependentBit c w z) :
    μ.quadraticInformation (fun ω => bitValue (c ω)) w ≤
      μ.quadraticInformation (fun ω => bitValue (c ω)) z := by
  have he := μ.conditionalQuadraticEntropy_equiv (fun ω => (z ω, w ω))
    (Equiv.prodComm Z W) (fun ω => bitValue (c ω))
  change μ.conditionalQuadraticEntropy (fun ω => (w ω, z ω)) (fun ω => bitValue (c ω)) =
    μ.conditionalQuadraticEntropy (fun ω => (z ω, w ω)) (fun ω => bitValue (c ω)) at he
  have hchain := μ.quadraticInformation_chain w z (fun ω => bitValue (c ω))
  have hnonneg := μ.conditionalQuadraticInformation_nonneg w z (fun ω => bitValue (c ω))
    (fun ω => bitValue_nonneg (c ω)) (fun ω => bitValue_le_one (c ω))
  unfold quadraticInformation at hchain ⊢
  rw [he, μ.conditionalQuadraticEntropy_of_conditionalIndependence c w z hmark] at hchain
  linarith

omit [Fintype U] [DecidableEq U] in
theorem shannonInformation_data_processing (μ : FiniteLaw Ω) (c : Ω → Bool)
    (z : Ω → Z) (w : Ω → W) (hmark : μ.conditionallyIndependentBit c w z) :
    μ.shannonInformation (fun ω => bitValue (c ω)) w ≤
      μ.shannonInformation (fun ω => bitValue (c ω)) z := by
  have he := μ.conditionalShannonEntropy_equiv (fun ω => (z ω, w ω))
    (Equiv.prodComm Z W) (fun ω => bitValue (c ω))
  change μ.conditionalShannonEntropy (fun ω => (w ω, z ω)) (fun ω => bitValue (c ω)) =
    μ.conditionalShannonEntropy (fun ω => (z ω, w ω)) (fun ω => bitValue (c ω)) at he
  have hchain := μ.shannonInformation_chain w z (fun ω => bitValue (c ω))
  have hnonneg := μ.conditionalShannonInformation_nonneg w z (fun ω => bitValue (c ω))
    (fun ω => bitValue_nonneg (c ω)) (fun ω => bitValue_le_one (c ω))
  unfold shannonInformation at hchain ⊢
  rw [he, μ.conditionalShannonEntropy_of_conditionalIndependence c w z hmark] at hchain
  linarith

omit [Fintype W] [DecidableEq W] in
theorem conditionalQuadraticInformation_le_shannonInformation (μ : FiniteLaw Ω) (u : Ω → U)
    (z : Ω → Z) (c : Ω → ℝ) (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    μ.conditionalQuadraticInformation c z u ≤ 2 * Real.log 2 * μ.conditionalShannonInformation c z u := by
  unfold conditionalQuadraticInformation conditionalShannonInformation
  rw [← (μ.map u).expect_const_mul]
  exact (μ.map u).expect_mono fun s => (μ.conditionOn u s).quadraticInformation_le_shannonInformation z c hc0 hc1

omit [Fintype W] [DecidableEq W] in
theorem conditionalShannonInformation_le_quadraticInformation_of_unbiased (μ : FiniteLaw Ω)
    (u : Ω → U) (z : Ω → Z) (c : Ω → Bool) (hcu : μ.independentUnbiasedBit c u) :
    μ.conditionalShannonInformation (fun ω => bitValue (c ω)) z u ≤
      μ.conditionalQuadraticInformation (fun ω => bitValue (c ω)) z u := by
  exact (μ.map u).expect_mono fun s =>
    (μ.conditionOn u s).shannonInformation_le_quadraticInformation_of_unbiased z _
      (fun ω => bitValue_nonneg (c ω)) (fun ω => bitValue_le_one (c ω))
      (μ.conditionOn_mean_of_independentUnbiasedBit c u hcu s)

omit [Fintype Z] [Fintype W] [DecidableEq Z] [DecidableEq W] in
/-- Independence of a bit with an arbitrary, possibly biased marginal. -/
def independentBit (μ : FiniteLaw Ω) (b : Ω → Bool) (u : Ω → U) : Prop :=
  ∀ s, μ.fibreMoment u (fun ω => bitValue (b ω)) s =
    μ.fibreMass u s * μ.expect (fun ω => bitValue (b ω))

omit [Fintype U] [Fintype Z] [Fintype W] [DecidableEq Z] [DecidableEq W] in
theorem conditionOn_mean_of_independentBit (μ : FiniteLaw Ω) (b : Ω → Bool) (u : Ω → U)
    (hbu : μ.independentBit b u) (s : U) :
    (μ.conditionOn u s).expect (fun ω => bitValue (b ω)) = μ.expect (fun ω => bitValue (b ω)) := by
  by_cases hs : 0 < μ.fibreMass u s
  · rw [μ.conditionOn_expect_of_pos u s hs]
    unfold conditionalMean
    rw [hbu s]
    field_simp
  · simp [conditionOn, hs]

omit [Fintype Z] [Fintype W] [DecidableEq Z] [DecidableEq W] in
theorem quadratic_conditioning_joint (μ : FiniteLaw Ω) (b c : Ω → Bool) (u : Ω → U)
    (hbu : μ.independentBit b u) :
    μ.conditionalQuadraticInformation (fun ω => bitValue (b ω)) c u *
      μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) ≥
      quadraticEntropy (μ.expect (fun ω => bitValue (b ω))) *
        μ.quadraticInformation (fun ω => bitValue (c ω)) b := by
  have h := (μ.map u).quadratic_conditioning (μ.conditionOn u) b c
    (μ.expect (fun ω => bitValue (b ω))) (μ.conditionOn_mean_of_independentBit b u hbu)
  rw [μ.conditionOn_quadraticEntropy_tower, μ.mixture_conditionOn] at h
  exact h

end CourtadeKumar.FiniteLaw
