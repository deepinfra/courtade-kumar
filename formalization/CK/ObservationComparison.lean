import CK.KernelMatchingComparator
import CK.ConditionalKernel

/-!
# Comparison hypotheses from genuine arbitrary observations

Joint independence of `(A,B)` and an arbitrary observation yields unbiased
conditional bits and the fixed signed channel. Conditional private randomness
is expressed by conditional expectations of the four joint bit cells; these
actual probability identities imply the finite conditional-law Markov property.
-/

set_option maxHeartbeats 700000
noncomputable section
namespace CourtadeKumar.KernelInformation
open Set MeasureTheory Filter ProbabilityTheory

variable {Ω U Γ : Type*} [mΩ : MeasurableSpace Ω] [mU : MeasurableSpace U]
  [Fintype Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [StandardBorelSpace Γ] [Nonempty Γ]

/-- The conditional probability factorization expressing that `C` is generated
from `(B,U)` using private randomness. All four terms are genuine conditional
expectations under the original probability measure. -/
def conditionalBitMarkov (ν : Measure Ω) (y : Ω → Γ) (u : Ω → U)
    (a b c : Γ → Bool) : Prop :=
  ∀ s t : Bool,
    (fun ω =>
      (ν[fun ω => if (b (y ω), a (y ω)) = (s,t) then FiniteLaw.bitValue (c (y ω)) else 0 |
        mU.comap u]) ω *
      (ν[fun ω => if b (y ω) = s then (1 : ℝ) else 0 | mU.comap u]) ω) =ᵐ[ν]
    (fun ω =>
      (ν[fun ω => if b (y ω) = s then FiniteLaw.bitValue (c (y ω)) else 0 | mU.comap u]) ω *
      (ν[fun ω => if (b (y ω), a (y ω)) = (s,t) then (1 : ℝ) else 0 | mU.comap u]) ω)

variable {ν : Measure Ω} [IsProbabilityMeasure ν] {y : Ω → Γ} {u : Ω → U}

/-- Actual conditional probability factorization transfers to the regular
conditional finite joint laws. No information inequality is assumed. -/
theorem conditionalKernel_markov_ae (hy : Measurable y) (hu : Measurable u)
    (a b c : Γ → Bool) (hprivate : conditionalBitMarkov ν y u a b c) :
    ∀ᵐ z ∂ν.map u, ((conditionalKernel ν y u).law z).conditionallyIndependentBit c a b := by
  let K := conditionalKernel ν y u
  have hs (s t : Bool) : MeasurableSet {z |
      (K.law z).fibreMoment (fun w => (b w, a w)) (fun w => FiniteLaw.bitValue (c w)) (s,t) *
        (K.law z).fibreMass b s =
      (K.law z).fibreMoment b (fun w => FiniteLaw.bitValue (c w)) s *
        (K.law z).fibreMass (fun w => (b w, a w)) (s,t)} :=
    measurableSet_eq_fun
      ((K.measurable_fibreMoment _ _ _).mul (K.measurable_fibreMass _ _))
      ((K.measurable_fibreMoment _ _ _).mul (K.measurable_fibreMass _ _))
  have hcell (s t : Bool) : ∀ᵐ z ∂ν.map u,
      (K.law z).fibreMoment (fun w => (b w, a w)) (fun w => FiniteLaw.bitValue (c w)) (s,t) *
        (K.law z).fibreMass b s =
      (K.law z).fibreMoment b (fun w => FiniteLaw.bitValue (c w)) s *
        (K.law z).fibreMass (fun w => (b w, a w)) (s,t) := by
    apply (ae_map_iff hu.aemeasurable (hs s t)).2
    have h1 := conditionalKernel_expect_ae (ν := ν) hy hu
      (fun w => if (b w, a w) = (s,t) then FiniteLaw.bitValue (c w) else 0)
    have h2 := conditionalKernel_expect_ae (ν := ν) hy hu
      (fun w => if b w = s then (1 : ℝ) else 0)
    have h3 := conditionalKernel_expect_ae (ν := ν) hy hu
      (fun w => if b w = s then FiniteLaw.bitValue (c w) else 0)
    have h4 := conditionalKernel_expect_ae (ν := ν) hy hu
      (fun w => if (b w, a w) = (s,t) then (1 : ℝ) else 0)
    filter_upwards [h1, h2, h3, h4, hprivate s t] with ω h1ω h2ω h3ω h4ω hp
    simp only [FiniteLaw.fibreMoment_eq_expect, FiniteLaw.fibreMass_eq_expect]
    exact (congrArg₂ (· * ·) h1ω h2ω).trans (hp.trans (congrArg₂ (· * ·) h3ω h4ω).symm)
  filter_upwards [hcell false false, hcell false true, hcell true false, hcell true true]
    with z h00 h01 h10 h11
  intro s t
  cases s <;> cases t <;> assumption

/-- The manuscript's genuine joint-independence hypothesis supplies all constant
conditional channel assumptions needed by the arbitrary-observation comparison. -/
theorem conditionalKernel_comparison_hypotheses (hy : Measurable y) (hu : Measurable u)
    (a b c : Γ → Bool)
    (hind : IndepFun (fun ω => (a (y ω), b (y ω))) u ν)
    (ha : (∫ ω, FiniteLaw.bitValue (a (y ω)) ∂ν) = 1 / 2)
    (hb : (∫ ω, FiniteLaw.bitValue (b (y ω)) ∂ν) = 1 / 2)
    (hprivate : conditionalBitMarkov ν y u a b c) :
    (∀ᵐ z ∂ν.map u, ((conditionalKernel ν y u).law z).expect
      (fun w => FiniteLaw.bitValue (a w)) = 1 / 2) ∧
    (∀ᵐ z ∂ν.map u, ((conditionalKernel ν y u).law z).expect
      (fun w => FiniteLaw.bitValue (b w)) = 1 / 2) ∧
    (∀ᵐ z ∂ν.map u, ((conditionalKernel ν y u).law z).bitCorrelation a b =
      ∫ ω, (2 * FiniteLaw.bitValue (a (y ω)) - 1) *
        (2 * FiniteLaw.bitValue (b (y ω)) - 1) ∂ν) ∧
    (∀ᵐ z ∂ν.map u, ((conditionalKernel ν y u).law z).conditionallyIndependentBit c a b) := by
  have ha' := conditionalKernel_expect_of_independent hy hu (fun w => (a w, b w)) hind
    (fun p => FiniteLaw.bitValue p.1)
  have hb' := conditionalKernel_expect_of_independent hy hu (fun w => (a w, b w)) hind
    (fun p => FiniteLaw.bitValue p.2)
  have hγ := conditionalKernel_expect_of_independent hy hu (fun w => (a w, b w)) hind
    (fun p => (2 * FiniteLaw.bitValue p.1 - 1) * (2 * FiniteLaw.bitValue p.2 - 1))
  exact ⟨by simpa only [ha] using ha', by simpa only [hb] using hb', hγ,
    conditionalKernel_markov_ae hy hu a b c hprivate⟩

/-- The denominator in the comparison is exactly the entropy of the genuine
posterior mean, evaluated on the original arbitrary probability space. -/
theorem conditionalKernel_quadraticEntropy_integral (hy : Measurable y) (hu : Measurable u)
    (c : Γ → Bool) :
    (∫ z, quadraticEntropy (((conditionalKernel ν y u).law z).expect
      (fun w => FiniteLaw.bitValue (c w))) ∂ν.map u) =
    ∫ ω, quadraticEntropy ((ν[fun ω => FiniteLaw.bitValue (c (y ω)) | mU.comap u]) ω) ∂ν := by
  rw [integral_map hu.aemeasurable ((conditionalKernel ν y u).measurable_bitEntropy c).aestronglyMeasurable]
  apply integral_congr_ae
  exact (conditionalKernel_expect_ae (ν := ν) hy hu (fun w => FiniteLaw.bitValue (c w))).mono
    fun _ h => congrArg quadraticEntropy h

/-- The paper's comparison existence theorem on an arbitrary original probability
space and with an arbitrary measurable observation. Conditional information is
literally averaged under the actual regular conditional joint law, as defined
in the manuscript. The only probabilistic assumptions are joint independence,
unbiasedness, and conditional probability factorization. -/
theorem observation_comparison_realized [DecidableEq Γ]
    (hy : Measurable y) (hu : Measurable u) (a b c : Γ → Bool)
    (hind : IndepFun (fun ω => (a (y ω), b (y ω))) u ν)
    (ha : (∫ ω, FiniteLaw.bitValue (a (y ω)) ∂ν) = 1 / 2)
    (hb : (∫ ω, FiniteLaw.bitValue (b (y ω)) ∂ν) = 1 / 2)
    (hprivate : conditionalBitMarkov ν y u a b c)
    (hV : 0 < ∫ ω, quadraticEntropy
      ((ν[fun ω => FiniteLaw.bitValue (c (y ω)) | mU.comap u]) ω) ∂ν) :
    letI : IsProbabilityMeasure (ν.map u) := isProbabilityMeasure_map hu.aemeasurable
    let K := conditionalKernel ν y u
    let V := ∫ ω, quadraticEntropy
      ((ν[fun ω => FiniteLaw.bitValue (c (y ω)) | mU.comap u]) ω) ∂ν
    ∃ (K' : FiniteKernel U (Γ × Bool)) (c' : Γ × Bool → Bool),
      (∀ z, (K'.law z).map Prod.fst = K.law z) ∧
      (∀ z, (K'.law z).conditionallyIndependentBit c' Prod.fst (fun p => b p.1)) ∧
      (K'.mixture (ν.map u)).map Prod.fst = K.mixture (ν.map u) ∧
      (K'.mixture (ν.map u)).conditionallyIndependentBit c' Prod.fst (fun p => b p.1) ∧
      (K'.mixture (ν.map u)).expect (fun p => FiniteLaw.bitValue (c' p)) = 1 / 2 ∧
      (K'.mixture (ν.map u)).shannonInformation (fun p => FiniteLaw.bitValue (b p.1)) c' =
        (∫ z, (K.law z).shannonInformation (fun s => FiniteLaw.bitValue (b s)) c ∂ν.map u) / V ∧
      (∫ z, (K.law z).shannonInformation (fun s => FiniteLaw.bitValue (a s)) c ∂ν.map u) / V ≤
        (K'.mixture (ν.map u)).shannonInformation (fun p => FiniteLaw.bitValue (a p.1)) c' ∧
      (K.mixture (ν.map u)).quadraticInformation (fun s => FiniteLaw.bitValue (c s)) b / V^2 ≤
        (K'.mixture (ν.map u)).quadraticInformation
          (fun p => FiniteLaw.bitValue (c' p)) (fun p => b p.1) := by
  letI : IsProbabilityMeasure (ν.map u) := isProbabilityMeasure_map hu.aemeasurable
  dsimp only
  obtain ⟨ha', hb', hchannel, hmark⟩ :=
    conditionalKernel_comparison_hypotheses hy hu a b c hind ha hb hprivate
  have hV' : 0 < ∫ z, quadraticEntropy (((conditionalKernel ν y u).law z).expect
      (fun w => FiniteLaw.bitValue (c w))) ∂ν.map u := by
    rw [conditionalKernel_quadraticEntropy_integral hy hu c]
    exact hV
  have h := (conditionalKernel ν y u).conditional_comparison_realized (ν.map u)
    a b c ha' hb' hchannel hmark hV'
  simpa only [conditionalKernel_quadraticEntropy_integral hy hu c] using h

end CourtadeKumar.KernelInformation
