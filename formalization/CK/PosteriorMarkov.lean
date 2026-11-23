import CK.PosteriorChain
import CK.Disintegration
import Mathlib.Probability.Independence.Conditional

/-!
# Data processing from actual conditional independence

The Markov hypothesis is conditional factorization against every measurable
event of the last observation. A pi-system argument derives posterior
sufficiency on the joined observation, and then both data-processing
inequalities follow from the proved nested-observation inequalities.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace CourtadeKumar.Posterior
open Set MeasureTheory Filter ProbabilityTheory

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- Conditional factorization of a binary input and an observed sigma-algebra
`n`, given `m`. For a bit indicator this is exactly the usual conditional
independence event criterion. It does not assert posterior sufficiency or an
information inequality. -/
def MarkovFactorization (ν : Measure Ω) (m n : MeasurableSpace Ω) (f : Ω → ℝ) : Prop :=
  ∀ t, MeasurableSet[n] t → ν[t.indicator f|m] =ᵐ[ν]
    (ν[f|m])*(ν[t.indicator (fun _ : Ω => (1:ℝ))|m])

private theorem join_generate_intersections (m n : MeasurableSpace Ω) :
    m ⊔ n=MeasurableSpace.generateFrom
      {t | ∃ a b, MeasurableSet[m] a ∧ MeasurableSet[n] b ∧ t=a ∩ b} := by
  apply le_antisymm
  · apply sup_le
    · intro a ha
      exact MeasurableSpace.measurableSet_generateFrom ⟨a,univ,ha,MeasurableSet.univ,by simp⟩
    · intro b hb
      exact MeasurableSpace.measurableSet_generateFrom ⟨univ,b,MeasurableSet.univ,hb,by simp⟩
  · apply MeasurableSpace.generateFrom_le
    rintro t ⟨a,b,ha,hb,rfl⟩
    exact ((show m ≤ m ⊔ n from le_sup_left) a ha).inter
      ((show n ≤ m ⊔ n from le_sup_right) b hb)

private theorem piSystem_intersections (m n : MeasurableSpace Ω) :
    IsPiSystem {t | ∃ a b, MeasurableSet[m] a ∧ MeasurableSet[n] b ∧ t=a ∩ b} := by
  rintro s ⟨a,b,ha,hb,rfl⟩ t ⟨c,d,hc,hd,rfl⟩ _
  refine ⟨a ∩ c,b ∩ d,ha.inter hc,hb.inter hd,?_⟩
  ext x
  simp only [mem_inter_iff,and_assoc,and_left_comm,and_comm]

/-- Conditional independence makes the middle observation sufficient for the
binary posterior, even after observing the last variable as well. -/
theorem posterior_sufficiency_of_markov {m n : MeasurableSpace Ω}
    (hm : m ≤ m₀) (hn : n ≤ m₀) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable[m₀] f ν) (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1)
    (hmark : MarkovFactorization (m₀ := m₀) ν m n f) :
    ν[f|m ⊔ n] =ᵐ[ν] ν[f|m] := by
  letI : MeasurableSpace Ω := m₀
  have hi := integrable_posterior hf hfr
  have hp := conditional_posterior hm hf hfr
  have hbound : ∀ᵐ ω ∂ν, ‖(ν[f|m]) ω‖ ≤ (1:ℝ) := hp.2.1.mono fun ω hω => by
    rw [Real.norm_eq_abs,abs_of_nonneg hω.1]
    exact hω.2
  have hrect : ∀ s t, MeasurableSet[m] s → MeasurableSet[n] t →
      (∫ ω in s ∩ t,(ν[f|m]) ω ∂ν)=(∫ ω in s ∩ t,f ω ∂ν) := by
    intro s t hs ht
    have hti : Integrable (t.indicator (fun _ : Ω => (1:ℝ))) ν :=
      (integrable_const _).indicator (hn t ht)
    have hmul := condExp_stronglyMeasurable_mul_of_bound hm
      (f := ν[f|m]) (g := t.indicator (fun _ : Ω => (1:ℝ)))
      stronglyMeasurable_condExp hti 1 hbound
    have heq : (ν[f|m])*t.indicator (fun _ : Ω => (1:ℝ))=t.indicator (ν[f|m]) := by
      funext ω
      by_cases hω : ω ∈ t <;> simp [hω]
    rw [heq] at hmul
    have he := (hmark t ht).trans hmul.symm
    calc
      (∫ ω in s ∩ t,(ν[f|m]) ω ∂ν)=∫ ω in s,t.indicator (ν[f|m]) ω ∂ν :=
        (setIntegral_indicator (hn t ht)).symm
      _=∫ ω in s,(ν[t.indicator (ν[f|m])|m]) ω ∂ν :=
        (setIntegral_condExp hm (integrable_condExp.indicator (hn t ht)) hs).symm
      _=∫ ω in s,(ν[t.indicator f|m]) ω ∂ν := integral_congr_ae (ae_restrict_of_ae he.symm)
      _=∫ ω in s,t.indicator f ω ∂ν := setIntegral_condExp hm (hi.indicator (hn t ht)) hs
      _=∫ ω in s ∩ t,f ω ∂ν := setIntegral_indicator (hn t ht)
  have hall : ∀ s, MeasurableSet[m ⊔ n] s →
      (∫ ω in s,(ν[f|m]) ω ∂ν)=(∫ ω in s,f ω ∂ν) := by
    apply @MeasurableSpace.induction_on_inter Ω (m ⊔ n)
      (fun s _ => (∫ ω in s,(ν[f|m]) ω ∂ν)=(∫ ω in s,f ω ∂ν))
      _ (join_generate_intersections m n) (piSystem_intersections m n)
    · simp
    · rintro t ⟨a,b,ha,hb,rfl⟩
      exact hrect a b ha hb
    · intro t ht hteq
      rw [setIntegral_compl ((sup_le hm hn) t ht) integrable_condExp,
        setIntegral_compl ((sup_le hm hn) t ht) hi,integral_condExp hm,hteq]
    · intro s hd hs hse
      rw [integral_iUnion (fun i => (sup_le hm hn) _ (hs i)) hd integrable_condExp.integrableOn,
        integral_iUnion (fun i => (sup_le hm hn) _ (hs i)) hd hi.integrableOn]
      exact tsum_congr hse
  exact (ae_eq_condExp_of_forall_setIntegral_eq (sup_le hm hn) hi
    (fun _ _ _ => integrable_condExp.integrableOn) (fun s hs _ => hall s hs)
    ((stronglyMeasurable_condExp (μ := ν) (f := f) (m := m)).mono
      (show m ≤ m ⊔ n from le_sup_left)).aestronglyMeasurable).symm

/-- Shannon and quadratic data processing for a genuine Markov factorization.
All observation spaces and the original probability space may be arbitrary. -/
theorem information_data_processing {m n : MeasurableSpace Ω}
    (hm : m ≤ m₀) (hn : n ≤ m₀) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable[m₀] f ν) (hfr : ∀ᵐ ω ∂ν,f ω ∈ Icc (0:ℝ) 1)
    (hmark : MarkovFactorization (m₀ := m₀) ν m n f) :
    conditionalShannonInformation (m₀ := m₀) ν n f ≤
      conditionalShannonInformation (m₀ := m₀) ν m f ∧
    conditionalQuadraticInformation (m₀ := m₀) ν n f ≤
      conditionalQuadraticInformation (m₀ := m₀) ν m f := by
  letI : MeasurableSpace Ω := m₀
  have he := posterior_sufficiency_of_markov hm hn hf hfr hmark
  have hS := shannonInformation_mono le_sup_right (sup_le hm hn) hf hfr
  have hQ := quadraticInformation_mono le_sup_right (sup_le hm hn) hf hfr
  have hHS : conditionalShannonInformation (m₀ := m₀) ν (m ⊔ n) f=
      conditionalShannonInformation (m₀ := m₀) ν m f := by
    unfold conditionalShannonInformation
    congr 1
    exact integral_congr_ae (he.fun_comp entropyBits)
  have hHQ : conditionalQuadraticInformation (m₀ := m₀) ν (m ⊔ n) f=
      conditionalQuadraticInformation (m₀ := m₀) ν m f := by
    unfold conditionalQuadraticInformation
    congr 1
    exact integral_congr_ae (he.fun_comp quadraticEntropy)
  exact ⟨hS.trans_eq hHS,hQ.trans_eq hHQ⟩

/-- Mathlib's standard conditional-independence predicate implies the event
factorization used above. The standard-Borel assumption here belongs only to
mathlib's definition of `CondIndepFun`; the main data-processing theorem does
not need it. -/
theorem markovFactorization_of_condIndepFun [StandardBorelSpace Ω]
    {W : Type*} [mW : MeasurableSpace W] {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {c : Ω → Bool} {w : Ω → W} (hc : Measurable[m₀] c) (hw : Measurable[m₀] w)
    (hind : CondIndepFun m hm c w ν) :
    MarkovFactorization (m₀ := m₀) ν m (mW.comap w) (fun ω => FiniteLaw.bitValue (c ω)) := by
  letI : MeasurableSpace Ω := m₀
  rintro s ⟨t,ht,rfl⟩
  have h := (condIndepFun_iff_condExp_inter_preimage_eq_mul hc hw).mp hind
    {true} t (measurableSet_singleton true) ht
  have hcEq : (c ⁻¹' {true}).indicator (fun _ : Ω => (1:ℝ))=
      (fun ω => FiniteLaw.bitValue (c ω)) := by
    funext ω
    cases hω : c ω <;> simp [FiniteLaw.bitValue,hω]
  have hprod : (c ⁻¹' {true} ∩ w ⁻¹' t).indicator (fun _ : Ω => (1:ℝ))=
      (w ⁻¹' t).indicator (fun ω => FiniteLaw.bitValue (c ω)) := by
    funext ω
    cases hω : c ω <;> by_cases hwω : w ω ∈ t <;> simp [FiniteLaw.bitValue,hω,hwω]
  simpa only [hprod,hcEq,Pi.mul_apply] using h

/-- The usual binary Markov-chain data-processing inequalities, stated directly
with mathlib's conditional independence and arbitrary measurable output. -/
theorem binary_information_data_processing [StandardBorelSpace Ω]
    {W : Type*} [mW : MeasurableSpace W] {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {c : Ω → Bool} {w : Ω → W} (hc : Measurable[m₀] c) (hw : Measurable[m₀] w)
    (hind : CondIndepFun m hm c w ν) :
    conditionalShannonInformation (m₀ := m₀) ν (mW.comap w) (fun ω => FiniteLaw.bitValue (c ω)) ≤
      conditionalShannonInformation (m₀ := m₀) ν m (fun ω => FiniteLaw.bitValue (c ω)) ∧
    conditionalQuadraticInformation (m₀ := m₀) ν (mW.comap w) (fun ω => FiniteLaw.bitValue (c ω)) ≤
      conditionalQuadraticInformation (m₀ := m₀) ν m (fun ω => FiniteLaw.bitValue (c ω)) := by
  letI : MeasurableSpace Ω := m₀
  apply information_data_processing hm hw.comap_le
    (((measurable_of_countable FiniteLaw.bitValue).comp hc).aestronglyMeasurable)
    _ (markovFactorization_of_condIndepFun hm hc hw hind)
  filter_upwards with ω
  cases hω : c ω <;> norm_num [FiniteLaw.bitValue,hω]

end CourtadeKumar.Posterior
