import CK.CubeMarkov
import CK.InductionStep
import CK.ChannelEndpoints

/-!
# The exact cube theorem, reduced to the three-bit analytic inequality

All finite-law premises of the induction step are discharged from the actual
uniform product-noise channel.  The lower-dimensional hypothesis is applied
to the two literal coordinate restrictions of the Boolean function.
-/

noncomputable section
namespace CourtadeKumar.Spec

theorem cube_induction_step_of_threeBit (hthree : ThreeBitTarget) {n : ℕ} (hn : 1 ≤ n)
    (f : Cube (n + 1) → Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hIH : ∀ g : Cube n → Bool, mutualInformation g p ≤ progressiveBound p (outputMean g)) :
    mutualInformation f p ≤ progressiveBound p (outputMean f) := by
  obtain ⟨i, hi⟩ := jointLaw_good_coordinate (n := n + 1) (by omega) f p hp0 hp1
  have hdelta := jointLaw_split_conditionalGap_nonneg i f p hp0 hp1 hIH
  have hgap := FiniteLaw.induction_step_of_threeBit hthree
    (jointLaw (n + 1) p hp0 hp1) p (fun xy => xy.1 i) (fun xy => xy.2 i)
    (fun xy => f xy.2) (fun xy => otherCoordinates i xy.1) hp0 hp1
    (jointLaw_independentUnbiased_input i p hp0 hp1)
    (jointLaw_independentUnbiased_output i p hp0 hp1)
    (fun s _ => congrArg abs (jointLaw_conditionOn_correlation i p hp0 hp1 s))
    (fun s _ => jointLaw_conditionOn_markov i f p hp0 hp1 s)
    (jointLaw_markov i f p hp0 hp1) hi hdelta
  rw [jointLaw_split_progressiveGap] at hgap
  exact sub_nonneg.mp hgap

theorem latest_of_threeBit_and_bases (hthree : ThreeBitTarget)
    (hzero : ∀ (f : Cube 0 → Bool) (p : ℝ),
      mutualInformation f p = progressiveBound p (outputMean f))
    (hone : ∀ (f : Cube 1 → Bool) (p : ℝ),
      mutualInformation f p = progressiveBound p (outputMean f)) : LatestPaperTarget := by
  intro n
  induction n with
  | zero =>
    intro f p hp0 hp1
    exact ⟨(hzero f p).le, progressiveBound_le_capacity f hp0 hp1⟩
  | succ n ih =>
    intro f p hp0 hp1
    refine ⟨?_, progressiveBound_le_capacity f hp0 hp1⟩
    cases n with
    | zero => exact (hone f p).le
    | succ n =>
      exact cube_induction_step_of_threeBit hthree (by omega) f p hp0 hp1
        (fun g => (ih g p hp0 hp1).1)

/-- Every other hypothesis of the independently stated latest-paper theorem is discharged. -/
theorem latest_of_threeBit (hthree : ThreeBitTarget) : LatestPaperTarget :=
  latest_of_threeBit_and_bases hthree target_dimension_zero target_dimension_one

theorem classical_of_threeBit (hthree : ThreeBitTarget) : ClassicalTarget :=
  classical_of_latest (latest_of_threeBit hthree)

end CourtadeKumar.Spec
