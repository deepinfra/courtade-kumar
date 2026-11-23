import CK.Latest
import Lean.Util.CollectAxioms

noncomputable section
open scoped BigOperators

namespace IndependentReview

/-- Independently expanded cube sums, probabilities, and bit normalization.
No hypothesis besides 0 ≤ p ≤ 1 is added to the universal Boolean-function claim. -/
theorem rawFiniteSumTarget
    (n : ℕ) (f : (Fin n → Bool) → Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let m : ℝ := (∑ y : Fin n → Bool, if f y then (1 : ℝ) else 0) / (2 : ℝ) ^ n
    let H : ℝ → ℝ := fun r => Real.binEntropy r / Real.log 2
    let I : ℝ := H m - (∑ x : Fin n → Bool,
      H (∑ y : Fin n → Bool,
        (∏ i : Fin n, if x i = y i then 1 - p else p) *
          (if f y then (1 : ℝ) else 0))) / (2 : ℝ) ^ n
    let Q : ℝ := (1 - 2 * p) ^ 2 * H m -
      ((1 - 2 * p) ^ 2 - (1 - H p)) * (4 * m * (1 - m))
    I ≤ Q ∧ Q ≤ 1 - H p := by
  exact CourtadeKumar.latestPaper n f p hp0 hp1

end IndependentReview

#print axioms IndependentReview.rawFiniteSumTarget
#print axioms CourtadeKumar.latestPaper
#print axioms CourtadeKumar.Spec.threeBit
#print axioms CourtadeKumar.classicalCourtadeKumar
#check CourtadeKumar.latestPaper
#check CourtadeKumar.Spec.LatestPaperTarget

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut state : Lean.CollectAxioms.State := {}
  for root in [`IndependentReview.rawFiniteSumTarget, `CourtadeKumar.latestPaper,
      `CourtadeKumar.Spec.threeBit, `CourtadeKumar.classicalCourtadeKumar] do
    let (_, nextState) := ((Lean.CollectAxioms.collect root).run env).run state
    state := nextState
    for ax in state.axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in independent target audit for {root}"
    logInfo m!"INDEPENDENT_AXIOMS_PASSED {root}"
