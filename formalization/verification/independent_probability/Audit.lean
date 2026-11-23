import CK.PosteriorMarkov
import CK.ConditionalKernel
import CK.ThresholdModel
import CK.MatchingComparator
import CK.QuantitativeInduction
import Lean.Util.CollectAxioms

#print axioms CourtadeKumar.Posterior.conditional_jensen_concave
#print axioms CourtadeKumar.Posterior.conditional_pinsker
#print axioms CourtadeKumar.Posterior.posterior_sufficiency_of_markov
#print axioms CourtadeKumar.Posterior.information_data_processing
#print axioms CourtadeKumar.Posterior.binary_information_data_processing
#print axioms CourtadeKumar.KernelInformation.conditionalKernel_expect_ae
#print axioms CourtadeKumar.KernelInformation.conditionalKernel_bit_unbiased
#print axioms CourtadeKumar.Threshold.progressiveEntropy_eq_kernelInformation_iff
#print axioms CourtadeKumar.FiniteLaw.every_matching_comparator
#print axioms CourtadeKumar.FiniteLaw.quantitative_induction_step

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots := [
    `CourtadeKumar.Posterior.conditional_jensen_concave,
    `CourtadeKumar.Posterior.conditional_pinsker,
    `CourtadeKumar.Posterior.posterior_sufficiency_of_markov,
    `CourtadeKumar.Posterior.information_data_processing,
    `CourtadeKumar.Posterior.binary_information_data_processing,
    `CourtadeKumar.KernelInformation.conditionalKernel_expect_ae,
    `CourtadeKumar.KernelInformation.conditionalKernel_bit_unbiased,
    `CourtadeKumar.Threshold.progressiveEntropy_eq_kernelInformation_iff,
    `CourtadeKumar.FiniteLaw.every_matching_comparator,
    `CourtadeKumar.FiniteLaw.quantitative_induction_step]
  let mut state : Lean.CollectAxioms.State := {}
  for root in roots do
    unless env.contains root do
      throwError "Missing probability audit root {root}"
    let (_, nextState) := ((Lean.CollectAxioms.collect root).run env).run state
    state := nextState
    for ax in state.axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in independent probability audit for {root}"
    logInfo m!"INDEPENDENT_PROBABILITY_AXIOMS_PASSED {root}"
