import CKLatest
import Lean.Util.CollectAxioms

open Lean Elab Command

/-!
Audit all safe project declarations, including private helpers and every theorem.
Selection is by source module, rather than by declaration namespace. Lean's compiler
also emits unsafe implementation helpers (e.g. `_cstage1`, `_elambda_1`) that
are not proof terms and cannot occur in safe kernel proofs. Source-level unsafe
declarations are independently prohibited by `verify.py`; no helper axiom is
added to the permitted axiom list.
-/
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut state : Lean.CollectAxioms.State := {}
  let mut count := 0
  let mut theoremCount := 0
  let mut unsafeCount := 0
  for moduleName in env.header.moduleNames do
    if moduleName == `CKLatest || (`CK).isPrefixOf moduleName then
      logInfo m!"CK_AUDITED_MODULE {moduleName}"
  for (name, info) in env.constants.toList do
    let module? := (env.getModuleIdxFor? name).bind fun i => env.header.moduleNames[i.toNat]?
    let selected := match module? with
      | some moduleName => moduleName == `CKLatest || (`CK).isPrefixOf moduleName
      | none => false
    if selected then
      if info.isUnsafe then
        unsafeCount := unsafeCount + 1
        logInfo m!"CK_EXCLUDED_UNSAFE_COMPILER_ARTIFACT {name}"
      else
        -- Sharing the visited set avoids re-walking mathlib for every theorem.
        -- The cumulative union is checked after each root; it is not presented
        -- as the exact minimal axiom set of an individual theorem.
        let (_, nextState) := ((Lean.CollectAxioms.collect name).run env).run state
        state := nextState
        for ax in state.axioms do
          unless allowed.contains ax do
            throwError "Unapproved transitive axiom {ax} reached while auditing {name}"
        count := count + 1
        if info matches .thmInfo _ then
          theoremCount := theoremCount + 1
          logInfo m!"CK_THEOREM {name} TRANSITIVE_AXIOMS_SUBSET_OF {allowed}"
  logInfo m!"CK_AUDIT_DECLARATIONS {count}"
  logInfo m!"CK_AUDIT_THEOREMS {theoremCount}"
  logInfo m!"CK_AUDIT_UNSAFE_COMPILER_ARTIFACTS {unsafeCount}"
  logInfo m!"CK_AUDIT_TRANSITIVE_AXIOM_UNION {state.axioms.toList}"
  logInfo m!"CK_LATEST_TARGET_DECLARED {env.contains `CourtadeKumar.latestPaper}"

#print CourtadeKumar.Spec.LatestPaperTarget
#print CourtadeKumar.Spec.ClassicalTarget
#print CourtadeKumar.Spec.ThreeBitTarget
