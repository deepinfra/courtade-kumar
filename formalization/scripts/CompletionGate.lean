import CKLatest

/-!
This file is intentionally outside the default library target. The full gate
must fail until a theorem with this exact independent type has been proved.
Do not replace the proof with a hypothesis or weaken the specification.
-/

example : CourtadeKumar.Spec.LatestPaperTarget := CourtadeKumar.latestPaper

#print axioms CourtadeKumar.latestPaper
