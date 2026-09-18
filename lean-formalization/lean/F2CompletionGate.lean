import CK
import CKF2.Spec

-- THIS GATE IS EXPECTED TO FAIL WITH THE PRESENT PARTIAL DRAFT.
-- CK.courtadeKumar_proved has not been written or verified.
set_option autoImplicit false

/-- No unproved branch, scalar, curvature, Fourier, or logarithm hypotheses. -/
theorem CKF2.exactTargetAccepted : CKF2.Spec.Target := by
  change CK.CourtadeKumar
  exact CK.courtadeKumar_proved

#print CKF2.exactTargetAccepted
#print axioms CKF2.exactTargetAccepted
