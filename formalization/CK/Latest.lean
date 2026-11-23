import CK.CubeInduction
import CK.ScalarThreeBit

/-!
# The latest Courtade–Kumar main theorem

These declarations prove the independently specified finite product-channel
targets for every dimension, every Boolean function, and every noise parameter
in the closed interval `[0,1]`.  Every scalar and probabilistic prerequisite is
provided by a proved declaration in the import graph.
-/

namespace CourtadeKumar

/-- The stronger main theorem of the pinned November 20 manuscript. -/
theorem latestPaper : Spec.LatestPaperTarget :=
  Spec.latest_of_threeBit Spec.threeBit

/-- The classical Courtade–Kumar information bound, as a corollary. -/
theorem classicalCourtadeKumar : Spec.ClassicalTarget :=
  Spec.classical_of_latest latestPaper

end CourtadeKumar
