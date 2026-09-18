import CK.Definitions

/-!
# Independently spelled-out challenge -- NOT COMPILED IN THE PREPARING SESSION

This freezes the intended finite-sum statement independently of the name
CK.CourtadeKumar. It is not an independent development of probability theory.
The equality at the bottom checks definitional agreement, not the theorem.
No custom theorem of entropy or CK is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace CKF2.Spec
open scoped BigOperators

abbrev BitVector (n : ℕ) := Fin n → Bool

def bitValue (b : Bool) : ℝ := if b then 1 else 0

def entropy (x : ℝ) : ℝ :=
  -x * Real.log x - (1 - x) * Real.log (1 - x)

def average {n : ℕ} (g : BitVector n → ℝ) : ℝ :=
  (∑ x : BitVector n, g x) / (2 : ℝ) ^ n

def channel {n : ℕ} (p : ℝ) (y x : BitVector n) : ℝ :=
  ∏ i : Fin n, if y i = x i then 1 - p else p

def outputMean {n : ℕ} (f : BitVector n → Bool) : ℝ :=
  average (fun x => bitValue (f x))

def outputPosterior {n : ℕ} (f : BitVector n → Bool) (p : ℝ)
    (y : BitVector n) : ℝ :=
  ∑ x : BitVector n, channel p y x * bitValue (f x)

def retainedInformation {n : ℕ} (f : BitVector n → Bool) (p : ℝ) : ℝ :=
  entropy (outputMean f) - average (fun y => entropy (outputPosterior f p y))

/-- Every finite dimension, every Boolean function, every allowed noise;
    no balance, Fourier, induction, or analytic hypothesis. -/
def Target : Prop :=
  ∀ (n : ℕ) (f : BitVector n → Bool) (p : ℝ),
    0 ≤ p → p ≤ 1 / 2 → retainedInformation f p ≤ Real.log 2 - entropy p

/-- Definitional correspondence ONLY; this does not establish Target. -/
theorem matches_f1_target : Target = CK.CourtadeKumar := by
  rfl

end CKF2.Spec
