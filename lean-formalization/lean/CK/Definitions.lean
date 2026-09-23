import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Exact target definitions -- UNCOMPILED SOURCE DRAFT

No Lean executable or mathlib installation was available during this run.
These definitions and scripts have NOT been accepted by a Lean kernel.
They do not import the native Z3 results as Lean axioms.

The finite model uses Bool instead of {-1,+1}; this is only a relabelling.
All entropies are in nats. The definition of the target is deliberately separate
from conditional algebra lemmas. There is no theorem here asserting the target.
-/

noncomputable section
namespace CK
open scoped BigOperators

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev BooleanFunction (n : ℕ) := Cube n → Bool

def indicator (b : Bool) : ℝ := if b then 1 else 0

def sign (b : Bool) : ℝ := if b then 1 else -1

def avg {n : ℕ} (v : Cube n → ℝ) : ℝ :=
  (∑ x : Cube n, v x) / (2 : ℝ) ^ n

def kernel {n : ℕ} (p : ℝ) (y x : Cube n) : ℝ :=
  ∏ i : Fin n, if y i = x i then 1 - p else p

def binaryEntropy (p : ℝ) : ℝ :=
  -p * Real.log p - (1 - p) * Real.log (1 - p)

def eta (u : ℝ) : ℝ := binaryEntropy ((1 + u) / 2)

def kappa (u : ℝ) : ℝ := Real.log 2 - eta u

def mean {n : ℕ} (f : BooleanFunction n) : ℝ :=
  avg (fun x => indicator (f x))

/-- The formula is the uniform-input posterior because the BSC is symmetric
and doubly stochastic. Establishing that semantic fact is an outstanding task. -/
def posterior {n : ℕ} (f : BooleanFunction n) (p : ℝ) (y : Cube n) : ℝ :=
  ∑ x : Cube n, kernel p y x * indicator (f x)

def conditionalEntropy {n : ℕ} (f : BooleanFunction n) (p : ℝ) : ℝ :=
  avg (fun y => binaryEntropy (posterior f p y))

def information {n : ℕ} (f : BooleanFunction n) (p : ℝ) : ℝ :=
  binaryEntropy (mean f) - conditionalEntropy f p

def varianceProfile (a : ℝ) : ℝ := 4 * a * (1 - a)

def mixedEntropy (p a b : ℝ) : ℝ :=
  (binaryEntropy ((1 - p) * a + p * b) +
   binaryEntropy (p * a + (1 - p) * b)) / 2

def scalarSlack (p d a b : ℝ) : ℝ :=
  (1 + d ^ 2) * mixedEntropy p a b -
    (binaryEntropy a + binaryEntropy b) / 2 -
    2 * d * binaryEntropy p * |a - b|

/-- The exact core target. This is a definition of a proposition, NOT a proof. -/
def CourtadeKumar : Prop :=
  ∀ (n : ℕ) (f : BooleanFunction n) (p : ℝ),
    0 ≤ p → p ≤ 1 / 2 → information f p ≤ Real.log 2 - binaryEntropy p

/-- Main scalar target from v9.1 Lemma 2.1, not assumed as a global axiom. -/
def ScalarMixingClaim : Prop :=
  ∀ p a b d : ℝ,
    0 < p → p ≤ 1 / 20 →
    0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → 0 ≤ d → d ≤ 1 / 2 →
    p ^ 2 / 25 * (a - b) ^ 2 ≤ scalarSlack p d a b

/-- Optional stronger target in Appendix G. -/
def LinearScalarMixingClaim : Prop :=
  ∀ p a b d : ℝ,
    0 < p → p ≤ 1 / 20 →
    0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → 0 ≤ d → d ≤ 1 / 2 →
    p / 500 * (a - b) ^ 2 ≤ scalarSlack p d a b

def LowNoiseProfileClaim : Prop :=
  ∀ (n : ℕ) (f : BooleanFunction n) (p : ℝ),
    0 ≤ p → p ≤ 1 / 20 →
    varianceProfile (mean f) * binaryEntropy p ≤ conditionalEntropy f p

def lowNoiseCK : Prop :=
  ∀ (n : ℕ) (f : BooleanFunction n) (p : ℝ),
    0 ≤ p → p ≤ 1 / 20 → information f p ≤ Real.log 2 - binaryEntropy p

def complementaryCK : Prop :=
  ∀ (n : ℕ) (f : BooleanFunction n) (p : ℝ),
    1 / 20 ≤ p → p ≤ 1 / 2 → information f p ≤ Real.log 2 - binaryEntropy p

/-- Only assembly; neither branch is proved or smuggled in as an axiom. -/
theorem assemble_conditional (low : lowNoiseCK) (high : complementaryCK) :
    CourtadeKumar := by
  intro n f p hp0 hp1
  by_cases h : p ≤ 1 / 20
  · exact low n f p hp0 h
  · exact high n f p (le_of_lt (lt_of_not_ge h)) hp1

/-- Empty points are independent of their unused coordinate arguments. -/
theorem indicator_square (b : Bool) : indicator b ^ 2 = indicator b := by
  cases b <;> norm_num [indicator]

theorem sign_square (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

theorem entropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy]

theorem entropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy]

end CK
