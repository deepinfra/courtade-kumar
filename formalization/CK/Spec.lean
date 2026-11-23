import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!+# Independently spelled specification of the November 20 manuscript

All entropies in this specification are in bits. The Boolean function is arbitrary;
the product binary symmetric channel is written as a finite sum, with no assumed
information inequality. `LatestPaperTarget` is a proposition, not a theorem.

Source: deepinfra/courtade-kumar, commit
45ad4866a41e04722f2cfcef4129a1050e59d3ca, Theorem `thm:ck+`.
-/

noncomputable section
namespace CourtadeKumar.Spec
open scoped BigOperators

abbrev Cube (n : ℕ) := Fin n → Bool

def bit (b : Bool) : ℝ := if b then 1 else 0

def average {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  (∑ x : Cube n, f x) / (2 : ℝ) ^ n

def entropy (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

def channel {n : ℕ} (p : ℝ) (x y : Cube n) : ℝ :=
  ∏ i : Fin n, if x i = y i then 1 - p else p

def outputMean {n : ℕ} (f : Cube n → Bool) : ℝ :=
  average (fun y => bit (f y))

/-- `P(f(Y)=1 | X=x)` for uniform X and independent flips of probability p. -/
def outputPosterior {n : ℕ} (f : Cube n → Bool) (p : ℝ) (x : Cube n) : ℝ :=
  ∑ y : Cube n, channel p x y * bit (f y)

def mutualInformation {n : ℕ} (f : Cube n → Bool) (p : ℝ) : ℝ :=
  entropy (outputMean f) - average (fun x => entropy (outputPosterior f p x))

def progressiveBound (p μ : ℝ) : ℝ :=
  (1 - 2 * p) ^ 2 * entropy μ -
    ((1 - 2 * p) ^ 2 - (1 - entropy p)) * (4 * μ * (1 - μ))

/-- Exact stronger main theorem, for every dimension and the full noise interval. -/
def LatestPaperTarget : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ), 0 ≤ p → p ≤ 1 →
    mutualInformation f p ≤ progressiveBound p (outputMean f) ∧
    progressiveBound p (outputMean f) ≤ 1 - entropy p

/-- The classical conclusion alone is deliberately a separate proposition. -/
def ClassicalTarget : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ), 0 ≤ p → p ≤ 1 →
    mutualInformation f p ≤ 1 - entropy p

def divergence (t : ℝ) : ℝ := 1 - entropy ((1 + t) / 2)

/-- The nondegenerate scalar target in equation `three-bit-scalar-target`. -/
def ThreeBitTarget : Prop :=
  ∀ (ρ σ : ℝ), 0 < ρ → ρ < 1 → 0 < σ → σ ≤ 1 →
    ρ ^ 2 - divergence ρ <
      (divergence ρ - divergence (ρ * σ)) /
        (2 * (1 + (ρ ^ 2 - divergence ρ) * Real.log 2 / (1 - ρ ^ 2))) +
      2 * (ρ ^ 2 * divergence σ - divergence (ρ * σ)) / σ

/-- The biased binary information profile from `comparison-calculus`. -/
def binaryProfile (x d : ℝ) : ℝ :=
  (1 + x) / 2 * divergence (d / (1 + x)) +
    (1 - x) / 2 * divergence (d / (1 - x))

/-- The pointwise matching construction; conditional averaging is a further obligation. -/
def PointwiseComparisonTarget : Prop :=
  ∀ (ρ x d : ℝ), 0 ≤ ρ → ρ ≤ 1 → |x| < 1 → |x| + |d| ≤ 1 →
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 ∧
      binaryProfile x d = (1 - x ^ 2) * divergence τ ∧
      binaryProfile x (ρ * d) ≤ (1 - x ^ 2) * divergence (ρ * τ) ∧
      |d| ≤ 1 - x ^ 2 ∧
      (1 - x ^ 2) * divergence (d / (1 - x ^ 2)) ≤ binaryProfile x d

end CourtadeKumar.Spec
