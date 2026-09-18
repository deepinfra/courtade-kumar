import CK.Definitions

/-!
# Outstanding analytic goals -- UNCOMPILED DEFINITIONS, NOT THEOREMS

Each item below is a proposition describing unfinished work. None is declared
as an axiom, and no subsequent theorem is allowed to silently use it.
-/
noncomputable section
namespace CK
open scoped BigOperators

-- Use a logarithmic definition to keep the atanh convention explicit.
def atanhLog (u : ℝ) : ℝ := (Real.log (1 + u) - Real.log (1 - u)) / 2

def curvature (u : ℝ) : ℝ := 1 / (1 - u ^ 2)

def curvatureGap (x y : ℝ) : ℝ :=
  (eta x + eta y) * (curvature y - curvature x) -
  (atanhLog y ^ 2 - atanhLog x ^ 2)

def CurvatureGoal : Prop :=
  ∀ x y : ℝ, 0 ≤ x → x ≤ y → y < 1 → 0 ≤ curvatureGap x y

def pairEntropy (nu z : ℝ) : ℝ := (eta (nu + z) + eta (nu - z)) / 2

def ProductCenteringGoal : Prop :=
  ∀ p nu t : ℝ,
    0 < p → p < 1 / 2 → 0 ≤ nu → 0 ≤ t → nu + t ≤ 1 →
    let J := pairEntropy nu t
    let M := pairEntropy nu ((1 - 2 * p) * t)
    let J0 := eta t
    let M0 := eta ((1 - 2 * p) * t)
    M0 - J0 ≤ M - J ∧ (M0 - J0) * M0 ≤ (M - J) * M

def logPartial (N : ℕ) (v : ℝ) : ℝ :=
  let z := (v - 1) / (v + 1)
  2 * ∑ j ∈ Finset.range N, z ^ (2 * j + 1) / (2 * (j : ℝ) + 1)

def logTail (N : ℕ) (v : ℝ) : ℝ :=
  let z := (v - 1) / (v + 1)
  2 * z ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - z ^ 2))

/-- Precisely the missing transcendental link for all 38 log-interval queries. -/
def LogEnclosureGoal : Prop :=
  ∀ (N : ℕ) (v : ℝ), 0 < N → 1 ≤ v → v ≤ 2 →
    logPartial N v ≤ Real.log v ∧
    Real.log v ≤ logPartial N v + logTail N v

def psi (rho t : ℝ) : ℝ := (1 - t) * (1 + t - rho ^ 2)
def lambdaDenom (rho : ℝ) : ℝ := 1 + rho - (31 / 40 : ℝ) * rho ^ 2

def EntropyComparisonGoal : Prop :=
  ∀ rho t : ℝ, 3 / 5 ≤ rho → rho ≤ 9 / 10 → 0 ≤ t → t ≤ 1 →
    eta rho / ((1 - rho) * lambdaDenom rho) * psi rho t ≤ eta t

def StrictAnchorGoal : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (39 / 40 : ℝ) * psi (3 / 5) t ≤ eta t

/-- Remaining tasks also include formal finite-channel semantics,
character orthogonality, the sign-sum moment induction, and uniform-reference
contraction. The real-algebra portfolio does not replace those tasks. -/
def ProbabilityKernelGoal : Prop :=
  ∀ (n : ℕ) (p : ℝ) (y : Cube n), 0 ≤ p → p ≤ 1 →
    (∑ x : Cube n, kernel p y x) = 1

end CK
