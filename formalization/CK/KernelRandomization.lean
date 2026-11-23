import CK.FiniteKernel
import CK.KernelInformationBasic
import CK.RandomizedComparator

/-!
# Private comparison randomness over arbitrary observation spaces

A measurable finite-output kernel is extended by the same independent BSC noise
in every fibre. Both the original conditional laws and their marginal mixture
are preserved. The factorization of moments includes arbitrary functions of the
observation and the original output.
-/

noncomputable section
namespace CourtadeKumar.KernelInformation.FiniteKernel
open Set MeasureTheory Filter
open scoped BigOperators

variable {U Γ : Type*} [MeasurableSpace U] [Fintype Γ]

/-- Adjoin one independent private flip bit to every conditional finite law. -/
def comparatorExtension (K : FiniteKernel U Γ) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    FiniteKernel U (Γ × Bool) where
  law u := (K.law u).comparatorExtension τ hτ0 hτ1
  measurable_mass p := (K.measurable_mass p.1).mul_const _

/-- Every original conditional law is preserved, including on null fibres. -/
theorem comparatorExtension_map_fst (K : FiniteKernel U Γ) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) [DecidableEq Γ] (u : U) :
    ((K.comparatorExtension τ hτ0 hτ1).law u).map Prod.fst = K.law u :=
  (K.law u).comparatorExtension_map_fst τ hτ0 hτ1

/-- Mixture and independent private randomization commute exactly. -/
theorem mixture_comparatorExtension (K : FiniteKernel U Γ) (ν : Measure U)
    [IsProbabilityMeasure ν] (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (K.comparatorExtension τ hτ0 hτ1).mixture ν =
      (K.mixture ν).comparatorExtension τ hτ0 hτ1 := by
  apply FiniteLaw.eq_of_mass_eq
  intro p
  change (∫ u, (K.law u).mass p.1 * (FiniteLaw.comparatorNoise τ hτ0 hτ1).mass p.2 ∂ν) =
    (∫ u, (K.law u).mass p.1 ∂ν) * (FiniteLaw.comparatorNoise τ hτ0 hτ1).mass p.2
  exact integral_mul_const _ _

/-- Private randomness is independent of the observation and all original outputs.
The original observable may depend on the arbitrary observation `u`. -/
theorem comparatorExtension_integral_independent_noise (K : FiniteKernel U Γ)
    (ν : Measure U) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (g : U → Γ → ℝ) (f : Bool → ℝ) :
    (∫ u, ((K.comparatorExtension τ hτ0 hτ1).law u).expect
      (fun p => g u p.1 * f p.2) ∂ν) =
    (∫ u, (K.law u).expect (g u) ∂ν) *
      (FiniteLaw.comparatorNoise τ hτ0 hτ1).expect f := by
  simp only [comparatorExtension, FiniteLaw.comparatorExtension_independent_noise]
  exact integral_mul_const _ _

/-- The generated comparison bit depends on all original outputs only through `b`. -/
theorem comparatorExtension_markov (K : FiniteKernel U Γ) (b : Γ → Bool) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) [DecidableEq Γ] (u : U) :
    ((K.comparatorExtension τ hτ0 hτ1).law u).conditionallyIndependentBit
      (FiniteLaw.comparatorBit b) Prod.fst (fun p => b p.1) :=
  (K.law u).comparatorExtension_markov b τ hτ0 hτ1 id

/-- The signed correlation of two original bits averages under an arbitrary observation law. -/
theorem bitCorrelation_mixture (K : FiniteKernel U Γ) (ν : Measure U)
    [IsProbabilityMeasure ν] (a b : Γ → Bool) :
    (K.mixture ν).bitCorrelation a b = ∫ u, (K.law u).bitCorrelation a b ∂ν :=
  K.expect_mixture ν _

/-- An unbiased conditional bit remains unbiased after integrating over the observation. -/
theorem mixture_unbiased (K : FiniteKernel U Γ) (ν : Measure U)
    [IsProbabilityMeasure ν] (a : Γ → Bool)
    (ha : ∀ᵐ u ∂ν, (K.law u).expect (fun s => FiniteLaw.bitValue (a s)) = 1 / 2) :
    (K.mixture ν).expect (fun s => FiniteLaw.bitValue (a s)) = 1 / 2 := by
  rw [K.expect_mixture ν]
  calc
    _ = ∫ _, (1 / 2 : ℝ) ∂ν := integral_congr_ae ha
    _ = _ := by simp

/-- A fixed signed conditional channel has that same signed correlation marginally. -/
theorem mixture_fixed_correlation (K : FiniteKernel U Γ) (ν : Measure U)
    [IsProbabilityMeasure ν] (a b : Γ → Bool) {γ : ℝ}
    (hγ : ∀ᵐ u ∂ν, (K.law u).bitCorrelation a b = γ) :
    (K.mixture ν).bitCorrelation a b = γ := by
  rw [K.bitCorrelation_mixture ν]
  calc
    _ = ∫ _, γ ∂ν := integral_congr_ae hγ
    _ = _ := by simp

end CourtadeKumar.KernelInformation.FiniteKernel
