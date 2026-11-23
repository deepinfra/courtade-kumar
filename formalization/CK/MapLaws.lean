import CK.Markov

/-! # Information quantities under an actual finite pushforward law -/

noncomputable section
namespace CourtadeKumar.FiniteLaw
open scoped BigOperators

variable {Ω V Z : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
  [Fintype Z] [DecidableEq Z]

omit [Fintype Z] [DecidableEq Z] in
theorem expect_map (μ : FiniteLaw Ω) (v : Ω → V) (g : V → ℝ) :
    (μ.map v).expect g = μ.expect (fun ω => g (v ω)) := by
  unfold expect map fibreMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [ite_mul]

omit [Fintype Z] in
theorem fibreMass_map (μ : FiniteLaw Ω) (v : Ω → V) (z : V → Z) (a : Z) :
    (μ.map v).fibreMass z a = μ.fibreMass (fun ω => z (v ω)) a := by
  rw [(μ.map v).fibreMass_eq_expect, μ.expect_map, μ.fibreMass_eq_expect]

omit [Fintype Z] in
theorem fibreMoment_map (μ : FiniteLaw Ω) (v : Ω → V) (z : V → Z) (g : V → ℝ) (a : Z) :
    (μ.map v).fibreMoment z g a = μ.fibreMoment (fun ω => z (v ω)) (fun ω => g (v ω)) a := by
  rw [(μ.map v).fibreMoment_eq_expect, μ.expect_map, μ.fibreMoment_eq_expect]

omit [Fintype Z] in
theorem conditionalMean_map (μ : FiniteLaw Ω) (v : Ω → V) (z : V → Z) (g : V → ℝ) (a : Z) :
    (μ.map v).conditionalMean z g a =
      μ.conditionalMean (fun ω => z (v ω)) (fun ω => g (v ω)) a := by
  unfold conditionalMean
  rw [μ.fibreMass_map, μ.fibreMoment_map]

theorem map_map (μ : FiniteLaw Ω) (v : Ω → V) (z : V → Z) :
    (μ.map v).map z = μ.map (fun ω => z (v ω)) := by
  apply eq_of_mass_eq
  intro a
  exact μ.fibreMass_map v z a

theorem conditionalShannonEntropy_map (μ : FiniteLaw Ω) (v : Ω → V) (z : V → Z) (g : V → ℝ) :
    (μ.map v).conditionalShannonEntropy z g =
      μ.conditionalShannonEntropy (fun ω => z (v ω)) (fun ω => g (v ω)) := by
  unfold conditionalShannonEntropy
  rw [μ.map_map]
  simp_rw [μ.conditionalMean_map]

theorem conditionalQuadraticEntropy_map (μ : FiniteLaw Ω) (v : Ω → V) (z : V → Z) (g : V → ℝ) :
    (μ.map v).conditionalQuadraticEntropy z g =
      μ.conditionalQuadraticEntropy (fun ω => z (v ω)) (fun ω => g (v ω)) := by
  unfold conditionalQuadraticEntropy
  rw [μ.map_map]
  simp_rw [μ.conditionalMean_map]

theorem shannonInformation_map (μ : FiniteLaw Ω) (v : Ω → V) (z : V → Z) (g : V → ℝ) :
    (μ.map v).shannonInformation g z =
      μ.shannonInformation (fun ω => g (v ω)) (fun ω => z (v ω)) := by
  unfold shannonInformation
  rw [μ.expect_map, μ.conditionalShannonEntropy_map]

theorem quadraticInformation_map (μ : FiniteLaw Ω) (v : Ω → V) (z : V → Z) (g : V → ℝ) :
    (μ.map v).quadraticInformation g z =
      μ.quadraticInformation (fun ω => g (v ω)) (fun ω => z (v ω)) := by
  unfold quadraticInformation
  rw [μ.expect_map, μ.conditionalQuadraticEntropy_map]

end CourtadeKumar.FiniteLaw
