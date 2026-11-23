import CK.ProfileSeries
import CK.FiniteProbability

/-! The exact equality cases in the manuscript's Shannon/Tsallis comparison. -/

noncomputable section
namespace CourtadeKumar

theorem Spec.divergence_lt_square {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| < 1) :
    Spec.divergence t < t ^ 2 := by
  have hq0 : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
  have hq1 : t ^ 2 < 1 := by
    have hm := mul_pos (by linarith [(abs_lt.mp ht1).1] : 0 < 1 + t)
      (by linarith [(abs_lt.mp ht1).2] : 0 < 1 - t)
    nlinarith
  have h := Scalar.alpha_pos hq0 hq1
  rw [Scalar.alpha_eq_paper ht1] at h
  have hp : 0 < (t ^ 2 - Spec.divergence t) * Real.log 2 :=
    (div_pos_iff_of_pos_right (sub_pos.mpr hq1)).mp h
  exact sub_pos.mp ((mul_pos_iff_of_pos_right log_two_pos).mp hp)

theorem Spec.divergence_eq_square_iff {t : ℝ} (ht : |t| ≤ 1) :
    Spec.divergence t = t ^ 2 ↔ t = -1 ∨ t = 0 ∨ t = 1 := by
  constructor
  · intro he
    by_cases hz : t = 0
    · exact Or.inr (Or.inl hz)
    have heabs : |t| = 1 := by
      by_contra hn
      have hlt := Spec.divergence_lt_square hz (lt_of_le_of_ne ht hn)
      linarith
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp heabs with hp | hm
    · exact Or.inr (Or.inr hp)
    · exact Or.inl hm
  · rintro (rfl | rfl | rfl) <;> norm_num [Spec.divergence_even]

theorem quadraticEntropy_lt_entropyBits {μ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hμhalf : μ ≠ 1 / 2) :
    quadraticEntropy μ < entropyBits μ := by
  have ht0 : 2 * μ - 1 ≠ 0 := by intro h; apply hμhalf; linarith
  have ht1 : |2 * μ - 1| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have h := Spec.divergence_lt_square ht0 ht1
  have he : Spec.divergence (2 * μ - 1) = 1 - entropyBits μ := by
    change 1 - entropyBits ((1 + (2 * μ - 1)) / 2) = _
    congr 2
    ring
  rw [he] at h
  unfold quadraticEntropy
  nlinarith

theorem quadraticEntropy_eq_entropyBits_iff {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    quadraticEntropy μ = entropyBits μ ↔ μ = 0 ∨ μ = 1 / 2 ∨ μ = 1 := by
  constructor
  · intro he
    by_cases hz : μ = 0
    · exact Or.inl hz
    by_cases ho : μ = 1
    · exact Or.inr (Or.inr ho)
    by_cases hh : μ = 1 / 2
    · exact Or.inr (Or.inl hh)
    have h := quadraticEntropy_lt_entropyBits
      (lt_of_le_of_ne hμ0 (Ne.symm hz)) (lt_of_le_of_ne hμ1 ho) hh
    linarith
  · rintro (rfl | rfl | rfl) <;> norm_num [quadraticEntropy, entropyBits_half]

end CourtadeKumar
