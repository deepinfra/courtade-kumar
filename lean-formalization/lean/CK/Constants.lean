import CK.LogEnclosure

/-!
# Appendix F: the rational constants, discharged from `CK.logEnclosure_proved`

Every lemma below is an instantiation of the kernel-checked series enclosure
(`LogEnclosureGoal`, N = 12) plus the splitting `log (2^k * r) = k*log 2 + log r`.
The published brackets sit on a 10^-12 grid strictly outside the exact N = 12
enclosure and strictly inside every downstream margin; all comparisons were
re-verified in exact rational arithmetic at emission time.
-/
noncomputable section
namespace CK
namespace AppF

theorem log_q2 : (346573590279 / 500000000000 : ℝ) < Real.log (2 : ℝ) ∧ Real.log (2 : ℝ) < (693147180561 / 1000000000000 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := logEnclosure_proved 12 (2 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · calc (346573590279 / 500000000000 : ℝ) < logPartial 12 (2 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
      _ ≤ Real.log (2 : ℝ) := hlo
  · calc Real.log (2 : ℝ) ≤ logPartial 12 (2 : ℝ) + logTail 12 (2 : ℝ) := hhi
      _ < (693147180561 / 1000000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]

theorem log_q3 : (219722457733 / 200000000000 : ℝ) < Real.log (3 : ℝ) ∧ Real.log (3 : ℝ) < (1098612288671 / 1000000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (3 / 2 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (405465108107 / 1000000000000 : ℝ) < logPartial 12 (3 / 2 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (3 / 2 : ℝ) + logTail 12 (3 / 2 : ℝ) < (40546510811 / 100000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (3 : ℝ) = 1 * Real.log 2 + Real.log (3 / 2 : ℝ) := by
    rw [show (3 : ℝ) = 2 ^ 1 * (3 / 2 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q20 : (599146454709 / 200000000000 : ℝ) < Real.log (20 : ℝ) ∧ Real.log (20 : ℝ) < (74893306839 / 25000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (5 / 4 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (223143551313 / 1000000000000 : ℝ) < logPartial 12 (5 / 4 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (5 / 4 : ℝ) + logTail 12 (5 / 4 : ℝ) < (55785887829 / 250000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (20 : ℝ) = 4 * Real.log 2 + Real.log (5 / 4 : ℝ) := by
    rw [show (20 : ℝ) = 2 ^ 4 * (5 / 4 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q50_3 : (2813410716751 / 1000000000000 : ℝ) < Real.log (50 / 3 : ℝ) ∧ Real.log (50 / 3 : ℝ) < (1406705358383 / 500000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (25 / 24 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (40821994519 / 1000000000000 : ℝ) < logPartial 12 (25 / 24 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (25 / 24 : ℝ) + logTail 12 (25 / 24 : ℝ) < (20410997261 / 500000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (50 / 3 : ℝ) = 4 * Real.log 2 + Real.log (25 / 24 : ℝ) := by
    rw [show (50 / 3 : ℝ) = 2 ^ 4 * (25 / 24 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q459_250 : (607589292197 / 1000000000000 : ℝ) < Real.log (459 / 250 : ℝ) ∧ Real.log (459 / 250 : ℝ) < (3037946461 / 5000000000 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := logEnclosure_proved 12 (459 / 250 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · calc (607589292197 / 1000000000000 : ℝ) < logPartial 12 (459 / 250 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
      _ ≤ Real.log (459 / 250 : ℝ) := hlo
  · calc Real.log (459 / 250 : ℝ) ≤ logPartial 12 (459 / 250 : ℝ) + logTail 12 (459 / 250 : ℝ) := hhi
      _ < (3037946461 / 5000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]

theorem log_q59_21 : (1033015006179 / 1000000000000 : ℝ) < Real.log (59 / 21 : ℝ) ∧ Real.log (59 / 21 : ℝ) < (206603001237 / 200000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (59 / 42 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (339867825621 / 1000000000000 : ℝ) < logPartial 12 (59 / 42 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (59 / 42 : ℝ) + logTail 12 (59 / 42 : ℝ) < (42483478203 / 125000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (59 / 21 : ℝ) = 1 * Real.log 2 + Real.log (59 / 42 : ℝ) := by
    rw [show (59 / 21 : ℝ) = 2 ^ 1 * (59 / 42 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q137_23 : (892243354947 / 500000000000 : ℝ) < Real.log (137 / 23 : ℝ) ∧ Real.log (137 / 23 : ℝ) < (1784486709903 / 1000000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (137 / 92 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (199096174389 / 500000000000 : ℝ) < logPartial 12 (137 / 92 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (137 / 92 : ℝ) + logTail 12 (137 / 92 : ℝ) < (398192348781 / 1000000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (137 / 23 : ℝ) = 2 * Real.log 2 + Real.log (137 / 92 : ℝ) := by
    rw [show (137 / 23 : ℝ) = 2 ^ 2 * (137 / 92 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q22_3 : (398486032937 / 200000000000 : ℝ) < Real.log (22 / 3 : ℝ) ∧ Real.log (22 / 3 : ℝ) < (996215082347 / 500000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (11 / 6 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (606135803569 / 1000000000000 : ℝ) < logPartial 12 (11 / 6 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (11 / 6 : ℝ) + logTail 12 (11 / 6 : ℝ) < (151533950893 / 250000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (22 / 3 : ℝ) = 2 * Real.log 2 + Real.log (11 / 6 : ℝ) := by
    rw [show (22 / 3 : ℝ) = 2 ^ 2 * (11 / 6 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q899_101 : (2186162517623 / 1000000000000 : ℝ) < Real.log (899 / 101 : ℝ) ∧ Real.log (899 / 101 : ℝ) < (437232503527 / 200000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (899 / 808 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (106720975949 / 1000000000000 : ℝ) < logPartial 12 (899 / 808 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (899 / 808 : ℝ) + logTail 12 (899 / 808 : ℝ) < (6670060997 / 62500000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (899 / 101 : ℝ) = 3 * Real.log 2 + Real.log (899 / 808 : ℝ) := by
    rw [show (899 / 101 : ℝ) = 2 ^ 3 * (899 / 808 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q459_41 : (2415478143349 / 1000000000000 : ℝ) < Real.log (459 / 41 : ℝ) ∧ Real.log (459 / 41 : ℝ) < (2415478143361 / 1000000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (459 / 328 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (13441464067 / 40000000000 : ℝ) < logPartial 12 (459 / 328 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (459 / 328 : ℝ) + logTail 12 (459 / 328 : ℝ) < (168018300839 / 500000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (459 / 41 : ℝ) = 3 * Real.log 2 + Real.log (459 / 328 : ℝ) := by
    rw [show (459 / 41 : ℝ) = 2 ^ 3 * (459 / 328 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q199_60 : (1198960262499 / 1000000000000 : ℝ) < Real.log (199 / 60 : ℝ) ∧ Real.log (199 / 60 : ℝ) < (239792052501 / 200000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (199 / 120 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (505813081941 / 1000000000000 : ℝ) < logPartial 12 (199 / 120 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (199 / 120 : ℝ) + logTail 12 (199 / 120 : ℝ) < (63226635243 / 125000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (199 / 60 : ℝ) = 1 * Real.log 2 + Real.log (199 / 120 : ℝ) := by
    rw [show (199 / 60 : ℝ) = 2 ^ 1 * (199 / 120 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q127_40 : (1155307632341 / 1000000000000 : ℝ) < Real.log (127 / 40 : ℝ) ∧ Real.log (127 / 40 : ℝ) < (1155307632347 / 1000000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (127 / 80 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (462160451783 / 1000000000000 : ℝ) < logPartial 12 (127 / 80 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (127 / 80 : ℝ) + logTail 12 (127 / 80 : ℝ) < (231080225893 / 500000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (127 / 40 : ℝ) = 1 * Real.log 2 + Real.log (127 / 80 : ℝ) := by
    rw [show (127 / 40 : ℝ) = 2 ^ 1 * (127 / 80 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q3967_1000 : (1378010141529 / 1000000000000 : ℝ) < Real.log (3967 / 1000 : ℝ) ∧ Real.log (3967 / 1000 : ℝ) < (275602028307 / 200000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (3967 / 2000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (684862960971 / 1000000000000 : ℝ) < logPartial 12 (3967 / 2000 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (3967 / 2000 : ℝ) + logTail 12 (3967 / 2000 : ℝ) < (342431480487 / 500000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (3967 / 1000 : ℝ) = 1 * Real.log 2 + Real.log (3967 / 2000 : ℝ) := by
    rw [show (3967 / 1000 : ℝ) = 2 ^ 1 * (3967 / 2000 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q4883_1000 : (792879892537 / 500000000000 : ℝ) < Real.log (4883 / 1000 : ℝ) ∧ Real.log (4883 / 1000 : ℝ) < (1585759785083 / 1000000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (4883 / 4000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (99732711979 / 500000000000 : ℝ) < logPartial 12 (4883 / 4000 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (4883 / 4000 : ℝ) + logTail 12 (4883 / 4000 : ℝ) < (199465423961 / 1000000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (4883 / 1000 : ℝ) = 2 * Real.log 2 + Real.log (4883 / 4000 : ℝ) := by
    rw [show (4883 / 1000 : ℝ) = 2 ^ 2 * (4883 / 4000 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q5619_1000 : (13809229697 / 8000000000 : ℝ) < Real.log (5619 / 1000 : ℝ) ∧ Real.log (5619 / 1000 : ℝ) < (863076856067 / 500000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (5619 / 4000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (339859351009 / 1000000000000 : ℝ) < logPartial 12 (5619 / 4000 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (5619 / 4000 : ℝ) + logTail 12 (5619 / 4000 : ℝ) < (84964837753 / 250000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (5619 / 1000 : ℝ) = 2 * Real.log 2 + Real.log (5619 / 4000 : ℝ) := by
    rw [show (5619 / 1000 : ℝ) = 2 ^ 2 * (5619 / 4000 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q5 : (1609437912429 / 1000000000000 : ℝ) < Real.log (5 : ℝ) ∧ Real.log (5 : ℝ) < (804718956219 / 500000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (5 / 4 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (223143551313 / 1000000000000 : ℝ) < logPartial 12 (5 / 4 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (5 / 4 : ℝ) + logTail 12 (5 / 4 : ℝ) < (55785887829 / 250000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (5 : ℝ) = 2 * Real.log 2 + Real.log (5 / 4 : ℝ) := by
    rw [show (5 : ℝ) = 2 ^ 2 * (5 / 4 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q8 : (2079441541673 / 1000000000000 : ℝ) < Real.log (8 : ℝ) ∧ Real.log (8 : ℝ) < (415888308337 / 200000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (1 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (-1 / 1000000000000 : ℝ) < logPartial 12 (1 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (1 : ℝ) + logTail 12 (1 : ℝ) < (1 / 500000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (8 : ℝ) = 3 * Real.log 2 + Real.log (1 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ 3 * (1 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q40_3 : (1295133582719 / 500000000000 : ℝ) < Real.log (40 / 3 : ℝ) ∧ Real.log (40 / 3 : ℝ) < (51805343309 / 20000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (5 / 3 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (127706405941 / 250000000000 : ℝ) < logPartial 12 (5 / 3 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (5 / 3 : ℝ) + logTail 12 (5 / 3 : ℝ) < (510825623767 / 1000000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (40 / 3 : ℝ) = 3 * Real.log 2 + Real.log (5 / 3 : ℝ) := by
    rw [show (40 / 3 : ℝ) = 2 ^ 3 * (5 / 3 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q4 : (277258872223 / 200000000000 : ℝ) < Real.log (4 : ℝ) ∧ Real.log (4 : ℝ) < (346573590281 / 250000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (1 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (-1 / 1000000000000 : ℝ) < logPartial 12 (1 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (1 : ℝ) + logTail 12 (1 : ℝ) < (1 / 500000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (4 : ℝ) = 2 * Real.log 2 + Real.log (1 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 * (1 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q7 : (38918202981 / 20000000000 : ℝ) < Real.log (7 : ℝ) ∧ Real.log (7 : ℝ) < (1945910149059 / 1000000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (7 / 4 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (279807893967 / 500000000000 : ℝ) < logPartial 12 (7 / 4 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (7 / 4 : ℝ) + logTail 12 (7 / 4 : ℝ) < (559615787937 / 1000000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (7 : ℝ) = 2 * Real.log 2 + Real.log (7 / 4 : ℝ) := by
    rw [show (7 : ℝ) = 2 ^ 2 * (7 / 4 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q10 : (2302585092987 / 1000000000000 : ℝ) < Real.log (10 : ℝ) ∧ Real.log (10 : ℝ) < (2302585092999 / 1000000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (5 / 4 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (223143551313 / 1000000000000 : ℝ) < logPartial 12 (5 / 4 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (5 / 4 : ℝ) + logTail 12 (5 / 4 : ℝ) < (55785887829 / 250000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (10 : ℝ) = 3 * Real.log 2 + Real.log (5 / 4 : ℝ) := by
    rw [show (10 : ℝ) = 2 ^ 3 * (5 / 4 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q9 : (2197224577329 / 1000000000000 : ℝ) < Real.log (9 : ℝ) ∧ Real.log (9 : ℝ) < (2197224577341 / 1000000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (9 / 8 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (23556607131 / 200000000000 : ℝ) < logPartial 12 (9 / 8 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (9 / 8 : ℝ) + logTail 12 (9 / 8 : ℝ) < (58891517829 / 500000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (9 : ℝ) = 3 * Real.log 2 + Real.log (9 / 8 : ℝ) := by
    rw [show (9 : ℝ) = 2 ^ 3 * (9 / 8 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q25 : (3218875824859 / 1000000000000 : ℝ) < Real.log (25 : ℝ) ∧ Real.log (25 : ℝ) < (1609437912437 / 500000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (25 / 16 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (446287102627 / 1000000000000 : ℝ) < logPartial 12 (25 / 16 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (25 / 16 : ℝ) + logTail 12 (25 / 16 : ℝ) < (44628710263 / 100000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (25 : ℝ) = 4 * Real.log 2 + Real.log (25 / 16 : ℝ) := by
    rw [show (25 : ℝ) = 2 ^ 4 * (25 / 16 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q23 : (39193677699 / 12500000000 : ℝ) < Real.log (23 : ℝ) ∧ Real.log (23 : ℝ) < (627098843187 / 200000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (23 / 16 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (45363186711 / 125000000000 : ℝ) < logPartial 12 (23 / 16 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (23 / 16 : ℝ) + logTail 12 (23 / 16 : ℝ) < (362905493691 / 1000000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (23 : ℝ) = 4 * Real.log 2 + Real.log (23 / 16 : ℝ) := by
    rw [show (23 : ℝ) = 2 ^ 4 * (23 / 16 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q50 : (3912023005417 / 1000000000000 : ℝ) < Real.log (50 : ℝ) ∧ Real.log (50 : ℝ) < (782404601087 / 200000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (25 / 16 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (446287102627 / 1000000000000 : ℝ) < logPartial 12 (25 / 16 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (25 / 16 : ℝ) + logTail 12 (25 / 16 : ℝ) < (44628710263 / 100000000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (50 : ℝ) = 5 * Real.log 2 + Real.log (25 / 16 : ℝ) := by
    rw [show (50 : ℝ) = 2 ^ 5 * (25 / 16 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q47 : (3850147601699 / 1000000000000 : ℝ) < Real.log (47 : ℝ) ∧ Real.log (47 : ℝ) < (3850147601717 / 1000000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (47 / 32 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (384411698909 / 1000000000000 : ℝ) < logPartial 12 (47 / 32 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (47 / 32 : ℝ) + logTail 12 (47 / 32 : ℝ) < (12012865591 / 31250000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (47 : ℝ) = 5 * Real.log 2 + Real.log (47 / 32 : ℝ) := by
    rw [show (47 : ℝ) = 2 ^ 5 * (47 / 32 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

theorem log_q19 : (2944438979157 / 1000000000000 : ℝ) < Real.log (19 : ℝ) ∧ Real.log (19 : ℝ) < (736109744793 / 250000000000 : ℝ) := by
  obtain ⟨h2lo, h2hi⟩ := log_q2
  obtain ⟨hrlo, hrhi⟩ := logEnclosure_proved 12 (19 / 16 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hplo : (6874010277 / 40000000000 : ℝ) < logPartial 12 (19 / 16 : ℝ) := by norm_num [logPartial, Finset.sum_range_succ, Finset.sum_range_zero]
  have hphi : logPartial 12 (19 / 16 : ℝ) + logTail 12 (19 / 16 : ℝ) < (5370320529 / 31250000000 : ℝ) := by norm_num [logPartial, logTail, Finset.sum_range_succ, Finset.sum_range_zero]
  have hsplit : Real.log (19 : ℝ) = 4 * Real.log 2 + Real.log (19 / 16 : ℝ) := by
    rw [show (19 : ℝ) = 2 ^ 4 * (19 / 16 : ℝ) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

/-! ## The manuscript log comparisons -/

theorem row_log_q2_lo : (56 / 81 : ℝ) < Real.log (2 : ℝ) := by
  obtain ⟨h, _⟩ := log_q2; linarith

theorem row_log_q2_hi : Real.log (2 : ℝ) < (7 / 10 : ℝ) := by
  obtain ⟨_, h⟩ := log_q2; linarith

theorem row_log_q3_lo : (13 / 12 : ℝ) < Real.log (3 : ℝ) := by
  obtain ⟨h, _⟩ := log_q3; linarith

theorem row_log_q3_hi : Real.log (3 : ℝ) < (11 / 10 : ℝ) := by
  obtain ⟨_, h⟩ := log_q3; linarith

theorem row_log_q20_lo : (299 / 100 : ℝ) < Real.log (20 : ℝ) := by
  obtain ⟨h, _⟩ := log_q20; linarith

theorem row_log_q20_hi : Real.log (20 : ℝ) < (749 / 250 : ℝ) := by
  obtain ⟨_, h⟩ := log_q20; linarith

theorem row_log_q50_3_lo : (14 / 5 : ℝ) < Real.log (50 / 3 : ℝ) := by
  obtain ⟨h, _⟩ := log_q50_3; linarith

theorem row_log_q459_250_lo : (3 / 5 : ℝ) < Real.log (459 / 250 : ℝ) := by
  obtain ⟨h, _⟩ := log_q459_250; linarith

theorem row_log_q59_21_lo : (1 : ℝ) < Real.log (59 / 21 : ℝ) := by
  obtain ⟨h, _⟩ := log_q59_21; linarith

theorem row_log_q137_23_lo : (7 / 4 : ℝ) < Real.log (137 / 23 : ℝ) := by
  obtain ⟨h, _⟩ := log_q137_23; linarith

theorem row_log_q22_3_lo : (39 / 20 : ℝ) < Real.log (22 / 3 : ℝ) := by
  obtain ⟨h, _⟩ := log_q22_3; linarith

theorem row_log_q899_101_lo : (13 / 6 : ℝ) < Real.log (899 / 101 : ℝ) := by
  obtain ⟨h, _⟩ := log_q899_101; linarith

theorem row_log_q459_41_hi : Real.log (459 / 41 : ℝ) < (5 / 2 : ℝ) := by
  obtain ⟨_, h⟩ := log_q459_41; linarith

theorem row_log_q199_60_lo : (599 / 500 : ℝ) < Real.log (199 / 60 : ℝ) := by
  obtain ⟨h, _⟩ := log_q199_60; linarith

theorem row_log_q127_40_lo : (11553 / 10000 : ℝ) < Real.log (127 / 40 : ℝ) := by
  obtain ⟨h, _⟩ := log_q127_40; linarith

theorem row_log_q3967_1000_lo : (689 / 500 : ℝ) < Real.log (3967 / 1000 : ℝ) := by
  obtain ⟨h, _⟩ := log_q3967_1000; linarith

theorem row_log_q4883_1000_lo : (15857 / 10000 : ℝ) < Real.log (4883 / 1000 : ℝ) := by
  obtain ⟨h, _⟩ := log_q4883_1000; linarith

theorem row_log_q5619_1000_lo : (17261 / 10000 : ℝ) < Real.log (5619 / 1000 : ℝ) := by
  obtain ⟨h, _⟩ := log_q5619_1000; linarith

/-! ## The lambda-bar knot inequalities -/

theorem knot_rho_3_5 :
    Real.log (2 / (1 - (3 / 5 : ℝ))) < 2 * (1 + (3 / 5 : ℝ) - (31/40) * (3 / 5 : ℝ) ^ 2) * (19 / 20 : ℝ) - 3/4 - (3 / 5 : ℝ) / 4 := by
  rw [show (2 / (1 - (3 / 5 : ℝ)) : ℝ) = (5 : ℝ) by norm_num]
  obtain ⟨_, h⟩ := log_q5; linarith

theorem knot_rho_3_4 :
    Real.log (2 / (1 - (3 / 4 : ℝ))) < 2 * (1 + (3 / 4 : ℝ) - (31/40) * (3 / 4 : ℝ) ^ 2) * (287 / 250 : ℝ) - 3/4 - (3 / 4 : ℝ) / 4 := by
  rw [show (2 / (1 - (3 / 4 : ℝ)) : ℝ) = (8 : ℝ) by norm_num]
  obtain ⟨_, h⟩ := log_q8; linarith

theorem knot_rho_17_20 :
    Real.log (2 / (1 - (17 / 20 : ℝ))) < 2 * (1 + (17 / 20 : ℝ) - (31/40) * (17 / 20 : ℝ) ^ 2) * (1377 / 1000 : ℝ) - 3/4 - (17 / 20 : ℝ) / 4 := by
  rw [show (2 / (1 - (17 / 20 : ℝ)) : ℝ) = (40 / 3 : ℝ) by norm_num]
  obtain ⟨_, h⟩ := log_q40_3; linarith

theorem knot_rho_9_10 :
    Real.log (2 / (1 - (9 / 10 : ℝ))) < 2 * (1 + (9 / 10 : ℝ) - (31/40) * (9 / 10 : ℝ) ^ 2) * (1561 / 1000 : ℝ) - 3/4 - (9 / 10 : ℝ) / 4 := by
  rw [show (2 / (1 - (9 / 10 : ℝ)) : ℝ) = (20 : ℝ) by norm_num]
  obtain ⟨_, h⟩ := log_q20; linarith

/-! ## The binary-entropy comparisons -/

theorem row_h_1_4_lo : (11 / 20 : ℝ) < binaryEntropy (1 / 4 : ℝ) := by
  have e : binaryEntropy (1 / 4 : ℝ) =
      Real.log (4 : ℝ) - (1 / 4 : ℝ) * Real.log (1 : ℝ) - (3 / 4 : ℝ) * Real.log (3 : ℝ) := by
    unfold binaryEntropy
    rw [show (1 - (1 / 4 : ℝ) : ℝ) = (3 : ℝ) / (4 : ℝ) by norm_num,
        show (1 / 4 : ℝ) = (1 : ℝ) / (4 : ℝ) by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num)]
    ring
  obtain ⟨log_q4_lo, log_q4_hi⟩ := log_q4
  obtain ⟨log_q3_lo, log_q3_hi⟩ := log_q3
  have l1 : Real.log (1 : ℝ) = 0 := Real.log_one
  rw [e]; linarith

theorem row_h_1_8_lo : (3 / 8 : ℝ) < binaryEntropy (1 / 8 : ℝ) := by
  have e : binaryEntropy (1 / 8 : ℝ) =
      Real.log (8 : ℝ) - (1 / 8 : ℝ) * Real.log (1 : ℝ) - (7 / 8 : ℝ) * Real.log (7 : ℝ) := by
    unfold binaryEntropy
    rw [show (1 - (1 / 8 : ℝ) : ℝ) = (7 : ℝ) / (8 : ℝ) by norm_num,
        show (1 / 8 : ℝ) = (1 : ℝ) / (8 : ℝ) by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num)]
    ring
  obtain ⟨log_q8_lo, log_q8_hi⟩ := log_q8
  obtain ⟨log_q7_lo, log_q7_hi⟩ := log_q7
  have l1 : Real.log (1 : ℝ) = 0 := Real.log_one
  rw [e]; linarith

theorem row_h_1_10_lo : (8 / 25 : ℝ) < binaryEntropy (1 / 10 : ℝ) := by
  have e : binaryEntropy (1 / 10 : ℝ) =
      Real.log (10 : ℝ) - (1 / 10 : ℝ) * Real.log (1 : ℝ) - (9 / 10 : ℝ) * Real.log (9 : ℝ) := by
    unfold binaryEntropy
    rw [show (1 - (1 / 10 : ℝ) : ℝ) = (9 : ℝ) / (10 : ℝ) by norm_num,
        show (1 / 10 : ℝ) = (1 : ℝ) / (10 : ℝ) by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num)]
    ring
  obtain ⟨log_q10_lo, log_q10_hi⟩ := log_q10
  obtain ⟨log_q9_lo, log_q9_hi⟩ := log_q9
  have l1 : Real.log (1 : ℝ) = 0 := Real.log_one
  rw [e]; linarith

theorem row_h_2_25_lo : (11 / 40 : ℝ) < binaryEntropy (2 / 25 : ℝ) := by
  have e : binaryEntropy (2 / 25 : ℝ) =
      Real.log (25 : ℝ) - (2 / 25 : ℝ) * Real.log (2 : ℝ) - (23 / 25 : ℝ) * Real.log (23 : ℝ) := by
    unfold binaryEntropy
    rw [show (1 - (2 / 25 : ℝ) : ℝ) = (23 : ℝ) / (25 : ℝ) by norm_num,
        show (2 / 25 : ℝ) = (2 : ℝ) / (25 : ℝ) by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num)]
    ring
  obtain ⟨log_q25_lo, log_q25_hi⟩ := log_q25
  obtain ⟨log_q2_lo, log_q2_hi⟩ := log_q2
  obtain ⟨log_q23_lo, log_q23_hi⟩ := log_q23
  rw [e]; linarith

theorem row_h_3_50_lo : (9 / 40 : ℝ) < binaryEntropy (3 / 50 : ℝ) := by
  have e : binaryEntropy (3 / 50 : ℝ) =
      Real.log (50 : ℝ) - (3 / 50 : ℝ) * Real.log (3 : ℝ) - (47 / 50 : ℝ) * Real.log (47 : ℝ) := by
    unfold binaryEntropy
    rw [show (1 - (3 / 50 : ℝ) : ℝ) = (47 : ℝ) / (50 : ℝ) by norm_num,
        show (3 / 50 : ℝ) = (3 : ℝ) / (50 : ℝ) by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num)]
    ring
  obtain ⟨log_q50_lo, log_q50_hi⟩ := log_q50
  obtain ⟨log_q3_lo, log_q3_hi⟩ := log_q3
  obtain ⟨log_q47_lo, log_q47_hi⟩ := log_q47
  rw [e]; linarith

theorem row_h_1_5_lo : (1 / 2 : ℝ) < binaryEntropy (1 / 5 : ℝ) := by
  have e : binaryEntropy (1 / 5 : ℝ) =
      Real.log (5 : ℝ) - (1 / 5 : ℝ) * Real.log (1 : ℝ) - (4 / 5 : ℝ) * Real.log (4 : ℝ) := by
    unfold binaryEntropy
    rw [show (1 - (1 / 5 : ℝ) : ℝ) = (4 : ℝ) / (5 : ℝ) by norm_num,
        show (1 / 5 : ℝ) = (1 : ℝ) / (5 : ℝ) by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num)]
    ring
  obtain ⟨log_q5_lo, log_q5_hi⟩ := log_q5
  obtain ⟨log_q4_lo, log_q4_hi⟩ := log_q4
  have l1 : Real.log (1 : ℝ) = 0 := Real.log_one
  rw [e]; linarith

theorem row_h_1_20_hi : binaryEntropy (1 / 20 : ℝ) < (1 / 5 : ℝ) := by
  have e : binaryEntropy (1 / 20 : ℝ) =
      Real.log (20 : ℝ) - (1 / 20 : ℝ) * Real.log (1 : ℝ) - (19 / 20 : ℝ) * Real.log (19 : ℝ) := by
    unfold binaryEntropy
    rw [show (1 - (1 / 20 : ℝ) : ℝ) = (19 : ℝ) / (20 : ℝ) by norm_num,
        show (1 / 20 : ℝ) = (1 : ℝ) / (20 : ℝ) by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num)]
    ring
  obtain ⟨log_q20_lo, log_q20_hi⟩ := log_q20
  obtain ⟨log_q19_lo, log_q19_hi⟩ := log_q19
  have l1 : Real.log (1 : ℝ) = 0 := Real.log_one
  rw [e]; linarith

/-! ## Combined comparisons -/

theorem comb_log3 : (949 / 1500 : ℝ) < Real.log 3 - (2/3) * Real.log 2 := by
  obtain ⟨h3, _⟩ := log_q3
  obtain ⟨_, h2⟩ := log_q2
  linarith

theorem comb_log2 : Real.log 2 - (39/40) * (2/5) * (1321/1000) < (9 / 50 : ℝ) := by
  obtain ⟨_, h2⟩ := log_q2
  linarith

theorem comb_rat1 : (1999 / 1250000 : ℝ) > 7 / 5000 := by norm_num

theorem comb_rat2 : (453 / 5000 : ℝ) > 7 / 250 := by norm_num

theorem comb_rat3 : (23 / 3600 : ℝ) > 1 / 500 := by norm_num

end AppF
end CK