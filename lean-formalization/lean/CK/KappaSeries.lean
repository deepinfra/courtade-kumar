import CK.GainBounds

/-!
# The power series of `kappa` (manuscript eq:series) and the scaling bound (eq:entropyfacts)

`kappa u = log 2 - eta u` has the closed form `((1+u) log(1+u) + (1-u) log(1-u)) / 2`
on `(-1, 1)`, hence the everywhere-nonnegative series
`kappa u = Σ_{j ≥ 1} u^{2j} / (2j (2j-1))` (eq:series).  Termwise comparison of the
series gives `kappa (θ u) ≤ θ² kappa u` for `0 ≤ θ ≤ 1` and `|u| < 1`; the endpoint
`|u| = 1` follows by continuity (eq:entropyfacts).
-/
noncomputable section
namespace CK
open scoped BigOperators

/-! ## Elementary facts about `kappa` -/

theorem kappa_even (u : ℝ) : kappa (-u) = kappa u := by
  unfold kappa; rw [eta_even]

theorem kappa_one : kappa 1 = Real.log 2 := by
  unfold kappa; rw [eta_one]; ring

theorem kappa_nonneg {u : ℝ} (hu0 : -1 ≤ u) (hu1 : u ≤ 1) : 0 ≤ kappa u :=
  le_trans (by positivity) (kappa_ge_half_sq hu0 hu1)

theorem continuous_kappa : Continuous kappa := by
  unfold kappa
  exact continuous_const.sub continuous_eta

/-- Closed form of `kappa` on `(-1, 1)`:
`kappa u = (log (1 - u²) + u (log (1+u) - log (1-u))) / 2`. -/
theorem kappa_closed {u : ℝ} (hu0 : -1 < u) (hu1 : u < 1) :
    kappa u = (Real.log (1 - u ^ 2) + u * (Real.log (1 + u) - Real.log (1 - u))) / 2 := by
  unfold kappa eta binaryEntropy
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 : (0 : ℝ) < 1 - u := by linarith
  rw [show (1 - (1 + u) / 2 : ℝ) = (1 - u) / 2 by ring,
    Real.log_div (ne_of_gt h1) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div (ne_of_gt h2) (by norm_num : (2 : ℝ) ≠ 0),
    show (1 - u ^ 2 : ℝ) = (1 + u) * (1 - u) by ring,
    Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]
  ring

/-! ## The series (eq:series) -/

/-- eq:series: κ(u) = Σ_{j≥1} u^{2j}/(2j(2j−1)) for |u| < 1 (index j = n+1). -/
theorem hasSum_kappa {u : ℝ} (hu : |u| < 1) :
    HasSum (fun n : ℕ => u ^ (2 * (n + 1)) / ((2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1)))
      (kappa u) := by
  have hu0 : -1 < u := (abs_lt.mp hu).1
  have hu1 : u < 1 := (abs_lt.mp hu).2
  have hsq : |u ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg u)]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - u) (by linarith : (0 : ℝ) < 1 + u)]
  have h1 := Real.hasSum_pow_div_log_of_abs_lt_one hsq
  have h2 := (Real.hasSum_log_sub_log_of_abs_lt_one hu).mul_left u
  have h3 := (h2.sub h1).mul_left (1 / 2)
  convert h3 using 1
  · funext n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hd1 : (2 * ((n : ℝ) + 1) - 1) ≠ 0 := ne_of_gt (by linarith)
    have hd2 : (2 * (n : ℝ) + 1) ≠ 0 := ne_of_gt (by linarith)
    have hd3 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by linarith)
    rw [pow_mul]
    field_simp
    ring
  · rw [kappa_closed hu0 hu1]
    ring

theorem kappa_ge_partial {u : ℝ} (hu : |u| < 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, u ^ (2 * (n + 1)) / ((2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1))
      ≤ kappa u := by
  refine sum_le_hasSum (Finset.range N) (fun n _ => ?_) (hasSum_kappa hu)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  apply div_nonneg
  · rw [pow_mul]; exact pow_nonneg (sq_nonneg u) _
  · apply mul_nonneg <;> linarith

/-! ## The scaling bound (eq:entropyfacts) -/

/-- eq:entropyfacts, interior case: termwise comparison of the series. -/
theorem kappa_scaling_of_abs_lt {θ u : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hu : |u| < 1) :
    kappa (θ * u) ≤ θ ^ 2 * kappa u := by
  have hθu : |θ * u| < 1 := by
    rw [abs_mul, abs_of_nonneg hθ0]
    calc θ * |u| ≤ 1 * |u| := mul_le_mul_of_nonneg_right hθ1 (abs_nonneg u)
      _ = |u| := one_mul _
      _ < 1 := hu
  refine hasSum_le (fun n => ?_) (hasSum_kappa hθu) ((hasSum_kappa hu).mul_left (θ ^ 2))
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hD : 0 < (2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1) := by
    apply mul_pos <;> linarith
  have hpow : (θ * u) ^ (2 * (n + 1)) ≤ θ ^ 2 * u ^ (2 * (n + 1)) := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hθ0 hθ1 (by omega)) ?_
    rw [pow_mul]; exact pow_nonneg (sq_nonneg u) _
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hpow hD.le

/-- eq:entropyfacts: κ(θu) ≤ θ² κ(u) for 0 ≤ θ ≤ 1, −1 ≤ u ≤ 1. -/
theorem kappa_scaling {θ u : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hu0 : -1 ≤ u) (hu1 : u ≤ 1) :
    kappa (θ * u) ≤ θ ^ 2 * kappa u := by
  have hcl : IsClosed {v : ℝ | kappa (θ * v) ≤ θ ^ 2 * kappa v} :=
    isClosed_le (continuous_kappa.comp (continuous_const.mul continuous_id))
      (continuous_const.mul continuous_kappa)
  have hsub : Set.Ioo (-1 : ℝ) 1 ⊆ {v : ℝ | kappa (θ * v) ≤ θ ^ 2 * kappa v} :=
    fun v hv => kappa_scaling_of_abs_lt hθ0 hθ1 (abs_lt.mpr hv)
  have hcls := hcl.closure_subset_iff.mpr hsub
  rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] at hcls
  exact hcls ⟨hu0, hu1⟩

end CK
