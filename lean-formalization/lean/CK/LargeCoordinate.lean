import CK.InfoContraction
import CK.LargeCoordScalar
import CK.NoiseOperator

/-!
# Lemma `lem:largecoordinate` at the last coordinate

If the last coordinate is dominant, `|μ₁ − μ₀| ≥ 13/20`, and `ρ = 1 − 2p ≤ 9/10`, then
`I(f(X);Y) ≤ log 2 − h(p)`.

Route (manuscript `lem:largecoordinate`, App. B):
1. `sigma_ge`: the residual conditional entropy `σ = avg (if f₁ = f₀ then 0 else h(p))`
   dominates `h(p)·|μ₁ − μ₀|`.
2. `conditionalEntropy_ge_conditional` (`eq:conditionalcontraction`):
   `H(f|Y) ≥ (1−ρ²)·Q(m, ρb) + ρ²·σ`.
3. `U_le_U_zero` (App. B.1) centers `m ↦ η(m) − (1−ρ²) Q(m, ρb)` at `m = 0`.
4. `large_coord_scalar` (`eq:largecoordscalar`) closes the scalar inequality.
The case `μ₁ − μ₀ ≤ −13/20` is reduced to the case `μ₁ − μ₀ ≥ 13/20` by complementing the
output (`information_compl`, `mean_compl`).
-/
noncomputable section
namespace CK
open scoped BigOperators

/-! ## Output complement -/

theorem indicator_not (b : Bool) : indicator (!b) = 1 - indicator b := by
  cases b <;> simp [indicator]

theorem mean_compl {n : ℕ} (f : BooleanFunction n) : mean (fun x => !(f x)) = 1 - mean f := by
  have h := avg_sub (fun _ : Cube n => (1 : ℝ)) (fun x => indicator (f x))
  rw [avg_const'] at h
  show avg (fun x => indicator (!(f x))) = 1 - avg (fun x => indicator (f x))
  rw [← h]
  congr 1
  funext x
  rw [indicator_not]

/-- The posterior of the complement is the complement of the posterior (`kernel_row_sum`). -/
theorem posterior_compl {n : ℕ} (f : BooleanFunction n) (p : ℝ) (y : Cube n) :
    posterior (fun x => !(f x)) p y = 1 - posterior f p y := by
  have hr := kernel_row_sum p y
  show ∑ x, kernel p y x * indicator (!(f x)) = 1 - ∑ x, kernel p y x * indicator (f x)
  calc ∑ x, kernel p y x * indicator (!(f x))
      = ∑ x, (kernel p y x - kernel p y x * indicator (f x)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [indicator_not]
        ring
    _ = 1 - ∑ x, kernel p y x * indicator (f x) := by
        rw [Finset.sum_sub_distrib, hr]

/-- Output complement: information is unchanged, section means are complemented. -/
theorem information_compl {n : ℕ} (f : BooleanFunction n) (p : ℝ) :
    information (fun x => !(f x)) p = information f p := by
  unfold information conditionalEntropy
  rw [mean_compl, binaryEntropy_symm]
  congr 2
  funext y
  rw [posterior_compl, binaryEntropy_symm]

/-! ## Step 1: the residual entropy dominates `h(p)·|μ₁ − μ₀|` -/

/-- `σ = avg (if f₁ = f₀ then 0 else h(p)) ≥ h(p)·|μ₁ − μ₀|`. -/
theorem sigma_ge {n : ℕ} (f : BooleanFunction (n + 1)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binaryEntropy p * |mean (sectionLast f true) - mean (sectionLast f false)|
      ≤ avg (fun w => if sectionLast f true w = sectionLast f false w
          then (0 : ℝ) else binaryEntropy p) := by
  have hh : 0 ≤ binaryEntropy p := binaryEntropy_nonneg' hp0 hp1
  have hpt : ∀ w, (if sectionLast f true w = sectionLast f false w then (0 : ℝ)
        else binaryEntropy p)
      = binaryEntropy p * |indicator (sectionLast f true w) - indicator (sectionLast f false w)| := by
    intro w
    cases sectionLast f true w <;> cases sectionLast f false w <;> simp [indicator]
  have hA : avg (fun w => if sectionLast f true w = sectionLast f false w then (0 : ℝ)
        else binaryEntropy p)
      = binaryEntropy p * avg (fun w =>
          |indicator (sectionLast f true w) - indicator (sectionLast f false w)|) := by
    rw [← avg_const_mul]
    congr 1
    funext w
    exact hpt w
  have hm : mean (sectionLast f true) - mean (sectionLast f false)
      = avg (fun w => indicator (sectionLast f true w) - indicator (sectionLast f false w)) :=
    (avg_sub (fun w => indicator (sectionLast f true w))
      (fun w => indicator (sectionLast f false w))).symm
  rw [hA, hm]
  exact mul_le_mul_of_nonneg_left (abs_avg_le_avg_abs _) hh

/-! ## Steps 3–5: the scalar assembly -/

/-- Steps 3–5 of `lem:largecoordinate`: `η(m) − (1−ρ²) Q(m, ρb) − ρ² b η(ρ) ≤ log 2 − η(ρ)`
for `0 ≤ ρ ≤ 9/10`, `13/20 ≤ b ≤ 1`, `|m| + b ≤ 1` (App. B.1 + `eq:largecoordscalar`). -/
theorem large_coord_assemble {ρ b m : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 9 / 10) (hb0 : 13 / 20 ≤ b)
    (hb1 : b ≤ 1) (hmb : |m| + b ≤ 1) :
    eta m - ((1 - ρ ^ 2) * pairEntropy m (ρ * b) + ρ ^ 2 * (b * eta ρ))
      ≤ Real.log 2 - eta ρ := by
  have hU := U_le_U_zero hρ0 (by linarith) (by linarith) hmb
  rw [eta_zero, pairEntropy_zero_left] at hU
  have hls := large_coord_scalar hρ0 hρ1 hb0 hb1
  linarith [hU, hls]

/-- `h(p) = η(1 − 2p)` (`binaryEntropy_symm`, `eta_even`). -/
theorem binaryEntropy_eq_eta_rho (p : ℝ) : binaryEntropy p = eta (1 - 2 * p) := by
  rw [binaryEntropy_eq_eta, show (2 * p - 1 : ℝ) = -(1 - 2 * p) by ring, eta_even]

/-! ## Lemma `lem:largecoordinate` -/

/-- `lem:largecoordinate` at the last coordinate, in the case `μ₁ − μ₀ ≥ 13/20`. -/
theorem large_coordinate_last_of_nonneg {n : ℕ} (f : BooleanFunction (n + 1)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (hρ : 1 - 2 * p ≤ 9 / 10)
    (hb : 13 / 20 ≤ mean (sectionLast f true) - mean (sectionLast f false)) :
    information f p ≤ Real.log 2 - binaryEntropy p := by
  have hμ1_0 := mean_nonneg (sectionLast f true)
  have hμ1_1 := mean_le_one (sectionLast f true)
  have hμ0_0 := mean_nonneg (sectionLast f false)
  have hμ0_1 := mean_le_one (sectionLast f false)
  have hmean := mean_snoc f
  have hρ0 : 0 ≤ 1 - 2 * p := by linarith
  have hbnn : 0 ≤ mean (sectionLast f true) - mean (sectionLast f false) := by linarith
  -- `|m| + b ≤ 1`
  have hmb : |2 * mean f - 1| + (mean (sectionLast f true) - mean (sectionLast f false)) ≤ 1 := by
    rw [hmean]
    rcases abs_cases (2 * ((mean (sectionLast f true) + mean (sectionLast f false)) / 2) - 1)
      with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  -- step 1
  have hσ := sigma_ge f hp0 (by linarith)
  rw [abs_of_nonneg hbnn] at hσ
  -- step 2
  have hce := conditionalEntropy_ge_conditional f hp0 hp1
  -- step 3
  have hinfo : information f p = eta (2 * mean f - 1) - conditionalEntropy f p := by
    unfold information
    rw [binaryEntropy_eq_eta]
  -- steps 4–5
  have hkey := large_coord_assemble hρ0 hρ hb (by linarith) hmb
  rw [← binaryEntropy_eq_eta_rho] at hkey
  rw [hinfo]
  have hsq : 0 ≤ (1 - 2 * p) ^ 2 := sq_nonneg _
  have hσ2 := mul_le_mul_of_nonneg_left hσ hsq
  linarith [hσ2, hce, hkey]

/-- Lemma lem:largecoordinate at the last coordinate: if |μ₁ − μ₀| ≥ 13/20 and ρ ≤ 9/10 then
I(f(X);Y) ≤ log 2 − h(p). -/
theorem large_coordinate_last {n : ℕ} (f : BooleanFunction (n + 1)) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1 / 2) (hρ : 1 - 2 * p ≤ 9 / 10)
    (hb : 13 / 20 ≤ |mean (sectionLast f true) - mean (sectionLast f false)|) :
    information f p ≤ Real.log 2 - binaryEntropy p := by
  rcases abs_cases (mean (sectionLast f true) - mean (sectionLast f false))
    with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h] at hb
    exact large_coordinate_last_of_nonneg f hp0 hp1 hρ hb
  · rw [h] at hb
    -- complement the output: the sections complement, `b ↦ −b`, information unchanged
    have hc : 13 / 20 ≤ mean (sectionLast (fun x => !(f x)) true)
        - mean (sectionLast (fun x => !(f x)) false) := by
      have e1 : sectionLast (fun x => !(f x)) true = fun w => !(sectionLast f true w) := rfl
      have e2 : sectionLast (fun x => !(f x)) false = fun w => !(sectionLast f false w) := rfl
      rw [e1, e2, mean_compl, mean_compl]
      linarith
    have hI := large_coordinate_last_of_nonneg (fun x => !(f x)) hp0 hp1 hρ hc
    rwa [information_compl] at hI

end CK
