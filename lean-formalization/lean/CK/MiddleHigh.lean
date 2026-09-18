import CK.NoiseOperator
import CK.Comparison
import CK.Anchor
import CK.InfoContraction
import CK.KappaSeries
import CK.Constants

/-!
# Propositions prop:middle and prop:high (the remainder class under the Fourier cap)

Under the cap `m² + W₁ ≤ 31/40` (with `m = E signOf f`) the Courtade–Kumar bound
`I(f;Y) ≤ log 2 − h(p)` holds

* on the correlation interval `3/5 ≤ ρ ≤ 9/10` (`middle_range`, Prop prop:middle):
  the conditional entropy `E eta(|T_ρ F|)` is bounded below through the entropy comparison
  eq:comparison (`entropy_comparison`) and the energy bound Lemma lem:energy
  (`energy_lower_bound`), while `h(E f) = eta m ≤ log 2 − m²/2` (Pinsker);
* on the high-noise interval `0 ≤ ρ ≤ 3/5` (`high_noise`, Prop prop:high): the strict anchor
  eq:anchorcomparison at `p₀ = 1/5` gives `I(f;Y_{p₀}) < 9/50`, the degradation inequality
  (`information_degrade`) scales this by `(ρ/ρ₀)²`, and `ρ²/2 ≤ kappa ρ` closes the argument.
-/
noncomputable section
namespace CK
open scoped BigOperators

/-! ## Common facts -/

/-- `eta (1 − 2p) = h(p)` (manuscript dictionary `ρ = 1 − 2p`). -/
theorem binaryEntropy_eq_eta_rho' (p : ℝ) : binaryEntropy p = eta (1 - 2 * p) := by
  unfold eta
  rw [show (1 + (1 - 2 * p)) / 2 = 1 - p by ring, binaryEntropy_symm]

/-- The mean of `signOf f` lies in `[-1, 1]` under the cap. -/
theorem avg_signOf_mem_of_cap {n : ℕ} (f : BooleanFunction n)
    (hcap : (avg (signOf f)) ^ 2 + weight (signOf f) 1 ≤ 31 / 40) :
    -1 ≤ avg (signOf f) ∧ avg (signOf f) ≤ 1 := by
  have hW := weight_nonneg (signOf f) 1
  exact abs_le_of_sq_le_sq' (by rw [one_pow]; linarith) zero_le_one

/-- `|T_p (signOf f)| ≤ 1` for `0 ≤ p ≤ 1`. -/
theorem abs_noiseOp_signOf_le_one {n : ℕ} (f : BooleanFunction n) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (y : Cube n) : |noiseOp p (signOf f) y| ≤ 1 :=
  abs_noiseOp_le_one hp0 hp1 (signOf f) (fun x => (abs_signOf f x).le) y

/-! ## Prop prop:middle -/

/-- `Γ(ρ)·1321 ≤ 1240·Λ(ρ)` on `[3/5, 9/10]`, i.e. `Γ/Λ ≤ 1240/1321`. -/
theorem gamma_le_lambdaDenom {ρ : ℝ} (hρ0 : 3 / 5 ≤ ρ) (_hρ1 : ρ ≤ 9 / 10) :
    1321 * (1 + ρ - ρ ^ 2) ≤ 1240 * lambdaDenom ρ := by
  unfold lambdaDenom
  nlinarith [mul_nonneg (sub_nonneg.2 hρ0) (by linarith : (0 : ℝ) ≤ 360 * ρ + 135)]

/-- `eta ρ < 13/25` for `ρ ≥ 3/5`. -/
theorem eta_lt_of_ge_three_fifths {ρ : ℝ} (hρ0 : 3 / 5 ≤ ρ) (hρ1 : ρ ≤ 1) :
    eta ρ < 13 / 25 := by
  have h1 : eta ρ ≤ eta (3 / 5) := eta_le_eta (by norm_num) hρ0 hρ1
  have h2 := kappa_ge_half_sq (u := 3 / 5) (by norm_num) (by norm_num)
  unfold kappa at h2
  have h3 := AppF.row_log_q2_hi
  linarith

/-- Arithmetic core of prop:middle: if `H ≥ λ(1−ρ)(Λ − Γ m²)` with `λ = eta ρ/((1−ρ)Λ)`,
then `eta m − H ≤ log 2 − eta ρ`. -/
theorem middle_core {ρ m H : ℝ} (hρ0 : 3 / 5 ≤ ρ) (hρ1 : ρ ≤ 9 / 10) (hm0 : -1 ≤ m) (hm1 : m ≤ 1)
    (hH : eta ρ / ((1 - ρ) * lambdaDenom ρ) *
      ((1 - ρ) * ((1 + ρ - 31 / 40 * ρ ^ 2) - (1 + ρ - ρ ^ 2) * m ^ 2)) ≤ H) :
    eta m - H ≤ Real.log 2 - eta ρ := by
  have hΛ : 1 ≤ lambdaDenom ρ := one_le_lambdaDenom (by linarith) (by linarith)
  have hΛpos : 0 < lambdaDenom ρ := by linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  have hΛdef : lambdaDenom ρ = 1 + ρ - 31 / 40 * ρ ^ 2 := rfl
  -- simplify the lower bound: λ(1−ρ)(Λ − Γm²) = eta ρ (Λ − Γ m²)/Λ
  have hkey : eta ρ / ((1 - ρ) * lambdaDenom ρ) *
      ((1 - ρ) * ((1 + ρ - 31 / 40 * ρ ^ 2) - (1 + ρ - ρ ^ 2) * m ^ 2))
      = eta ρ * (lambdaDenom ρ - (1 + ρ - ρ ^ 2) * m ^ 2) / lambdaDenom ρ := by
    have hΛne : lambdaDenom ρ ≠ 0 := hΛpos.ne'
    have h1ρne : (1 - ρ) ≠ 0 := h1ρ.ne'
    rw [← hΛdef]
    field_simp
    ring
  rw [hkey, div_le_iff₀ hΛpos] at hH
  -- Pinsker at m
  have hk := kappa_ge_half_sq hm0 hm1
  unfold kappa at hk
  -- the bracket is nonpositive: 2 eta ρ Γ ≤ Λ
  have hΓ : 0 ≤ 1 + ρ - ρ ^ 2 := by nlinarith
  have heta := eta_lt_of_ge_three_fifths hρ0 (by linarith)
  have hpoly := gamma_le_lambdaDenom hρ0 hρ1
  have h1 : eta ρ * (1 + ρ - ρ ^ 2) ≤ 13 / 25 * (1 + ρ - ρ ^ 2) :=
    mul_le_mul_of_nonneg_right heta.le hΓ
  have hbr : 2 * (eta ρ * (1 + ρ - ρ ^ 2)) ≤ lambdaDenom ρ := by linarith
  have h3 : m ^ 2 * (2 * (eta ρ * (1 + ρ - ρ ^ 2)) - lambdaDenom ρ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg m) (by linarith)
  have hkΛ : lambdaDenom ρ * eta m ≤ lambdaDenom ρ * (Real.log 2 - m ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hΛpos.le
  refine le_of_mul_le_mul_left ?_ hΛpos
  nlinarith [hH, hk, h3, hkΛ]

/-- Prop prop:middle: under the cap m² + W₁ ≤ 31/40, the CK bound holds for 3/5 ≤ ρ ≤ 9/10. -/
theorem middle_range {n : ℕ} (f : BooleanFunction n) {p : ℝ} (hρ0 : 3 / 5 ≤ 1 - 2 * p) (hρ1 : 1 - 2 * p ≤ 9 / 10)
    (hcap : (avg (signOf f)) ^ 2 + weight (signOf f) 1 ≤ 31 / 40) :
    information f p ≤ Real.log 2 - binaryEntropy p := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : p ≤ 1 / 2 := by linarith
  have h1ρ : 0 < 1 - (1 - 2 * p) := by linarith
  have hΛ : 1 ≤ lambdaDenom (1 - 2 * p) := one_le_lambdaDenom (by linarith) (by linarith)
  have hG : ∀ y, |noiseOp p (signOf f) y| ≤ 1 :=
    abs_noiseOp_signOf_le_one f hp0 (by linarith)
  -- Step 1: H(f|Y) ≥ λ · E psi_ρ(|G|)
  have hlam0 : 0 ≤ eta (1 - 2 * p) / ((1 - (1 - 2 * p)) * lambdaDenom (1 - 2 * p)) :=
    div_nonneg (eta_nonneg (by linarith) (by linarith)) (mul_nonneg h1ρ.le (by linarith))
  have hH : eta (1 - 2 * p) / ((1 - (1 - 2 * p)) * lambdaDenom (1 - 2 * p)) *
      avg (fun y => psi (1 - 2 * p) |noiseOp p (signOf f) y|) ≤ conditionalEntropy f p := by
    rw [conditionalEntropy_eq_avg_eta_abs, ← avg_const_mul]
    apply avg_le_avg
    intro y
    exact entropy_comparison (1 - 2 * p) |noiseOp p (signOf f) y| hρ0 hρ1 (abs_nonneg _) (hG y)
  -- Step 2: the energy lower bound with Ω = 31/40
  have hE := energy_lower_bound hp0 hp1 f (31 / 40) hcap
  have hH' := le_trans (mul_le_mul_of_nonneg_left hE hlam0) hH
  -- Steps 3–4: assemble
  obtain ⟨hm0, hm1⟩ := avg_signOf_mem_of_cap f hcap
  unfold information
  rw [binaryEntropy_mean_eq, binaryEntropy_eq_eta_rho']
  exact middle_core hρ0 hρ1 hm0 hm1 hH'

/-! ## Prop prop:high -/

/-- Arithmetic core of prop:high at the anchor `p₀ = 1/5`: if `H ≥ (39/40)(2/5)(Λ₀ − Γ₀ m²)`
then `eta m − H ≤ 9/50`. -/
theorem high_core {m H : ℝ} (hm0 : -1 ≤ m) (hm1 : m ≤ 1)
    (hH : 39 / 40 * ((1 - 3 / 5) * ((1 + 3 / 5 - 31 / 40 * (3 / 5) ^ 2)
      - (1 + 3 / 5 - (3 / 5) ^ 2) * m ^ 2)) ≤ H) :
    eta m - H ≤ 9 / 50 := by
  have hk := kappa_ge_half_sq hm0 hm1
  unfold kappa at hk
  have hc := AppF.comb_log2
  nlinarith [sq_nonneg m, hH, hk, hc]

/-- At the anchor `p₀ = 1/5`, under the cap, `I(f;Y_{1/5}) ≤ 9/50`. -/
theorem information_anchor_le {n : ℕ} (f : BooleanFunction n)
    (hcap : (avg (signOf f)) ^ 2 + weight (signOf f) 1 ≤ 31 / 40) :
    information f (1 / 5) ≤ 9 / 50 := by
  have hG : ∀ y, |noiseOp (1 / 5) (signOf f) y| ≤ 1 :=
    abs_noiseOp_signOf_le_one f (by norm_num) (by norm_num)
  have h35 : (1 : ℝ) - 2 * (1 / 5) = 3 / 5 := by norm_num
  -- pointwise strict anchor, averaged
  have hH : 39 / 40 * avg (fun y => psi (3 / 5) |noiseOp (1 / 5) (signOf f) y|)
      ≤ conditionalEntropy f (1 / 5) := by
    rw [conditionalEntropy_eq_avg_eta_abs, ← avg_const_mul]
    apply avg_le_avg
    intro y
    exact strict_anchor _ (abs_nonneg _) (hG y)
  -- energy lower bound at p = 1/5
  have hE := energy_lower_bound (p := 1 / 5) (by norm_num) (by norm_num) f (31 / 40) hcap
  rw [h35] at hE
  have hH' := le_trans (mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 39 / 40)) hH
  obtain ⟨hm0, hm1⟩ := avg_signOf_mem_of_cap f hcap
  unfold information
  rw [binaryEntropy_mean_eq]
  exact high_core hm0 hm1 hH'

/-- Prop prop:high: under the cap, the CK bound holds for 0 ≤ ρ ≤ 3/5. -/
theorem high_noise {n : ℕ} (f : BooleanFunction n) {p : ℝ} (hρ0 : 0 ≤ 1 - 2 * p) (hρ1 : 1 - 2 * p ≤ 3 / 5)
    (hcap : (avg (signOf f)) ^ 2 + weight (signOf f) 1 ≤ 31 / 40) :
    information f p ≤ Real.log 2 - binaryEntropy p := by
  have hpp : (1 / 5 : ℝ) ≤ p := by linarith
  have hp1 : p ≤ 1 / 2 := by linarith
  have hdeg := information_degrade f (p0 := 1 / 5) (p := p) (by norm_num) (by norm_num) hpp hp1
  have hI0 := information_anchor_le f hcap
  have hsc : ((1 - 2 * p) / (1 - 2 * (1 / 5))) ^ 2 * information f (1 / 5)
      ≤ ((1 - 2 * p) / (1 - 2 * (1 / 5))) ^ 2 * (9 / 50) :=
    mul_le_mul_of_nonneg_left hI0 (sq_nonneg _)
  have hsq : ((1 - 2 * p) / (1 - 2 * (1 / 5))) ^ 2 * (9 / 50) = (1 - 2 * p) ^ 2 / 2 := by
    norm_num
    ring
  have hk := kappa_ge_half_sq (u := 1 - 2 * p) (by linarith) (by linarith)
  unfold kappa at hk
  rw [binaryEntropy_eq_eta_rho']
  linarith [hdeg, hsc, hsq, hk]

end CK
