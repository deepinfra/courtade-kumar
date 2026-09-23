import CK.Transfer
import CK.EntropyBounds
import CK.Constants

/-!
# The `(a,b) ↔ (ν,t)` coordinate bridge and the trivial regimes (manuscript Sec. 3.1)

Dictionary: `t = |a - b|`, `ν = |a + b - 1|`, `ρ = 1 - 2p`,
`J = pairEntropy ν t`, `M = pairEntropy ν (ρt)`, `K = M - J`, `ℓ = h(p)·t`.

* `binaryEntropy_eq_eta`, `half_sum_entropy_eq`, `mixedEntropy_eq`, `scalarSlack_eq`:
  the scalar slack of `lem:mixing` in centered coordinates,
  `q(d) = K + M d² - 2 ℓ d`.
* `nu_add_t_le_one`, `abs_sub_eq_one_cases`: the admissible region `ν + t ≤ 1` and
  the corners `t = 1`.
* `scalarSlack_nonneg_of_eq`, `scalarSlack_endpoints`: the trivial regimes `t = 0`
  and `t = 1` from the last paragraph of the proof of `lem:mixing`.
-/
noncomputable section
namespace CK

/-! ## Parity lemmas for `pairEntropy` -/

/-- `h(a) = η(2a - 1)` since `η(u) = h((1+u)/2)`. -/
theorem binaryEntropy_eq_eta (a : ℝ) : binaryEntropy a = eta (2 * a - 1) := by
  unfold eta
  congr 1
  ring

/-- `pairEntropy ν z` is even in `z` (the two terms of the sum swap). -/
theorem pairEntropy_neg_right (nu z : ℝ) : pairEntropy nu (-z) = pairEntropy nu z := by
  unfold pairEntropy
  rw [show nu + -z = nu - z by ring, show nu - -z = nu + z by ring]
  ring

/-- `pairEntropy` only depends on `|ν|` (evenness of `η`). -/
theorem pairEntropy_abs_left (s z : ℝ) : pairEntropy |s| z = pairEntropy s z := by
  rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  unfold pairEntropy
  rw [show -s + z = -(s - z) by ring, show -s - z = -(s + z) by ring, eta_even, eta_even]
  ring

/-- `pairEntropy ν (c·|u|) = pairEntropy ν (c·u)` by evenness in the second argument. -/
theorem pairEntropy_mul_abs (nu c u : ℝ) : pairEntropy nu (c * |u|) = pairEntropy nu (c * u) := by
  rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  rw [mul_neg, pairEntropy_neg_right]

theorem pairEntropy_abs_right (nu u : ℝ) : pairEntropy nu |u| = pairEntropy nu u := by
  have h := pairEntropy_mul_abs nu 1 u
  rwa [one_mul, one_mul] at h

/-! ## The bridge identities (manuscript Sec. 3.1) -/

/-- `(h(a) + h(b))/2 = J(ν, t)` with `ν = |a + b - 1|`, `t = |a - b|`. -/
theorem half_sum_entropy_eq (a b : ℝ) :
    (binaryEntropy a + binaryEntropy b) / 2 = pairEntropy |a + b - 1| |a - b| := by
  rw [pairEntropy_abs_left, pairEntropy_abs_right, binaryEntropy_eq_eta a,
    binaryEntropy_eq_eta b]
  unfold pairEntropy
  rw [show a + b - 1 + (a - b) = 2 * a - 1 by ring,
    show a + b - 1 - (a - b) = 2 * b - 1 by ring]

/-- The mixed entropy is `M(ν, ρt)` with `ρ = 1 - 2p`. -/
theorem mixedEntropy_eq (p a b : ℝ) :
    mixedEntropy p a b = pairEntropy |a + b - 1| ((1 - 2 * p) * |a - b|) := by
  rw [pairEntropy_abs_left, pairEntropy_mul_abs]
  unfold mixedEntropy pairEntropy
  rw [binaryEntropy_eq_eta ((1 - p) * a + p * b), binaryEntropy_eq_eta (p * a + (1 - p) * b),
    show 2 * ((1 - p) * a + p * b) - 1 = a + b - 1 + (1 - 2 * p) * (a - b) by ring,
    show 2 * (p * a + (1 - p) * b) - 1 = a + b - 1 - (1 - 2 * p) * (a - b) by ring]

/-- The scalar slack in centered coordinates: `q(d) = K + M d² - 2 ℓ d`. -/
theorem scalarSlack_eq (p d a b : ℝ) :
    scalarSlack p d a b =
      (pairEntropy |a + b - 1| ((1 - 2 * p) * |a - b|) - pairEntropy |a + b - 1| |a - b|)
        + pairEntropy |a + b - 1| ((1 - 2 * p) * |a - b|) * d ^ 2
        - 2 * (binaryEntropy p * |a - b|) * d := by
  unfold scalarSlack
  rw [mixedEntropy_eq, half_sum_entropy_eq]
  ring

/-! ## The admissible region -/

/-- `ν + t ≤ 1` for `a, b ∈ [0,1]`. -/
theorem nu_add_t_le_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |a + b - 1| + |a - b| ≤ 1 := by
  rcases abs_cases (a + b - 1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (a - b) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> rw [h1, h2] <;> linarith

/-- `t = 1` only at the two corners `(0,1)` and `(1,0)`. -/
theorem abs_sub_eq_one_cases {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (h : |a - b| = 1) : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  rcases abs_cases (a - b) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h] at h1
  · right; constructor <;> linarith
  · left; constructor <;> linarith

/-! ## The trivial regimes `t = 0` and `t = 1` (proof of `lem:mixing`, last paragraph) -/

/-- t = 0: the slack is d² h(a) ≥ 0. -/
theorem scalarSlack_nonneg_of_eq {p d a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ scalarSlack p d a a := by
  unfold scalarSlack mixedEntropy
  rw [show (1 - p) * a + p * a = a by ring, show p * a + (1 - p) * a = a by ring, sub_self,
    abs_zero]
  have hh := binaryEntropy_nonneg' ha0 ha1
  nlinarith [mul_nonneg (sq_nonneg d) hh]

/-- `p ≤ h(p)` for `0 < p ≤ 1/20`: `h(p) ≥ p log(1/p) ≥ p log 20 ≥ p`. -/
theorem le_binaryEntropy_of_small' {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) :
    p ≤ binaryEntropy p := by
  unfold binaryEntropy
  have h20 : Real.log 20 ≤ Real.log (1 / p) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hp0]; linarith)
  rw [Real.log_div one_ne_zero hp0.ne', Real.log_one] at h20
  have hl20 := AppF.row_log_q20_lo
  have hlog1p : Real.log (1 - p) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h1 : 0 ≤ -(1 - p) * Real.log (1 - p) := by nlinarith
  have h2 : p * 1 ≤ p * (-Real.log p) := mul_le_mul_of_nonneg_left (by linarith) hp0.le
  nlinarith

/-- t = 1: the slack is h(p)(1−d)² ≥ h(p)/4 ≥ p/4. -/
theorem scalarSlack_endpoints {p d : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 20) (hd0 : 0 ≤ d)
    (hd : d ≤ 1 / 2) :
    p / 4 ≤ scalarSlack p d 0 1 ∧ p / 4 ≤ scalarSlack p d 1 0 := by
  have hpe := le_binaryEntropy_of_small' hp0 hp1
  have hsq : 1 / 4 ≤ (1 - d) ^ 2 := by
    -- `0 ≤ d` is not needed for this bound; it is kept as the manuscript's hypothesis.
    have _ := hd0
    nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1 / 2) (by linarith : 1 / 2 ≤ 1 - d)]
  have hkey : ∀ x : ℝ, x = binaryEntropy p * (1 - d) ^ 2 → p / 4 ≤ x := by
    intro x hx
    rw [hx]
    have := mul_le_mul_of_nonneg_left hsq (le_trans hp0.le hpe)
    linarith
  constructor
  · apply hkey
    unfold scalarSlack mixedEntropy
    rw [show (1 - p) * 0 + p * 1 = p by ring, show p * 0 + (1 - p) * 1 = 1 - p by ring,
      binaryEntropy_symm, binaryEntropy_zero, binaryEntropy_one,
      show (0 : ℝ) - 1 = -1 by ring, abs_neg, abs_one]
    ring
  · apply hkey
    unfold scalarSlack mixedEntropy
    rw [show (1 - p) * 1 + p * 0 = 1 - p by ring, show p * 1 + (1 - p) * 0 = p by ring,
      binaryEntropy_symm, binaryEntropy_zero, binaryEntropy_one, sub_zero, abs_one]
    ring

end CK
