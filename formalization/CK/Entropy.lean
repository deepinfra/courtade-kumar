import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

/-!+# Binary entropy and progressive entropy, in bits

The power-series argument is adapted from the repository's earlier
`CK/KappaSeries.lean` (commit a42afce1b0d2c2c2f05d5845478faa1570c14e63).
It is rebuilt here with the definitions and units of the November 20 paper.
-/

noncomputable section
namespace CourtadeKumar
open scoped BigOperators

/-- Shannon entropy of a Bernoulli variable, in bits, including both endpoints. -/
def entropyBits (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- Natural-log version of the divergence from an unbiased bit. -/
def divergenceNats (u : ℝ) : ℝ := Real.log 2 - Real.binEntropy ((1 + u) / 2)

/-- `I_p` in the manuscript. -/
def noiseInformation (p : ℝ) : ℝ := 1 - entropyBits p

/-- The squared correlation, called barred `I_p` in the manuscript. -/
def noiseCorrelationSq (p : ℝ) : ℝ := (1 - 2 * p) ^ 2

/-- `J_p` in the manuscript. -/
def noiseGap (p : ℝ) : ℝ := noiseCorrelationSq p - noiseInformation p

/-- `Q(C)` for a bit whose mean is `mu`, with the channel parameter held fixed. -/
def progressiveEntropy (p μ : ℝ) : ℝ :=
  noiseCorrelationSq p * entropyBits μ - noiseGap p * (4 * μ * (1 - μ))

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

@[simp] theorem entropyBits_zero : entropyBits 0 = 0 := by simp [entropyBits]
@[simp] theorem entropyBits_one : entropyBits 1 = 0 := by simp [entropyBits]
@[simp] theorem entropyBits_half : entropyBits (1 / 2) = 1 := by
  unfold entropyBits
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv,
    div_self (ne_of_gt log_two_pos)]

@[simp] theorem entropyBits_complement (p : ℝ) : entropyBits (1 - p) = entropyBits p := by
  simp [entropyBits]

theorem entropyBits_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ entropyBits p := div_nonneg (Real.binEntropy_nonneg hp0 hp1) log_two_pos.le

theorem entropyBits_le_one (p : ℝ) : entropyBits p ≤ 1 := by
  apply (div_le_iff₀ log_two_pos).mpr
  simpa using (Real.binEntropy_le_log_two (p := p))

theorem continuous_divergenceNats : Continuous divergenceNats := by
  unfold divergenceNats
  fun_prop

@[simp] theorem divergenceNats_even (u : ℝ) : divergenceNats (-u) = divergenceNats u := by
  unfold divergenceNats
  have he : (1 + -u) / 2 = 1 - (1 + u) / 2 := by ring
  rw [he, Real.binEntropy_one_sub]

@[simp] theorem divergenceNats_one : divergenceNats 1 = Real.log 2 := by
  norm_num [divergenceNats]

theorem divergenceNats_closed {u : ℝ} (hu0 : -1 < u) (hu1 : u < 1) :
    divergenceNats u =
      (Real.log (1 - u ^ 2) + u * (Real.log (1 + u) - Real.log (1 - u))) / 2 := by
  unfold divergenceNats Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 : (0 : ℝ) < 1 - u := by linarith
  rw [show (1 - (1 + u) / 2 : ℝ) = (1 - u) / 2 by ring,
    Real.log_div (ne_of_gt h1) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div (ne_of_gt h2) (by norm_num : (2 : ℝ) ≠ 0),
    show (1 - u ^ 2 : ℝ) = (1 + u) * (1 - u) by ring,
    Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]
  ring

/-- Equation `binary-divergence-series`, interior case, with index `k=n+1`. -/
theorem hasSum_divergenceNats {u : ℝ} (hu : |u| < 1) :
    HasSum (fun n : ℕ =>
      u ^ (2 * (n + 1)) / ((2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1)))
      (divergenceNats u) := by
  have hu0 : -1 < u := (abs_lt.mp hu).1
  have hu1 : u < 1 := (abs_lt.mp hu).2
  have hsq : |u ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg u)]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - u)
      (by linarith : (0 : ℝ) < 1 + u)]
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
  · rw [divergenceNats_closed hu0 hu1]
    ring

theorem divergenceNats_scaling_interior {θ u : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hu : |u| < 1) :
    divergenceNats (θ * u) ≤ θ ^ 2 * divergenceNats u := by
  have hθu : |θ * u| < 1 := by
    rw [abs_mul, abs_of_nonneg hθ0]
    calc θ * |u| ≤ 1 * |u| := mul_le_mul_of_nonneg_right hθ1 (abs_nonneg u)
      _ = |u| := one_mul _
      _ < 1 := hu
  refine hasSum_le (fun n => ?_) (hasSum_divergenceNats hθu)
    ((hasSum_divergenceNats hu).mul_left (θ ^ 2))
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hD : 0 < (2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1) - 1) := by
    apply mul_pos <;> linarith
  have hpow : (θ * u) ^ (2 * (n + 1)) ≤ θ ^ 2 * u ^ (2 * (n + 1)) := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hθ0 hθ1 (by omega)) ?_
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg u) _
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hpow hD.le

/-- Data processing for two unbiased binary channels, including endpoints. -/
theorem divergenceNats_scaling {θ u : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hu0 : -1 ≤ u) (hu1 : u ≤ 1) :
    divergenceNats (θ * u) ≤ θ ^ 2 * divergenceNats u := by
  have hcl : IsClosed {v : ℝ | divergenceNats (θ * v) ≤ θ ^ 2 * divergenceNats v} :=
    isClosed_le (continuous_divergenceNats.comp (continuous_const.mul continuous_id))
      (continuous_const.mul continuous_divergenceNats)
  have hsub : Set.Ioo (-1 : ℝ) 1 ⊆
      {v : ℝ | divergenceNats (θ * v) ≤ θ ^ 2 * divergenceNats v} :=
    fun v hv => divergenceNats_scaling_interior hθ0 hθ1 (abs_lt.mpr hv)
  have hcls := hcl.closure_subset_iff.mpr hsub
  rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] at hcls
  exact hcls ⟨hu0, hu1⟩

theorem divergenceNats_upper {u : ℝ} (hu0 : -1 ≤ u) (hu1 : u ≤ 1) :
    divergenceNats u ≤ u ^ 2 * Real.log 2 := by
  by_cases hu : 0 ≤ u
  · simpa using divergenceNats_scaling hu hu1 (by norm_num : (-1 : ℝ) ≤ 1) le_rfl
  · have hu' : 0 ≤ -u := by linarith
    have h := divergenceNats_scaling hu' (by linarith : -u ≤ 1)
      (by norm_num : (-1 : ℝ) ≤ 1) le_rfl
    simpa using h

theorem divergenceNats_lower {u : ℝ} (hu0 : -1 ≤ u) (hu1 : u ≤ 1) :
    u ^ 2 / 2 ≤ divergenceNats u := by
  have hcl : IsClosed {v : ℝ | v ^ 2 / 2 ≤ divergenceNats v} :=
    isClosed_le (by fun_prop) continuous_divergenceNats
  have hsub : Set.Ioo (-1 : ℝ) 1 ⊆ {v : ℝ | v ^ 2 / 2 ≤ divergenceNats v} := by
    intro v hv
    have h := le_hasSum (hasSum_divergenceNats (abs_lt.mpr hv)) 0
      (fun n _ => by
        apply div_nonneg
        · rw [pow_mul]; exact pow_nonneg (sq_nonneg v) _
        · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          apply mul_nonneg <;> linarith)
    norm_num at h
    exact h
  have hcls := hcl.closure_subset_iff.mpr hsub
  rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] at hcls
  exact hcls ⟨hu0, hu1⟩

/-- The lower Shannon/Tsallis comparison in Lemma `tsallis-properties` (i). -/
theorem quadratic_le_entropyBits {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    4 * μ * (1 - μ) ≤ entropyBits μ := by
  have h := divergenceNats_upper (by linarith : -1 ≤ 2 * μ - 1)
    (by linarith : 2 * μ - 1 ≤ 1)
  unfold divergenceNats at h
  rw [show (1 + (2 * μ - 1)) / 2 = μ by ring] at h
  unfold entropyBits
  apply (le_div_iff₀ log_two_pos).mpr
  nlinarith

/-- The upper Shannon/Tsallis comparison in Lemma `tsallis-properties` (i). -/
theorem entropyBits_le_quadratic_upper {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    entropyBits μ ≤ (1 + 4 * μ * (1 - μ)) / 2 := by
  have h := divergenceNats_lower (by linarith : -1 ≤ 2 * μ - 1)
    (by linarith : 2 * μ - 1 ≤ 1)
  unfold divergenceNats at h
  rw [show (1 + (2 * μ - 1)) / 2 = μ by ring] at h
  have hL : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hsq := mul_nonneg (sq_nonneg (2 * μ - 1)) (sub_nonneg.mpr hL)
  unfold entropyBits
  apply (div_le_iff₀ log_two_pos).mpr
  nlinarith

theorem noiseGap_bounds {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ noiseGap p ∧ noiseGap p ≤ noiseInformation p := by
  have hlow := quadratic_le_entropyBits hp0 hp1
  have hupp := entropyBits_le_quadratic_upper hp0 hp1
  unfold noiseGap noiseCorrelationSq noiseInformation
  constructor <;> nlinarith

/-- Lemma `ck+to_ck`, uniformly for all channel parameters in `[0,1]`. -/
theorem progressiveEntropy_le_noiseInformation {p μ : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    progressiveEntropy p μ ≤ noiseInformation p := by
  have hJ := noiseGap_bounds hp0 hp1
  have hH := entropyBits_le_quadratic_upper hμ0 hμ1
  have hH1 := entropyBits_le_one μ
  have hstep1 := mul_le_mul_of_nonneg_left
    (show entropyBits μ - 4 * μ * (1 - μ) ≤ 1 - entropyBits μ by linarith) hJ.1
  have hstep2 := mul_le_mul_of_nonneg_right hJ.2 (sub_nonneg.mpr hH1)
  unfold progressiveEntropy noiseGap at *
  nlinarith

@[simp] theorem progressiveEntropy_zero (p : ℝ) : progressiveEntropy p 0 = 0 := by
  simp [progressiveEntropy]

@[simp] theorem progressiveEntropy_one (p : ℝ) : progressiveEntropy p 1 = 0 := by
  simp [progressiveEntropy]

@[simp] theorem progressiveEntropy_half (p : ℝ) :
    progressiveEntropy p (1 / 2) = noiseInformation p := by
  rw [progressiveEntropy, entropyBits_half]
  norm_num [noiseGap]

@[simp] theorem noiseInformation_complement (p : ℝ) :
    noiseInformation (1 - p) = noiseInformation p := by
  simp [noiseInformation]

@[simp] theorem noiseCorrelationSq_complement (p : ℝ) :
    noiseCorrelationSq (1 - p) = noiseCorrelationSq p := by
  unfold noiseCorrelationSq
  ring

@[simp] theorem progressiveEntropy_complement_noise (p μ : ℝ) :
    progressiveEntropy (1 - p) μ = progressiveEntropy p μ := by
  simp [progressiveEntropy, noiseGap]

end CourtadeKumar
