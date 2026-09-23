import CK.InfoContraction
import CK.NoiseOperator
import CK.Constants
import CK.EtaDeriv

/-!
# Large output bias (manuscript Lemma `lem:bias`)

If the output bias `|m| = |E signOf f|` is at least `13/20`, then `H(f(X)) = eta m` is at
most `log 2 − m²/2 < 1/2`, so the contraction bound `I(f(X);Y) ≤ ρ² H(f(X))`
(`information_le_contraction`) gives `I ≤ ρ²/2 ≤ κ(ρ) = log 2 − h(p)` by Pinsker
(`kappa_ge_half_sq`).
-/
noncomputable section
namespace CK
open scoped BigOperators

/-- `eta (1 − 2p) = h(p)` (since `(1 + (1 − 2p))/2 = 1 − p` and `h(1 − p) = h(p)`). -/
theorem eta_one_sub_two_mul (p : ℝ) : eta (1 - 2 * p) = binaryEntropy p := by
  unfold eta
  rw [show (1 + (1 - 2 * p)) / 2 = 1 - p by ring]
  exact binaryEntropy_symm p

/-- Under `|m| ≥ 13/20`, the output entropy `H(f(X)) = eta m` is below `1/2`
(`eta m ≤ log 2 − m²/2 ≤ 7/10 − 169/800 < 1/2`). -/
theorem binaryEntropy_mean_le_half {n : ℕ} (f : BooleanFunction n)
    (hm : 13 / 20 ≤ |avg (signOf f)|) : binaryEntropy (mean f) ≤ 1 / 2 := by
  have hmean0 := mean_nonneg f
  have hmean1 := mean_le_one f
  have hm_eq : avg (signOf f) = 2 * mean f - 1 := avg_signOf f
  have hm_lo : -1 ≤ avg (signOf f) := by linarith
  have hm_hi : avg (signOf f) ≤ 1 := by linarith
  have hm2 : (13 / 20 : ℝ) ^ 2 ≤ avg (signOf f) ^ 2 := by
    rw [← sq_abs (avg (signOf f))]
    exact pow_le_pow_left₀ (by norm_num) hm 2
  have hkm := kappa_ge_half_sq hm_lo hm_hi
  have hlog2 := AppF.row_log_q2_hi
  rw [binaryEntropy_mean_eq]
  unfold kappa at hkm
  nlinarith

/-- Lemma lem:bias: if |m| ≥ 13/20 then I(f(X);Y) ≤ κ(ρ) = log 2 − h(p), for every 0 ≤ p ≤ 1/2. -/
theorem large_bias {n : ℕ} (f : BooleanFunction n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (hm : 13 / 20 ≤ |avg (signOf f)|) :
    information f p ≤ Real.log 2 - binaryEntropy p := by
  have hH := binaryEntropy_mean_le_half f hm
  have hI := information_le_contraction f hp0 hp1
  have hkρ := kappa_ge_half_sq (u := 1 - 2 * p) (by linarith) (by linarith)
  unfold kappa at hkρ
  rw [eta_one_sub_two_mul] at hkρ
  have hsq : 0 ≤ (1 - 2 * p) ^ 2 := sq_nonneg _
  calc information f p ≤ (1 - 2 * p) ^ 2 * binaryEntropy (mean f) := hI
    _ ≤ (1 - 2 * p) ^ 2 * (1 / 2) := by gcongr
    _ = (1 - 2 * p) ^ 2 / 2 := by ring
    _ ≤ Real.log 2 - binaryEntropy p := hkρ

end CK
