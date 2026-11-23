import CK.BiasCoefficient
import CK.Shannon
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Sharp biased Bernoulli divergence bound

The Taylor integral is proved by differentiating an explicit primitive.
Convexity of reciprocal curvature bounds its integrand by the two endpoint
integrands. This avoids treating a numerical sample as a bound on the domain.
-/

noncomputable section
namespace CourtadeKumar
open Set MeasureTheory

def binaryDivergenceNats (a b : ℝ) : ℝ :=
  Real.binEntropy b - Real.binEntropy a +
    (a - b) * (Real.log (1 - b) - Real.log b)

@[simp] theorem binaryDivergenceNats_self (b : ℝ) : binaryDivergenceNats b b = 0 := by
  simp [binaryDivergenceNats]

@[simp] theorem binaryDivergenceNats_zero (b : ℝ) :
    binaryDivergenceNats 0 b = -Real.log (1 - b) := by
  simp only [binaryDivergenceNats, Real.binEntropy_zero, sub_zero, zero_sub,
    Real.binEntropy, Real.log_inv, Real.log_one]
  ring

@[simp] theorem binaryDivergenceNats_one (b : ℝ) :
    binaryDivergenceNats 1 b = -Real.log b := by
  simp only [binaryDivergenceNats, Real.binEntropy_one, sub_zero,
    Real.binEntropy, Real.log_inv, Real.log_one]
  ring

theorem binaryDivergenceNats_complement (a b : ℝ) :
    binaryDivergenceNats (1 - a) (1 - b) = binaryDivergenceNats a b := by
  simp only [binaryDivergenceNats, Real.binEntropy_one_sub, sub_sub_cancel]
  ring

theorem binaryDivergenceNats_deriv {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (b : ℝ) :
    HasDerivAt (fun x => binaryDivergenceNats x b)
      (Real.log a - Real.log (1 - a) + Real.log (1 - b) - Real.log b) a := by
  have h := ((hasDerivAt_const a (Real.binEntropy b)).sub
    (Real.hasDerivAt_binEntropy ha0.ne' ha1.ne)).add
      (((hasDerivAt_id a).sub_const b).mul_const (Real.log (1 - b) - Real.log b))
  convert h using 1
  simp [binaryDivergenceNats]
  ring

private theorem segment_mem_unit {a b t : ℝ} (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1)
    (ht : t ∈ Icc 0 1) : b + t * (a - b) ∈ Ioo 0 1 := by
  have h0 := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  constructor
  · by_cases h : a ≤ b
    · have := mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.mpr h)
      nlinarith [ha.1]
    · have := mul_nonneg ht.1 (sub_nonneg.mpr (le_of_not_ge h))
      linarith [hb.1]
  · by_cases h : a ≤ b
    · have := mul_nonneg ht.1 (sub_nonneg.mpr h)
      linarith [hb.2]
    · have := mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.mpr (le_of_not_ge h))
      nlinarith [ha.2]

private theorem curvature_integrable {a b : ℝ} (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) :
    IntervalIntegrable (fun t : ℝ => (1 - t) /
      ((b + t * (a - b)) * (1 - b - t * (a - b)))) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (continuousOn_const.sub continuousOn_id) (by fun_prop)
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  have hm := segment_mem_unit ha hb ht'
  apply mul_ne_zero hm.1.ne'
  linarith [hm.2]

private theorem taylor_primitive_deriv {a b t : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) (ht : t ∈ Icc 0 1) :
    HasDerivAt (fun u : ℝ =>
      (1 - u) * (a - b) * (Real.log (b + u * (a - b)) -
        Real.log (1 - b - u * (a - b)) + Real.log (1 - b) - Real.log b) +
      binaryDivergenceNats (b + u * (a - b)) b)
      ((a - b) ^ 2 * ((1 - t) /
        ((b + t * (a - b)) * (1 - b - t * (a - b))))) t := by
  let z := b + t * (a - b)
  have hz := segment_mem_unit ha hb ht
  have hz0 : z ≠ 0 := hz.1.ne'
  have hz1 : 1 - z ≠ 0 := by dsimp [z]; linarith [hz.2]
  have hz1' : 1 - b - t * (a - b) ≠ 0 := by linarith [hz.2]
  have hd : HasDerivAt (fun u : ℝ => b + u * (a - b)) (a - b) t := by
    convert ((hasDerivAt_id t).mul_const (a - b)).const_add b using 1
    simp
  have hd' : HasDerivAt (fun u : ℝ => 1 - b - u * (a - b)) (-(a - b)) t := by
    convert ((hasDerivAt_const t (1 - b)).sub ((hasDerivAt_id t).mul_const (a - b))) using 1
    simp
  have hlog0 := (hd.log hz0).sub (hd'.log hz1')
  have hlog := (hlog0.add_const (Real.log (1 - b))).sub_const (Real.log b)
  have hlin := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const (a - b)
  have hD := (binaryDivergenceNats_deriv hz.1 hz.2 b).comp t hd
  convert (hlin.mul hlog).add hD using 1
  dsimp [z] at *
  field_simp [hz0, hz1, hz1']
  ring

theorem binaryDivergenceNats_taylor_integral {a b : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) :
    binaryDivergenceNats a b = (a - b) ^ 2 *
      (∫ t : ℝ in (0 : ℝ)..1, (1 - t) /
        ((b + t * (a - b)) * (1 - b - t * (a - b)))) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => taylor_primitive_deriv ha hb (by simpa using ht))
    ((curvature_integrable ha hb).const_mul ((a - b) ^ 2))
  rw [intervalIntegral.integral_const_mul] at h
  have h0 : b + 0 * (a - b) = b := by ring
  have h1 : b + 1 * (a - b) = a := by ring
  simp only [h0, h1, sub_self, zero_mul, zero_add, binaryDivergenceNats_self,
    zero_sub, add_zero, sub_zero, mul_zero, one_mul] at h
  simpa using h.symm

def endpointCurvature (b t : ℝ) : ℝ :=
  1 / ((1 - b) * (b + (1 - b) * t))

private theorem endpointCurvature_integrable {b : ℝ} (hb : b ∈ Ioo 0 1) :
    IntervalIntegrable (endpointCurvature b) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro t ht
  have ht0 : 0 ≤ t := by simpa using ht.1
  have hm := mul_nonneg (sub_nonneg.mpr hb.2.le) ht0
  exact mul_ne_zero (ne_of_gt (sub_pos.mpr hb.2)) (ne_of_gt (by linarith [hb.1]))

theorem integral_endpointCurvature {b : ℝ} (hb : b ∈ Ioo 0 1) :
    (∫ t : ℝ in (0 : ℝ)..1, endpointCurvature b t) = -Real.log b / (1 - b) ^ 2 := by
  have hbne : 1 - b ≠ 0 := ne_of_gt (sub_pos.mpr hb.2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => Real.log (b + (1 - b) * t) / (1 - b) ^ 2)
    (f' := endpointCurvature b) (a := (0 : ℝ)) (b := 1) ?_ (endpointCurvature_integrable hb)
  · convert h using 1
    simp only [mul_one, add_sub_cancel, Real.log_one, zero_div, mul_zero, add_zero,
      zero_sub, neg_div]
  · intro t ht
    have ht0 : 0 ≤ t := by simpa using ht.1
    have hm := mul_nonneg (sub_nonneg.mpr hb.2.le) ht0
    have hz : b + (1 - b) * t ≠ 0 := ne_of_gt (by linarith [hb.1])
    have hd := (((hasDerivAt_id t).const_mul (1 - b)).const_add b).log hz
    convert hd.div_const ((1 - b) ^ 2) using 1
    unfold endpointCurvature
    field_simp [hbne, hz]
    ring

/-- Convexity of reciprocal curvature, with the two endpoint singularities canceled. -/
private theorem curvature_le_endpoints {a b t : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) (ht : t ∈ Icc 0 1) :
    (1 - t) / ((b + t * (a - b)) * (1 - b - t * (a - b))) ≤
      (1 - a) * endpointCurvature (1 - b) t + a * endpointCurvature b t := by
  have hz := segment_mem_unit ha hb ht
  have hz0 : b + t * (a - b) ≠ 0 := hz.1.ne'
  have hz1 : 1 - b - t * (a - b) ≠ 0 := by linarith [hz.2]
  by_cases ht1 : t = 1
  · rw [ht1]
    simp only [sub_self, zero_div]
    unfold endpointCurvature
    have hp0 : 0 < 1 - a := sub_pos.mpr ha.2
    have hp1 : 0 < 1 - b := sub_pos.mpr hb.2
    have ha0 := ha.1
    have hb0 := hb.1
    simp only [sub_sub_cancel, mul_one, sub_add_cancel, add_sub_cancel_left]
    positivity
  have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
  let u := b * (1 - t)
  let v := b + (1 - b) * t
  have hu : 0 < u := mul_pos hb.1 (sub_pos.mpr htlt)
  have hv : 0 < v := by
    have hm := mul_nonneg (sub_nonneg.mpr hb.2.le) ht.1
    dsimp [v]
    linarith [hb.1]
  have hu1 : 0 < 1 - u := by
    have hm := mul_nonneg hb.1.le ht.1
    dsimp [u]
    nlinarith [hb.2]
  have hv1 : 0 < 1 - v := by
    dsimp [v]
    nlinarith [mul_pos (sub_pos.mpr hb.2) (sub_pos.mpr htlt)]
  have hi := (convexOn_zpow (𝕜 := ℝ) (-1)).2 hu hv
    (sub_nonneg.mpr ha.2.le) ha.1.le (by ring : (1 - a) + a = 1)
  have hi' := (convexOn_zpow (𝕜 := ℝ) (-1)).2 hu1 hv1
    (sub_nonneg.mpr ha.2.le) ha.1.le (by ring : (1 - a) + a = 1)
  simp only [zpow_neg_one, smul_eq_mul, inv_eq_one_div] at hi hi'
  have he : (1 - a) * u + a * v = b + t * (a - b) := by dsimp [u, v]; ring
  have he' : (1 - a) * (1 - u) + a * (1 - v) = 1 - b - t * (a - b) := by
    dsimp [u, v]; ring
  rw [he] at hi
  rw [he'] at hi'
  have hsum : 1 / (b + t * (a - b)) + 1 / (1 - b - t * (a - b)) ≤
      (1 - a) * (1 / u + 1 / (1 - u)) + a * (1 / v + 1 / (1 - v)) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr ht.2)
  have hleft : (1 - t) * (1 / (b + t * (a - b)) + 1 / (1 - b - t * (a - b))) =
      (1 - t) / ((b + t * (a - b)) * (1 - b - t * (a - b))) := by
    field_simp [hz0, hz1]
  have hU : (1 - t) * (1 / u + 1 / (1 - u)) = endpointCurvature (1 - b) t := by
    have hbne : b ≠ 0 := hb.1.ne'
    have heU : endpointCurvature (1 - b) t = 1 / (b * (1 - u)) := by
      unfold endpointCurvature
      congr 1
      dsimp [u]
      ring
    rw [heU]
    field_simp [hbne, hu.ne', hu1.ne']
    dsimp [u]
    ring
  have hV : (1 - t) * (1 / v + 1 / (1 - v)) = endpointCurvature b t := by
    change (1 - t) * (1 / v + 1 / (1 - v)) = 1 / ((1 - b) * v)
    have hbne : 1 - b ≠ 0 := ne_of_gt (sub_pos.mpr hb.2)
    field_simp [hbne, hv.ne', hv1.ne']
    dsimp [v]
    ring
  rw [hleft] at hmul
  calc
    _ ≤ (1 - t) * ((1 - a) * (1 / u + 1 / (1 - u)) +
        a * (1 / v + 1 / (1 - v))) := hmul
    _ = (1 - a) * ((1 - t) * (1 / u + 1 / (1 - u))) +
        a * ((1 - t) * (1 / v + 1 / (1 - v))) := by ring
    _ = _ := by rw [hU, hV]

theorem binaryDivergenceNats_interpolated_bound {a b : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) :
    binaryDivergenceNats a b ≤ (a - b) ^ 2 *
      ((1 - a) * (-Real.log (1 - b) / b ^ 2) + a * (-Real.log b / (1 - b) ^ 2)) := by
  have hb' : 1 - b ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hb.1, hb.2]
  have hi0 := endpointCurvature_integrable hb'
  have hi1 := endpointCurvature_integrable hb
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (curvature_integrable ha hb) ((hi0.const_mul (1 - a)).add (hi1.const_mul a))
    (fun t ht => curvature_le_endpoints ha hb ht)
  rw [intervalIntegral.integral_add (hi0.const_mul (1 - a)) (hi1.const_mul a),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_endpointCurvature hb', integral_endpointCurvature hb] at h
  rw [binaryDivergenceNats_taylor_integral ha hb]
  simpa only [sub_sub_cancel] using mul_le_mul_of_nonneg_left h (sq_nonneg (a - b))

def endpointCoefficientGap (b : ℝ) : ℝ :=
  -b ^ 2 * Real.log b + (1 - b) ^ 2 * Real.log (1 - b)

private theorem continuous_endpointCoefficientGap : Continuous endpointCoefficientGap := by
  have he : endpointCoefficientGap = fun b : ℝ =>
      -(b * (b * Real.log b)) + (1 - b) * ((1 - b) * Real.log (1 - b)) := by
    funext b
    unfold endpointCoefficientGap
    ring
  rw [he]
  exact (continuous_id.mul Real.continuous_mul_log).neg.add
    ((continuous_const.sub continuous_id).mul
      (Real.continuous_mul_log.comp (continuous_const.sub continuous_id)))

private theorem endpointCoefficientGap_deriv {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    HasDerivAt endpointCoefficientGap (2 * Real.binEntropy b - 1) b := by
  have hc := (hasDerivAt_const b (1 : ℝ)).sub (hasDerivAt_id b)
  have hleft := (((hasDerivAt_id b).pow 2).mul (Real.hasDerivAt_log hb0.ne')).neg
  have hright := (hc.pow 2).mul (hc.log (by linarith : 1 - b ≠ 0))
  convert hleft.add hright using 1
  · funext y
    unfold endpointCoefficientGap
    simp only [id_eq]
    ring
  · simp only [Real.binEntropy, Real.log_inv]
    field_simp [hb0.ne', ne_of_gt (sub_pos.mpr hb1)]
    ring

private theorem endpointCoefficientGap_concave :
    ConcaveOn ℝ (Icc (1 / 2) 1) endpointCoefficientGap := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (1 / 2 : ℝ) 1)
    (f' := fun b => 2 * Real.binEntropy b - 1)
    (f'' := fun b => 2 * (Real.log (1 - b) - Real.log b))
  · exact continuous_endpointCoefficientGap.continuousOn
  · intro b hb
    rw [interior_Icc] at hb
    exact (endpointCoefficientGap_deriv (by linarith [hb.1]) hb.2).hasDerivWithinAt
  · intro b hb
    rw [interior_Icc] at hb
    have hbase := Real.hasDerivAt_binEntropy (by linarith [hb.1] : b ≠ 0) hb.2.ne
    have h := (hbase.const_mul 2).sub_const 1
    exact h.hasDerivWithinAt
  · intro b hb
    rw [interior_Icc] at hb
    have hlog := Real.log_le_log (by linarith [hb.2] : 0 < 1 - b)
      (by linarith [hb.1] : 1 - b ≤ b)
    linarith

theorem endpointCoefficientGap_nonneg {b : ℝ} (hb0 : 1 / 2 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ endpointCoefficientGap b := by
  have h := endpointCoefficientGap_concave.2
    (by norm_num : (1 / 2 : ℝ) ∈ Icc (1 / 2) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (1 / 2) 1)
    (by linarith : 0 ≤ 2 * (1 - b)) (by linarith : 0 ≤ 2 * b - 1)
    (by ring : 2 * (1 - b) + (2 * b - 1) = 1)
  have hhalf : endpointCoefficientGap (1 / 2) = 0 := by
    unfold endpointCoefficientGap
    norm_num
  have hone : endpointCoefficientGap 1 = 0 := by norm_num [endpointCoefficientGap]
  simpa only [smul_eq_mul, hhalf, hone, mul_zero, add_zero,
    show 2 * (1 - b) * (1 / 2) + (2 * b - 1) * 1 = b by ring] using h

theorem divergence_endpoint_coefficient_order {b : ℝ}
    (hb0 : 1 / 2 ≤ b) (hb1 : b < 1) :
    -Real.log (1 - b) / b ^ 2 ≤ -Real.log b / (1 - b) ^ 2 := by
  have hbpos : 0 < b := by linarith
  apply (div_le_div_iff₀ (sq_pos_of_pos hbpos) (sq_pos_of_pos (sub_pos.mpr hb1))).mpr
  have h := endpointCoefficientGap_nonneg hb0 hb1.le
  unfold endpointCoefficientGap at h
  nlinarith

/-- The sharp upper Bernoulli-divergence estimate in Lemma `binary-divergence-comparison`. -/
theorem binaryDivergenceNats_upper {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 1 / 2 ≤ b) (hb1 : b < 1) :
    binaryDivergenceNats a b ≤ (-Real.log b / (1 - b) ^ 2) * (a - b) ^ 2 := by
  have hbpos : 0 < b := by linarith
  have horder := divergence_endpoint_coefficient_order hb0 hb1
  have hclosed : IsClosed {x : ℝ | binaryDivergenceNats x b ≤
      (-Real.log b / (1 - b) ^ 2) * (x - b) ^ 2} := by
    apply isClosed_le
    · unfold binaryDivergenceNats
      fun_prop
    · fun_prop
  have hinterior : Ioo (0 : ℝ) 1 ⊆ {x : ℝ | binaryDivergenceNats x b ≤
      (-Real.log b / (1 - b) ^ 2) * (x - b) ^ 2} := by
    intro x hx
    have hi := binaryDivergenceNats_interpolated_bound hx ⟨hbpos, hb1⟩
    have hm := mul_le_mul_of_nonneg_left horder (sub_nonneg.mpr hx.2.le)
    have hmix : (1 - x) * (-Real.log (1 - b) / b ^ 2) +
        x * (-Real.log b / (1 - b) ^ 2) ≤ -Real.log b / (1 - b) ^ 2 := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hmix (sq_nonneg (x - b))
    simpa [mul_comm] using hi.trans hp
  have hclosure := hclosed.closure_subset_iff.mpr hinterior
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hclosure
  exact hclosure ⟨ha0, ha1⟩

/-- Symmetric form, using the manuscript's exact piecewise coefficient. -/
theorem binaryDivergenceNats_le_biasCoefficient {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b < 1) :
    binaryDivergenceNats a b ≤ 4 * biasCoefficient b * (a - b) ^ 2 := by
  by_cases hbhalf : 1 / 2 ≤ b
  · have h := binaryDivergenceNats_upper ha0 ha1 hbhalf hb1
    have he : 4 * biasCoefficient b = -Real.log b / (1 - b) ^ 2 := by
      rw [biasCoefficient, if_pos hbhalf, biasCoefficientUpper]
      simp only [one_div, Real.log_inv]
      field_simp [ne_of_gt (sub_pos.mpr hb1)]
      ring
    rw [he]
    exact h
  · have h := binaryDivergenceNats_upper (by linarith : 0 ≤ 1 - a)
      (by linarith : 1 - a ≤ 1) (by linarith : 1 / 2 ≤ 1 - b) (by linarith : 1 - b < 1)
    rw [binaryDivergenceNats_complement] at h
    have he : 4 * biasCoefficient b = -Real.log (1 - b) / b ^ 2 := by
      rw [biasCoefficient, if_neg hbhalf, biasCoefficientUpper]
      simp only [one_div, Real.log_inv, sub_sub_cancel]
      field_simp [hb0.ne']
      ring
    rw [he]
    convert h using 1
    ring

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem expect_binaryDivergenceNats (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.expect (fun ω => binaryDivergenceNats (f ω) (μ.expect f)) =
      Real.log 2 * μ.shannonGap f := by
  unfold binaryDivergenceNats
  rw [μ.expect_add, μ.expect_sub, μ.expect_const, μ.expect_mul_const,
    μ.expect_sub, μ.expect_const]
  simp only [sub_self, zero_mul, add_zero]
  have he : Real.binEntropy (μ.expect f) = Real.log 2 * entropyBits (μ.expect f) := by
    unfold entropyBits
    field_simp [log_two_pos.ne']
  rw [he, μ.expect_binEntropy]
  unfold shannonGap
  ring

theorem shannonGap_le_biasCoefficient (μ : FiniteLaw Ω) (f : Ω → ℝ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hf1 : ∀ ω, f ω ≤ 1)
    (hmean0 : 0 < μ.expect f) (hmean1 : μ.expect f < 1) :
    μ.shannonGap f ≤ biasCoefficient (μ.expect f) / Real.log 2 *
      (quadraticEntropy (μ.expect f) - μ.expect (fun ω => quadraticEntropy (f ω))) := by
  have h := μ.expect_mono (fun ω =>
    binaryDivergenceNats_le_biasCoefficient (hf0 ω) (hf1 ω) hmean0 hmean1)
  rw [μ.expect_binaryDivergenceNats, μ.expect_const_mul] at h
  calc
    μ.shannonGap f ≤ (4 * biasCoefficient (μ.expect f) *
        μ.expect (fun ω => (f ω - μ.expect f) ^ 2)) / Real.log 2 := by
          apply (le_div_iff₀ log_two_pos).mpr
          simpa [mul_comm] using h
    _ = _ := by rw [μ.quadratic_gap]; ring

/-- Complete finite-law biased-information estimate from Lemma `biased-comparison`. -/
theorem shannonInformation_le_biasCoefficient {Z : Type*} [Fintype Z] [DecidableEq Z]
    (μ : FiniteLaw Ω) (z : Ω → Z) (c : Ω → ℝ)
    (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1)
    (hmean0 : 0 < μ.expect c) (hmean1 : μ.expect c < 1) :
    μ.shannonInformation c z ≤ biasCoefficient (μ.expect c) / Real.log 2 *
      μ.quadraticInformation c z := by
  have hm := μ.total_expectation z hc0 hc1
  have h := (μ.map z).shannonGap_le_biasCoefficient (μ.conditionalMean z c)
    (μ.conditionalMean_nonneg z hc0) (μ.conditionalMean_le_one z hc1)
    (by rw [hm]; exact hmean0) (by rw [hm]; exact hmean1)
  simpa [shannonGap, shannonInformation, quadraticInformation,
    conditionalShannonEntropy, conditionalQuadraticEntropy, hm] using h

end FiniteLaw
end CourtadeKumar
