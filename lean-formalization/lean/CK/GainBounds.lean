import CK.Transfer

/-!
# Layer C, part 1: the gain integral and elementary entropy bounds

* `gain_integral` (eq:gainintegral, integral-free): `K₀ ≥ 2pt·atanhLog((1-p)t)`,
  by midpoint Jensen for `atanhLog` — which is exactly `Lpair_le` at `r = 0`.
* `atanhLog_le_mul_curvature` and `atanhLog_div_le_atanhLog_div`: `atanh u ≤ u/(1-u²)`
  and monotonicity of `atanh u / u` (the manuscript's nonnegative-coefficient series).
* Bounds for `𝓑(s) = -(1-s)/s·ln(1-s)` (eq:Bbounds), stated as log inequalities.
* `binaryEntropy_le_mul` : `h(p) ≤ p(ln(1/p)+1)`.
-/
noncomputable section
namespace CK

/-! ## `atanh u ≤ u/(1-u²)` and monotonicity of `atanh u / u` -/

theorem atanhLog_le_mul_curvature {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    atanhLog u ≤ u * curvature u := by
  have hmono : MonotoneOn (fun v : ℝ => v * curvature v - atanhLog v) (Set.Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro v hv
      have hv1 : v < 1 := lt_of_le_of_lt hv.2 hu1
      have hv0 : (-1 : ℝ) < v := by linarith [hv.1]
      have hd : HasDerivAt (fun v : ℝ => v * curvature v - atanhLog v)
          (1 * curvature v + v * (2 * v / (1 - v ^ 2) ^ 2) - curvature v) v :=
        ((hasDerivAt_id v).mul (hasDerivAt_curvature hv0 hv1)).sub
          (hasDerivAt_atanhLog hv0 hv1)
      exact hd.continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro v hv
      have hv1 : v < 1 := lt_trans hv.2 hu1
      have hv0 : (-1 : ℝ) < v := by linarith [hv.1]
      have hd : HasDerivAt (fun v : ℝ => v * curvature v - atanhLog v)
          (1 * curvature v + v * (2 * v / (1 - v ^ 2) ^ 2) - curvature v) v :=
        ((hasDerivAt_id v).mul (hasDerivAt_curvature hv0 hv1)).sub
          (hasDerivAt_atanhLog hv0 hv1)
      exact hd.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro v hv
      have hv1 : v < 1 := lt_trans hv.2 hu1
      have hv0 : (-1 : ℝ) < v := by linarith [hv.1]
      have hd : HasDerivAt (fun v : ℝ => v * curvature v - atanhLog v)
          (1 * curvature v + v * (2 * v / (1 - v ^ 2) ^ 2) - curvature v) v :=
        ((hasDerivAt_id v).mul (hasDerivAt_curvature hv0 hv1)).sub
          (hasDerivAt_atanhLog hv0 hv1)
      rw [hd.deriv]
      have h1 : 0 ≤ 2 * v / (1 - v ^ 2) ^ 2 := by
        apply div_nonneg (by linarith [hv.1]) (by positivity)
      nlinarith [h1, mul_nonneg (le_of_lt hv.1) h1]
  have h := hmono ⟨le_refl 0, hu0⟩ ⟨hu0, le_refl u⟩ hu0
  have h0 : (0 : ℝ) * curvature 0 - atanhLog 0 = 0 := by
    rw [atanhLog_zero]; ring
  simp only at h
  rw [h0] at h
  linarith

theorem atanhLog_div_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    atanhLog a / a ≤ atanhLog b / b := by
  have hmono : MonotoneOn (fun v : ℝ => atanhLog v / v) (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro v hv
      have hv0 : 0 < v := lt_of_lt_of_le ha hv.1
      have hv1 : v < 1 := lt_of_le_of_lt hv.2 hb
      have hd : HasDerivAt (fun v : ℝ => atanhLog v / v)
          ((curvature v * v - atanhLog v * 1) / v ^ 2) v :=
        (hasDerivAt_atanhLog (by linarith) hv1).div (hasDerivAt_id v) (ne_of_gt hv0)
      exact hd.continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro v hv
      have hv0 : 0 < v := lt_trans ha hv.1
      have hv1 : v < 1 := lt_trans hv.2 hb
      have hd : HasDerivAt (fun v : ℝ => atanhLog v / v)
          ((curvature v * v - atanhLog v * 1) / v ^ 2) v :=
        (hasDerivAt_atanhLog (by linarith) hv1).div (hasDerivAt_id v) (ne_of_gt hv0)
      exact hd.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro v hv
      have hv0 : 0 < v := lt_trans ha hv.1
      have hv1 : v < 1 := lt_trans hv.2 hb
      have hd : HasDerivAt (fun v : ℝ => atanhLog v / v)
          ((curvature v * v - atanhLog v * 1) / v ^ 2) v :=
        (hasDerivAt_atanhLog (by linarith) hv1).div (hasDerivAt_id v) (ne_of_gt hv0)
      rw [hd.deriv]
      have hle := atanhLog_le_mul_curvature (le_of_lt hv0) hv1
      apply div_nonneg _ (by positivity)
      nlinarith
  exact hmono ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab

/-! ## The gain integral (eq:gainintegral), integral-free -/

theorem gain_integral {p t : ℝ} (hp0 : 0 < p) (hp1 : p < 1 / 2) (ht0 : 0 < t) (ht1 : t < 1) :
    2 * p * t * atanhLog ((1 - p) * t) ≤ eta ((1 - 2 * p) * t) - eta t := by
  set m : ℝ := (1 - p) * t with hm
  have hm0 : 0 < m := by rw [hm]; nlinarith
  have hm1 : m < 1 := by rw [hm]; nlinarith
  have hpt : 0 < p * t := by positivity
  have hmono : MonotoneOn (fun x : ℝ => eta (m - x) - eta (m + x) - 2 * x * atanhLog m)
      (Set.Icc 0 (p * t)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · apply ContinuousOn.sub
      apply ContinuousOn.sub
      · exact (continuous_eta.comp (continuous_const.sub continuous_id)).continuousOn
      · exact (continuous_eta.comp (continuous_const.add continuous_id)).continuousOn
      · exact ((continuous_const.mul continuous_id).mul continuous_const).continuousOn
    · rw [interior_Icc]
      intro x hx
      have h1 : m + x < 1 := by rw [hm]; nlinarith [hx.2]
      have h2 : -1 < m - x := by nlinarith [hx.2]
      have ha : HasDerivAt (fun x : ℝ => eta (m - x)) (-atanhLog (m - x) * (0 - 1)) x :=
        (hasDerivAt_eta h2 (by linarith [hx.1, hm1])).comp x
          ((hasDerivAt_const x m).sub (hasDerivAt_id x))
      have hb : HasDerivAt (fun x : ℝ => eta (m + x)) (-atanhLog (m + x)) x := by
        simpa using (hasDerivAt_eta (by linarith [hx.1, hm0]) h1).comp x
          ((hasDerivAt_id x).const_add m)
      have hc : HasDerivAt (fun x : ℝ => 2 * x * atanhLog m) (2 * atanhLog m) x := by
        simpa using ((hasDerivAt_id x).const_mul 2).mul_const (atanhLog m)
      exact ((ha.sub hb).sub hc).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have h1 : m + x < 1 := by rw [hm]; nlinarith [hx.2]
      have h2 : -1 < m - x := by nlinarith [hx.2]
      have ha : HasDerivAt (fun x : ℝ => eta (m - x)) (-atanhLog (m - x) * (0 - 1)) x :=
        (hasDerivAt_eta h2 (by linarith [hx.1, hm1])).comp x
          ((hasDerivAt_const x m).sub (hasDerivAt_id x))
      have hb : HasDerivAt (fun x : ℝ => eta (m + x)) (-atanhLog (m + x)) x := by
        simpa using (hasDerivAt_eta (by linarith [hx.1, hm0]) h1).comp x
          ((hasDerivAt_id x).const_add m)
      have hc : HasDerivAt (fun x : ℝ => 2 * x * atanhLog m) (2 * atanhLog m) x := by
        simpa using ((hasDerivAt_id x).const_mul 2).mul_const (atanhLog m)
      rw [((ha.sub hb).sub hc).deriv]
      -- derivative = A(m-x) + A(m+x) - 2A(m) = 2(Lpair m x - Lpair m 0) ≥ 0
      have hL := Lpair_le (nu := m) (le_of_lt hm0) (le_refl 0) (le_of_lt hx.1) h1
      have hL0 : Lpair m 0 = atanhLog m := by
        unfold Lpair
        rw [add_zero, sub_zero]
        ring
      rw [hL0] at hL
      unfold Lpair at hL
      linarith
  have h := hmono ⟨le_refl 0, le_of_lt hpt⟩ ⟨le_of_lt hpt, le_refl (p * t)⟩ (le_of_lt hpt)
  simp only at h
  have e1 : m - p * t = (1 - 2 * p) * t := by rw [hm]; ring
  have e2 : m + p * t = t := by rw [hm]; ring
  rw [e1, e2] at h
  have e0 : eta (m - 0) - eta (m + 0) - 2 * 0 * atanhLog m = 0 := by
    rw [sub_zero, add_zero]; ring
  rw [e0] at h
  linarith

/-! ## Bounds for the entropy remainder `𝓑` (eq:Bbounds), as log inequalities -/

/-- `-ln(1-s) ≥ s`. -/
theorem neg_log_one_sub_ge {s : ℝ} (_hs0 : 0 ≤ s) (hs1 : s < 1) :
    s ≤ -Real.log (1 - s) := by
  have h := Real.log_le_sub_one_of_pos (x := 1 - s) (by linarith)
  linarith

/-- `-ln(1-s) ≤ (s - s²/2)/(1-s)`, i.e. `𝓑(s) ≤ 1 - s/2`. -/
theorem neg_log_one_sub_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    -Real.log (1 - s) ≤ (s - s ^ 2 / 2) / (1 - s) := by
  have hmono : MonotoneOn
      (fun v : ℝ => (v - v ^ 2 / 2) / (1 - v) + Real.log (1 - v)) (Set.Icc 0 s) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro v hv
      have hv1 : v < 1 := lt_of_le_of_lt hv.2 hs1
      have hne : (1 - v : ℝ) ≠ 0 := by linarith
      have hd1 : HasDerivAt (fun v : ℝ => (v - v ^ 2 / 2) / (1 - v))
          (((1 - (2:ℕ) * v ^ (2-1) / 2) * (1 - v) - (v - v ^ 2 / 2) * (0 - 1)) / (1 - v) ^ 2) v :=
        ((hasDerivAt_id v).sub ((hasDerivAt_pow 2 v).div_const 2)).div
          ((hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v)) hne
      have hd2 : HasDerivAt (fun v : ℝ => Real.log (1 - v)) ((1 - v)⁻¹ * (0 - 1)) v :=
        (Real.hasDerivAt_log hne).comp v ((hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v))
      exact (hd1.add hd2).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro v hv
      have hv1 : v < 1 := lt_trans hv.2 hs1
      have hne : (1 - v : ℝ) ≠ 0 := by linarith
      have hd1 : HasDerivAt (fun v : ℝ => (v - v ^ 2 / 2) / (1 - v))
          (((1 - (2:ℕ) * v ^ (2-1) / 2) * (1 - v) - (v - v ^ 2 / 2) * (0 - 1)) / (1 - v) ^ 2) v :=
        ((hasDerivAt_id v).sub ((hasDerivAt_pow 2 v).div_const 2)).div
          ((hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v)) hne
      have hd2 : HasDerivAt (fun v : ℝ => Real.log (1 - v)) ((1 - v)⁻¹ * (0 - 1)) v :=
        (Real.hasDerivAt_log hne).comp v ((hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v))
      exact (hd1.add hd2).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro v hv
      have hv1 : v < 1 := lt_trans hv.2 hs1
      have hne : (1 - v : ℝ) ≠ 0 := by linarith
      have hd1 : HasDerivAt (fun v : ℝ => (v - v ^ 2 / 2) / (1 - v))
          (((1 - (2:ℕ) * v ^ (2-1) / 2) * (1 - v) - (v - v ^ 2 / 2) * (0 - 1)) / (1 - v) ^ 2) v :=
        ((hasDerivAt_id v).sub ((hasDerivAt_pow 2 v).div_const 2)).div
          ((hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v)) hne
      have hd2 : HasDerivAt (fun v : ℝ => Real.log (1 - v)) ((1 - v)⁻¹ * (0 - 1)) v :=
        (Real.hasDerivAt_log hne).comp v ((hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v))
      rw [(hd1.add hd2).deriv]
      have hv0 : 0 ≤ v := le_of_lt (lt_of_le_of_lt (le_refl 0) hv.1)
      have key : ((1 - (2:ℕ) * v ^ (2-1) / 2) * (1 - v) - (v - v ^ 2 / 2) * (0 - 1)) / (1 - v) ^ 2
          + (1 - v)⁻¹ * (0 - 1) = v ^ 2 / 2 / (1 - v) ^ 2 := by
        push_cast
        norm_num
        field_simp
        ring
      rw [key]
      positivity
  have h := hmono ⟨le_refl 0, hs0⟩ ⟨hs0, le_refl s⟩ hs0
  simp only at h
  norm_num [Real.log_one] at h
  linarith

/-- `-ln(1-s) ≥ (s - s²/2 - s³/4)/(1-s)` for `0 ≤ s ≤ 1/2`, i.e. `𝓑(s) ≥ 1 - s/2 - s²/4`. -/
theorem neg_log_one_sub_ge' {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    (s - s ^ 2 / 2 - s ^ 3 / 4) / (1 - s) ≤ -Real.log (1 - s) := by
  have hmono : MonotoneOn
      (fun v : ℝ => -Real.log (1 - v) - (v - v ^ 2 / 2 - v ^ 3 / 4) / (1 - v))
      (Set.Icc 0 s) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro v hv
      have hv1 : v < 1 := by linarith [hv.2]
      have hne : (1 - v : ℝ) ≠ 0 := by linarith
      have hd2 : HasDerivAt (fun v : ℝ => Real.log (1 - v)) ((1 - v)⁻¹ * (0 - 1)) v :=
        (Real.hasDerivAt_log hne).comp v ((hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v))
      have hd1 : HasDerivAt (fun v : ℝ => (v - v ^ 2 / 2 - v ^ 3 / 4) / (1 - v))
          ((((1 - (2:ℕ) * v ^ (2-1) / 2) - (3:ℕ) * v ^ (3-1) / 4) * (1 - v)
            - (v - v ^ 2 / 2 - v ^ 3 / 4) * (0 - 1)) / (1 - v) ^ 2) v :=
        (((hasDerivAt_id v).sub ((hasDerivAt_pow 2 v).div_const 2)).sub
          ((hasDerivAt_pow 3 v).div_const 4)).div
          ((hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v)) hne
      exact (hd2.neg.sub hd1).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro v hv
      have hv1 : v < 1 := by linarith [hv.2]
      have hne : (1 - v : ℝ) ≠ 0 := by linarith
      have hd2 : HasDerivAt (fun v : ℝ => Real.log (1 - v)) ((1 - v)⁻¹ * (0 - 1)) v :=
        (Real.hasDerivAt_log hne).comp v ((hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v))
      have hd1 : HasDerivAt (fun v : ℝ => (v - v ^ 2 / 2 - v ^ 3 / 4) / (1 - v))
          ((((1 - (2:ℕ) * v ^ (2-1) / 2) - (3:ℕ) * v ^ (3-1) / 4) * (1 - v)
            - (v - v ^ 2 / 2 - v ^ 3 / 4) * (0 - 1)) / (1 - v) ^ 2) v :=
        (((hasDerivAt_id v).sub ((hasDerivAt_pow 2 v).div_const 2)).sub
          ((hasDerivAt_pow 3 v).div_const 4)).div
          ((hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v)) hne
      exact (hd2.neg.sub hd1).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro v hv
      have hv0 : 0 < v := hv.1
      have hv1 : v < 1 := by linarith [hv.2]
      have hvh : v < 1 / 2 := by linarith [hv.2]
      have hne : (1 - v : ℝ) ≠ 0 := by linarith
      have hd2 : HasDerivAt (fun v : ℝ => Real.log (1 - v)) ((1 - v)⁻¹ * (0 - 1)) v :=
        (Real.hasDerivAt_log hne).comp v ((hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v))
      have hd1 : HasDerivAt (fun v : ℝ => (v - v ^ 2 / 2 - v ^ 3 / 4) / (1 - v))
          ((((1 - (2:ℕ) * v ^ (2-1) / 2) - (3:ℕ) * v ^ (3-1) / 4) * (1 - v)
            - (v - v ^ 2 / 2 - v ^ 3 / 4) * (0 - 1)) / (1 - v) ^ 2) v :=
        (((hasDerivAt_id v).sub ((hasDerivAt_pow 2 v).div_const 2)).sub
          ((hasDerivAt_pow 3 v).div_const 4)).div
          ((hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v)) hne
      rw [(hd2.neg.sub hd1).deriv]
      have key : -((1 - v)⁻¹ * (0 - 1))
          - (((1 - (2:ℕ) * v ^ (2-1) / 2) - (3:ℕ) * v ^ (3-1) / 4) * (1 - v)
            - (v - v ^ 2 / 2 - v ^ 3 / 4) * (0 - 1)) / (1 - v) ^ 2
          = v ^ 2 * (1 - 2 * v) / (4 * (1 - v) ^ 2) := by
        push_cast
        norm_num
        field_simp
        ring
      rw [key]
      apply div_nonneg _ (by positivity)
      nlinarith
  have h := hmono ⟨le_refl 0, hs0⟩ ⟨hs0, le_refl s⟩ hs0
  simp only at h
  norm_num [Real.log_one] at h
  linarith

/-- `h(p) ≤ p (ln(1/p) + 1)`. -/
theorem binaryEntropy_le_mul {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    binaryEntropy p ≤ p * (Real.log (1 / p) + 1) := by
  unfold binaryEntropy
  have hne : (1 - p : ℝ) ≠ 0 := by linarith
  rw [Real.log_div one_ne_zero (ne_of_gt hp0), Real.log_one]
  have h2 := Real.log_le_sub_one_of_pos (x := 1 / (1 - p))
    (by have hgt : (0:ℝ) < 1 - p := by linarith
        positivity)
  rw [Real.log_div one_ne_zero hne, Real.log_one] at h2
  have h3 : -(1 - p) * Real.log (1 - p) ≤ p := by
    have hmul := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 1 - p)
    have he : (1 - p) * (1 / (1 - p) - 1) = p := by
      field_simp
    nlinarith [hmul, he]
  nlinarith [h3]

end CK
