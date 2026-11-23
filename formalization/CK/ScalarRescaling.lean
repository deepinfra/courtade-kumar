import CK.ScalarIntegral
import CK.ScalarCovariance

/-!
# Rescaling positive tails on the unit interval

The integer rescaling proof uses finite geometric sums and monotone integral
reweighting. All substitutions are polynomial maps of the compact unit interval.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace CourtadeKumar
namespace Scalar
open Finset Set MeasureTheory

/-- Even geometric sum, kept finite throughout the pointwise rescaling proof. -/
def evenGeom (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ range n, x^(2*k)

private theorem evenGeom_add_two (n : ℕ) (x : ℝ) :
    evenGeom (n+2) x = 1+x^(2*(n+1))+x^2*evenGeom n x := by
  unfold evenGeom
  rw [sum_range_succ, sum_range_succ']
  simp only [Nat.mul_zero, pow_zero, mul_sum]
  have heq : (∑ k ∈ range n, x^(2*(k+1))) = ∑ k ∈ range n, x^2*x^(2*k) := by
    apply sum_congr rfl
    intro k _
    rw [show 2*(k+1) = 2+2*k by omega, pow_add]
  rw [heq]
  ring

private theorem geom_endpoint_pair {σ v : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (n : ℕ) :
    σ^n*(1+v^(2*n)) ≤ 1+(σ*v)^(2*n) := by
  have hσ : σ^n ≤ 1 := pow_le_one₀ hσ0 hσ1
  have hv : v^(2*n) ≤ 1 := pow_le_one₀ hv0 hv1
  have hp : σ^n*v^(2*n) ≤ 1 := mul_le_one₀ hσ (pow_nonneg hv0 _) hv
  have h := mul_nonneg (sub_nonneg.mpr hσ) (sub_nonneg.mpr hp)
  have hpow : σ^(2*n) = (σ^n)^2 := by
    rw [show 2*n=n*2 by omega, pow_mul]
  rw [mul_pow, hpow]
  nlinarith

/-- Finite geometric comparison replacing the hyperbolic quotient argument. -/
theorem evenGeom_rescaling {σ v : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (n : ℕ) :
    σ^n*evenGeom (n+1) v ≤ evenGeom (n+1) (σ*v) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [evenGeom]
  | one =>
      simpa [evenGeom, sum_range_succ, pow_succ] using
        geom_endpoint_pair hσ0 hσ1 hv0 hv1 1
  | more n ihn _ =>
      rw [show n+2+1=(n+1)+2 by omega, evenGeom_add_two, evenGeom_add_two]
      have hp := geom_endpoint_pair hσ0 hσ1 hv0 hv1 (n+2)
      have hm := mul_le_mul_of_nonneg_left ihn (sq_nonneg (σ*v))
      have heq : (σ*v)^2*(σ^n*evenGeom (n+1) v) =
          σ^(n+2)*(v^2*evenGeom (n+1) v) := by
        rw [pow_add, mul_pow]
        ring
      rw [heq] at hm
      nlinarith

/-- Ratio of the density after `u = v^j` to the `j`-tail density, up to a constant. -/
def densityRatio (j : ℕ) (v : ℝ) : ℝ := v^(j-1)*(1+v)/(1+v^j)

/-- The polynomial density tilt is increasing on the unit interval. -/
theorem densityRatio_monotone {j : ℕ} (hj : 1 ≤ j) :
    MonotoneOn (densityRatio j) (Icc 0 1) := by
  intro x hx y hy hxy
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  simp only [densityRatio, Nat.add_sub_cancel, Nat.succ_sub_one]
  have hxp := pow_nonneg hx.1 n
  have hyp := pow_nonneg hy.1 n
  have hp : x^n ≤ y^n := pow_le_pow_left₀ hx.1 hxy n
  have hyp1 : y^n ≤ 1 := pow_le_one₀ hy.1 hy.2
  have hdenx : 0 < 1+x^(n+1) := by linarith [pow_nonneg hx.1 (n+1)]
  have hdeny : 0 < 1+y^(n+1) := by linarith [pow_nonneg hy.1 (n+1)]
  apply (div_le_div_iff₀ hdenx hdeny).2
  have h1 := mul_nonneg (sub_nonneg.mpr hxy) hxp
  have h2 := mul_nonneg (sub_nonneg.mpr hp) (by linarith [hy.1] : 0 ≤ 1+y)
  have h3 := mul_nonneg (sub_nonneg.mpr hyp1) h1
  simp only [pow_succ]
  nlinarith

/-- The decreasing factor left after normalizing the tail integral. -/
def tailQuotient (σ v : ℝ) : ℝ := (1-v^2)/(1-σ^2*v^2)

private theorem tailQuotient_den_pos {σ v : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : 0 < 1-σ^2*v^2 := by
  have hs : σ^2 < 1 := by nlinarith
  have hv : v^2 ≤ 1 := by nlinarith
  have hp : σ^2*v^2 ≤ σ^2 := mul_le_of_le_one_right (sq_nonneg σ) hv
  linarith

/-- The quotient is decreasing, so increasing density tilts lower its expectation. -/
theorem tailQuotient_antitone {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    AntitoneOn (tailQuotient σ) (Icc 0 1) := by
  intro x hx y hy hxy
  have hxden := tailQuotient_den_pos hσ0 hσ1 hx.1 hx.2
  have hyden := tailQuotient_den_pos hσ0 hσ1 hy.1 hy.2
  unfold tailQuotient
  apply (div_le_div_iff₀ hyden hxden).2
  have hsq : x^2 ≤ y^2 := pow_le_pow_left₀ hx.1 hxy 2
  have hs : σ^2 ≤ 1 := by nlinarith
  have h := mul_nonneg (sub_nonneg.mpr hsq) (sub_nonneg.mpr hs)
  nlinarith

private theorem evenGeom_factor (n : ℕ) (x : ℝ) :
    (1-x^2)*evenGeom n x = 1-x^(2*n) := by
  induction n with
  | zero => simp [evenGeom]
  | succ n ih =>
      have heq : evenGeom (n+1) x = evenGeom n x+x^(2*n) := by
        exact sum_range_succ _ _
      rw [heq, show 2*(n+1)=2*n+2 by omega, pow_add]
      nlinarith

/-- The finite geometric comparison is precisely the rescaled quotient inequality. -/
theorem tailQuotient_rescaling {σ v : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) {j : ℕ} (hj : 1 ≤ j) :
    σ^(j-1)*tailQuotient (σ^j) (v^j) ≤ tailQuotient σ v := by
  have hσj0 : 0 ≤ σ^j := pow_nonneg hσ0 j
  have hσj1 : σ^j < 1 := pow_lt_one₀ hσ0 hσ1 (by omega : j ≠ 0)
  have hvj0 : 0 ≤ v^j := pow_nonneg hv0 j
  have hvj1 : v^j ≤ 1 := pow_le_one₀ hv0 hv1
  have hden := tailQuotient_den_pos hσ0 hσ1 hv0 hv1
  have hdenj := tailQuotient_den_pos hσj0 hσj1 hvj0 hvj1
  have hg : σ^(j-1)*evenGeom j v ≤ evenGeom j (σ*v) := by
    simpa only [Nat.sub_add_cancel hj] using evenGeom_rescaling hσ0 hσ1.le hv0 hv1 (j-1)
  have hv : 0 ≤ 1-v^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hg (mul_nonneg hv hden.le)
  have hvf := evenGeom_factor j v
  have hσvf := evenGeom_factor j (σ*v)
  have hpv : (v^j)^2 = v^(2*j) := by rw [← pow_mul]; congr 1; omega
  have hpσv : (σ^j)^2*(v^j)^2 = (σ*v)^(2*j) := by
    rw [← mul_pow, ← mul_pow, ← pow_mul]
    congr 1
    omega
  unfold tailQuotient
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hdenj hden).2
  rw [hpσv, hpv, ← hvf, ← hσvf]
  nlinarith [hm]

/-- Positive density representing `b_j` on the unit interval. -/
def tailDensity (j : ℕ) (v : ℝ) : ℝ := v^(2*j)/(1+v)

private theorem tailDensity_continuousOn (j : ℕ) :
    ContinuousOn (tailDensity j) (Icc 0 1) := by
  unfold tailDensity
  apply (continuousOn_id.pow (2*j)).div (continuousOn_const.add continuousOn_id)
  intro v hv
  have h : 0 < 1+v := by linarith [hv.1]
  exact ne_of_gt h

private theorem densityRatio_continuousOn (j : ℕ) :
    ContinuousOn (densityRatio j) (Icc 0 1) := by
  unfold densityRatio
  apply ((continuousOn_id.pow (j-1)).mul (continuousOn_const.add continuousOn_id)).div
    (continuousOn_const.add (continuousOn_id.pow j))
  intro v hv
  have h : 0 < 1+v^j := by linarith [pow_nonneg hv.1 j]
  exact ne_of_gt h

private theorem tailQuotient_continuousOn {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    ContinuousOn (tailQuotient σ) (Icc 0 1) := by
  unfold tailQuotient
  apply (continuousOn_const.sub (continuousOn_id.pow 2)).div
    (continuousOn_const.sub (continuousOn_const.mul (continuousOn_id.pow 2)))
  intro v hv
  exact ne_of_gt (tailQuotient_den_pos hσ0 hσ1 hv.1 hv.2)

private theorem tailDensity_nonneg (j : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ tailDensity j v := div_nonneg (pow_nonneg hv _) (by linarith)

private theorem densityRatio_nonneg (j : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ densityRatio j v :=
  div_nonneg (mul_nonneg (pow_nonneg hv _) (by linarith))
    (by linarith [pow_nonneg hv j])

private theorem tailDensity_integral {j : ℕ} (hj : 1 ≤ j) :
    (∫ v : ℝ in (0 : ℝ)..(1 : ℝ), tailDensity j v) = b (Real.log 2) j :=
  (b_integral hj).symm

/-- The normalized kernel representation of the exact tail. -/
theorem s_eq_weighted_integral {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (j : ℕ) :
    s j σ = σ^(2*j+2) *
      (∫ v : ℝ in (0 : ℝ)..(1 : ℝ), tailDensity j v*tailQuotient σ v) := by
  rw [s_eq_integral hσ0 hσ1]
  congr 1
  apply intervalIntegral.integral_congr
  intro v hv
  norm_num at hv
  have hd := ne_of_gt (tailQuotient_den_pos hσ0 hσ1 hv.1 hv.2)
  have hv1 : 1+v ≠ 0 := by linarith [hv.1]
  change (1-v)*v^(2*j)/(1-σ^2*v^2) = tailDensity j v*tailQuotient σ v
  unfold tailDensity tailQuotient
  field_simp
  <;> ring

private theorem transformed_density {j : ℕ} (hj : 1 ≤ j) {v : ℝ} (hv : 0 ≤ v) :
    tailDensity 1 (v^j)*((j:ℝ)*v^(j-1)) =
      (j:ℝ)*tailDensity j v*densityRatio j v := by
  unfold tailDensity densityRatio
  have hd : 1+v ≠ 0 := by linarith
  have hdj : 1+v^j ≠ 0 := by linarith [pow_nonneg hv j]
  have hp : (v^j)^2 = v^(2*j) := by rw [← pow_mul]; congr 1; omega
  norm_num only [Nat.mul_one]
  rw [hp]
  field_simp
  <;> ring

/-- Exact compact change of variables for the tilted density. -/
theorem tailDensity_substitution {j : ℕ} (hj : 1 ≤ j) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) :
    (j:ℝ)*(∫ v : ℝ in (0 : ℝ)..(1 : ℝ),
      tailDensity j v*densityRatio j v*f (v^j)) =
    (∫ u : ℝ in (0 : ℝ)..(1 : ℝ), tailDensity 1 u*f u) := by
  rw [← intervalIntegral.integral_const_mul]
  calc
    _ = ∫ v : ℝ in (0 : ℝ)..(1 : ℝ),
        (tailDensity 1 (v^j)*f (v^j))*((j:ℝ)*v^(j-1)) := by
      apply intervalIntegral.integral_congr
      intro v hv
      norm_num at hv
      have h := transformed_density hj hv.1
      dsimp
      calc
        _ = ((j:ℝ)*tailDensity j v*densityRatio j v)*f (v^j) := by ring
        _ = (tailDensity 1 (v^j)*((j:ℝ)*v^(j-1)))*f (v^j) := by rw [← h]
        _ = _ := by ring
    _ = _ := integral_pow_substitution hj ((tailDensity_continuousOn 1).mul hf)

/-- Covariance and finite geometric comparison give the normalized kernel order. -/
theorem tail_kernel_order {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {j : ℕ} (hj : 1 ≤ j) :
    σ^(j-1)*b (Real.log 2) j *
      (∫ u : ℝ in (0 : ℝ)..(1 : ℝ), tailDensity 1 u*tailQuotient (σ^j) u) ≤
    b (Real.log 2) 1 *
      (∫ v : ℝ in (0 : ℝ)..(1 : ℝ), tailDensity j v*tailQuotient σ v) := by
  let I := ∫ v : ℝ in (0 : ℝ)..(1 : ℝ), tailDensity j v*tailQuotient σ v
  let I₁ := ∫ u : ℝ in (0 : ℝ)..(1 : ℝ), tailDensity 1 u*tailQuotient (σ^j) u
  let R := ∫ v : ℝ in (0 : ℝ)..(1 : ℝ), tailDensity j v*densityRatio j v
  let T := ∫ v : ℝ in (0 : ℝ)..(1 : ℝ),
    tailDensity j v*densityRatio j v*tailQuotient (σ^j) (v^j)
  let C := ∫ v : ℝ in (0 : ℝ)..(1 : ℝ),
    tailDensity j v*tailQuotient σ v*densityRatio j v
  have hw := tailDensity_continuousOn j
  have hr := densityRatio_continuousOn j
  have hQ := tailQuotient_continuousOn hσ0 hσ1
  have hσj0 : 0 ≤ σ^j := pow_nonneg hσ0 j
  have hσj1 : σ^j < 1 := pow_lt_one₀ hσ0 hσ1 (by omega : j ≠ 0)
  have hQj := tailQuotient_continuousOn hσj0 hσj1
  have hQcomp : ContinuousOn (fun v => tailQuotient (σ^j) (v^j)) (Icc 0 1) := by
    apply hQj.comp (continuousOn_id.pow j)
    intro v hv
    exact ⟨pow_nonneg hv.1 j, pow_le_one₀ hv.1 hv.2⟩
  have hcov : b (Real.log 2) j*C ≤ I*R := by
    have h := weighted_covariance_nonpos hw hQ hr
      (fun v hv => tailDensity_nonneg j hv.1)
      (tailQuotient_antitone hσ0 hσ1) (densityRatio_monotone hj)
    rw [tailDensity_integral hj] at h
    exact h
  have hR : (j:ℝ)*R = b (Real.log 2) 1 := by
    have h := tailDensity_substitution hj (f := fun _ => (1:ℝ)) continuousOn_const
    simpa only [mul_one, tailDensity_integral (by omega : 1 ≤ (1:ℕ))] using h
  have hT : (j:ℝ)*T = I₁ := tailDensity_substitution hj hQj
  have hinter : σ^(j-1)*T ≤ C := by
    dsimp [T, C]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((continuousOn_const.mul ((hw.mul hr).mul hQcomp)).intervalIntegrable_of_Icc (by norm_num))
      (((hw.mul hQ).mul hr).intervalIntegrable_of_Icc (by norm_num))
    intro v hv
    have hvw : 0 ≤ tailDensity j v*densityRatio j v :=
      mul_nonneg (tailDensity_nonneg j hv.1) (densityRatio_nonneg j hv.1)
    calc
      _ = (tailDensity j v*densityRatio j v)*
          (σ^(j-1)*tailQuotient (σ^j) (v^j)) := by ring
      _ ≤ (tailDensity j v*densityRatio j v)*tailQuotient σ v :=
        mul_le_mul_of_nonneg_left (tailQuotient_rescaling hσ0 hσ1 hv.1 hv.2 hj) hvw
      _ = _ := by ring
  change σ^(j-1)*b (Real.log 2) j*I₁ ≤ b (Real.log 2) 1*I
  calc
    _ = b (Real.log 2) j*((j:ℝ)*(σ^(j-1)*T)) := by rw [← hT]; ring
    _ ≤ b (Real.log 2) j*((j:ℝ)*C) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinter (Nat.cast_nonneg j))
        (b_log_two_nonneg j)
    _ = (j:ℝ)*(b (Real.log 2) j*C) := by ring
    _ ≤ (j:ℝ)*(I*R) := mul_le_mul_of_nonneg_left hcov (Nat.cast_nonneg j)
    _ = I*((j:ℝ)*R) := by ring
    _ = _ := by rw [hR]; ring

/-- The manuscript's rescaled-tail inequality, proved for the actual infinite tails. -/
theorem tail_rescaling {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    {j : ℕ} (hj : 1 ≤ j) :
    s 1 (σ^j)/(σ^j*b (Real.log 2) 1) ≤ s j σ/(σ*b (Real.log 2) j) := by
  rcases lt_or_eq_of_le hσ1 with hlt | rfl
  · have hσj : σ^j < 1 := pow_lt_one₀ hσ0.le hlt (by omega : j ≠ 0)
    have hbj := b_log_two_pos hj
    have hb1 := b_log_two_pos (by omega : 1 ≤ (1:ℕ))
    apply (div_le_div_iff₀ (mul_pos (pow_pos hσ0 j) hb1) (mul_pos hσ0 hbj)).2
    have hp : σ^(3*j+2)*σ^(j-1) = σ^(4*j+1) := by
      rw [← pow_add]
      congr 1
      omega
    have hp₁ : (σ^j)^4*σ = σ^(4*j+1) := by
      rw [← pow_mul, ← pow_succ]
      congr 1
      omega
    have hp₂ : σ^(2*j+2)*σ^j = σ^(3*j+2) := by
      rw [← pow_add]
      congr 1
      omega
    let I := ∫ v : ℝ in (0 : ℝ)..(1 : ℝ), tailDensity j v*tailQuotient σ v
    let I₁ := ∫ u : ℝ in (0 : ℝ)..(1 : ℝ), tailDensity 1 u*tailQuotient (σ^j) u
    have hs : s j σ = σ^(2*j+2)*I := s_eq_weighted_integral hσ0.le hlt j
    have hs₁ : s 1 (σ^j) = (σ^j)^4*I₁ :=
      s_eq_weighted_integral (pow_nonneg hσ0.le j) hσj 1
    calc
      s 1 (σ^j)*(σ*b (Real.log 2) j)
          = ((σ^j)^4*σ)*(b (Real.log 2) j*I₁) := by rw [hs₁]; ring
      _ = σ^(4*j+1)*(b (Real.log 2) j*I₁) := by rw [hp₁]
      _ = σ^(3*j+2)*(σ^(j-1)*b (Real.log 2) j*I₁) := by rw [← hp]; ring
      _ ≤ σ^(3*j+2)*(b (Real.log 2) 1*I) :=
        mul_le_mul_of_nonneg_left (tail_kernel_order hσ0.le hlt hj) (pow_nonneg hσ0.le _)
      _ = (σ^(2*j+2)*I)*(σ^j*b (Real.log 2) 1) := by rw [← hp₂]; ring
      _ = s j σ*(σ^j*b (Real.log 2) 1) := by rw [hs]
  · simp only [one_pow, one_mul, ← b_eq_s_one hj,
      ← b_eq_s_one (by omega : 1 ≤ (1:ℕ)),
      div_self (ne_of_gt (b_log_two_pos hj)),
      div_self (ne_of_gt (b_log_two_pos (by omega : 1 ≤ (1:ℕ)))), le_refl]

end Scalar
end CourtadeKumar
