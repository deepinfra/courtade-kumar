import CK.ScalarTails

/-!
# Weighted covariance on the compact unit interval

Oppositely monotone continuous functions have nonpositive covariance under any
continuous nonnegative weight. The proof integrates the elementary two-point
inequality twice; no probability-measure normalization is assumed.
-/

noncomputable section
namespace CourtadeKumar
namespace Scalar
open Set MeasureTheory

private theorem integral_four_terms {u v r s : ℝ → ℝ} {A B C : ℝ}
    (hu : IntervalIntegrable u volume 0 1) (hv : IntervalIntegrable v volume 0 1)
    (hr : IntervalIntegrable r volume 0 1) (hs : IntervalIntegrable s volume 0 1) :
    (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), A*u x-B*v x-C*r x+s x) =
      A*(∫ x : ℝ in (0 : ℝ)..(1 : ℝ), u x) -
      B*(∫ x : ℝ in (0 : ℝ)..(1 : ℝ), v x) -
      C*(∫ x : ℝ in (0 : ℝ)..(1 : ℝ), r x) +
      (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), s x) := by
  rw [intervalIntegral.integral_add (((hu.const_mul A).sub (hv.const_mul B)).sub (hr.const_mul C)) hs,
    intervalIntegral.integral_sub ((hu.const_mul A).sub (hv.const_mul B)) (hr.const_mul C),
    intervalIntegral.integral_sub (hu.const_mul A) (hv.const_mul B)]
  simp only [intervalIntegral.integral_const_mul]

/-- Continuous weighted Chebyshev inequality for oppositely monotone factors. -/
theorem weighted_covariance_nonpos {w f g : ℝ → ℝ}
    (hw : ContinuousOn w (Icc 0 1)) (hf : ContinuousOn f (Icc 0 1))
    (hg : ContinuousOn g (Icc 0 1)) (hw0 : ∀ x ∈ Icc 0 1, 0 ≤ w x)
    (hfanti : AntitoneOn f (Icc 0 1)) (hgmono : MonotoneOn g (Icc 0 1)) :
    (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), w x) *
      (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), w x*f x*g x) ≤
    (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), w x*f x) *
      (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), w x*g x) := by
  let W := ∫ x : ℝ in (0 : ℝ)..(1 : ℝ), w x
  let F := ∫ x : ℝ in (0 : ℝ)..(1 : ℝ), w x*f x
  let G := ∫ x : ℝ in (0 : ℝ)..(1 : ℝ), w x*g x
  let M := ∫ x : ℝ in (0 : ℝ)..(1 : ℝ), w x*f x*g x
  have hwI : IntervalIntegrable w volume 0 1 := hw.intervalIntegrable_of_Icc (by norm_num : (0:ℝ)≤1)
  have hwfI : IntervalIntegrable (fun x => w x*f x) volume 0 1 := (hw.mul hf).intervalIntegrable_of_Icc (by norm_num : (0:ℝ)≤1)
  have hwgI : IntervalIntegrable (fun x => w x*g x) volume 0 1 := (hw.mul hg).intervalIntegrable_of_Icc (by norm_num : (0:ℝ)≤1)
  have hwfgI : IntervalIntegrable (fun x => w x*f x*g x) volume 0 1 := ((hw.mul hf).mul hg).intervalIntegrable_of_Icc (by norm_num : (0:ℝ)≤1)
  have hpair (x y : ℝ) (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
      (f x-f y)*(g x-g y) ≤ 0 := by
    rcases le_total x y with hxy | hyx
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hfanti hx hy hxy))
        (sub_nonpos.mpr (hgmono hx hy hxy))
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hfanti hy hx hyx))
        (sub_nonneg.mpr (hgmono hy hx hyx))
  have hinner (x : ℝ) :
      (∫ y : ℝ in (0 : ℝ)..(1 : ℝ), w y*(f x-f y)*(g x-g y)) =
      f x*g x*W-f x*G-g x*F+M := by
    calc
      _ = ∫ y : ℝ in (0 : ℝ)..(1 : ℝ),
          (f x*g x)*w y-f x*(w y*g y)-g x*(w y*f y)+w y*f y*g y := by
        apply intervalIntegral.integral_congr
        intro y _
        ring
      _ = _ := integral_four_terms hwI hwgI hwfI hwfgI
  have hpoint (x : ℝ) (hx : x ∈ Icc 0 1) :
      f x*g x*W-f x*G-g x*F+M ≤ 0 := by
    rw [← hinner]
    have hc : ContinuousOn (fun y => w y*(f x-f y)*(g x-g y)) (Icc 0 1) :=
      (hw.mul (continuousOn_const.sub hf)).mul (continuousOn_const.sub hg)
    calc
      _ ≤ ∫ y : ℝ in (0 : ℝ)..(1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (hc.intervalIntegrable_of_Icc (by norm_num)) intervalIntegrable_const
        intro y hy
        have h := mul_nonpos_of_nonneg_of_nonpos (hw0 y hy) (hpair x y hx hy)
        nlinarith
      _ = 0 := by simp
  have hout : (∫ x : ℝ in (0 : ℝ)..(1 : ℝ),
      w x*(f x*g x*W-f x*G-g x*F+M)) ≤ 0 := by
    have hc : ContinuousOn (fun x => w x*(f x*g x*W-f x*G-g x*F+M)) (Icc 0 1) :=
      hw.mul (((((hf.mul hg).mul continuousOn_const).sub (hf.mul continuousOn_const)).sub
        (hg.mul continuousOn_const)).add continuousOn_const)
    calc
      _ ≤ ∫ x : ℝ in (0 : ℝ)..(1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (hc.intervalIntegrable_of_Icc (by norm_num)) intervalIntegrable_const
        intro x hx
        exact mul_nonpos_of_nonneg_of_nonpos (hw0 x hx) (hpoint x hx)
      _ = 0 := by simp
  have heq : (∫ x : ℝ in (0 : ℝ)..(1 : ℝ),
      w x*(f x*g x*W-f x*G-g x*F+M)) = W*M-G*F-F*G+M*W := by
    calc
      _ = ∫ x : ℝ in (0 : ℝ)..(1 : ℝ),
          W*(w x*f x*g x)-G*(w x*f x)-F*(w x*g x)+M*w x := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = _ := by
        rw [integral_four_terms hwfgI hwfI hwgI (hwI.const_mul M)]
        simp only [intervalIntegral.integral_const_mul]
        rfl
  rw [heq] at hout
  change W*M ≤ F*G
  nlinarith

end Scalar
end CourtadeKumar
