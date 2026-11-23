import CK.ScalarMeans
import Mathlib.Analysis.NormedSpace.FunctionSeries

/-!
# Countable Jensen bounds used by the three-bit argument

Exponential supporting lines suffice for both distributions. All countable
exchanges are justified by nonnegative, explicitly summable product majorants.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace CourtadeKumar
namespace Scalar
open Finset

/-- The exponential supporting line, in the multiplicative form used below. -/
theorem exp_support (x y : ℝ) : Real.exp y*(1+x-y) ≤ Real.exp x := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x-y)) (Real.exp_pos y).le
  calc
    Real.exp y*(1+x-y) = Real.exp y*((x-y)+1) := by ring
    _ ≤ Real.exp y*Real.exp (x-y) := h
    _ = Real.exp x := by rw [← Real.exp_add]; congr 1; ring

theorem summable_weighted_exp {w : ℕ → ℝ} (hw : Summable w) (hw0 : ∀ n, 0 ≤ w n)
    {c : ℝ} (hc : c ≤ 0) : Summable (fun n : ℕ => w n*Real.exp (c*n)) := by
  apply hw.of_nonneg_of_le
  · intro n
    exact mul_nonneg (hw0 n) (Real.exp_pos _).le
  · intro n
    have he : Real.exp (c*n) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg hc (Nat.cast_nonneg n))
    exact (mul_le_mul_of_nonneg_left he (hw0 n)).trans_eq (mul_one _)

/-- Countable exponential Jensen with an upper bound on the weighted mean. -/
theorem weighted_exp_lower {w : ℕ → ℝ} (hw : Summable w)
    (hwm : Summable (fun n : ℕ => (n:ℝ)*w n)) (hw0 : ∀ n, 0 ≤ w n)
    {c h : ℝ} (hc : c ≤ 0)
    (hmean : (∑' n : ℕ, (n:ℝ)*w n) ≤ h*(∑' n : ℕ, w n)) :
    (∑' n : ℕ, w n)*Real.exp (c*h) ≤ ∑' n : ℕ, w n*Real.exp (c*n) := by
  let A : ℕ → ℝ := fun n => Real.exp (c*h)*((1-c*h)*w n+c*((n:ℝ)*w n))
  have hA : Summable A := ((hw.mul_left (1-c*h)).add (hwm.mul_left c)).mul_left _
  have hle : ∀ n : ℕ, A n ≤ w n*Real.exp (c*n) := by
    intro n
    have hp := mul_le_mul_of_nonneg_left (exp_support (c*n) (c*h)) (hw0 n)
    dsimp [A]
    nlinarith [hp]
  have hs := tsum_le_tsum hle hA (summable_weighted_exp hw hw0 hc)
  have hsum : (∑' n : ℕ, A n) = Real.exp (c*h)*
      ((1-c*h)*(∑' n : ℕ,w n)+c*(∑' n : ℕ,(n:ℝ)*w n)) := by
    dsimp [A]
    rw [tsum_mul_left, (hw.mul_left (1-c*h)).tsum_add (hwm.mul_left c),
      tsum_mul_left, tsum_mul_left]
  rw [hsum] at hs
  have hm : 0 ≤ c*((∑' n : ℕ,(n:ℝ)*w n)-h*(∑' n : ℕ,w n)) :=
    mul_nonneg_of_nonpos_of_nonpos hc (sub_nonpos.mpr hmean)
  have hp := mul_nonneg (Real.exp_pos (c*h)).le hm
  nlinarith

/-- The positive exponential series `s_1(exp(c*x))/exp(c*x)`. -/
def tailLaplace (c x : ℝ) : ℝ :=
  ∑' k : ℕ, a (k+2)*Real.exp (c*((2*(k:ℝ)+3)*x))

private theorem summable_a_shift_two : Summable (fun k : ℕ => a (k+2)) :=
  (summable_nat_add_iff 2).mpr summable_a

private theorem exp_tail_le_one {c x : ℝ} (hc : c ≤ 0) (hx : 0 ≤ x) (k : ℕ) :
    Real.exp (c*((2*(k:ℝ)+3)*x)) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg hc (mul_nonneg (by positivity) hx)

theorem summable_tailLaplace {c x : ℝ} (hc : c ≤ 0) (hx : 0 ≤ x) :
    Summable (fun k : ℕ => a (k+2)*Real.exp (c*((2*(k:ℝ)+3)*x))) := by
  apply summable_a_shift_two.of_nonneg_of_le
  · intro k
    exact mul_nonneg (a_nonneg _) (Real.exp_pos _).le
  · intro k
    exact (mul_le_mul_of_nonneg_left (exp_tail_le_one hc hx k) (a_nonneg _)).trans_eq (mul_one _)

/-- Jensen for the entire positive exponential tail series, with no finite-support assumption. -/
theorem weighted_tailLaplace_lower {w : ℕ → ℝ} (hw : Summable w)
    (hwm : Summable (fun n : ℕ => (n:ℝ)*w n)) (hw0 : ∀ n, 0 ≤ w n)
    {c h : ℝ} (hc : c ≤ 0) (hh : 0 ≤ h)
    (hmean : (∑' n : ℕ, (n:ℝ)*w n) ≤ h*(∑' n : ℕ,w n)) :
    (∑' n : ℕ,w n)*tailLaplace c h ≤ ∑' n : ℕ,w n*tailLaplace c n := by
  let F : ℕ × ℕ → ℝ := fun p => a (p.1+2)*w p.2*
    Real.exp (c*((2*(p.1:ℝ)+3)*(p.2:ℝ)))
  have hmajor : Summable (fun p : ℕ × ℕ => a (p.1+2)*w p.2) :=
    summable_a_shift_two.mul_of_nonneg hw (fun k => a_nonneg _) hw0
  have hF : Summable F := by
    apply hmajor.of_nonneg_of_le
    · intro p
      exact mul_nonneg (mul_nonneg (a_nonneg _) (hw0 _)) (Real.exp_pos _).le
    · intro p
      exact (mul_le_mul_of_nonneg_left (exp_tail_le_one hc (Nat.cast_nonneg p.2) p.1)
        (mul_nonneg (a_nonneg _) (hw0 _))).trans_eq (mul_one _)
  have hleft : Summable (fun k : ℕ => (∑' n : ℕ,w n)*
      (a (k+2)*Real.exp (c*((2*(k:ℝ)+3)*h)))) :=
    (summable_tailLaplace hc hh).mul_left _
  have hpoint (k : ℕ) : (∑' n : ℕ,w n)*
      (a (k+2)*Real.exp (c*((2*(k:ℝ)+3)*h))) ≤ ∑' n : ℕ,F (k,n) := by
    have hc' : c*(2*(k:ℝ)+3) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by positivity)
    have hj := mul_le_mul_of_nonneg_left (weighted_exp_lower hw hwm hw0 hc' hmean) (a_nonneg (k+2))
    rw [← tsum_mul_left] at hj
    convert hj using 1
    · ring
    · apply tsum_congr
      intro n
      dsimp [F]
      simp only [mul_assoc]
  have hs := tsum_le_tsum hpoint hleft hF.prod
  have hswap : (∑' k : ℕ, ∑' n : ℕ,F (k,n)) =
      ∑' n : ℕ,w n*tailLaplace c n := by
    rw [← hF.tsum_comm]
    apply tsum_congr
    intro n
    unfold tailLaplace
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    dsimp [F]
    ring
  rw [hswap] at hs
  simpa only [tailLaplace,tsum_mul_left] using hs

/-- Identification of the Laplace form with the exact infinite tail. -/
theorem tailLaplace_eq (c x : ℝ) :
    tailLaplace c x = s 1 (Real.exp (c*x))/Real.exp (c*x) := by
  unfold tailLaplace s
  rw [← tsum_div_const]
  apply tsum_congr
  intro k
  rw [mul_div_assoc, ← Real.exp_nat_mul, ← Real.exp_sub]
  congr 1
  push_cast
  ring

end Scalar
end CourtadeKumar
