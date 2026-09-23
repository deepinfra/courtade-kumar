import CK.Definitions

/-!
# Real-algebra formalization draft -- NOT COMPILED

These are explicit mathematical theorem statements and proof scripts for a
subset of the solver-checked obligations. They have not been typechecked here.
There are no custom axioms or unproved declaration bodies. Analytic facts enter
only through ordinary explicit theorem parameters, where needed.
-/
noncomputable section
namespace CK
namespace Algebra

def q (K M l d : ℝ) : ℝ := K + M * d ^ 2 - 2 * l * d

theorem variance_restriction (a b : ℝ) :
    (varianceProfile a + varianceProfile b) / 2 =
      varianceProfile ((a + b) / 2) - (b - a) ^ 2 := by
  unfold varianceProfile
  ring

theorem variance_range (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ varianceProfile a ∧ varianceProfile a ≤ 1 := by
  constructor
  · unfold varianceProfile
    have hsub : 0 ≤ 1 - a := sub_nonneg.mpr ha1
    positivity
  · unfold varianceProfile
    nlinarith [sq_nonneg (2 * a - 1)]

theorem mixture_left (a b p : ℝ) :
    (((1 - p) * a / 2 + p * b / 2) / (1 / 2 : ℝ)) =
      (1 - p) * a + p * b := by ring

theorem mixture_right (a b p : ℝ) :
    ((p * a / 2 + (1 - p) * b / 2) / (1 / 2 : ℝ)) =
      p * a + (1 - p) * b := by ring

theorem small_gap_pair (a b : ℝ) (hab : a + b ≤ 1) :
    a ≤ 1 / 2 ∨ b ≤ 1 / 2 := by
  by_cases ha : a ≤ 1 / 2
  · exact Or.inl ha
  · right
    linarith

/-- Algebraic induction step only. The child/scalar bounds are hypotheses. -/
theorem induction_step (V h d e J H : ℝ)
    (hV : V ≤ 1) (hh : 0 ≤ h) (hd : 0 ≤ d) (he : d ≤ e)
    (hc : (V - d ^ 2) * h ≤ J)
    (hs : J + 2 * d * h * e ≤ (1 + d ^ 2) * H) : V * h ≤ H := by
  have hed : 0 ≤ e - d := sub_nonneg.mpr he
  have hvv : 0 ≤ 1 - V := sub_nonneg.mpr hV
  have he' : 0 ≤ 2 * d * h * (e - d) := by positivity
  have hv' : 0 ≤ d ^ 2 * h * (1 - V) := by positivity
  have hprod : 0 ≤ (1 + d ^ 2) * (H - V * h) := by
    nlinarith [he', hv']
  have hpos : 0 < 1 + d ^ 2 := by positivity
  have : 0 ≤ H - V * h := (nonneg_of_mul_nonneg_right hprod hpos)
  linarith

theorem deficit_identity (V h d e H H0 H1 v0 v1 : ℝ)
    (hv : (v0 + v1) / 2 = V - d ^ 2) :
    (1 + d ^ 2) * (H - V * h) =
      ((1 + d ^ 2) * H - (H0 + H1) / 2 - 2 * d * h * e) +
      ((H0 - v0 * h) + (H1 - v1 * h)) / 2 +
      2 * d * h * (e - d) + d ^ 2 * (1 - V) * h := by
  nlinarith [congrArg (fun x : ℝ => h * x) hv]

theorem bias_payment (m hs hp L2 H I : ℝ)
    (hp_le : hp ≤ 1 / 2)
    (profile : (1 - m ^ 2) * hp ≤ H)
    (entropy : hs ≤ L2 - m ^ 2 / 2)
    (information : I = hs - H) : I ≤ L2 - hp := by
  have hh : 0 ≤ (1 / 2 : ℝ) - hp := sub_nonneg.mpr hp_le
  have hm : 0 ≤ m ^ 2 * (1 / 2 - hp) := by positivity
  nlinarith

theorem complete_square (K M l d : ℝ) (hM : M ≠ 0) :
    q K M l d = M * (d - l / M) ^ 2 + (K * M - l ^ 2) / M := by
  unfold q
  field_simp [hM] ; ring

/-- Conditional product-transfer theorem. Every positive division is cleared
at the target where it actually occurs; product centering is a parameter. -/
theorem product_transfer_direct (K M K0 M0 l d gamma cap : ℝ)
    (hM : 0 < M) (hcap : M ≤ cap)
    (hprod : K0 * M0 ≤ K * M)
    (hmargin : gamma ≤ K0 * M0 - l ^ 2) (hg : 0 ≤ gamma) :
    gamma / cap ≤ q K M l d := by
  have hc : 0 < cap := lt_of_lt_of_le hM hcap
  have hq : gamma / M ≤ q K M l d := by
    apply (div_le_iff₀ hM).2
    unfold q
    nlinarith [sq_nonneg (M * d - l)]
  exact le_trans (div_le_div_of_nonneg_left hg hM hcap) hq

theorem gain_factorization (w K0 M0 d : ℝ) (hw : w ≠ 0) :
    w * K0 + M0 * d ^ 2 / w - (K0 + M0 * d ^ 2) =
      (w - 1) * (K0 - M0 * d ^ 2 / w) := by
  field_simp [hw] ; ring

theorem centering_remainder (J M Lt Lrt Cint : ℝ)
    (h : J * Lt - M * Lrt = Cint / 4) :
    J * (M * Lt - (2 * M - J) * Lrt) =
      M * Cint / 4 + (M - J) ^ 2 * Lrt := by
  nlinarith [congrArg (fun x : ℝ => M * x) h]

theorem centering_sign (J M K Lrt Cint derivative : ℝ)
    (hJ : 0 < J) (hM : 0 ≤ M) (hL : 0 ≤ Lrt) (hC : 0 ≤ Cint)
    (h : J * derivative = M * Cint / 4 + K ^ 2 * Lrt) :
    0 ≤ derivative := by
  have hright : 0 ≤ M * Cint / 4 + K ^ 2 * Lrt := by positivity
  exact nonneg_of_mul_nonneg_right (h ▸ hright) hJ

theorem curvature_integrand (a b v g2 gplus : ℝ)
    (ha : a ≤ v) (hb : v ≤ b) (hg2 : 0 ≤ g2) (hgp : 0 ≤ gplus) :
    0 ≤ (v - a) * (b - v) * g2 + 2 * gplus := by
  have hav : 0 ≤ v - a := sub_nonneg.mpr ha
  have hvb : 0 ≤ b - v := sub_nonneg.mpr hb
  positivity

theorem endpoint_polynomial_identity (v : ℝ) :
    ((249 / 100 : ℝ) - 13 * v / 18) * (643 / 100 + 454 * v / 225) -
      (399 / 100 : ℝ) ^ 2 =
      453 / 5000 + 17117 * v / 45000 - 2951 * v ^ 2 / 2025 := by ring

theorem endpoint_polynomial_margin (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 5) :
    (453 / 5000 : ℝ) + 36013 * v / 405000 ≤
      453 / 5000 + 17117 * v / 45000 - 2951 * v ^ 2 / 2025 := by
  have : v ^ 2 ≤ v / 5 := by nlinarith
  nlinarith

theorem antipodal_pointwise (a b : ℝ) (ha : a ^ 2 = a) (hb : b ^ 2 = b) :
    (a - b) ^ 2 / 4 = (a + b) / 4 - a * b / 2 := by nlinarith

theorem section_bound (beta w : ℝ)
    (hlo : 7 / 40 ≤ beta) (hhi : beta ≤ 13 / 40)
    (hw : w ≤ beta ^ 2 + (1 / 2 - beta) / 2) :
    w ≤ 309 / 1600 := by
  have hleft : 0 ≤ beta - 7 / 40 := sub_nonneg.mpr hlo
  have hright : 0 ≤ 13 / 40 - beta := sub_nonneg.mpr hhi
  have hprod : 0 ≤ (beta - 7 / 40) * (13 / 40 - beta) := by positivity
  nlinarith

def majorant (x : ℝ) : ℝ :=
  (4336*x^10 - 117880*x^8 + 1187295*x^6 - 5572600*x^4 +
    15433465*x^2 + 2903076) / 12862500

theorem majorant_factorization (x : ℝ) :
    majorant x - x =
      (x-3)^2*(x-2)^2*(2*x-1)^2 *
      (1084*x^4+11924*x^3+50475*x^2+99674*x+80641) / 12862500 := by
  unfold majorant
  ring

theorem majorant_even (x : ℝ) : majorant (-x) = majorant x := by
  unfold majorant
  ring

theorem majorant_halfline (x : ℝ) (hx : 0 ≤ x) : x ≤ majorant x := by
  have h : 0 ≤ majorant x - x := by
    rw [majorant_factorization]
    positivity
  linarith

theorem majorant_absolute (x : ℝ) : |x| ≤ majorant x := by
  by_cases hx : 0 ≤ x
  · simpa [abs_of_nonneg hx] using majorant_halfline x hx
  · have hn : 0 ≤ -x := by linarith
    have h := majorant_halfline (-x) hn
    rw [majorant_even] at h
    simpa [abs_of_neg (lt_of_not_ge hx)] using h

theorem linear_margin_dominates (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1 / 20) :
    p ^ 2 / 25 ≤ p / 500 := by
  have hp : 0 ≤ (1 / 20 : ℝ) - p := sub_nonneg.mpr h1
  have : 0 ≤ p * (1 / 20 - p) := by positivity
  nlinarith

theorem weighted_coefficient (r : ℝ) (hr : 81 / 100 ≤ r) :
    (4661 / 10000 : ℝ) ≤ r + r ^ 2 - 1 := by nlinarith

/-- Weighted refinement: only the real-arithmetic closing step, not the
Fourier restriction identity or its probabilistic instantiation. -/
theorem weighted_step (lam r W T2 T3 tail d deficit : ℝ)
    (hlam : 0 ≤ lam) (hr : 81 / 100 ≤ r) (hW : W ≤ 1)
    (hT3 : 0 ≤ T3) (ht : 0 ≤ tail)
    (hstep : lam * (W-r*T2-(1-r)*T3) +
      lam * (d^2+r*T2+r^2*T3+tail) ≤ (1+d^2)*deficit) :
    lam * W ≤ deficit := by
  have hc : 0 ≤ r + r^2 - 1 := le_trans (by norm_num) (weighted_coefficient r hr)
  have hw : 0 ≤ 1 - W := sub_nonneg.mpr hW
  have hrem : 0 ≤ lam * (d^2*(1-W)+(r+r^2-1)*T3+tail) := by positivity
  have hd : 0 < 1 + d^2 := by positivity
  have hh : 0 ≤ (1+d^2) * (deficit-lam*W) := by nlinarith [hrem]
  have := nonneg_of_mul_nonneg_right hh hd
  linarith

end Algebra
end CK
