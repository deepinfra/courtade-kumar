import CK.Fourier
import CK.SignSum

/-!
# The bias-inclusive Fourier cap (manuscript lem:antipodal, lem:balancedcap, prop:cap)

* `weight_one_indicator_le` (Lemma lem:antipodal, consequence): for an indicator `g = 1_f`
  with mean `a`, `W₁(g) ≤ a/2` and `W₁(g) ≤ (1−a)/2`, via the odd part `(g(x) − g(−x))/2`
  and Parseval.
* `balanced_first_level` (Lemma lem:balancedcap): a balanced indicator all of whose singleton
  coefficients are at most `13/40` in absolute value has `W₁ ≤ 31/160`.  Case (A), all
  coefficients at most `7/40`, is the capped Rademacher estimate `capped_sign_sum`; case (B),
  a coefficient above `7/40`, is the sectioning argument along that coordinate
  (`Algebra.section_bound`).
* `bias_inclusive_cap` (Prop prop:cap): `|m| ≤ 13/20` and all `|b_i| ≤ 13/20` imply
  `m² + W₁(F) ≤ 31/40`, through the balancing lift `F♯(x,z) = z·F(zx)`.
-/
noncomputable section
namespace CK
open scoped BigOperators

variable {n : ℕ}

/-! ### Permuting coordinates -/

/-- Fourier coefficients of a relabelled function: singleton coefficients are permuted. -/
theorem fourierCoeff_comp_perm_singleton {n : ℕ} (σ : Equiv.Perm (Fin n)) (F : Cube n → ℝ) (j : Fin n) :
    fourierCoeff (fun x => F (x ∘ σ)) {j} = fourierCoeff F {σ.symm j} := by
  unfold fourierCoeff
  rw [← avg_comp σ (fun y => F y * chi {σ.symm j} y)]
  congr 1
  funext x
  simp only [chi_singleton, Function.comp_apply, Equiv.apply_symm_apply]

theorem weight_one_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (F : Cube n → ℝ) :
    weight (fun x => F (x ∘ σ)) 1 = weight F 1 := by
  rw [weight_one, weight_one]
  simp only [fourierCoeff_comp_perm_singleton]
  exact Equiv.sum_comp σ.symm (fun i => fourierCoeff F {i} ^ 2)

/-! ### Lemma lem:antipodal -/

/-- The level-one part of Parseval: `W₁(F) ≤ E[F²]`. -/
theorem weight_one_le_avg_sq (F : Cube n → ℝ) : weight F 1 ≤ avg (fun x => F x ^ 2) := by
  rw [parseval]
  unfold weight
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _

/-- The odd part `(F(x) − F(−x))/2` has the same singleton coefficients as `F`. -/
theorem fourierCoeff_oddPart_singleton (F : Cube n → ℝ) (i : Fin n) :
    fourierCoeff (fun x => (F x - F (negCube x)) / 2) {i} = fourierCoeff F {i} := by
  have h : (fun x => (F x - F (negCube x)) / 2)
      = fun x => (1 / 2 : ℝ) * (F x + (-1) * F (negCube x)) := by
    funext x; ring
  rw [h, fourierCoeff_const_mul, fourierCoeff_add, fourierCoeff_const_mul,
    fourierCoeff_comp_negCube, Finset.card_singleton]
  ring

theorem indicator_mul_ge (a b : Bool) :
    indicator a + indicator b - 1 ≤ indicator a * indicator b := by
  cases a <;> cases b <;> norm_num [indicator]

/-- Lemma lem:antipodal (consequence): for an indicator g = 1_f with mean a, W₁(g) ≤ a/2 and W₁(g) ≤ (1−a)/2. -/
theorem weight_one_indicator_le {n : ℕ} (f : BooleanFunction n) :
    weight (fun x => indicator (f x)) 1 ≤ mean f / 2 ∧ weight (fun x => indicator (f x)) 1 ≤ (1 - mean f) / 2 := by
  have hodd : weight (fun x => indicator (f x)) 1
      = weight (fun x => (indicator (f x) - indicator (f (negCube x))) / 2) 1 := by
    rw [weight_one, weight_one]
    exact Finset.sum_congr rfl fun i _ => by
      rw [fourierCoeff_oddPart_singleton (fun x => indicator (f x)) i]
  have hle : weight (fun x => (indicator (f x) - indicator (f (negCube x))) / 2) 1
      ≤ avg (fun x => ((indicator (f x) - indicator (f (negCube x))) / 2) ^ 2) :=
    weight_one_le_avg_sq _
  have hsq : avg (fun x => ((indicator (f x) - indicator (f (negCube x))) / 2) ^ 2)
      = (2 * mean f - 2 * avg (fun x => indicator (f x) * indicator (f (negCube x)))) / 4 := by
    have h : (fun x => ((indicator (f x) - indicator (f (negCube x))) / 2) ^ 2)
        = fun x => (1 / 4 : ℝ) * ((indicator (f x) + indicator (f (negCube x)))
            - 2 * (indicator (f x) * indicator (f (negCube x)))) := by
      funext x
      linear_combination (1 / 4 : ℝ) * indicator_square (f x)
        + (1 / 4 : ℝ) * indicator_square (f (negCube x))
    rw [h, avg_const_mul, avg_sub, avg_add, avg_const_mul,
      avg_comp_negCube (fun x => indicator (f x))]
    unfold mean
    ring
  have hc0 : 0 ≤ avg (fun x => indicator (f x) * indicator (f (negCube x))) := by
    have h := avg_le_avg (n := n) (u := fun _ => (0 : ℝ))
      (fun x => mul_nonneg (indicator_nonneg (f x)) (indicator_nonneg (f (negCube x))))
    rwa [avg_const] at h
  have hc1 : 2 * mean f - 1 ≤ avg (fun x => indicator (f x) * indicator (f (negCube x))) := by
    have h := avg_le_avg (fun x => indicator_mul_ge (f x) (f (negCube x)))
    rw [avg_sub, avg_add, avg_const, avg_comp_negCube (fun x => indicator (f x))] at h
    unfold mean
    linarith
  constructor <;> linarith

/-! ### Lemma lem:balancedcap, case (A): all singleton coefficients at most 7/40 -/

/-- `E[g · R_c] = Σ c_i ĝ({i})` for the Rademacher sum with weights `c`. -/
theorem avg_mul_signSum (g : Cube n → ℝ) (c : Fin n → ℝ) :
    avg (fun x => g x * signSum c x) = ∑ i, c i * fourierCoeff g {i} := by
  have h : (fun x => g x * signSum c x) = fun x => ∑ i, c i * (g x * chi {i} x) := by
    funext x
    unfold signSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [chi_singleton]; ring
  rw [h, avg_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [avg_const_mul]
  rfl

/-- pointwise `g·L ≤ (L + |L|)/2` for `0 ≤ g ≤ 1` -/
theorem mul_le_half_add_abs {g L : ℝ} (h0 : 0 ≤ g) (h1 : g ≤ 1) : g * L ≤ (L + |L|) / 2 := by
  rcases le_or_lt 0 L with hL | hL
  · rw [abs_of_nonneg hL]
    nlinarith [mul_le_mul_of_nonneg_right h1 hL]
  · rw [abs_of_neg hL]
    nlinarith [mul_nonneg h0 (neg_nonneg.mpr hL.le)]

/-- Case (A) of lem:balancedcap: a `[0,1]`-valued function all of whose singleton
coefficients are at most `7/40` in absolute value has `W₁ ≤ 31/160`, by `capped_sign_sum`. -/
theorem weight_one_le_of_small_coeffs (g : Cube n → ℝ) (h0 : ∀ x, 0 ≤ g x) (h1 : ∀ x, g x ≤ 1)
    (hsmall : ∀ i, |fourierCoeff g {i}| ≤ 7 / 40) : weight g 1 ≤ 31 / 160 := by
  obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, ∀ i, c i = fourierCoeff g {i} := ⟨_, fun _ => rfl⟩
  have hw : weight g 1 = ∑ i, c i ^ 2 := by
    rw [weight_one]
    simp only [hc]
  rw [hw]
  by_contra hcon
  push_neg at hcon
  -- `E[g R_c] = w`
  have hA1 : avg (fun x => g x * signSum c x) = ∑ i, c i ^ 2 := by
    rw [avg_mul_signSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i]; ring
  -- `w ≤ E|R_c| / 2`
  have hA3 : ∑ i, c i ^ 2 ≤ avg (fun x => |signSum c x|) / 2 := by
    rw [← hA1]
    calc avg (fun x => g x * signSum c x)
        ≤ avg (fun x => (signSum c x + |signSum c x|) / 2) :=
          avg_le_avg fun x => mul_le_half_add_abs (h0 x) (h1 x)
      _ = (avg (fun x => signSum c x) + avg (fun x => |signSum c x|)) / 2 := by
          have h : (fun x : Cube n => (signSum c x + |signSum c x|) / 2)
              = fun x => (1 / 2 : ℝ) * (signSum c x + |signSum c x|) := by
            funext x; ring
          rw [h, avg_const_mul, avg_add]; ring
      _ = avg (fun x => |signSum c x|) / 2 := by rw [avg_signSum]; ring
  -- normalize the weights
  have hwpos : 0 < ∑ i, c i ^ 2 := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (∑ i, c i ^ 2) := ⟨_, rfl⟩
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hwpos
  have hs2 : s ^ 2 = ∑ i, c i ^ 2 := by rw [hs]; exact Real.sq_sqrt hwpos.le
  have hs_ge : 7 / 16 ≤ s := by
    by_contra h
    push_neg at h
    nlinarith [mul_pos hspos (sub_pos.mpr h)]
  obtain ⟨a, ha⟩ : ∃ a : Fin n → ℝ, ∀ i, a i = c i / s := ⟨_, fun _ => rfl⟩
  have hnorm : ∑ i, a i ^ 2 = 1 := by
    simp only [ha, div_pow]
    rw [← Finset.sum_div, ← hs2, div_self (pow_pos hspos 2).ne']
  have hcap : ∀ i, |a i| ≤ 2 / 5 := by
    intro i
    rw [ha, abs_div, abs_of_pos hspos, div_le_iff₀ hspos]
    have h := hsmall i
    rw [← hc i] at h
    linarith
  have hsc : ∀ x, signSum c x = s * signSum a x := by
    intro x
    unfold signSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha, ← mul_assoc, mul_div_cancel₀ _ hspos.ne']
  have habs : avg (fun x => |signSum c x|) = s * avg (fun x => |signSum a x|) := by
    rw [← avg_const_mul]
    congr 1
    funext x
    rw [hsc x, abs_mul, abs_of_pos hspos]
  have hcs := capped_sign_sum a hnorm hcap
  have hfin : ∑ i, c i ^ 2 ≤ 7 / 16 * s := by
    rw [habs] at hA3
    nlinarith [mul_le_mul_of_nonneg_left hcs hspos.le]
  have hs_le : s ≤ 7 / 16 := by
    by_contra h
    push_neg at h
    nlinarith [mul_lt_mul_of_pos_left h hspos]
  nlinarith [mul_le_mul hs_le hs_le hspos.le (by norm_num : (0 : ℝ) ≤ 7 / 16)]

/-! ### Lemma lem:balancedcap, case (B): a large coefficient at the last coordinate -/

theorem map_castSuccEmb_singleton (j : Fin n) :
    ({j} : Finset (Fin n)).map Fin.castSuccEmb = {Fin.castSucc j} := by
  rw [Finset.map_singleton, Fin.castSuccEmb_apply]

/-- A singleton coefficient at a non-last coordinate is the average of the two section
coefficients. -/
theorem fourierCoeff_castSucc_singleton (F : Cube (n + 1) → ℝ) (j : Fin n) :
    fourierCoeff F {Fin.castSucc j} =
      (fourierCoeff (fun w => F (Fin.snoc w true)) {j}
        + fourierCoeff (fun w => F (Fin.snoc w false)) {j}) / 2 := by
  rw [← map_castSuccEmb_singleton, fourierCoeff_castSucc_image]

/-- `W₁(F) ≤ F̂({last})² + (W₁(F_true) + W₁(F_false))/2`. -/
theorem weight_one_snoc_le (F : Cube (n + 1) → ℝ) :
    weight F 1 ≤ fourierCoeff F {Fin.last n} ^ 2 +
      (weight (fun w => F (Fin.snoc w true)) 1 + weight (fun w => F (Fin.snoc w false)) 1) / 2 := by
  rw [weight_one, weight_one, weight_one, Fin.sum_univ_castSucc]
  have key : ∑ j : Fin n, fourierCoeff F {Fin.castSucc j} ^ 2 ≤
      (∑ j : Fin n, fourierCoeff (fun w => F (Fin.snoc w true)) {j} ^ 2
        + ∑ j : Fin n, fourierCoeff (fun w => F (Fin.snoc w false)) {j} ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [fourierCoeff_castSucc_singleton]
    nlinarith [sq_nonneg (fourierCoeff (fun w => F (Fin.snoc w true)) {j}
      - fourierCoeff (fun w => F (Fin.snoc w false)) {j})]
  linarith

/-- Case (B) of lem:balancedcap with the large coefficient in the last position: sectioning
along the last coordinate and `Algebra.section_bound`. -/
theorem weight_one_le_of_large_last {k : ℕ} (f : BooleanFunction (k + 1)) (hbal : mean f = 1 / 2)
    (hhi : |fourierCoeff (fun x => indicator (f x)) {Fin.last k}| ≤ 13 / 40)
    (hlo : 7 / 40 < |fourierCoeff (fun x => indicator (f x)) {Fin.last k}|) :
    weight (fun x => indicator (f x)) 1 ≤ 31 / 160 := by
  have hc : fourierCoeff (fun x => indicator (f x)) {Fin.last k}
      = (mean (sectionLast f true) - mean (sectionLast f false)) / 2 := by
    rw [fourierCoeff_indicator f {Fin.last k} (Finset.singleton_ne_empty _),
      fourierCoeff_singleton_last]
  have hsum : (mean (sectionLast f true) + mean (sectionLast f false)) / 2 = 1 / 2 :=
    (mean_snoc f).symm.trans hbal
  have ht := weight_one_indicator_le (sectionLast f true)
  have hf := weight_one_indicator_le (sectionLast f false)
  have hsplit : weight (fun x => indicator (f x)) 1 ≤
      fourierCoeff (fun x => indicator (f x)) {Fin.last k} ^ 2 +
        (weight (fun w => indicator (sectionLast f true w)) 1
          + weight (fun w => indicator (sectionLast f false w)) 1) / 2 :=
    weight_one_snoc_le (fun x => indicator (f x))
  set c := fourierCoeff (fun x => indicator (f x)) {Fin.last k}
  set w := weight (fun x => indicator (f x)) 1
  have hW : w ≤ |c| ^ 2 + (1 / 2 - |c|) / 2 := by
    rw [sq_abs]
    rcases abs_cases c with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      linarith [ht.1, ht.2, hf.1, hf.2, hsplit, hc, hsum]
  have h := Algebra.section_bound |c| w hlo.le hhi hW
  linarith

/-- Lemma lem:balancedcap: a balanced indicator with all |E(g X_i)| ≤ 13/40 has W₁(g) ≤ 31/160. -/
theorem balanced_first_level {n : ℕ} (f : BooleanFunction n) (hbal : mean f = 1 / 2)
    (hcoef : ∀ i, |fourierCoeff (fun x => indicator (f x)) {i}| ≤ 13 / 40) :
    weight (fun x => indicator (f x)) 1 ≤ 31 / 160 := by
  by_cases hA : ∀ i, |fourierCoeff (fun x => indicator (f x)) {i}| ≤ 7 / 40
  · exact weight_one_le_of_small_coeffs _ (fun x => indicator_nonneg _)
      (fun x => indicator_le_one _) hA
  · push_neg at hA
    obtain ⟨i, hi⟩ := hA
    cases n with
    | zero => exact i.elim0
    | succ k =>
      obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (k + 1)), σ = Equiv.swap i (Fin.last k) := ⟨_, rfl⟩
      have hσsymm : σ.symm = σ := by rw [hσ, Equiv.symm_swap]
      have hσlast : σ (Fin.last k) = i := by rw [hσ, Equiv.swap_apply_right]
      have hperm : ∀ j, fourierCoeff (fun x => indicator (relabel σ f x)) {j}
          = fourierCoeff (fun x => indicator (f x)) {σ j} := by
        intro j
        have h := fourierCoeff_comp_perm_singleton σ (fun x => indicator (f x)) j
        rw [hσsymm] at h
        exact h
      have hbal' : mean (relabel σ f) = 1 / 2 := by rw [mean_relabel, hbal]
      have hcoef' : |fourierCoeff (fun x => indicator (relabel σ f x)) {Fin.last k}| ≤ 13 / 40 := by
        rw [hperm]; exact hcoef _
      have hlarge' : 7 / 40 < |fourierCoeff (fun x => indicator (relabel σ f x)) {Fin.last k}| := by
        rw [hperm, hσlast]; exact hi
      have hres := weight_one_le_of_large_last (relabel σ f) hbal' hcoef' hlarge'
      have hw : weight (fun x => indicator (relabel σ f x)) 1 = weight (fun x => indicator (f x)) 1 :=
        weight_one_comp_perm σ (fun x => indicator (f x))
      rw [hw] at hres
      exact hres

/-! ### Prop prop:cap: the balancing lift -/

/-- The balancing lift F♯(x,z) = z·F(zx), encoded on Cube (n+1) with z the last coordinate. -/
def lift {n : ℕ} (f : BooleanFunction n) : BooleanFunction (n + 1) :=
  fun y => decide (f (fun i => decide (y (Fin.castSucc i) = y (Fin.last n))) = y (Fin.last n))

theorem decide_eq_true_fun (w : Cube n) : (fun i => decide (w i = true)) = w := by
  funext i
  cases w i <;> rfl

theorem decide_eq_false_fun (w : Cube n) : (fun i => decide (w i = false)) = negCube w := by
  funext i
  show decide (w i = false) = !(w i)
  cases w i <;> rfl

theorem lift_snoc_true (f : BooleanFunction n) (w : Cube n) : lift f (Fin.snoc w true) = f w := by
  unfold lift
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [decide_eq_true_fun]
  exact Bool.decide_eq_true

theorem lift_snoc_false (f : BooleanFunction n) (w : Cube n) :
    lift f (Fin.snoc w false) = !(f (negCube w)) := by
  unfold lift
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [decide_eq_false_fun]
  exact Bool.decide_eq_false

theorem signOf_lift_true (f : BooleanFunction n) (w : Cube n) :
    signOf (lift f) (Fin.snoc w true) = signOf f w := by
  show sign (lift f (Fin.snoc w true)) = sign (f w)
  rw [lift_snoc_true]

theorem signOf_lift_false (f : BooleanFunction n) (w : Cube n) :
    signOf (lift f) (Fin.snoc w false) = -1 * signOf f (negCube w) := by
  show sign (lift f (Fin.snoc w false)) = -1 * sign (f (negCube w))
  rw [lift_snoc_false, sign_not]

/-- The lift is balanced: `E[F♯] = 0`. -/
theorem avg_signOf_lift (f : BooleanFunction n) : avg (signOf (lift f)) = 0 := by
  rw [avg_snoc]
  have e1 : avg (fun w : Cube n => signOf (lift f) (Fin.snoc w true)) = avg (signOf f) := by
    congr 1
    funext w
    exact signOf_lift_true f w
  have e2 : avg (fun w : Cube n => signOf (lift f) (Fin.snoc w false)) = -avg (signOf f) := by
    rw [← avg_comp_negCube (signOf f), ← avg_neg]
    congr 1
    funext w
    rw [signOf_lift_false]; ring
  rw [e1, e2]; ring

/-- `F̂♯({last}) = m = E[F]`. -/
theorem fourierCoeff_lift_last (f : BooleanFunction n) :
    fourierCoeff (signOf (lift f)) {Fin.last n} = avg (signOf f) := by
  unfold fourierCoeff
  rw [avg_snoc]
  have e1 : avg (fun w : Cube n =>
      signOf (lift f) (Fin.snoc w true) * chi {Fin.last n} (Fin.snoc w true)) = avg (signOf f) := by
    congr 1
    funext w
    rw [signOf_lift_true, chi_singleton, Fin.snoc_last, sign_true, mul_one]
  have e2 : avg (fun w : Cube n =>
      signOf (lift f) (Fin.snoc w false) * chi {Fin.last n} (Fin.snoc w false)) = avg (signOf f) := by
    rw [← avg_comp_negCube (signOf f)]
    congr 1
    funext w
    rw [signOf_lift_false, chi_singleton, Fin.snoc_last, sign_false]; ring
  rw [e1, e2]; ring

/-- `F̂♯({castSucc i}) = b_i = F̂({i})`. -/
theorem fourierCoeff_lift_castSucc (f : BooleanFunction n) (i : Fin n) :
    fourierCoeff (signOf (lift f)) {Fin.castSucc i} = fourierCoeff (signOf f) {i} := by
  rw [fourierCoeff_castSucc_singleton]
  have e1 : (fun w : Cube n => signOf (lift f) (Fin.snoc w true)) = signOf f := by
    funext w; exact signOf_lift_true f w
  have e2 : (fun w : Cube n => signOf (lift f) (Fin.snoc w false))
      = fun w => -1 * signOf f (negCube w) := by
    funext w; exact signOf_lift_false f w
  rw [e1, e2, fourierCoeff_const_mul, fourierCoeff_comp_negCube, Finset.card_singleton]
  ring

/-- `W₁(F♯) = m² + W₁(F)`. -/
theorem weight_one_lift (f : BooleanFunction n) :
    weight (signOf (lift f)) 1 = avg (signOf f) ^ 2 + weight (signOf f) 1 := by
  rw [weight_one, weight_one, Fin.sum_univ_castSucc, fourierCoeff_lift_last]
  simp only [fourierCoeff_lift_castSucc]
  ring

/-- Prop prop:cap: |m| ≤ 13/20 and all |b_i| ≤ 13/20 imply m² + W₁(F) ≤ 31/40. -/
theorem bias_inclusive_cap {n : ℕ} (f : BooleanFunction n) (hm : |avg (signOf f)| ≤ 13 / 20)
    (hb : ∀ i, |fourierCoeff (signOf f) {i}| ≤ 13 / 20) :
    (avg (signOf f)) ^ 2 + weight (signOf f) 1 ≤ 31 / 40 := by
  have hbal : mean (lift f) = 1 / 2 := by
    have h := avg_signOf (lift f)
    rw [avg_signOf_lift] at h
    linarith
  have hcoef : ∀ j, |fourierCoeff (fun x => indicator (lift f x)) {j}| ≤ 13 / 40 := by
    intro j
    rw [fourierCoeff_indicator _ _ (Finset.singleton_ne_empty _), abs_div, abs_two,
      div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · rw [fourierCoeff_lift_castSucc]; linarith [hb i]
    · rw [fourierCoeff_lift_last]; linarith [hm]
  have hW := balanced_first_level (lift f) hbal hcoef
  have hrel : weight (fun x => indicator (lift f x)) 1 = weight (signOf (lift f)) 1 / 4 := by
    rw [weight_one, weight_one, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fourierCoeff_indicator _ _ (Finset.singleton_ne_empty _)]
    ring
  rw [hrel, weight_one_lift] at hW
  linarith

end CK
