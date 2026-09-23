import CK.Sections
import CK.AvgLemmas
import CK.Relabel

/-!
# Boolean Fourier analysis on the cube (manuscript Sec. 5.4 basics)

Characters `chi S x = ∏_{i ∈ S} sign (x i)`, Fourier coefficients
`fourierCoeff F S = avg (F · chi S)`, Fourier weights, orthonormality, the
expansion formula, Plancherel/Parseval, and the interaction with the sign
function of a Boolean function, negation of the cube, and the last-coordinate
sections.  These are the ingredients used by the complementary branch.
-/
noncomputable section
namespace CK
open scoped BigOperators

variable {n : ℕ}

/-- Walsh character `χ_S(x) = ∏_{i∈S} sign (x i)`. -/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : ℝ := ∏ i ∈ S, sign (x i)

/-- Fourier coefficient `F̂(S) = E_x[F(x) χ_S(x)]`. -/
def fourierCoeff {n : ℕ} (F : Cube n → ℝ) (S : Finset (Fin n)) : ℝ := avg (fun x => F x * chi S x)

/-- Fourier weight at level `k`: `W_k(F) = Σ_{|S|=k} F̂(S)²`. -/
def weight {n : ℕ} (F : Cube n → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = k), fourierCoeff F S ^ 2

/-- The `±1`-valued version of a Boolean function. -/
def signOf {n : ℕ} (f : BooleanFunction n) : Cube n → ℝ := fun x => sign (f x)

/-- Coordinatewise negation `x ↦ −x` of a point of the cube. -/
def negCube {n : ℕ} (x : Cube n) : Cube n := fun i => !(x i)

/-! ### Elementary facts about `sign` and `avg` -/

theorem sign_mul_self (b : Bool) : sign b * sign b = 1 := by
  cases b <;> norm_num [sign]

theorem sign_mul_sign (a b : Bool) : sign a * sign b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> norm_num [sign]

theorem sign_not (b : Bool) : sign (!b) = -1 * sign b := by
  cases b <;> norm_num [sign]

theorem avg_const (c : ℝ) : avg (fun _ : Cube n => c) = c := by
  unfold avg
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  field_simp

theorem avg_neg (u : Cube n → ℝ) : avg (fun x => -u x) = -avg u := by
  unfold avg
  rw [Finset.sum_neg_distrib, neg_div]

theorem sum_div_const {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem avg_finset_sum {ι : Type*} (s : Finset ι) (g : ι → Cube n → ℝ) :
    avg (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, avg (g i) := by
  unfold avg
  rw [Finset.sum_comm, sum_div_const]

/-! ### Characters -/

theorem chi_empty (x : Cube n) : chi ∅ x = 1 := by
  unfold chi
  exact Finset.prod_empty

theorem chi_singleton (i : Fin n) (x : Cube n) : chi {i} x = sign (x i) := by
  unfold chi
  exact Finset.prod_singleton _ _

/-- `χ_S` as a product over all coordinates. -/
theorem chi_eq_prod_univ (S : Finset (Fin n)) (x : Cube n) :
    chi S x = ∏ i : Fin n, (if i ∈ S then sign (x i) else 1) := by
  unfold chi
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp

theorem chi_mul_self (S : Finset (Fin n)) (x : Cube n) : chi S x * chi S x = 1 := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => sign_mul_self (x i)

theorem chi_mul (S T : Finset (Fin n)) (x : Cube n) : chi S x * chi T x = chi (symmDiff S T) x := by
  simp only [chi_eq_prod_univ, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [hS, hT, Finset.mem_symmDiff, sign_mul_self]

/-- `E[χ_S] = [S = ∅]`: a nonempty character averages to zero. -/
theorem avg_chi (S : Finset (Fin n)) : avg (chi S) = if S = ∅ then 1 else 0 := by
  by_cases hS : S = ∅
  · subst hS
    rw [if_pos rfl]
    have h : chi (∅ : Finset (Fin n)) = fun _ => (1 : ℝ) := funext chi_empty
    rw [h, avg_const]
  · rw [if_neg hS]
    unfold avg
    have h : (∑ x : Cube n, chi S x) = ∏ i : Fin n, ∑ b : Bool, (if i ∈ S then sign b else 1) := by
      simp_rw [chi_eq_prod_univ]
      exact (Fintype.prod_sum (fun (i : Fin n) (b : Bool) => if i ∈ S then sign b else 1)).symm
    rw [h]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, sign]), zero_div]

theorem chi_orthonormal (S T : Finset (Fin n)) :
    avg (fun x => chi S x * chi T x) = if S = T then 1 else 0 := by
  simp_rw [chi_mul]
  rw [avg_chi]
  by_cases h : S = T
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro he
    exact h (symmDiff_eq_bot.mp (he.trans Finset.bot_eq_empty.symm))

/-- Σ_S χ_S(x)χ_S(y) = 2^n·[x = y]. -/
theorem sum_chi_mul_chi (x y : Cube n) :
    (∑ S : Finset (Fin n), chi S x * chi S y) = if x = y then (2 : ℝ) ^ n else 0 := by
  have h : (∑ S : Finset (Fin n), chi S x * chi S y)
      = ∏ i : Fin n, (1 + sign (x i) * sign (y i)) := by
    rw [Finset.prod_one_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun S _ => ?_
    unfold chi
    rw [Finset.prod_mul_distrib]
  rw [h]
  by_cases hxy : x = y
  · rw [if_pos hxy]
    calc ∏ i : Fin n, (1 + sign (x i) * sign (y i)) = ∏ _i : Fin n, (2 : ℝ) :=
          Finset.prod_congr rfl fun i _ => by rw [hxy, sign_mul_self]; norm_num
      _ = 2 ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [sign_mul_sign, if_neg hi]; norm_num)

/-! ### Expansion, Plancherel, Parseval -/

theorem fourier_expansion (F : Cube n → ℝ) (x : Cube n) :
    F x = ∑ S : Finset (Fin n), fourierCoeff F S * chi S x := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have key : (∑ S : Finset (Fin n), fourierCoeff F S * chi S x)
      = (∑ y : Cube n, F y * ∑ S : Finset (Fin n), chi S y * chi S x) / 2 ^ n := by
    unfold fourierCoeff avg
    simp only [div_mul_eq_mul_div, Finset.sum_mul]
    rw [← sum_div_const, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  rw [key]
  simp_rw [sum_chi_mul_chi]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [mul_div_assoc, div_self h2.ne', mul_one]

theorem plancherel (F G : Cube n → ℝ) :
    avg (fun x => F x * G x) = ∑ S : Finset (Fin n), fourierCoeff F S * fourierCoeff G S := by
  have h : (fun x => F x * G x)
      = fun x => ∑ S : Finset (Fin n), fourierCoeff G S * (F x * chi S x) := by
    funext x
    rw [fourier_expansion G x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun S _ => by ring
  rw [h, avg_finset_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [avg_const_mul]
  unfold fourierCoeff
  ring

theorem parseval (F : Cube n → ℝ) :
    avg (fun x => F x ^ 2) = ∑ S : Finset (Fin n), fourierCoeff F S ^ 2 := by
  simp_rw [sq]
  exact plancherel F F

/-! ### Weights -/

theorem weight_nonneg (F : Cube n → ℝ) (k : ℕ) : 0 ≤ weight F k := by
  unfold weight
  exact Finset.sum_nonneg fun S _ => sq_nonneg _

theorem sum_weight (F : Cube n → ℝ) :
    ∑ k ∈ Finset.range (n + 1), weight F k = ∑ S : Finset (Fin n), fourierCoeff F S ^ 2 := by
  unfold weight
  exact Finset.sum_fiberwise_of_maps_to (fun S _ => Finset.mem_range.mpr
    (Nat.lt_succ_of_le ((Finset.card_le_univ S).trans_eq (Fintype.card_fin n)))) _

theorem fourierCoeff_empty (F : Cube n → ℝ) : fourierCoeff F ∅ = avg F := by
  unfold fourierCoeff
  congr 1
  funext x
  rw [chi_empty, mul_one]

theorem weight_zero (F : Cube n → ℝ) : weight F 0 = (avg F) ^ 2 := by
  unfold weight
  have h : (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = 0) = {∅} := by
    ext S
    simp [Finset.card_eq_zero]
  rw [h, Finset.sum_singleton, fourierCoeff_empty]

theorem weight_one (F : Cube n → ℝ) : weight F 1 = ∑ i : Fin n, fourierCoeff F {i} ^ 2 := by
  unfold weight
  have h : (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = 1)
      = Finset.univ.image (fun i : Fin n => ({i} : Finset (Fin n))) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.card_eq_one]
    constructor <;> rintro ⟨a, ha⟩ <;> exact ⟨a, ha.symm⟩
  rw [h, Finset.sum_image (g := fun i : Fin n => ({i} : Finset (Fin n)))
    (fun _ _ _ _ hij => Finset.singleton_inj.mp hij)]

/-! ### Linearity -/

theorem fourierCoeff_add (F G : Cube n → ℝ) (S) :
    fourierCoeff (fun x => F x + G x) S = fourierCoeff F S + fourierCoeff G S := by
  unfold fourierCoeff
  simp only [add_mul]
  exact avg_add _ _

theorem fourierCoeff_const_mul (c : ℝ) (F : Cube n → ℝ) (S) :
    fourierCoeff (fun x => c * F x) S = c * fourierCoeff F S := by
  unfold fourierCoeff
  simp only [mul_assoc]
  exact avg_const_mul _ _

theorem fourierCoeff_const (c : ℝ) (S : Finset (Fin n)) :
    fourierCoeff (fun _ => c) S = if S = ∅ then c else 0 := by
  unfold fourierCoeff
  rw [avg_const_mul, avg_chi]
  split_ifs <;> simp

/-! ### The sign function of a Boolean function -/

theorem signOf_sq (f : BooleanFunction n) (x : Cube n) : signOf f x ^ 2 = 1 :=
  sign_square (f x)

theorem signOf_eq (f : BooleanFunction n) (x : Cube n) : signOf f x = 2 * indicator (f x) - 1 := by
  show sign (f x) = 2 * indicator (f x) - 1
  cases f x <;> norm_num [sign, indicator]

theorem avg_signOf (f : BooleanFunction n) : avg (signOf f) = 2 * mean f - 1 := by
  have h : signOf f = fun x => 2 * indicator (f x) - 1 := funext (signOf_eq f)
  unfold mean
  rw [h, avg_sub, avg_const_mul, avg_const]

theorem abs_signOf (f : BooleanFunction n) (x : Cube n) : |signOf f x| = 1 := by
  show |sign (f x)| = 1
  cases f x <;> norm_num [sign]

/-- nonconstant coefficients of the indicator are half those of the sign function -/
theorem fourierCoeff_indicator (f : BooleanFunction n) (S : Finset (Fin n)) (hS : S ≠ ∅) :
    fourierCoeff (fun x => indicator (f x)) S = fourierCoeff (signOf f) S / 2 := by
  have h : (fun x => indicator (f x)) = fun x => (1 / 2 : ℝ) * (signOf f x + 1) := by
    funext x
    rw [signOf_eq]
    ring
  rw [h, fourierCoeff_const_mul, fourierCoeff_add, fourierCoeff_const, if_neg hS]
  ring

/-! ### Negation of the cube -/

theorem negCube_negCube (x : Cube n) : negCube (negCube x) = x := by
  funext i
  simp [negCube]

/-- `x ↦ −x` as a bijection of the cube. -/
def negCubeEquiv {n : ℕ} : Cube n ≃ Cube n where
  toFun := negCube
  invFun := negCube
  left_inv := negCube_negCube
  right_inv := negCube_negCube

/-- χ_S(−x) = (−1)^{|S|} χ_S(x) -/
theorem chi_negCube (S : Finset (Fin n)) (x : Cube n) : chi S (negCube x) = (-1) ^ S.card * chi S x := by
  unfold chi
  simp only [negCube, sign_not]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

theorem avg_comp_negCube (v : Cube n → ℝ) : avg (fun x => v (negCube x)) = avg v := by
  unfold avg
  rw [Fintype.sum_equiv negCubeEquiv (fun x => v (negCube x)) v (fun _ => rfl)]

theorem fourierCoeff_comp_negCube (F : Cube n → ℝ) (S) :
    fourierCoeff (fun x => F (negCube x)) S = (-1) ^ S.card * fourierCoeff F S := by
  unfold fourierCoeff
  rw [← avg_const_mul, ← avg_comp_negCube (fun x => F (negCube x) * chi S x)]
  congr 1
  funext y
  simp only [negCube_negCube, chi_negCube]
  ring

/-! ### Sections along the last coordinate -/

/-- the singleton coefficient at the last coordinate is the difference of section means
(b_i = μ₁ − μ₀). -/
theorem fourierCoeff_singleton_last (f : BooleanFunction (n + 1)) :
    fourierCoeff (signOf f) {Fin.last n} = mean (sectionLast f true) - mean (sectionLast f false) := by
  have e1 : avg (fun w : Cube n => signOf f (Fin.snoc w true) * chi {Fin.last n} (Fin.snoc w true))
      = 2 * mean (sectionLast f true) - 1 := by
    rw [← avg_signOf]
    congr 1
    funext w
    simp [chi_singleton, Fin.snoc_last, sign, signOf, sectionLast]
  have e2 : avg (fun w : Cube n => signOf f (Fin.snoc w false) * chi {Fin.last n} (Fin.snoc w false))
      = -(2 * mean (sectionLast f false) - 1) := by
    rw [← avg_signOf, ← avg_neg]
    congr 1
    funext w
    simp [chi_singleton, Fin.snoc_last, sign, signOf, sectionLast]
  unfold fourierCoeff
  rw [avg_snoc (fun x => signOf f x * chi {Fin.last n} x), e1, e2]
  ring

theorem chi_map_castSucc (S : Finset (Fin n)) (w : Cube n) (s : Bool) :
    chi (S.map Fin.castSuccEmb) (Fin.snoc w s) = chi S w := by
  unfold chi
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl fun i _ => by simp [Fin.snoc_castSucc]

/-- for S not containing the last coordinate, the coefficient is the average of the two
sections' coefficients -/
theorem fourierCoeff_castSucc_image (F : Cube (n + 1) → ℝ) (S : Finset (Fin n)) :
    fourierCoeff F (S.map Fin.castSuccEmb) =
      (fourierCoeff (fun w => F (Fin.snoc w true)) S + fourierCoeff (fun w => F (Fin.snoc w false)) S) / 2 := by
  unfold fourierCoeff
  rw [avg_snoc (fun x => F x * chi (S.map Fin.castSuccEmb) x)]
  simp only [chi_map_castSucc]

end CK
