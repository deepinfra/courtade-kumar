import CK.Fourier
import CK.Semantics
import CK.EtaDeriv
import CK.ProductCentering

/-!
# The noise operator `T_ρ` (manuscript Sec. 6.1, Lemma lem:energy)

`noiseOp p F y = Σ_x kernel p y x · F x` is the Bonami–Beckner noise operator
`T_ρ` with `ρ = 1 − 2p`.  It multiplies the Fourier coefficient at `S` by
`ρ^{|S|}` (`noiseOp_chi`, `fourierCoeff_noiseOp`), the posterior of a Boolean
function is `(1 + T_ρ F)/2` with `F = signOf f` (`posterior_eq_noiseOp`), so
the conditional entropy is `E eta(T_ρ F)`.  The cancellation identity
(eq:cancellation) and the energy lower bound (Lemma lem:energy) follow from
Plancherel.
-/
noncomputable section
namespace CK
open scoped BigOperators

variable {n : ℕ}

/-- The noise operator `T_ρ F (y) = Σ_x kernel p y x · F x`, `ρ = 1 − 2p`. -/
def noiseOp {n : ℕ} (p : ℝ) (F : Cube n → ℝ) (y : Cube n) : ℝ := ∑ x, kernel p y x * F x

/-! ### Spectral action -/

/-- one-coordinate factor: `(1−p) sign b + p sign (!b) = (1 − 2p) sign b`. -/
theorem kernel_factor_sign (p : ℝ) (b : Bool) :
    (∑ c : Bool, (if b = c then 1 - p else p) * sign c) = (1 - 2 * p) * sign b := by
  cases b <;> simp [Fintype.sum_bool, sign] <;> ring

/-- `T_ρ χ_S = ρ^{|S|} χ_S`. -/
theorem noiseOp_chi (p : ℝ) (S : Finset (Fin n)) (y : Cube n) :
    noiseOp p (chi S) y = (1 - 2 * p) ^ S.card * chi S y := by
  unfold noiseOp
  have h1 : (∑ x : Cube n, kernel p y x * chi S x)
      = ∏ i : Fin n, ∑ b : Bool, (if y i = b then 1 - p else p) * (if i ∈ S then sign b else 1) := by
    rw [Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
      (if y i = b then 1 - p else p) * (if i ∈ S then sign b else 1))]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold kernel
    rw [chi_eq_prod_univ, Finset.prod_mul_distrib]
  have h2 : ∀ i : Fin n,
      (∑ b : Bool, (if y i = b then 1 - p else p) * (if i ∈ S then sign b else 1))
        = (if i ∈ S then (1 - 2 * p) else 1) * (if i ∈ S then sign (y i) else 1) := by
    intro i
    by_cases hi : i ∈ S
    · simp only [if_pos hi]
      exact kernel_factor_sign p (y i)
    · simp only [if_neg hi, mul_one]
      exact bool_sum_kernel_factor p (y i)
  rw [h1]
  simp_rw [h2]
  rw [Finset.prod_mul_distrib, chi_eq_prod_univ, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const]

theorem noiseOp_add (p : ℝ) (F G : Cube n → ℝ) :
    noiseOp p (fun x => F x + G x) = fun y => noiseOp p F y + noiseOp p G y := by
  funext y
  unfold noiseOp
  simp only [mul_add, Finset.sum_add_distrib]

theorem noiseOp_const_mul (p c : ℝ) (F : Cube n → ℝ) :
    noiseOp p (fun x => c * F x) = fun y => c * noiseOp p F y := by
  funext y
  unfold noiseOp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- `T_ρ F = Σ_S ρ^{|S|} F̂(S) χ_S`. -/
theorem noiseOp_eq_sum (p : ℝ) (F : Cube n → ℝ) (y : Cube n) :
    noiseOp p F y = ∑ S : Finset (Fin n), (1 - 2 * p) ^ S.card * fourierCoeff F S * chi S y := by
  have h : noiseOp p F y = ∑ S : Finset (Fin n), fourierCoeff F S * noiseOp p (chi S) y := by
    unfold noiseOp
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [fourier_expansion F x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  rw [h]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [noiseOp_chi]
  ring

/-- `(T_ρ F)^(S) = ρ^{|S|} F̂(S)`. -/
theorem fourierCoeff_noiseOp (p : ℝ) (F : Cube n → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (noiseOp p F) S = (1 - 2 * p) ^ S.card * fourierCoeff F S := by
  have h : (fun y => noiseOp p F y * chi S y)
      = fun y => ∑ T : Finset (Fin n),
          ((1 - 2 * p) ^ T.card * fourierCoeff F T) * (chi T y * chi S y) := by
    funext y
    rw [noiseOp_eq_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun T _ => by ring
  show avg (fun y => noiseOp p F y * chi S y) = _
  rw [h, avg_finset_sum]
  simp_rw [avg_const_mul, chi_orthonormal]
  simp

/-! ### The posterior and the conditional entropy -/

/-- the posterior is `(1 + T_ρ F)/2` with `F = signOf f`. -/
theorem posterior_eq_noiseOp (f : BooleanFunction n) (p : ℝ) (y : Cube n) :
    posterior f p y = (1 + noiseOp p (signOf f) y) / 2 := by
  unfold posterior noiseOp
  have h : ∀ x, kernel p y x * indicator (f x)
      = (kernel p y x + kernel p y x * signOf f x) / 2 := by
    intro x
    rw [signOf_eq]
    ring
  simp_rw [h]
  rw [← sum_div_const, Finset.sum_add_distrib, kernel_row_sum]

/-- `T_ρ` is a contraction in sup norm (kernel rows are probability vectors). -/
theorem abs_noiseOp_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : Cube n → ℝ)
    (hF : ∀ x, |F x| ≤ 1) (y : Cube n) : |noiseOp p F y| ≤ 1 := by
  unfold noiseOp
  calc |∑ x : Cube n, kernel p y x * F x| ≤ ∑ x : Cube n, |kernel p y x * F x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : Cube n, kernel p y x := by
        apply Finset.sum_le_sum
        intro x _
        rw [abs_mul, abs_of_nonneg (kernel_nonneg p hp0 hp1 y x)]
        exact mul_le_of_le_one_right (kernel_nonneg p hp0 hp1 y x) (hF x)
    _ = 1 := kernel_row_sum p y

theorem binaryEntropy_mean_eq (f : BooleanFunction n) :
    binaryEntropy (mean f) = eta (avg (signOf f)) := by
  unfold eta
  rw [avg_signOf]
  congr 1
  ring

theorem conditionalEntropy_eq_avg_eta (f : BooleanFunction n) (p : ℝ) :
    conditionalEntropy f p = avg (fun y => eta (noiseOp p (signOf f) y)) := by
  unfold conditionalEntropy eta
  congr 1
  funext y
  rw [posterior_eq_noiseOp]

theorem conditionalEntropy_eq_avg_eta_abs (f : BooleanFunction n) (p : ℝ) :
    conditionalEntropy f p = avg (fun y => eta |noiseOp p (signOf f) y|) := by
  rw [conditionalEntropy_eq_avg_eta]
  congr 1
  funext y
  rw [eta_abs]

/-! ### Cancellation and energy (eq:cancellation, Lemma lem:energy) -/

/-- eq:cancellation: E G² − ρ² E(F G) = Σ_k (ρ^{2k} − ρ^{k+2}) W_k(F), G = T_ρ F. -/
theorem cancellation (p : ℝ) (F : Cube n → ℝ) :
    avg (fun x => noiseOp p F x ^ 2) - (1 - 2 * p) ^ 2 * avg (fun x => F x * noiseOp p F x)
      = ∑ k ∈ Finset.range (n + 1), ((1 - 2 * p) ^ (2 * k) - (1 - 2 * p) ^ (k + 2)) * weight F k := by
  have hL : avg (fun x => noiseOp p F x ^ 2) - (1 - 2 * p) ^ 2 * avg (fun x => F x * noiseOp p F x)
      = ∑ S : Finset (Fin n),
          ((1 - 2 * p) ^ (2 * S.card) - (1 - 2 * p) ^ (S.card + 2)) * fourierCoeff F S ^ 2 := by
    rw [parseval, plancherel, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [fourierCoeff_noiseOp]
    ring
  rw [hL]
  unfold weight
  symm
  calc ∑ k ∈ Finset.range (n + 1), ((1 - 2 * p) ^ (2 * k) - (1 - 2 * p) ^ (k + 2)) *
          ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = k),
            fourierCoeff F S ^ 2
      = ∑ k ∈ Finset.range (n + 1),
          ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = k),
            ((1 - 2 * p) ^ (2 * S.card) - (1 - 2 * p) ^ (S.card + 2)) * fourierCoeff F S ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S hS => ?_
        have hk : S.card = k := (Finset.mem_filter.mp hS).2
        rw [hk]
    _ = ∑ S : Finset (Fin n),
          ((1 - 2 * p) ^ (2 * S.card) - (1 - 2 * p) ^ (S.card + 2)) * fourierCoeff F S ^ 2 :=
        Finset.sum_fiberwise_of_maps_to (fun S _ => Finset.mem_range.mpr
          (Nat.lt_succ_of_le ((Finset.card_le_univ S).trans_eq (Fintype.card_fin n)))) _

/-- For `k ≥ 2` and `0 ≤ ρ ≤ 1` the cancellation coefficient `ρ^{2k} − ρ^{k+2}` is nonpositive. -/
theorem cancel_term_nonpos {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (F : Cube n → ℝ) {k : ℕ}
    (hk : 2 ≤ k) : (ρ ^ (2 * k) - ρ ^ (k + 2)) * weight F k ≤ 0 := by
  have hpow : ρ ^ (2 * k) ≤ ρ ^ (k + 2) := pow_le_pow_of_le_one hρ0 hρ1 (by omega)
  have hW := weight_nonneg F k
  nlinarith [mul_le_mul_of_nonneg_right hpow hW]

/-- Only the levels `k = 0, 1` contribute positively to the cancellation sum. -/
theorem cancel_sum_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (F : Cube n → ℝ) :
    ∑ k ∈ Finset.range (n + 1), (ρ ^ (2 * k) - ρ ^ (k + 2)) * weight F k
      ≤ (1 - ρ ^ 2) * weight F 0 + ρ ^ 2 * (1 - ρ) * weight F 1 := by
  have hW1 : 0 ≤ ρ ^ 2 * (1 - ρ) * weight F 1 :=
    mul_nonneg (mul_nonneg (sq_nonneg ρ) (by linarith)) (weight_nonneg F 1)
  have h0 : (ρ ^ (2 * 0) - ρ ^ (0 + 2)) * weight F 0 = (1 - ρ ^ 2) * weight F 0 := by
    norm_num
  rcases n with _ | n'
  · rw [Finset.sum_range_one]
    linarith
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have h1 : (ρ ^ (2 * (0 + 1)) - ρ ^ (0 + 1 + 2)) * weight F (0 + 1)
        = ρ ^ 2 * (1 - ρ) * weight F 1 := by
      show (ρ ^ 2 - ρ ^ 3) * weight F 1 = ρ ^ 2 * (1 - ρ) * weight F 1
      ring
    have hrest : ∑ i ∈ Finset.range n',
        (ρ ^ (2 * (i + 1 + 1)) - ρ ^ (i + 1 + 1 + 2)) * weight F (i + 1 + 1) ≤ 0 :=
      Finset.sum_nonpos fun i _ => cancel_term_nonpos hρ0 hρ1 F (by omega)
    linarith

/-- Lemma lem:energy with a free cap Ω: if m² + W₁(F) ≤ Ω then E ψ_ρ(|G|) ≥ (1−ρ)(Λ_Ω − Γ m²), with ρ = 1 − 2p ∈ [0,1],
    Λ_Ω = 1 + ρ − Ωρ², Γ = 1 + ρ − ρ², m = E F, F = signOf f. -/
theorem energy_lower_bound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (f : BooleanFunction n) (Ω : ℝ)
    (hcap : (avg (signOf f)) ^ 2 + weight (signOf f) 1 ≤ Ω) :
    (1 - (1 - 2 * p)) * ((1 + (1 - 2 * p) - Ω * (1 - 2 * p) ^ 2)
        - (1 + (1 - 2 * p) - (1 - 2 * p) ^ 2) * (avg (signOf f)) ^ 2)
      ≤ avg (fun y => psi (1 - 2 * p) |noiseOp p (signOf f) y|) := by
  have hρ0 : 0 ≤ 1 - 2 * p := by linarith
  have hρ1 : 1 - 2 * p ≤ 1 := by linarith
  -- pointwise: ψ_ρ(|G|) = 1 − ρ² + ρ²|G| − G²
  have hpsi : avg (fun y => psi (1 - 2 * p) |noiseOp p (signOf f) y|)
      = (1 - (1 - 2 * p) ^ 2) + (1 - 2 * p) ^ 2 * avg (fun y => |noiseOp p (signOf f) y|)
        - avg (fun y => noiseOp p (signOf f) y ^ 2) := by
    have hpt : (fun y => psi (1 - 2 * p) |noiseOp p (signOf f) y|)
        = fun y => ((1 - (1 - 2 * p) ^ 2) + (1 - 2 * p) ^ 2 * |noiseOp p (signOf f) y|)
            - noiseOp p (signOf f) y ^ 2 := by
      funext y
      unfold psi
      rw [← sq_abs (noiseOp p (signOf f) y)]
      ring
    rw [hpt, avg_sub, avg_add, avg_const, avg_const_mul]
  -- F·G ≤ |G| pointwise since |F| = 1
  have hFG : avg (fun y => signOf f y * noiseOp p (signOf f) y)
      ≤ avg (fun y => |noiseOp p (signOf f) y|) := by
    apply avg_le_avg
    intro y
    calc signOf f y * noiseOp p (signOf f) y ≤ |signOf f y * noiseOp p (signOf f) y| :=
          le_abs_self _
      _ = |noiseOp p (signOf f) y| := by rw [abs_mul, abs_signOf, one_mul]
  have hcancel := cancellation p (signOf f)
  have hsum := cancel_sum_le hρ0 hρ1 (signOf f)
  have hW0 : weight (signOf f) 0 = (avg (signOf f)) ^ 2 := weight_zero _
  have h1 : (1 - 2 * p) ^ 2 * avg (fun y => signOf f y * noiseOp p (signOf f) y)
      ≤ (1 - 2 * p) ^ 2 * avg (fun y => |noiseOp p (signOf f) y|) :=
    mul_le_mul_of_nonneg_left hFG (sq_nonneg _)
  have h2 : (1 - 2 * p) ^ 2 * (1 - (1 - 2 * p)) * weight (signOf f) 1
      ≤ (1 - 2 * p) ^ 2 * (1 - (1 - 2 * p)) * (Ω - (avg (signOf f)) ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (sq_nonneg _) (by linarith))
  rw [hpsi]
  nlinarith [h1, h2, hcancel, hsum, hW0]

end CK
