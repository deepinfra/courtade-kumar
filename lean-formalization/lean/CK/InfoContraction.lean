import CK.Deficit
import CK.Bridge

/-!
# Information contraction in posterior form (manuscript `lem:contraction`, Lemma 5.1)

`infoP π = h(E π) − E h(π)` is the mutual information `I(Z;U)` between a bit `Z` and a
uniform cube variable `U` when `π u = P(Z = 1 | U = u)`.  Passing `U` through the product
BSC contracts this information by `(1 − 2p)²` (`infoP_noisy_le`).  This is derived from the
deficit contraction `deficit_noisy_le` of `CK.Deficit` through the identity
`μ·deficit q₁ + (1 − μ)·deficit q₀ = infoP π` (`infoP_eq_deficit`), where `q₁, q₀` are the
conditional distributions of `U` given `Z = 1`, resp. `Z = 0`.

Applications:
* U1 `information_le_contraction`: `I(f(X);Y) ≤ ρ² H(f(X))`;
* U3 `information_degrade` (degradation, Prop `prop:high`): `I(f;Y_p) ≤ ((1−2p)/(1−2p₀))² I(f;Y_{p₀})`
  via the BSC composition rule `kernel_compose` / `noisy_noisy`;
* U2 `conditionalEntropy_ge_conditional` (`eq:conditionalcontraction` at the last coordinate,
  used by `lem:largecoordinate`).
-/
noncomputable section
namespace CK
open scoped BigOperators

/-- Posterior-form information: for π : Cube k → [0,1] (π u = P(Z = 1 | U = u), U uniform),
I(Z;U) = h(E π) − E h(π). -/
def infoP {k : ℕ} (π : Cube k → ℝ) : ℝ :=
  binaryEntropy (avg π) - avg (fun u => binaryEntropy (π u))

/-! ## Elementary facts about `avg`, `noisy`, `ent` -/

/-- `Fintype.card (Cube k) = 2^k` as a real number. -/
theorem card_cube_real (k : ℕ) : ((Fintype.card (Cube k) : ℕ) : ℝ) = 2 ^ k := by
  simp

theorem sum_one_cube (k : ℕ) : ∑ _u : Cube k, (1 : ℝ) = 2 ^ k := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube_real, mul_one]

theorem avg_const' {k : ℕ} (c : ℝ) : avg (fun _ : Cube k => c) = c := by
  unfold avg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube_real]
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  field_simp

theorem avg_lin2 {k : ℕ} (a b : ℝ) (u v : Cube k → ℝ) :
    avg (fun x => a * u x + b * v x) = a * avg u + b * avg v := by
  unfold avg
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The channel preserves the uniform average. -/
theorem avg_noisy {k : ℕ} {p : ℝ} (π : Cube k → ℝ) : avg (noisy p π) = avg π := by
  unfold avg
  rw [sum_noisy]

theorem noisy_const {k : ℕ} (p c : ℝ) : noisy p (fun _ : Cube k => c) = fun _ => c := by
  funext w
  unfold noisy
  rw [← Finset.sum_mul, kernel_row_sum, one_mul]

theorem noisy_lin {k : ℕ} (p a b : ℝ) (q q' : Cube k → ℝ) :
    noisy p (fun u => a * q u + b * q' u) = fun w => a * noisy p q w + b * noisy p q' w := by
  funext w
  unfold noisy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

theorem noisy_smul_one_sub {k : ℕ} (p c : ℝ) (q : Cube k → ℝ) :
    noisy p (fun u => c * (1 - q u)) = fun w => c * (1 - noisy p q w) := by
  funext w
  unfold noisy
  have hr := kernel_row_sum p w
  calc ∑ u, kernel p w u * (c * (1 - q u))
      = c * ∑ u, kernel p w u - c * ∑ u, kernel p w u * q u := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        ring
    _ = c * (1 - ∑ u, kernel p w u * q u) := by rw [hr]; ring

/-- Entropy of a rescaled vector (`Real.negMulLog_mul`). -/
theorem ent_smul {α : Type*} [Fintype α] (c : ℝ) (v : α → ℝ) :
    ent (fun a => c * v a) = c * ent v + (∑ a, v a) * Real.negMulLog c := by
  unfold ent
  simp_rw [Real.negMulLog_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- `Σ_u h(π u) = ent π + ent (1 − π)`. -/
theorem sum_binaryEntropy_eq_ent {k : ℕ} (π : Cube k → ℝ) :
    ∑ u, binaryEntropy (π u) = ent π + ent (fun u => 1 - π u) := by
  unfold ent
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold binaryEntropy Real.negMulLog
  ring

theorem infoP_const {k : ℕ} (c : ℝ) : infoP (fun _ : Cube k => c) = 0 := by
  unfold infoP
  rw [avg_const', avg_const', sub_self]

/-! ## The key identity: `μ·deficit q₁ + (1 − μ)·deficit q₀ = infoP π` -/

/-- With `μ = avg π`, `q₁ = π/(2^k μ)` and `q₀ = (1 − π)/(2^k (1 − μ))` (the conditional
distributions of `U` given `Z = 1`, resp. `Z = 0`), the weighted deficits sum to the
posterior-form information. -/
theorem infoP_eq_deficit {k : ℕ} {π : Cube k → ℝ} (hμ0 : 0 < avg π) (hμ1 : avg π < 1) :
    avg π * deficit (fun u => ((2 : ℝ) ^ k * avg π)⁻¹ * π u)
      + (1 - avg π) * deficit (fun u => ((2 : ℝ) ^ k * (1 - avg π))⁻¹ * (1 - π u)) = infoP π := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hμ1' : 0 < 1 - avg π := by linarith
  have hS : ∑ u, π u = 2 ^ k * avg π := by
    unfold avg
    field_simp
  have hT : ∑ u, (1 - π u) = 2 ^ k * (1 - avg π) := by
    rw [Finset.sum_sub_distrib, sum_one_cube, hS]
    ring
  have he1 : ent (fun u => ((2 : ℝ) ^ k * avg π)⁻¹ * π u)
      = ((2 : ℝ) ^ k * avg π)⁻¹ * ent π
        + (∑ u, π u) * Real.negMulLog (((2 : ℝ) ^ k * avg π)⁻¹) :=
    ent_smul _ _
  have he0 : ent (fun u => ((2 : ℝ) ^ k * (1 - avg π))⁻¹ * (1 - π u))
      = ((2 : ℝ) ^ k * (1 - avg π))⁻¹ * ent (fun u => 1 - π u)
        + (∑ u, (1 - π u)) * Real.negMulLog (((2 : ℝ) ^ k * (1 - avg π))⁻¹) :=
    ent_smul _ _
  have hl1 : Real.negMulLog (((2 : ℝ) ^ k * avg π)⁻¹)
      = ((2 : ℝ) ^ k * avg π)⁻¹ * (k * Real.log 2 + Real.log (avg π)) := by
    unfold Real.negMulLog
    rw [Real.log_inv, Real.log_mul h2.ne' hμ0.ne', Real.log_pow]
    ring
  have hl0 : Real.negMulLog (((2 : ℝ) ^ k * (1 - avg π))⁻¹)
      = ((2 : ℝ) ^ k * (1 - avg π))⁻¹ * (k * Real.log 2 + Real.log (1 - avg π)) := by
    unfold Real.negMulLog
    rw [Real.log_inv, Real.log_mul h2.ne' hμ1'.ne', Real.log_pow]
    ring
  have hA : avg (fun u => binaryEntropy (π u)) = (ent π + ent (fun u => 1 - π u)) / 2 ^ k := by
    unfold avg
    rw [sum_binaryEntropy_eq_ent]
  unfold infoP deficit
  rw [he1, he0, hl1, hl0, hS, hT, hA]
  unfold binaryEntropy
  field_simp
  ring

/-! ## Lemma `lem:contraction` in posterior form -/

/-- Lemma lem:contraction, posterior form: I(Z; U_θ) ≤ θ² I(Z; U) with θ = 1 − 2p. -/
theorem infoP_noisy_le {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) {π : Cube k → ℝ}
    (h0 : ∀ u, 0 ≤ π u) (h1 : ∀ u, π u ≤ 1) :
    infoP (noisy p π) ≤ (1 - 2 * p) ^ 2 * infoP π := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hS : ∑ u, π u = 2 ^ k * avg π := by
    unfold avg
    field_simp
  have hμ0 : 0 ≤ avg π := div_nonneg (Finset.sum_nonneg fun u _ => h0 u) h2.le
  have hμ1 : avg π ≤ 1 := by
    unfold avg
    rw [div_le_one h2]
    calc ∑ u, π u ≤ ∑ _u : Cube k, (1 : ℝ) := Finset.sum_le_sum fun u _ => h1 u
      _ = 2 ^ k := sum_one_cube k
  rcases hμ0.eq_or_lt with hz | hpos
  · -- `avg π = 0`: then `π ≡ 0` and both sides vanish.
    have hπ : π = fun _ => 0 := by
      funext u
      have hs : ∑ u, π u = 0 := by rw [hS, ← hz, mul_zero]
      exact (Finset.sum_eq_zero_iff_of_nonneg fun u _ => h0 u).mp hs u (Finset.mem_univ u)
    subst hπ
    simp only [noisy_const, infoP_const, mul_zero, le_refl]
  rcases hμ1.eq_or_lt with ho | hlt
  · -- `avg π = 1`: then `π ≡ 1` and both sides vanish.
    have hπ : π = fun _ => 1 := by
      funext u
      have hs : ∑ u, (1 - π u) = 0 := by
        rw [Finset.sum_sub_distrib, sum_one_cube, hS, ho]
        ring
      have := (Finset.sum_eq_zero_iff_of_nonneg fun u _ => sub_nonneg.mpr (h1 u)).mp hs u
        (Finset.mem_univ u)
      linarith
    subst hπ
    simp only [noisy_const, infoP_const, mul_zero, le_refl]
  -- main case `0 < avg π < 1`
  have hμ1' : 0 < 1 - avg π := by linarith
  have hT : ∑ u, (1 - π u) = 2 ^ k * (1 - avg π) := by
    rw [Finset.sum_sub_distrib, sum_one_cube, hS]
    ring
  have hc1 : (2 : ℝ) ^ k * avg π ≠ 0 := (mul_pos h2 hpos).ne'
  have hc0 : (2 : ℝ) ^ k * (1 - avg π) ≠ 0 := (mul_pos h2 hμ1').ne'
  have hq1 : IsDist (fun u => ((2 : ℝ) ^ k * avg π)⁻¹ * π u) :=
    ⟨fun u => mul_nonneg (inv_pos.mpr (mul_pos h2 hpos)).le (h0 u),
     by rw [← Finset.mul_sum, hS]; exact inv_mul_cancel₀ hc1⟩
  have hq0 : IsDist (fun u => ((2 : ℝ) ^ k * (1 - avg π))⁻¹ * (1 - π u)) :=
    ⟨fun u => mul_nonneg (inv_pos.mpr (mul_pos h2 hμ1')).le (sub_nonneg.mpr (h1 u)),
     by rw [← Finset.mul_sum, hT]; exact inv_mul_cancel₀ hc0⟩
  have hd1 := deficit_noisy_le hp0 hp1 hq1
  have hd0 := deficit_noisy_le hp0 hp1 hq0
  rw [noisy_smul] at hd1
  rw [noisy_smul_one_sub] at hd0
  have hidπ := infoP_eq_deficit hpos hlt
  have hidN := infoP_eq_deficit (π := noisy p π) (by rwa [avg_noisy]) (by rwa [avg_noisy])
  rw [avg_noisy] at hidN
  nlinarith [mul_le_mul_of_nonneg_left hd1 hpos.le, mul_le_mul_of_nonneg_left hd0 hμ1'.le,
    hidN, hidπ]

/-! ## U1: information contraction for Boolean functions -/

theorem posterior_eq_noisy {n : ℕ} (f : BooleanFunction n) (p : ℝ) :
    posterior f p = noisy p (fun x => indicator (f x)) := rfl

/-- `infoP` of the posterior is the information of `f` (`posterior_mean`). -/
theorem infoP_posterior {n : ℕ} (f : BooleanFunction n) (p : ℝ) :
    infoP (posterior f p) = information f p := by
  unfold infoP information conditionalEntropy
  have h := posterior_mean f p
  rw [show avg (posterior f p) = avg (fun y => posterior f p y) from rfl, h]

theorem binaryEntropy_indicator (b : Bool) : binaryEntropy (indicator b) = 0 := by
  cases b <;> simp [indicator, binaryEntropy_zero, binaryEntropy_one]

/-- The information of a deterministic bit is its entropy. -/
theorem infoP_indicator {n : ℕ} (f : BooleanFunction n) :
    infoP (fun x => indicator (f x)) = binaryEntropy (mean f) := by
  unfold infoP mean
  simp only [binaryEntropy_indicator, avg_const', sub_zero]

/-- U1 (used by Lemma lem:bias): I(f(X);Y) ≤ ρ² H(f(X)). -/
theorem information_le_contraction {n : ℕ} (f : BooleanFunction n) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1 / 2) :
    information f p ≤ (1 - 2 * p) ^ 2 * binaryEntropy (mean f) := by
  have h := infoP_noisy_le hp0 hp1 (π := fun x => indicator (f x))
    (fun x => indicator_nonneg (f x)) (fun x => indicator_le_one (f x))
  rw [← posterior_eq_noisy, infoP_posterior, infoP_indicator] at h
  exact h

/-! ## BSC composition and U3 (degradation) -/

/-- BSC composition: BSC(p₀) followed by BSC(p') is BSC(p₀ + p' − 2p₀p'). (NB: the name
`kernel_comp` is already taken in CK/Relabel.lean for the permutation lemma.) -/
theorem kernel_compose {n : ℕ} (p0 p' : ℝ) (y x : Cube n) :
    (∑ z : Cube n, kernel p' y z * kernel p0 z x) = kernel (p0 + p' - 2 * p0 * p') y x := by
  unfold kernel
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    (if y i = b then 1 - p' else p') * (if b = x i then 1 - p0 else p0))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  cases hy : y i <;> cases hx : x i <;> simp <;> ring

theorem noisy_noisy {k : ℕ} (p0 p' : ℝ) (π : Cube k → ℝ) :
    noisy p' (noisy p0 π) = noisy (p0 + p' - 2 * p0 * p') π := by
  funext w
  unfold noisy
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← kernel_compose, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  ring

/-- U3 (degradation, used by Prop prop:high): for 0 ≤ p₀ ≤ p ≤ 1/2, p₀ < 1/2:
I(f;Y_p) ≤ ((1−2p)/(1−2p₀))² I(f;Y_{p₀}). -/
theorem information_degrade {n : ℕ} (f : BooleanFunction n) {p0 p : ℝ} (hp0 : 0 ≤ p0)
    (hp0' : p0 < 1 / 2) (hpp : p0 ≤ p) (hp1 : p ≤ 1 / 2) :
    information f p ≤ ((1 - 2 * p) / (1 - 2 * p0)) ^ 2 * information f p0 := by
  have hd : 0 < 1 - 2 * p0 := by linarith
  obtain ⟨p', hp'⟩ : ∃ p', p' = (p - p0) / (1 - 2 * p0) := ⟨_, rfl⟩
  have hp'0 : 0 ≤ p' := by rw [hp']; exact div_nonneg (by linarith) hd.le
  have hp'1 : p' ≤ 1 / 2 := by rw [hp', div_le_iff₀ hd]; linarith
  have hcomp : p0 + p' - 2 * p0 * p' = p := by
    rw [hp']
    field_simp
    ring
  have hrho : 1 - 2 * p' = (1 - 2 * p) / (1 - 2 * p0) := by
    rw [hp']
    field_simp
    ring
  have h := infoP_noisy_le hp'0 hp'1 (π := posterior f p0)
    (posterior_nonneg f p0 hp0 (by linarith)) (posterior_le_one f p0 hp0 (by linarith))
  rw [posterior_eq_noisy f p0, noisy_noisy, hcomp, ← posterior_eq_noisy f p,
    ← posterior_eq_noisy f p0, hrho, infoP_posterior, infoP_posterior] at h
  exact h

/-! ## U2: `eq:conditionalcontraction` at the last coordinate -/

/-- `h((1−p)·1_a + p·1_b)` is `0` when `a = b` and `h(p)` otherwise. -/
theorem binaryEntropy_mix_indicator (p : ℝ) (a b : Bool) :
    binaryEntropy ((1 - p) * indicator a + p * indicator b)
      = if a = b then 0 else binaryEntropy p := by
  cases a <;> cases b <;> simp [indicator, binaryEntropy_zero, binaryEntropy_one, binaryEntropy_symm]

/-- U2 (eq:conditionalcontraction at the last coordinate, used by Lemma lem:largecoordinate):
H(f|Y) ≥ (1−ρ²) H(f|Y_last) + ρ² H(f|X',Y_last), with H(f|Y_last) = Q(m, ρb) and
H(f|X',Y_last) = σ h(p). -/
theorem conditionalEntropy_ge_conditional {n : ℕ} (f : BooleanFunction (n + 1)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (1 - (1 - 2 * p) ^ 2) * pairEntropy (2 * mean f - 1)
        ((1 - 2 * p) * (mean (sectionLast f true) - mean (sectionLast f false)))
      + (1 - 2 * p) ^ 2 * avg (fun w => if sectionLast f true w = sectionLast f false w
          then (0 : ℝ) else binaryEntropy p)
    ≤ conditionalEntropy f p := by
  have hp1' : p ≤ 1 := by linarith
  -- the contraction applied to the section mixture `π_s`
  have key : ∀ s : Bool,
      (1 - (1 - 2 * p) ^ 2)
          * binaryEntropy ((1 - p) * mean (sectionLast f s) + p * mean (sectionLast f (!s)))
        + (1 - 2 * p) ^ 2 * avg (fun w => if sectionLast f true w = sectionLast f false w
            then (0 : ℝ) else binaryEntropy p)
      ≤ avg (fun w => binaryEntropy (posterior f p (Fin.snoc w s))) := by
    intro s
    have h0 : ∀ w, 0 ≤ (1 - p) * indicator (sectionLast f s w)
        + p * indicator (sectionLast f (!s) w) := fun w =>
      add_nonneg (mul_nonneg (by linarith) (indicator_nonneg _))
        (mul_nonneg hp0 (indicator_nonneg _))
    have h1 : ∀ w, (1 - p) * indicator (sectionLast f s w)
        + p * indicator (sectionLast f (!s) w) ≤ 1 := fun w => by
      have ha := indicator_le_one (sectionLast f s w)
      have hb := indicator_le_one (sectionLast f (!s) w)
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - p) (sub_nonneg.mpr ha),
        mul_nonneg hp0 (sub_nonneg.mpr hb)]
    have h := infoP_noisy_le hp0 hp1
      (π := fun w => (1 - p) * indicator (sectionLast f s w) + p * indicator (sectionLast f (!s) w))
      h0 h1
    have hN : ∀ w, noisy p (fun w => (1 - p) * indicator (sectionLast f s w)
        + p * indicator (sectionLast f (!s) w)) w = posterior f p (Fin.snoc w s) := by
      intro w
      rw [posterior_snoc, posterior_eq_noisy (sectionLast f s), posterior_eq_noisy (sectionLast f (!s))]
      exact congrFun (noisy_lin p (1 - p) p (fun w => indicator (sectionLast f s w))
        (fun w => indicator (sectionLast f (!s) w))) w
    have hA : avg (fun w => (1 - p) * indicator (sectionLast f s w)
        + p * indicator (sectionLast f (!s) w))
        = (1 - p) * mean (sectionLast f s) + p * mean (sectionLast f (!s)) :=
      avg_lin2 (1 - p) p (fun w => indicator (sectionLast f s w))
        (fun w => indicator (sectionLast f (!s) w))
    have hE : avg (fun w => binaryEntropy ((1 - p) * indicator (sectionLast f s w)
        + p * indicator (sectionLast f (!s) w)))
        = avg (fun w => if sectionLast f true w = sectionLast f false w
            then (0 : ℝ) else binaryEntropy p) := by
      congr 1
      funext w
      rw [binaryEntropy_mix_indicator]
      cases s
      · simp only [Bool.not_false]
        by_cases hw : sectionLast f true w = sectionLast f false w
        · simp [hw]
        · simp [hw, Ne.symm hw]
      · simp only [Bool.not_true]
    unfold infoP at h
    rw [avg_noisy, hA, hE] at h
    simp only [hN] at h
    linarith
  have hT := key true
  have hF := key false
  simp only [Bool.not_true, Bool.not_false] at hT hF
  have hce : conditionalEntropy f p
      = (avg (fun w => binaryEntropy (posterior f p (Fin.snoc w true)))
        + avg (fun w => binaryEntropy (posterior f p (Fin.snoc w false)))) / 2 := by
    unfold conditionalEntropy
    exact avg_snoc _
  have hpe : pairEntropy (2 * mean f - 1)
      ((1 - 2 * p) * (mean (sectionLast f true) - mean (sectionLast f false)))
      = (binaryEntropy ((1 - p) * mean (sectionLast f true) + p * mean (sectionLast f false))
        + binaryEntropy ((1 - p) * mean (sectionLast f false) + p * mean (sectionLast f true)))
          / 2 := by
    unfold pairEntropy
    rw [mean_snoc f, binaryEntropy_eq_eta, binaryEntropy_eq_eta]
    ring_nf
  rw [hce, hpe]
  linarith

end CK
