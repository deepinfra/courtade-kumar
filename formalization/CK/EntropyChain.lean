import CK.Disintegration

/-!
# Exact entropy chain identities on a finite probability space

Successive conditioning is reduced to explicit weighted fibre identities.
All zero-probability fibres remain covered by `conditionOn`'s normalized fallback.
-/

noncomputable section
namespace CourtadeKumar
namespace FiniteLaw
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]
variable {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]

omit [Fintype U] [Fintype Z] in
theorem mass_mul_conditionOn_fibreMass (μ : FiniteLaw Ω) (u : Ω → U) (z : Ω → Z)
    (a : U) (b : Z) :
    μ.fibreMass u a * (μ.conditionOn u a).fibreMass z b =
      μ.fibreMass (fun ω => (u ω, z ω)) (a, b) := by
  change μ.fibreMass u a * (∑ ω, if z ω = b then (μ.conditionOn u a).mass ω else 0) =
    ∑ ω, if (u ω, z ω) = (a, b) then μ.mass ω else 0
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hz : z ω = b
  · simp only [if_pos hz]
    rw [μ.mass_mul_conditionOn_mass u a ω]
    simp [hz]
  · simp [hz]

omit [Fintype U] [Fintype Z] in
theorem mass_mul_conditionOn_fibreMoment (μ : FiniteLaw Ω) (u : Ω → U) (z : Ω → Z)
    (a : U) (b : Z) (c : Ω → ℝ) :
    μ.fibreMass u a * (μ.conditionOn u a).fibreMoment z c b =
      μ.fibreMoment (fun ω => (u ω, z ω)) c (a, b) := by
  change μ.fibreMass u a *
      (∑ ω, if z ω = b then (μ.conditionOn u a).mass ω * c ω else 0) =
    ∑ ω, if (u ω, z ω) = (a, b) then μ.mass ω * c ω else 0
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hz : z ω = b
  · simp only [if_pos hz]
    rw [← mul_assoc, μ.mass_mul_conditionOn_mass u a ω]
    simp [hz, mul_ite, ite_mul]
  · simp [hz]

omit [Fintype U] [Fintype Z] in
theorem conditionOn_conditionalMean (μ : FiniteLaw Ω) (u : Ω → U) (z : Ω → Z)
    (a : U) (ha : μ.fibreMass u a ≠ 0) (b : Z) (c : Ω → ℝ) :
    (μ.conditionOn u a).conditionalMean z c b =
      μ.conditionalMean (fun ω => (u ω, z ω)) c (a, b) := by
  unfold conditionalMean
  rw [← μ.mass_mul_conditionOn_fibreMoment u z a b c,
    ← μ.mass_mul_conditionOn_fibreMass u z a b, mul_div_mul_left _ _ ha]

/-- The weighted tower identity holds for every function of the posterior mean. -/
theorem iterated_conditionalMean_tower (μ : FiniteLaw Ω) (u : Ω → U) (z : Ω → Z)
    (c : Ω → ℝ) (F : ℝ → ℝ) :
    (μ.map u).expect (fun a => ((μ.conditionOn u a).map z).expect
      (fun b => F ((μ.conditionOn u a).conditionalMean z c b))) =
      (μ.map (fun ω => (u ω, z ω))).expect
        (fun ab => F (μ.conditionalMean (fun ω => (u ω, z ω)) c ab)) := by
  change (∑ a, μ.fibreMass u a *
      ∑ b, (μ.conditionOn u a).fibreMass z b * F ((μ.conditionOn u a).conditionalMean z c b)) =
    ∑ ab : U × Z, μ.fibreMass (fun ω => (u ω, z ω)) ab *
      F (μ.conditionalMean (fun ω => (u ω, z ω)) c ab)
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : μ.fibreMass u a = 0
  · have hz : μ.fibreMass (fun ω => (u ω, z ω)) (a, b) = 0 := by
      rw [← μ.mass_mul_conditionOn_fibreMass u z a b, ha, zero_mul]
    simp [ha, hz]
  · rw [μ.conditionOn_conditionalMean u z a ha b c, ← mul_assoc,
      μ.mass_mul_conditionOn_fibreMass u z a b]

theorem conditionalShannonEntropy_tower (μ : FiniteLaw Ω) (u : Ω → U) (z : Ω → Z)
    (c : Ω → ℝ) :
    (μ.map u).expect (fun a => (μ.conditionOn u a).conditionalShannonEntropy z c) =
      μ.conditionalShannonEntropy (fun ω => (u ω, z ω)) c :=
  μ.iterated_conditionalMean_tower u z c entropyBits

theorem conditionalQuadraticEntropy_tower (μ : FiniteLaw Ω) (u : Ω → U) (z : Ω → Z)
    (c : Ω → ℝ) :
    (μ.map u).expect (fun a => (μ.conditionOn u a).conditionalQuadraticEntropy z c) =
      μ.conditionalQuadraticEntropy (fun ω => (u ω, z ω)) c :=
  μ.iterated_conditionalMean_tower u z c quadraticEntropy

/-- Shannon chain rule with an arbitrary finite observed alphabet. -/
theorem shannonInformation_chain (μ : FiniteLaw Ω) (u : Ω → U) (z : Ω → Z)
    (c : Ω → ℝ) :
    μ.shannonInformation c (fun ω => (u ω, z ω)) =
      μ.shannonInformation c u + μ.conditionalShannonInformation c z u := by
  unfold conditionalShannonInformation shannonInformation
  rw [(μ.map u).expect_sub, μ.conditionOn_shannonEntropy_tower u c,
    μ.conditionalShannonEntropy_tower u z c]
  ring

def conditionalQuadraticInformation (μ : FiniteLaw Ω) (c : Ω → ℝ)
    (z : Ω → Z) (u : Ω → U) : ℝ :=
  (μ.map u).expect (fun a => (μ.conditionOn u a).quadraticInformation c z)

/-- The normalized quadratic information has the same conditional chain identity. -/
theorem quadraticInformation_chain (μ : FiniteLaw Ω) (u : Ω → U) (z : Ω → Z)
    (c : Ω → ℝ) :
    μ.quadraticInformation c (fun ω => (u ω, z ω)) =
      μ.quadraticInformation c u + μ.conditionalQuadraticInformation c z u := by
  unfold conditionalQuadraticInformation quadraticInformation
  rw [(μ.map u).expect_sub, μ.conditionOn_quadraticEntropy_tower u c,
    μ.conditionalQuadraticEntropy_tower u z c]
  ring

/-- Binary entropy's exact perspective identity, with zero denominators covered. -/
theorem entropyBits_perspective {q r : ℝ} (hr0 : 0 ≤ r) (hrq : r ≤ q) :
    q * entropyBits (r / q) =
      (Real.negMulLog r + Real.negMulLog (q - r) - Real.negMulLog q) / Real.log 2 := by
  by_cases hq0 : q = 0
  · have hr : r = 0 := by linarith
    simp [hq0, hr]
  · have he1 : q * (r / q) = r := by field_simp
    have he2 : q * (1 - r / q) = q - r := by field_simp
    have h1 := Real.negMulLog_mul q (r / q)
    have h2 := Real.negMulLog_mul q (1 - r / q)
    rw [he1] at h1
    rw [he2] at h2
    have hn : q * Real.binEntropy (r / q) =
        Real.negMulLog r + Real.negMulLog (q - r) - Real.negMulLog q := by
      rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      nlinarith
    unfold entropyBits
    rw [← mul_div_assoc, hn]

theorem fibreMoment_bit_eq_pair (μ : FiniteLaw Ω) (b c : Ω → Bool) (s : Bool) :
    μ.fibreMoment b (fun ω => bitValue (c ω)) s =
      μ.fibreMass (fun ω => (b ω, c ω)) (s, true) := by
  unfold fibreMoment fibreMass
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hb : b ω = s <;> cases hc : c ω <;> simp [hb, hc, bitValue]

theorem bit_entropy_eq_fibreMass (μ : FiniteLaw Ω) (b : Ω → Bool) :
    entropyBits (μ.expect (fun ω => bitValue (b ω))) =
      (Real.negMulLog (μ.fibreMass b true) + Real.negMulLog (μ.fibreMass b false)) / Real.log 2 := by
  have hm := μ.fibreMass_sum b
  simp only [Fintype.sum_bool] at hm
  rw [μ.expect_bitValue]
  unfold entropyBits
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    show 1 - μ.fibreMass b true = μ.fibreMass b false by linarith]

/-- Shannon entropy of the exact four-cell joint distribution. -/
def bitJointEntropy (μ : FiniteLaw Ω) (b c : Ω → Bool) : ℝ :=
  (∑ s : Bool, ∑ t : Bool,
    Real.negMulLog (μ.fibreMass (fun ω => (b ω, c ω)) (s, t))) / Real.log 2

theorem pair_fibreMass_swap (μ : FiniteLaw Ω) (b c : Ω → Bool) (s t : Bool) :
    μ.fibreMass (fun ω => (b ω, c ω)) (s, t) =
      μ.fibreMass (fun ω => (c ω, b ω)) (t, s) := by
  unfold fibreMass
  apply Finset.sum_congr rfl
  intro ω _
  simp only [Prod.mk.injEq, and_comm]

theorem bitJointEntropy_symm (μ : FiniteLaw Ω) (b c : Ω → Bool) :
    μ.bitJointEntropy b c = μ.bitJointEntropy c b := by
  unfold bitJointEntropy
  simp_rw [μ.pair_fibreMass_swap b c]
  rw [Finset.sum_comm]

/-- The exact binary conditional entropy identity, including constant bits. -/
theorem conditionalShannonEntropy_bits (μ : FiniteLaw Ω) (b c : Ω → Bool) :
    μ.conditionalShannonEntropy b (fun ω => bitValue (c ω)) =
      μ.bitJointEntropy b c - entropyBits (μ.expect (fun ω => bitValue (b ω))) := by
  have hs (s : Bool) := entropyBits_perspective
    (μ.fibreMoment_nonneg b (fun ω => bitValue_nonneg (c ω)) s)
    (μ.fibreMoment_le_mass b (fun ω => bitValue_le_one (c ω)) s)
  have he (s : Bool) : μ.fibreMass b s - μ.fibreMoment b (fun ω => bitValue (c ω)) s =
      μ.fibreMass (fun ω => (b ω, c ω)) (s, false) := by
    rw [μ.fibreMoment_bit_eq_pair b c s, μ.fibreMass_first_pair b c s]
    ring
  change (∑ s : Bool, μ.fibreMass b s *
      entropyBits (μ.fibreMoment b (fun ω => bitValue (c ω)) s / μ.fibreMass b s)) = _
  simp_rw [hs, he, μ.fibreMoment_bit_eq_pair b c]
  rw [μ.bit_entropy_eq_fibreMass b]
  unfold bitJointEntropy
  simp only [Fintype.sum_bool]
  ring

/-- Mutual information of two bits is symmetric; no nondegeneracy hypotheses. -/
theorem shannonInformation_symm (μ : FiniteLaw Ω) (b c : Ω → Bool) :
    μ.shannonInformation (fun ω => bitValue (b ω)) c =
      μ.shannonInformation (fun ω => bitValue (c ω)) b := by
  unfold shannonInformation
  rw [μ.conditionalShannonEntropy_bits c b, μ.conditionalShannonEntropy_bits b c,
    μ.bitJointEntropy_symm c b]
  ring

theorem conditionalShannonInformation_symm (μ : FiniteLaw Ω)
    (b c : Ω → Bool) (u : Ω → U) :
    μ.conditionalShannonInformation (fun ω => bitValue (b ω)) c u =
      μ.conditionalShannonInformation (fun ω => bitValue (c ω)) b u := by
  unfold conditionalShannonInformation
  congr 1
  funext a
  exact (μ.conditionOn u a).shannonInformation_symm b c

end FiniteLaw
end CourtadeKumar
