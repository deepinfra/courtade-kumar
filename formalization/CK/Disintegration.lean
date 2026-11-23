import CK.InformationChain

/-!
# Conditioning an actual finite joint law

`conditionOn` constructs the conditional law from the original sample space.
Zero-probability observations use the original law as a normalized fallback;
their contribution to every conditional average is zero.
-/

noncomputable section
namespace CourtadeKumar
namespace FiniteLaw
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]
variable {U : Type*} [DecidableEq U]

theorem atom_le_fibreMass (μ : FiniteLaw Ω) (u : Ω → U) (ω : Ω) :
    μ.mass ω ≤ μ.fibreMass u (u ω) := by
  classical
  have h := Finset.single_le_sum
    (fun x (_ : x ∈ Finset.univ) =>
      show 0 ≤ if u x = u ω then μ.mass x else 0 from by
        split_ifs
        · exact μ.mass_nonneg x
        · exact le_rfl)
    (Finset.mem_univ ω)
  simpa [fibreMass] using h

theorem atom_eq_zero_of_fibreMass_eq_zero (μ : FiniteLaw Ω) (u : Ω → U)
    (a : U) (ha : μ.fibreMass u a = 0) (ω : Ω) (hω : u ω = a) : μ.mass ω = 0 := by
  have h := μ.atom_le_fibreMass u ω
  rw [hω, ha] at h
  exact le_antisymm h (μ.mass_nonneg ω)

/-- Conditional law on an observed fibre, normalized even on a null observation. -/
def conditionOn (μ : FiniteLaw Ω) (u : Ω → U) (a : U) : FiniteLaw Ω :=
  if h : 0 < μ.fibreMass u a then
    μ.reweight (fun ω => if u ω = a then 1 else 0)
      (fun ω => by dsimp only; split_ifs <;> norm_num)
      (by rw [← μ.fibreMass_eq_expect u a]; exact h)
  else μ

theorem conditionOn_mass_of_pos (μ : FiniteLaw Ω) (u : Ω → U) (a : U)
    (ha : 0 < μ.fibreMass u a) (ω : Ω) :
    (μ.conditionOn u a).mass ω =
      μ.mass ω * (if u ω = a then 1 else 0) / μ.fibreMass u a := by
  simp [conditionOn, ha, reweight, ← μ.fibreMass_eq_expect u a]

/-- Bayes' numerator identity, with null events included. -/
theorem mass_mul_conditionOn_mass (μ : FiniteLaw Ω) (u : Ω → U) (a : U) (ω : Ω) :
    μ.fibreMass u a * (μ.conditionOn u a).mass ω =
      if u ω = a then μ.mass ω else 0 := by
  by_cases ha : 0 < μ.fibreMass u a
  · rw [μ.conditionOn_mass_of_pos u a ha ω]
    by_cases hω : u ω = a
    · simp [hω]
      field_simp [ha.ne']
    · simp [hω]
  · have hz : μ.fibreMass u a = 0 := le_antisymm (le_of_not_gt ha) (μ.fibreMass_nonneg u a)
    by_cases hω : u ω = a
    · rw [hz, zero_mul, if_pos hω, μ.atom_eq_zero_of_fibreMass_eq_zero u a hz ω hω]
    · simp [hz, hω]

theorem eq_of_mass_eq (μ ν : FiniteLaw Ω) (h : ∀ ω, μ.mass ω = ν.mass ω) : μ = ν := by
  cases μ with
  | mk m hm hs =>
    cases ν with
    | mk m' hm' hs' =>
      have he : m = m' := funext h
      cases he
      rfl

variable [Fintype U]

/-- The conditional laws reconstruct the original joint law exactly. -/
theorem mixture_conditionOn (μ : FiniteLaw Ω) (u : Ω → U) :
    (μ.map u).mixture (μ.conditionOn u) = μ := by
  apply eq_of_mass_eq
  intro ω
  change (∑ a, μ.fibreMass u a * (μ.conditionOn u a).mass ω) = μ.mass ω
  simp_rw [μ.mass_mul_conditionOn_mass u]
  simp

omit [Fintype U] in
theorem mass_mul_conditionOn_expect (μ : FiniteLaw Ω) (u : Ω → U)
    (a : U) (c : Ω → ℝ) :
    μ.fibreMass u a * (μ.conditionOn u a).expect c = μ.fibreMoment u c a := by
  unfold expect fibreMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← mul_assoc, μ.mass_mul_conditionOn_mass u a ω]
  split_ifs <;> simp_all

omit [Fintype U] in
theorem conditionOn_expect_of_pos (μ : FiniteLaw Ω) (u : Ω → U)
    (a : U) (ha : 0 < μ.fibreMass u a) (c : Ω → ℝ) :
    (μ.conditionOn u a).expect c = μ.conditionalMean u c a := by
  unfold conditionalMean
  apply (eq_div_iff ha.ne').2
  rw [mul_comm]
  exact μ.mass_mul_conditionOn_expect u a c

/-- Every function of the conditional mean has the correct weighted average. -/
theorem conditionOn_mean_tower (μ : FiniteLaw Ω) (u : Ω → U) (c : Ω → ℝ) (F : ℝ → ℝ) :
    (μ.map u).expect (fun a => F ((μ.conditionOn u a).expect c)) =
      (μ.map u).expect (fun a => F (μ.conditionalMean u c a)) := by
  apply Finset.sum_congr rfl
  intro a _
  change μ.fibreMass u a * F ((μ.conditionOn u a).expect c) =
    μ.fibreMass u a * F (μ.conditionalMean u c a)
  by_cases ha : 0 < μ.fibreMass u a
  · rw [μ.conditionOn_expect_of_pos u a ha c]
  · have hz : μ.fibreMass u a = 0 := le_antisymm (le_of_not_gt ha) (μ.fibreMass_nonneg u a)
    simp [hz]

theorem conditionOn_quadraticEntropy_tower (μ : FiniteLaw Ω) (u : Ω → U) (c : Ω → ℝ) :
    (μ.map u).expect (fun a => quadraticEntropy ((μ.conditionOn u a).expect c)) =
      μ.conditionalQuadraticEntropy u c :=
  μ.conditionOn_mean_tower u c quadraticEntropy

theorem conditionOn_shannonEntropy_tower (μ : FiniteLaw Ω) (u : Ω → U) (c : Ω → ℝ) :
    (μ.map u).expect (fun a => entropyBits ((μ.conditionOn u a).expect c)) =
      μ.conditionalShannonEntropy u c :=
  μ.conditionOn_mean_tower u c entropyBits

/-- Conditional Shannon information, evaluated in the actual conditional laws. -/
def conditionalShannonInformation {Z : Type*} [Fintype Z] [DecidableEq Z]
    (μ : FiniteLaw Ω) (c : Ω → ℝ) (z : Ω → Z) (u : Ω → U) : ℝ :=
  (μ.map u).expect (fun a => (μ.conditionOn u a).shannonInformation c z)

/-- The first bit is unbiased and independent of the observation.  In probabilities,
this is `P(B=1, U=a) = P(U=a)/2` for every `a`. -/
def independentUnbiasedBit (μ : FiniteLaw Ω) (b : Ω → Bool) (u : Ω → U) : Prop :=
  ∀ a, μ.fibreMoment u (fun ω => bitValue (b ω)) a = μ.fibreMass u a / 2

theorem mean_of_independentUnbiasedBit (μ : FiniteLaw Ω) (b : Ω → Bool) (u : Ω → U)
    (hbu : μ.independentUnbiasedBit b u) :
    μ.expect (fun ω => bitValue (b ω)) = 1 / 2 := by
  calc
    _ = ∑ a, μ.fibreMoment u (fun ω => bitValue (b ω)) a :=
      (μ.fibreMoment_sum u _).symm
    _ = ∑ a, μ.fibreMass u a / 2 := Finset.sum_congr rfl (fun a _ => hbu a)
    _ = 1 / 2 := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, μ.fibreMass_sum u]

theorem conditionOn_mean_of_independentUnbiasedBit (μ : FiniteLaw Ω)
    (b : Ω → Bool) (u : Ω → U) (hbu : μ.independentUnbiasedBit b u) (a : U) :
    (μ.conditionOn u a).expect (fun ω => bitValue (b ω)) = 1 / 2 := by
  by_cases ha : 0 < μ.fibreMass u a
  · rw [μ.conditionOn_expect_of_pos u a ha]
    unfold conditionalMean
    rw [hbu a]
    field_simp [ha.ne']
    ring
  · simp only [conditionOn, dif_neg ha]
    exact μ.mean_of_independentUnbiasedBit b u hbu

/-- Manuscript Lemma `conditioning-gain`, directly for an arbitrary finite joint law.

Every term is defined from `μ`, `b`, `c`, and `u`.  No separately supplied
conditional laws, entropy identities, or information inequalities occur among
the assumptions.  The numerator is exactly `T(C; B) T(C; U)`.
-/
theorem conditioning_gain_joint (μ : FiniteLaw Ω) (b c : Ω → Bool) (u : Ω → U)
    (hbu : μ.independentUnbiasedBit b u)
    (hv : 0 < μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω))) :
    μ.conditionalShannonInformation (fun ω => bitValue (b ω)) c u -
        μ.shannonInformation (fun ω => bitValue (b ω)) c ≥
      μ.quadraticInformation (fun ω => bitValue (c ω)) b *
        μ.quadraticInformation (fun ω => bitValue (c ω)) u /
        (2 * Real.log 2 * quadraticEntropy (μ.expect (fun ω => bitValue (c ω))) *
          μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω))) := by
  have h := (μ.map u).conditioning_gain (μ.conditionOn u) b c
    (fun a => μ.conditionOn_mean_of_independentUnbiasedBit b u hbu a)
    (by rw [μ.conditionOn_quadraticEntropy_tower]; exact hv)
  rw [μ.mixture_conditionOn u, μ.conditionOn_quadraticEntropy_tower] at h
  exact h

end FiniteLaw
end CourtadeKumar
