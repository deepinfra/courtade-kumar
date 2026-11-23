import CK.FiniteProbability

/-!
# The good-coordinate lemma

This is the finite-law form of manuscript Lemma `lem:good-coordinate`.
It applies to any independent pair of unbiased bits and any `[0,1]`-valued
conditional success probability.  In particular it does not assume that the
output bit is unbiased or determined by these two coordinates.
-/

noncomputable section
namespace CourtadeKumar

open scoped BigOperators

/-- The exact four-cell calculation underlying the manuscript's good-coordinate proof. -/
theorem four_cell_abs_bound (p00 p01 p10 p11 : ℝ)
    (h00 : 0 ≤ p00 ∧ p00 ≤ 1 / 4) (h01 : 0 ≤ p01 ∧ p01 ≤ 1 / 4)
    (h10 : 0 ≤ p10 ∧ p10 ≤ 1 / 4) (h11 : 0 ≤ p11 ∧ p11 ≤ 1 / 4) :
    |2 * (p10 + p11 - p00 - p01)| +
      |2 * (p01 + p11 - p00 - p10)| ≤ 1 := by
  let x := 2 * (p10 + p11 - p00 - p01)
  let y := 2 * (p01 + p11 - p00 - p10)
  change |x| + |y| ≤ 1
  have hpp : x + y ≤ 1 := by dsimp [x, y]; linarith
  have hpm : x - y ≤ 1 := by dsimp [x, y]; linarith
  have hmp : -x + y ≤ 1 := by dsimp [x, y]; linarith
  have hmm : -x - y ≤ 1 := by dsimp [x, y]; linarith
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · simpa [abs_of_nonneg hx, abs_of_nonneg hy] using hpp
  · simpa [abs_of_nonneg hx, abs_of_nonpos hy, sub_eq_add_neg] using hpm
  · simpa [abs_of_nonpos hx, abs_of_nonneg hy] using hmp
  · simpa [abs_of_nonpos hx, abs_of_nonpos hy, sub_eq_add_neg] using hmm

theorem square_small_of_abs_le_half {x : ℝ} (hx : |x| ≤ 1 / 2) : x ^ 2 ≤ 1 / 4 := by
  have ha : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_pos (by norm_num)
  have h : x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := sq_le_sq.mpr (by rw [ha]; exact hx)
  norm_num at h
  exact h

/-- Among two independent uniform coordinates one squared correlation is at most `1/4`. -/
theorem four_cell_good_coordinate (p00 p01 p10 p11 : ℝ)
    (h00 : 0 ≤ p00 ∧ p00 ≤ 1 / 4) (h01 : 0 ≤ p01 ∧ p01 ≤ 1 / 4)
    (h10 : 0 ≤ p10 ∧ p10 ≤ 1 / 4) (h11 : 0 ≤ p11 ∧ p11 ≤ 1 / 4) :
    (2 * (p10 + p11 - p00 - p01)) ^ 2 ≤ 1 / 4 ∨
      (2 * (p01 + p11 - p00 - p10)) ^ 2 ≤ 1 / 4 := by
  have h := four_cell_abs_bound p00 p01 p10 p11 h00 h01 h10 h11
  by_cases hx : |2 * (p10 + p11 - p00 - p01)| ≤ 1 / 2
  · exact Or.inl (square_small_of_abs_le_half hx)
  · exact Or.inr (square_small_of_abs_le_half (by linarith))

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem binary_quadraticInformation (μ : FiniteLaw Ω) (b : Ω → Bool) (c : Ω → ℝ)
    (hb : ∀ s, μ.fibreMass b s = 1 / 2) :
    μ.quadraticInformation c b =
      (2 * (μ.fibreMoment b c true - μ.fibreMoment b c false)) ^ 2 := by
  have hm := μ.fibreMoment_sum b c
  simp only [Fintype.sum_bool] at hm
  unfold expect at hm
  unfold quadraticInformation conditionalQuadraticEntropy expect map conditionalMean
  simp only [Fintype.sum_bool, hb]
  rw [← hm]
  unfold quadraticEntropy
  ring

/-- The real-valued indicator of a Boolean random variable. -/
def bitValue (b : Bool) : ℝ := if b then 1 else 0

theorem bitValue_nonneg (b : Bool) : 0 ≤ bitValue b := by cases b <;> norm_num [bitValue]

theorem bitValue_le_one (b : Bool) : bitValue b ≤ 1 := by cases b <;> norm_num [bitValue]

/-- Probability that two Boolean random variables agree. -/
def agreementMass (μ : FiniteLaw Ω) (b c : Ω → Bool) : ℝ :=
  ∑ ω, if b ω = c ω then μ.mass ω else 0

theorem binary_moment_difference (μ : FiniteLaw Ω) (b c : Ω → Bool) :
    μ.fibreMoment b (fun ω => bitValue (c ω)) true -
        μ.fibreMoment b (fun ω => bitValue (c ω)) false =
      μ.agreementMass b c - μ.fibreMass b false := by
  unfold fibreMoment agreementMass fibreMass
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  cases hb : b ω <;> cases hc : c ω <;> simp [bitValue, hb, hc]

/-- Manuscript Lemma `tsallis-properties`, unbiased-bit correlation identity. -/
theorem quadraticInformation_eq_agreement (μ : FiniteLaw Ω) (b c : Ω → Bool)
    (hb : ∀ s, μ.fibreMass b s = 1 / 2) :
    μ.quadraticInformation (fun ω => bitValue (c ω)) b =
      (2 * μ.agreementMass b c - 1) ^ 2 := by
  rw [μ.binary_quadraticInformation b _ hb, μ.binary_moment_difference b c, hb false]
  ring

theorem expect_bitValue (μ : FiniteLaw Ω) (b : Ω → Bool) :
    μ.expect (fun ω => bitValue (b ω)) = μ.fibreMass b true := by
  unfold expect fibreMass
  apply Finset.sum_congr rfl
  intro ω _
  cases hb : b ω <;> simp [bitValue, hb]

theorem expect_bitValue_mul (μ : FiniteLaw Ω) (b : Ω → Bool) (c : Ω → ℝ) :
    μ.expect (fun ω => bitValue (b ω) * c ω) = μ.fibreMoment b c true := by
  unfold expect fibreMoment
  apply Finset.sum_congr rfl
  intro ω _
  cases hb : b ω <;> simp [bitValue, hb]

/-- A division-safe form of the binary conditional-variance calculation.

Zero-probability outcomes are covered by the bounds on the two fibre moments.
-/
theorem binary_weighted_variance (p0 p1 m0 m1 : ℝ) (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1)
    (hp : p0 + p1 = 1) (hm0 : 0 ≤ m0 ∧ m0 ≤ p0) (hm1 : 0 ≤ m1 ∧ m1 ≤ p1) :
    quadraticEntropy p1 *
      (quadraticEntropy (m0 + m1) -
        (p0 * quadraticEntropy (m0 / p0) + p1 * quadraticEntropy (m1 / p1))) =
      16 * (m1 - p1 * (m0 + m1)) ^ 2 := by
  by_cases h0 : p0 = 0
  · have hm : m0 = 0 := by linarith
    have h1 : p1 = 1 := by linarith
    simp [h0, hm, h1, quadraticEntropy]
  by_cases h1 : p1 = 0
  · have hm : m1 = 0 := by linarith
    simp [h1, hm, quadraticEntropy]
  have hp' : p0 = 1 - p1 := by linarith
  unfold quadraticEntropy
  field_simp [h0, h1]
  rw [hp']
  ring

/-- Quadratic information times the entropy of the observed bit is sixteen times
the squared covariance.  This also covers constant observed bits. -/
theorem binary_quadratic_covariance (μ : FiniteLaw Ω) (b : Ω → Bool) (c : Ω → ℝ)
    (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1) :
    quadraticEntropy (μ.expect (fun ω => bitValue (b ω))) *
      μ.quadraticInformation c b =
      16 * (μ.expect (fun ω => bitValue (b ω) * c ω) -
        μ.expect (fun ω => bitValue (b ω)) * μ.expect c) ^ 2 := by
  have hp := μ.fibreMass_sum b
  have hm := μ.fibreMoment_sum b c
  simp only [Fintype.sum_bool] at hp hm
  unfold expect at hm
  have h := binary_weighted_variance
    (μ.fibreMass b false) (μ.fibreMass b true)
    (μ.fibreMoment b c false) (μ.fibreMoment b c true)
    (μ.fibreMass_nonneg b false) (μ.fibreMass_nonneg b true)
    (by linarith)
    ⟨μ.fibreMoment_nonneg b hc0 false, μ.fibreMoment_le_mass b hc1 false⟩
    ⟨μ.fibreMoment_nonneg b hc0 true, μ.fibreMoment_le_mass b hc1 true⟩
  simp_rw [μ.expect_bitValue b, μ.expect_bitValue_mul b c]
  unfold quadraticInformation conditionalQuadraticEntropy expect map conditionalMean
  simp only [Fintype.sum_bool]
  convert h using 1
  all_goals
    rw [← hm]
    try unfold quadraticEntropy
    ring

/-- Manuscript Lemma `tsallis-properties`, the exact asymmetry identity for two bits. -/
theorem binary_quadratic_symmetry (μ : FiniteLaw Ω) (b c : Ω → Bool) :
    quadraticEntropy (μ.expect (fun ω => bitValue (c ω))) *
        μ.quadraticInformation (fun ω => bitValue (b ω)) c =
      quadraticEntropy (μ.expect (fun ω => bitValue (b ω))) *
        μ.quadraticInformation (fun ω => bitValue (c ω)) b := by
  rw [μ.binary_quadratic_covariance c _ (fun ω => bitValue_nonneg (b ω))
      (fun ω => bitValue_le_one (b ω)),
    μ.binary_quadratic_covariance b _ (fun ω => bitValue_nonneg (c ω))
      (fun ω => bitValue_le_one (c ω))]
  simp only [mul_comm]

theorem fibreMass_first_pair (μ : FiniteLaw Ω) (a b : Ω → Bool) (s : Bool) :
    μ.fibreMass a s = μ.fibreMass (fun ω => (a ω, b ω)) (s, false) +
      μ.fibreMass (fun ω => (a ω, b ω)) (s, true) := by
  unfold fibreMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ha : a ω = s <;> cases hb : b ω <;> simp [ha, hb]

theorem fibreMass_second_pair (μ : FiniteLaw Ω) (a b : Ω → Bool) (t : Bool) :
    μ.fibreMass b t = μ.fibreMass (fun ω => (a ω, b ω)) (false, t) +
      μ.fibreMass (fun ω => (a ω, b ω)) (true, t) := by
  unfold fibreMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hb : b ω = t <;> cases ha : a ω <;> simp [ha, hb]

theorem fibreMoment_first_pair (μ : FiniteLaw Ω) (a b : Ω → Bool) (c : Ω → ℝ)
    (s : Bool) :
    μ.fibreMoment a c s = μ.fibreMoment (fun ω => (a ω, b ω)) c (s, false) +
      μ.fibreMoment (fun ω => (a ω, b ω)) c (s, true) := by
  unfold fibreMoment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ha : a ω = s <;> cases hb : b ω <;> simp [ha, hb]

theorem fibreMoment_second_pair (μ : FiniteLaw Ω) (a b : Ω → Bool) (c : Ω → ℝ)
    (t : Bool) :
    μ.fibreMoment b c t = μ.fibreMoment (fun ω => (a ω, b ω)) c (false, t) +
      μ.fibreMoment (fun ω => (a ω, b ω)) c (true, t) := by
  unfold fibreMoment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hb : b ω = t <;> cases ha : a ω <;> simp [ha, hb]

/-- The manuscript's good-coordinate lemma for an arbitrary finite sample space.

The four probabilities `1/4` say exactly that `a` and `b` are independent
unbiased bits.  The output `c` may depend on all of `Ω`, and may be randomized.
-/
theorem good_coordinate_of_uniform_pair (μ : FiniteLaw Ω) (a b : Ω → Bool)
    (c : Ω → ℝ) (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1)
    (hab : ∀ s t, μ.fibreMass (fun ω => (a ω, b ω)) (s, t) = 1 / 4) :
    μ.quadraticInformation c a ≤ 1 / 4 ∨ μ.quadraticInformation c b ≤ 1 / 4 := by
  have ha : ∀ s, μ.fibreMass a s = 1 / 2 := by
    intro s
    rw [μ.fibreMass_first_pair a b s, hab, hab]
    norm_num
  have hb : ∀ t, μ.fibreMass b t = 1 / 2 := by
    intro t
    rw [μ.fibreMass_second_pair a b t, hab, hab]
    norm_num
  have hp (s t : Bool) :
      0 ≤ μ.fibreMoment (fun ω => (a ω, b ω)) c (s, t) ∧
      μ.fibreMoment (fun ω => (a ω, b ω)) c (s, t) ≤ 1 / 4 := by
    constructor
    · exact μ.fibreMoment_nonneg _ hc0 _
    · simpa [hab] using μ.fibreMoment_le_mass (fun ω => (a ω, b ω)) hc1 (s, t)
  rw [μ.binary_quadraticInformation a c ha, μ.binary_quadraticInformation b c hb,
    μ.fibreMoment_first_pair a b c true, μ.fibreMoment_first_pair a b c false,
    μ.fibreMoment_second_pair a b c true, μ.fibreMoment_second_pair a b c false]
  simp only [sub_add_eq_sub_sub]
  exact four_cell_good_coordinate
    (μ.fibreMoment (fun ω => (a ω, b ω)) c (false, false))
    (μ.fibreMoment (fun ω => (a ω, b ω)) c (false, true))
    (μ.fibreMoment (fun ω => (a ω, b ω)) c (true, false))
    (μ.fibreMoment (fun ω => (a ω, b ω)) c (true, true))
    (hp false false) (hp false true) (hp true false) (hp true true)

/-- The paper's existential coordinate conclusion for pairwise independent uniform inputs.

This isolates the only probabilistic property of the cube used in the argument.
-/
theorem exists_good_coordinate {n : ℕ} (hn : 2 ≤ n) (μ : FiniteLaw Ω)
    (y : Fin n → Ω → Bool) (c : Ω → ℝ)
    (hc0 : ∀ ω, 0 ≤ c ω) (hc1 : ∀ ω, c ω ≤ 1)
    (hy : ∀ (i j : Fin n), i ≠ j → ∀ s t,
      μ.fibreMass (fun ω => (y i ω, y j ω)) (s, t) = 1 / 4) :
    ∃ i : Fin n, μ.quadraticInformation c (y i) ≤ 1 / 4 := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  rcases μ.good_coordinate_of_uniform_pair (y i) (y j) c hc0 hc1 (hy i j hij) with h | h
  · exact ⟨i, h⟩
  · exact ⟨j, h⟩

end FiniteLaw
end CourtadeKumar
