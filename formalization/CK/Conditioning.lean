import CK.GoodCoordinate

/-!
# Conditioning increases quadratic information

This is manuscript Lemma `tsallis-properties`, part `tsallis-conditioning`,
for finite conditional laws.  `ν` is the law of the observed variable `U`,
and `μ u` is the law of the underlying sample conditional on `U = u`.
Their marginal law is the explicitly defined mixture `ν.mixture μ`.

Independence of `B` and `U` is expressed by the same success probability for
`B` under every component law.  Components of zero `ν` mass are harmless.
-/

noncomputable section
namespace CourtadeKumar
namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- Covariance of two Boolean random variables under a finite law. -/
def bitCovariance (μ : FiniteLaw Ω) (b c : Ω → Bool) : ℝ :=
  μ.expect (fun ω => bitValue (b ω) * bitValue (c ω)) -
    μ.expect (fun ω => bitValue (b ω)) * μ.expect (fun ω => bitValue (c ω))

theorem bitCovariance_symm (μ : FiniteLaw Ω) (b c : Ω → Bool) :
    μ.bitCovariance b c = μ.bitCovariance c b := by
  unfold bitCovariance
  simp only [mul_comm]

theorem binary_covariance_identity (μ : FiniteLaw Ω) (b c : Ω → Bool) :
    quadraticEntropy (μ.expect (fun ω => bitValue (b ω))) *
      μ.quadraticInformation (fun ω => bitValue (c ω)) b =
      16 * (μ.bitCovariance b c) ^ 2 :=
  μ.binary_quadratic_covariance b _ (fun ω => bitValue_nonneg (c ω))
    (fun ω => bitValue_le_one (c ω))

theorem bit_entropy_nonneg (μ : FiniteLaw Ω) (c : Ω → Bool) :
    0 ≤ quadraticEntropy (μ.expect (fun ω => bitValue (c ω))) :=
  quadraticEntropy_nonneg (μ.expect_nonneg fun ω => bitValue_nonneg (c ω))
    (μ.expect_le_one fun ω => bitValue_le_one (c ω))

theorem bitCovariance_eq_zero_of_entropy_eq_zero (μ : FiniteLaw Ω) (b c : Ω → Bool)
    (hc : quadraticEntropy (μ.expect (fun ω => bitValue (c ω))) = 0) :
    μ.bitCovariance b c = 0 := by
  have h := μ.binary_covariance_identity c b
  rw [hc, zero_mul, μ.bitCovariance_symm c b] at h
  have hs : (μ.bitCovariance b c) ^ 2 = 0 := by linarith
  exact sq_eq_zero_iff.mp hs

/-- Zero-safe division of the covariance identity. -/
theorem covariance_div_le_information (μ : FiniteLaw Ω) (b c : Ω → Bool) :
    16 * ((μ.bitCovariance b c) ^ 2 /
      quadraticEntropy (μ.expect (fun ω => bitValue (c ω)))) ≤
      μ.quadraticInformation (fun ω => bitValue (b ω)) c := by
  have h := μ.binary_covariance_identity c b
  rw [μ.bitCovariance_symm c b] at h
  by_cases hc : quadraticEntropy (μ.expect (fun ω => bitValue (c ω))) = 0
  · simp only [hc, div_zero, mul_zero]
    exact μ.quadraticInformation_nonneg c (fun ω => bitValue_nonneg (b ω))
      (fun ω => bitValue_le_one (b ω))
  · have he : 16 * ((μ.bitCovariance b c) ^ 2 /
        quadraticEntropy (μ.expect (fun ω => bitValue (c ω)))) =
        μ.quadraticInformation (fun ω => bitValue (b ω)) c := by
      rw [← mul_div_assoc]
      apply (div_eq_iff hc).2
      nlinarith
    exact le_of_eq he

variable {U : Type*} [Fintype U]

/-- Covariance commutes with a mixture when the first bit's conditional mean is fixed. -/
theorem bitCovariance_mixture (ν : FiniteLaw U) (μ : U → FiniteLaw Ω)
    (b c : Ω → Bool) (β : ℝ)
    (hb : ∀ u, (μ u).expect (fun ω => bitValue (b ω)) = β) :
    (ν.mixture μ).bitCovariance b c = ν.expect (fun u => (μ u).bitCovariance b c) := by
  unfold bitCovariance
  simp_rw [ν.expect_mixture μ, hb]
  rw [ν.expect_const, ν.expect_sub, ν.expect_const_mul]

/-- The finite-mixture form of the paper's quadratic conditioning inequality.

The left factor is `T(B; C | U)`, the right factor is `T(C | U)`, and
the right-hand side is `T(B) T(C; B)` under the marginal law.
-/
theorem quadratic_conditioning (ν : FiniteLaw U) (μ : U → FiniteLaw Ω)
    (b c : Ω → Bool) (β : ℝ)
    (hb : ∀ u, (μ u).expect (fun ω => bitValue (b ω)) = β) :
    ν.expect (fun u => (μ u).quadraticInformation (fun ω => bitValue (b ω)) c) *
        ν.expect (fun u => quadraticEntropy ((μ u).expect (fun ω => bitValue (c ω)))) ≥
      quadraticEntropy ((ν.mixture μ).expect (fun ω => bitValue (b ω))) *
        (ν.mixture μ).quadraticInformation (fun ω => bitValue (c ω)) b := by
  let r : U → ℝ := fun u => (μ u).bitCovariance b c
  let v : U → ℝ := fun u => quadraticEntropy ((μ u).expect (fun ω => bitValue (c ω)))
  have hv : ∀ u, 0 ≤ v u := fun u => (μ u).bit_entropy_nonneg c
  have hz : ∀ u, v u = 0 → r u = 0 := fun u h =>
    (μ u).bitCovariance_eq_zero_of_entropy_eq_zero b c h
  have hcs := ν.cauchy_div r v hv hz
  have hi : 16 * ν.expect (fun u => r u ^ 2 / v u) ≤
      ν.expect (fun u => (μ u).quadraticInformation (fun ω => bitValue (b ω)) c) := by
    rw [← ν.expect_const_mul]
    exact ν.expect_mono fun u => (μ u).covariance_div_le_information b c
  have hv' : 0 ≤ ν.expect v := ν.expect_nonneg hv
  have hi' := mul_le_mul_of_nonneg_right hi hv'
  rw [(ν.mixture μ).binary_covariance_identity b c,
    ν.bitCovariance_mixture μ b c β hb]
  change 16 * (ν.expect r) ^ 2 ≤ _
  nlinarith

end FiniteLaw
end CourtadeKumar
