import CK.ComparisonAveraging
import CK.Markov

/-! Actual finite-law semantics for the binary profiles in the comparison lemma. -/

noncomputable section
namespace CourtadeKumar

namespace Spec

theorem binaryProfile_even_correlation (x d : ℝ) : binaryProfile x (-d) = binaryProfile x d := by
  simp [binaryProfile, neg_div]

theorem binaryProfile_abs_channel (x γ d : ℝ) :
    binaryProfile x (γ * d) = binaryProfile x (|γ| * d) := by
  rcases le_total 0 γ with hγ | hγ
  · rw [abs_of_nonneg hγ]
  · rw [abs_of_nonpos hγ, neg_mul, binaryProfile_even_correlation]

end Spec

namespace FiniteLaw
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

def bitBias (μ : FiniteLaw Ω) (c : Ω → Bool) : ℝ :=
  2 * μ.expect (fun ω => bitValue (c ω)) - 1

def bitCorrelation (μ : FiniteLaw Ω) (b c : Ω → Bool) : ℝ :=
  μ.expect (fun ω => (2 * bitValue (b ω) - 1) * (2 * bitValue (c ω) - 1))

theorem bitCorrelation_symm (μ : FiniteLaw Ω) (b c : Ω → Bool) :
    μ.bitCorrelation b c = μ.bitCorrelation c b := by
  simp only [bitCorrelation, mul_comm]

theorem bitCorrelation_expand (μ : FiniteLaw Ω) (b c : Ω → Bool) :
    μ.bitCorrelation b c = 4 * μ.expect (fun ω => bitValue (b ω) * bitValue (c ω)) -
      2 * μ.expect (fun ω => bitValue (b ω)) -
      2 * μ.expect (fun ω => bitValue (c ω)) + 1 := by
  have he : (fun ω => (2 * bitValue (b ω) - 1) * (2 * bitValue (c ω) - 1)) =
      (fun ω => 4 * (bitValue (b ω) * bitValue (c ω)) -
        2 * bitValue (b ω) - 2 * bitValue (c ω) + 1) := by
    funext ω
    ring
  rw [bitCorrelation, he, μ.expect_add, μ.expect_sub, μ.expect_sub,
    μ.expect_const_mul, μ.expect_const_mul, μ.expect_const_mul, μ.expect_const]

theorem bitCorrelation_unbiased (μ : FiniteLaw Ω) (b c : Ω → Bool)
    (hb : μ.expect (fun ω => bitValue (b ω)) = 1 / 2) :
    μ.bitCorrelation b c =
      4 * μ.expect (fun ω => bitValue (b ω) * bitValue (c ω)) -
        2 * μ.expect (fun ω => bitValue (c ω)) := by
  rw [μ.bitCorrelation_expand, hb]
  ring

theorem bitCorrelation_mixture {U : Type*} [Fintype U]
    (ν : FiniteLaw U) (μ : U → FiniteLaw Ω) (b c : Ω → Bool) :
    (ν.mixture μ).bitCorrelation b c = ν.expect (fun u => (μ u).bitCorrelation b c) :=
  ν.expect_mixture μ _

theorem fibreMass_of_unbiased (μ : FiniteLaw Ω) (b : Ω → Bool)
    (hb : μ.expect (fun ω => bitValue (b ω)) = 1 / 2) (s : Bool) :
    μ.fibreMass b s = 1 / 2 := by
  have hbt := μ.expect_bitValue b
  have hbs := μ.fibreMass_sum b
  simp only [Fintype.sum_bool] at hbs
  cases s <;> linarith

theorem bitCorrelation_eq_moment_difference (μ : FiniteLaw Ω) (b c : Ω → Bool)
    (hb : μ.expect (fun ω => bitValue (b ω)) = 1 / 2) :
    μ.bitCorrelation b c = 2 * (μ.fibreMoment b (fun ω => bitValue (c ω)) true -
      μ.fibreMoment b (fun ω => bitValue (c ω)) false) := by
  rw [μ.bitCorrelation_unbiased b c hb, μ.expect_bitValue_mul]
  have h := μ.fibreMoment_sum b (fun ω => bitValue (c ω))
  simp only [Fintype.sum_bool] at h
  linarith

theorem binaryProfile_parameters_domain (μ : FiniteLaw Ω) (b c : Ω → Bool)
    (hb : μ.expect (fun ω => bitValue (b ω)) = 1 / 2) :
    |μ.bitBias c| + |μ.bitCorrelation b c| ≤ 1 := by
  have hm0 := μ.fibreMoment_nonneg b (fun ω => bitValue_nonneg (c ω)) false
  have hm1 := μ.fibreMoment_nonneg b (fun ω => bitValue_nonneg (c ω)) true
  have hm0' := μ.fibreMoment_le_mass b (fun ω => bitValue_le_one (c ω)) false
  have hm1' := μ.fibreMoment_le_mass b (fun ω => bitValue_le_one (c ω)) true
  rw [μ.fibreMass_of_unbiased b hb false] at hm0'
  rw [μ.fibreMass_of_unbiased b hb true] at hm1'
  have hsum := μ.fibreMoment_sum b (fun ω => bitValue (c ω))
  simp only [Fintype.sum_bool] at hsum
  rw [μ.bitCorrelation_eq_moment_difference b c hb]
  unfold bitBias
  rw [← hsum]
  rcases le_total 0 (2 * (μ.fibreMoment b (fun ω => bitValue (c ω)) true +
      μ.fibreMoment b (fun ω => bitValue (c ω)) false) - 1) with hx | hx <;>
    rcases le_total 0 (2 * (μ.fibreMoment b (fun ω => bitValue (c ω)) true -
      μ.fibreMoment b (fun ω => bitValue (c ω)) false)) with hd | hd
  · rw [abs_of_nonneg hx, abs_of_nonneg hd]; linarith
  · rw [abs_of_nonneg hx, abs_of_nonpos hd]; linarith
  · rw [abs_of_nonpos hx, abs_of_nonneg hd]; linarith
  · rw [abs_of_nonpos hx, abs_of_nonpos hd]; linarith

theorem unbiased_profile_information_algebra (q r : ℝ)
    (hr0 : 0 ≤ r) (hrq : r ≤ q) (hrem0 : 0 ≤ 1 / 2 - r)
    (hremq : 1 / 2 - r ≤ 1 - q) :
    1 - (q * entropyBits (r / q) + (1 - q) * entropyBits ((1 / 2 - r) / (1 - q))) =
      Spec.binaryProfile (2 * q - 1) (4 * r - 2 * q) := by
  by_cases hq0 : q = 0
  · have hr : r = 0 := by linarith
    simp [hq0, hr, ← one_div]
  by_cases hq1 : 1 - q = 0
  · have hq : q = 1 := by linarith
    have hr : r = 1 / 2 := by linarith
    norm_num [hq, hr, Spec.binaryProfile_zero_correlation]
  have hp : (1 + (2 * q - 1)) / 2 = q := by ring
  have hm : (1 - (2 * q - 1)) / 2 = 1 - q := by ring
  have hpArg : (1 + (4 * r - 2 * q) / (1 + (2 * q - 1))) / 2 = r / q := by
    have : 1 + (2 * q - 1) = 2 * q := by ring
    rw [this]
    field_simp [hq0]
    ring
  have hmArg : (1 + (4 * r - 2 * q) / (1 - (2 * q - 1))) / 2 =
      1 - (1 / 2 - r) / (1 - q) := by
    have : 1 - (2 * q - 1) = 2 * (1 - q) := by ring
    rw [this]
    field_simp [hq1]
    ring
  unfold Spec.binaryProfile Spec.divergence
  rw [hp, hm, hpArg, hmArg]
  change _ = q * (1 - entropyBits (r / q)) +
    (1 - q) * (1 - entropyBits (1 - (1 / 2 - r) / (1 - q)))
  rw [entropyBits_complement]
  ring

theorem shannonInformation_eq_binaryProfile (μ : FiniteLaw Ω) (b c : Ω → Bool)
    (hb : μ.expect (fun ω => bitValue (b ω)) = 1 / 2) :
    μ.shannonInformation (fun ω => bitValue (b ω)) c =
      Spec.binaryProfile (μ.bitBias c) (μ.bitCorrelation b c) := by
  have hs := μ.fibreMass_sum c
  have hm := μ.fibreMoment_sum c (fun ω => bitValue (b ω))
  simp only [Fintype.sum_bool] at hs hm
  rw [hb] at hm
  have hmass : μ.fibreMass c false = 1 - μ.fibreMass c true := by linarith
  have hmom : μ.fibreMoment c (fun ω => bitValue (b ω)) false =
      1 / 2 - μ.fibreMoment c (fun ω => bitValue (b ω)) true := by linarith
  have hr0 := μ.fibreMoment_nonneg c (fun ω => bitValue_nonneg (b ω)) true
  have hrq := μ.fibreMoment_le_mass c (fun ω => bitValue_le_one (b ω)) true
  have hrem0 := μ.fibreMoment_nonneg c (fun ω => bitValue_nonneg (b ω)) false
  have hremq := μ.fibreMoment_le_mass c (fun ω => bitValue_le_one (b ω)) false
  rw [hmom] at hrem0
  rw [hmom, hmass] at hremq
  have hcalc := unbiased_profile_information_algebra _ _ hr0 hrq hrem0 hremq
  have hjoint : μ.expect (fun ω => bitValue (b ω) * bitValue (c ω)) =
      μ.fibreMoment c (fun ω => bitValue (b ω)) true := by
    simp_rw [mul_comm (bitValue (b _)) (bitValue (c _))]
    exact μ.expect_bitValue_mul c _
  rw [bitBias, μ.bitCorrelation_unbiased b c hb, hjoint, μ.expect_bitValue c]
  rw [← hcalc]
  unfold shannonInformation
  rw [hb, entropyBits_half]
  unfold conditionalShannonEntropy expect map conditionalMean
  simp only [Fintype.sum_bool, hmom, hmass]

theorem quadraticEntropy_eq_bitBias (μ : FiniteLaw Ω) (c : Ω → Bool) :
    quadraticEntropy (μ.expect (fun ω => bitValue (c ω))) = 1 - (μ.bitBias c) ^ 2 :=
  quadraticEntropy_eq_one_sub_sq _

theorem quadraticInformation_eq_bitCorrelation (μ : FiniteLaw Ω) (b c : Ω → Bool)
    (hb : μ.expect (fun ω => bitValue (b ω)) = 1 / 2) :
    μ.quadraticInformation (fun ω => bitValue (c ω)) b = (μ.bitCorrelation b c) ^ 2 := by
  rw [μ.binary_quadraticInformation b _ (μ.fibreMass_of_unbiased b hb),
    μ.bitCorrelation_eq_moment_difference b c hb]

theorem bitCorrelation_markov (μ : FiniteLaw Ω) (a b c : Ω → Bool)
    (ha : μ.expect (fun ω => bitValue (a ω)) = 1 / 2)
    (hb : μ.expect (fun ω => bitValue (b ω)) = 1 / 2)
    (hmark : μ.conditionallyIndependentBit c a b) :
    μ.bitCorrelation a c = μ.bitCorrelation a b * μ.bitCorrelation b c := by
  have h0 := hmark false true
  have h1 := hmark true true
  rw [μ.fibreMass_of_unbiased b hb false, ← μ.fibreMoment_bit_eq_pair b a false] at h0
  rw [μ.fibreMass_of_unbiased b hb true, ← μ.fibreMoment_bit_eq_pair b a true] at h1
  have hsum := μ.fibreMoment_second_pair b a (fun ω => bitValue (c ω)) true
  have hAsum := μ.fibreMoment_sum b (fun ω => bitValue (a ω))
  have hCsum := μ.fibreMoment_sum b (fun ω => bitValue (c ω))
  simp only [Fintype.sum_bool] at hAsum hCsum
  rw [ha] at hAsum
  rw [μ.bitCorrelation_unbiased a c ha, μ.bitCorrelation_symm a b,
    μ.bitCorrelation_unbiased b a hb, μ.bitCorrelation_unbiased b c hb,
    μ.expect_bitValue_mul a _, μ.expect_bitValue_mul b _, μ.expect_bitValue_mul b _, ha]
  have hA0 : μ.fibreMoment b (fun ω => bitValue (a ω)) false =
      1 / 2 - μ.fibreMoment b (fun ω => bitValue (a ω)) true := by linarith
  have hC0 : μ.fibreMoment b (fun ω => bitValue (c ω)) false =
      μ.expect (fun ω => bitValue (c ω)) -
        μ.fibreMoment b (fun ω => bitValue (c ω)) true := by linarith
  rw [hA0, hC0] at h0
  nlinarith

theorem shannonInformation_markov_profile (μ : FiniteLaw Ω) (a b c : Ω → Bool)
    (ha : μ.expect (fun ω => bitValue (a ω)) = 1 / 2)
    (hb : μ.expect (fun ω => bitValue (b ω)) = 1 / 2)
    (hmark : μ.conditionallyIndependentBit c a b) :
    μ.shannonInformation (fun ω => bitValue (a ω)) c =
      Spec.binaryProfile (μ.bitBias c) (μ.bitCorrelation a b * μ.bitCorrelation b c) := by
  rw [μ.shannonInformation_eq_binaryProfile a c ha, μ.bitCorrelation_markov a b c ha hb hmark]

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem conditionalShannonInformation_eq_binaryProfile (μ : FiniteLaw Ω)
    (b c : Ω → Bool) (u : Ω → U) (hbu : μ.independentUnbiasedBit b u) :
    μ.conditionalShannonInformation (fun ω => bitValue (b ω)) c u =
      (μ.map u).expect (fun a => Spec.binaryProfile ((μ.conditionOn u a).bitBias c)
        ((μ.conditionOn u a).bitCorrelation b c)) := by
  unfold conditionalShannonInformation
  congr 1
  funext a
  exact (μ.conditionOn u a).shannonInformation_eq_binaryProfile b c
    (μ.conditionOn_mean_of_independentUnbiasedBit b u hbu a)

theorem conditionalQuadraticEntropy_eq_bitBias (μ : FiniteLaw Ω)
    (c : Ω → Bool) (u : Ω → U) :
    μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) =
      (μ.map u).expect (fun a => 1 - ((μ.conditionOn u a).bitBias c) ^ 2) := by
  rw [← μ.conditionOn_quadraticEntropy_tower]
  congr 1
  funext a
  exact (μ.conditionOn u a).quadraticEntropy_eq_bitBias c

theorem bitCorrelation_conditionOn_tower (μ : FiniteLaw Ω)
    (b c : Ω → Bool) (u : Ω → U) :
    (μ.map u).expect (fun a => (μ.conditionOn u a).bitCorrelation b c) =
      μ.bitCorrelation b c := by
  rw [← bitCorrelation_mixture, μ.mixture_conditionOn]

/-- The conditional comparison and correlation lemmas for actual finite joint
laws. The channel and Markov assumptions are stated on positive conditional
fibres; null fibres impose no condition. No information inequality is assumed. -/
theorem conditional_comparison (μ : FiniteLaw Ω) (a b c : Ω → Bool) (u : Ω → U)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hau : μ.independentUnbiasedBit a u) (hbu : μ.independentUnbiasedBit b u)
    (hchannel : ∀ s, 0 < μ.fibreMass u s → |(μ.conditionOn u s).bitCorrelation a b| = ρ)
    (hmark : ∀ s, 0 < μ.fibreMass u s →
      (μ.conditionOn u s).conditionallyIndependentBit c a b)
    (hV : 0 < μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω))) :
    ∃ τ ∈ Set.Icc (0 : ℝ) 1,
      μ.conditionalShannonInformation (fun ω => bitValue (b ω)) c u =
        μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) * Spec.divergence τ ∧
      μ.conditionalShannonInformation (fun ω => bitValue (a ω)) c u ≤
        μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) * Spec.divergence (ρ * τ) ∧
      μ.quadraticInformation (fun ω => bitValue (c ω)) b /
        (μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω))) ^ 2 ≤ τ ^ 2 := by
  let x : U → ℝ := fun s => (μ.conditionOn u s).bitBias c
  let d : U → ℝ := fun s => (μ.conditionOn u s).bitCorrelation b c
  have hdom (s : U) : |x s| + |d s| ≤ 1 :=
    (μ.conditionOn u s).binaryProfile_parameters_domain b c
      (μ.conditionOn_mean_of_independentUnbiasedBit b u hbu s)
  have hVeq : (μ.map u).expect (fun s => 1 - x s ^ 2) =
      μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) :=
    (μ.conditionalQuadraticEntropy_eq_bitBias c u).symm
  have hIeq : (μ.map u).expect (fun s => Spec.binaryProfile (x s) (d s)) =
      μ.conditionalShannonInformation (fun ω => bitValue (b ω)) c u :=
    (μ.conditionalShannonInformation_eq_binaryProfile b c u hbu).symm
  have hAeq : μ.conditionalShannonInformation (fun ω => bitValue (a ω)) c u =
      (μ.map u).expect (fun s => Spec.binaryProfile (x s) (ρ * d s)) := by
    unfold conditionalShannonInformation expect
    apply Finset.sum_congr rfl
    intro s _
    change μ.fibreMass u s * (μ.conditionOn u s).shannonInformation
      (fun ω => bitValue (a ω)) c = μ.fibreMass u s * Spec.binaryProfile (x s) (ρ * d s)
    by_cases hs : μ.fibreMass u s = 0
    · simp [hs]
    · have hsp : 0 < μ.fibreMass u s :=
        lt_of_le_of_ne (μ.fibreMass_nonneg u s) (Ne.symm hs)
      rw [(μ.conditionOn u s).shannonInformation_markov_profile a b c
        (μ.conditionOn_mean_of_independentUnbiasedBit a u hau s)
        (μ.conditionOn_mean_of_independentUnbiasedBit b u hbu s) (hmark s hsp),
        Spec.binaryProfile_abs_channel, hchannel s hsp]
  have hdeq : (μ.map u).expect d = μ.bitCorrelation b c :=
    μ.bitCorrelation_conditionOn_tower b c u
  obtain ⟨τ, hτ, hmatch, hupper, hcorr⟩ :=
    (μ.map u).binaryProfile_average_comparison x d hρ0 hρ1 hdom (by rwa [hVeq])
  refine ⟨τ, hτ, ?_, ?_, ?_⟩
  · simpa only [hVeq, hIeq] using hmatch
  · simpa only [hVeq, ← hAeq] using hupper
  · rw [hdeq, hVeq] at hcorr
    rwa [μ.quadraticInformation_eq_bitCorrelation b c
      (μ.mean_of_independentUnbiasedBit b u hbu)]

end FiniteLaw
end CourtadeKumar
