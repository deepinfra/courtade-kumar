import CK.BinaryProfileSemantics
import CK.MapLaws

/-!
# Explicit private-randomness realization of the comparison bit

The original finite law is extended by one independent biased noise bit. The
comparison bit is the XOR of the original input bit with that noise. The
construction preserves the original joint law and has exactly the specified
correlation, Shannon information, and quadratic information.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace CourtadeKumar
namespace FiniteLaw
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- Independent flip-noise law with correlation parameter `τ`. -/
def comparatorNoise (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) : FiniteLaw Bool where
  mass n := if n then (1-τ)/2 else (1+τ)/2
  mass_nonneg n := by cases n <;> simp only [Bool.false_eq_true,if_false,if_true] <;> linarith
  mass_sum := by simp only [Fintype.sum_bool,Bool.false_eq_true,if_false,if_true]; ring

/-- Product extension by one private random bit; it is independent of every original observation. -/
def comparatorExtension (μ : FiniteLaw Ω) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    FiniteLaw (Ω × Bool) where
  mass p := μ.mass p.1*(comparatorNoise τ hτ0 hτ1).mass p.2
  mass_nonneg p := mul_nonneg (μ.mass_nonneg p.1) ((comparatorNoise τ hτ0 hτ1).mass_nonneg p.2)
  mass_sum := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,FiniteLaw.mass_sum,mul_one]
    exact μ.mass_sum

/-- The comparison bit generated from `B` and private flip noise. -/
def comparatorBit (b : Ω → Bool) (p : Ω × Bool) : Bool := Bool.xor (b p.1) p.2

/-- Expectation under the product extension, with the two noise outcomes explicit. -/
theorem expect_comparatorExtension (μ : FiniteLaw Ω) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (f : Ω × Bool → ℝ) :
    (μ.comparatorExtension τ hτ0 hτ1).expect f =
      μ.expect (fun ω => ((1+τ)/2)*f (ω,false)+((1-τ)/2)*f (ω,true)) := by
  unfold expect comparatorExtension comparatorNoise
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [Fintype.sum_bool,Bool.false_eq_true,if_false,if_true]
  ring

/-- The original sample has exactly its original law after adjoining the randomizer. -/
theorem comparatorExtension_expect_fst (μ : FiniteLaw Ω) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (g : Ω → ℝ) :
    (μ.comparatorExtension τ hτ0 hτ1).expect (fun p => g p.1) = μ.expect g := by
  rw [expect_comparatorExtension]
  congr 1
  funext ω
  ring

/-- Private randomness is independent of every original real-valued observation. -/
theorem comparatorExtension_independent_noise (μ : FiniteLaw Ω) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (g : Ω → ℝ) (f : Bool → ℝ) :
    (μ.comparatorExtension τ hτ0 hτ1).expect (fun p => g p.1*f p.2) =
      μ.expect g*(comparatorNoise τ hτ0 hτ1).expect f := by
  rw [expect_comparatorExtension]
  unfold expect comparatorNoise
  simp only [Fintype.sum_bool,Bool.false_eq_true,if_false,if_true]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem comparatorExtension_map_fst (μ : FiniteLaw Ω) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    [DecidableEq Ω] : (μ.comparatorExtension τ hτ0 hτ1).map Prod.fst = μ := by
  apply eq_of_mass_eq
  intro ω
  change (μ.comparatorExtension τ hτ0 hτ1).fibreMass Prod.fst ω = μ.mass ω
  rw [fibreMass_eq_expect,μ.comparatorExtension_expect_fst τ hτ0 hτ1
    (fun ω' => if ω'=ω then 1 else 0)]
  simp [expect]

/-- Exact conditional success probability of the generated comparison bit. -/
def comparatorPosterior (τ : ℝ) (s : Bool) : ℝ := (1-τ)/2+τ*bitValue s

/-- Every original observable can be tested against the exact comparator posterior. -/
theorem comparatorExtension_output_moment (μ : FiniteLaw Ω) (b : Ω → Bool) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (g : Ω → ℝ) :
    (μ.comparatorExtension τ hτ0 hτ1).expect
      (fun p => g p.1*bitValue (comparatorBit b p)) =
    μ.expect (fun ω => g ω*comparatorPosterior τ (b ω)) := by
  rw [expect_comparatorExtension]
  congr 1
  funext ω
  cases hb : b ω <;> simp [comparatorBit,comparatorPosterior,bitValue,hb] <;> ring

theorem comparatorExtension_output_mean (μ : FiniteLaw Ω) (b : Ω → Bool) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (μ.comparatorExtension τ hτ0 hτ1).expect (fun p => bitValue (comparatorBit b p)) =
      (1-τ)/2+τ*μ.expect (fun ω => bitValue (b ω)) := by
  have h := μ.comparatorExtension_output_moment b τ hτ0 hτ1 (fun _ => 1)
  simp only [one_mul] at h
  rw [h]
  unfold comparatorPosterior
  rw [μ.expect_add,μ.expect_const,μ.expect_const_mul]

/-- Unbiased input produces the required unbiased comparison bit. -/
theorem comparatorExtension_output_unbiased (μ : FiniteLaw Ω) (b : Ω → Bool) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hb : μ.expect (fun ω => bitValue (b ω))=1/2) :
    (μ.comparatorExtension τ hτ0 hτ1).expect (fun p => bitValue (comparatorBit b p))=1/2 := by
  rw [μ.comparatorExtension_output_mean b τ hτ0 hτ1,hb]
  ring

/-- The requested correlation is realized exactly, even if the source bit is biased. -/
theorem comparatorExtension_correlation (μ : FiniteLaw Ω) (b : Ω → Bool) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (μ.comparatorExtension τ hτ0 hτ1).bitCorrelation (fun p => b p.1) (comparatorBit b)=τ := by
  unfold bitCorrelation
  rw [expect_comparatorExtension]
  have heq : (fun ω => (1+τ)/2*((2*bitValue (b ω)-1)*
      (2*bitValue (comparatorBit b (ω,false))-1))+
      (1-τ)/2*((2*bitValue (b ω)-1)*
      (2*bitValue (comparatorBit b (ω,true))-1))) = fun _ => τ := by
    funext ω
    cases hb : b ω <;> simp [comparatorBit,bitValue,hb] <;> ring
  rw [heq,expect_const]

private theorem binaryProfile_unbiased (d : ℝ) : Spec.binaryProfile 0 d=Spec.divergence d := by
  norm_num [Spec.binaryProfile]
  ring

/-- Shannon mutual information of the realized unbiased comparator. -/
theorem comparatorExtension_shannonInformation (μ : FiniteLaw Ω) (b : Ω → Bool) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hb : μ.expect (fun ω => bitValue (b ω))=1/2) :
    (μ.comparatorExtension τ hτ0 hτ1).shannonInformation
      (fun p => bitValue (b p.1)) (comparatorBit b)=Spec.divergence τ := by
  have hb' : (μ.comparatorExtension τ hτ0 hτ1).expect (fun p => bitValue (b p.1))=1/2 := by
    rw [μ.comparatorExtension_expect_fst τ hτ0 hτ1 (fun ω => bitValue (b ω)),hb]
  rw [shannonInformation_eq_binaryProfile _ _ _ hb',μ.comparatorExtension_correlation]
  have hc := μ.comparatorExtension_output_unbiased b τ hτ0 hτ1 hb
  simp only [bitBias,hc]
  norm_num
  exact binaryProfile_unbiased τ

/-- Quadratic information is precisely the squared comparator correlation. -/
theorem comparatorExtension_quadraticInformation (μ : FiniteLaw Ω) (b : Ω → Bool) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hb : μ.expect (fun ω => bitValue (b ω))=1/2) :
    (μ.comparatorExtension τ hτ0 hτ1).quadraticInformation
      (fun p => bitValue (comparatorBit b p)) (fun p => b p.1)=τ^2 := by
  rw [quadraticInformation_eq_bitCorrelation _ _ _ ?_,μ.comparatorExtension_correlation]
  rw [μ.comparatorExtension_expect_fst τ hτ0 hτ1 (fun ω => bitValue (b ω)),hb]

private theorem comparatorExtension_fibreMass (μ : FiniteLaw Ω) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) {Z : Type*} [Fintype Z] [DecidableEq Z]
    (z : Ω → Z) (a : Z) :
    (μ.comparatorExtension τ hτ0 hτ1).fibreMass (fun p => z p.1) a=μ.fibreMass z a := by
  rw [fibreMass_eq_expect,μ.comparatorExtension_expect_fst τ hτ0 hτ1
    (fun ω => if z ω=a then 1 else 0),μ.fibreMass_eq_expect]

private theorem comparatorExtension_fibreMoment (μ : FiniteLaw Ω) (b : Ω → Bool) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) {Z : Type*} [Fintype Z] [DecidableEq Z]
    (z : Ω → Z) (a : Z) :
    (μ.comparatorExtension τ hτ0 hτ1).fibreMoment (fun p => z p.1)
      (fun p => bitValue (comparatorBit b p)) a =
    μ.fibreMoment z (fun ω => comparatorPosterior τ (b ω)) a := by
  rw [fibreMoment_eq_expect]
  have heq : (fun p : Ω × Bool => if z p.1=a then bitValue (comparatorBit b p) else 0)=
      (fun p : Ω × Bool => (if z p.1=a then 1 else 0)*bitValue (comparatorBit b p)) := by
    funext p
    split_ifs <;> simp
  rw [heq,μ.comparatorExtension_output_moment b τ hτ0 hτ1
    (fun ω => if z ω=a then 1 else 0),μ.fibreMoment_eq_expect]
  congr 1
  funext ω
  split_ifs <;> simp

private theorem fibreMoment_comparatorPosterior (μ : FiniteLaw Ω) (b : Ω → Bool) (τ : ℝ) (s : Bool) :
    μ.fibreMoment b (fun ω => comparatorPosterior τ (b ω)) s =
      comparatorPosterior τ s*μ.fibreMass b s := by
  unfold fibreMoment fibreMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : b ω=s <;> simp [h] <;> ring

private theorem fibreMoment_comparatorPosterior_pair (μ : FiniteLaw Ω) (b : Ω → Bool) (τ : ℝ)
    {Z : Type*} [Fintype Z] [DecidableEq Z] (z : Ω → Z) (s : Bool) (a : Z) :
    μ.fibreMoment (fun ω => (b ω,z ω)) (fun ω => comparatorPosterior τ (b ω)) (s,a) =
      comparatorPosterior τ s*μ.fibreMass (fun ω => (b ω,z ω)) (s,a) := by
  unfold fibreMoment fibreMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : (b ω,z ω)=(s,a)
  · have hb : b ω=s := congrArg Prod.fst h
    simp [h,hb]
    ring
  · simp [h]

/-- The output depends on every original observation only through the chosen input bit. -/
theorem comparatorExtension_markov (μ : FiniteLaw Ω) (b : Ω → Bool) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) {Z : Type*} [Fintype Z] [DecidableEq Z] (z : Ω → Z) :
    (μ.comparatorExtension τ hτ0 hτ1).conditionallyIndependentBit (comparatorBit b)
      (fun p => z p.1) (fun p => b p.1) := by
  intro s a
  rw [μ.comparatorExtension_fibreMoment b τ hτ0 hτ1 (fun ω => (b ω,z ω)) (s,a),
    μ.comparatorExtension_fibreMass τ hτ0 hτ1 b s,
    μ.comparatorExtension_fibreMoment b τ hτ0 hτ1 b s,
    μ.comparatorExtension_fibreMass τ hτ0 hτ1 (fun ω => (b ω,z ω)) (s,a),
    μ.fibreMoment_comparatorPosterior b τ s,
    μ.fibreMoment_comparatorPosterior_pair b τ z s a]
  ring

/-- Original signed correlations are unchanged on the extended probability space. -/
theorem comparatorExtension_old_correlation (μ : FiniteLaw Ω) (a b : Ω → Bool) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (μ.comparatorExtension τ hτ0 hτ1).bitCorrelation (fun p => a p.1) (fun p => b p.1)=
      μ.bitCorrelation a b := by
  unfold bitCorrelation
  exact μ.comparatorExtension_expect_fst τ hτ0 hτ1
    (fun ω => (2*bitValue (a ω)-1)*(2*bitValue (b ω)-1))

/-- Information from any original unbiased bit is the fixed-channel divergence profile. -/
theorem comparatorExtension_channel_information (μ : FiniteLaw Ω) (a b : Ω → Bool) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (ha : μ.expect (fun ω => bitValue (a ω))=1/2)
    (hb : μ.expect (fun ω => bitValue (b ω))=1/2) :
    (μ.comparatorExtension τ hτ0 hτ1).shannonInformation
      (fun p => bitValue (a p.1)) (comparatorBit b)=
      Spec.divergence (|μ.bitCorrelation a b| * τ) := by
  have ha' : (μ.comparatorExtension τ hτ0 hτ1).expect (fun p => bitValue (a p.1))=1/2 := by
    rw [μ.comparatorExtension_expect_fst τ hτ0 hτ1 (fun ω => bitValue (a ω)),ha]
  have hb' : (μ.comparatorExtension τ hτ0 hτ1).expect (fun p => bitValue (b p.1))=1/2 := by
    rw [μ.comparatorExtension_expect_fst τ hτ0 hτ1 (fun ω => bitValue (b ω)),hb]
  rw [shannonInformation_markov_profile _ _ _ _ ha' hb'
    (μ.comparatorExtension_markov b τ hτ0 hτ1 a),
    μ.comparatorExtension_old_correlation,μ.comparatorExtension_correlation,
    Spec.binaryProfile_abs_channel]
  have hc := μ.comparatorExtension_output_unbiased b τ hτ0 hτ1 hb
  simp only [bitBias,hc]
  norm_num
  exact binaryProfile_unbiased _

/-- Literal finite-law realization of the paper's conditional comparison bit.
The signed `A–B` channel is fixed under conditioning by `U`, as in the manuscript.
The witness is generated using one independent private noise bit. -/
theorem conditional_comparison_realized (μ : FiniteLaw Ω) (a b c : Ω → Bool)
    {U : Type*} [Fintype U] [DecidableEq U] (u : Ω → U)
    (hau : μ.independentUnbiasedBit a u) (hbu : μ.independentUnbiasedBit b u)
    (hchannel : ∀ s, 0 < μ.fibreMass u s →
      (μ.conditionOn u s).bitCorrelation a b=μ.bitCorrelation a b)
    (hmark : ∀ s, 0 < μ.fibreMass u s →
      (μ.conditionOn u s).conditionallyIndependentBit c a b)
    (hV : 0 < μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)))
    [DecidableEq Ω] :
    ∃ (ν : FiniteLaw (Ω × Bool)) (c' : Ω × Bool → Bool),
      ν.map Prod.fst=μ ∧
      ν.conditionallyIndependentBit c' Prod.fst (fun p => b p.1) ∧
      ν.expect (fun p => bitValue (c' p))=1/2 ∧
      ν.shannonInformation (fun p => bitValue (b p.1)) c' =
        μ.conditionalShannonInformation (fun ω => bitValue (b ω)) c u /
          μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) ∧
      μ.conditionalShannonInformation (fun ω => bitValue (a ω)) c u /
          μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)) ≤
        ν.shannonInformation (fun p => bitValue (a p.1)) c' ∧
      μ.quadraticInformation (fun ω => bitValue (c ω)) b /
          (μ.conditionalQuadraticEntropy u (fun ω => bitValue (c ω)))^2 ≤
        ν.quadraticInformation (fun p => bitValue (c' p)) (fun p => b p.1) := by
  have ha := μ.mean_of_independentUnbiasedBit a u hau
  have hb := μ.mean_of_independentUnbiasedBit b u hbu
  have hρ1 : |μ.bitCorrelation a b| ≤ 1 := by
    have h := μ.binaryProfile_parameters_domain b a hb
    rw [μ.bitCorrelation_symm b a] at h
    have hbiasa : μ.bitBias a=0 := by unfold bitBias; rw [ha]; ring
    simpa only [hbiasa,abs_zero,zero_add] using h
  obtain ⟨τ,hτ,hmatch,hupper,hcorr⟩ := μ.conditional_comparison a b c u
    (abs_nonneg _) hρ1 hau hbu (fun s hs => by rw [hchannel s hs]) hmark hV
  refine ⟨μ.comparatorExtension τ hτ.1 hτ.2,comparatorBit b,
    μ.comparatorExtension_map_fst τ hτ.1 hτ.2,
    μ.comparatorExtension_markov b τ hτ.1 hτ.2 id,
    μ.comparatorExtension_output_unbiased b τ hτ.1 hτ.2 hb,?_,?_,?_⟩
  · rw [μ.comparatorExtension_shannonInformation b τ hτ.1 hτ.2 hb]
    apply (eq_div_iff (ne_of_gt hV)).mpr
    nlinarith [hmatch]
  · rw [μ.comparatorExtension_channel_information a b τ hτ.1 hτ.2 ha hb]
    exact (div_le_iff₀ hV).mpr (by nlinarith [hupper])
  · rw [μ.comparatorExtension_quadraticInformation b τ hτ.1 hτ.2 hb]
    exact hcorr

end FiniteLaw
end CourtadeKumar
