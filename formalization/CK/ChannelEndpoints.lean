import CK.Channel

/-! Exact degenerate cases and noise-complement symmetry for the frozen target. -/

noncomputable section
namespace CourtadeKumar.Spec
open scoped BigOperators

def complementCube (n : ℕ) : Cube n ≃ Cube n where
  toFun x i := !(x i)
  invFun x i := !(x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

theorem average_complement {n : ℕ} (g : Cube n → ℝ) :
    average (fun x => g (complementCube n x)) = average g := by
  unfold average
  rw [(complementCube n).sum_comp g]

theorem channel_complement_noise {n : ℕ} (p : ℝ) (x y : Cube n) :
    channel (1 - p) x y = channel p (complementCube n x) y := by
  unfold channel
  apply Finset.prod_congr rfl
  intro i _
  cases hxi : x i <;> cases hyi : y i <;> simp [complementCube, hxi, hyi]

theorem outputPosterior_complement_noise {n : ℕ} (f : Cube n → Bool) (p : ℝ) (x : Cube n) :
    outputPosterior f (1 - p) x = outputPosterior f p (complementCube n x) := by
  simp only [outputPosterior, channel_complement_noise]

theorem mutualInformation_complement_noise {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    mutualInformation f (1 - p) = mutualInformation f p := by
  unfold mutualInformation
  simp_rw [outputPosterior_complement_noise]
  congr 1
  exact average_complement (fun x => entropy (outputPosterior f p x))

theorem progressiveBound_complement_noise (p μ : ℝ) :
    progressiveBound (1 - p) μ = progressiveBound p μ :=
  progressiveEntropy_complement_noise p μ

@[simp] theorem entropy_bit (b : Bool) : entropy (bit b) = 0 := by
  cases b <;> simp [bit, entropy]

theorem channel_zero {n : ℕ} (x y : Cube n) :
    channel 0 x y = if x = y then 1 else 0 := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [channel]
  · rw [if_neg hxy]
    have hex : ∃ i, x i ≠ y i := by
      by_contra h
      push_neg at h
      exact hxy (funext h)
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

@[simp] theorem outputPosterior_zero {n : ℕ} (f : Cube n → Bool) (x : Cube n) :
    outputPosterior f 0 x = bit (f x) := by
  classical
  simp [outputPosterior, channel_zero, ite_mul]

@[simp] theorem mutualInformation_zero {n : ℕ} (f : Cube n → Bool) :
    mutualInformation f 0 = entropy (outputMean f) := by
  simp [mutualInformation, average_const]

theorem channel_half {n : ℕ} (x y : Cube n) :
    channel (1 / 2) x y = (1 / 2 : ℝ) ^ n := by
  unfold channel
  simp only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ite_self]
  simp

@[simp] theorem outputPosterior_half {n : ℕ} (f : Cube n → Bool) (x : Cube n) :
    outputPosterior f (1 / 2) x = outputMean f := by
  simp only [outputPosterior, channel_half, ← Finset.mul_sum]
  unfold outputMean average
  rw [div_pow, one_pow]
  ring

@[simp] theorem mutualInformation_half {n : ℕ} (f : Cube n → Bool) :
    mutualInformation f (1 / 2) = 0 := by
  simp only [mutualInformation, outputPosterior_half, average_const, sub_self]

@[simp] theorem mutualInformation_one {n : ℕ} (f : Cube n → Bool) :
    mutualInformation f 1 = entropy (outputMean f) := by
  simpa using mutualInformation_complement_noise f 0

@[simp] theorem progressiveBound_zero_noise (μ : ℝ) : progressiveBound 0 μ = entropy μ := by
  simp [progressiveBound, entropy]

@[simp] theorem progressiveBound_half_noise (μ : ℝ) : progressiveBound (1 / 2) μ = 0 := by
  have h : entropy (1 / 2) = 1 := entropyBits_half
  unfold progressiveBound
  rw [h]
  norm_num

@[simp] theorem progressiveBound_one_noise (μ : ℝ) : progressiveBound 1 μ = entropy μ := by
  simpa using progressiveBound_complement_noise 0 μ

theorem target_noise_endpoints {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (hp : p = 0 ∨ p = 1 / 2 ∨ p = 1) :
    mutualInformation f p ≤ progressiveBound p (outputMean f) := by
  rcases hp with rfl | rfl | rfl <;>
    simp only [mutualInformation_zero, mutualInformation_half, mutualInformation_one,
      progressiveBound_zero_noise, progressiveBound_half_noise, progressiveBound_one_noise, le_refl]

@[simp] theorem outputMean_const (n : ℕ) (b : Bool) :
    outputMean (n := n) (fun _ => b) = bit b := average_const n _

@[simp] theorem outputPosterior_const {n : ℕ} (p : ℝ) (b : Bool) (x : Cube n) :
    outputPosterior (fun _ => b) p x = bit b := by
  unfold outputPosterior
  rw [← Finset.sum_mul, channel_row_sum, one_mul]

@[simp] theorem mutualInformation_const (n : ℕ) (p : ℝ) (b : Bool) :
    mutualInformation (n := n) (fun _ => b) p = 0 := by
  simp [mutualInformation, average_const]

theorem target_constant (n : ℕ) (p : ℝ) (b : Bool) :
    mutualInformation (n := n) (fun _ => b) p = progressiveBound p (outputMean (n := n) (fun _ => b)) := by
  cases b <;> simp [progressiveBound, bit, entropy]

theorem target_dimension_zero (f : Cube 0 → Bool) (p : ℝ) :
    mutualInformation f p = progressiveBound p (outputMean f) := by
  let x : Cube 0 := fun i => Fin.elim0 i
  have hf : f = fun _ => f x := by
    funext y
    exact congrArg f (Subsingleton.elim y x)
  rw [hf]
  exact target_constant 0 p (f x)

def oneCube : Bool ≃ Cube 1 where
  toFun b _ := b
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    rw [hi]

theorem average_one (g : Cube 1 → ℝ) :
    average g = (g (oneCube false) + g (oneCube true)) / 2 := by
  unfold average
  rw [← oneCube.sum_comp g]
  simp [Fintype.sum_bool, add_comm]

theorem channel_one (p : ℝ) (x y : Cube 1) :
    channel p x y = if x 0 = y 0 then 1 - p else p := by
  unfold channel
  simp

theorem posterior_one_false (f : Cube 1 → Bool) (p : ℝ) :
    outputPosterior f p (oneCube false) =
      (1 - p) * bit (f (oneCube false)) + p * bit (f (oneCube true)) := by
  unfold outputPosterior
  rw [← oneCube.sum_comp]
  simp [Fintype.sum_bool, channel_one, oneCube, add_comm]

theorem posterior_one_true (f : Cube 1 → Bool) (p : ℝ) :
    outputPosterior f p (oneCube true) =
      p * bit (f (oneCube false)) + (1 - p) * bit (f (oneCube true)) := by
  unfold outputPosterior
  rw [← oneCube.sum_comp]
  simp [Fintype.sum_bool, channel_one, oneCube, add_comm]

theorem target_dimension_one (f : Cube 1 → Bool) (p : ℝ) :
    mutualInformation f p = progressiveBound p (outputMean f) := by
  have hhalf : entropy (1 / 2) = 1 := entropyBits_half
  have hQhalf : progressiveBound p (1 / 2) = 1 - entropy p := progressiveEntropy_half p
  have hQzero : progressiveBound p 0 = 0 := progressiveEntropy_zero p
  have hQone : progressiveBound p 1 = 0 := progressiveEntropy_one p
  unfold mutualInformation outputMean
  rw [average_one, average_one]
  rw [posterior_one_false, posterior_one_true]
  cases h0 : f (oneCube false) <;> cases h1 : f (oneCube true) <;>
    norm_num [bit, hhalf, hQhalf, hQzero, hQone, entropy, Real.binEntropy_one_sub,
      Real.binEntropy_two_inv]
  all_goals field_simp [log_two_pos.ne'] <;> ring
  all_goals simpa only [one_div] using Real.binEntropy_two_inv

end CourtadeKumar.Spec
