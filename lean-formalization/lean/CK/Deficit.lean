import CK.KappaSeries
import CK.Sections
import CK.AvgLemmas
import Mathlib.Algebra.BigOperators.Field

/-!
# Entropy-deficit contraction under BSC noise (manuscript `lem:contraction`)

For a probability vector `q` on the cube `Cube k`, `deficit q = k log 2 − H(q)` is the
entropy deficit relative to the uniform distribution.  Passing `q` through the product
binary symmetric channel with flip probability `p` (`noisy p q`) contracts the deficit
by the factor `(1 − 2p)²` (`deficit_noisy_le`).

The proof is by induction on the dimension: the chain rule along the last coordinate
(`ent_chain`, `deficit_chain`), the one-bit contraction `kappa (θu) ≤ θ² kappa u`
(`kappa_scaling`, manuscript `eq:entropyfacts`), and concavity of entropy
(`ent_mixture_ge`) applied to the conditional distributions of the noisy output.
-/
noncomputable section
namespace CK
open scoped BigOperators

/-- Shannon entropy (nats) of a nonnegative vector on a finite type. -/
def ent {α : Type*} [Fintype α] (q : α → ℝ) : ℝ := ∑ a, Real.negMulLog (q a)

/-- Probability vector. -/
structure IsDist {α : Type*} [Fintype α] (q : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ q a
  sum_one : ∑ a, q a = 1

/-- Push-forward of a distribution on the cube through the product BSC with flip probability p. -/
def noisy {k : ℕ} (p : ℝ) (q : Cube k → ℝ) (w : Cube k) : ℝ := ∑ u, kernel p w u * q u

/-- Entropy deficit relative to the uniform distribution on Cube k. -/
def deficit {k : ℕ} (q : Cube k → ℝ) : ℝ := k * Real.log 2 - ent q

/-! ## Basic facts about `noisy` -/

/-- Columns of the product kernel sum to one (symmetry + `kernel_row_sum`). -/
theorem kernel_col_sum {n : ℕ} (p : ℝ) (u : Cube n) : ∑ w : Cube n, kernel p w u = 1 := by
  rw [Finset.sum_congr rfl fun w _ => kernel_symm p w u]
  exact kernel_row_sum p u

/-- The channel preserves total mass (no sign or range condition needed). -/
theorem sum_noisy {k : ℕ} (p : ℝ) (q : Cube k → ℝ) : ∑ w, noisy p q w = ∑ u, q u := by
  unfold noisy
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_mul, kernel_col_sum, one_mul]

theorem noisy_nonneg {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q : Cube k → ℝ}
    (hq : ∀ x, 0 ≤ q x) (w : Cube k) : 0 ≤ noisy p q w :=
  Finset.sum_nonneg fun u _ => mul_nonneg (kernel_nonneg p hp0 hp1 w u) (hq u)

theorem noisy_isDist {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q : Cube k → ℝ}
    (hq : IsDist q) : IsDist (noisy p q) where
  nonneg := noisy_nonneg hp0 hp1 hq.nonneg
  sum_one := by rw [sum_noisy]; exact hq.sum_one

theorem noisy_add {k : ℕ} (p : ℝ) (q q' : Cube k → ℝ) :
    noisy p (fun u => q u + q' u) = fun w => noisy p q w + noisy p q' w := by
  funext w
  unfold noisy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

theorem noisy_smul {k : ℕ} (p c : ℝ) (q : Cube k → ℝ) :
    noisy p (fun u => c * q u) = fun w => c * noisy p q w := by
  funext w
  unfold noisy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

/-- Linearity of `noisy` for finite mixtures. -/
theorem noisy_sum {k : ℕ} {β : Type*} [Fintype β] (p : ℝ) (c : β → ℝ) (f : β → Cube k → ℝ)
    (w : Cube k) :
    noisy p (fun u => ∑ s, c s * f s u) w = ∑ s, c s * noisy p (f s) w := by
  unfold noisy
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun u _ => ?_
  ring

/-! ## Basic facts about `ent` -/

theorem ent_nonneg {α : Type*} [Fintype α] {q : α → ℝ} (hq : IsDist q) : 0 ≤ ent q := by
  unfold ent
  refine Finset.sum_nonneg fun a _ => Real.negMulLog_nonneg (hq.nonneg a) ?_
  calc q a ≤ ∑ b, q b := Finset.single_le_sum (fun b _ => hq.nonneg b) (Finset.mem_univ a)
    _ = 1 := hq.sum_one

/-- concavity of entropy for finite mixtures -/
theorem ent_mixture_ge {α β : Type*} [Fintype α] [Fintype β] (lam : β → ℝ) (hl0 : ∀ b, 0 ≤ lam b)
    (hl1 : ∑ b, lam b = 1) (q : β → α → ℝ) (hq : ∀ b a, 0 ≤ q b a) :
    ∑ b, lam b * ent (q b) ≤ ent (fun a => ∑ b, lam b * q b a) := by
  unfold ent
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ => ?_
  have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := lam) (p := fun b => q b a)
    (fun b _ => hl0 b) hl1 (fun b _ => Set.mem_Ici.mpr (hq b a))
  simpa only [smul_eq_mul] using h

/-- one-bit deficit: for the distribution (r, 1−r) on Bool the deficit is kappa (2r−1). -/
theorem deficit_bool (r : ℝ) :
    Real.log 2 - (Real.negMulLog r + Real.negMulLog (1 - r)) = kappa (2 * r - 1) := by
  unfold kappa eta binaryEntropy Real.negMulLog
  rw [show (1 + (2 * r - 1)) / 2 = r by ring]
  ring

theorem ent_bool (m : Bool → ℝ) : ent m = Real.negMulLog (m true) + Real.negMulLog (m false) := by
  unfold ent
  exact Fintype.sum_bool _

theorem ent_zero_dim {q : Cube 0 → ℝ} (hq : IsDist q) : ent q = 0 := by
  unfold ent
  rw [Fintype.sum_unique]
  have h := hq.sum_one
  rw [Fintype.sum_unique] at h
  rw [h, Real.negMulLog_one]

theorem deficit_zero_dim {q : Cube 0 → ℝ} (hq : IsDist q) : deficit q = 0 := by
  unfold deficit
  rw [ent_zero_dim hq]
  simp

/-! ## Splitting the last coordinate: marginal and conditional -/

/-- Sums over `Cube (k+1)` split along the last coordinate. -/
theorem sum_snoc {k : ℕ} (v : Cube (k + 1) → ℝ) :
    ∑ x, v x = ∑ s : Bool, ∑ w : Cube k, v (Fin.snoc w s) := by
  rw [← Fintype.sum_equiv (Fin.snocEquiv fun _ => Bool) _ _ (fun q => rfl), Fintype.sum_prod_type]
  rfl

/-- Marginal of the last coordinate. -/
def marg {k : ℕ} (q : Cube (k + 1) → ℝ) (s : Bool) : ℝ := ∑ w : Cube k, q (Fin.snoc w s)

/-- Conditional distribution on the first `k` coordinates given the last coordinate `s`
(zero when the marginal vanishes). -/
def condDist {k : ℕ} (q : Cube (k + 1) → ℝ) (s : Bool) (w : Cube k) : ℝ :=
  if marg q s = 0 then 0 else q (Fin.snoc w s) / marg q s

theorem marg_nonneg {k : ℕ} {q : Cube (k + 1) → ℝ} (hq : ∀ x, 0 ≤ q x) (s : Bool) :
    0 ≤ marg q s :=
  Finset.sum_nonneg fun w _ => hq (Fin.snoc w s)

theorem sum_marg {k : ℕ} (q : Cube (k + 1) → ℝ) : ∑ s, marg q s = ∑ x, q x := by
  unfold marg
  rw [sum_snoc]

theorem snoc_eq_zero_of_marg {k : ℕ} {q : Cube (k + 1) → ℝ} (hq : ∀ x, 0 ≤ q x) {s : Bool}
    (h : marg q s = 0) (w : Cube k) : q (Fin.snoc w s) = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun w _ => hq (Fin.snoc w s)).mp h w (Finset.mem_univ w)

theorem snoc_eq_marg_mul_condDist {k : ℕ} {q : Cube (k + 1) → ℝ} (hq : ∀ x, 0 ≤ q x)
    (w : Cube k) (s : Bool) : q (Fin.snoc w s) = marg q s * condDist q s w := by
  unfold condDist
  by_cases h : marg q s = 0
  · rw [if_pos h, mul_zero]
    exact snoc_eq_zero_of_marg hq h w
  · rw [if_neg h]
    field_simp

theorem condDist_nonneg {k : ℕ} {q : Cube (k + 1) → ℝ} (hq : ∀ x, 0 ≤ q x) (s : Bool)
    (w : Cube k) : 0 ≤ condDist q s w := by
  unfold condDist
  split_ifs
  · exact le_rfl
  · exact div_nonneg (hq _) (marg_nonneg hq s)

theorem sum_condDist {k : ℕ} {q : Cube (k + 1) → ℝ} {s : Bool} (h : marg q s ≠ 0) :
    ∑ w, condDist q s w = 1 := by
  unfold condDist
  simp only [if_neg h]
  rw [← Finset.sum_div]
  exact div_self h

theorem condDist_isDist {k : ℕ} {q : Cube (k + 1) → ℝ} (hq : ∀ x, 0 ≤ q x) {s : Bool}
    (h : marg q s ≠ 0) : IsDist (condDist q s) where
  nonneg := condDist_nonneg hq s
  sum_one := sum_condDist h

theorem marg_mul_sum_condDist {k : ℕ} (q : Cube (k + 1) → ℝ) (s : Bool) :
    marg q s * ∑ w, condDist q s w = marg q s := by
  by_cases h : marg q s = 0
  · rw [h, zero_mul]
  · rw [sum_condDist h, mul_one]

theorem sum_condDist_mul_negMulLog {k : ℕ} (q : Cube (k + 1) → ℝ) (s : Bool) :
    (∑ w, condDist q s w) * Real.negMulLog (marg q s) = Real.negMulLog (marg q s) := by
  by_cases h : marg q s = 0
  · rw [h, Real.negMulLog_zero, mul_zero]
  · rw [sum_condDist h, one_mul]

/-- Chain rule for the entropy along the last coordinate. -/
theorem ent_chain {k : ℕ} {q : Cube (k + 1) → ℝ} (hq : ∀ x, 0 ≤ q x) :
    ent q = ent (marg q) + ∑ s, marg q s * ent (condDist q s) := by
  unfold ent
  rw [sum_snoc, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [snoc_eq_marg_mul_condDist hq, Real.negMulLog_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, sum_condDist_mul_negMulLog]

/-- Chain rule for the deficit along the last coordinate. -/
theorem deficit_chain {k : ℕ} {q : Cube (k + 1) → ℝ} (hq : IsDist q) :
    deficit q = (Real.log 2 - ent (marg q)) + ∑ s, marg q s * deficit (condDist q s) := by
  have hsum : ∑ s, marg q s = 1 := by rw [sum_marg]; exact hq.sum_one
  unfold deficit
  rw [ent_chain hq.nonneg]
  have h2 : ∑ s, marg q s * ((k : ℝ) * Real.log 2 - ent (condDist q s)) =
      (k : ℝ) * Real.log 2 - ∑ s, marg q s * ent (condDist q s) := by
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [h2]
  push_cast
  ring

/-! ## Structure of `noisy` along the last coordinate -/

/-- The one-bit BSC kernel. -/
def k1 (p : ℝ) (b s : Bool) : ℝ := if b = s then 1 - p else p

theorem k1_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b s : Bool) : 0 ≤ k1 p b s := by
  unfold k1
  split_ifs <;> linarith

theorem sum_k1 (p : ℝ) (s : Bool) : ∑ b : Bool, k1 p b s = 1 := by
  rw [Fintype.sum_bool]
  cases s <;> simp [k1]

/-- `noisy p q` at an output with last bit `b` is the `k1`-mixture of the noisy conditionals. -/
theorem noisy_snoc {k : ℕ} {p : ℝ} {q : Cube (k + 1) → ℝ} (hq : ∀ x, 0 ≤ q x) (w : Cube k)
    (b : Bool) :
    noisy p q (Fin.snoc w b) = ∑ s, k1 p b s * (marg q s * noisy p (condDist q s) w) := by
  unfold noisy
  rw [sum_snoc]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [kernel_snoc, snoc_eq_marg_mul_condDist hq]
  unfold k1
  ring

/-- Marginal of the noisy output: the one-bit channel applied to the marginal. -/
theorem marg_noisy {k : ℕ} {p : ℝ} {q : Cube (k + 1) → ℝ} (hq : ∀ x, 0 ≤ q x) (b : Bool) :
    marg (noisy p q) b = ∑ s, k1 p b s * marg q s := by
  rw [show marg (noisy p q) b = ∑ w, noisy p q (Fin.snoc w b) from rfl]
  simp_rw [noisy_snoc hq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_noisy, marg_mul_sum_condDist]

/-- Mixing weights of the noisy conditional. -/
def lam {k : ℕ} (p : ℝ) (q : Cube (k + 1) → ℝ) (b s : Bool) : ℝ :=
  k1 p b s * marg q s / marg (noisy p q) b

/-- The mixture of the conditionals of `q` whose noisy version is the conditional of
`noisy p q`. -/
def mix {k : ℕ} (p : ℝ) (q : Cube (k + 1) → ℝ) (b : Bool) (w : Cube k) : ℝ :=
  ∑ s, lam p q b s * condDist q s w

theorem lam_nonneg {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q : Cube (k + 1) → ℝ}
    (hq : ∀ x, 0 ≤ q x) (b s : Bool) : 0 ≤ lam p q b s := by
  unfold lam
  exact div_nonneg (mul_nonneg (k1_nonneg hp0 hp1 b s) (marg_nonneg hq s))
    (marg_nonneg (noisy_nonneg hp0 hp1 hq) b)

theorem sum_lam {k : ℕ} {p : ℝ} {q : Cube (k + 1) → ℝ} (hq : ∀ x, 0 ≤ q x) {b : Bool}
    (h : marg (noisy p q) b ≠ 0) : ∑ s, lam p q b s = 1 := by
  unfold lam
  rw [← Finset.sum_div, ← marg_noisy hq]
  exact div_self h

theorem lam_mul_sum_condDist {k : ℕ} (p : ℝ) (q : Cube (k + 1) → ℝ) (b s : Bool) :
    lam p q b s * ∑ w, condDist q s w = lam p q b s := by
  by_cases h : marg q s = 0
  · unfold lam
    rw [h, mul_zero, zero_div, zero_mul]
  · rw [sum_condDist h, mul_one]

theorem mix_isDist {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q : Cube (k + 1) → ℝ}
    (hq : ∀ x, 0 ≤ q x) {b : Bool} (h : marg (noisy p q) b ≠ 0) : IsDist (mix p q b) where
  nonneg w := Finset.sum_nonneg fun s _ =>
    mul_nonneg (lam_nonneg hp0 hp1 hq b s) (condDist_nonneg hq s w)
  sum_one := by
    unfold mix
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, lam_mul_sum_condDist]
    exact sum_lam hq h

/-- `M b * lam b s = k1 b s * marg q s` (also when `M b = 0`, since then every term vanishes). -/
theorem marg_noisy_mul_lam {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q : Cube (k + 1) → ℝ}
    (hq : ∀ x, 0 ≤ q x) (b s : Bool) :
    marg (noisy p q) b * lam p q b s = k1 p b s * marg q s := by
  by_cases h : marg (noisy p q) b = 0
  · rw [h, zero_mul]
    have h' : ∑ s, k1 p b s * marg q s = 0 := by rw [← marg_noisy hq]; exact h
    exact ((Finset.sum_eq_zero_iff_of_nonneg fun s _ =>
      mul_nonneg (k1_nonneg hp0 hp1 b s) (marg_nonneg hq s)).mp h' s (Finset.mem_univ s)).symm
  · unfold lam
    calc marg (noisy p q) b * (k1 p b s * marg q s / marg (noisy p q) b)
        = k1 p b s * marg q s * (marg (noisy p q) b / marg (noisy p q) b) := by ring
      _ = k1 p b s * marg q s := by rw [div_self h, mul_one]

/-- The conditional of the noisy output is the noisy version of the mixture `mix`. -/
theorem condDist_noisy {k : ℕ} {p : ℝ} {q : Cube (k + 1) → ℝ} (hq : ∀ x, 0 ≤ q x) {b : Bool}
    (h : marg (noisy p q) b ≠ 0) : condDist (noisy p q) b = noisy p (mix p q b) := by
  funext w
  unfold condDist
  rw [if_neg h, noisy_snoc hq]
  unfold mix
  rw [noisy_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold lam
  ring

/-- Reassembling the mixture weights: `Σ_b M b (c Σ_s lam b s D s) = c Σ_s marg q s D s`. -/
theorem sum_marg_noisy_lam {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q : Cube (k + 1) → ℝ}
    (hq : ∀ x, 0 ≤ q x) (c : ℝ) (D : Bool → ℝ) :
    ∑ b, marg (noisy p q) b * (c * ∑ s, lam p q b s * D s) = c * ∑ s, marg q s * D s := by
  have h1 : ∀ b, marg (noisy p q) b * (c * ∑ s, lam p q b s * D s) =
      c * ∑ s, k1 p b s * marg q s * D s := by
    intro b
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← marg_noisy_mul_lam hp0 hp1 hq b s]
    ring
  simp_rw [h1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul, sum_k1, one_mul]

/-! ## The two ingredients of the induction step -/

/-- One-bit step: the deficit of the marginal contracts by `(1 − 2p)²` (`kappa_scaling`). -/
theorem onebit_step {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) {q : Cube (k + 1) → ℝ}
    (hq : IsDist q) :
    Real.log 2 - ent (marg (noisy p q)) ≤ (1 - 2 * p) ^ 2 * (Real.log 2 - ent (marg q)) := by
  have hr0 : 0 ≤ marg q true := marg_nonneg hq.nonneg _
  have hr1 : 0 ≤ marg q false := marg_nonneg hq.nonneg _
  have hsum : marg q true + marg q false = 1 := by
    have h := sum_marg q
    rw [hq.sum_one, Fintype.sum_bool] at h
    exact h
  have hmt : marg (noisy p q) true = (1 - p) * marg q true + p * marg q false := by
    rw [marg_noisy hq.nonneg, Fintype.sum_bool]
    simp [k1]
  have hmf : marg (noisy p q) false = p * marg q true + (1 - p) * marg q false := by
    rw [marg_noisy hq.nonneg, Fintype.sum_bool]
    simp [k1]
  rw [ent_bool, ent_bool, hmt, hmf, show marg q false = 1 - marg q true by linarith,
    show p * marg q true + (1 - p) * (1 - marg q true) =
      1 - ((1 - p) * marg q true + p * (1 - marg q true)) by ring,
    deficit_bool, deficit_bool,
    show 2 * ((1 - p) * marg q true + p * (1 - marg q true)) - 1 =
      (1 - 2 * p) * (2 * marg q true - 1) by ring]
  exact kappa_scaling (by linarith) (by linarith) (by linarith) (by linarith)

/-- Concavity step: the deficit of the mixture is at most the mixture of the deficits. -/
theorem deficit_mix_le {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q : Cube (k + 1) → ℝ}
    (hq : ∀ x, 0 ≤ q x) {b : Bool} (h : marg (noisy p q) b ≠ 0) :
    deficit (mix p q b) ≤ ∑ s, lam p q b s * deficit (condDist q s) := by
  have hl1 := sum_lam hq h
  have hc := ent_mixture_ge (lam p q b) (lam_nonneg hp0 hp1 hq b) hl1 (condDist q)
    (fun s w => condDist_nonneg hq s w)
  unfold deficit
  have h2 : ∑ s, lam p q b s * ((k : ℝ) * Real.log 2 - ent (condDist q s)) =
      (k : ℝ) * Real.log 2 - ∑ s, lam p q b s * ent (condDist q s) := by
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hl1, one_mul]
  rw [h2]
  have h3 : ent (mix p q b) = ent (fun w => ∑ s, lam p q b s * condDist q s w) := rfl
  linarith

/-! ## The main theorem -/

theorem deficit_noisy_le_aux {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    ∀ (k : ℕ) (q : Cube k → ℝ), IsDist q →
      deficit (noisy p q) ≤ (1 - 2 * p) ^ 2 * deficit q := by
  intro k
  induction k with
  | zero =>
    intro q hq
    rw [deficit_zero_dim hq, deficit_zero_dim (noisy_isDist hp0 (by linarith) hq), mul_zero]
  | succ k ih =>
    intro q hq
    have hp1' : p ≤ 1 := by linarith
    have hN : IsDist (noisy p q) := noisy_isDist hp0 hp1' hq
    have hterm : ∀ b, marg (noisy p q) b * deficit (condDist (noisy p q) b) ≤
        marg (noisy p q) b * ((1 - 2 * p) ^ 2 * ∑ s, lam p q b s * deficit (condDist q s)) := by
      intro b
      by_cases h : marg (noisy p q) b = 0
      · rw [h, zero_mul, zero_mul]
      · refine mul_le_mul_of_nonneg_left ?_ (marg_nonneg hN.nonneg b)
        rw [condDist_noisy hq.nonneg h]
        calc deficit (noisy p (mix p q b))
            ≤ (1 - 2 * p) ^ 2 * deficit (mix p q b) := ih _ (mix_isDist hp0 hp1' hq.nonneg h)
          _ ≤ (1 - 2 * p) ^ 2 * ∑ s, lam p q b s * deficit (condDist q s) :=
            mul_le_mul_of_nonneg_left (deficit_mix_le hp0 hp1' hq.nonneg h) (sq_nonneg _)
    calc deficit (noisy p q)
        = (Real.log 2 - ent (marg (noisy p q))) +
            ∑ b, marg (noisy p q) b * deficit (condDist (noisy p q) b) := deficit_chain hN
      _ ≤ (1 - 2 * p) ^ 2 * (Real.log 2 - ent (marg q)) +
            ∑ b, marg (noisy p q) b *
              ((1 - 2 * p) ^ 2 * ∑ s, lam p q b s * deficit (condDist q s)) :=
          add_le_add (onebit_step hp0 hp1 hq) (Finset.sum_le_sum fun b _ => hterm b)
      _ = (1 - 2 * p) ^ 2 *
            ((Real.log 2 - ent (marg q)) + ∑ s, marg q s * deficit (condDist q s)) := by
          rw [sum_marg_noisy_lam hp0 hp1' hq.nonneg, mul_add]
      _ = (1 - 2 * p) ^ 2 * deficit q := by rw [deficit_chain hq]

/-- THE MAIN THEOREM: BSC noise contracts the deficit by (1 − 2p)² (manuscript
`lem:contraction`). -/
theorem deficit_noisy_le {k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) {q : Cube k → ℝ}
    (hq : IsDist q) : deficit (noisy p q) ≤ (1 - 2 * p) ^ 2 * deficit q :=
  deficit_noisy_le_aux hp0 hp1 k q hq

end CK
