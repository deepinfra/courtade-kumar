import CK.Algebra

/-!
# An arbitrary-dimensional induction interface -- UNCOMPILED DRAFT

This proves a generic induction FROM explicit splitting data. Instantiating that
data for actual Boolean functions requires the unformalized posterior lemma and
scalar estimate. It does not prove those hypotheses or the CK theorem.
-/
noncomputable section
universe u
namespace CK

/-- The quantifier over dimensions is real mathematical induction, but the
conditional interface is deliberately exposed rather than hidden in axioms. -/
theorem abstract_profile_induction
    (Obj : ℕ → Type u)
    (V H : (n : ℕ) → Obj n → ℝ)
    (h : ℝ) (hh : 0 ≤ h)
    (vrange : ∀ n (f : Obj n), V n f ≤ 1)
    (base_zero : ∀ f : Obj 0, V 0 f * h ≤ H 0 f)
    (base_one : ∀ f : Obj 1, V 1 f * h ≤ H 1 f)
    (split : ∀ n (f : Obj (n + 2)),
      ∃ (f0 f1 : Obj (n + 1)) (d e J : ℝ),
        0 ≤ d ∧ d ≤ 1 / 2 ∧ d ≤ e ∧
        (V (n + 1) f0 + V (n + 1) f1) / 2 = V (n + 2) f - d ^ 2 ∧
        (H (n + 1) f0 + H (n + 1) f1) / 2 ≤ J ∧
        J + 2 * d * h * e ≤ (1 + d ^ 2) * H (n + 2) f) :
    ∀ n (f : Obj n), V n f * h ≤ H n f := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · exact base_zero
    rcases n with _ | n
    · exact base_one
    intro f
    rcases split n f with ⟨f0, f1, d, e, J, hd, _hsmall, he, hv, hj, hm⟩
    have h0 := ih (n + 1) (by omega) f0
    have h1 := ih (n + 1) (by omega) f1
    have hc : (V (n + 2) f - d ^ 2) * h ≤ J := by
      nlinarith [congrArg (fun x : ℝ => h * x) hv]
    exact Algebra.induction_step (V (n + 2) f) h d e J (H (n + 2) f)
      (vrange (n + 2) f) hh hd he hc hm

end CK
