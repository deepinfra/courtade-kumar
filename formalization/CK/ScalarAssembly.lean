import CK.ScalarJensen

/-! # Exact algebraic assembly of the three-bit scalar barrier -/

noncomputable section
namespace CourtadeKumar
namespace Scalar

/-- Algebra joining the two Jensen bounds to the strict tail barrier. -/
theorem scalar_barrier_assembly {J B K h L t S G₁ G₂ σ : ℝ}
    (hJ : 0 < J) (hB : 0 < B) (hh : 0 < h) (hL : 0 < L)
    (ht : 0 < t) (hσ : 0 < σ)
    (hexponent : h*L*J=2*B*K)
    (hfirst : K*(1-t^2)/h ≤ G₁)
    (hsecond : J*S/t ≤ B*G₂/σ)
    (hbarrier : 2*B < (1-t^2)/2+4*S/t) :
    J < G₁/(2*L)+2*G₂/σ := by
  let X := G₁/(2*L)
  let Y := 2*G₂/σ
  have hx : 2*L*X=G₁ := by dsimp [X]; field_simp
  have hy : σ*Y=2*G₂ := by dsimp [Y]; field_simp
  have hf := (div_le_iff₀ hh).mp hfirst
  have hf₂ : L*J*(1-t^2) ≤ 2*B*G₁ := by
    apply (mul_le_mul_left hh).mp
    calc
      h*(L*J*(1-t^2))=(h*L*J)*(1-t^2) := by ring
      _ = (2*B*K)*(1-t^2) := by rw [hexponent]
      _ = 2*B*(K*(1-t^2)) := by ring
      _ ≤ 2*B*(G₁*h) := mul_le_mul_of_nonneg_left hf (by positivity)
      _ = h*(2*B*G₁) := by ring
  have hX : J*(1-t^2) ≤ 4*B*X := by
    apply (mul_le_mul_left hL).mp
    calc
      L*(J*(1-t^2))=L*J*(1-t^2) := by ring
      _ ≤ 2*B*G₁ := hf₂
      _ = L*(4*B*X) := by rw [← hx]; ring
  have hs := (div_le_div_iff₀ ht hσ).mp hsecond
  have hY : 2*J*S ≤ B*Y*t := by
    apply (mul_le_mul_left hσ).mp
    calc
      σ*(2*J*S)=2*(J*S*σ) := by ring
      _ ≤ 2*(B*G₂*t) := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = B*(σ*Y)*t := by rw [hy]; ring
      _ = σ*(B*Y*t) := by ring
  have hb : 4*B*t < t*(1-t^2)+8*S := by
    have h := mul_lt_mul_of_pos_right hbarrier (show 0 < 2*t by positivity)
    have heq : ((1-t^2)/2+4*S/t)*(2*t)=t*(1-t^2)+8*S := by
      field_simp
      ring
    rw [heq] at h
    nlinarith
  have hbJ := mul_lt_mul_of_pos_left hb hJ
  have hXt := mul_le_mul_of_nonneg_right hX ht.le
  have hfinal : (4*B*t)*J < (4*B*t)*(X+Y) := by nlinarith [hbJ,hXt,hY]
  exact (mul_lt_mul_left (show 0 < 4*B*t by positivity)).mp hfinal

end Scalar
end CourtadeKumar
