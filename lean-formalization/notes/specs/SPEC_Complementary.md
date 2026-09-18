# TASK: CK/Complementary.lean — the complementary branch and the main theorem (manuscript Sec. 6.6 proof of Theorem thm:main)

Imports: `import CK.LargeBias`, `import CK.LargeCoordinate`, `import CK.MiddleHigh`, `import CK.FourierCap`, `import CK.ScalarMixing`, `import CK.Relabel`, `import CK.SmallGap`.
Read CK/Definitions.lean: `complementaryCK : Prop := ∀ n f p, 1/20 ≤ p → p ≤ 1/2 → information f p ≤ log 2 − binaryEntropy p`, `CourtadeKumar`, `assemble_conditional (low : lowNoiseCK) (high : complementaryCK) : CourtadeKumar`.

## TARGETS (exact statements)
```lean
/-- Sections 5–6: the CK bound for 1/20 ≤ p ≤ 1/2. -/
theorem complementary_proved : complementaryCK
/-- Theorem thm:main: the Courtade–Kumar inequality. -/
theorem courtadeKumar_proved : CourtadeKumar
```
with `courtadeKumar_proved := assemble_conditional lowNoise_proved complementary_proved`.

## Proof plan for complementary_proved
`intro n f p hp hp'`; ρ := 1 − 2p ∈ [0, 9/10]; m := avg (signOf f); F := signOf f.
1. `by_cases hm : 13/20 ≤ |m|` → `large_bias`.
2. `by_cases hc : ∃ i, 13/20 ≤ |fourierCoeff F {i}|`:
   obtain i; then n ≠ 0, write n = k + 1 (`cases n` — the case n = 0 is impossible since Fin 0 is empty; or `obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero`), let σ := Equiv.swap i (Fin.last k), g := relabel σ f.
   `information_relabel`: information g p = information f p. `fourierCoeff_comp_perm_singleton` (FourierCap.lean; note signOf (relabel σ f) = fun x => signOf f (x ∘ σ) definitionally) gives fourierCoeff (signOf g) {Fin.last k} = fourierCoeff F {σ.symm (Fin.last k)} = fourierCoeff F {i} (σ is an involution: `Equiv.swap_apply_right`/`Equiv.symm_swap`).
   `fourierCoeff_singleton_last` (Fourier.lean): fourierCoeff (signOf g) {last} = mean (sectionLast g true) − mean (sectionLast g false). So `large_coordinate_last` applies to g (with hρ : ρ ≤ 9/10 from p ≥ 1/20).
3. Otherwise |m| ≤ 13/20 and ∀ i, |fourierCoeff F {i}| ≤ 13/20 (push_neg): `bias_inclusive_cap` gives m² + W₁(F) ≤ 31/40; then `by_cases 3/5 ≤ ρ`: `middle_range`, else `high_noise` (0 ≤ ρ from p ≤ 1/2).
Then `courtadeKumar_proved := assemble_conditional lowNoise_proved complementary_proved`.
Finally add at the end of the file (and keep them: they are informative, not warnings): nothing. (The gate's #print axioms audit is run separately.)
