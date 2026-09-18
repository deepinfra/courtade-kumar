# TASK: CK/Fourier.lean — Boolean Fourier analysis on Cube n (manuscript Sec. 5.4 basics; used by the complementary branch)

Imports: `import CK.Sections`, `import CK.AvgLemmas`, `import CK.Relabel` (read Semantics.lean, Sections.lean, AvgLemmas.lean first).
Conventions: Cube n = Fin n → Bool; `sign b = if b then 1 else -1`; `avg v = (∑ x, v x)/2^n`; `sectionLast f s w = f (Fin.snoc w s)`;
`mean f = avg (fun x => indicator (f x))`; `mean_snoc` (Sections.lean) : mean f = (mean (sectionLast f true) + mean (sectionLast f false))/2 (check exact form).

## DEFINITIONS (use exactly these names/types)
```lean
def chi {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : ℝ := ∏ i ∈ S, sign (x i)
def fourierCoeff {n : ℕ} (F : Cube n → ℝ) (S : Finset (Fin n)) : ℝ := avg (fun x => F x * chi S x)
def weight {n : ℕ} (F : Cube n → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = k), fourierCoeff F S ^ 2
def signOf {n : ℕ} (f : BooleanFunction n) : Cube n → ℝ := fun x => sign (f x)
def negCube {n : ℕ} (x : Cube n) : Cube n := fun i => !(x i)      -- x ↦ −x
```
## TARGETS (exact statements; `n` implicit throughout, `F G : Cube n → ℝ`)
```lean
theorem chi_empty (x : Cube n) : chi ∅ x = 1
theorem chi_mul_self (S : Finset (Fin n)) (x : Cube n) : chi S x * chi S x = 1
theorem chi_mul (S T : Finset (Fin n)) (x : Cube n) : chi S x * chi T x = chi (symmDiff S T) x
theorem avg_chi (S : Finset (Fin n)) : avg (chi S) = if S = ∅ then 1 else 0
theorem chi_orthonormal (S T : Finset (Fin n)) : avg (fun x => chi S x * chi T x) = if S = T then 1 else 0
/-- Σ_S χ_S(x)χ_S(y) = 2^n·[x = y]. -/
theorem sum_chi_mul_chi (x y : Cube n) : (∑ S : Finset (Fin n), chi S x * chi S y) = if x = y then (2:ℝ)^n else 0
theorem fourier_expansion (F : Cube n → ℝ) (x : Cube n) : F x = ∑ S : Finset (Fin n), fourierCoeff F S * chi S x
theorem plancherel (F G : Cube n → ℝ) : avg (fun x => F x * G x) = ∑ S : Finset (Fin n), fourierCoeff F S * fourierCoeff G S
theorem parseval (F : Cube n → ℝ) : avg (fun x => F x ^ 2) = ∑ S : Finset (Fin n), fourierCoeff F S ^ 2
theorem weight_nonneg (F : Cube n → ℝ) (k : ℕ) : 0 ≤ weight F k
theorem sum_weight (F : Cube n → ℝ) : ∑ k ∈ Finset.range (n + 1), weight F k = ∑ S : Finset (Fin n), fourierCoeff F S ^ 2
theorem fourierCoeff_empty (F : Cube n → ℝ) : fourierCoeff F ∅ = avg F
theorem weight_zero (F : Cube n → ℝ) : weight F 0 = (avg F) ^ 2
theorem weight_one (F : Cube n → ℝ) : weight F 1 = ∑ i : Fin n, fourierCoeff F {i} ^ 2
theorem fourierCoeff_add (F G : Cube n → ℝ) (S) : fourierCoeff (fun x => F x + G x) S = fourierCoeff F S + fourierCoeff G S
theorem fourierCoeff_const_mul (c : ℝ) (F : Cube n → ℝ) (S) : fourierCoeff (fun x => c * F x) S = c * fourierCoeff F S
theorem fourierCoeff_const (c : ℝ) (S : Finset (Fin n)) : fourierCoeff (fun _ => c) S = if S = ∅ then c else 0
theorem signOf_sq (f : BooleanFunction n) (x : Cube n) : signOf f x ^ 2 = 1
theorem signOf_eq (f : BooleanFunction n) (x : Cube n) : signOf f x = 2 * indicator (f x) - 1
theorem avg_signOf (f : BooleanFunction n) : avg (signOf f) = 2 * mean f - 1
theorem abs_signOf (f : BooleanFunction n) (x : Cube n) : |signOf f x| = 1
/-- nonconstant coefficients of the indicator are half those of the sign function -/
theorem fourierCoeff_indicator (f : BooleanFunction n) (S : Finset (Fin n)) (hS : S ≠ ∅) :
    fourierCoeff (fun x => indicator (f x)) S = fourierCoeff (signOf f) S / 2
/-- χ_S(−x) = (−1)^{|S|} χ_S(x) -/
theorem chi_negCube (S : Finset (Fin n)) (x : Cube n) : chi S (negCube x) = (-1) ^ S.card * chi S x
theorem avg_comp_negCube (v : Cube n → ℝ) : avg (fun x => v (negCube x)) = avg v
theorem fourierCoeff_comp_negCube (F : Cube n → ℝ) (S) : fourierCoeff (fun x => F (negCube x)) S = (-1) ^ S.card * fourierCoeff F S
/-- the singleton coefficient at the last coordinate is the difference of section means (b_i = μ₁ − μ₀). -/
theorem fourierCoeff_singleton_last (f : BooleanFunction (n + 1)) :
    fourierCoeff (signOf f) {Fin.last n} = mean (sectionLast f true) - mean (sectionLast f false)
/-- for S not containing the last coordinate, the coefficient is the average of the two sections' coefficients -/
theorem fourierCoeff_castSucc_image (F : Cube (n + 1) → ℝ) (S : Finset (Fin n)) :
    fourierCoeff F (S.map Fin.castSuccEmb) =
      (fourierCoeff (fun w => F (Fin.snoc w true)) S + fourierCoeff (fun w => F (Fin.snoc w false)) S) / 2
```
(If `Fin.castSuccEmb` is not the right name at this pin, use `Finset.map ⟨Fin.castSucc, Fin.castSucc_injective n⟩` or `S.image Fin.castSucc`; state the lemma with whichever embedding you use and say so.)

## Proof hints
- avg of a product over coordinates: Σ_{x : Cube n} ∏_i g_i (x i) = ∏_i Σ_{b : Bool} g_i b (`Fintype.prod_sum` as in `kernel_row_sum`, or `Finset.prod_univ_sum`).
  For `avg_chi` with S ≠ ∅: write chi S x = ∏_i (if i ∈ S then sign (x i) else 1); the factor at i ∈ S is sign true + sign false = 0.
- `sum_chi_mul_chi`: chi S x * chi S y = ∏_{i∈S} (sign (x i) * sign (y i)); Σ_S ∏_{i∈S} a_i = ∏_i (1 + a_i) (`Finset.prod_one_add` with s = univ, sum over `univ.powerset`;
  `Finset.powerset_univ`); 1 + sign(x i)·sign(y i) = 2 if x i = y i else 0.
- `fourier_expansion`: Σ_S fourierCoeff F S · chi S x = Σ_S avg(F·chi S)·chi S x = avg_y F y · Σ_S chi S y chi S x = avg_y F y · 2^n [y = x] = F x.
- plancherel/parseval from the expansion: avg(F G) = avg(F · Σ_S Ĝ(S) χ_S) = Σ_S Ĝ(S) avg(F χ_S) = Σ_S F̂(S) Ĝ(S).
- `sum_weight`: `Finset.sum_fiberwise`-type lemma (`Finset.sum_fiberwise_of_maps_to` with the map S ↦ S.card into range (n+1); card ≤ n by `Finset.card_le_univ`).
- `weight_one`: the filter {S | card = 1} is the image of i ↦ {i} (`Finset.card_eq_one`), sum over it via `Finset.sum_image` (injective).
- `fourierCoeff_singleton_last`: chi {last} x = sign (x last); split the sum over Cube (n+1) with `Fin.snocEquiv` as in `posterior_snoc` (Sections.lean);
  signOf f (snoc w s) = 2·indicator(sectionLast f s w) − 1; use `avg_snoc` and `mean` definitions.
- `fourierCoeff_castSucc_image`: chi (S.map castSucc) (snoc w s) = chi S w; split with `Fin.snocEquiv`, `Fin.snoc_castSucc`.
