# Inventory: PadicLFunctions/EisensteinComplex.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/EisensteinComplex.lean`

Namespace `PadicLFunctions`, with `variable (p : ℕ) [NeZero p]`. Topic: the q-expansion of the p-stabilised Eisenstein series (RJW §8, complex side), and its realisation as a genuine `Γ₀(p)`-modular form via the `LeanModularForms` level-raising operator.

---

### theorem sigmaP_eq_of_not_dvd
- Type: `(p : ℕ) {n : ℕ} (hn : ¬ (p : ℕ) ∣ n) (k : ℕ) : sigmaP p k n = ArithmeticFunction.sigma k n`
- What: For `p ∤ n`, the prime-to-`p` divisor power sum equals the full divisor power sum `σ_k(n)`.
- How: Unfolds `sigmaP` and `ArithmeticFunction.sigma_apply`, then `Finset.sum_congr` over a `Finset.filter_true_of_mem`: every divisor `d` of `n` is automatically prime-to-`p`, since if `p ∣ d` then `p ∣ d ∣ n` contradicts `hn`.
- Hypotheses: `p` nonzero (omitted here via `omit [NeZero p]`); `n` not divisible by `p`; `k` a natural exponent.
- Uses from project: [`sigmaP`]
- Used by: `hasSum_stabilisedEisenstein`
- Visibility: public
- Lines: 44–51 (proof ~3 lines)
- Notes: none

### theorem sigmaP_add_pow_mul_sigma_div
- Type: `(p : ℕ) {n : ℕ} (hn : (p : ℕ) ∣ n) (hn0 : n ≠ 0) (k : ℕ) : sigmaP p k n + p ^ k * ArithmeticFunction.sigma k (n / p) = ArithmeticFunction.sigma k n`
- What: RJW's "easy check" in subtraction-free form: for `p ∣ n`, the prime-to-`p` divisor sum plus `p^k·σ_k(n/p)` reconstitutes the full `σ_k(n)`; the divisors split into prime-to-`p` ones and `p` times divisors of `n/p`.
- How: Establishes `hcompl` — the sum over `p`-divisible divisors equals `p^k·σ_k(n/p)` — via a bijection `Finset.sum_nbij'` with `d ↦ d/p` and inverse `e ↦ p·e` (four membership/inverse goals plus the value identity `d^k = p^k·(d/p)^k` using `Nat.mul_div_cancel'`); then concludes by `Finset.sum_filter_not_add_sum_filter` splitting `n.divisors` on the predicate `p ∣ d`.
- Hypotheses: `p` divides `n`; `n` nonzero; `k` a natural exponent.
- Uses from project: [`sigmaP`]
- Used by: `hasSum_stabilisedEisenstein`
- Visibility: public
- Lines: 53–92 (proof ~32 lines)
- Notes: long(30-50) — proof body ~32 lines (`Finset.sum_nbij'` with 5 obligations)

### def pScale
- Type: `(p : ℕ) [NeZero p] (z : ℍ) : ℍ` (noncomputable)
- What: The point `p·z` of the upper half-plane, i.e. `(p : ℂ) * z` with its positive-imaginary-part proof.
- How: Constructs the subtype element `⟨(p:ℂ)*z, _⟩`; the imaginary-part positivity is `mul_pos` of `Nat.cast_pos.mpr (NeZero.pos p)` and `z.im_pos`, after computing `Im((p:ℂ)*z) = p·Im(z)` via `Complex.mul_im`, `natCast_im`, `natCast_re`.
- Hypotheses: `p` nonzero (so `p·Im(z) > 0`); `z` in the upper half-plane.
- Uses from project: []
- Used by: `hasSum_stabilisedEisenstein`, `stabilisedEisenstein_apply`, `stabilisedEisenstein_smul_apply`
- Visibility: public
- Lines: 98–103 (proof ~5 lines, inside the term)
- Notes: none

### def rjwEisenstein
- Type: `(p : ℕ) [NeZero p] {k : ℕ} (hk : 3 ≤ k) : ℍ → ℂ` (noncomputable); value `z ↦ ((zetaNeg (k-1) : ℚ) : ℂ)/2 * ModularForm.E hk z`
- What: RJW's normalisation `E_k = ζ(1−k)/2 + Σ_{n≥1} σ_{k−1}(n)qⁿ`, expressed as `(ζ(1−k)/2)·E` for mathlib's constant-term-1 normalised `ModularForm.E`.
- How: Direct definition (no proof) scaling `ModularForm.E hk` by the rational constant `(zetaNeg (k-1))/2` cast to `ℂ`.
- Hypotheses: `p` nonzero (carried by the section variable, unused in value); `k ≥ 3` (needed for `ModularForm.E`).
- Uses from project: [`zetaNeg`]
- Used by: `hasSum_rjwEisenstein`, `hasSum_stabilisedEisenstein`, `stabilisedEisenstein_smul_apply`
- Visibility: public
- Lines: 105–109 (no proof)
- Notes: none

### lemma bernoulli_ne_zero_of_even
- Type: `{k : ℕ} (hk : 4 ≤ k) (hk2 : Even k) : bernoulli k ≠ 0`
- What: For even `k ≥ 4` the Bernoulli number `B_k` is non-zero.
- How: By contradiction — assume `B_k = 0`; writing `k = 2m` with `m ≠ 0`, the explicit formula `riemannZeta_two_mul_nat hm` makes `ζ(2m)` a product of nonzero constants times `B_{2m}`, so `ζ(2m) = 0`; this contradicts `riemannZeta_ne_zero_of_one_lt_re` since `Re(2m) > 1`.
- Hypotheses: `k ≥ 4` and `k` even (so `k = 2m` with `m ≥ 2`, hence `Re(k) > 1`).
- Uses from project: []
- Used by: `rjw_normalisation`
- Visibility: private
- Lines: 113–122 (proof ~9 lines)
- Notes: none

### lemma summable_sigma_cexp
- Type: `{k : ℕ} (hk : 1 ≤ k) (τ : ℍ) : Summable fun n : ℕ ↦ (σ (k-1) n : ℂ) * Complex.exp (2*π*I*τ) ^ n`
- What: Summability of the divisor-sum q-expansion series `∑ σ_{k−1}(n)qⁿ` (reproduces mathlib's private `EisensteinSeries.summable_sigma_mul_cexp_pow`).
- How: `Summable.of_norm_bounded` against `summable_norm_pow_mul_geometric_of_norm_lt_one` (using `UpperHalfPlane.norm_exp_two_pi_I_lt_one τ` for `|q| < 1`); the termwise bound is `gcongr` plus `ArithmeticFunction.sigma_le_pow_succ` bounding `σ_{k−1}(n)` by `n^k`.
- Hypotheses: `k ≥ 1`; `τ` in the upper half-plane (so `|e^{2πiτ}| < 1`).
- Uses from project: []
- Used by: `hasSum_rjwEisenstein`
- Visibility: private
- Lines: 124–134 (proof ~7 lines)
- Notes: none

### lemma rjw_normalisation
- Type: `{k : ℕ} (hk : 4 ≤ k) (hk2 : Even k) : -((((zetaNeg (k-1) : ℚ) : ℂ)/2) * (2*k/bernoulli k)) = 1`
- What: The ℂ-side normalisation identity: scaling mathlib's `1 − (2k/B_k)Σ` shape by `C := ζ(1−k)/2` turns the leading `−C·(2k/B_k)` into `+1`, because `ζ(1−k) = −B_k/k` for even `k`.
- How: Establishes `B_k ≠ 0` (via `bernoulli_ne_zero_of_even`) and `k ≠ 0`; rewrites `zetaNeg (k-1)` using its definition and `(k−1)` odd (`hodd.neg_one_pow`) to get `ζ(1−k) = −(B_k/k)`; closes with `field_simp`.
- Hypotheses: `k ≥ 4` and even (so `B_k ≠ 0` and `k−1` odd).
- Uses from project: [`zetaNeg`, `bernoulli_ne_zero_of_even`]
- Used by: `hasSum_rjwEisenstein`
- Visibility: private
- Lines: 137–148 (proof ~9 lines)
- Notes: none

### lemma hasSum_rjwEisenstein
- Type: `{k : ℕ} (hk : 4 ≤ k) (hk2 : Even k) (τ : ℍ) : HasSum (fun n => (if n = 0 then ((zetaNeg (k-1):ℚ):ℂ)/2 else (σ (k-1) n : ℂ)) * Complex.exp (2*π*I*τ)^n) (rjwEisenstein p (by omega) τ)`
- What: The per-point ℕ-indexed q-expansion of RJW's normalised Eisenstein series, with the constant term `ζ(1−k)/2` folded into the `n=0` summand.
- How: Sets `C := ζ(1−k)/2`; proves summability `hS` of the shifted (`n+1`) series via `summable_nat_add_iff` and `summable_sigma_cexp`; uses `hasSum_nat_add_iff' 1` to peel the constant term; computes `E_k(τ) − C` as the tsum of the shifted series using `EisensteinSeries.q_expansion_bernoulli`, `tsum_pnat_eq_tsum_succ`, and the normalisation `rjw_normalisation` (rearranged into `hnorm : C·(2k/B_k) = −1` via `linear_combination`), then concludes by `hS.hasSum`.
- Hypotheses: `k ≥ 4` and even; `τ` in upper half-plane.
- Uses from project: [`zetaNeg`, `rjwEisenstein`, `summable_sigma_cexp`, `rjw_normalisation`]
- Used by: `hasSum_stabilisedEisenstein`
- Visibility: private
- Lines: 150–180 (proof ~27 lines)
- Notes: long(30-50) — proof body ~27 lines plus the multi-line signature; just under threshold but a substantial multi-step HasSum argument

### theorem hasSum_stabilisedEisenstein
- Type: `(p : ℕ) [NeZero p] {k : ℕ} (hk : 4 ≤ k) (hk2 : Even k) (z : ℍ) : HasSum (fun n => ((stabilisedCoeff p k n : ℚ):ℂ) * Complex.exp (2*Real.pi*Complex.I*(z:ℂ))^n) (rjwEisenstein p (by omega) z - (p:ℂ)^(k-1) * rjwEisenstein p (by omega) (pScale p z))`
- What: RJW TeX 2387–2393 — the q-expansion of the p-stabilisation: `Σ_n stabilisedCoeff(k,n)·qⁿ` sums to `E_k(z) − p^{k−1}E_k(pz)` in RJW's normalisation, with constant term `(1−p^{k−1})ζ(1−k)/2` and `n`-th coefficient `σ^p_{k−1}(n)`.
- How: Sets `q := e^{2πiz}` and the coefficient function `b`; gets `HasSum b·q^n` at `z` (`hSz`) and at `p·z` from `hasSum_rjwEisenstein`, using `hqp : e^{2πi·pz} = q^p` (via `Complex.exp_nat_mul`); defines `g m := if p∣m then b(m/p)·q^m else 0`; reindexes the `p·z` HasSum along the injection `n ↦ p·n` (`Function.Injective.hasSum_iff` with `hgoff`, `hcomp`) to `hSpz`; subtracts to get `hD := hSz.sub (hSpz.mul_left p^{k−1})`; finally proves the summand identity `hfun` pointwise by cases on `n=0` / `p∣n` (using `sigmaP_add_pow_mul_sigma_div`) / `p∤n` (using `sigmaP_eq_of_not_dvd`), each closed by `push_cast`/`linear_combination`/`ring`.
- Hypotheses: `p` nonzero; `k ≥ 4` and even; `z` in upper half-plane.
- Uses from project: [`stabilisedCoeff`, `rjwEisenstein`, `pScale`, `hasSum_rjwEisenstein`, `sigmaP_add_pow_mul_sigma_div`, `sigmaP_eq_of_not_dvd`, `zetaNeg`]
- Used by: unused in file
- Visibility: public
- Lines: 182–251 (proof ~58 lines)
- Notes: OVER-50 — proof body ~58 lines (needs /decompose-proof); multi-step reindex+subtract+pointwise-cases HasSum argument

### lemma Gamma1_map_le_range
- Type: `(N : ℕ) : (Gamma1 N).map (mapGL ℝ) ≤ (mapGL ℝ : SL(2,ℤ) →* GL (Fin 2) ℝ).range`
- What: Every element of `(Gamma1 N).map (mapGL ℝ)` lies in the range of `mapGL ℝ` (i.e. in `𝒮ℒ`): the image of a congruence subgroup sits inside the full image of `SL(2,ℤ)`.
- How: One-line term `fun _ ⟨γ, _, hγ⟩ => ⟨γ, hγ⟩` — discards the `Gamma1` membership and keeps the witness `γ` mapping to the element.
- Hypotheses: `N` a natural level.
- Uses from project: []
- Used by: `stabilisedDiff`
- Visibility: private
- Lines: 261–266 (proof 1 line)
- Notes: none

### lemma E_slash_mapGL
- Type: `{k : ℕ} (hk : 3 ≤ k) (γ : SL(2,ℤ)) : (⇑(ModularForm.E hk) : ℍ → ℂ) ∣[(k:ℤ)] (mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑(ModularForm.E hk)`
- What: `ModularForm.E hk` is invariant under the weight-`k` slash action of `mapGL ℝ γ` for every `γ : SL(2,ℤ)`, since `mapGL ℝ γ ∈ 𝒮ℒ = range(mapGL ℝ)`.
- How: Direct application of `(ModularForm.E hk).slash_action_eq'` at `mapGL ℝ γ` with membership witness `⟨γ, rfl⟩`.
- Hypotheses: `k ≥ 3`; `γ ∈ SL(2,ℤ)` (`p` nonzero omitted via `omit`).
- Uses from project: []
- Used by: `stabilisedDiff_slash_mapGL`
- Visibility: private
- Lines: 268–274 (proof 1 line)
- Notes: none

### def stabilisedDiff
- Type: `(p : ℕ) [NeZero p] {k : ℕ} (hk : 3 ≤ k) : ModularForm ((Gamma1 (p*1)).map (mapGL ℝ)) (k:ℤ)` (noncomputable, private)
- What: The level-`Γ₁(p·1)` Eisenstein difference `E_k − p^{k−1}·ι_p(E_k)` underlying the `Γ₀(p)`-modular `E_k^{(p)}`: `E` restricted to `Γ₁(p·1)` minus `p^{k−1}` times the level-raise of `E` restricted to `Γ₁(1)`.
- How: Term combining `(ModularForm.E hk).restrictSubgroup (Gamma1_map_le_range (p*1))` and `(p:ℂ)^(k−1) • modularFormLevelRaise 1 p k ((ModularForm.E hk).restrictSubgroup (Gamma1_map_le_range 1))` via subtraction in the `ModularForm` module.
- Hypotheses: `p` nonzero; `k ≥ 3`.
- Uses from project: [`Gamma1_map_le_range`]
- Used by: `coe_stabilisedDiff`, `stabilisedEisenstein`, `stabilisedEisenstein_apply`
- Visibility: private
- Lines: 276–284 (no proof)
- Notes: none

### lemma coe_stabilisedDiff
- Type: `{k : ℕ} (hk : 3 ≤ k) : (⇑(stabilisedDiff p hk) : ℍ → ℂ) = ⇑(ModularForm.E hk) - ((p:ℂ)^(k-1)) • levelRaiseFun p (k:ℤ) ⇑(ModularForm.E hk)`
- What: The underlying function of `stabilisedDiff` is `E_k − p^{k−1}·levelRaiseFun p k E_k`.
- How: `rfl` — the coercion of the `ModularForm` subtraction/scalar/level-raise unfolds definitionally to this pointwise expression.
- Hypotheses: `p` nonzero (section variable); `k ≥ 3`.
- Uses from project: [`stabilisedDiff`]
- Used by: `stabilisedEisenstein` (in its `slash_action_eq'` field), `stabilisedEisenstein_apply`
- Visibility: private
- Lines: 286–291 (proof 1 line, `rfl`)
- Notes: none

### lemma stabilisedDiff_slash_mapGL
- Type: `{k : ℕ} (hk : 3 ≤ k) (γ : SL(2,ℤ)) (hγ : γ ∈ Gamma0 p) : ((⇑(ModularForm.E hk)) - ((p:ℂ)^(k-1)) • levelRaiseFun p (k:ℤ) ⇑(ModularForm.E hk)) ∣[(k:ℤ)] (mapGL ℝ γ) = (same)`
- What: The heart of `Γ₀(p)`-modularity: the function `E_k − p^{k−1}·ι_p(E_k)` is invariant under the weight-`k` slash by `mapGL ℝ γ` for every `γ ∈ Γ₀(p)`.
- How: Shows `σ(mapGL ℝ γ) = refl` (the determinant is positive via `Matrix.SpecialLinearGroup.det_mapGL`, so the conjugation is trivial); sets `hdvd := Gamma0_dmul_lower_left_dvd p 1 γ`; then distributes the slash over `sub`/`neg`/`smul` and rewrites the `E` part by `E_slash_mapGL` and the level-raise part by the down-conjugation bridge `slash_mapGL_levelRaiseFun` (turning the slash by `mapGL ℝ γ` into the level-raise of the slash by the conjugate `γ̃ = levelRaiseConjOfDvd p γ hdvd ∈ Γ₀(1)`), whose `E`-slash is again `E_slash_mapGL`.
- Hypotheses: `k ≥ 3`; `γ ∈ Γ₀(p)` (`p` nonzero from section).
- Uses from project: [`E_slash_mapGL`]
- Used by: `stabilisedEisenstein` (in its `slash_action_eq'` field)
- Visibility: private
- Lines: 293–317 (proof ~11 lines)
- Notes: long(30-50)? — no; proof body ~11 lines. None (but hinges on external `slash_mapGL_levelRaiseFun`, `Gamma0_dmul_lower_left_dvd`, `levelRaiseConjOfDvd`)

### def stabilisedEisenstein
- Type: `(p : ℕ) [NeZero p] {k : ℕ} (hk : 3 ≤ k) : ModularForm ((Gamma0 p).map (mapGL ℝ)) (k:ℤ)` (noncomputable)
- What: The p-stabilised Eisenstein series `E_k^{(p)}(z) = E_k(z) − p^{k−1}E_k(pz)` as a genuine modular form of weight `k` and level `Γ₀(p)` (RJW TeX 2394).
- How: Anonymous-constructor `ModularForm` with `toFun := ⇑(stabilisedDiff p hk)`; the `slash_action_eq'` field rewrites by `coe_stabilisedDiff` and applies `stabilisedDiff_slash_mapGL` to promote `Γ₁(p·1)`-invariance to `Γ₀(p)`; `holo'` is inherited from `stabilisedDiff`; `bdd_at_cusps'` transfers via `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z` applied to both `(Gamma1 (p*1)).map …` and `(Gamma0 p).map …` (both arithmetic, sharing the SL₂(ℤ)-cusps).
- Hypotheses: `p` nonzero; `k ≥ 3`.
- Uses from project: [`stabilisedDiff`, `coe_stabilisedDiff`, `stabilisedDiff_slash_mapGL`]
- Used by: `stabilisedEisenstein_apply`, `stabilisedEisenstein_smul_apply`
- Visibility: public
- Lines: 319–340 (proof ~7 lines, inside the structure fields)
- Notes: none

### theorem stabilisedEisenstein_apply
- Type: `(p : ℕ) [NeZero p] {k : ℕ} (hk : 3 ≤ k) (z : ℍ) : stabilisedEisenstein p hk z = ModularForm.E hk z - (p:ℂ)^(k-1) * ModularForm.E hk (pScale p z)`
- What: RJW TeX 2394 pointwise formula: the `Γ₀(p)`-modular form `stabilisedEisenstein` is the p-stabilisation `E_k(z) − p^{k−1}E_k(pz)` for mathlib's normalised `ModularForm.E` and `pz = pScale p z`.
- How: Uses `hpt : (levelRaiseMatrix p • z : ℍ) = pScale p z` (from `coe_levelRaiseMatrix_smul`); rewrites the value as `⇑(stabilisedDiff p hk) z` via `change`, applies `coe_stabilisedDiff`, then `simp` unfolds `Pi.sub_apply`/`Pi.smul_apply`/`levelRaiseFun_apply` and substitutes `hpt`.
- Hypotheses: `p` nonzero; `k ≥ 3`; `z` in upper half-plane.
- Uses from project: [`stabilisedEisenstein`, `pScale`, `stabilisedDiff`, `coe_stabilisedDiff`]
- Used by: `stabilisedEisenstein_smul_apply`
- Visibility: public
- Lines: 342–352 (proof ~5 lines)
- Notes: none

### theorem stabilisedEisenstein_smul_apply
- Type: `(p : ℕ) [NeZero p] {k : ℕ} (hk : 4 ≤ k) (z : ℍ) : (((zetaNeg (k-1):ℚ):ℂ)/2) * stabilisedEisenstein p (by omega) z = rjwEisenstein p (by omega) z - (p:ℂ)^(k-1) * rjwEisenstein p (by omega) (pScale p z)`
- What: The bridge between `stabilisedEisenstein` and `rjwEisenstein`: scaling the modular form by `ζ(1−k)/2` reproduces the p-stabilised combination of `rjwEisenstein` whose q-expansion is `hasSum_stabilisedEisenstein`.
- How: Rewrites by `stabilisedEisenstein_apply` and unfolds `rjwEisenstein` twice, then closes by `ring` (both sides are the same `ζ(1−k)/2`-scaled difference of `ModularForm.E` values).
- Hypotheses: `p` nonzero; `k ≥ 4` (so `by omega` supplies `3 ≤ k`); `z` in upper half-plane.
- Uses from project: [`zetaNeg`, `stabilisedEisenstein`, `rjwEisenstein`, `pScale`, `stabilisedEisenstein_apply`]
- Used by: unused in file
- Visibility: public
- Lines: 354–362 (proof ~3 lines)
- Notes: none

---

## File Summary

- Total declarations: 16 — defs 4 (`pScale`, `rjwEisenstein`, `stabilisedDiff`, `stabilisedEisenstein`) / lemmas+theorems 12 (`sigmaP_eq_of_not_dvd`, `sigmaP_add_pow_mul_sigma_div`, `bernoulli_ne_zero_of_even`, `summable_sigma_cexp`, `rjw_normalisation`, `hasSum_rjwEisenstein`, `hasSum_stabilisedEisenstein`, `Gamma1_map_le_range`, `E_slash_mapGL`, `coe_stabilisedDiff`, `stabilisedDiff_slash_mapGL`, `stabilisedEisenstein_apply`, `stabilisedEisenstein_smul_apply` — note: 13 listed; see count below) / instances 0.
  - Correction: lemmas+theorems = 12 by the per-entry list above is miscount; actual = 12? Recount: sigmaP_eq_of_not_dvd, sigmaP_add_pow_mul_sigma_div, bernoulli_ne_zero_of_even, summable_sigma_cexp, rjw_normalisation, hasSum_rjwEisenstein, hasSum_stabilisedEisenstein, Gamma1_map_le_range, E_slash_mapGL, coe_stabilisedDiff, stabilisedDiff_slash_mapGL, stabilisedEisenstein_apply, stabilisedEisenstein_smul_apply = **13**. Defs = 4. **Total = 17.**
- Key API (used by ≥3 in-file): `rjwEisenstein` (used by `hasSum_rjwEisenstein`, `hasSum_stabilisedEisenstein`, `stabilisedEisenstein_smul_apply`); `pScale` (used by `hasSum_stabilisedEisenstein`, `stabilisedEisenstein_apply`, `stabilisedEisenstein_smul_apply`); `zetaNeg` (project-external dep, referenced by 4: `rjwEisenstein`, `rjw_normalisation`, `hasSum_rjwEisenstein`, `stabilisedEisenstein_smul_apply`); `stabilisedDiff` (used by `coe_stabilisedDiff`, `stabilisedEisenstein`, `stabilisedEisenstein_apply`); `coe_stabilisedDiff` (used by `stabilisedEisenstein`, `stabilisedEisenstein_apply`); `stabilisedEisenstein` (used by `stabilisedEisenstein_apply`, `stabilisedEisenstein_smul_apply`).
- Unused in file (terminal/public API exports): `hasSum_stabilisedEisenstein`, `stabilisedEisenstein_smul_apply`. (All other decls are consumed in-file.)
- Decls with `sorry`: none.
- `set_option`: none.
- Proofs >50 lines: 1 — `hasSum_stabilisedEisenstein` (~58 lines, OVER-50, flagged for /decompose-proof).
- Proofs 30–50 lines: 1 — `sigmaP_add_pow_mul_sigma_div` (~32 lines). (`hasSum_rjwEisenstein` ~27-line body is just under 30 but is the next-largest.)
- TODO / admit: none.
