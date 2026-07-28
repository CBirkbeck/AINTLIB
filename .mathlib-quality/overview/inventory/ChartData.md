# Inventory — `projects/AdicSpaces/Adic spaces/FarguesFontaine/ChartData.lean`

1674 lines. Namespace `FarguesFontaine`. Imports `«Adic spaces».FarguesFontaine.SheafyBI`.
Whole file is inside `noncomputable section` and carries the section variables
`(p : ℕ) [Fact p.Prime]`, `(F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
[UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]`,
`(ϖ : PseudoUniformizer F)`, and from line 513 also
`{ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}`.
Every entry below silently assumes those.

---

### `theorem isAdic_idealToTop_of_isAdic`
- **Type**: `{R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {I : Ideal R} (hadic : IsAdic I) : IsAdic (idealToTop I)`
- **What**: If the topology of `R` is `I`-adic, then the subspace topology on the top subring `⊤ : Subring R` is adic for the transported ideal `idealToTop I`.
- **How**: `isAdic_iff` splits the goal into "all powers open" and "some power inside each nbhd of 0". `idealToTop_pow_eq_preimage` identifies `(idealToTop I)^n` with the `Subtype.val`-preimage of `I^n`, so openness is `IsOpen.preimage continuous_subtype_val`; for the second half `nhds_subtype_eq_comap` + `Filter.mem_comap` reduce to the ambient basis `hadic.hasBasis_nhds_zero`.
- **Hypotheses**: `IsAdic I` for the ambient topology (a *given* adic ideal, not the ideal's own canonical topology — that is the point of the lemma).
- **Uses from project**: `idealToTop`, `idealToTop_pow_eq_preimage` (both `TateAlgebraTopology.lean`).
- **Used by**: `podAinf`.
- **Visibility**: public
- **Lines**: 51–62 (proof 10 lines)
- **Notes**: general-purpose transfer lemma, no `p`/`F` dependence; the project already has `isAdic_idealToTop` in `TateAlgebraTopology.lean` for the canonical case.

### `def podAinf`
- **Type**: `PairOfDefinition (Ainf p F)`
- **What**: The `(⊤, (p, [ϖ]))` pair of definition on `A_inf` — ring of definition all of `A_inf`, ideal of definition `I_inf = (p,[ϖ])` pushed into `⊤`. This is the non-Tate Huber pair `(A_inf, A_inf)` over which the two Fargues–Fontaine charts are rational-localization data.
- **How**: Field-by-field: `isOpen := isOpen_univ`; `fg := idealToTop_fg _ (Submodule.fg_span (Set.toFinite _))` since `I_inf` is spanned by the two-element set `{p,[ϖ]}`; `isAdic := isAdic_idealToTop_of_isAdic (isAdic_Iinf p F ϖ)`.
- **Hypotheses**: the ambient perfectoid data; any pseudo-uniformizer `ϖ` works because the `(p,[ϖ])`-filtrations for different `ϖ` are mutually cofinal.
- **Uses from project**: `Ainf`, `Iinf`, `isAdic_Iinf` (`AinfHuber.lean`), `idealToTop`, `idealToTop_fg` (`TateAlgebraTopology.lean`), `PairOfDefinition` (`HuberRings.lean`), `isAdic_idealToTop_of_isAdic`.
- **Used by**: `divBySIdeal`, `span_chartMonomials_le_divBySIdeal`, `chartData`, `map_locSubring_chartData`, `map_locSubring_le_blocUnitBall`, `wI_le_of_mem_locIdeal_pow`, `exists_locNhd_le_ball`, `tendsto_chartToBIProd`, `ball_le_locNhd`.
- **Visibility**: public
- **Lines**: 64–71 (definition 6 lines)
- **Notes**: headline definition listed in the module docstring.

### `theorem divByS_eq_mul_inv`
- **Type**: `{A : Type*} [CommRing A] (t s : A) : divByS t s = algebraMap A (Localization.Away s) t * IsLocalization.mk' (Localization.Away s) 1 (⟨s, ⟨1, pow_one s⟩⟩ : Submonoid.powers s)`
- **What**: Normal form for fractions in `Localization.Away s`: `t/s = (image of t) · (1/s)`.
- **How**: Unfold `divByS` and apply `IsLocalization.mk'_eq_mul_mk'_one`.
- **Hypotheses**: only `CommRing A`.
- **Uses from project**: `divByS` (`LocalizationTopology.lean`).
- **Used by**: `divByS_mul_left`, `divByS_add`.
- **Visibility**: public
- **Lines**: 73–78 (proof 1 line)
- **Notes**: none.

### `theorem divByS_mul_left`
- **Type**: `{A : Type*} [CommRing A] (c t s : A) : divByS (c * t) s = algebraMap A (Localization.Away s) c * divByS t s`
- **What**: A fraction with a factored numerator splits: `(c·t)/s = c·(t/s)`.
- **How**: Rewrite both sides through `divByS_eq_mul_inv`, then `map_mul` and `mul_assoc`.
- **Hypotheses**: only `CommRing A`.
- **Uses from project**: `divByS`, `divByS_eq_mul_inv`.
- **Used by**: `divBySIdeal` (the `smul_mem'` field), `span_chartMonomials_le_divBySIdeal` (both branches).
- **Visibility**: public
- **Lines**: 80–83 (proof 1 line)
- **Notes**: none.

### `theorem divByS_mul_cancel`
- **Type**: `{A : Type*} [CommRing A] (c s : A) : divByS (c * s) s = algebraMap A (Localization.Away s) c`
- **What**: The denominator cancels: `(c·s)/s = c` in `Localization.Away s`.
- **How**: Unfold `divByS` and use `IsLocalization.mk'_eq_iff_eq_mul` together with `map_mul`.
- **Hypotheses**: only `CommRing A`.
- **Uses from project**: `divByS`.
- **Used by**: `divBySIdeal` (the `zero_mem'` field).
- **Visibility**: public
- **Lines**: 85–88 (proof 1 line)
- **Notes**: none.

### `theorem divByS_add`
- **Type**: `{A : Type*} [CommRing A] (t t' s : A) : divByS (t + t') s = divByS t s + divByS t' s`
- **What**: Division by a fixed `s` is additive in the numerator.
- **How**: Three `divByS_eq_mul_inv` rewrites reduce to `map_add` and `add_mul` distributivity over the common factor `1/s`.
- **Hypotheses**: only `CommRing A`.
- **Uses from project**: `divByS`, `divByS_eq_mul_inv`.
- **Used by**: `divBySIdeal` (the `add_mem'` field).
- **Visibility**: public
- **Lines**: 90–93 (proof 1 line)
- **Notes**: none.

### `local instance (anonymous) : DecidableEq (Ainf p F)`
- **Type**: `DecidableEq (Ainf p F)`
- **What**: Classical decidable equality on `A_inf`, so that the two-element `Finset` literal `{p^{a+1}, [ϖ]^{b+1}}` in `chartT` elaborates.
- **How**: `Classical.decEq _`.
- **Hypotheses**: none (classical choice).
- **Uses from project**: `Ainf`.
- **Used by**: `chartT` (and therefore, transitively, every declaration mentioning `chartT`).
- **Visibility**: file-local (`noncomputable local instance`), anonymous
- **Lines**: 95 (1 line)
- **Notes**: `local` keeps it from leaking into downstream files.

### `def chartT`
- **Type**: `(a b : ℕ) : Finset (Ainf p F)`
- **What**: The numerator set of the chart datum, `T = {p^{a+1}, [ϖ]^{b+1}}` — the two "tray" elements whose fractions over `s` encode the two window inequalities `κ ≤ …` and `κ ≥ …`.
- **How**: Literal `Finset` insert/singleton, using the local `DecidableEq`.
- **Hypotheses**: none beyond the ambient setup.
- **Uses from project**: `Ainf`, `teichPi` (`AinfHuber.lean`).
- **Used by**: `span_chartMonomials_le_divBySIdeal`, `chartData`, `isRational_chartData`, `mem_rationalOpen_chartData_iff`, `windowU_zero_eq_rationalOpen`, `windowV_zero_eq_rationalOpen`, `map_locSubring_chartData`, `map_locSubring_le_blocUnitBall`, `wI_le_of_mem_locIdeal_pow`, `exists_locNhd_le_ball`, `tendsto_chartToBIProd`, `ball_le_locNhd`.
- **Visibility**: public
- **Lines**: 97–99 (definition 2 lines)
- **Notes**: none.

### `def chartS`
- **Type**: `(u v : ℕ) : Ainf p F`
- **What**: The single denominator of the chart datum, `s = p^u · [ϖ]^v`.
- **How**: Literal product of powers in `A_inf`.
- **Hypotheses**: none beyond the ambient setup.
- **Uses from project**: `Ainf`, `teichPi`.
- **Used by**: `span_chartMonomials_le_divBySIdeal`, `chartData`, `mem_rationalOpen_chartData_iff`, `windowU_zero_eq_rationalOpen`, `windowV_zero_eq_rationalOpen`, `chartS_pow_eq`, `isLocalization_chartS_Bloc`, `blocEquivAwayChartS`, `blocEquiv_divByS_teichPi`, `blocEquiv_divByS_p`, `blocEquivAwayChartS_algebraMap`, `map_locSubring_chartData`, `map_locSubring_le_blocUnitBall`, `wI_le_of_mem_locIdeal_pow`, `chartToBIProd`, `exists_locNhd_le_ball`, `chartTopology`, `tendsto_chartToBIProd`, `chartTopologicalRing`, `continuous_chartToBIProd`, `chartUniformity`, `chartIsUniformAddGroup`, `chartCompletionToBIProd`, `presheafChartToBIProd_coe`, `ball_le_locNhd`.
- **Visibility**: public
- **Lines**: 101–103 (definition 2 lines)
- **Notes**: the "single-denominator presentation" that makes the window a rational subset in Wedhorn's sense.

### `def divBySIdeal`
- **Type**: `(T : Finset (Ainf p F)) (s : Ainf p F) : Ideal (Ainf p F)`
- **What**: The set `{x ∈ A_inf : x/s ∈ locSubring (podAinf) T s}` — elements whose fraction over `s` already lies in the ring of definition of the localization — packaged as an ideal of `A_inf`. This is the object the openness condition `hopen` of `RationalLocData` is checked against.
- **How**: `zero_mem'` rewrites `0 = 0·s` and applies `divByS_mul_cancel` + `map_zero`; `add_mem'` is `divByS_add` + `add_mem` in the subring; `smul_mem'` uses `divByS_mul_left` to peel the scalar and then `algebraMap_A₀_subset_locSubring` to see the scalar's image (from `A₀ = ⊤`) inside `locSubring`, closing with `mul_mem`.
- **Hypotheses**: none beyond the ambient setup; `T`, `s` arbitrary.
- **Uses from project**: `Ainf`, `divByS`, `locSubring`, `algebraMap_A₀_subset_locSubring` (`LocalizationTopology.lean`), `podAinf`, `divByS_mul_cancel`, `divByS_add`, `divByS_mul_left`.
- **Used by**: `span_chartMonomials_le_divBySIdeal`.
- **Visibility**: public
- **Lines**: 105–129 (structure body 23 lines)
- **Notes**: the `Ideal` packaging is what lets `Ideal.span_le` do the generator-only work in `span_chartMonomials_le_divBySIdeal`.

### `def chartMonomials`
- **Type**: `(N : ℕ) : Finset (Ainf p F)`
- **What**: The degree-`N` monomials `p^i · [ϖ]^{N-i}` for `0 ≤ i ≤ N` — a finite generating set for `I_inf^N`.
- **How**: `(Finset.range (N+1)).image (fun i => p^i * teichPi^(N-i))`.
- **Hypotheses**: none.
- **Uses from project**: `Ainf`, `teichPi`.
- **Used by**: `Iinf_pow_le_span_chartMonomials`, `span_chartMonomials_le_divBySIdeal`, `isRational_chartData`, `gaussValue_le_of_mem_Iinf_pow`.
- **Visibility**: public
- **Lines**: 131–134 (definition 3 lines)
- **Notes**: truncated subtraction `N - i` is harmless because `i` ranges over `range (N+1)`.

### `theorem Iinf_pow_le_span_chartMonomials`
- **Type**: `(N : ℕ) : Iinf p F ϖ ^ N ≤ Ideal.span (chartMonomials p F ϖ N : Set (Ainf p F))`
- **What**: `I_inf^N = (p,[ϖ])^N` is contained in the ideal generated by the degree-`N` monomials. (The reverse containment is not needed.)
- **How**: Induction on `N`. Base: `1 = p^0[ϖ]^0` lies in `chartMonomials 0`, so `Ideal.span_singleton_one` + `Ideal.span_mono` gives `⊤ ≤ span`. Step: `pow_succ`, `Ideal.mul_mono` with the IH, then `Iinf` unfolds to `Ideal.span {p, [ϖ]}` and `Ideal.span_mul_span` + `Ideal.span_le` reduces to checking `g · (p^i[ϖ]^{N-i})` for `g ∈ {p, [ϖ]}`: for `g = p` it is the index-`(i+1)` monomial of degree `N+1`, for `g = [ϖ]` the index-`i` one, in each case via `Ideal.subset_span` with the exponent identity closed by `omega` and `pow_succ`/`ring`.
- **Hypotheses**: none.
- **Uses from project**: `Iinf`, `chartMonomials`, `teichPi`, `Ainf`.
- **Used by**: `chartData` (the `hopen` field), `isRational_chartData`, `gaussValue_le_of_mem_Iinf_pow`.
- **Visibility**: public
- **Lines**: 136–177 (proof 39 lines)
- **Notes**: proof >30 lines.

### `theorem span_chartMonomials_le_divBySIdeal`
- **Type**: `(u v a b : ℕ) : Ideal.span (chartMonomials p F ϖ (a+b+2) : Set (Ainf p F)) ≤ divBySIdeal p F ϖ (chartT p F ϖ a b) (chartS p F ϖ u v)`
- **What**: Every degree-`(a+b+2)` monomial, divided by `s = p^u[ϖ]^v`, already lies in the ring of definition of the localization. This is the numerical heart of the `hopen` condition.
- **How**: `Ideal.span_le` reduces to the generators `p^i[ϖ]^{a+b+2-i}`. Case `i ≤ a`: the `[ϖ]`-exponent is `≥ b+1`, so factor `= (p^i[ϖ]^{a+b+2-i-(b+1)})·[ϖ]^{b+1}`, use `divByS_mul_left` and then `divByS_mem_locSubring` because `[ϖ]^{b+1} ∈ chartT`; the `A_inf`-cofactor is absorbed by `algebraMap_A₀_subset_locSubring` (`A₀ = ⊤`). Case `i > a`: symmetric, factoring off `p^{a+1} ∈ chartT`. All exponent arithmetic (truncated subtraction) by `omega`.
- **Hypotheses**: none — the bound `a+b+2` is exactly what forces one of the two factorisations to exist.
- **Uses from project**: `chartMonomials`, `divBySIdeal`, `chartT`, `chartS`, `podAinf`, `divByS`, `locSubring`, `divByS_mul_left`, `divByS_mem_locSubring`, `algebraMap_A₀_subset_locSubring`, `teichPi`, `Ainf`.
- **Used by**: `chartData` (the `hopen` field).
- **Visibility**: public
- **Lines**: 179–221 (proof 38 lines)
- **Notes**: proof >30 lines; the same case split reappears verbatim inside `isRational_chartData` (dedup candidate).

### `def chartData`
- **Type**: `(u v a b : ℕ) : RationalLocData (Ainf p F)`
- **What**: **The chart datum**: `P = podAinf`, `T = {p^{a+1}, [ϖ]^{b+1}}`, `s = p^u[ϖ]^v`, i.e. Kedlaya's window `R(T/s)` presented as rational-localization data over the non-Tate Huber pair `(A_inf, A_inf)`.
- **How**: The only real field is `hopen`: take `N = a+b+2`; for `bb` in `(idealToTop I_inf)^N`, `idealToTop_pow_eq_preimage` pushes membership down to `↑bb ∈ I_inf^N`, and then the composite `Iinf_pow_le_span_chartMonomials` followed by `span_chartMonomials_le_divBySIdeal` puts `divByS ↑bb s` in `locSubring`.
- **Hypotheses**: none on `u v a b` (the openness bound is uniform).
- **Uses from project**: `RationalLocData` (`Presheaf.lean`), `podAinf`, `chartT`, `chartS`, `Iinf`, `idealToTop`, `idealToTop_pow_eq_preimage`, `span_chartMonomials_le_divBySIdeal`, `Iinf_pow_le_span_chartMonomials`, `Ainf`.
- **Used by**: `isRational_chartData`, `chartTopology`, `tendsto_chartToBIProd`, `chartTopologicalRing`, `chartUniformity_eq`, `presheafChartToBIProd`, `presheafChartToBIProd_coe`.
- **Visibility**: public
- **Lines**: 223–240 (definition 15 lines)
- **Notes**: headline definition; downstream files use `chartData p F ϖ 1 b a b` (i.e. `u=1`, `v=b`) exclusively.

### `theorem isRational_chartData`
- **Type**: `(u v a b : ℕ) : (chartData p F ϖ u v a b).IsRational`
- **What**: The chart datum presents a *rational subset* in Wedhorn Definition 7.29's sense: the ideal generated by `T = {p^{a+1},[ϖ]^{b+1}}` is open in `A_inf`.
- **How**: Show `I_inf^{a+b+2} ⊆ span T` set-theoretically: by `Iinf_pow_le_span_chartMonomials` it suffices to check the degree-`(a+b+2)` monomials, and the same `i ≤ a` / `i > a` factorisation as in `span_chartMonomials_le_divBySIdeal` writes each monomial as `A_inf`-multiple of `[ϖ]^{b+1}` resp. `p^{a+1}` (`Ideal.mul_mem_left` + `Ideal.subset_span`). `I_inf^{a+b+2}` is open by `(isAdic_iff.mp (isAdic_Iinf p F ϖ)).1`, so `span T` contains an open nbhd of `0` and `AddSubgroup.isOpen_of_mem_nhds` upgrades it to open.
- **Hypotheses**: none; the openness exponent `a+b+2` is uniform.
- **Uses from project**: `chartData`, `RationalLocData.IsRational` (`Presheaf.lean`), `Iinf`, `isAdic_Iinf`, `chartT`, `chartMonomials`, `Iinf_pow_le_span_chartMonomials`, `teichPi`, `Ainf`.
- **Used by**: unused in file (headline export; also currently unused elsewhere in the project).
- **Visibility**: public
- **Lines**: 242–291 (proof 46 lines)
- **Notes**: proof >30 lines; duplicates the monomial case split of `span_chartMonomials_le_divBySIdeal`.

### `theorem mem_rationalOpen_chartData_iff`
- **Type**: `(a₁ b₁ a₂ b₂ : ℕ) (ha₁ : 0 < a₁) (hb₁ : 0 < b₁) (ha₂ : 0 < a₂) (hb₂ : 0 < b₂) (v : Spv (Ainf p F)) : v ∈ rationalOpen (chartT p F ϖ (a₁+a₂-1) (b₁+b₂-1)) (chartS p F ϖ a₁ b₂) ↔ v ∈ Y p F ϖ ∧ v.vle (teichPi p F ϖ ^ b₁) ((p : Ainf p F) ^ a₁) ∧ v.vle ((p : Ainf p F) ^ a₂) (teichPi p F ϖ ^ b₂)`
- **What**: **The chart datum cuts out exactly the two-sided window** (raw-exponent form): the rational subset `R({p^{a₁+a₂},[ϖ]^{b₁+b₂}} / p^{a₁}[ϖ]^{b₂})` is `{v ∈ 𝒴 : κ(v) ≥ a₁/b₁ and κ(v) ≤ a₂/b₂}`.
- **How**: Install `v.toValuativeRel` and translate `Spv.vle` into `≤` of the associated valuation `w` via `Valuation.vle_iff_le`. Forward: the two `T`-conditions read `w(p)^{a₁+a₂} ≤ w(s)` and `w([ϖ])^{b₁+b₂} ≤ w(s)` with `w(s) = w(p)^{a₁}w([ϖ])^{b₂}`; `s ≠ 0`-in-valuation forces `w(p) ≠ 0 ≠ w([ϖ])` (which is exactly membership in `Y`, i.e. `¬ v.vle (p·[ϖ]) 0`), and cancelling the shared factor `w([ϖ])^{b₂}` (resp. `w(p)^{a₁}`) by `mul_le_mul_right` + `inv_mul_cancel₀`/`mul_inv_cancel₀` (legal since those factors are nonzero) yields the two window inequalities. Backward: multiply each window inequality by the complementary factor using `mul_le_mul'` to recover the `T`-conditions, and re-derive `w(s) ≠ 0` from `¬ v.vle (p[ϖ]) 0` via `pow_eq_zero_iff` with `ha₁`, `hb₂`.
- **Hypotheses**: all four exponents strictly positive — needed both to rewrite `(a₁+a₂-1)+1 = a₁+a₂` (`omega`) and to convert `w(s) ≠ 0` into `w(p) ≠ 0 ∧ w([ϖ]) ≠ 0`.
- **Uses from project**: `chartT`, `chartS`, `rationalOpen` (`AdicSpectrum.lean`), `Y` (`YSpace.lean`), `teichPi`, `Ainf`.
- **Used by**: `windowU_zero_eq_rationalOpen`, `windowV_zero_eq_rationalOpen`.
- **Visibility**: public
- **Lines**: 293–384 (proof 80 lines)
- **Notes**: proof >30 lines; the bridge between the adic-spectrum side (`rationalOpen`) and the Fargues–Fontaine window side (`Y`, `κ`).

### `theorem windowU_zero_eq_rationalOpen`
- **Type**: `(hp : 1 < p) : windowU p F ϖ 0 = rationalOpen (chartT p F ϖ (1 + (p+1) - 1) (1 + 2 - 1)) (chartS p F ϖ 1 2)`
- **What**: **The chart `U₀` is a rational subset**: the window `κ ∈ [1, c]` with `c = (p+1)/2` equals `R({p^{p+2}, [ϖ]³} / p·[ϖ]²)`.
- **How**: `ext v`, then `mem_rationalOpen_chartData_iff` at `(a₁,b₁,a₂,b₂) = (1,1,p+1,2)` turns the right side into raw exponent inequalities; `KGE_iff` at `q = (p:ℚ)^(0:ℤ) = 1` (with `a/b = 1/1`) and `KLE_iff` at `q = cFF p · p^0` (with `a/b = (p+1)/2`, positivity from `one_lt_cFF hp`, and `cFF` unfolded by `push_cast; ring`) convert the window's `KGE`/`KLE` predicates into the same inequalities in both directions.
- **Hypotheses**: `1 < p` (needed for `one_lt_cFF` and hence `0 < cFF p`).
- **Uses from project**: `windowU`, `KGE_iff`, `KLE_iff`, `cFF`, `one_lt_cFF` (all `YSpace.lean`), `rationalOpen`, `chartT`, `chartS`, `mem_rationalOpen_chartData_iff`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 386–415 (proof 24 lines)
- **Notes**: none.

### `theorem windowV_zero_eq_rationalOpen`
- **Type**: `(hp : 1 < p) : windowV p F ϖ 0 = rationalOpen (chartT p F ϖ ((p+1) + p - 1) (2 + 1 - 1)) (chartS p F ϖ (p+1) 1)`
- **What**: **The chart `V₀` is a rational subset**: the window `κ ∈ [c, p]` equals `R({p^{2p+1}, [ϖ]³} / p^{p+1}·[ϖ])`.
- **How**: Same shape as `windowU_zero_eq_rationalOpen` but at `(a₁,b₁,a₂,b₂) = (p+1,2,p,1)`: `mem_rationalOpen_chartData_iff` supplies the exponent form, `KGE_iff` at `q = cFF p` gives the left endpoint `κ ≥ c` and `KLE_iff` at `q = (p:ℚ)^((0:ℤ)+1) = p` gives the right endpoint `κ ≤ p`.
- **Hypotheses**: `1 < p`.
- **Uses from project**: `windowV`, `KGE_iff`, `KLE_iff`, `cFF`, `one_lt_cFF`, `rationalOpen`, `chartT`, `chartS`, `mem_rationalOpen_chartData_iff`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 417–445 (proof 23 lines)
- **Notes**: together with `windowU_zero_eq_rationalOpen` this exhibits both charts of the FF curve as rational subsets of `Spa(A_inf, A_inf)`.

### `theorem chartS_pow_eq`
- **Type**: `(b k : ℕ) (hb : 0 < b) : chartS p F ϖ 1 b ^ k = ((p : Ainf p F) * teichPi p F ϖ) ^ k * teichPi p F ϖ ^ (k * (b-1))`
- **What**: The chart denominator `p[ϖ]^b` raised to `k` decomposes as the standard Robba denominator `(p[ϖ])^k` times a pure `[ϖ]`-power.
- **How**: Unfold `chartS`, `pow_one`, distribute with `mul_pow`, then collect `[ϖ]`-exponents via `pow_mul`/`pow_add`; the residual natural identity `b·k = k + k(b-1)` is proved from `b = 1 + (b-1)` (`omega`) and `ring`.
- **Hypotheses**: `0 < b`, so that truncated `b - 1` behaves.
- **Uses from project**: `chartS`, `teichPi`, `Ainf`.
- **Used by**: `isLocalization_chartS_Bloc`.
- **Visibility**: public
- **Lines**: 447–456 (proof 5 lines)
- **Notes**: none.

### `theorem isLocalization_chartS_Bloc`
- **Type**: `(b : ℕ) (hb : 0 < b) : IsLocalization (Submonoid.powers (chartS p F ϖ 1 b)) (Bloc p F ϖ)`
- **What**: **`Bloc = A_inf[1/(p[ϖ])]` is also the localization of `A_inf` away from the chart denominator `p·[ϖ]^b`** — the two multiplicative sets have the same saturation.
- **How**: `map_units`: the image of `p[ϖ]^b` is a unit by `isUnit_p_image` times `(isUnit_teichPi_image).pow b`, hence so is every power. `surj` and `exists_of_eq` are transported from the known `IsLocalization (Submonoid.powers (p·[ϖ])) (Bloc …)` structure by `chartS_pow_eq`: a witness `(p[ϖ])^k` is replaced by `(p[ϖ]^b)^k` at the cost of the extra factor `[ϖ]^{k(b-1)}`, which is inserted into the numerator (`surj`) or multiplied through the equation (`exists_of_eq`, closed by `calc … ring`).
- **Hypotheses**: `0 < b`.
- **Uses from project**: `chartS`, `Bloc`, `isUnit_p_image`, `isUnit_teichPi_image` (`RobbaLoc.lean`), `chartS_pow_eq`, `teichPi`, `Ainf`.
- **Used by**: `blocEquivAwayChartS`, `blocEquiv_divByS_teichPi`, `blocEquiv_divByS_p`, `blocEquivAwayChartS_algebraMap`.
- **Visibility**: public
- **Lines**: 458–503 (proof 42 lines)
- **Notes**: proof >30 lines; stated as a `theorem` (not `instance`) and introduced by `letI` at each use site.

### `def blocEquivAwayChartS`
- **Type**: `(b : ℕ) (hb : 0 < b) : Localization.Away (chartS p F ϖ 1 b) ≃+* Bloc p F ϖ`
- **What**: **ID2a** — the canonical ring isomorphism `A_inf[1/(p[ϖ]^b)] ≃+* A_inf[1/(p[ϖ])] = Bloc`.
- **How**: With `isLocalization_chartS_Bloc` in scope, `IsLocalization.algEquiv` between two localizations of `A_inf` at the same submonoid, then `.toRingEquiv`.
- **Hypotheses**: `0 < b`.
- **Uses from project**: `chartS`, `Bloc`, `isLocalization_chartS_Bloc`.
- **Used by**: `blocEquiv_divByS_teichPi`, `blocEquiv_divByS_p`, `blocEquivAwayChartS_algebraMap`, `map_locSubring_chartData`, `map_locSubring_le_blocUnitBall`, `wI_le_of_mem_locIdeal_pow`, `chartToBIProd`, `exists_locNhd_le_ball`, `tendsto_chartToBIProd`, `ball_le_locNhd`.
- **Visibility**: public
- **Lines**: 505–511 (definition 4 lines)
- **Notes**: the pivot between the abstract localization side (where `RationalLocData` lives) and the concrete `Bloc` side (where the Gauss norms live).

### `def chartFracPi`
- **Type**: `Bloc p F ϖ`
- **What**: The first chart fraction `[ϖ]/p ∈ Bloc` — the image of the tray fraction `[ϖ]^{b+1}/s`.
- **How**: `algebraMap [ϖ] * ↑(isUnit_p_image p F ϖ).unit⁻¹`, i.e. multiply by the inverse of the unit `p`.
- **Hypotheses**: none beyond the ambient setup (`p` is a unit in `Bloc`).
- **Uses from project**: `Bloc`, `Ainf`, `teichPi`, `isUnit_p_image`.
- **Used by**: `wI_chartFracPi_le_one`, `closure_chart_le_blocUnitBall`, `blocEquiv_divByS_teichPi`, `map_locSubring_chartData`, `chartFracPi_pow_mul_p_pow`, `chart_term_low_eq`, `mem_chartSubring_of_wI_le`, `exists_p_pow_mul_mem_chartSubring`.
- **Visibility**: public
- **Lines**: 515–518 (definition 3 lines)
- **Notes**: none.

### `def chartFracP`
- **Type**: `(a b : ℕ) : Bloc p F ϖ`
- **What**: The second chart fraction `p^a/[ϖ]^b ∈ Bloc` — the image of the tray fraction `p^{a+1}/s`.
- **How**: `algebraMap (p^a) * (AlocToBloc (teichPiInvAloc))^b`, using the pre-built inverse of `[ϖ]` in `Aloc` pushed to `Bloc`.
- **Hypotheses**: none beyond the ambient setup.
- **Uses from project**: `Bloc`, `Ainf`, `AlocToBloc`, `teichPiInvAloc` (`Presentation.lean`).
- **Used by**: `wI_chartFracP_le_one`, `closure_chart_le_blocUnitBall`, `blocEquiv_divByS_p`, `map_locSubring_chartData`, `chartFracP_pow_mul_teichPi_pow`, `chart_term_high_eq`, `chart_tail_eq`, `mem_chartSubring_of_wI_le`, `exists_p_pow_mul_mem_chartSubring`.
- **Visibility**: public
- **Lines**: 520–523 (definition 3 lines)
- **Notes**: none.

### `theorem wI_chartFracPi_le_one`
- **Type**: `(h1 : perfectoidValuation p F ↑(PseudoUniformizer.toOF F ϖ) ≤ ρ₁) (h2 : … ≤ ρ₂) : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (chartFracPi p F ϖ)) ≤ 1`
- **What**: `wI([ϖ]/p) ≤ 1` exactly when both radii dominate `|ϖ|` — the left-endpoint condition `κ ≥ 1` of the chart window, in interval-norm form.
- **How**: `wI_BIProd` plus two `valued_BlocToHatK` rewrites express `wI` as `max` of the two `wLoc`s. At either radius, `Valuation.map_mul` + `wLoc_algebraMap` + `wLoc_p_inv` + `gaussValue_teichmuller` compute `wLoc([ϖ]/p) = |ϖ|·ρ⁻¹`; then `max_le` and `mul_le_mul_of_nonneg_right h` with `mul_inv_cancel₀ hρ0.ne'` give `|ϖ|ρ⁻¹ ≤ ρρ⁻¹ = 1`.
- **Hypotheses**: `|ϖ| ≤ ρ₁` and `|ϖ| ≤ ρ₂` (the window's left endpoint).
- **Uses from project**: `wI`, `BIProd`, `wI_BIProd`, `valued_BlocToHatK` (`IntervalRing.lean`), `chartFracPi`, `wLoc`, `wLoc_algebraMap`, `wLoc_p_inv` (`RobbaLoc.lean`), `gaussValue_teichmuller`, `perfectoidValuation` (`GaussNorm.lean`), `teichPi`, `Bloc`, `Ainf`, `isUnit_p_image`, `PseudoUniformizer.toOF`, `OF`.
- **Used by**: `closure_chart_le_blocUnitBall`.
- **Visibility**: public
- **Lines**: 525–547 (proof 15 lines)
- **Notes**: none.

### `theorem wI_chartFracP_le_one`
- **Type**: `(a b : ℕ) (h1 : ρ₁ ^ a ≤ perfectoidValuation p F ↑(PseudoUniformizer.toOF F ϖ) ^ b) (h2 : ρ₂ ^ a ≤ … ^ b) : wI … (BIProd … (chartFracP p F ϖ a b)) ≤ 1`
- **What**: `wI(p^a/[ϖ]^b) ≤ 1` exactly when `ρ^a ≤ |ϖ|^b` at both radii — the right-endpoint condition `κ ≤ a/b` of the chart window.
- **How**: Again `wI_BIProd` + `valued_BlocToHatK` reduce to the two `wLoc`s; at either radius `wLoc(p^a/[ϖ]^b) = ρ^a·(|ϖ|⁻¹)^b` is computed by `wLoc_algebraMap` with `gaussValue_p_pow_mul` and `gaussValue_one` for the numerator and `wLoc_AlocToBloc` + `wAloc_teichPiInvAloc` for the inverse Teichmüller factor. The final estimate `ρ^a(|ϖ|^b)⁻¹ ≤ 1` follows from the hypothesis and `mul_inv_cancel₀ (pow_pos hϖ0 b).ne'`, where `|ϖ| > 0` comes from `PseudoUniformizer.toOF_ne_zero` and `Valuation.ne_zero_iff`.
- **Hypotheses**: `ρ₁^a ≤ |ϖ|^b`, `ρ₂^a ≤ |ϖ|^b`.
- **Uses from project**: `wI`, `BIProd`, `wI_BIProd`, `valued_BlocToHatK`, `chartFracP`, `wLoc`, `wLoc_algebraMap`, `wLoc_AlocToBloc`, `wAloc_teichPiInvAloc`, `AlocToBloc`, `teichPiInvAloc`, `gaussValue_p_pow_mul`, `gaussValue_one`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `OF`, `Ainf`, `Bloc`.
- **Used by**: `closure_chart_le_blocUnitBall`.
- **Visibility**: public
- **Lines**: 549–587 (proof 30 lines)
- **Notes**: proof exactly 30 lines.

### `def blocUnitBall`
- **Type**: `(hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) : Subring (Bloc p F ϖ)`
- **What**: **The unit ball of `Bloc` for the interval norm** `wI ∘ BIProd`, as a subring: `{x : wI(BIProd x) ≤ 1}`.
- **How**: Each subring axiom is the corresponding `wI` estimate after pushing `BIProd` through: `wI_zero`, `wI_one`, `wI_add_le` (ultrametric, so `max_le` closes `add_mem'`), `wI_mul_le` (submultiplicative, closed by `mul_le_mul … ≤ 1*1`), `wI_neg`.
- **Hypotheses**: the four radius conditions `0 < ρᵢ < 1` taken explicitly (shadowing the section variables).
- **Uses from project**: `Bloc`, `wI`, `BIProd`, `wI_zero`, `wI_one`, `wI_add_le`, `wI_mul_le`, `wI_neg` (`IntervalRing.lean`).
- **Used by**: `algebraMap_mem_blocUnitBall`, `closure_chart_le_blocUnitBall`, `map_locSubring_le_blocUnitBall`.
- **Visibility**: public
- **Lines**: 589–622 (structure body 30 lines)
- **Notes**: docstring records "carrier given explicitly per PERF-1" — the carrier is spelled out so elaboration does not unfold `wI`.

### `theorem algebraMap_mem_blocUnitBall`
- **Type**: `(x : Ainf p F) : algebraMap (Ainf p F) (Bloc p F ϖ) x ∈ blocUnitBall p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1`
- **What**: Images of `A_inf` land in the unit ball — all Gauss values at radii `< 1` are `≤ 1`.
- **How**: `wI_BIProd` + `valued_BlocToHatK` + `wLoc_algebraMap` (twice) turn the goal into `max (gaussValue ρ₁ x) (gaussValue ρ₂ x) ≤ 1`, closed by `max_le` and two instances of `gaussValue_le_one`.
- **Hypotheses**: `ρ₁ < 1`, `ρ₂ < 1` (used as `hρ1.le` in `gaussValue_le_one`).
- **Uses from project**: `Ainf`, `Bloc`, `blocUnitBall`, `wI`, `BIProd`, `wI_BIProd`, `valued_BlocToHatK`, `wLoc_algebraMap`, `gaussValue_le_one`.
- **Used by**: `closure_chart_le_blocUnitBall`.
- **Visibility**: public
- **Lines**: 624–632 (proof 5 lines)
- **Notes**: none.

### `theorem closure_chart_le_blocUnitBall`
- **Type**: `(a b : ℕ) (hπ1 : |ϖ| ≤ ρ₁) (hπ2 : |ϖ| ≤ ρ₂) (hr1 : ρ₁^a ≤ |ϖ|^b) (hr2 : ρ₂^a ≤ |ϖ|^b) : Subring.closure (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ)) ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b}) ≤ blocUnitBall p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1`
- **What**: **The chart subring** — generated by `A_inf` and the two window fractions — sits inside the `wI`-unit ball. This is the generator step of the forward half of the topology comparison.
- **How**: `Subring.closure_le` reduces to the three generator families: `A_inf`-images by `algebraMap_mem_blocUnitBall`, `[ϖ]/p` by `wI_chartFracPi_le_one`, `p^a/[ϖ]^b` by `wI_chartFracP_le_one`.
- **Hypotheses**: exactly the two window-endpoint inequalities at both radii.
- **Uses from project**: `Ainf`, `Bloc`, `chartFracPi`, `chartFracP`, `blocUnitBall`, `algebraMap_mem_blocUnitBall`, `wI_chartFracPi_le_one`, `wI_chartFracP_le_one`.
- **Used by**: `map_locSubring_le_blocUnitBall`.
- **Visibility**: public
- **Lines**: 634–653 (proof 7 lines)
- **Notes**: none.

### `theorem blocEquiv_divByS_teichPi`
- **Type**: `(b : ℕ) (hb : 0 < b) : blocEquivAwayChartS p F ϖ b hb (divByS (teichPi p F ϖ ^ (b+1)) (chartS p F ϖ 1 b)) = chartFracPi p F ϖ`
- **What**: Under the localization identification, the tray fraction `[ϖ]^{b+1}/s` corresponds to `[ϖ]/p`.
- **How**: `IsLocalization.algEquiv_mk'` transports the `mk'` across the equivalence, then `IsLocalization.mk'_eq_iff_eq_mul` turns the goal into the `Bloc`-identity `[ϖ]^{b+1} = ([ϖ]/p)·(p·[ϖ]^b)`. That is verified by a `calc` that inserts `p·p⁻¹ = 1` (from `(isUnit_p_image …).unit.mul_inv` and `unit_spec`) and rearranges with `map_mul`/`ring`.
- **Hypotheses**: `0 < b`.
- **Uses from project**: `blocEquivAwayChartS`, `isLocalization_chartS_Bloc`, `divByS`, `teichPi`, `chartS`, `chartFracPi`, `isUnit_p_image`, `Bloc`, `Ainf`.
- **Used by**: `map_locSubring_chartData`.
- **Visibility**: public
- **Lines**: 655–690 (proof 31 lines)
- **Notes**: proof >30 lines.

### `theorem blocEquiv_divByS_p`
- **Type**: `(a b : ℕ) (hb : 0 < b) : blocEquivAwayChartS p F ϖ b hb (divByS ((p : Ainf p F) ^ (a+1)) (chartS p F ϖ 1 b)) = chartFracP p F ϖ a b`
- **What**: Under the localization identification, the tray fraction `p^{a+1}/s` corresponds to `p^a/[ϖ]^b`.
- **How**: Same pattern as `blocEquiv_divByS_teichPi`: `IsLocalization.algEquiv_mk'` then `IsLocalization.mk'_eq_iff_eq_mul`, reducing to `p^{a+1} = (p^a/[ϖ]^b)·(p[ϖ]^b)`; the inverse-Teichmüller cancellation `([ϖ]⁻¹)^b·[ϖ]^b = 1` comes from `AlocToBloc_teichPiInv_mul` (at exponent 1, powered up by `mul_pow`/`one_pow`).
- **Hypotheses**: `0 < b`.
- **Uses from project**: `blocEquivAwayChartS`, `isLocalization_chartS_Bloc`, `divByS`, `chartS`, `chartFracP`, `AlocToBloc`, `teichPiInvAloc`, `AlocToBloc_teichPiInv_mul`, `teichPi`, `Bloc`, `Ainf`.
- **Used by**: `map_locSubring_chartData`.
- **Visibility**: public
- **Lines**: 692–730 (proof 34 lines)
- **Notes**: proof >30 lines.

### `theorem blocEquivAwayChartS_algebraMap`
- **Type**: `(b : ℕ) (hb : 0 < b) (y : Ainf p F) : blocEquivAwayChartS p F ϖ b hb (algebraMap (Ainf p F) (Localization.Away (chartS p F ϖ 1 b)) y) = algebraMap (Ainf p F) (Bloc p F ϖ) y`
- **What**: The localization identification commutes with the two structure maps from `A_inf`.
- **How**: It is `(IsLocalization.algEquiv …).commutes y` once `isLocalization_chartS_Bloc` is installed.
- **Hypotheses**: `0 < b`.
- **Uses from project**: `blocEquivAwayChartS`, `isLocalization_chartS_Bloc`, `chartS`, `Bloc`, `Ainf`.
- **Used by**: `map_locSubring_chartData`, `wI_le_of_mem_locIdeal_pow`, `ball_le_locNhd`.
- **Visibility**: public
- **Lines**: 732–739 (proof 3 lines)
- **Notes**: none.

### `theorem map_locSubring_chartData`
- **Type**: `(a b : ℕ) (hb : 0 < b) : (locSubring (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b)).map (blocEquivAwayChartS p F ϖ b hb).toRingHom = Subring.closure (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ)) ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b})`
- **What**: **The ring of definition of the chart localization transports exactly onto the chart subring of `Bloc`** — the image of `locSubring` under the identification is the subring generated by `A_inf` and the two window fractions.
- **How**: `locSubring` is by definition a `Subring.closure`, so `RingHom.map_closure` reduces the goal to equality of generator sets; `Set.image_union` splits it. For the `A₀ = ⊤` half both inclusions are `blocEquivAwayChartS_algebraMap`. For the two-fraction half, `Finset.mem_insert`/`Finset.mem_singleton` case-analyse `chartT` and each case is `blocEquiv_divByS_p` resp. `blocEquiv_divByS_teichPi`.
- **Hypotheses**: `0 < b`.
- **Uses from project**: `locSubring`, `podAinf`, `chartT`, `chartS`, `blocEquivAwayChartS`, `blocEquivAwayChartS_algebraMap`, `blocEquiv_divByS_p`, `blocEquiv_divByS_teichPi`, `divByS`, `chartFracPi`, `chartFracP`, `teichPi`, `Bloc`, `Ainf`.
- **Used by**: `map_locSubring_le_blocUnitBall`, `ball_le_locNhd`.
- **Visibility**: public
- **Lines**: 741–781 (proof 31 lines)
- **Notes**: proof >30 lines; used in *both* directions (forward for the ball bound, backward in `ball_le_locNhd`).

### `theorem map_locSubring_le_blocUnitBall`
- **Type**: `(a b : ℕ) (hb : 0 < b) (hπ1 hπ2 hr1 hr2 : window endpoint bounds) : (locSubring (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b)).map (blocEquivAwayChartS p F ϖ b hb).toRingHom ≤ blocUnitBall p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1`
- **What**: **The forward half of the topology comparison, assembled**: the ring of definition of the chart localization lands inside the `wI`-unit ball.
- **How**: Rewrite the left side by `map_locSubring_chartData` and apply `closure_chart_le_blocUnitBall`.
- **Hypotheses**: `0 < b` plus the four window-endpoint bounds `|ϖ| ≤ ρᵢ`, `ρᵢ^a ≤ |ϖ|^b`.
- **Uses from project**: `locSubring`, `podAinf`, `chartT`, `chartS`, `blocEquivAwayChartS`, `blocUnitBall`, `map_locSubring_chartData`, `closure_chart_le_blocUnitBall`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`.
- **Used by**: `wI_le_of_mem_locIdeal_pow` (as the `wI(c) ≤ 1` input in the `smul_mem'` field).
- **Visibility**: public
- **Lines**: 783–796 (proof 2 lines)
- **Notes**: none.

### `theorem gaussValue_le_of_mem_Iinf_pow`
- **Type**: `{ρ : NNReal} (hρ1 : ρ < 1) (n : ℕ) {w : Ainf p F} (hw : w ∈ Iinf p F ϖ ^ n) : gaussValue p F ρ w ≤ (max ρ (perfectoidValuation p F ↑(PseudoUniformizer.toOF F ϖ))) ^ n`
- **What**: **Elements of `I_inf^n` have Gauss value at most `max(ρ,|ϖ|)^n`** — the quantitative cofinality of the adic filtration against the Gauss norm.
- **How**: Build the bound set `BdIdeal = {w : gaussValue ρ w ≤ q^n}` (with `q = max ρ |ϖ|`) as an `Ideal`: `zero_mem'` by `gaussValue_zero`, `add_mem'` by the ultrametric `gaussValue_add_le` + `max_le`, `smul_mem'` by `gaussValue_mul_le` together with `gaussValue_le_one` for the scalar. Then show `span (chartMonomials n) ≤ BdIdeal` by computing each monomial's value `gaussValue(p^i[ϖ]^{n-i}) = ρ^i·|ϖ|^{n-i}` via `gaussValue_p_pow_mul` and `gaussValue_teichmuller` (after rewriting `[ϖ]^{n-i}` as `teichmuller (ϖ^{n-i})` through `map_pow`), and bounding it by `q^i q^{n-i} = q^n` with `pow_le_pow_left₀`. Finally `Iinf_pow_le_span_chartMonomials` transfers `hw` into the span.
- **Hypotheses**: `ρ < 1` (needed for `gaussValue_add_le`, `gaussValue_mul_le`, `gaussValue_le_one`).
- **Uses from project**: `Ainf`, `Iinf`, `gaussValue`, `gaussValue_zero`, `gaussValue_add_le`, `gaussValue_mul_le`, `gaussValue_le_one`, `gaussValue_p_pow_mul`, `gaussValue_teichmuller`, `perfectoidValuation` (`GaussNorm.lean`), `chartMonomials`, `Iinf_pow_le_span_chartMonomials`, `teichPi`, `PseudoUniformizer.toOF`, `OF`.
- **Used by**: `wI_le_of_mem_locIdeal_pow` (at both radii).
- **Visibility**: public
- **Lines**: 798–858 (proof 54 lines)
- **Notes**: proof >30 lines; the `set … with` ideal is built inline rather than as a named auxiliary definition.

### `theorem wI_BIProd_algebraMap`
- **Type**: `(x : Ainf p F) : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (algebraMap (Ainf p F) (Bloc p F ϖ) x)) = max (gaussValue p F ρ₁ x) (gaussValue p F ρ₂ x)`
- **What**: The interval norm of an `A_inf`-element's image is the max of its two Gauss values.
- **How**: One rewrite chain: `wI_BIProd`, two `valued_BlocToHatK`, two `wLoc_algebraMap`.
- **Hypotheses**: the ambient radius conditions.
- **Uses from project**: `wI`, `BIProd`, `wI_BIProd`, `valued_BlocToHatK`, `wLoc_algebraMap`, `gaussValue`, `Bloc`, `Ainf`.
- **Used by**: `wI_le_of_mem_locIdeal_pow`.
- **Visibility**: public
- **Lines**: 860–867 (proof 2 lines)
- **Notes**: none.

### `theorem wI_le_of_mem_locIdeal_pow`
- **Type**: `(a b : ℕ) (hb : 0 < b) (hπ1 hπ2 hr1 hr2 : window endpoint bounds) (n : ℕ) {y : ↥(locSubring (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b))} (hy : y ∈ locIdeal (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b) ^ n) : wI … (BIProd … (blocEquivAwayChartS p F ϖ b hb ↑y)) ≤ (max (max ρ₁ ρ₂) |ϖ|) ^ n`
- **What**: **The `J^n`-cofinality estimate**: the `n`-th power of the ideal of definition of the chart localization transports into the `q^n`-ball of `B^I`, where `q = max(ρ₁,ρ₂,|ϖ|) < 1`. This is what makes the chart map continuous.
- **How**: Build the bound ideal `Bd ⊆ locSubring` of elements with `wI(image) ≤ q^n` (`wI_zero`, `wI_add_le`, and for `smul_mem'` the crucial `map_locSubring_le_blocUnitBall`, which says every ring-of-definition scalar has `wI ≤ 1`, combined with `wI_mul_le`). Then `locIdeal` unfolds to `Ideal.map (algebraMapD …) (P.I)`, so `Ideal.map_pow` + `Ideal.span_le` reduce to generators `algebraMapD w` with `w ∈ (idealToTop I_inf)^n`; `idealToTop_pow_eq_preimage` gives `↑w ∈ I_inf^n`, `blocEquivAwayChartS_algebraMap` + `wI_BIProd_algebraMap` turn the value into `max` of two Gauss values, and `gaussValue_le_of_mem_Iinf_pow` at `ρ₁` and `ρ₂` bounds each by `q^n` (`pow_le_pow_left₀` for the max-monotonicity).
- **Hypotheses**: `0 < b` and the four window-endpoint bounds (only via `map_locSubring_le_blocUnitBall`); `ρᵢ < 1` implicitly through `gaussValue_le_of_mem_Iinf_pow`.
- **Uses from project**: `locSubring`, `locIdeal`, `algebraMapD` (`LocalizationTopology.lean`), `podAinf`, `chartT`, `chartS`, `blocEquivAwayChartS`, `blocEquivAwayChartS_algebraMap`, `wI`, `BIProd`, `wI_zero`, `wI_add_le`, `wI_mul_le`, `wI_BIProd_algebraMap`, `map_locSubring_le_blocUnitBall`, `gaussValue`, `gaussValue_le_of_mem_Iinf_pow`, `Iinf`, `idealToTop`, `idealToTop_pow_eq_preimage`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`, `Ainf`.
- **Used by**: `exists_locNhd_le_ball`.
- **Visibility**: public
- **Lines**: 869–959 (proof 75 lines)
- **Notes**: proof >30 lines; the longest single estimate in the forward direction.

### `theorem gaussTerm_le_of_wI_le`
- **Type**: `{ε : NNReal} (k : ℕ) (A : Ainf p F) {x : Bloc p F ϖ} (hx : x * algebraMap (Ainf p F) (Bloc p F ϖ) ((p * teichPi)^k) = algebraMap (Ainf p F) (Bloc p F ϖ) A) (hwI : wI … (BIProd … x) ≤ ε) {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρmem : ρ = ρ₁ ∨ ρ = ρ₂) (m : ℕ) : gaussTerm p F ρ A m ≤ ε * (ρ * perfectoidValuation p F ↑(PseudoUniformizer.toOF F ϖ)) ^ k`
- **What**: **Coefficient bounds from an interval-norm bound**: if `x = A/(p[ϖ])^k` has `wI(x) ≤ ε`, then every Teichmüller coordinate of the numerator `A` satisfies `ρ^m|a_m| ≤ ε(ρ|ϖ|)^k` at either radius.
- **How**: Apply `wLoc` to the relation `hx`: `Valuation.map_mul` + `wLoc_algebraMap` + `gaussValue_p_teichPi` (which evaluates `gaussValue ρ (p[ϖ]) = ρ|ϖ|`) give `wLoc(x)·(ρ|ϖ|)^k = gaussValue ρ A`. Separately `wI_BIProd` + `valued_BlocToHatK` and `le_max_left`/`le_max_right` give `wLoc(x) ≤ wI(x) ≤ ε`. Chaining with `gaussTerm_le_gaussValue` (each term is at most the sup) and `mul_le_mul_of_nonneg_right` finishes.
- **Hypotheses**: `ρ ∈ {ρ₁, ρ₂}` with `0 < ρ < 1`; `x` presented with denominator `(p[ϖ])^k`.
- **Uses from project**: `Ainf`, `Bloc`, `teichPi`, `wI`, `BIProd`, `wI_BIProd`, `valued_BlocToHatK`, `wLoc`, `wLoc_algebraMap`, `gaussValue`, `gaussValue_p_teichPi` (`RobbaLoc.lean`), `gaussTerm`, `gaussTerm_le_gaussValue`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`.
- **Used by**: `exists_teichCoeff_factor_low`, `exists_teichCoeff_factor_high`.
- **Visibility**: public
- **Lines**: 961–990 (proof 18 lines)
- **Notes**: this is the entry point of the reverse (Kedlaya plus-ring) direction.

### `def chartToBIProd`
- **Type**: `(b : ℕ) (hb : 0 < b) : Localization.Away (chartS p F ϖ 1 b) →+* (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)`
- **What**: The chart-to-`B^I` ring homomorphism on the localization, before completion: `z ↦ BIProd (blocEquivAwayChartS z)`.
- **How**: Bundled `RingHom` with an explicit `toFun`; all four axioms are `map_one`/`map_mul`/`map_zero`/`map_add` of the two composed maps.
- **Hypotheses**: `0 < b`, plus the ambient radius conditions (through `hatK`, `BIProd`).
- **Uses from project**: `chartS`, `hatK` (`ArCompletion.lean`), `BIProd`, `blocEquivAwayChartS`.
- **Used by**: `tendsto_chartToBIProd_coe`, `continuous_chartToBIProd`, `chartCompletionToBIProd`, `presheafChartToBIProd_coe`.
- **Visibility**: public
- **Lines**: 992–1002 (definition 8 lines)
- **Notes**: docstring records a PERF rationale — the explicit `toFun` keeps the localization equivalence's body out of coercion unfolds.

### `theorem exists_locNhd_le_ball`
- **Type**: `(a b : ℕ) (hb : 0 < b) (hπ1 hπ2 hr1 hr2 : window endpoint bounds) {ε : NNReal} (hε : 0 < ε) : ∃ n : ℕ, ∀ z ∈ locNhd (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b) n, wI … (BIProd … (blocEquivAwayChartS p F ϖ b hb z)) ≤ ε`
- **What**: **The forward ball inclusion, basis form**: for each `ε > 0` some basic `locNhd` neighbourhood maps into the `ε`-ball of `B^I`. Topology-free core of continuity.
- **How**: Set `q = max (max ρ₁ ρ₂) |ϖ|`; `q < 1` by `max_lt` and `perfectoidValuation_toOF_lt_one`. Then `tendsto_pow_atTop_nhds_zero_of_lt_one hq1 |>.eventually_le_const hε |>.exists` yields `n` with `q^n ≤ ε`. Each `z ∈ locNhd … n` is by definition the image of some `y ∈ locIdeal^n`, so `wI_le_of_mem_locIdeal_pow` bounds it by `q^n ≤ ε`.
- **Hypotheses**: `0 < b`, the four window-endpoint bounds, `0 < ε`; implicitly `ρᵢ < 1` for `q < 1`.
- **Uses from project**: `locNhd`, `podAinf`, `chartT`, `chartS`, `wI`, `BIProd`, `blocEquivAwayChartS`, `wI_le_of_mem_locIdeal_pow`, `perfectoidValuation`, `perfectoidValuation_toOF_lt_one` (`GaussPoint.lean`), `PseudoUniformizer.toOF`, `OF`.
- **Used by**: `tendsto_chartToBIProd`.
- **Visibility**: public
- **Lines**: 1004–1027 (proof 10 lines)
- **Notes**: none.

### `def chartTopology`
- **Type**: `(a b : ℕ) : TopologicalSpace (Localization.Away (chartS p F ϖ 1 b))`
- **What**: The chart topology on the localization — the `RationalLocData` topology of `chartData p F ϖ 1 b a b`, behind a non-reducible wrapper.
- **How**: `(chartData p F ϖ 1 b a b).topology`.
- **Hypotheses**: none.
- **Uses from project**: `chartS`, `chartData`, `RationalLocData.topology` (`Presheaf.lean`).
- **Used by**: `tendsto_chartToBIProd`, `tendsto_chartToBIProd_coe`, `chartTopologicalRing`, `continuous_chartToBIProd`, `chartUniformity`, `chartIsUniformAddGroup`.
- **Visibility**: public
- **Lines**: 1029–1033 (definition 2 lines)
- **Notes**: docstring records the PERF rationale — statements must never unfold the `RingSubgroupsBasis` construction.

### `theorem tendsto_chartToBIProd`
- **Type**: `(a b : ℕ) (hb : 0 < b) (hπ1 hπ2 hr1 hr2 : window endpoint bounds) : @Filter.Tendsto _ _ (fun z => BIProd … (blocEquivAwayChartS p F ϖ b hb z)) (@nhds _ (chartTopology p F ϖ a b) 0) (nhds 0)`
- **What**: The chart map is continuous at `0` for the chart topology.
- **How**: Given a nbhd `U` of `0` in the product, `exists_wI_ball_subset` extracts an `ε`-ball inside `U`; `exists_locNhd_le_ball` supplies `n` whose `locNhd` maps into that ball; `locBasis … (chartData …).hopen |>.hasBasis_nhds_zero.mem_of_mem` witnesses that the `n`-th `locNhd` really is a nbhd of `0` for the chart topology; `Filter.mem_of_superset` closes.
- **Hypotheses**: `0 < b` plus the four window-endpoint bounds.
- **Uses from project**: `BIProd`, `blocEquivAwayChartS`, `chartTopology`, `exists_wI_ball_subset` (`IntervalRing.lean`), `exists_locNhd_le_ball`, `locNhd`, `locBasis`, `podAinf`, `chartT`, `chartS`, `chartData`.
- **Used by**: `tendsto_chartToBIProd_coe`.
- **Visibility**: public
- **Lines**: 1035–1063 (proof 16 lines)
- **Notes**: none.

### `theorem tendsto_chartToBIProd_coe`
- **Type**: same hypotheses as `tendsto_chartToBIProd`, conclusion `Filter.Tendsto ⇑(chartToBIProd p F ϖ … b hb) (@nhds _ (chartTopology p F ϖ a b) 0) (nhds 0)`
- **What**: The `⇑`-coerced form of `tendsto_chartToBIProd`.
- **How**: `(tendsto_chartToBIProd …).congr fun z => rfl` — the coercion of the bundled hom is definitionally the lambda.
- **Hypotheses**: as above.
- **Uses from project**: `chartToBIProd`, `chartTopology`, `tendsto_chartToBIProd`.
- **Used by**: `continuous_chartToBIProd`.
- **Visibility**: public
- **Lines**: 1065–1078 (proof 2 lines)
- **Notes**: docstring records the PERF rationale — isolating the coercion-vs-lambda defeq check to one place.

### `theorem chartTopologicalRing`
- **Type**: `(a b : ℕ) : @IsTopologicalRing (Localization.Away (chartS p F ϖ 1 b)) (chartTopology p F ϖ a b) _`
- **What**: The chart topology makes the localization a topological ring.
- **How**: `(chartData p F ϖ 1 b a b).isTopologicalRing`.
- **Hypotheses**: none.
- **Uses from project**: `chartS`, `chartTopology`, `chartData`, `RationalLocData.isTopologicalRing`.
- **Used by**: `continuous_chartToBIProd`, `chartUniformity`, `chartIsUniformAddGroup`, `chartCompletionToBIProd`, `presheafChartToBIProd_coe`.
- **Visibility**: public
- **Lines**: 1080–1084 (proof 1 line)
- **Notes**: docstring records that the instance is "elaborated once" for performance.

### `theorem continuous_chartToBIProd`
- **Type**: `(a b : ℕ) (hb : 0 < b) (hπ1 hπ2 hr1 hr2 : window endpoint bounds) : @Continuous _ _ (chartTopology p F ϖ a b) _ (chartToBIProd p F ϖ … b hb)`
- **What**: The chart map is continuous (everywhere) for the chart topology.
- **How**: Install `chartTopology`, `chartTopologicalRing` and its `to_topologicalAddGroup` as local instances, then `continuous_of_tendsto_nhds_zero` (continuity of an additive-group hom from continuity at `0`) applied to `tendsto_chartToBIProd_coe`.
- **Hypotheses**: `0 < b` plus the four window-endpoint bounds.
- **Uses from project**: `chartTopology`, `chartTopologicalRing`, `chartToBIProd`, `tendsto_chartToBIProd_coe`, `chartS`.
- **Used by**: `chartCompletionToBIProd`, `presheafChartToBIProd_coe`.
- **Visibility**: public
- **Lines**: 1086–1106 (proof 10 lines)
- **Notes**: none.

### `def chartUniformity`
- **Type**: `(a b : ℕ) : UniformSpace (Localization.Away (chartS p F ϖ 1 b))`
- **What**: The chart uniformity — the right uniformity attached to the chart topology — behind an opaque wrapper.
- **How**: `@IsTopologicalAddGroup.rightUniformSpace` applied to the additive-group structure extracted from `chartTopologicalRing`.
- **Hypotheses**: none.
- **Uses from project**: `chartS`, `chartTopology`, `chartTopologicalRing`.
- **Used by**: `chartIsUniformAddGroup`, `chartCompletionToBIProd`, `chartUniformity_eq`, `presheafChartToBIProd_coe`.
- **Visibility**: public
- **Lines**: 1108–1114 (definition 5 lines)
- **Notes**: **the only `set_option` in the file** — `set_option warn.classDefReducibility false in` on line 1108.

### `theorem chartIsUniformAddGroup`
- **Type**: `(a b : ℕ) : @IsUniformAddGroup (Localization.Away (chartS p F ϖ 1 b)) (chartUniformity p F ϖ a b) _`
- **What**: The chart uniformity is compatible with addition (uniform additive group).
- **How**: `@isUniformAddGroup_of_addCommGroup` applied to the topological-add-group structure from `chartTopologicalRing`.
- **Hypotheses**: none.
- **Uses from project**: `chartS`, `chartUniformity`, `chartTopology`, `chartTopologicalRing`.
- **Used by**: `chartCompletionToBIProd`, `presheafChartToBIProd_coe`.
- **Visibility**: public
- **Lines**: 1116–1122 (proof 3 lines)
- **Notes**: none.

### `def chartCompletionToBIProd`
- **Type**: `(a b : ℕ) (hb : 0 < b) (hπ1 hπ2 hr1 hr2 : window endpoint bounds) : (UniformSpace.Completion (Localization.Away (chartS p F ϖ 1 b))) →+* (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)` (with `letI` uniformity/ring/add-group instances in the statement)
- **What**: **The chart map extended to the completion** — the canonical continuous ring homomorphism from the completed chart localization to the product of completed fields (landing in `B^I` by density).
- **How**: `UniformSpace.Completion.extensionHom` applied to `chartToBIProd` with continuity from `continuous_chartToBIProd`, after installing `chartUniformity`, `chartTopologicalRing`, `chartIsUniformAddGroup` as local instances.
- **Hypotheses**: `0 < b` plus the four window-endpoint bounds.
- **Uses from project**: `chartS`, `hatK`, `chartUniformity`, `chartTopologicalRing`, `chartIsUniformAddGroup`, `chartToBIProd`, `continuous_chartToBIProd`.
- **Used by**: `presheafChartToBIProd`.
- **Visibility**: public
- **Lines**: 1124–1151 (definition 25 lines, mostly `letI` instance plumbing)
- **Notes**: instances appear both in the type (`letI …` inside the statement) and in the body.

### `theorem chartUniformity_eq`
- **Type**: `(a b : ℕ) : chartUniformity p F ϖ a b = (chartData p F ϖ 1 b a b).uniformSpace`
- **What**: The opaque chart uniformity is *definitionally* the `RationalLocData` uniformity of the chart datum.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `chartUniformity`, `chartData`, `RationalLocData.uniformSpace`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 1153–1155 (proof `rfl`)
- **Notes**: the defeq bridge that makes `presheafChartToBIProd` typecheck.

### `def presheafChartToBIProd`
- **Type**: `(a b : ℕ) (hb : 0 < b) (hπ1 hπ2 hr1 hr2 : window endpoint bounds) : presheafValue (chartData p F ϖ 1 b a b) →+* (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)`
- **What**: **The presheaf value of the chart datum maps to the product of completed fields**: the canonical continuous ring homomorphism `𝒪(R(T/s)) = A_inf⟨T/s⟩ →+* hatK ρ₁ × hatK ρ₂`.
- **How**: It *is* `chartCompletionToBIProd`, retyped: `presheafValue D` is by definition the completion of `Localization.Away D.s` at `D.uniformSpace`, which is defeq to `chartUniformity` (`chartUniformity_eq`).
- **Hypotheses**: `0 < b` plus the four window-endpoint bounds.
- **Uses from project**: `presheafValue` (`Presheaf.lean`), `chartData`, `hatK`, `chartCompletionToBIProd`.
- **Used by**: `presheafChartToBIProd_coe`.
- **Visibility**: public
- **Lines**: 1157–1170 (definition 3 lines after the long signature)
- **Notes**: this is the file's interface to the structure presheaf of `Spa(A_inf, A_inf)`.

### `theorem presheafChartToBIProd_coe`
- **Type**: `(a b : ℕ) (hb : 0 < b) (hπ1 hπ2 hr1 hr2 : window endpoint bounds) (z : Localization.Away (chartS p F ϖ 1 b)) : presheafChartToBIProd … a b hb hπ1 hπ2 hr1 hr2 ((chartData p F ϖ 1 b a b).coeRingHom z) = chartToBIProd p F ϖ … b hb z`
- **What**: The presheaf-value chart map genuinely extends the chart map along the completion coercion.
- **How**: After installing the three chart instances, it is `UniformSpace.Completion.extensionHom_coe` for `chartToBIProd` with `continuous_chartToBIProd`.
- **Hypotheses**: `0 < b` plus the four window-endpoint bounds.
- **Uses from project**: `presheafChartToBIProd`, `chartData`, `RationalLocData.coeRingHom`, `chartToBIProd`, `chartS`, `chartUniformity`, `chartTopologicalRing`, `chartIsUniformAddGroup`, `continuous_chartToBIProd`.
- **Used by**: unused in file (used 3× elsewhere in the project, in `ChartComparison.lean` / `BigWindows.lean`).
- **Visibility**: public
- **Lines**: 1172–1196 (proof 10 lines)
- **Notes**: none.

### `theorem exists_factor_toOF`
- **Type**: `(e : ℕ) (c : OF F) (h : perfectoidValuation p F (c : F) ≤ perfectoidValuation p F ↑(PseudoUniformizer.toOF F ϖ) ^ e) : ∃ c' : OF F, c = c' * PseudoUniformizer.toOF F ϖ ^ e`
- **What**: **Division by a pseudo-uniformizer power in `O_F`**: an element of value at most `|ϖ|^e` is divisible by `ϖ^e` in the valuation ring.
- **How**: The hypothesis and `mul_inv_cancel₀ (pow_ne_zero e hπ0)` give `|c·(ϖ^e)⁻¹| ≤ 1`; `(perfectoidValuation_integers p F).exists_of_le_one` (the `Valuation.Integers` API) produces `u ∈ O_F` whose image is `c/ϖ^e`; `Subtype.ext` plus `push_cast`/`inv_mul_cancel₀` (with `|ϖ| ≠ 0` from `PseudoUniformizer.toOF_ne_zero`) identifies `c = u·ϖ^e`.
- **Hypotheses**: `|c| ≤ |ϖ|^e`; `ϖ` a genuine pseudo-uniformizer (nonzero).
- **Uses from project**: `OF`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero` (`PerfectoidFieldCharP.lean`), `perfectoidValuation`, `perfectoidValuation_integers` (`GaussNorm.lean`).
- **Used by**: `exists_teichCoeff_factor_low`, `exists_teichCoeff_factor_high`.
- **Visibility**: public
- **Lines**: 1198–1226 (proof 23 lines)
- **Notes**: none.

### `theorem chartFracPi_pow_mul_p_pow`
- **Type**: `(e : ℕ) : chartFracPi p F ϖ ^ e * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ e) = algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ e)`
- **What**: `([ϖ]/p)^e · p^e = [ϖ]^e` in `Bloc`.
- **How**: First the `e = 1` case `chartFracPi · p = [ϖ]` by `IsUnit.val_inv_mul` on the unit `p`; then `map_pow`, `← mul_pow` and that identity.
- **Hypotheses**: none.
- **Uses from project**: `chartFracPi`, `Ainf`, `Bloc`, `teichPi`.
- **Used by**: `chart_term_low_eq`.
- **Visibility**: public
- **Lines**: 1228–1236 (proof 4 lines)
- **Notes**: none.

### `theorem chartFracP_pow_mul_teichPi_pow`
- **Type**: `(a b t : ℕ) : chartFracP p F ϖ a b ^ t * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ (b*t)) = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) ^ (a*t))`
- **What**: `(p^a/[ϖ]^b)^t · [ϖ]^{bt} = p^{at}` in `Bloc`.
- **How**: `AlocToBloc_teichPiInv_mul` at exponent `b·t` gives `([ϖ]⁻¹)^{bt}·[ϖ]^{bt} = 1`; unfolding `chartFracP` and collecting exponents with `mul_pow`/`pow_mul` reduces the goal to that.
- **Hypotheses**: none.
- **Uses from project**: `chartFracP`, `AlocToBloc`, `teichPiInvAloc`, `AlocToBloc_teichPiInv_mul`, `Ainf`, `Bloc`, `teichPi`.
- **Used by**: `chart_term_high_eq`, `chart_tail_eq`.
- **Visibility**: public
- **Lines**: 1238–1248 (proof 6 lines)
- **Notes**: none.

### `theorem teich_shift_low`
- **Type**: `(k m : ℕ) (hm : m ≤ k) (c c' : OF F) (hc : c = c' * PseudoUniformizer.toOF F ϖ ^ (2*k - m)) : teichPi p F ϖ ^ (k-m) * (WittVector.teichmuller p c' * ((p : Ainf p F)^m * teichPi p F ϖ ^ k)) = WittVector.teichmuller p c * (p : Ainf p F)^m`
- **What**: The pure `A_inf`-side identity behind the low-term split: shifting `[ϖ]^{k-m}` onto `[c']` reproduces `[c]`.
- **How**: Split `ϖ^{2k-m} = ϖ^{k-m}·ϖ^k` (exponent identity by `omega`), push through the multiplicativity of `WittVector.teichmuller` (`map_mul`) and `teichPi_pow`, then `ring`.
- **Hypotheses**: `m ≤ k` (so `2k-m ≥ k` and both truncated subtractions are honest); the divisibility relation `hc`.
- **Uses from project**: `teichPi`, `teichPi_pow` (`AinfHuber.lean`), `Ainf`, `OF`, `PseudoUniformizer.toOF`.
- **Used by**: `chart_term_low_eq`.
- **Visibility**: public
- **Lines**: 1251–1263 (proof 6 lines)
- **Notes**: none.

### `theorem teich_cross`
- **Type**: `(e f : ℕ) (c c' : OF F) (hc : c * PseudoUniformizer.toOF F ϖ ^ e = c' * PseudoUniformizer.toOF F ϖ ^ f) : WittVector.teichmuller p c' * teichPi p F ϖ ^ f = WittVector.teichmuller p c * teichPi p F ϖ ^ e`
- **What**: The `A_inf`-side cross identity: a relation between `O_F`-elements times uniformizer powers lifts to their Teichmüller representatives.
- **How**: `teichPi_pow` writes `[ϖ]^n = teichmuller (ϖ^n)`, then `← map_mul` on both sides turns the goal into `teichmuller` applied to the two sides of `hc`.
- **Hypotheses**: the `O_F`-relation `hc`.
- **Uses from project**: `teichPi`, `teichPi_pow`, `OF`, `PseudoUniformizer.toOF`.
- **Used by**: `high_arg_split`.
- **Visibility**: public
- **Lines**: 1265–1272 (proof 3 lines)
- **Notes**: none.

### `theorem chart_term_low_eq`
- **Type**: `(k m : ℕ) (hm : m ≤ k) (c c' : OF F) (hc : c = c' * ϖ^(2k-m)) : chartFracPi p F ϖ ^ (k-m) * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c') * algebraMap (Ainf p F) (Bloc p F ϖ) ((p * teichPi)^k) = algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c * (p : Ainf p F)^m)`
- **What**: **The low-term identity**: for `m ≤ k`, the chart-subring element `([ϖ]/p)^{k-m}·[c']` multiplied by the denominator `(p[ϖ])^k` gives exactly the `m`-th Teichmüller term `[c]·p^m`.
- **How**: Regroup `[c']·(p[ϖ])^k = p^{k-m}·([c']·(p^m[ϖ]^k))` (exponent split by `omega`, then `ring`), so `chartFracPi_pow_mul_p_pow` converts `([ϖ]/p)^{k-m}·p^{k-m}` into `[ϖ]^{k-m}`, and `teich_shift_low` finishes on the `A_inf` side.
- **Hypotheses**: `m ≤ k`, plus `c = c'·ϖ^{2k-m}` (supplied by `exists_teichCoeff_factor_low`).
- **Uses from project**: `chartFracPi`, `chartFracPi_pow_mul_p_pow`, `teich_shift_low`, `teichPi`, `Ainf`, `Bloc`, `OF`, `PseudoUniformizer.toOF`.
- **Used by**: `mem_chartSubring_of_wI_le`.
- **Visibility**: public
- **Lines**: 1274–1292 (proof 10 lines)
- **Notes**: none.

### `theorem high_arg_split`
- **Type**: `(b k t j : ℕ) (c c' : OF F) (hc : c * ϖ^(b*t) = c' * ϖ^k) : (p : Ainf p F)^j * WittVector.teichmuller p c' * ((p : Ainf p F) * teichPi p F ϖ)^k = teichPi p F ϖ ^ (b*t) * (WittVector.teichmuller p c * (p : Ainf p F)^(k+j))`
- **What**: The `A_inf`-side regrouping used for the high (`m > k`) Teichmüller terms.
- **How**: Expand `(p[ϖ])^k` with `mul_pow`, collect the `p`-powers into `p^{k+j}` (`pow_add`, `ring`), and replace `[c']·[ϖ]^k` by `[c]·[ϖ]^{bt}` using `teich_cross`.
- **Hypotheses**: the `O_F`-relation `hc`.
- **Uses from project**: `teich_cross`, `teichPi`, `Ainf`, `OF`, `PseudoUniformizer.toOF`.
- **Used by**: `chart_term_high_eq`.
- **Visibility**: public
- **Lines**: 1294–1313 (proof 12 lines)
- **Notes**: none.

### `theorem high_arg_final`
- **Type**: `(a k t j : ℕ) (c : OF F) : (p : Ainf p F)^(a*t) * (WittVector.teichmuller p c * (p : Ainf p F)^(k+j)) = WittVector.teichmuller p c * (p : Ainf p F)^(k + a*t + j)`
- **What**: The `A_inf`-side final `p`-power collection for the high terms.
- **How**: Reassociate the exponent `k + a·t + j = a·t + (k+j)` (`omega`), `pow_add`, `ring`.
- **Hypotheses**: none.
- **Uses from project**: `Ainf`, `OF`.
- **Used by**: `chart_term_high_eq`.
- **Visibility**: public
- **Lines**: 1315–1320 (proof 2 lines)
- **Notes**: none.

### `theorem chart_term_high_eq`
- **Type**: `(a b k t j : ℕ) (c c' : OF F) (hc : c * ϖ^(b*t) = c' * ϖ^k) : chartFracP p F ϖ a b ^ t * algebraMap … ((p : Ainf p F)^j * WittVector.teichmuller p c') * algebraMap … ((p * teichPi)^k) = algebraMap … (WittVector.teichmuller p c * (p : Ainf p F)^(k + a*t + j))`
- **What**: **The high-term identity**: the chart-subring element `(p^a/[ϖ]^b)^t·(p^j·[c'])` multiplied by the denominator gives the Teichmüller term `[c]·p^{k+at+j}`.
- **How**: `high_arg_split` regroups the `A_inf`-side into `[ϖ]^{bt}·([c]·p^{k+j})`; `chartFracP_pow_mul_teichPi_pow` then converts `(p^a/[ϖ]^b)^t·[ϖ]^{bt}` into `p^{at}`; `high_arg_final` collects the powers.
- **Hypotheses**: the `O_F`-relation `hc` (supplied by `exists_teichCoeff_factor_high`).
- **Uses from project**: `chartFracP`, `high_arg_split`, `chartFracP_pow_mul_teichPi_pow`, `high_arg_final`, `teichPi`, `Ainf`, `Bloc`, `OF`, `PseudoUniformizer.toOF`.
- **Used by**: `mem_chartSubring_of_wI_le`.
- **Visibility**: public
- **Lines**: 1322–1335 (proof 3 lines)
- **Notes**: none.

### `theorem tail_arg_split`
- **Type**: `(b k : ℕ) (hb : 0 < b) (z : Ainf p F) : teichPi p F ϖ ^ (b*k - k) * z * ((p : Ainf p F) * teichPi p F ϖ)^k = teichPi p F ϖ ^ (b*k) * ((p : Ainf p F)^k * z)`
- **What**: The `A_inf`-side regrouping for the tail term of the Teichmüller expansion.
- **How**: `mul_pow` and the exponent split `[ϖ]^{bk} = [ϖ]^{bk-k}·[ϖ]^k`, which needs `k ≤ b·k` — supplied by `Nat.le_mul_of_pos_left k hb` and `omega` — then `ring`.
- **Hypotheses**: `0 < b`.
- **Uses from project**: `teichPi`, `Ainf`.
- **Used by**: `chart_tail_eq`.
- **Visibility**: public
- **Lines**: 1337–1346 (proof 6 lines)
- **Notes**: none.

### `theorem tail_arg_final`
- **Type**: `(a k : ℕ) (z : Ainf p F) : (p : Ainf p F)^(a*k) * ((p : Ainf p F)^k * z) = (p : Ainf p F)^(k + a*k) * z`
- **What**: The `A_inf`-side final `p`-power collection for the tail.
- **How**: `Nat.add_comm`, `pow_add`, `ring`.
- **Hypotheses**: none.
- **Uses from project**: `Ainf`.
- **Used by**: `chart_tail_eq`.
- **Visibility**: public
- **Lines**: 1348–1353 (proof 2 lines)
- **Notes**: none.

### `theorem chart_tail_eq`
- **Type**: `(a b k : ℕ) (hb : 0 < b) (z : Ainf p F) : chartFracP p F ϖ a b ^ k * algebraMap … (teichPi p F ϖ ^ (b*k - k) * z) * algebraMap … ((p * teichPi)^k) = algebraMap … ((p : Ainf p F)^(k + a*k) * z)`
- **What**: **The tail identity**: the `p^N`-tail (`N = k + ak`) of the Teichmüller prefix decomposition is produced by the chart-subring element `(p^a/[ϖ]^b)^k·[ϖ]^{bk-k}·z`.
- **How**: `tail_arg_split` regroups on the `A_inf` side; `chartFracP_pow_mul_teichPi_pow` cancels `(p^a/[ϖ]^b)^k` against `[ϖ]^{bk}`; `tail_arg_final` collects the `p`-powers.
- **Hypotheses**: `0 < b`.
- **Uses from project**: `chartFracP`, `tail_arg_split`, `chartFracP_pow_mul_teichPi_pow`, `tail_arg_final`, `teichPi`, `Ainf`, `Bloc`.
- **Used by**: `mem_chartSubring_of_wI_le`.
- **Visibility**: public
- **Lines**: 1355–1364 (proof 2 lines)
- **Notes**: none.

### `theorem exists_teichCoeff_factor_low`
- **Type**: `(b k m : ℕ) (hm : m ≤ k) (hexact1 : perfectoidValuation p F ↑(PseudoUniformizer.toOF F ϖ) = ρ₁) (A : Ainf p F) {x : Bloc p F ϖ} (hx : x * algebraMap … ((p*teichPi)^k) = algebraMap … A) (hwI : wI … (BIProd … x) ≤ |ϖ|^b) : ∃ c' : OF F, teichCoeff p F A m = c' * PseudoUniformizer.toOF F ϖ ^ (2*k - m)`
- **What**: **Existence of the low-term factor**: at the exact left endpoint `ρ₁ = |ϖ|`, the Teichmüller coordinates `a_m` of the numerator with `m ≤ k` are divisible by `ϖ^{2k-m}`.
- **How**: `gaussTerm_le_of_wI_le` at `ρ = ρ₁ = |ϖ|` gives `|ϖ|^m·|a_m| ≤ |ϖ|^b·(|ϖ|·|ϖ|)^k`; the exponent identity `|ϖ|^b(|ϖ|²)^k = |ϖ|^m·|ϖ|^{2k-m+b}` (`pow_two`, `pow_mul`, `pow_add`, `omega`) lets `le_of_mul_le_mul_left (pow_pos hπ0 m)` cancel `|ϖ|^m`, leaving `|a_m| ≤ |ϖ|^{2k-m+b} ≤ |ϖ|^{2k-m}` (`pow_le_pow_of_le_one`, using `|ϖ| < 1`). Then `exists_factor_toOF` produces `c'`.
- **Hypotheses**: `m ≤ k`; the **exact** left endpoint `|ϖ| = ρ₁`; `wI(x) ≤ |ϖ|^b`.
- **Uses from project**: `gaussTerm_le_of_wI_le`, `gaussTerm`, `teichCoeff` (`GaussNorm.lean`), `exists_factor_toOF`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`, `wI`, `BIProd`, `Ainf`, `Bloc`, `teichPi`.
- **Used by**: `mem_chartSubring_of_wI_le`.
- **Visibility**: public
- **Lines**: 1367–1396 (proof 18 lines)
- **Notes**: none.

### `theorem exists_teichCoeff_factor_high`
- **Type**: `(a b k m : ℕ) (ha : 0 < a) (hm : k < m) (hexact2 : ρ₂^a = perfectoidValuation p F ↑(PseudoUniformizer.toOF F ϖ) ^ b) (A : Ainf p F) {x : Bloc p F ϖ} (hx : …) (hwI : wI … (BIProd … x) ≤ |ϖ|^b) : ∃ c' : OF F, teichCoeff p F A m * PseudoUniformizer.toOF F ϖ ^ (b * ((m-k)/a)) = c' * PseudoUniformizer.toOF F ϖ ^ k`
- **What**: **Existence of the high-term factor**: at the exact right endpoint `ρ₂^a = |ϖ|^b`, the coordinates with `m > k` satisfy `a_m·ϖ^{bt} ∈ ϖ^k·O_F` where `t = (m-k)/a`.
- **How**: First `|ϖ| < 1` is deduced from `ρ₂ < 1` and `hexact2` (with `b > 0` forced by `pow_lt_one₀`). `gaussTerm_le_of_wI_le` at `ρ₂` gives `ρ₂^m·X ≤ |ϖ|^b(ρ₂|ϖ|)^k` (`X = |a_m|`); cancelling `ρ₂^k` yields `ρ₂^i X ≤ |ϖ|^{b+k}` for `i = m-k`. Raising to the `a`-th power (`pow_le_pow_left₀`) and substituting `hexact2` turns this into `|ϖ|^{bi}X^a ≤ |ϖ|^{ab+ak}`. Euclidean division `Nat.div_add_mod i a` with `Nat.mod_lt` gives the exponent inequality `ka + bi ≤ ab + ak + bta`, so `pow_le_pow_of_le_one` (with `|ϖ| ≤ 1`) yields `X^a·|ϖ|^{bta} ≤ (|ϖ|^k)^a`, and `le_of_pow_le_pow_left₀ ha.ne'` extracts `X·|ϖ|^{bt} ≤ |ϖ|^k`. `exists_factor_toOF` then produces `c'`.
- **Hypotheses**: `0 < a`, `k < m`, the **exact** right endpoint `ρ₂^a = |ϖ|^b`, and `wI(x) ≤ |ϖ|^b`.
- **Uses from project**: `gaussTerm_le_of_wI_le`, `gaussTerm`, `teichCoeff`, `exists_factor_toOF`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`, `wI`, `BIProd`, `Ainf`, `Bloc`, `teichPi`.
- **Used by**: `mem_chartSubring_of_wI_le`.
- **Visibility**: public
- **Lines**: 1398–1484 (proof 73 lines)
- **Notes**: proof >30 lines; the trickiest arithmetic in the file (the `a`-th-power trick to move between `ρ₂` and `|ϖ|`).

### `theorem mem_chartSubring_of_wI_le`
- **Type**: `(a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hexact1 : |ϖ| = ρ₁) (hexact2 : ρ₂^a = |ϖ|^b) {x : Bloc p F ϖ} (hwI : wI … (BIProd … x) ≤ |ϖ|^b) : x ∈ Subring.closure (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ)) ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b})`
- **What**: **The reverse inclusion at the exact chart interval** (Kedlaya's plus-ring arithmetic on the dense layer): at exact endpoints, every element of `Bloc` in the `|ϖ|^b`-ball already lies in the subring generated by `A_inf` and the two chart fractions.
- **How**: `IsLocalization.surj` at `Submonoid.powers (p·[ϖ])` writes `x·(p[ϖ])^k = A`. Set `N = k + a·k` and use `exists_eq_sum_teichCoeff_add` to expand `A = ∑_{m<N} [a_m]p^m + p^N·z`. For each `m < N` a chart-subring witness `y m` with `y m·(p[ϖ])^k = [a_m]p^m` is produced: for `m ≤ k` by `exists_teichCoeff_factor_low` + `chart_term_low_eq`; for `m > k` by `exists_teichCoeff_factor_high` + `chart_term_high_eq` at `t = (m-k)/a`, `j = (m-k)%a` (with `Nat.div_add_mod`+`omega` to see `k + a·t + j = m`). The tail is handled by `chart_tail_eq`. Membership of each witness is `Subring.subset_closure` with `pow_mem`/`mul_mem`. Summing (`Finset.sum_congr`, `map_sum`) gives the total relation, and since `(p[ϖ])^k` is a unit in `Bloc` (`isUnit_p_teichPi_image`), `IsUnit.mul_right_cancel` identifies `x` with the sum, which is in the subring by `sum_mem`/`add_mem`.
- **Hypotheses**: `0 < a`, `0 < b`, **both exact endpoints** `|ϖ| = ρ₁` and `ρ₂^a = |ϖ|^b`, and `wI(x) ≤ |ϖ|^b`.
- **Uses from project**: `Bloc`, `Ainf`, `teichPi`, `chartFracPi`, `chartFracP`, `wI`, `BIProd`, `teichCoeff`, `exists_eq_sum_teichCoeff_add` (`GaussNorm.lean`), `exists_teichCoeff_factor_low`, `exists_teichCoeff_factor_high`, `chart_term_low_eq`, `chart_term_high_eq`, `chart_tail_eq`, `isUnit_p_teichPi_image` (`RobbaLoc.lean`), `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`.
- **Used by**: `exists_p_pow_mul_mem_chartSubring`.
- **Visibility**: public
- **Lines**: 1487–1567 (proof 67 lines)
- **Notes**: proof >30 lines; the mathematical core of the reverse direction (Kedlaya §2 plus-ring arithmetic).

### `theorem exists_p_pow_mul_mem_chartSubring`
- **Type**: `(a b n : ℕ) (ha : 0 < a) (hb : 0 < b) (hexact1 : |ϖ| = ρ₁) (hexact2 : ρ₂^a = |ϖ|^b) {x : Bloc p F ϖ} (hwI : wI … (BIProd … x) ≤ min ρ₁ ρ₂ ^ n * |ϖ|^b) : ∃ x' ∈ Subring.closure (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ)) ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b}), x = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)^n) * x'`
- **What**: **The scaled reverse inclusion**: an element in the smaller ball `min(ρ₁,ρ₂)^n·|ϖ|^b` is `p^n` times a chart-subring element.
- **How**: Put `x' = (p⁻¹)^n·x` using the unit `p` (`isUnit_p_image`); `IsUnit.mul_val_inv` gives `x = p^n·x'`. At each radius, `wLoc_p_inv` computes `wLoc(x') = (ρ⁻¹)^n·wLoc(x)`, and combining `wLoc(x) ≤ min(ρ₁,ρ₂)^n|ϖ|^b` with `min ρ₁ ρ₂ ≤ ρ` (`pow_le_pow_left₀`) and `inv_mul_cancel₀ hρ0.ne'` yields `wLoc(x') ≤ |ϖ|^b`; `max_le` upgrades this to `wI(x') ≤ |ϖ|^b`. Then `mem_chartSubring_of_wI_le` applies to `x'`.
- **Hypotheses**: `0 < a`, `0 < b`, both exact endpoints, and the scaled ball bound.
- **Uses from project**: `Bloc`, `Ainf`, `chartFracPi`, `chartFracP`, `wI`, `BIProd`, `wI_BIProd`, `valued_BlocToHatK`, `wLoc`, `wLoc_p_inv`, `isUnit_p_image`, `mem_chartSubring_of_wI_le`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`.
- **Used by**: `ball_le_locNhd`.
- **Visibility**: public
- **Lines**: 1569–1624 (proof 42 lines)
- **Notes**: proof >30 lines.

### `theorem ball_le_locNhd`
- **Type**: `(a b n : ℕ) (ha : 0 < a) (hb : 0 < b) (hexact1 : |ϖ| = ρ₁) (hexact2 : ρ₂^a = |ϖ|^b) {z : Localization.Away (chartS p F ϖ 1 b)} (hz : wI … (BIProd … (blocEquivAwayChartS p F ϖ b hb z)) ≤ min ρ₁ ρ₂ ^ n * |ϖ|^b) : z ∈ locNhd (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b) n`
- **What**: **The reverse basis inclusion**: the `min(ρ₁,ρ₂)^n·|ϖ|^b`-ball of the chart localization sits inside the `n`-th basic neighbourhood of `0` for the chart topology. Together with `exists_locNhd_le_ball` this is the two-sided topology comparison.
- **How**: `exists_p_pow_mul_mem_chartSubring` writes the image of `z` as `p^n·x'` with `x'` in the chart subring; `map_locSubring_chartData` (used right-to-left) pulls `x'` back to some `y ∈ locSubring`, and injectivity of `blocEquivAwayChartS` together with `blocEquivAwayChartS_algebraMap` gives `z = p^n·y` in the localization. Since `p ∈ I_inf` (`Ideal.subset_span`), `algebraMapD` of `p` lies in `locIdeal` (`Ideal.mem_map_of_mem`), so `w = (algebraMapD p)^n · ⟨y, …⟩ ∈ locIdeal^n` (`Ideal.pow_mem_pow`, `Ideal.mul_mem_right`) and its coercion is exactly `z`, exhibiting `z ∈ locNhd … n`.
- **Hypotheses**: `0 < a`, `0 < b`, both exact endpoints, and the scaled ball bound.
- **Uses from project**: `chartS`, `chartT`, `podAinf`, `locNhd`, `locIdeal`, `locSubring`, `algebraMapD`, `blocEquivAwayChartS`, `blocEquivAwayChartS_algebraMap`, `map_locSubring_chartData`, `exists_p_pow_mul_mem_chartSubring`, `Iinf`, `wI`, `BIProd`, `Ainf`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`.
- **Used by**: unused in file (used 2× elsewhere in the project).
- **Visibility**: public
- **Lines**: 1626–1670 (proof 32 lines)
- **Notes**: proof >30 lines; the file's final result.

---

### File Summary
- **Total declarations**: 67 (15 defs, 51 lemmas/theorems, 1 instance — the anonymous file-`local` `DecidableEq (Ainf p F)` at line 95)
- **Key API (used by 3+ others in this file)**: `podAinf` (9), `chartT` (12), `chartS` (25), `chartMonomials` (4), `chartData` (7), `blocEquivAwayChartS` (10), `chartFracPi` (8), `chartFracP` (9), `blocUnitBall` (3), `blocEquivAwayChartS_algebraMap` (3), `Iinf_pow_le_span_chartMonomials` (3), `isLocalization_chartS_Bloc` (4), `chartToBIProd` (4), `chartTopology` (6), `chartTopologicalRing` (5), `chartUniformity` (4)
- **Unused declarations** (no in-file consumer): `isRational_chartData`, `windowU_zero_eq_rationalOpen`, `windowV_zero_eq_rationalOpen`, `chartUniformity_eq`, `presheafChartToBIProd_coe`, `ball_le_locNhd`. Of these, `presheafChartToBIProd_coe` (3 uses) and `ball_le_locNhd` (2 uses) are consumed downstream in `FarguesFontaine/ChartComparison.lean` and `FarguesFontaine/BigWindows.lean`; `isRational_chartData`, `windowU_zero_eq_rationalOpen`, `windowV_zero_eq_rationalOpen`, `chartUniformity_eq` currently have **no consumer anywhere in the project** (they are headline exports / defeq bridges).
- **Declarations with sorry**: none — the file is sorry-free.
- **Declarations with set_option**: `chartUniformity` (`set_option warn.classDefReducibility false in`, line 1108). No `maxHeartbeats` bumps anywhere.
- **Proofs >30 lines**:
  - `Iinf_pow_le_span_chartMonomials` — 39
  - `span_chartMonomials_le_divBySIdeal` — 38
  - `isRational_chartData` — 46
  - `mem_rationalOpen_chartData_iff` — 80
  - `isLocalization_chartS_Bloc` — 42
  - `blocEquiv_divByS_teichPi` — 31
  - `blocEquiv_divByS_p` — 34
  - `map_locSubring_chartData` — 31
  - `gaussValue_le_of_mem_Iinf_pow` — 54
  - `wI_le_of_mem_locIdeal_pow` — 75
  - `exists_teichCoeff_factor_high` — 73
  - `mem_chartSubring_of_wI_le` — 67
  - `exists_p_pow_mul_mem_chartSubring` — 42
  - `ball_le_locNhd` — 32
  - (borderline, exactly 30: `wI_chartFracP_le_one`, `blocUnitBall`'s structure body)
