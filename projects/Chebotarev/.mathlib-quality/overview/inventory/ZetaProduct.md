# Inventory: `ZetaProduct.lean`

Project: Chebotarev. File: `projects/Chebotarev/CebotarevDensity/ZetaProduct.lean` (3176 lines).
Namespace `Chebotarev`; whole file `@[expose] public section` + `noncomputable section`.

All decls carry the standard number-field instance bundle `[Field K] [NumberField K] [Field L]
[NumberField L] [Algebra K L] [IsGalois K L]`; below this is abbreviated **NF-bundle**. Many add
`[FiniteDimensional K L]`, `[IsMulCommutative Gal(L/K)]` (abbreviated **abelian**), and the
cyclotomic data `(m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]` (abbreviated **cyclo m**).

---

### `abbrev galoisCharacter`
- **Type**: `(K L : Type*) [NF-bundle] : Type _ := Gal(L/K) →* ℂˣ`
- **What**: A character of the Galois group `Gal(L/K)` valued in `ℂ^×`.
- **How**: Plain type abbreviation for the monoid-hom type.
- **Hypotheses**: `L/K` a Galois extension of number fields.
- **Uses from project**: []
- **Used by**: nearly every decl in the file (the central object).
- **Visibility**: public
- **Lines**: 71–73 (proof 0)
- **Notes**: none

### `def galoisCharacterOnIdeal`
- **Type**: `(K L) [NF-bundle] (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)) : ℂ` = product over `normalizedFactors 𝔞` `.toFinset` of `(if UnramifiedIn K L 𝔭 then χ(Frob 𝔭).out else 0) ^ count`
- **What**: The completely-multiplicative extension `χ̃(𝔞)` of a Galois character to nonzero ideals (Sharifi Notation 7.1.17): `χ(Frob 𝔭)` at unramified primes, `0` at ramified, multiplicative over factorisation.
- **How**: Direct `Finset.prod` over the prime-factor finset with per-factor power.
- **Hypotheses**: NF-bundle; `χ` a character.
- **Uses from project**: [`galoisCharacter`, `UnramifiedIn`, `frobeniusClass` (Frobenius import)]
- **Used by**: `galoisCharacterOnIdeal_eq_map_prod`, `_apply_prime`, `_mul`, `_one`, `norm_galoisCharacterOnIdeal_le_one`, `exists_artinLSeries_eulerProduct_abelian`, and downstream throughout.
- **Visibility**: public
- **Lines**: 75–84 (proof 0, a def)
- **Notes**: `open Classical in`

### `theorem galoisCharacterOnIdeal_eq_map_prod`
- **Type**: `(K L) [NF-bundle] (χ) (𝔞)` : `galoisCharacterOnIdeal K L χ 𝔞 = ((normalizedFactors 𝔞).map (fun 𝔭 ↦ if … then χ(Frob 𝔭).out else 0)).prod`
- **What**: Rewrites `χ̃(𝔞)` as a `Multiset.map`-product over factors *with multiplicity* instead of `toFinset`+`count`.
- **How**: `Finset.prod_multiset_map_count`.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`galoisCharacterOnIdeal`]
- **Used by**: `_apply_prime`, `_mul`, `_one`, `norm_…_le_one`, `galoisCharacterOnIdeal_eq_char_frobeniusIdeal`, `unramifiedIn_of_mem_…`, `galoisCharacterOnIdeal_mem_insert_zero_nthRootsFinset`
- **Visibility**: private
- **Lines**: 86–97 (proof ~1)
- **Notes**: `open Classical in`

### `theorem galoisCharacterOnIdeal_apply_prime`
- **Type**: `(K L) [NF-bundle] (χ) (𝔭) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥)` : `χ̃(𝔭) = if UnramifiedIn K L 𝔭 then χ(Frob 𝔭).out else 0`
- **What**: Evaluates the ideal character on a nonzero prime.
- **How**: `normalizedFactors_irreducible` collapses the factor multiset to a singleton, then `Multiset.prod_singleton`.
- **Hypotheses**: NF-bundle; `𝔭` prime, nonzero.
- **Uses from project**: [`galoisCharacterOnIdeal_eq_map_prod`, `UnramifiedIn`, `frobeniusClass`]
- **Used by**: `exists_artinLSeries_eulerProduct_abelian`
- **Visibility**: public
- **Lines**: 99–111 (proof ~3)
- **Notes**: `open Classical in`

### `theorem galoisCharacterOnIdeal_mul`
- **Type**: `(K L) [NF-bundle] (χ) {𝔞 𝔟} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥)` : `χ̃(𝔞·𝔟) = χ̃(𝔞)·χ̃(𝔟)`
- **What**: Complete multiplicativity of the ideal character on nonzero ideals.
- **How**: `normalizedFactors_mul` + `Multiset.map_add` + `Multiset.prod_add`.
- **Hypotheses**: NF-bundle; `𝔞,𝔟` nonzero.
- **Uses from project**: [`galoisCharacterOnIdeal_eq_map_prod`]
- **Used by**: `exists_artinLSeries_eulerProduct_abelian`
- **Visibility**: public
- **Lines**: 113–122 (proof ~3)
- **Notes**: none

### `theorem galoisCharacterOnIdeal_one`
- **Type**: `(K L) [NF-bundle] (χ)` : `χ̃(⊤) = 1` ; `@[simp]`
- **What**: The ideal character of the unit ideal is `1` (empty product).
- **How**: `normalizedFactors_one` → empty multiset → `Multiset.prod_zero`.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`galoisCharacterOnIdeal_eq_map_prod`]
- **Used by**: `exists_artinLSeries_eulerProduct_abelian`
- **Visibility**: public
- **Lines**: 124–130 (proof ~2)
- **Notes**: none

### `theorem norm_galoisCharacter_out`
- **Type**: `(K L) [NF-bundle] (χ) (c : ConjClasses Gal(L/K))` : `‖(χ c.out : ℂ)‖ = 1`
- **What**: A Galois-character value on a conjugacy-class representative is a root of unity, so has norm `1`.
- **How**: finiteness of `Gal(L/K)` ⇒ `isOfFinOrder` ⇒ `norm_eq_one`.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`galoisCharacter`]
- **Used by**: `norm_galoisCharacterOnIdeal_le_one`, `multipliable_artinLocalFactor`
- **Visibility**: private
- **Lines**: 159–165 (proof 0, term)
- **Notes**: none

### `theorem norm_galoisCharacterOnIdeal_le_one`
- **Type**: `(K L) [NF-bundle] (χ) (𝔞)` : `‖χ̃(𝔞)‖ ≤ 1`
- **What**: The ideal character has norm `≤ 1`.
- **How**: `Finset.prod_le_one`; each factor is `0` (ramified) or a norm-`1` root of unity (unramified) via `norm_galoisCharacter_out`.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`galoisCharacterOnIdeal`, `norm_galoisCharacter_out`, `UnramifiedIn`]
- **Used by**: `norm_galoisCharacterCoeff_le`, `lseries_galoisCharacterCoeff_eq_tsum`, `log_norm_artinDirichletSeries_one_le`
- **Visibility**: private
- **Lines**: 167–180 (proof ~7)
- **Notes**: `open Classical in`

### `theorem exists_artinLSeries_eulerProduct_abelian`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian] (χ)` : `∀ s, 1 < s.re → (∏'_{𝔭 prime,unram} (1 - χ(Frob 𝔭).out · N𝔭^{-s})⁻¹) = ∑'_{𝔞≠⊥} χ̃(𝔞)·N𝔞^{-s}`
- **What**: Sharifi 7.1.18 — the abelian Euler product equals the Dirichlet series of the ideal character, on `Re s > 1`.
- **How**: instantiates the generic `weighted_eulerProduct_eq_tsum` (CyclotomicNormResidue import) with weight `χ̃`; ramified factors drop out (weight `0`, local factor `1`); `galoisCharacterOnIdeal_apply_prime` identifies the unramified factors. ~25-line proof hinging on `weighted_eulerProduct_eq_tsum` and an injectivity/mulSupport reindex.
- **Hypotheses**: NF-bundle, finite-dim, abelian.
- **Uses from project**: [`galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `galoisCharacterOnIdeal`, `weighted_eulerProduct_eq_tsum`, `galoisCharacterOnIdeal_one`, `galoisCharacterOnIdeal_mul`, `norm_galoisCharacterOnIdeal_le_one`, `galoisCharacterOnIdeal_apply_prime`]
- **Used by**: `tprod_unramified_eq_prod_artinDirichletSeries`
- **Visibility**: public
- **Lines**: 182–226 (proof ~25)
- **Notes**: none

### `theorem prod_one_sub_nthRoots`
- **Type**: `(f : ℕ) (hf : 0 < f) (Y : ℂ)` : `∏_{ζ ∈ μ_f} (1 - ζ·Y) = 1 - Y^f`
- **What**: Roots-of-unity factorisation specialised at `x = 1`.
- **How**: `IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul` at `x = 1`.
- **Hypotheses**: `f > 0`.
- **Uses from project**: []
- **Used by**: `prod_galoisCharacter_one_sub`
- **Visibility**: private
- **Lines**: 241–246 (proof ~1)
- **Notes**: none

### `def charEval`
- **Type**: `{G} [CommGroup G] [Finite G] (σ : G)` : `(G →* ℂˣ) →* ℂˣ`
- **What**: The evaluation homomorphism `χ ↦ χ σ` on the dual group, via the double-dual identification.
- **How**: `(CommGroup.monoidHomMonoidHomEquiv G ℂ).symm σ`.
- **Hypotheses**: `G` finite commutative.
- **Uses from project**: []
- **Used by**: `charEval_apply`, `charEval_ker_card`, `prod_galoisCharacter_one_sub`
- **Visibility**: private
- **Lines**: 248–251 (proof 0, def)
- **Notes**: none

### `theorem charEval_apply`
- **Type**: `{G} [CommGroup G] [Finite G] (σ) (φ : G →* ℂˣ)` : `charEval σ φ = φ σ`
- **What**: `charEval` evaluates a character at `σ`.
- **How**: `monoidHomMonoidHomEquiv_symm_apply_apply`.
- **Hypotheses**: `G` finite commutative.
- **Uses from project**: [`charEval`]
- **Used by**: `charEval_ker_card`, `prod_galoisCharacter_one_sub`
- **Visibility**: private
- **Lines**: 253–254 (proof ~1)
- **Notes**: none

### `theorem charEval_ker_card`
- **Type**: `{G} [CommGroup G] [Finite G] (σ)` : `Nat.card (charEval σ).ker = Nat.card G / orderOf σ`
- **What**: The kernel of evaluation-at-`σ` has order `|G| / orderOf σ`.
- **How**: identifies kernel with `(restrictHom ⟨σ⟩).ker`, then `CommGroup.card_restrictHom_ker` + Lagrange (`card_eq_card_quotient_mul_card_subgroup`) + `Nat.card_zpowers`.
- **Hypotheses**: `G` finite commutative.
- **Uses from project**: [`charEval`, `charEval_apply`]
- **Used by**: `prod_galoisCharacter_one_sub`
- **Visibility**: private
- **Lines**: 256–273 (proof ~14)
- **Notes**: long-ish (14); no flag

### `theorem prod_galoisCharacter_one_sub`
- **Type**: `{G} [CommGroup G] [Finite G] [Fintype (G →* ℂˣ)] (σ) (Y : ℂ)` : `∏_{χ} (1 - χ(σ)·Y) = (1 - Y^{orderOf σ})^{|G|/orderOf σ}`
- **What**: The character-product identity at the heart of Sharifi 7.1.16 (group-theoretic).
- **How**: evaluation map `χ ↦ χ(σ)` surjects onto `μ_f` (`f = orderOf σ`) with uniform fibres of size `|G|/f` (`MonoidHom.card_fiber_eq_of_mem_range`, `charEval_ker_card`, `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`); product factors over `μ_f` (`Finset.prod_fiberwise_of_maps_to'`) and collapses via `prod_one_sub_nthRoots`. ~63-line proof.
- **Hypotheses**: `G` finite commutative, `Fintype` on dual.
- **Uses from project**: [`charEval`, `charEval_apply`, `charEval_ker_card`, `prod_one_sub_nthRoots`]
- **Used by**: `dedekindZeta_local_factor_eq_product_artin_local`
- **Visibility**: private
- **Lines**: 275–344 (proof ~63)
- **Notes**: **OVER-50 — needs further /decompose-proof pass**; `open Finset in`

### `theorem cpow_neg_absNorm_eq_pow`
- **Type**: `{a b : ℕ} (f : ℕ) (s : ℂ) (h : b = a^f)` : `(b:ℂ)^(-s) = ((a:ℂ)^(-s))^f`
- **What**: If `N𝔓 = N𝔭^f` then `N𝔓^{-s} = (N𝔭^{-s})^f`.
- **How**: `Complex.natCast_cpow_natCast_mul` + `Complex.cpow_nat_mul`.
- **Hypotheses**: `b = a^f`.
- **Uses from project**: []
- **Used by**: `dedekindZeta_local_factor_eq_product_artin_local`
- **Visibility**: private
- **Lines**: 346–350 (proof ~1)
- **Notes**: none

### `theorem dedekindZeta_local_factor_eq_product_artin_local`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian] (𝔭) [𝔭.IsPrime] (_hunr : UnramifiedIn K L 𝔭) (s) (_hs : 1 < s.re)` : `∏'_{𝔓|𝔭} (1 - N𝔓^{-s})⁻¹ = ∏'_{χ} (1 - χ(Frob 𝔭).out · N𝔭^{-s})⁻¹`
- **What**: Sharifi 7.1.16 local step — the local Euler factor of `ζ_L` at an unramified prime factors over characters.
- **How**: both sides reduce to `(1 - Y^f)^{±g}` with `f = orderOf σ`, `g = |G|/f`; right side via `prod_galoisCharacter_one_sub`; left side counts `g` primes above (`card_primesAbove_mul_orderOf_eq`) each with `N𝔓 = N𝔭^f` (`absNorm_eq_pow_inertiaDeg_of_liesOver`, `finrank_residue_eq_orderOf`, `inertiaDeg = f`). ~50-line proof.
- **Hypotheses**: NF-bundle, finite-dim, abelian; `𝔭` prime, unramified.
- **Uses from project**: [`frobeniusClass`, `UnramifiedIn`, `galoisCharacter`, `prod_galoisCharacter_one_sub`, `card_primesAbove_mul_orderOf_eq`, `finrank_residue_eq_orderOf` (Frobenius import), `cpow_neg_absNorm_eq_pow`, `UnramifiedIn.ne_bot`]
- **Used by**: `tprod_unramified_eq_prod_artinDirichletSeries`
- **Visibility**: public
- **Lines**: 352–409 (proof ~46)
- **Notes**: long (30–50) — ~46 lines; `open scoped IsMulCommutative`

### `def frobeniusIdeal`
- **Type**: `(K L) [NF-bundle] [abelian] (𝔞 : Ideal (𝓞 K)) : Gal(L/K)` = `(normalizedFactors 𝔞).map (Frob ·.out)).prod`
- **What**: The `Gal(L/K)`-valued completely-multiplicative ideal Frobenius `Frob_𝔞` (a genuine group element since the group is abelian).
- **How**: `Multiset.prod` of chosen Frobenius reps over the prime factors (commutativity from `IsMulCommutative`).
- **Hypotheses**: NF-bundle, abelian.
- **Uses from project**: [`frobeniusClass`]
- **Used by**: `frobeniusIdeal_apply_prime`, `_mul`, `_one`, `galoisCharacterOnIdeal_eq_char_frobeniusIdeal`, and most of the geometry-of-numbers chain.
- **Visibility**: public
- **Lines**: 441–453 (proof 0, def)
- **Notes**: `open Classical in`

### `theorem frobeniusIdeal_apply_prime`
- **Type**: `(K L) [NF-bundle] [abelian] (𝔭) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥)` : `frobeniusIdeal K L 𝔭 = (frobeniusClass K L 𝔭).out` ; `@[simp]`
- **What**: `Frob_𝔭` of a prime is the chosen Frobenius rep.
- **How**: `normalizedFactors_irreducible` singleton collapse + `Multiset.prod_singleton`.
- **Hypotheses**: NF-bundle, abelian; `𝔭` prime, nonzero.
- **Uses from project**: [`frobeniusIdeal`, `frobeniusClass`]
- **Used by**: `autToPow_frobeniusIdeal`
- **Visibility**: public
- **Lines**: 455–464 (proof ~3)
- **Notes**: `open Classical in`

### `theorem frobeniusIdeal_mul`
- **Type**: `(K L) [NF-bundle] [abelian] {𝔞 𝔟} (h𝔞) (h𝔟)` : `frobeniusIdeal K L (𝔞·𝔟) = frobeniusIdeal K L 𝔞 · frobeniusIdeal K L 𝔟`
- **What**: Complete multiplicativity of `Frob_·` on nonzero ideals.
- **How**: `normalizedFactors_mul` + `Multiset.map_add` + `Multiset.prod_add`.
- **Hypotheses**: NF-bundle, abelian; `𝔞,𝔟` nonzero.
- **Uses from project**: [`frobeniusIdeal`]
- **Used by**: `autToPow_frobeniusIdeal`, `card_good_fibre_eq_card_residue`, `card_fibre_eq_card_good_fibre`, `realizedResidues` chain.
- **Visibility**: public
- **Lines**: 466–473 (proof ~3)
- **Notes**: none

### `theorem frobeniusIdeal_one`
- **Type**: `(K L) [NF-bundle] [abelian]` : `frobeniusIdeal K L ⊤ = 1` ; `@[simp]`
- **What**: `Frob_⊤ = 1` (empty product).
- **How**: `normalizedFactors_one` → empty multiset → `prod_zero`.
- **Hypotheses**: NF-bundle, abelian.
- **Uses from project**: [`frobeniusIdeal`]
- **Used by**: `autToPow_frobeniusIdeal`, `card_fibre_bound_eq_one`
- **Visibility**: public
- **Lines**: 475–482 (proof ~2)
- **Notes**: none

### `theorem galoisCharacterOnIdeal_eq_char_frobeniusIdeal`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian] (cyclo m) (χ) {𝔞} (hU : ∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭)` : `χ̃(𝔞) = χ(Frob_𝔞)`
- **What**: Helper 1 — on unramified-supported `𝔞`, the multiplicative ideal character equals `χ` of the ideal Frobenius.
- **How**: push `χ` through the `frobeniusIdeal` multiset product (`map_multiset_prod`), then match factor-by-factor using `hU` to discharge the `if`.
- **Hypotheses**: NF-bundle, finite-dim, abelian, cyclo m; all factors of `𝔞` unramified.
- **Uses from project**: [`galoisCharacter`, `frobeniusIdeal`, `frobeniusClass`, `galoisCharacterOnIdeal_eq_map_prod`, `UnramifiedIn`]
- **Used by**: `card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre`, `galoisCharacterOnIdeal_mem_insert_zero_nthRootsFinset`
- **Visibility**: public
- **Lines**: 484–505 (proof ~10)
- **Notes**: `open Classical in`

### `theorem unramifiedIn_of_mem_normalizedFactors_of_galoisCharacterOnIdeal_ne_zero`
- **Type**: `(K L) [NF-bundle] (χ) {𝔞 𝔭} (h : χ̃(𝔞) ≠ 0) (h𝔭 : 𝔭 ∈ normalizedFactors 𝔞)` : `UnramifiedIn K L 𝔭`
- **What**: If `χ̃(𝔞) ≠ 0` then every prime factor of `𝔞` is unramified.
- **How**: contrapositive — a ramified factor zeroes the product (`Multiset.prod_eq_zero`).
- **Hypotheses**: NF-bundle; `χ̃(𝔞) ≠ 0`.
- **Uses from project**: [`galoisCharacter`, `galoisCharacterOnIdeal`, `galoisCharacterOnIdeal_eq_map_prod`, `UnramifiedIn`]
- **Used by**: `card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre`
- **Visibility**: private
- **Lines**: 507–517 (proof ~5)
- **Notes**: `open Classical in`

### `theorem card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian] (cyclo m) (χ) (ζ : ℂ) (hζ : ζ ≠ 0) (N)` : `Nat.card {𝔞 ≠ ⊥ ∧ N𝔞 ≤ N ∧ χ̃(𝔞) = ζ} = Nat.card {𝔞 ≠ ⊥ ∧ N𝔞 ≤ N ∧ U 𝔞 ∧ χ(Frob_𝔞) = ζ}`
- **What**: Helper 1a — for `ζ ≠ 0` the value-fibre equals the unramified-supported Frobenius-value-fibre.
- **How**: `Equiv.subtypeEquivRight`; forward uses `unramifiedIn_of_mem_…_ne_zero` to get `U`, then Helper 1; backward applies Helper 1 directly.
- **Hypotheses**: NF-bundle, finite-dim, abelian, cyclo m; `ζ ≠ 0`.
- **Uses from project**: [`galoisCharacter`, `galoisCharacterOnIdeal`, `frobeniusIdeal`, `UnramifiedIn`, `unramifiedIn_of_mem_normalizedFactors_of_galoisCharacterOnIdeal_ne_zero`, `galoisCharacterOnIdeal_eq_char_frobeniusIdeal`]
- **Used by**: `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`
- **Visibility**: public
- **Lines**: 519–548 (proof ~11)
- **Notes**: `open Classical in`

### `theorem charFibre_mem_range`
- **Type**: `{G} [CommGroup G] [Finite G] (χ : G →* ℂˣ) (ζ : ℂˣ) (hζ : ζ^{orderOf χ} = 1)` : `∃ g, χ g = ζ`
- **What**: The image of a finite-abelian-group character is exactly `μ_{orderOf χ}`, so any `ζ` with `ζ^{ord} = 1` is hit.
- **How**: shows `range χ = rootsOfUnity (orderOf χ) ℂ` via `Subgroup.eq_of_le_of_card_ge`, matching exponent (`IsCyclic.exponent_eq_card`) to `Complex.card_rootsOfUnity`. ~24-line proof.
- **Hypotheses**: `G` finite commutative; `ζ^{ord} = 1`.
- **Uses from project**: []
- **Used by**: `card_charFibre_eq_card_ker`
- **Visibility**: public
- **Lines**: 550–578 (proof ~24)
- **Notes**: long (30–50)? — proof is ~24 lines, below 30; no flag

### `theorem card_charFibre_eq_card_ker`
- **Type**: `{G} [CommGroup G] [Finite G] (χ) (ζ : ℂˣ) (hζ : ζ^{orderOf χ} = 1)` : `Nat.card {g // χ g = ζ} = Nat.card (MonoidHom.ker χ)`
- **What**: Helper 1b — the character fibre over `ζ` is a coset of `ker χ`, so has cardinality `|ker χ|` independent of `ζ`.
- **How**: `charFibre_mem_range` to get a base point `g₀`, then `χ.fiberEquivKer g₀`.
- **Hypotheses**: `G` finite commutative; `ζ^{ord} = 1`.
- **Uses from project**: [`charFibre_mem_range`]
- **Used by**: `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`
- **Visibility**: public
- **Lines**: 580–590 (proof ~4)
- **Notes**: none

### `theorem unramifiedIn_of_coprime_absNorm`
- **Type**: `(K L) [NF-bundle] (cyclo m) (𝔭) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) (hcop : (N𝔭).Coprime m)` : `UnramifiedIn K L 𝔭`
- **What**: A nonzero prime with norm coprime to `m` is unramified in `L = K(μ_m)`.
- **How**: different-ideal criterion (`not_dvd_differentIdeal_iff`); a ramified `𝔭` would divide the different, which divides `aeval ζ (minpoly)'` via `conductor_mul_differentIdeal`; since `minpoly ∣ X^m − 1`, that value divides `m·ζ^{m−1}`, forcing `m ∈ 𝔓`, so `N𝔭 ∣ m^d`, contradicting coprimality. ~55-line proof.
- **Hypotheses**: NF-bundle, cyclo m; `𝔭` prime, nonzero, norm coprime to `m`.
- **Uses from project**: [`UnramifiedIn`]
- **Used by**: `autToPow_frobeniusIdeal`, `card_fibre_eq_card_good_fibre`
- **Visibility**: private
- **Lines**: 614–673 (proof ~55)
- **Notes**: **OVER-50 — needs further /decompose-proof pass** (~55 lines)

### `theorem autToPow_frobeniusIdeal`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian] (cyclo m) {ζ} (hζ : IsPrimitiveRoot ζ m) (𝔠) (h𝔠 : 𝔠 ≠ ⊥) (hcop : (N𝔠).Coprime m)` : `hζ.autToPow K (frobeniusIdeal K L 𝔠) = ZMod.unitOfCoprime (N𝔠) hcop`
- **What**: On a coprime-norm ideal the cyclotomic character sends `Frob_𝔠` to its norm residue.
- **How**: `UniqueFactorizationMonoid.induction_on_prime`; prime case is `autToPow_frobeniusClass_out` (Frobenius import); multiplicativity via `frobeniusIdeal_mul` + coprimality split.
- **Hypotheses**: NF-bundle, finite-dim, abelian, cyclo m; `hζ` primitive, `𝔠` nonzero, coprime norm.
- **Uses from project**: [`frobeniusIdeal`, `frobeniusIdeal_one`, `frobeniusIdeal_mul`, `frobeniusIdeal_apply_prime`, `autToPow_frobeniusClass_out`, `unramifiedIn_of_coprime_absNorm`]
- **Used by**: `card_good_fibre_eq_card_residue`
- **Visibility**: private
- **Lines**: 675–710 (proof ~25)
- **Notes**: long-ish (~25); no 30+ flag

### `theorem card_good_fibre_eq_card_residue`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian] (cyclo m) {ζ} (hζ) (h : Gal(L/K)) (X : ℕ)` : `Nat.card {𝔠 ≠ ⊥ ∧ N𝔠 ≤ X ∧ (N𝔠).Coprime m ∧ Frob_𝔠 = h} = Nat.card {I : (Ideal)⁰ // N I ≤ X ∧ (N I mod m) = (autToPow h mod m)}`
- **What**: The good (coprime-norm) Frobenius fibre is exactly a norm-residue class.
- **How**: explicit `Nat.card_congr` bijection; coprimality+support free from the residue being a unit; Frobenius ⇔ residue via `autToPow_frobeniusIdeal` + injectivity of `autToPow`.
- **Hypotheses**: NF-bundle, finite-dim, abelian, cyclo m; `hζ` primitive.
- **Uses from project**: [`frobeniusIdeal`, `autToPow_frobeniusIdeal`, `autToPow_injective` (CNR import)]
- **Used by**: `card_L2_eq_sum_residue`
- **Visibility**: private
- **Lines**: 712–747 (proof ~30)
- **Notes**: long (30–50) — ~30 lines; `open nonZeroDivisors in`

### `def badPart`
- **Type**: `(K) [Field K] [NumberField K] (m) (𝔞)` : `Ideal (𝓞 K)` = product of factors with norm **not** coprime to `m`
- **What**: The bad part of `𝔞` at level `m`.
- **How**: `Multiset.filter` (¬coprime) `.prod`.
- **Hypotheses**: `K` a number field.
- **Uses from project**: []
- **Used by**: `goodPart_mul_badPart`, `badPart_ne_bot`, `mem_factors_badPart`, `badPart_mul_eq`, `card_fibre_eq_card_good_fibre`, the partition chain.
- **Visibility**: private
- **Lines**: 749–755 (proof 0, def)
- **Notes**: none

### `def goodPart`
- **Type**: `(K) [Field K] [NumberField K] (m) (𝔞)` : `Ideal (𝓞 K)` = product of factors with norm coprime to `m`
- **What**: The good part of `𝔞` at level `m`.
- **How**: `Multiset.filter` (coprime) `.prod`.
- **Hypotheses**: `K` a number field.
- **Uses from project**: []
- **Used by**: `goodPart_mul_badPart`, `goodPart_ne_bot`, `absNorm_goodPart_coprime`, `goodPart_mul_eq`, `card_fibre_eq_card_good_fibre`
- **Visibility**: private
- **Lines**: 757–761 (proof 0, def)
- **Notes**: none

### `theorem prod_filter_normalizedFactors_ne_bot`
- **Type**: `(K) (𝔞) (p) [DecidablePred p]` : `((normalizedFactors 𝔞).filter p).prod ≠ ⊥`
- **What**: A filtered factor product is never the zero ideal.
- **How**: `Multiset.prod_ne_zero`; each factor is a prime, hence nonzero.
- **Hypotheses**: `K` a number field.
- **Uses from project**: []
- **Used by**: `badPart_ne_bot`, `goodPart_ne_bot`
- **Visibility**: private
- **Lines**: 767–771 (proof ~2)
- **Notes**: none

### `theorem goodPart_mul_badPart`
- **Type**: `(K) (𝔞) (h𝔞 : 𝔞 ≠ ⊥)` : `goodPart K m 𝔞 · badPart K m 𝔞 = 𝔞`
- **What**: Good and bad parts recombine to `𝔞`.
- **How**: `Multiset.filter_add_not` + `Ideal.prod_normalizedFactors_eq_self`.
- **Hypotheses**: `K` a number field; `𝔞 ≠ ⊥`.
- **Uses from project**: [`goodPart`, `badPart`]
- **Used by**: `card_fibre_eq_card_good_fibre`, `card_L2_eq_sum_fibres`
- **Visibility**: private
- **Lines**: 773–776 (proof ~2)
- **Notes**: none

### `theorem badPart_ne_bot`
- **Type**: `(K) (𝔞)` : `badPart K m 𝔞 ≠ ⊥`
- **What**: The bad part is nonzero.
- **How**: `prod_filter_normalizedFactors_ne_bot`.
- **Hypotheses**: `K` a number field.
- **Uses from project**: [`badPart`, `prod_filter_normalizedFactors_ne_bot`]
- **Used by**: `card_L2_eq_sum_fibres`
- **Visibility**: private
- **Lines**: 778–779 (proof ~1)
- **Notes**: none

### `theorem goodPart_ne_bot`
- **Type**: `(K) (𝔞)` : `goodPart K m 𝔞 ≠ ⊥`
- **What**: The good part is nonzero.
- **How**: `prod_filter_normalizedFactors_ne_bot`.
- **Hypotheses**: `K` a number field.
- **Uses from project**: [`goodPart`, `prod_filter_normalizedFactors_ne_bot`]
- **Used by**: `card_fibre_eq_card_good_fibre`
- **Visibility**: private
- **Lines**: 781–782 (proof ~1)
- **Notes**: none

### `theorem absNorm_goodPart_coprime`
- **Type**: `(K) (𝔞)` : `(Ideal.absNorm (goodPart K m 𝔞)).Coprime m`
- **What**: The good part has norm coprime to `m`.
- **How**: `Multiset.prod_induction` on the coprimality predicate; each factor's norm is coprime by the filter.
- **Hypotheses**: `K` a number field.
- **Uses from project**: [`goodPart`]
- **Used by**: `card_fibre_eq_card_good_fibre`
- **Visibility**: private
- **Lines**: 784–790 (proof ~5)
- **Notes**: none

### `theorem mem_factors_badPart`
- **Type**: `(K) {𝔞 𝔭} (h𝔭 : 𝔭 ∈ normalizedFactors (badPart K m 𝔞))` : `𝔭 ∈ normalizedFactors 𝔞 ∧ ¬(N𝔭).Coprime m`
- **What**: A factor of the bad part is a non-coprime-norm factor of `𝔞`.
- **How**: `normalizedFactors_prod_of_prime` to recover the filtered multiset, then `Multiset.mem_of_mem_filter` / `mem_filter`.
- **Hypotheses**: `K` a number field.
- **Uses from project**: [`badPart`]
- **Used by**: `card_L2_eq_sum_fibres`
- **Visibility**: private
- **Lines**: 792–799 (proof ~4)
- **Notes**: `classical`

### `theorem coprime_absNorm_of_mem_factors_of_coprime`
- **Type**: `(K) {𝔠} (hcop : (N𝔠).Coprime m) {𝔮} (h𝔮 : 𝔮 ∈ normalizedFactors 𝔠)` : `(N𝔮).Coprime m`
- **What**: Every prime factor of a coprime-norm ideal has coprime norm.
- **How**: `absNorm_dvd_absNorm_of_le` + `Nat.Coprime.coprime_dvd_left`.
- **Hypotheses**: `K` a number field; `N𝔠` coprime to `m`.
- **Uses from project**: []
- **Used by**: `card_fibre_eq_card_good_fibre`, `card_L2_eq_sum_fibres` (indirectly), `goodPart_mul_eq`/`badPart_mul_eq` call sites
- **Visibility**: private
- **Lines**: 801–809 (proof ~3, term)
- **Notes**: none

### `theorem goodPart_mul_eq`
- **Type**: `(K) {𝔠 𝔟} (h𝔠) (h𝔟) (hc : all factors of 𝔠 coprime) (hb : all factors of 𝔟 ¬coprime)` : `goodPart K m (𝔠·𝔟) = 𝔠`
- **What**: Good part of a coprime·bad product is the coprime side.
- **How**: `normalizedFactors_mul` + `Multiset.filter_add` with `filter_eq_self`/`filter_eq_nil`.
- **Hypotheses**: `K` number field; `𝔠,𝔟` nonzero, factor-sign hypotheses.
- **Uses from project**: [`goodPart`]
- **Used by**: `card_fibre_eq_card_good_fibre`
- **Visibility**: private
- **Lines**: 811–821 (proof ~4)
- **Notes**: `classical`

### `theorem badPart_mul_eq`
- **Type**: `(K) {𝔠 𝔟} (h𝔠) (h𝔟) (hc) (hb)` : `badPart K m (𝔠·𝔟) = 𝔟`
- **What**: Bad part of a coprime·bad product is the bad side.
- **How**: symmetric to `goodPart_mul_eq`.
- **Hypotheses**: same as above.
- **Uses from project**: [`badPart`]
- **Used by**: `card_fibre_eq_card_good_fibre`
- **Visibility**: private
- **Lines**: 823–832 (proof ~4)
- **Notes**: `classical`

### `theorem card_fibre_eq_card_good_fibre`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian] (cyclo m) (g) (N) {𝔟} (h𝔟 : 𝔟 ≠ ⊥) (hbU) (hbn)` : `Nat.card {𝔞 ≠ ⊥ ∧ N𝔞 ≤ N ∧ U 𝔞 ∧ Frob_𝔞 = g ∧ badPart 𝔞 = 𝔟} = Nat.card {𝔠 ≠ ⊥ ∧ N𝔠 ≤ ⌊N/N𝔟⌋ ∧ (N𝔠).Coprime m ∧ Frob_𝔠 = g·Frob_𝔟⁻¹}`
- **What**: Per-bad-part fibre bijection (Sharifi 7.2.2 step C): fixing the bad part `𝔟`, the `g`-fibre is in bijection with coprime good fibres at `g·Frob_𝔟⁻¹`.
- **How**: explicit `Nat.card_congr` via `𝔞 ↦ goodPart 𝔞`; norm bound through `N(goodPart)·N𝔟 = N𝔞` (`Nat.le_div_iff_mul_le`); Frobenius via multiplicativity/cancellation; split via `goodPart_mul_eq`/`badPart_mul_eq`. ~55-line proof.
- **Hypotheses**: NF-bundle, finite-dim, abelian, cyclo m; `𝔟` bad-supported nonzero.
- **Uses from project**: [`frobeniusIdeal`, `frobeniusIdeal_mul`, `UnramifiedIn`, `badPart`, `goodPart`, `goodPart_ne_bot`, `goodPart_mul_badPart`, `goodPart_mul_eq`, `badPart_mul_eq`, `unramifiedIn_of_coprime_absNorm`, `coprime_absNorm_of_mem_factors_of_coprime`]
- **Used by**: `card_L2_eq_sum_residue`
- **Visibility**: private
- **Lines**: 840–904 (proof ~55)
- **Notes**: **OVER-50 — needs further /decompose-proof pass** (~55 lines); `open UniqueFactorizationMonoid in`

### `def IsBadPart`
- **Type**: `(K L) [NF-bundle …abelian, cyclo m] (N) (𝔟)` : `Prop` = `𝔟 ≠ ⊥ ∧ (∀ factor unramified ∧ ¬coprime norm) ∧ N𝔟 ≤ N`
- **What**: The bad-supported-ideals predicate of norm `≤ N`.
- **How**: conjunction definition.
- **Hypotheses**: full bundle (section variables).
- **Uses from project**: [`UnramifiedIn`]
- **Used by**: `finite_isBadPart`, `card_L2_eq_sum_fibres`
- **Visibility**: private
- **Lines**: 910–915 (proof 0, def)
- **Notes**: `open UniqueFactorizationMonoid in`

### `theorem finite_isBadPart`
- **Type**: `(K L) [bundle] (N)` : `{𝔟 | IsBadPart K L m N 𝔟}.Finite`
- **What**: Bad-supported ideals of norm `≤ N` form a finite set.
- **How**: subset of the finitely many ideals of norm `≤ N` (`Ideal.finite_setOf_absNorm_le`).
- **Hypotheses**: NF-bundle (most instances omitted via `omit`).
- **Uses from project**: [`IsBadPart`]
- **Used by**: `card_L2_eq_sum_fibres`, `card_L2_eq_sum_residue`, `badFinset_subset_of_le`, `sum_rpow_badFinset_le`, the error-assembly lemmas.
- **Visibility**: private
- **Lines**: 917–922 (proof ~1)
- **Notes**: `omit` several instances

### `instance finite_L2`
- **Type**: `(K L) [bundle] (g) (N)` : `Finite {𝔞 ≠ ⊥ ∧ N𝔞 ≤ N ∧ U 𝔞 ∧ Frob_𝔞 = g}`
- **What**: The L2 fibre subtype at `g` is finite.
- **How**: injection into ideals of norm `≤ N`.
- **Hypotheses**: full bundle.
- **Uses from project**: [`frobeniusIdeal`, `UnramifiedIn`]
- **Used by**: instance resolution for `card_L2_eq_sum_fibres`, etc.
- **Visibility**: private (instance)
- **Lines**: 924–933 (proof ~5)
- **Notes**: `open UniqueFactorizationMonoid in`

### `theorem card_L2_eq_sum_fibres`
- **Type**: `(K L) [bundle] (g) (N)` : `Nat.card (L2 fibre at g) = ∑_{𝔟 ∈ badFinset N} Nat.card (per-bad-part fibre)`
- **What**: The partition (Sharifi 7.2.2 step B) — L2 count is the sum over bad parts of per-bad-part counts.
- **How**: fibration `𝔞 ↦ badPart 𝔞` via `Equiv.sigmaFiberEquiv` + `Nat.card_sigma`; membership `badPart 𝔞 ∈ B_N` from `badPart_ne_bot`/`mem_factors_badPart` + `N(badPart) ∣ N𝔞`. ~33-line proof.
- **Hypotheses**: full bundle (several omitted via `omit`).
- **Uses from project**: [`frobeniusIdeal`, `UnramifiedIn`, `IsBadPart`, `badPart`, `finite_isBadPart`, `badPart_ne_bot`, `mem_factors_badPart`]
- **Used by**: `card_L2_eq_sum_residue`
- **Visibility**: private
- **Lines**: 935–973 (proof ~33)
- **Notes**: long (30–50) — ~33 lines; `omit` + `open UniqueFactorizationMonoid in`

### `theorem card_L2_eq_sum_residue`
- **Type**: `(K L) [bundle] {ζ} (hζ) (g) (N)` : `Nat.card (L2 fibre at g) = ∑_{𝔟 ∈ badFinset N} Nat.card (norm-residue count at autToPow(g·Frob_𝔟⁻¹), window ⌊N/N𝔟⌋)`
- **What**: The L2 count as a sum of norm-residue counts (chaining partition + per-bad-part bijection + good-fibre↔residue dictionary).
- **How**: rewrite `card_L2_eq_sum_fibres`, then per term `card_fibre_eq_card_good_fibre` + `card_good_fibre_eq_card_residue`.
- **Hypotheses**: full bundle; `hζ` primitive.
- **Uses from project**: [`frobeniusIdeal`, `UnramifiedIn`, `finite_isBadPart`, `card_L2_eq_sum_fibres`, `card_fibre_eq_card_good_fibre`, `card_good_fibre_eq_card_residue`]
- **Used by**: `card_fibre_bound_two_le`, `card_fibre_bound_eq_one`
- **Visibility**: private
- **Lines**: 975–995 (proof ~10)
- **Notes**: `open UniqueFactorizationMonoid nonZeroDivisors in`

### `def realizedResidues`
- **Type**: `(K) [Field K] [NumberField K] (m) [NeZero m]` : `Subgroup (ZMod m)ˣ`
- **What**: The realized-residue subgroup `R ≤ (ℤ/m)ˣ` — residues that are `N𝔟 mod m` for some nonzero ideal.
- **How**: genuine subgroup: `1` from `⊤`, products from ideal products, inverses from finite-order power `𝔟^{ord−1}`.
- **Hypotheses**: `K` number field; `NeZero m`.
- **Uses from project**: []
- **Used by**: `autToPow_range_le_realizedResidues`
- **Visibility**: private
- **Lines**: 1014–1035 (proof ~12, structure fields)
- **Notes**: `open nonZeroDivisors in`

### `theorem autToPow_range_le_realizedResidues`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian] (cyclo m) {ζ} (hζ)` : `(hζ.autToPow K).range ≤ realizedResidues K m`
- **What**: Every cyclotomic-character value is a realized norm residue.
- **How**: apply `subgroup_eq_top_of_forall_frobenius_mem_of_coprime` (CNR import) to `H = comap autToPow R`, which contains every coprime-norm unramified prime's Frobenius (`autToPow_frobeniusClass_out`), forcing `H = ⊤`.
- **Hypotheses**: NF-bundle, finite-dim, abelian, cyclo m; `hζ` primitive.
- **Uses from project**: [`realizedResidues`, `subgroup_eq_top_of_forall_frobenius_mem_of_coprime` (CNR), `autToPow_frobeniusClass_out` (CNR)]
- **Used by**: `realizes_autToPow_range`
- **Visibility**: private
- **Lines**: 1037–1061 (proof ~17)
- **Notes**: `open nonZeroDivisors in`

### `theorem realizes_autToPow_range`
- **Type**: `(K L) [NF-bundle …] (cyclo m) {ζ} (hζ)` : `∀ a ∈ (hζ.autToPow K).range, ∃ 𝔟 : (Ideal)⁰, (N𝔟 mod m) = (a mod m)`
- **What**: The realizer hypothesis `hS` for `S = range autToPow`, in the shape the ICC producer consumes.
- **How**: unfolds `autToPow_range_le_realizedResidues`.
- **Hypotheses**: NF-bundle, finite-dim, abelian, cyclo m; `hζ` primitive.
- **Uses from project**: [`autToPow_range_le_realizedResidues`]
- **Used by**: `exists_kappa_uniform`
- **Visibility**: private
- **Lines**: 1063–1073 (proof ~1, term)
- **Notes**: `open nonZeroDivisors in`

### `theorem pow_count_dvd_prod`
- **Type**: `{α} [CommMonoid α] [DecidableEq α] (a) (s : Multiset α)` : `a^{s.count a} ∣ s.prod`
- **What**: `a^{count}` divides the multiset product.
- **How**: `Multiset.prod_replicate` + `prod_dvd_prod_of_le` (`le_count_iff_replicate_le`).
- **Hypotheses**: commutative monoid, decidable eq.
- **Uses from project**: []
- **Used by**: `count_normalizedFactors_le_log`
- **Visibility**: private
- **Lines**: 1085–1089 (proof ~2, term)
- **Notes**: none

### `theorem prod_pow_count_normalizedFactors_eq`
- **Type**: `(K) (P : Finset (Ideal (𝓞 K))) {𝔠} (h0 : 𝔠 ≠ ⊥) (hP : factors ⊆ P)` : `𝔠 = ∏_{𝔭 ∈ P} 𝔭^{count}`
- **What**: A nonzero ideal supported on `P` factors as the `P`-product of prime powers.
- **How**: `Ideal.prod_normalizedFactors_eq_self` + `Finset.prod_multiset_count` + `Finset.prod_subset` (zero-count padding).
- **Hypotheses**: `K` number field; `𝔠 ≠ ⊥`, factors ⊆ `P`.
- **Uses from project**: []
- **Used by**: `absNorm_rpow_eq_prod_attach_count`, `sum_rpow_le_euler_prod`
- **Visibility**: private
- **Lines**: 1091–1101 (proof ~5)
- **Notes**: none

### `theorem count_normalizedFactors_le_log`
- **Type**: `{K} {𝔭 𝔟} (h𝔭p) (h𝔭0) (hb0) {N} (hbN : N𝔟 ≤ N)` : `(normalizedFactors 𝔟).count 𝔭 ≤ Nat.log 2 N`
- **What**: The multiplicity of a prime in `𝔟` (norm `≤ N`) is `≤ log₂ N`.
- **How**: `𝔭^{count} ∣ 𝔟` ⇒ `2^{count} ≤ N𝔭^{count} ≤ N𝔟 ≤ N`, then `Nat.le_log_of_pow_le`.
- **Hypotheses**: `𝔭` prime nonzero, `𝔟 ≠ ⊥`, `N𝔟 ≤ N`.
- **Uses from project**: [`pow_count_dvd_prod`]
- **Used by**: `sum_rpow_le_euler_prod`
- **Visibility**: private
- **Lines**: 1105–1121 (proof ~12)
- **Notes**: none

### `theorem absNorm_rpow_eq_prod_attach_count`
- **Type**: `(K) (P) {𝔟} (h0) (hP) (e : ℝ)` : `(N𝔟)^e = ∏_{𝔭 ∈ P.attach} ((N𝔭)^e)^{count}`
- **What**: The real `e`-power of `N𝔟` distributes over the prime factorisation.
- **How**: `prod_pow_count_normalizedFactors_eq` + `map_prod` + `Real.finsetProd_rpow` + `Real.rpow_mul` shuffling.
- **Hypotheses**: `K` number field; `𝔟 ≠ ⊥`, factors ⊆ `P`.
- **Uses from project**: [`prod_pow_count_normalizedFactors_eq`]
- **Used by**: `sum_rpow_le_euler_prod`
- **Visibility**: private
- **Lines**: 1123–1142 (proof ~17)
- **Notes**: none

### `theorem sum_rpow_le_euler_prod`
- **Type**: `(K) (P) (hPprime) (N) (BF) (hBF) (e : ℝ) (hxlt : ∀ 𝔭 ∈ P, (N𝔭)^e < 1)` : `∑_{𝔟 ∈ BF} (N𝔟)^e ≤ ∏_{𝔭 ∈ P} (1 − (N𝔭)^e)⁻¹`
- **What**: The bad-part Euler bound — a finite set of `P`-supported ideals' `e`-power sum is bounded by the geometric Euler product over `P`.
- **How**: count map `𝔟 ↦ (count 𝔭)` injects into bounded exponent vectors (`count ≤ ⌊log₂ N⌋`, via `count_normalizedFactors_le_log`); `Finset.prod_sum` expands the product-of-geometric-sums; per-prime geometric partial sum `≤ (1−(N𝔭)^e)⁻¹` via `geom_sum_mul`. ~62-line proof.
- **Hypotheses**: `K` number field; `P` nonzero primes, `BF` `P`-supported norm-`≤N` ideals, `(N𝔭)^e < 1`.
- **Uses from project**: [`absNorm_rpow_eq_prod_attach_count`, `count_normalizedFactors_le_log`, `prod_pow_count_normalizedFactors_eq`]
- **Used by**: `sum_rpow_badFinset_le`
- **Visibility**: private
- **Lines**: 1144–1214 (proof ~62)
- **Notes**: **OVER-50 — needs further /decompose-proof pass** (~62 lines); `classical`

### `theorem badFinset_subset_of_le`
- **Type**: `(K L) [bundle] {N M} (hNM : N ≤ M)` : `badFinset N ⊆ badFinset M`
- **What**: The bad-part finite set grows with `N`.
- **How**: norm-bound monotonicity on `IsBadPart`.
- **Hypotheses**: full bundle (most omitted).
- **Uses from project**: [`finite_isBadPart`]
- **Used by**: `ciSup_sum_inv_absNorm_sub_le`, `card_fibre_bound_two_le`
- **Visibility**: private
- **Lines**: 1220–1228 (proof ~3)
- **Notes**: `omit` + `open UniqueFactorizationMonoid in`

### `theorem sum_rpow_badFinset_le`
- **Type**: `(K L) [bundle] (N) (e : ℝ) (hxlt : ∀ 𝔭 ∈ badPrimes, (N𝔭)^e < 1)` : `∑_{𝔟 ∈ badFinset N} (N𝔟)^e ≤ ∏_{𝔭 ∈ badPrimes} (1 − (N𝔭)^e)⁻¹`
- **What**: The Euler bound specialised to `BF = badFinset N`, `P = badPrimes`, uniform in `N`.
- **How**: `sum_rpow_le_euler_prod` with `finite_badPrimes` (CNR import) as `P`; checks the support/finiteness side conditions.
- **Hypotheses**: full bundle; `(N𝔭)^e < 1` on bad primes.
- **Uses from project**: [`finite_isBadPart`, `finite_badPrimes` (CNR), `sum_rpow_le_euler_prod`]
- **Used by**: `card_fibre_bound_two_le`
- **Visibility**: private
- **Lines**: 1230–1247 (proof ~7)
- **Notes**: `omit` + `open UniqueFactorizationMonoid in`

### `theorem exists_kappa_uniform`
- **Type**: `(K L) [bundle] {ζ} (hζ)` : `∃ κ₀ C₀, ∀ a ∈ (autToPow).range, ∀ N ≥ 1, |#{I // N I ≤ N ∧ N I ≡ a} − κ₀·N| ≤ C₀·N^{1−1/d}`
- **What**: (C) The `g`-uniform per-residue ideal count — one `(κ₀,C₀)` for every residue in `range autToPow`.
- **How**: ICC κ-uniform count `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform` (ICC import), Fourier-decay hypothesis from the ICC producer `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` fed `realizes_autToPow_range`.
- **Hypotheses**: full bundle; `hζ` primitive.
- **Uses from project**: [`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform` (ICC), `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` (ICC), `realizes_autToPow_range`]
- **Used by**: `card_fibre_bound_two_le`, `card_fibre_bound_eq_one`
- **Visibility**: private
- **Lines**: 1249–1266 (proof ~3, term)
- **Notes**: `open nonZeroDivisors in`

### `theorem abs_sub_kappa_mul_div_le`
- **Type**: `{N Nb} {RCb κ₀ C₀ α e₂ : ℝ} (hNb : 0 < Nb) (hαnn) (hαe₂ : α = -e₂) (hC₀nn) (heff …)` : `|RCb − κ₀·(N/Nb)| ≤ C₀·N^α·Nb^{e₂} + |κ₀|`
- **What**: Per-bad-part floor→real-division error transfer (real-arithmetic kernel).
- **How**: triangle inequality splitting floor-rounding slack `N/Nb − ⌊N/Nb⌋ ∈ [0,1]` and the window-power bound `⌊N/Nb⌋^α ≤ (N/Nb)^α = N^α·Nb^{e₂}`. ~33-line `calc` proof.
- **Hypotheses**: real-variable; `Nb > 0`, `α = −e₂ ≥ 0`, `C₀ ≥ 0`, effective estimate `heff`.
- **Uses from project**: []
- **Used by**: `card_fibre_bound_two_le`
- **Visibility**: private
- **Lines**: 1268–1307 (proof ~33)
- **Notes**: long (30–50) — ~33 lines

### `theorem ciSup_sum_inv_absNorm_sub_le`
- **Type**: `(K L) [bundle] {d} {e₂ E₂ : ℝ} (he₂ : e₂ = 1/d − 1) (hE₂nn) (hEuler …) (N) (hN1 : 1 ≤ N)` : `(⨆ M, T_M) − T_N ≤ N^{−1/d}·E₂`
- **What**: The bad-part inverse-norm tail bound: `T_N → T` with tail `≤ N^{−1/d}·E₂`.
- **How**: on `badFinset M ∖ badFinset N` each `N𝔟 > N` so `(N𝔟)⁻¹ = (N𝔟)^{e₂}·(N𝔟)^{−1/d} ≤ N^{−1/d}·(N𝔟)^{e₂}`; sum + `hEuler` + `ciSup_le`. ~55-line proof.
- **Hypotheses**: full bundle; `e₂ = 1/d − 1`, `E₂ ≥ 0`, Euler bound `hEuler`.
- **Uses from project**: [`finite_isBadPart`, `badFinset_subset_of_le`]
- **Used by**: `card_fibre_bound_two_le`
- **Visibility**: private
- **Lines**: 1309–1370 (proof ~55)
- **Notes**: **OVER-50 — needs further /decompose-proof pass** (~55 lines); `open UniqueFactorizationMonoid in`

### `theorem card_finite_isBadPart_le`
- **Type**: `(K L) [bundle] {α e₂ E₂ : ℝ} (hαnn) (hαe₂ : α = -e₂) (N) (hNα_nn) (hsumE₂ …)` : `|badFinset N| ≤ N^α·E₂`
- **What**: The bad-part finset cardinality bound.
- **How**: each `𝔟 ∈ badFinset N` has `1 = (N𝔟)^α·(N𝔟)^{e₂} ≤ N^α·(N𝔟)^{e₂}`; sum and bound by the `e₂`-Euler sum `E₂`. `calc` proof.
- **Hypotheses**: full bundle; `α = −e₂`, etc.
- **Uses from project**: [`finite_isBadPart`]
- **Used by**: `card_fibre_bound_two_le`
- **Visibility**: private
- **Lines**: 1372–1400 (proof ~24)
- **Notes**: `open UniqueFactorizationMonoid in`

### `theorem card_fibre_bound_two_le`
- **Type**: `(K L) [bundle] {ζ} (hζ) (hd : 2 ≤ finrank ℚ K)` : `∃ κ C', ∀ g N ≥ 1, |#(L2 fibre at g) − κ·N| ≤ C'·N^{1−1/d}`
- **What**: The L2 fibre bound, `d ≥ 2` branch (bad-part Euler tail converges).
- **How**: assembles `exists_kappa_uniform`, `sum_rpow_badFinset_le` (Euler bounds at exponents `−1` and `e₂`), `ciSup_sum_inv_absNorm_sub_le` (tail), `abs_sub_kappa_mul_div_le` (per-bad-part), `card_finite_isBadPart_le`, via `card_L2_eq_sum_residue` + a three-piece triangle inequality; `κ = κ₀·T`. ~127-line proof.
- **Hypotheses**: full bundle; `hζ` primitive, `d ≥ 2`.
- **Uses from project**: [`frobeniusIdeal`, `UnramifiedIn`, `finite_isBadPart`, `finite_badPrimes` (CNR), `card_L2_eq_sum_residue`, `exists_kappa_uniform`, `sum_rpow_badFinset_le`, `badFinset_subset_of_le`, `ciSup_sum_inv_absNorm_sub_le`, `abs_sub_kappa_mul_div_le`, `card_finite_isBadPart_le`]
- **Used by**: `exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`
- **Visibility**: private
- **Lines**: 1416–1552 (proof ~127)
- **Notes**: **OVER-50 — needs further /decompose-proof pass** (~127 lines); `open UniqueFactorizationMonoid nonZeroDivisors in`

### `theorem associated_natCast_sub_one_pow`
- **Type**: `{A} [CommRing A] [IsDomain A] {p k} [Fact p.Prime] {ζ'} (hζ' : IsPrimitiveRoot ζ' (p^{k+1}))` : `Associated (p : A) ((ζ' − 1)^{p^k(p−1)})`
- **What**: Cyclotomic Eisenstein identity (element level, base-free): `p ~ (ζ'−1)^{φ(p^{k+1})}`.
- **How**: evaluate `cyclotomic (p^{k+1}) = ∏ (X − μ)` at `1` (`eval_one_cyclotomic_prime_pow`), each factor associated to `ζ'−1` (`IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime`); `card_primitiveRoots` = `totient_prime_pow_succ`. ~23-line proof.
- **Hypotheses**: domain; `ζ'` primitive `p^{k+1}`-th root.
- **Uses from project**: []
- **Used by**: `coprime_absNorm_of_unramified_of_finrank_eq_one`
- **Visibility**: private
- **Lines**: 1563–1590 (proof ~23)
- **Notes**: `open Polynomial Finset in`

### `theorem two_le_pow_mul_pred`
- **Type**: `{p k} (hp : p.Prime) (hbad : ¬(p = 2 ∧ k = 0))` : `2 ≤ p^k(p−1)`
- **What**: Totient lower bound away from the degenerate `(p,k)=(2,0)`.
- **How**: case split `p = 2` (so `k ≥ 1`) vs `p ≥ 3`; monotonicity of powers.
- **Hypotheses**: `p` prime, not `(2,0)`.
- **Uses from project**: []
- **Used by**: `coprime_absNorm_of_unramified_of_finrank_eq_one`
- **Visibility**: private
- **Lines**: 1592–1601 (proof ~7)
- **Notes**: none

### `theorem factorization_two_ne_one_of_mod_four`
- **Type**: `{m} (hm0 : m ≠ 0) (hm : m % 4 ≠ 2)` : `m.factorization 2 ≠ 1`
- **What**: The degenerate case `2 ∥ m` is exactly `m ≡ 2 (mod 4)`, excluded by `hm`.
- **How**: `Nat.Prime.pow_dvd_iff_le_factorization` for `2 ∣ m` and `¬ 4 ∣ m`, then `omega`.
- **Hypotheses**: `m ≠ 0`, `m % 4 ≠ 2`.
- **Uses from project**: []
- **Used by**: `coprime_absNorm_of_unramified_of_finrank_eq_one`
- **Visibility**: private
- **Lines**: 1603–1615 (proof ~9)
- **Notes**: none

### `theorem span_singleton_natCast_eq_of_finrank_eq_one`
- **Type**: `(K) (hd1 : finrank ℚ K = 1) (p) (hp : p.Prime) (𝔭) [𝔭.IsPrime] (hmem : (p:𝓞 K) ∈ 𝔭)` : `Ideal.span {(p:𝓞 K)} = 𝔭`
- **What**: At `[K:ℚ]=1`, a rational prime in a prime `𝔭` spans `𝔭`.
- **How**: `N((p)) = p`, `𝔭 ∣ (p)` with `N𝔭 > 1` ⇒ cofactor norm `1` ⇒ `(p) = 𝔭`.
- **Hypotheses**: `finrank ℚ K = 1`; `p` prime, `(p) ∈ 𝔭`.
- **Uses from project**: []
- **Used by**: `coprime_absNorm_of_unramified_of_finrank_eq_one`
- **Visibility**: private
- **Lines**: 1617–1636 (proof ~17)
- **Notes**: none

### `theorem coprime_absNorm_of_unramified_of_finrank_eq_one`
- **Type**: `(K L) [NF-bundle …] (cyclo m) (hd1 : finrank ℚ K = 1) (𝔭) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) (hunr : UnramifiedIn K L 𝔭) (hm : m % 4 ≠ 2)` : `(N𝔭).Coprime m`
- **What**: Bad primes are empty when `K = ℚ`: an unramified nonzero prime cannot have norm sharing a factor with `m`.
- **How**: K-internal different-ideal argument — extract rational `p ∣ m` with `(p) ∈ 𝔭`; the Eisenstein identity `(p) = (ζ'−1)^{φ(p^v)}` (`associated_natCast_sub_one_pow`, `φ ≥ 2` via `two_le_pow_mul_pred`) gives `𝔓² ∣ (𝔭)·𝓞 L`, so `𝔓 ∣ differentIdeal` (`pow_sub_one_dvd_differentIdeal`), contradicting unramifiedness. ~53-line proof.
- **Hypotheses**: full bundle; `finrank ℚ K = 1`, `𝔭` prime nonzero unramified, `m % 4 ≠ 2`.
- **Uses from project**: [`UnramifiedIn`, `exists_primeFactor_natCast_mem_of_not_coprime` (CNR), `associated_natCast_sub_one_pow`, `two_le_pow_mul_pred`, `factorization_two_ne_one_of_mod_four`, `span_singleton_natCast_eq_of_finrank_eq_one`]
- **Used by**: `card_fibre_bound_eq_one`
- **Visibility**: private
- **Lines**: 1638–1715 (proof ~53)
- **Notes**: **OVER-50 — needs further /decompose-proof pass** (~53 lines); `omit` instances

### `theorem card_fibre_bound_eq_one`
- **Type**: `(K L) [bundle] {ζ} (hζ) (hd1 : finrank ℚ K = 1) (hm : m % 4 ≠ 2)` : `∃ κ C', ∀ g N ≥ 1, |#(L2 fibre at g) − κ·N| ≤ C'·N^{1−1/d}`
- **What**: The L2 fibre bound, `d = 1` branch — bad set is `{⊤}`, L2 count is one good-fibre count.
- **How**: `badFinset N = {⊤}` via `coprime_absNorm_of_unramified_of_finrank_eq_one`; `card_L2_eq_sum_residue` collapses to a single `RC(autToPow g, N)`, bounded by `exists_kappa_uniform`.
- **Hypotheses**: full bundle; `hζ` primitive, `finrank ℚ K = 1`, `m % 4 ≠ 2`.
- **Uses from project**: [`frobeniusIdeal`, `frobeniusIdeal_one`, `UnramifiedIn`, `finite_isBadPart`, `exists_kappa_uniform`, `card_L2_eq_sum_residue`, `coprime_absNorm_of_unramified_of_finrank_eq_one`]
- **Used by**: `exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`
- **Visibility**: private
- **Lines**: 1717–1755 (proof ~33)
- **Notes**: long (30–50) — ~33 lines; `open UniqueFactorizationMonoid nonZeroDivisors in`

### `theorem exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian] (cyclo m) (hm : m % 4 ≠ 2)` : `∃ κ C', ∀ g N ≥ 1, |#{𝔞 ≠ ⊥ ∧ N𝔞 ≤ N ∧ U 𝔞 ∧ Frob_𝔞 = g} − κ·N| ≤ C'·N^{1−1/d}` (L2)
- **What**: L2 — unramified-supported Frobenius-fibre equidistribution, leading constant `κ` independent of `g`.
- **How**: case `finrank ℚ K < 2` (so `= 1`) → `card_fibre_bound_eq_one`; else → `card_fibre_bound_two_le`.
- **Hypotheses**: NF-bundle, finite-dim, abelian, cyclo m; `m % 4 ≠ 2`.
- **Uses from project**: [`frobeniusIdeal`, `UnramifiedIn`, `card_fibre_bound_eq_one`, `card_fibre_bound_two_le`]
- **Used by**: `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`
- **Visibility**: public
- **Lines**: 1759–1804 (proof ~6)
- **Notes**: none

### `theorem card_unramifiedSupported_frobeniusValueFibre_eq_sum`
- **Type**: `(K L) [bundle] (χ) (ζ : ℂ) (N)` : `Nat.card {U 𝔞 ∧ χ(Frob_𝔞)=ζ} = ∑_{g ∈ S_ζ} Nat.card {U 𝔞 ∧ Frob_𝔞 = g}`
- **What**: The unramified-supported Frobenius-value-fibre partitions over the character fibre `S_ζ = {g : χ g = ζ}`.
- **How**: `Nat.card_sigma` + an explicit `Equiv.ofBijective` dropping `g = Frob_𝔞`.
- **Hypotheses**: full bundle.
- **Uses from project**: [`galoisCharacter`, `frobeniusIdeal`, `UnramifiedIn`]
- **Used by**: `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`
- **Visibility**: private
- **Lines**: 1806–1846 (proof ~25)
- **Notes**: `classical`

### `theorem exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`
- **Type**: `(K L) [bundle] (cyclo m) (hm : m % 4 ≠ 2) (χ) (_hχ : χ ≠ 1)` : `∃ C C', ∀ ζ, ζ^{orderOf χ}=1 → ∀ N ≥ 1, |#{𝔞 ≠ ⊥ ∧ N𝔞 ≤ N ∧ χ̃(𝔞)=ζ} − C·N| ≤ C'·N^{1−1/d}`
- **What**: Geometry of numbers (Sharifi 7.1.19 step 1) — value-fibre count `C·N + O(N^{1−1/d})` with `C` independent of `ζ`.
- **How**: Helper 1a exact set equality (`card_valueFibre_eq_…`) for `ζ ≠ 0`, partition over `S_ζ` (`card_unramifiedSupported_frobeniusValueFibre_eq_sum`, `|S_ζ| = |ker χ|` via `card_charFibre_eq_card_ker`), L2 per-`g` (`exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`); `C = |ker χ|·κ`. ~65-line `calc` proof.
- **Hypotheses**: full bundle; `m % 4 ≠ 2`, `χ ≠ 1`.
- **Uses from project**: [`galoisCharacter`, `galoisCharacterOnIdeal`, `frobeniusIdeal`, `UnramifiedIn`, `exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`, `card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre`, `card_unramifiedSupported_frobeniusValueFibre_eq_sum`, `card_charFibre_eq_card_ker`]
- **Used by**: `character_sum_geometry_of_numbers_bound`
- **Visibility**: public
- **Lines**: 1848–1947 (proof ~65)
- **Notes**: **OVER-50 — needs further /decompose-proof pass** (~65 lines); `classical`

### `theorem sum_nthRootsFinset_eq_zero`
- **Type**: `{R} [CommRing R] [IsDomain R] {ζ n} (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n)` : `∑_{v ∈ μ_n} v = 0`
- **What**: The sum of all `n`-th roots of unity (`n > 1`) in a domain is `0`.
- **How**: multiplication by `ζ` permutes `μ_n` (`Finset.image`), so `(ζ − 1)·∑ = 0`; `ζ ≠ 1` cancels.
- **Hypotheses**: domain; `ζ` primitive, `n > 1`.
- **Uses from project**: []
- **Used by**: `sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul`
- **Visibility**: private
- **Lines**: 1949–1970 (proof ~18)
- **Notes**: `classical`

### `theorem galoisCharacterOnIdeal_mem_insert_zero_nthRootsFinset`
- **Type**: `(K L) [bundle] (cyclo m) (χ) (𝔞)` : `χ̃(𝔞) ∈ insert 0 (μ_{orderOf χ})`
- **What**: Every ideal-character value is `0` or an `orderOf χ`-th root of unity.
- **How**: case on unramified support: if `U 𝔞`, then `χ̃(𝔞) = χ(Frob_𝔞)` (Helper 1) is a root of unity; else a ramified factor zeroes the product.
- **Hypotheses**: full bundle.
- **Uses from project**: [`galoisCharacter`, `galoisCharacterOnIdeal`, `frobeniusIdeal`, `UnramifiedIn`, `galoisCharacterOnIdeal_eq_char_frobeniusIdeal`, `galoisCharacterOnIdeal_eq_map_prod`]
- **Used by**: `sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul`
- **Visibility**: private
- **Lines**: 1972–1989 (proof ~12)
- **Notes**: `classical`

### `theorem sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul`
- **Type**: `(K L) [bundle] (cyclo m) (χ) (hord2 : 1 < orderOf χ) (C₀ : ℝ) (N) [Fintype …]` : `∑_{𝔞 ≠ ⊥, N𝔞 ≤ N} χ̃(𝔞) = ∑_{v ∈ μ_{ord}} ((#{χ̃=v} − C₀·N : ℝ):ℂ)·v`
- **What**: Regroups the bounded-norm character sum by value `v`, subtracting the common `C₀·N` (which drops out since `∑ v = 0`).
- **How**: `Finset.sum_fiberwise_of_maps_to'` over `insert 0 μ_{ord}` (`galoisCharacterOnIdeal_mem_insert_zero_nthRootsFinset`), `0`-term vanishes, `C₀·N`-term killed by `sum_nthRootsFinset_eq_zero`. ~33-line `calc` proof.
- **Hypotheses**: full bundle; `orderOf χ > 1`, `Fintype` on the index.
- **Uses from project**: [`galoisCharacter`, `galoisCharacterOnIdeal`, `galoisCharacterOnIdeal_mem_insert_zero_nthRootsFinset`, `sum_nthRootsFinset_eq_zero`]
- **Used by**: `character_sum_geometry_of_numbers_bound`
- **Visibility**: private
- **Lines**: 1991–2040 (proof ~33)
- **Notes**: long (30–50) — ~33 lines; `classical`

### `theorem character_sum_geometry_of_numbers_bound`
- **Type**: `(K L) [bundle] (cyclo m) (hm : m % 4 ≠ 2) (χ) (_hχ : χ ≠ 1)` : `∃ C, ∀ N, ‖∑'_{N𝔞 ≤ N} χ̃(𝔞)‖ ≤ C·N^{1−1/d}`
- **What**: Sharifi 7.1.19 step 1 — the partial-sum character sum is `O(N^{1−1/[K:ℚ]})` for nontrivial `χ`.
- **How**: rewrite via `sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul`, bound each value term by `|#{χ̃=v} − C₀·N|` from `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow` (each root of unity has norm 1). ~33-line proof.
- **Hypotheses**: full bundle; `m % 4 ≠ 2`, `χ ≠ 1`.
- **Uses from project**: [`galoisCharacter`, `galoisCharacterOnIdeal`, `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`, `finite_nonzeroIdeal_absNorm_le`, `sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul`]
- **Used by**: `sum_galoisCharacterCoeff_isBigO`, `artinLSeries_analytic_extension`
- **Visibility**: public
- **Lines**: 2051–2098 (proof ~33)
- **Notes**: long (30–50) — ~33 lines; `classical`

### `def galoisCharacterCoeff`
- **Type**: `(K L) [NF-bundle] (χ) (n : ℕ)` : `ℂ` = `∑'_{N𝔞 = n} χ̃(𝔞)`
- **What**: The `n`-th Dirichlet coefficient of the Artin L-series — sum of `χ̃(𝔞)` over nonzero ideals of norm `n`.
- **How**: `tsum` over the norm-`n` fibre.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`galoisCharacterOnIdeal`, `NonzeroIdeal` (project type)]
- **Used by**: `galoisCharacterCoeff_zero`, `norm_galoisCharacterCoeff_le`, `sum_galoisCharacterCoeff_eq_tsum_absNorm_le`, the L-series steps and analytic extension.
- **Visibility**: private
- **Lines**: 2100–2106 (proof 0, def)
- **Notes**: none

### `theorem finite_nonzeroIdeal_absNorm_eq`
- **Type**: `(K) [Field K] [NumberField K] (n)` : `Finite {𝔞 : NonzeroIdeal K // N𝔞 = n}`
- **What**: Each norm-`n` fibre of nonzero ideals is finite.
- **How**: image-finiteness from `Ideal.finite_setOf_absNorm_eq`.
- **Hypotheses**: `K` a number field.
- **Uses from project**: [`NonzeroIdeal`]
- **Used by**: `norm_galoisCharacterCoeff_le`, `sum_galoisCharacterCoeff_eq_tsum_absNorm_le`
- **Visibility**: private
- **Lines**: 2108–2115 (proof ~3)
- **Notes**: none

### `theorem galoisCharacterCoeff_zero`
- **Type**: `(K L) [NF-bundle] (χ)` : `galoisCharacterCoeff K L χ 0 = 0` ; `@[simp]`
- **What**: The `0`-th coefficient vanishes (no nonzero ideal has norm `0`).
- **How**: empty fibre → `tsum_empty`.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`galoisCharacterCoeff`, `NonzeroIdeal`]
- **Used by**: `lseries_galoisCharacterCoeff_eq_tsum`
- **Visibility**: private
- **Lines**: 2117–2123 (proof ~3)
- **Notes**: none

### `theorem norm_galoisCharacterCoeff_le`
- **Type**: `(K L) [NF-bundle] (χ) (n)` : `‖galoisCharacterCoeff K L χ n‖ ≤ (idealNormMultiplicity K n : ℝ)`
- **What**: The `n`-th coefficient is bounded by the ideal-norm multiplicity.
- **How**: `norm_tsum_le_tsum_norm`, each term `≤ 1` (`norm_galoisCharacterOnIdeal_le_one`), fibre size = multiplicity.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`galoisCharacterCoeff`, `galoisCharacterOnIdeal`, `norm_galoisCharacterOnIdeal_le_one`, `idealNormMultiplicity` (Density import), `finite_nonzeroIdeal_absNorm_eq`, `NonzeroIdeal`]
- **Used by**: `sum_norm_galoisCharacterCoeff_isBigO`
- **Visibility**: private
- **Lines**: 2125–2144 (proof ~11)
- **Notes**: none

### `theorem sum_galoisCharacterCoeff_eq_tsum_absNorm_le`
- **Type**: `(K L) [NF-bundle] (χ) (n)` : `∑_{k ∈ Icc 1 n} galoisCharacterCoeff K L χ k = ∑'_{N𝔞 ≤ n} χ̃(𝔞)`
- **What**: Partial sums of coefficients equal the bounded-norm character sum.
- **How**: fibrewise regrouping (`Finset.sum_fiberwise_of_maps_to`) by `N𝔞 ∈ [1,n]`, matched against the per-`n` fibre `tsum`.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`galoisCharacterCoeff`, `galoisCharacterOnIdeal`, `finite_nonzeroIdeal_absNorm_le`, `finite_nonzeroIdeal_absNorm_eq`, `NonzeroIdeal`]
- **Used by**: `sum_galoisCharacterCoeff_isBigO`, `artinLSeries_analytic_extension`
- **Visibility**: private
- **Lines**: 2146–2175 (proof ~19)
- **Notes**: `classical`

### `theorem sum_galoisCharacterCoeff_isBigO`
- **Type**: `(K L) [bundle] (cyclo m) (hm) (χ) (_hχ : χ ≠ 1)` : `(fun n ↦ ∑_{Icc 1 n} coeff k) =O[atTop] (fun n ↦ n^{1−1/d})`
- **What**: Step 1 (LF3 input) — coefficient partial sums are `O(n^{1−1/d})`.
- **How**: `character_sum_geometry_of_numbers_bound` rewritten through `sum_galoisCharacterCoeff_eq_tsum_absNorm_le`.
- **Hypotheses**: full bundle; `m % 4 ≠ 2`, `χ ≠ 1`.
- **Uses from project**: [`galoisCharacterCoeff`, `character_sum_geometry_of_numbers_bound`, `sum_galoisCharacterCoeff_eq_tsum_absNorm_le`]
- **Used by**: `artinLSeries_analytic_extension`
- **Visibility**: private
- **Lines**: 2177–2190 (proof ~5)
- **Notes**: none

### `theorem sum_norm_galoisCharacterCoeff_isBigO`
- **Type**: `(K L) [NF-bundle] (χ)` : `(fun n ↦ ∑_{Icc 1 n} ‖coeff k‖) =O[atTop] (fun n ↦ n^1)`
- **What**: Step 2 — partial sums of coefficient norms are `O(n)` (crude absolute-convergence bound).
- **How**: pointwise `‖coeff‖ ≤ idealNormMultiplicity`, whose partial sums are `O(n)` (`sum_idealNormMultiplicity_isBigO`, Density import).
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`galoisCharacterCoeff`, `norm_galoisCharacterCoeff_le`, `sum_idealNormMultiplicity_isBigO` (Density)]
- **Used by**: `artinLSeries_analytic_extension`
- **Visibility**: private
- **Lines**: 2192–2205 (proof ~5)
- **Notes**: none

### `theorem lseries_galoisCharacterCoeff_eq_tsum`
- **Type**: `(K L) [NF-bundle] (χ) (s) (hs : 1 < s.re)` : `LSeries (galoisCharacterCoeff K L χ) s = ∑'_{𝔞 ≠ ⊥} χ̃(𝔞)·N𝔞^{-s}`
- **What**: Step 3 — on `Re s > 1` the L-series of the coefficients equals the absolutely convergent ideal sum.
- **How**: `Equiv.sigmaFiberEquiv` partitions by `N𝔞`, per-fibre collapse to `coeff n · n^{-s}` (`tsum_mul_right`), `LSeries.term_def₀`; summability by comparison `≤ N𝔞^{-s}` against `hasSum_nonzeroIdeal_absNorm_cpow`. ~27-line proof.
- **Hypotheses**: NF-bundle; `Re s > 1`.
- **Uses from project**: [`galoisCharacterCoeff`, `galoisCharacterOnIdeal`, `galoisCharacterCoeff_zero`, `norm_galoisCharacterOnIdeal_le_one`, `hasSum_nonzeroIdeal_absNorm_cpow` (Density), `NonzeroIdeal`]
- **Used by**: `artinLSeries_analytic_extension`
- **Visibility**: private
- **Lines**: 2207–2245 (proof ~27)
- **Notes**: `classical`

### `theorem setIntegral_Ioi_one_mul_cpow_eq_mellin`
- **Type**: `(S : ℝ → ℂ) (hS : ∀ t < 1, S t = 0) (s)` : `∫_{Ioi 1} S t · t^{-(s+1)} = mellin S (-s)`
- **What**: A Mellin-transform identity over `Ioi 1` for a function supported on `[1,∞)`.
- **How**: `mellin` over `Ioi 0` restricts to `Ioi 1` (indicator a.e. argument), then `ring`-shuffles the integrand.
- **Hypotheses**: `S` supported on `[1,∞)`.
- **Uses from project**: []
- **Used by**: `artinLSeries_analytic_extension`
- **Visibility**: private
- **Lines**: 2247–2264 (proof ~17)
- **Notes**: `open MeasureTheory Set in`

### `theorem artinLSeries_analytic_extension`
- **Type**: `(K L) [bundle] (cyclo m) (hm) (χ) (_hχ : χ ≠ 1)` : `∃ Lf, AnalyticOn ℂ Lf {Re s > 1 − 1/d} ∧ (∀ s, 1 < s.re → Lf s = ∑'_{𝔞 ≠ ⊥} χ̃(𝔞)·N𝔞^{-s})`
- **What**: Sharifi 7.1.19 step 1b — analytic extension of `L(χ,·)` from `Re s > 1` to `Z(1 − 1/[K:ℚ])`.
- **How**: defines `Lf s = s·mellin S (-s)` with `S` the coefficient partial-sum step function; analyticity via `mellin_differentiableAt_of_isBigO_rpow` (using `sum_galoisCharacterCoeff_isBigO` for the top tail); value via `LSeries_eq_mul_integral` + `lseries_galoisCharacterCoeff_eq_tsum` + `setIntegral_Ioi_one_mul_cpow_eq_mellin`. ~50-line proof.
- **Hypotheses**: full bundle; `m % 4 ≠ 2`, `χ ≠ 1`.
- **Uses from project**: [`galoisCharacter`, `galoisCharacterOnIdeal`, `galoisCharacterCoeff`, `sum_galoisCharacterCoeff_isBigO`, `sum_norm_galoisCharacterCoeff_isBigO`, `lseries_galoisCharacterCoeff_eq_tsum`, `setIntegral_Ioi_one_mul_cpow_eq_mellin`, `NonzeroIdeal`]
- **Used by**: `artinDirichletSeries_norm_le_of_ne_one`
- **Visibility**: public
- **Lines**: 2266–2341 (proof ~50)
- **Notes**: long (30–50) — borderline at ~50 lines; `open Filter Topology Set MeasureTheory Asymptotics in`

### `theorem logDedekindZeta_re_tendsto_atTop`
- **Type**: `(L) [Field L] [NumberField L]` : `Tendsto (fun s : ℝ ↦ log (dedekindZeta L s).re) (𝓝[>] 1) atTop`
- **What**: Ingredient B — `log ζ_L(s).re → +∞` as `s ↓ 1` (simple pole).
- **How**: `logDedekindZeta_sub_log_inv_sub_one_bounded` (Density import) squeezed against `log(1/(s−1)) → +∞`.
- **Hypotheses**: `L` a number field.
- **Uses from project**: [`logDedekindZeta_sub_log_inv_sub_one_bounded` (Density)]
- **Used by**: `false_of_eventually_log_norm_le_pole_zero_ite`
- **Visibility**: private
- **Lines**: 2358–2372 (proof ~6)
- **Notes**: `open Filter Topology Set in`

### `theorem analytic_log_norm_le_of_apply_eq_zero`
- **Type**: `{f : ℂ → ℂ} (hf : AnalyticAt ℂ f 1) (hf0 : f 1 = 0) (hne : ¬ ∀ᶠ z near 1, f z = 0)` : `∃ C, ∀ᶠ s ↓ 1 (real), log‖f s‖ ≤ −log(1/(s−1)) + C`
- **What**: Ingredient C — an analytic function with a zero at `1` (order `≥ 1`) has log-norm bounded above by `−log(1/(s−1)) + C` near `s ↓ 1`.
- **How**: `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` factors `f = (z−1)^n g`, `n ≥ 1`; `log‖f s‖ = n·log(s−1) + log‖g s‖`, with `log(s−1) < 0` and `‖g‖` bounded by continuity. ~48-line proof.
- **Hypotheses**: `f` analytic at `1`, `f 1 = 0`, not locally zero.
- **Uses from project**: []
- **Used by**: `artinLSeries_one_ne_zero`
- **Visibility**: private
- **Lines**: 2374–2428 (proof ~48)
- **Notes**: long (30–50) — ~48 lines; `open Filter Topology Set in`

### `instance galoisCharacter.instFintype`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L]` : `Fintype (galoisCharacter K L)` ; `local instance`
- **What**: The character group is finite (so `∏ χ` / `∑ χ` parse).
- **How**: `Fintype.ofFinite`.
- **Hypotheses**: NF-bundle, finite-dim.
- **Uses from project**: [`galoisCharacter`]
- **Used by**: instance resolution in the finite character-product/sum statements below.
- **Visibility**: local instance
- **Lines**: 2430–2436 (proof ~1)
- **Notes**: none

### `def artinDirichletSeries`
- **Type**: `(K L) [NF-bundle] (χ) (s : ℂ)` : `ℂ` = `∑'_{𝔞 ≠ ⊥} χ̃(𝔞)·N𝔞^{-s}`
- **What**: The Dirichlet series `L_χ(s)` of a Galois character.
- **How**: `tsum` over nonzero ideals.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`galoisCharacterOnIdeal`]
- **Used by**: `tprod_unramified_eq_prod_artinDirichletSeries`, the factorisation and non-vanishing chains.
- **Visibility**: public
- **Lines**: 2438–2445 (proof 0, def)
- **Notes**: none

### `theorem norm_one_sub_inv_sub_one_le`
- **Type**: `{y : ℂ} (hy : ‖y‖ ≤ 1/2)` : `‖(1 − y)⁻¹ − 1‖ ≤ 2‖y‖`
- **What**: Pure-`ℂ` Euler-factor estimate.
- **How**: `(1−y)⁻¹ − 1 = y·(1−y)⁻¹`, `‖(1−y)⁻¹‖ ≤ 2` from `‖1−y‖ ≥ 1/2`.
- **Hypotheses**: `‖y‖ ≤ 1/2`.
- **Uses from project**: []
- **Used by**: `summable_norm_primeIdeal_factor_sub_one`, `multipliable_artinLocalFactor`
- **Visibility**: private
- **Lines**: 2447–2466 (proof ~12)
- **Notes**: none

### `theorem two_le_absNorm`
- **Type**: `{R} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {𝔭} (hp : 𝔭.IsPrime) (hb : 𝔭 ≠ ⊥)` : `2 ≤ Ideal.absNorm 𝔭`
- **What**: A nonzero prime of a number ring has norm `≥ 2`.
- **How**: norm `≠ 0` (only `⊥`) and `≠ 1` (only `⊤`), then `lia`.
- **Hypotheses**: Dedekind domain, free/finite over `ℤ`; `𝔭` prime nonzero.
- **Uses from project**: []
- **Used by**: `norm_absNorm_cpow_neg_le_half`, `log_norm_ramified_factor_bounded`
- **Visibility**: private
- **Lines**: 2468–2475 (proof ~3)
- **Notes**: none

### `theorem norm_absNorm_cpow_neg_le_half`
- **Type**: `{R} [Dedekind…] {s} (hs : 1 < s.re) (𝔭 : {𝔭 // prime ∧ ≠⊥})` : `‖N𝔭^{-s}‖ ≤ 1/2`
- **What**: For a nonzero prime and `Re s > 1`, `‖N𝔭^{-s}‖ ≤ 1/2`.
- **How**: `N𝔭 ≥ 2` (`two_le_absNorm`), `Real.rpow_le_rpow_of_exponent_le` to bound `N𝔭^{-Re s} ≤ N𝔭^{-1} ≤ 1/2`.
- **Hypotheses**: Dedekind domain etc.; `Re s > 1`.
- **Uses from project**: [`two_le_absNorm`]
- **Used by**: `summable_norm_primeIdeal_factor_sub_one`, `multipliable_artinLocalFactor`
- **Visibility**: private
- **Lines**: 2477–2493 (proof ~11)
- **Notes**: none

### `theorem summable_norm_primeIdeal_factor_sub_one`
- **Type**: `(L) [Field L] [NumberField L] {s} (hs : 1 < s.re)` : `Summable fun 𝔓 ↦ ‖(1 − N𝔓^{-s})⁻¹ − 1‖`
- **What**: The shifted prime-ideal Euler factors of `ζ_L` are absolutely summable.
- **How**: per-factor `≤ 2‖N𝔓^{-s}‖` (`norm_one_sub_inv_sub_one_le` + `norm_absNorm_cpow_neg_le_half`), and `∑ ‖N𝔓^{-s}‖` converges (sub-sum of `ζ_L`, `hasSum_nonzeroIdeal_absNorm_cpow`).
- **Hypotheses**: `L` number field; `Re s > 1`.
- **Uses from project**: [`norm_one_sub_inv_sub_one_le`, `norm_absNorm_cpow_neg_le_half`, `hasSum_nonzeroIdeal_absNorm_cpow` (Density), `NonzeroIdeal`]
- **Used by**: `hasProd_primeIdeal_factor`, `multipliable_primeIdeal_factor_subtype`, `tprod_unramified_eq_prod_artinDirichletSeries`
- **Visibility**: private
- **Lines**: 2495–2511 (proof ~12)
- **Notes**: none

### `theorem hasProd_primeIdeal_factor`
- **Type**: `(L) [Field L] [NumberField L] {s} (hs)` : `HasProd (fun 𝔓 ↦ (1 − N𝔓^{-s})⁻¹) (dedekindZeta L s)`
- **What**: The prime-ideal Euler product of `ζ_L` is multipliable with value `ζ_L(s)`.
- **How**: multipliability from `multipliable_one_add_of_summable` (+ `summable_norm_primeIdeal_factor_sub_one`); value pinned by `dedekindZeta_eq_tprod_primeIdeal` (Density import).
- **Hypotheses**: `L` number field; `Re s > 1`.
- **Uses from project**: [`summable_norm_primeIdeal_factor_sub_one`, `dedekindZeta_eq_tprod_primeIdeal` (Density)]
- **Used by**: `dedekindZeta_eq_unramifiedNested_mul_ramifiedNested`
- **Visibility**: private
- **Lines**: 2513–2528 (proof ~6)
- **Notes**: none

### `theorem multipliable_primeIdeal_factor_subtype`
- **Type**: `(L) [Field L] [NumberField L] {s} (hs) (p : … → Prop)` : `Multipliable fun 𝔓 : {𝔓 // p 𝔓} ↦ (1 − N𝔓^{-s})⁻¹`
- **What**: The prime-ideal Euler factor restricted to any predicate-subtype is multipliable.
- **How**: restrict the *summable* norm via `Summable.subtype` (to avoid the `Multipliable.subtype` whnf blow-up), then rebuild with `multipliable_one_add_of_summable`.
- **Hypotheses**: `L` number field; `Re s > 1`.
- **Uses from project**: [`summable_norm_primeIdeal_factor_sub_one`]
- **Used by**: `dedekindZeta_eq_unramifiedNested_mul_ramifiedNested`
- **Visibility**: private
- **Lines**: 2530–2545 (proof ~6)
- **Notes**: none

### `theorem multipliable_artinLocalFactor`
- **Type**: `(K L) [NF-bundle] (χ) {s} (hs : 1 < s.re)` : `Multipliable fun 𝔭 : {𝔭 // prime ∧ unram} ↦ (1 − χ(Frob 𝔭).out · N𝔭^{-s})⁻¹`
- **What**: The χ-twisted local Euler product `L_χ` is multipliable.
- **How**: `‖χ(σ_𝔭)‖ = 1` (`norm_galoisCharacter_out`) ⇒ `‖χ(σ_𝔭) N𝔭^{-s}‖ ≤ 1/2`, sub-sum of `ζ_K` summable; `multipliable_one_add_of_summable`.
- **Hypotheses**: NF-bundle; `Re s > 1`.
- **Uses from project**: [`galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `norm_galoisCharacter_out`, `norm_absNorm_cpow_neg_le_half`, `norm_one_sub_inv_sub_one_le`, `hasSum_nonzeroIdeal_absNorm_cpow` (Density), `UnramifiedIn.ne_bot`, `NonzeroIdeal`]
- **Used by**: `tprod_unramified_eq_prod_artinDirichletSeries`
- **Visibility**: private
- **Lines**: 2547–2576 (proof ~25)
- **Notes**: long-ish (~25); no flag

### `def underUP`
- **Type**: `(K L) [NF-bundle] (𝔓 : {𝔓 // prime ∧ ≠⊥ ∧ unram-below})` : `{𝔭 // prime ∧ unram}`
- **What**: Sends an unramified-below `L`-prime `𝔓` to the `K`-prime `𝔓.under` below it.
- **How**: `Subtype.mk` with `𝔓.under`.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`UnramifiedIn`]
- **Used by**: `underUP_val`, `fiberUnderEquiv`, `tprod_unramified_eq_prod_artinDirichletSeries`
- **Visibility**: private (def)
- **Lines**: 2578–2584 (proof 0, def)
- **Notes**: none

### `theorem underUP_val`
- **Type**: `(K L) [NF-bundle] (𝔓)` : `(underUP K L 𝔓).1 = 𝔓.1.under (𝓞 K)` ; `@[simp]`
- **What**: The underlying ideal of `underUP 𝔓` is `𝔓.under`.
- **How**: `rfl`.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`underUP`]
- **Used by**: `fiberUnderEquiv`
- **Visibility**: private
- **Lines**: 2586–2589 (proof 0)
- **Notes**: none

### `def fiberUnderEquiv`
- **Type**: `(K L) [NF-bundle] (c : {𝔭 // prime ∧ unram})` : `{𝔓 // underUP 𝔓 = c} ≃ {𝔓 // prime ∧ LiesOver c ∧ ≠⊥}`
- **What**: The fibre of `underUP` over `c` is, reindexed, the primes of `𝓞 L` lying over `c`.
- **How**: explicit `Equiv` with `LiesOver`/`under` bookkeeping.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`underUP`, `underUP_val`, `UnramifiedIn`]
- **Used by**: `tprod_unramified_eq_prod_artinDirichletSeries`
- **Visibility**: private (def)
- **Lines**: 2591–2607 (proof ~8, equiv)
- **Notes**: none

### `def unramifiedFlattenEquiv`
- **Type**: `(K L) [NF-bundle]` : `{𝔓 : {𝔓 // prime ∧ ≠⊥} // unram-below} ≃ {𝔔 // prime ∧ ≠⊥ ∧ unram-below}`
- **What**: Flattens the doubly-nested unramified-below prime subtype to triply-nested.
- **How**: explicit `Equiv`, `rfl` round-trips.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`UnramifiedIn`]
- **Used by**: `tprod_unramified_eq_prod_artinDirichletSeries`, `tprod_unramifiedNested_eq_prod_artin`
- **Visibility**: private (def)
- **Lines**: 2609–2620 (proof ~4, equiv)
- **Notes**: none

### `def ramifiedFlattenEquiv`
- **Type**: `(K L) [NF-bundle]` : `{𝔓 : {𝔓 // prime ∧ ≠⊥} // ¬unram-below} ≃ {𝔔 // prime ∧ ≠⊥ ∧ ¬unram-below}`
- **What**: Flattens the doubly-nested ramified-below prime subtype to triply-nested.
- **How**: explicit `Equiv`.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`UnramifiedIn`]
- **Used by**: `tprod_ramifiedNested_eq_ramified`
- **Visibility**: private (def)
- **Lines**: 2622–2633 (proof ~4, equiv)
- **Notes**: none

### `theorem tprod_unramified_eq_prod_artinDirichletSeries`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian] {s} (hs : 1 < s.re)` : `∏'_{𝔓 prime ≠⊥ unram-below} (1 − N𝔓^{-s})⁻¹ = ∏'_{χ} artinDirichletSeries K L χ s`
- **What**: The unramified part of `ζ_L`'s prime product equals `∏_χ L_χ`.
- **How**: regroup unramified `L`-primes fibrewise over the `K`-prime below (`Equiv.sigmaFiberEquiv` + `HasProd.sigma`); each fibre product is `∏_χ(1 − χ(σ_𝔭) N𝔭^{-s})⁻¹` (`dedekindZeta_local_factor_eq_product_artin_local`, `fiberUnderEquiv`); swap the finite character product (`Multipliable.tprod_finsetProd`) + abelian Euler product (`exists_artinLSeries_eulerProduct_abelian`). ~57-line proof.
- **Hypotheses**: NF-bundle, finite-dim, abelian; `Re s > 1`.
- **Uses from project**: [`galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `artinDirichletSeries`, `summable_norm_primeIdeal_factor_sub_one`, `unramifiedFlattenEquiv`, `underUP`, `fiberUnderEquiv`, `dedekindZeta_local_factor_eq_product_artin_local`, `multipliable_artinLocalFactor`, `exists_artinLSeries_eulerProduct_abelian`, `UnramifiedIn.ne_bot`]
- **Used by**: `tprod_unramifiedNested_eq_prod_artin`
- **Visibility**: private
- **Lines**: 2635–2707 (proof ~57)
- **Notes**: **OVER-50 — needs further /decompose-proof pass** (~57 lines); `classical`

### `theorem dedekindZeta_eq_unramifiedNested_mul_ramifiedNested`
- **Type**: `(K L) [NF-bundle] {s} (hs)` : `dedekindZeta L s = (∏'_{unram-below nested}(…)⁻¹) · (∏'_{ramified-below nested}(…)⁻¹)`
- **What**: Splits `ζ_L`'s prime product into unramified-below and ramified-below halves.
- **How**: `HasProd.mul_compl` (avoiding the off-the-shelf `tprod_subtype_mul_tprod_subtype_compl` whnf blow-up) on the two `multipliable_primeIdeal_factor_subtype` products, unique against `hasProd_primeIdeal_factor`.
- **Hypotheses**: NF-bundle; `Re s > 1`.
- **Uses from project**: [`UnramifiedIn`, `multipliable_primeIdeal_factor_subtype`, `hasProd_primeIdeal_factor`]
- **Used by**: `dedekindZeta_eq_prod_artinDirichletSeries`
- **Visibility**: private
- **Lines**: 2709–2733 (proof ~12)
- **Notes**: none

### `theorem tprod_unramifiedNested_eq_prod_artin`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian] {s} (hs)` : `∏'_{unram-below nested}(…)⁻¹ = ∏'_{χ} artinDirichletSeries K L χ s`
- **What**: The unramified-below half (nested form) equals `∏_χ L_χ`.
- **How**: flatten with `unramifiedFlattenEquiv`, then `tprod_unramified_eq_prod_artinDirichletSeries`.
- **Hypotheses**: NF-bundle, finite-dim, abelian; `Re s > 1`.
- **Uses from project**: [`galoisCharacter`, `artinDirichletSeries`, `tprod_unramified_eq_prod_artinDirichletSeries`, `unramifiedFlattenEquiv`, `UnramifiedIn`]
- **Used by**: `dedekindZeta_eq_prod_artinDirichletSeries`
- **Visibility**: private
- **Lines**: 2735–2747 (proof ~3)
- **Notes**: none

### `theorem tprod_ramifiedNested_eq_ramified`
- **Type**: `(K L) [NF-bundle] {s}` : `∏'_{ramified-below nested}(…)⁻¹ = ∏'_{ramified-below flat}(…)⁻¹`
- **What**: Rewrites the ramified-below half from nested to flat subtype.
- **How**: `Equiv.tprod_eq (ramifiedFlattenEquiv K L)`.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`ramifiedFlattenEquiv`, `UnramifiedIn`]
- **Used by**: `dedekindZeta_eq_prod_artinDirichletSeries`
- **Visibility**: private
- **Lines**: 2749–2759 (proof ~1, term)
- **Notes**: none

### `theorem dedekindZeta_eq_prod_artinDirichletSeries`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian] {s} (hs : 1 < s.re)` : `dedekindZeta L s = (∏'_{χ} artinDirichletSeries K L χ s) · ∏'_{𝔓 prime ≠⊥ ramified-below}(1 − N𝔓^{-s})⁻¹`
- **What**: The zeta factorisation (Sharifi 7.1.16 with explicit ramified correction): `ζ_L = (∏_χ L_χ)·R` on `Re s > 1`.
- **How**: chain `dedekindZeta_eq_unramifiedNested_mul_ramifiedNested`, `tprod_unramifiedNested_eq_prod_artin`, `tprod_ramifiedNested_eq_ramified`.
- **Hypotheses**: NF-bundle, finite-dim, abelian; `Re s > 1`.
- **Uses from project**: [`galoisCharacter`, `artinDirichletSeries`, `UnramifiedIn`, `dedekindZeta_eq_unramifiedNested_mul_ramifiedNested`, `tprod_unramifiedNested_eq_prod_artin`, `tprod_ramifiedNested_eq_ramified`]
- **Used by**: `log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded`, `artinDirichletSeries_ne_zero_of_one_lt`
- **Visibility**: public
- **Lines**: 2761–2780 (proof ~2)
- **Notes**: none

### `instance finite_ramifiedAbove`
- **Type**: `(K L) [NF-bundle]` : `Finite {𝔓 : Ideal (𝓞 L) // prime ∧ ≠⊥ ∧ ¬unram-below}`
- **What**: The primes of `𝓞 L` over a ramified `K`-prime form a finite set.
- **How**: only finitely many `K`-primes ramify (`finite_ramifiedIn`, Frobenius import), each with finitely many primes above; injection into the sigma type.
- **Hypotheses**: NF-bundle.
- **Uses from project**: [`UnramifiedIn`, `finite_ramifiedIn` (Frobenius)]
- **Used by**: instance resolution for `log_norm_ramified_factor_bounded` and the corrected-factorisation lemmas.
- **Visibility**: private (instance)
- **Lines**: 2782–2802 (proof ~17)
- **Notes**: `classical`

### `theorem dedekindZeta_eq_ofReal_re`
- **Type**: `(L) [Field L] [NumberField L] {s : ℝ} (hs : 1 < s)` : `dedekindZeta L (s:ℂ) = ((dedekindZeta L (s:ℂ)).re : ℂ)`
- **What**: For real `s > 1`, `ζ_L(s)` is a real number (its Dirichlet series has real terms).
- **How**: `dedekindZeta_eq_tsum_idealNormMultiplicity` (Density import) + `Complex.ofReal_tsum`, each term real-cast.
- **Hypotheses**: `L` number field; real `s > 1`.
- **Uses from project**: [`idealNormMultiplicity` (Density), `dedekindZeta_eq_tsum_idealNormMultiplicity` (Density)]
- **Used by**: `log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded`
- **Visibility**: private
- **Lines**: 2804–2821 (proof ~14)
- **Notes**: none

### `theorem log_norm_ramified_factor_bounded`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian]` : `∃ C, ∀ᶠ s ↓ 1 (real), |log ‖∏'_{ramified-below 𝔓} (1 − N𝔓^{-s})⁻¹‖| ≤ C`
- **What**: The ramified correction factor `R(s)` has bounded `|log‖R‖|` near `s ↓ 1` (finite nonzero product).
- **How**: finite product (`finite_ramifiedAbove`) of factors continuous at `1` with nonzero limit (`N𝔓 ≥ 2`); `ContinuousAt` of `log‖R‖` + a closed-ball neighbourhood bound. ~42-line proof.
- **Hypotheses**: NF-bundle, finite-dim, abelian.
- **Uses from project**: [`UnramifiedIn`, `two_le_absNorm`, `finite_ramifiedAbove` (instance)]
- **Used by**: `log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded`
- **Visibility**: private
- **Lines**: 2823–2876 (proof ~42)
- **Notes**: long (30–50) — ~42 lines; `classical`, `open Filter Topology Set in`

### `theorem log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian]` : `∃ C, ∀ᶠ s ↓ 1 (real), |log ζ_L(s).re − ∑_χ log‖L_χ(s)‖| ≤ C`
- **What**: Ingredient A (bounded log form) — the gap between `log ζ_L(s).re` and `∑_χ log‖L_χ‖` is `O(1)`.
- **How**: take `log‖·‖` of the corrected factorisation `ζ_L = (∏_χ L_χ)·R`; `ζ_L(s)` is a positive real (`dedekindZeta_re_pos_of_one_lt`, `dedekindZeta_eq_ofReal_re`); `log‖R‖` bounded (`log_norm_ramified_factor_bounded`). ~32-line proof.
- **Hypotheses**: NF-bundle, finite-dim, abelian.
- **Uses from project**: [`galoisCharacter`, `artinDirichletSeries`, `UnramifiedIn`, `log_norm_ramified_factor_bounded`, `dedekindZeta_re_pos_of_one_lt` (Density), `dedekindZeta_eq_prod_artinDirichletSeries`, `dedekindZeta_eq_ofReal_re`]
- **Used by**: `false_of_eventually_log_norm_le_pole_zero_ite`
- **Visibility**: private
- **Lines**: 2878–2922 (proof ~32)
- **Notes**: long (30–50) — ~32 lines; `open Filter Topology Set in`

### `theorem analyticAt_one_of_analyticOn_finrankDomain`
- **Type**: `(K) [Field K] [NumberField K] {Lf} (hLf : AnalyticOn ℂ Lf {Re s > 1 − 1/d})` : `AnalyticAt ℂ Lf 1`
- **What**: `1` is interior to the analyticity half-plane, so `AnalyticOn` upgrades to `AnalyticAt` at `1`.
- **How**: open-set membership of `1` (`isOpen_lt`) → `AnalyticOn.analyticAt`.
- **Hypotheses**: `K` number field; `Lf` analytic on the half-plane.
- **Uses from project**: []
- **Used by**: `artinDirichletSeries_norm_le_of_ne_one`, `artinLSeries_one_ne_zero`
- **Visibility**: private
- **Lines**: 2924–2935 (proof ~7)
- **Notes**: none

### `theorem artinDirichletSeries_norm_le_of_ne_one`
- **Type**: `(K L) [bundle] (cyclo m) (hm) (χ') (hχ' : χ' ≠ 1)` : `∃ C, ∀ᶠ s ↓ 1 (real), ‖artinDirichletSeries K L χ' (s:ℂ)‖ ≤ C`
- **What**: Assembly helper (ii) — a nontrivial `L_{χ'}` is bounded above near `s = 1` (via its analytic extension across `1`).
- **How**: `artinLSeries_analytic_extension` gives `Lf'` analytic at `1`, continuous, hence locally bounded; `Lf'` agrees with `artinDirichletSeries` on `Re s > 1`.
- **Hypotheses**: full bundle; `m % 4 ≠ 2`, `χ' ≠ 1`.
- **Uses from project**: [`galoisCharacter`, `artinDirichletSeries`, `artinLSeries_analytic_extension`, `analyticAt_one_of_analyticOn_finrankDomain`]
- **Used by**: `log_norm_artinDirichletSeries_le_pole_zero_ite`
- **Visibility**: private
- **Lines**: 2937–2961 (proof ~16)
- **Notes**: `open Filter Topology Set in`

### `theorem log_norm_artinDirichletSeries_one_le`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian]` : `∃ C, ∀ᶠ s ↓ 1 (real), log‖artinDirichletSeries K L 1 (s:ℂ)‖ ≤ log(1/(s−1)) + C`
- **What**: Assembly helper (i) — the trivial-character `L_1` is bounded by the `ζ_K`-pole asymptotic.
- **How**: `‖χ̃_1(𝔞)‖ ≤ 1` ⇒ `‖L_1(s)‖ ≤ ζ_K(s)` termwise; `ζ_K(s) ≥ 1` and `log ζ_K(s) ≤ log(1/(s−1)) + C` (`logDedekindZeta_sub_log_inv_sub_one_bounded`). ~47-line proof.
- **Hypotheses**: NF-bundle, finite-dim, abelian.
- **Uses from project**: [`galoisCharacterOnIdeal`, `artinDirichletSeries`, `norm_galoisCharacterOnIdeal_le_one`, `logDedekindZeta_sub_log_inv_sub_one_bounded` (Density), `hasSum_nonzeroIdeal_absNorm_cpow` (Density), `NonzeroIdeal`]
- **Used by**: `log_norm_artinDirichletSeries_le_pole_zero_ite`
- **Visibility**: private
- **Lines**: 2963–3025 (proof ~47)
- **Notes**: long (30–50) — ~47 lines; `open Filter Topology Set in`

### `theorem sum_ite_pole_zero_cancel`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] {χ} (hχ : χ ≠ 1) (a : ℝ)` : `∑_{χ'} (if χ'=1 then a else if χ'=χ then -a else 0) = 0`
- **What**: The pole-at-`1` and zero-at-`χ` ite-terms cancel summing over the character group.
- **How**: split the nested ite into two single-ites and apply `Finset.sum_ite_eq'` twice (`χ ≠ 1` ensures disjointness).
- **Hypotheses**: NF-bundle, finite-dim; `χ ≠ 1`.
- **Uses from project**: [`galoisCharacter`]
- **Used by**: `false_of_eventually_log_norm_le_pole_zero_ite`
- **Visibility**: private
- **Lines**: 3027–3040 (proof ~12)
- **Notes**: `open Classical in`

### `theorem log_norm_artinDirichletSeries_le_pole_zero_ite`
- **Type**: `(K L) [bundle] (cyclo m) (hm) {χ Cχ} (hCχ : analytic-zero bound for χ) (χ')` : `∃ C, ∀ᶠ s ↓ 1, log‖L_{χ'}(s)‖ ≤ (pole if χ'=1 / zero if χ'=χ / 0) + C`
- **What**: Per-character log bound (Dirichlet's contradiction assembled over all characters).
- **How**: case `χ'=1` (`log_norm_artinDirichletSeries_one_le`), `χ'=χ` (supplied `hCχ`), else `O(1)` (`artinDirichletSeries_norm_le_of_ne_one`).
- **Hypotheses**: full bundle; `m % 4 ≠ 2`, analytic-zero bound `hCχ`.
- **Uses from project**: [`galoisCharacter`, `artinDirichletSeries`, `log_norm_artinDirichletSeries_one_le`, `artinDirichletSeries_norm_le_of_ne_one`]
- **Used by**: `artinLSeries_one_ne_zero`
- **Visibility**: private
- **Lines**: 3042–3078 (proof ~19)
- **Notes**: `open Classical Filter Topology Set in`

### `theorem artinDirichletSeries_ne_zero_of_one_lt`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian] (χ) {s : ℝ} (hs : 1 < s)` : `artinDirichletSeries K L χ (s:ℂ) ≠ 0`
- **What**: For real `s > 1`, `L_χ(s) ≠ 0` (it is a factor of the positive real `ζ_L(s)`).
- **How**: if `L_χ(s) = 0`, the factorisation `ζ_L = (∏ L_{χ'})·R` forces `ζ_L(s) = 0`, contradicting `dedekindZeta_re_pos_of_one_lt`.
- **Hypotheses**: NF-bundle, finite-dim, abelian; real `s > 1`.
- **Uses from project**: [`galoisCharacter`, `artinDirichletSeries`, `dedekindZeta_re_pos_of_one_lt` (Density), `dedekindZeta_eq_prod_artinDirichletSeries`]
- **Used by**: `artinLSeries_one_ne_zero`
- **Visibility**: private
- **Lines**: 3080–3092 (proof ~6, term)
- **Notes**: none

### `theorem false_of_eventually_log_norm_le_pole_zero_ite`
- **Type**: `(K L) [NF-bundle] [FiniteDimensional K L] [abelian] {χ} (hχ : χ ≠ 1) {C} (hC : ite-bound for all χ')` : `False`
- **What**: Pole-cancellation contradiction — the ite-bounds keep `log ζ_L(s).re` bounded above, contradicting its `→ +∞` divergence.
- **How**: sum the ite-bounds, cancel the pole/zero (`sum_ite_pole_zero_cancel`), absorb the ramified `O(1)` slack (`log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded`); contradiction with `logDedekindZeta_re_tendsto_atTop`. ~27-line proof.
- **Hypotheses**: NF-bundle, finite-dim, abelian; `χ ≠ 1`, ite-bound `hC`.
- **Uses from project**: [`galoisCharacter`, `artinDirichletSeries`, `log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded`, `sum_ite_pole_zero_cancel`, `logDedekindZeta_re_tendsto_atTop`]
- **Used by**: `artinLSeries_one_ne_zero`
- **Visibility**: private
- **Lines**: 3094–3127 (proof ~27)
- **Notes**: `open Classical Filter Topology Set in`

### `theorem artinLSeries_one_ne_zero`
- **Type**: `(K L) [bundle] (cyclo m) (hm : m % 4 ≠ 2) (χ) (_hχ : χ ≠ 1)` : `∀ Lf, AnalyticOn ℂ Lf {Re s > 1 − 1/d} → (∀ s, 1 < s.re → Lf s = ∑'_{𝔞 ≠ ⊥} χ̃(𝔞)·N𝔞^{-s}) → Lf 1 ≠ 0`
- **What**: Sharifi 7.1.19 step 2 — non-vanishing `L(χ,1) ≠ 0` for nontrivial `χ`.
- **How**: Dirichlet's global argument: if `Lf 1 = 0`, `Lf` is not locally zero (`artinDirichletSeries_ne_zero_of_one_lt`), so `analytic_log_norm_le_of_apply_eq_zero` gives the analytic-zero bound, fed to `log_norm_artinDirichletSeries_le_pole_zero_ite`, then `false_of_eventually_log_norm_le_pole_zero_ite`. ~20-line proof.
- **Hypotheses**: full bundle; `m % 4 ≠ 2`, `χ ≠ 1`.
- **Uses from project**: [`galoisCharacter`, `galoisCharacterOnIdeal`, `artinDirichletSeries`, `analyticAt_one_of_analyticOn_finrankDomain`, `artinDirichletSeries_ne_zero_of_one_lt`, `analytic_log_norm_le_of_apply_eq_zero`, `log_norm_artinDirichletSeries_le_pole_zero_ite`, `false_of_eventually_log_norm_le_pole_zero_ite`, `NonzeroIdeal`]
- **Used by**: unused in file (top-level export)
- **Visibility**: public
- **Lines**: 3129–3173 (proof ~20)
- **Notes**: `classical`

---

## File Summary

**Total declarations: 84.**
- **defs: 11** — `galoisCharacterOnIdeal`, `charEval`, `frobeniusIdeal`, `badPart`, `goodPart`, `IsBadPart`, `realizedResidues`, `galoisCharacterCoeff`, `artinDirichletSeries`, `underUP`, `fiberUnderEquiv`, `unramifiedFlattenEquiv`, `ramifiedFlattenEquiv` — *(13 defs counting the four `Equiv`/map defs `underUP`/`fiberUnderEquiv`/`unramifiedFlattenEquiv`/`ramifiedFlattenEquiv`; `galoisCharacter` is an `abbrev`)*.
  - Precisely: 1 `abbrev` (`galoisCharacter`) + 12 `def`s.
- **lemmas/theorems: 67.**
- **instances: 4** — `finite_L2`, `finite_ramifiedAbove` (private instances), `galoisCharacter.instFintype` (local instance); plus `finite_isBadPart` is a `theorem` not an instance. (3 declared `instance` + the local Fintype.)

(Net: 1 abbrev + 12 defs + 67 lemmas/theorems + 3 `instance`/`local instance` + 1 `local instance` Fintype = 84 declarations.)

### Key API (used by ≥ 3 in-file decls)
- `galoisCharacter` (abbrev) — the central type, used ubiquitously.
- `galoisCharacterOnIdeal` (def) and `galoisCharacterOnIdeal_eq_map_prod` — the ideal character + its multiset form.
- `norm_galoisCharacterOnIdeal_le_one` — used by 3.
- `frobeniusIdeal` (def), `frobeniusIdeal_mul`, `frobeniusIdeal_one` — the ideal Frobenius and its multiplicativity.
- `UnramifiedIn` (project import) — pervasive.
- `frobeniusClass` (project import) — pervasive.
- `finite_isBadPart` — used by ~6 error-assembly lemmas.
- `card_L2_eq_sum_residue` — used by both `d≥2`/`d=1` branches.
- `exists_kappa_uniform` — used by both branches.
- `artinDirichletSeries` (def) — used across the factorisation + non-vanishing chains.
- `NonzeroIdeal` (project type, from Density/CNR), `idealNormMultiplicity`, `hasSum_nonzeroIdeal_absNorm_cpow` (Density imports) — recurring infrastructure.

### Unused decls (within this file)
- `artinLSeries_one_ne_zero` — top-level export (consumed by other files / final Chebotarev assembly), unused in this file.
- `dedekindZeta_eq_prod_artinDirichletSeries`, `character_sum_geometry_of_numbers_bound`, `artinLSeries_analytic_extension`, `exists_artinLSeries_eulerProduct_abelian`, `dedekindZeta_local_factor_eq_product_artin_local` are all used in-file EXCEPT note that the headline public theorems are also intended as exports. All other public/private decls are consumed in-file.

### Decls with `sorry`
- **None.** The file is `sorry`-free (the L2 assembly and the `d=1` Eisenstein branch are fully discharged; confirmed by reading every proof body).

### Decls with `set_option`
- **None.** No `set_option` anywhere in the file.

### Proofs > 50 lines (decompose-needed)
| Decl | Lines | Proof length |
|---|---|---|
| `prod_galoisCharacter_one_sub` | 275–344 | ~63 |
| `unramifiedIn_of_coprime_absNorm` | 614–673 | ~55 |
| `card_fibre_eq_card_good_fibre` | 840–904 | ~55 |
| `sum_rpow_le_euler_prod` | 1144–1214 | ~62 |
| `ciSup_sum_inv_absNorm_sub_le` | 1309–1370 | ~55 |
| `card_fibre_bound_two_le` | 1416–1552 | ~127 |
| `coprime_absNorm_of_unramified_of_finrank_eq_one` | 1638–1715 | ~53 |
| `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow` | 1848–1947 | ~65 |
| `tprod_unramified_eq_prod_artinDirichletSeries` | 2635–2707 | ~57 |

(9 proofs over 50 lines; `card_fibre_bound_two_le` at ~127 is the largest and the highest-priority decompose target.)

### Proofs 30–50 lines
| Decl | Lines | Proof length |
|---|---|---|
| `dedekindZeta_local_factor_eq_product_artin_local` | 352–409 | ~46 |
| `card_good_fibre_eq_card_residue` | 712–747 | ~30 |
| `card_L2_eq_sum_fibres` | 935–973 | ~33 |
| `abs_sub_kappa_mul_div_le` | 1268–1307 | ~33 |
| `card_fibre_bound_eq_one` | 1717–1755 | ~33 |
| `sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul` | 1991–2040 | ~33 |
| `character_sum_geometry_of_numbers_bound` | 2051–2098 | ~33 |
| `artinLSeries_analytic_extension` | 2266–2341 | ~50 (borderline) |
| `analytic_log_norm_le_of_apply_eq_zero` | 2374–2428 | ~48 |
| `log_norm_ramified_factor_bounded` | 2823–2876 | ~42 |
| `log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded` | 2878–2922 | ~32 |
| `log_norm_artinDirichletSeries_one_le` | 2963–3025 | ~47 |

(12 proofs in the 30–50 band; `card_finite_isBadPart_le` ~24, `card_charFibre_…`/`charFibre_mem_range` ~24, `multipliable_artinLocalFactor`/`autToPow_frobeniusIdeal` ~25, `card_unramifiedSupported_…_eq_sum`/`lseries_…_eq_tsum`/`false_of_…_ite` ~27 sit just below 30.)
