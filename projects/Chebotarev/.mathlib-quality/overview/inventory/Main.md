# Inventory: `projects/Chebotarev/CebotarevDensity/Main.lean`

File-level context: top of file declares `@[expose] public section`, `noncomputable section`,
`open Filter NumberField Topology Set`, `open scoped ENNReal`, `namespace Chebotarev`.
File-level variables (lines 62–63): `{K L : Type*} [Field K] [NumberField K] [Field L]
[NumberField L] [Algebra K L] [IsGalois K L]`.

This file holds the **top-level Chebotarev density theorem**:
`Chebotarev.chebotarev_density` (lines 71–87).

---

### `theorem chebotarev_density`
- **Type**: `[FiniteDimensional K L] (C : ConjClasses Gal(L/K)) : HasDirichletDensity {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = C} ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K))`
- **What**: Chebotarev's density theorem in conjugacy-class form: for a finite Galois extension `L/K` of number fields with group `G`, the set of unramified primes `𝔭` of `𝓞 K` whose Frobenius conjugacy class equals a fixed class `C` has Dirichlet density `|C| / |G|`.
- **How**: Reduces the conjugacy-class statement to the cyclic case. Picks a representative `σ` of `C`, passes to the intermediate field `E = L^⟨σ⟩` (`IntermediateField.fixedField (Subgroup.zpowers σ)`), establishes that `Gal(L/E)` is commutative via `IntermediateField.subgroupEquivAlgEquiv` transporting `mul_comm'` from `zpowers σ`, then invokes the project lemma `density_lift_through_fixedField` together with the abelian case `chebotarev_abelian`.
- **Hypotheses**: `L/K` finite-dimensional (and the ambient finite Galois extension of number fields from the file variables); `C` a conjugacy class of the Galois group.
- **Uses from project**: `density_lift_through_fixedField`, `chebotarev_abelian` (both imported, not defined in this file).
- **Used by**: `chebotarev_density_of_comm`, `infinite_setOf_frobenius_class`, `density_split_completely`.
- **Visibility**: public.
- **Lines**: 71–87 (proof ≈ 11 lines, 77–87).
- **Notes**: long proof body is just at the boundary; under 30. none.

---

### `theorem ConjClasses_carrier_card_eq_one_of_comm`
- **Type**: `{G : Type*} [Monoid G] [IsMulCommutative G] [Finite G] (g : G) : Nat.card (ConjClasses.mk g).carrier = 1`
- **What**: In a finite commutative monoid every conjugacy class is a singleton, so its carrier has cardinality `1`.
- **How**: In a commutative monoid `isConj_iff_eq` makes conjugacy equality, so the carrier of `mk g` equals `{g}`; concludes by `Nat.card` of a singleton.
- **Hypotheses**: `G` a finite commutative monoid; `g` an element.
- **Uses from project**: `[]`.
- **Used by**: `chebotarev_density_of_comm`.
- **Visibility**: public.
- **Lines**: 89–98 (proof ≈ 6 lines).
- **Notes**: none.

---

### `theorem chebotarev_density_of_comm`
- **Type**: `[FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (C : ConjClasses Gal(L/K)) : HasDirichletDensity {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = C} ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K))`
- **What**: The abelian case of Chebotarev stated in conjugacy-class form: for an abelian Galois extension the density of unramified primes with Frobenius class `C` is `|C| / |G|`.
- **How**: Picks a representative `σ` of `C`; since the group is commutative `ConjClasses_carrier_card_eq_one_of_comm` makes `|C| = 1`, and the result reduces to `chebotarev_abelian`.
- **Hypotheses**: `L/K` finite-dimensional and the Galois group commutative; `C` a conjugacy class.
- **Uses from project**: `ConjClasses_carrier_card_eq_one_of_comm` (this file), `chebotarev_abelian` (imported).
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 100–110 (proof ≈ 2 lines).
- **Notes**: none.

---

### `theorem infinite_of_hasDirichletDensity_pos`
- **Type**: `{S : Set (Ideal (𝓞 K))} {δ : ℝ} (h : HasDirichletDensity S δ) (hδ : 0 < δ) : S.Infinite`
- **What**: A set of prime ideals with strictly positive Dirichlet density is infinite.
- **How**: Contrapositive — a finite set has density `0` (`hasDirichletDensity_of_finite`), and uniqueness of limits (`tendsto_nhds_unique`) would force `δ = 0`, contradicting `0 < δ`.
- **Hypotheses**: `S` has Dirichlet density `δ` with `δ > 0`.
- **Uses from project**: `hasDirichletDensity_of_finite` (imported).
- **Used by**: `infinite_setOf_frobenius_class`.
- **Visibility**: public.
- **Lines**: 113–116 (proof ≈ 1 line, term-mode).
- **Notes**: none.

---

### `theorem ConjClasses_carrier_card_pos`
- **Type**: `{G : Type*} [Monoid G] [Finite G] (C : ConjClasses G) : 0 < Nat.card C.carrier`
- **What**: In a finite monoid the carrier of any conjugacy class has positive cardinality (it is nonempty).
- **How**: Pick a representative `a` of `C`; `a` itself lies in the carrier of `mk a` (`ConjClasses.mem_carrier_mk`), so the carrier is nonempty and `Nat.card_pos` applies.
- **Hypotheses**: `G` a finite monoid; `C` a conjugacy class.
- **Uses from project**: `[]`.
- **Used by**: `infinite_setOf_frobenius_class`.
- **Visibility**: public.
- **Lines**: 119–124 (proof ≈ 4 lines).
- **Notes**: none.

---

### `theorem infinite_setOf_frobenius_class`
- **Type**: `(C : ConjClasses Gal(L/K)) : Set.Infinite {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = C}`
- **What**: There are infinitely many primes of `𝓞 K` with any prescribed Frobenius conjugacy class — the qualitative corollary of `chebotarev_density`.
- **How**: Applies `infinite_of_hasDirichletDensity_pos` to `chebotarev_density C`; positivity of the density `|C|/|G|` follows from `div_pos`, `ConjClasses_carrier_card_pos`, and `Nat.card_pos` for the (nonempty finite) Galois group.
- **Hypotheses**: ambient finite Galois extension of number fields; `C` a conjugacy class.
- **Uses from project**: `infinite_of_hasDirichletDensity_pos`, `chebotarev_density`, `ConjClasses_carrier_card_pos` (all this file).
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 126–136 (proof ≈ 5 lines).
- **Notes**: none.

---

### `theorem ConjClasses_mk_one_carrier_card_eq_one`
- **Type**: `(G : Type*) [Monoid G] [Finite G] : Nat.card (ConjClasses.mk (1 : G)).carrier = 1`
- **What**: In a finite monoid the identity conjugacy class has carrier `{1}`, of cardinality `1` (anything conjugate to `1` equals `1`).
- **How**: Shows the carrier of `mk 1` equals `{1}` via `ConjClasses.mem_carrier_iff_mk_eq` and `mk_eq_mk_iff_isConj`, then `Nat.card` of a singleton.
- **Hypotheses**: `G` a finite monoid.
- **Uses from project**: `[]`.
- **Used by**: `density_split_completely`.
- **Visibility**: public.
- **Lines**: 138–144 (proof ≈ 4 lines).
- **Notes**: none.

---

### `theorem density_split_completely`
- **Type**: `HasDirichletDensity {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk 1} ((Module.finrank K L : ℝ)⁻¹)`
- **What**: The Dirichlet density of primes of `𝓞 K` that split completely in `L` (Frobenius class = identity) equals `1 / [L:K]`.
- **How**: Specialises `chebotarev_density` to the identity class; `ConjClasses_mk_one_carrier_card_eq_one` makes the numerator `1` and `IsGalois.card_aut_eq_finrank` rewrites `|Gal(L/K)| = [L:K]`.
- **Hypotheses**: ambient finite Galois extension of number fields.
- **Uses from project**: `chebotarev_density`, `ConjClasses_mk_one_carrier_card_eq_one` (this file).
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 146–158 (proof ≈ 3 lines).
- **Notes**: none.

---

(Section `DirichletAP` opens at line 173 with `variable {K : Type*} [Field K] [NumberField K]`.)

### `private theorem primeIdealZetaSum_eq_add_sub_sdiff`
- **Type**: `{S T : Set (Ideal (𝓞 K))} {s : ℝ} (hs : 1 < s) : primeIdealZetaSum T s = primeIdealZetaSum S s + primeIdealZetaSum (T \ S) s - primeIdealZetaSum (S \ T) s`
- **What**: An inclusion–exclusion identity for the partial prime-ideal zeta sum: `Σ_T = Σ_S + Σ_{T∖S} − Σ_{S∖T}` for `s > 1`.
- **How**: From the two disjoint-union decompositions `T = (T∩S) ⊔ (T∖S)` and `S = (T∩S) ⊔ (S∖T)`, applies `primeIdealZetaSum_union_of_disjoint` (with `inter_union_diff` and a generic `Disjoint (A∩B) (A∖B)` fact), then `ring`.
- **Hypotheses**: `s > 1` (convergence regime); arbitrary sets `S`, `T` of ideals.
- **Uses from project**: `primeIdealZetaSum` and `primeIdealZetaSum_union_of_disjoint` (imported).
- **Used by**: `hasDirichletDensity_of_finite_symmDiff`.
- **Visibility**: private.
- **Lines**: 179–194 (proof ≈ 12 lines).
- **Notes**: none.

---

### `private theorem hasDirichletDensity_of_finite_symmDiff`
- **Type**: `{S T : Set (Ideal (𝓞 K))} {δ : ℝ} (hST : (S \ T).Finite) (hTS : (T \ S).Finite) (hS : HasDirichletDensity S δ) : HasDirichletDensity T δ`
- **What**: Dirichlet density is insensitive to finite symmetric differences: if `S∖T` and `T∖S` are finite and `S` has density `δ`, then `T` also has density `δ`.
- **How**: The finite differences have density `0` (`hasDirichletDensity_of_finite`); combining the density limits via `.add`/`.sub` and rewriting the ratio with `primeIdealZetaSum_eq_add_sub_sdiff` (on the `1 < s` neighbourhood, using `Filter.congr'`/`filter_upwards`) shows `T`'s ratio shares the limit `δ`.
- **Hypotheses**: both one-sided differences finite; `S` has density `δ`.
- **Uses from project**: `HasDirichletDensity`, `hasDirichletDensity_of_finite`, `primeIdealZetaSum_eq_add_sub_sdiff` (last is this file; others imported).
- **Used by**: `dirichlet_AP_main`, `dirichlet_AP_two_mul`.
- **Visibility**: private.
- **Lines**: 199–210 (proof ≈ 9 lines).
- **Notes**: none.

---

### `private theorem zmod_eq_of_castHom_eq`
- **Type**: `{m k : ℕ} (hcop : Nat.Coprime m k) (x y : ZMod (m * k)) (h1 : castHom (dvd_mul_right m k) (ZMod m) x = … y) (h2 : castHom (dvd_mul_left k m) (ZMod k) x = … y) : x = y`
- **What**: Chinese-remainder injectivity: two elements of `ZMod (m*k)` (with `m,k` coprime) that agree under both coordinate reduction maps to `ZMod m` and `ZMod k` are equal.
- **How**: Uses injectivity of `ZMod.chineseRemainder hcop`; identifies the two product-coordinates of the CRT image with the two `castHom` reductions (`Prod.fst_zmod_cast` / `Prod.snd_zmod_cast`) and concludes by `Prod.ext`.
- **Hypotheses**: `m`, `k` coprime; `x`, `y` agree under both reductions.
- **Uses from project**: `[]`.
- **Used by**: `residue_iff_half`.
- **Visibility**: private.
- **Lines**: 214–228 (proof ≈ 10 lines).
- **Notes**: none.

---

(Section `DirichletAP` closes at line 230; subsequent privates are back in the file-`{K L}` scope but most fix `ℚ` explicitly.)

### `private theorem absNorm_span_nat`
- **Type**: `(p : ℕ) : Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p`
- **What**: The absolute norm of the principal ideal `span {(p)}` in `𝓞 ℚ` equals `p`.
- **How**: `Ideal.absNorm_span_natCast` gives `p ^ rank ℤ (𝓞 ℚ)`; since `rank ℤ (𝓞 ℚ) = finrank ℚ ℚ = 1` (`NumberField.RingOfIntegers.rank`, `Module.finrank_self`), the exponent is `1`.
- **Hypotheses**: `p` a natural number.
- **Uses from project**: `[]`.
- **Used by**: `dirichlet_AP_fibre_diff_image_subset_bad`, `dirichlet_AP_image_diff_fibre_subset_bad`.
- **Visibility**: private.
- **Lines**: 234–235 (proof ≈ 1 line).
- **Notes**: none.

---

### `private theorem ratSpan_eq_comap_intSpan`
- **Type**: `(p : ℕ) : Ideal.span {(p : 𝓞 ℚ)} = Ideal.comap Rat.ringOfIntegersEquiv (Ideal.span {(p : ℤ)})`
- **What**: The rational prime ideal `span {(p)}` of `𝓞 ℚ` is the pullback of `span {(p : ℤ)}` along the canonical ring isomorphism `Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ`.
- **How**: Rewrites `comap` as `map` along the inverse (`Ideal.map_symm`), uses `Ideal.map_span` / `Set.image_singleton`, and reduces to `map_natCast` on the generator.
- **Hypotheses**: `p` a natural number.
- **Uses from project**: `[]`.
- **Used by**: `ratPrime_eq_span`, `span_nat_isPrime`.
- **Visibility**: private.
- **Lines**: 238–243 (proof ≈ 4 lines).
- **Notes**: none.

---

### `private theorem ratPrime_eq_span`
- **Type**: `(𝔭 : Ideal (𝓞 ℚ)) (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) : ∃ p : ℕ, p.Prime ∧ 𝔭 = Ideal.span {(p : 𝓞 ℚ)}`
- **What**: Every nonzero prime ideal of `𝓞 ℚ` equals `span {(p)}` for some rational prime `p`.
- **How**: Transports `𝔭` through `Rat.ringOfIntegersEquiv`: its image is a nonzero prime of `ℤ`, hence `span {(p : ℤ)}` for a prime `p` by `Ideal.isPrime_int_iff`; pulls back using `Ideal.comap_map_of_bijective` and `ratSpan_eq_comap_intSpan`.
- **Hypotheses**: `𝔭` a nonzero prime ideal of `𝓞 ℚ`.
- **Uses from project**: `ratSpan_eq_comap_intSpan` (this file).
- **Used by**: `dirichlet_AP_fibre_diff_image_subset_bad`.
- **Visibility**: private.
- **Lines**: 248–258 (proof ≈ 9 lines).
- **Notes**: none.

---

### `private theorem span_nat_isPrime`
- **Type**: `{p : ℕ} (hpp : p.Prime) : (Ideal.span {(p : 𝓞 ℚ)}).IsPrime`
- **What**: For a rational prime `p`, the principal ideal `span {(p)}` of `𝓞 ℚ` is prime (the converse classification ingredient).
- **How**: `span {(p : ℤ)}` is prime (`Ideal.span_singleton_prime` + `Nat.prime_iff_prime_int`); since `span {(p : 𝓞 ℚ)}` is its `comap` along `Rat.ringOfIntegersEquiv` (`ratSpan_eq_comap_intSpan`), `Ideal.comap_isPrime` finishes.
- **Hypotheses**: `p` prime.
- **Uses from project**: `ratSpan_eq_comap_intSpan` (this file).
- **Used by**: `dirichlet_AP_image_diff_fibre_subset_bad`.
- **Visibility**: private.
- **Lines**: 262–268 (proof ≈ 5 lines).
- **Notes**: none.

---

### `private theorem unramifiedIn_cyclotomic_of_coprime`
- **Type**: `{K} [Field K] [NumberField K] (L) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) (hcop : (Ideal.absNorm 𝔭).Coprime m) : UnramifiedIn K L 𝔭`
- **What**: A prime `𝔭` of `𝓞 K` whose absolute norm is coprime to `m` is unramified in the cyclotomic extension `L = K(μ_m)`.
- **How**: A ramified prime `𝔓` above `𝔭` divides the different, which (conductor formula `conductor_mul_differentIdeal`) divides `(f'(ζ))`; since `minpoly ∣ X^m − 1`, that derivative value divides `m·ζ^{m−1}`, forcing `m ∈ 𝔓` hence `m ∈ 𝔭`, so `N𝔭 ∣ m^d` — contradicting coprimality via `Ideal.absNorm_eq_one_iff` / `Nat.eq_one_of_dvd_coprimes`. Hinges on `not_dvd_differentIdeal_iff`, `conductor_mul_differentIdeal`, and `IsCyclotomicExtension.adjoin_primitive_root_eq_top`.
- **Hypotheses**: `L = K(μ_m)` Galois cyclotomic over `K`, `m ≠ 0`; `𝔭` a nonzero prime with `gcd(N𝔭, m) = 1`.
- **Uses from project**: `[]` (a self-contained replica of a private lemma from `ZetaProduct.lean`; relies only on mathlib).
- **Used by**: `dirichlet_AP_image_diff_fibre_subset_bad`.
- **Visibility**: private.
- **Lines**: 275–327 (proof ≈ 48 lines, 280–327).
- **Notes**: `long (30–50)` — 48-line proof; uses `classical`. No sorry/TODO.

---

### `private theorem frobeniusClass_eq_iff_residue`
- **Type**: `(n : ℕ) [NeZero n] (L) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L] [IsCyclotomicExtension {n} ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)] {ζ : L} (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) (ha : IsUnit a) (σ : L ≃ₐ[ℚ] L) (hσ : hζ.autToPow ℚ σ = ha.unit) (𝔭 : Ideal (𝓞 ℚ)) [𝔭.IsPrime] (hunr : UnramifiedIn ℚ L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime n) : frobeniusClass ℚ L 𝔭 = ConjClasses.mk σ ↔ (Ideal.absNorm 𝔭 : ZMod n) = a`
- **What**: Frobenius ↔ residue dictionary for `L = ℚ(μ_n)`: for a coprime-norm unramified prime `𝔭`, with `σ` chosen so the cyclotomic character sends `σ` to the unit `a`, the Frobenius class of `𝔭` is `mk σ` iff `N𝔭 ≡ a [n]`.
- **How**: Uses the imported `autToPow_frobeniusClass_out` (Frobenius realised as `N𝔭 mod n` under the cyclotomic character), reduces conjugacy-class equality to element equality (commutative group, `isConj_iff_eq`), and uses injectivity `IsPrimitiveRoot.autToPow_injective`, transferring through `ZMod.coe_unitOfCoprime` / `IsUnit.unit_spec`.
- **Hypotheses**: `L = ℚ(μ_n)` abelian Galois cyclotomic; `σ` realising the unit `a` under `autToPow`; `𝔭` unramified prime with norm coprime to `n`.
- **Uses from project**: `autToPow_frobeniusClass_out` (imported).
- **Used by**: `dirichlet_AP_fibre_diff_image_subset_bad`, `dirichlet_AP_image_diff_fibre_subset_bad`.
- **Visibility**: private.
- **Lines**: 333–355 (proof ≈ 14 lines, 341–355).
- **Notes**: none.

---

### `private theorem residue_iff_half`
- **Type**: `(n' : ℕ) (hcop : Nat.Coprime 2 n') (a : ZMod (2 * n')) (ha : IsUnit a) (p : ℕ) (hpp : p.Prime) (hodd : p ≠ 2) : ((p : ZMod (2 * n')) = a ↔ (p : ZMod n') = (ZMod.castHom (dvd_mul_left n' 2) (ZMod n')) a)`
- **What**: For `n = 2·n'` with `n'` odd and an odd prime `p`, the residue condition `p ≡ a [2n']` is equivalent to `p ≡ a' [n']` where `a' = a mod n'`.
- **How**: Forward by reducing mod `n'` (`map_natCast`). Backward by `zmod_eq_of_castHom_eq` (CRT): the `mod n'` coordinates agree by hypothesis and the `mod 2` coordinates agree because `(p : ZMod 2) = 1` (odd prime, `Nat.Prime.eq_two_or_odd`) and a unit of `ZMod (2n')` reduces to `1` mod `2` (finite `decide`).
- **Hypotheses**: `n'` odd; `a` a unit of `ZMod (2n')`; `p` an odd prime.
- **Uses from project**: `zmod_eq_of_castHom_eq` (this file).
- **Used by**: `dirichlet_AP_two_mul`.
- **Visibility**: private.
- **Lines**: 360–378 (proof ≈ 18 lines, 364–378).
- **Notes**: none. Uses `decide` on a `ZMod 2` unit.

---

### `private theorem dirichlet_AP_fibre_diff_image_subset_bad`
- **Type**: `(n : ℕ) (L) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L] [NeZero n] [IsCyclotomicExtension {n} ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)] {ζ} (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) (ha : IsUnit a) (σ : L ≃ₐ[ℚ] L) (hσ : hζ.autToPow ℚ σ = ha.unit) : {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn ℚ L 𝔭 ∧ frobeniusClass ℚ L 𝔭 = mk σ} \ (span∘cast '' {p | p.Prime ∧ (p : ZMod n) = a}) ⊆ (span∘cast '' {q | q.Prime ∧ q ∣ n})`
- **What**: Primes in the Frobenius fibre `F` but outside the AP image-set `I` must divide `n`: `F ∖ I ⊆ Bad`.
- **How**: A prime of `F∖I` is `span {(q)}` for a rational prime `q` (`ratPrime_eq_span`) with norm `q` (`absNorm_span_nat`); if its norm were coprime to `n`, `frobeniusClass_eq_iff_residue` would place it in `I` (contradiction), so `q ∣ n`, landing in `Bad`.
- **Hypotheses**: `L = ℚ(μ_n)` abelian cyclotomic; `σ` realising unit `a`.
- **Uses from project**: `ratPrime_eq_span`, `absNorm_span_nat`, `frobeniusClass_eq_iff_residue` (all this file).
- **Used by**: `dirichlet_AP_main`.
- **Visibility**: private.
- **Lines**: 383–402 (proof ≈ 11 lines, 392–402).
- **Notes**: none.

---

### `private theorem dirichlet_AP_image_diff_fibre_subset_bad`
- **Type**: `(n : ℕ) (L) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L] [NeZero n] [IsCyclotomicExtension {n} ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)] {ζ} (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) (ha : IsUnit a) (σ : L ≃ₐ[ℚ] L) (hσ : hζ.autToPow ℚ σ = ha.unit) : (span∘cast '' {p | p.Prime ∧ (p : ZMod n) = a}) \ {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn ℚ L 𝔭 ∧ frobeniusClass ℚ L 𝔭 = mk σ} ⊆ (span∘cast '' {q | q.Prime ∧ q ∣ n})`
- **What**: Primes in the AP image-set `I` but outside the Frobenius fibre `F` must divide `n`: `I ∖ F ⊆ Bad`.
- **How**: For `p ≡ a [n]` with `p ∤ n`, `span {(p)}` is prime (`span_nat_isPrime`) with norm coprime to `n` (`absNorm_span_nat`), hence unramified (`unramifiedIn_cyclotomic_of_coprime`) and `frobeniusClass_eq_iff_residue` puts it in `F` — contradiction; therefore `p ∣ n`.
- **Hypotheses**: `L = ℚ(μ_n)` abelian cyclotomic; `σ` realising unit `a`.
- **Uses from project**: `span_nat_isPrime`, `unramifiedIn_cyclotomic_of_coprime`, `frobeniusClass_eq_iff_residue`, `absNorm_span_nat` (all this file).
- **Used by**: `dirichlet_AP_main`.
- **Visibility**: private.
- **Lines**: 407–430 (proof ≈ 15 lines, 416–430).
- **Notes**: none.

---

### `private theorem dirichlet_AP_main`
- **Type**: `(n : ℕ) (hn4 : n % 4 ≠ 2) (hn : 1 ≤ n) (a : ZMod n) (ha : IsUnit a) : HasDirichletDensity ((fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) '' {p : ℕ | p.Prime ∧ (p : ZMod n) = a}) ((Nat.totient n : ℝ)⁻¹)`
- **What**: The main case of Dirichlet's arithmetic-progression theorem (`n ≢ 2 [4]`): primes `p ≡ a [n]` have Dirichlet density `1/φ(n)`.
- **How**: Instantiates `L = CyclotomicField n ℚ` with its cyclotomic/Galois/commutative instances, picks `σ` via `IsCyclotomicExtension.autEquivPow` with `autToPow σ = a` (proved through `IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter`), invokes `chebotarev_cyclotomic` to get density `1/|Gal|` on the Frobenius fibre, rewrites `|Gal| = φ(n)` (`ZMod.card_units_eq_totient`), then transfers to the image-set `I` via `hasDirichletDensity_of_finite_symmDiff` using the two `…_subset_bad` lemmas and finiteness of `Bad`.
- **Hypotheses**: `n ≥ 1`, `n % 4 ≠ 2`; `a` a unit of `ZMod n`.
- **Uses from project**: `chebotarev_cyclotomic` (imported); `hasDirichletDensity_of_finite_symmDiff`, `dirichlet_AP_fibre_diff_image_subset_bad`, `dirichlet_AP_image_diff_fibre_subset_bad` (this file).
- **Used by**: `dirichlet_AP_two_mul`, `dirichlet_primes_in_AP`.
- **Visibility**: private.
- **Lines**: 435–478 (proof ≈ 39 lines, 440–478).
- **Notes**: `long (30–50)` — 39-line proof. Uses `lia`; two explanatory `haveI` comments. No sorry.

---

### `private theorem dirichlet_AP_two_mul`
- **Type**: `(n' : ℕ) (hn'1 : 1 ≤ n') (hcop : Nat.Coprime 2 n') (a : ZMod (2 * n')) (ha : IsUnit a) : HasDirichletDensity ((fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) '' {p : ℕ | p.Prime ∧ (p : ZMod (2 * n')) = a}) ((Nat.totient (2 * n') : ℝ)⁻¹)`
- **What**: The degenerate corner `n = 2·n'` with `n'` odd (so `n ≡ 2 [4]`), where `chebotarev_cyclotomic` does not apply: the AP density for `2n'` equals that for the odd modulus `n'`, namely `1/φ(2n') = 1/φ(n')`.
- **How**: Reduces to `dirichlet_AP_main n'` with `a' = a mod n'`; equates totients (`Nat.totient_mul` + `Nat.totient_two`); the image-sets for `2n'` and `n'` differ only by the single prime `2` (shown by `residue_iff_half`), so `hasDirichletDensity_of_finite_symmDiff` over a singleton transfers the density.
- **Hypotheses**: `n' ≥ 1`, `n'` odd (`Coprime 2 n'`); `a` a unit of `ZMod (2n')`.
- **Uses from project**: `dirichlet_AP_main`, `residue_iff_half`, `hasDirichletDensity_of_finite_symmDiff` (all this file).
- **Used by**: `dirichlet_primes_in_AP`.
- **Visibility**: private.
- **Lines**: 483–509 (proof ≈ 22 lines, 488–509).
- **Notes**: none. Uses `lia`.

---

### `theorem dirichlet_primes_in_AP`
- **Type**: `(n : ℕ) (hn : 1 ≤ n) (a : ZMod n) (ha : IsUnit a) : HasDirichletDensity ((fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) '' {p : ℕ | p.Prime ∧ (p : ZMod n) = a}) ((Nat.totient n : ℝ)⁻¹)`
- **What**: Dirichlet's theorem on primes in arithmetic progressions, as a density refinement: for `a` coprime to `n` (`1 ≤ n`), the density of primes `p ≡ a [n]` equals `1/φ(n)`. The `K=ℚ`, `L=ℚ(μ_n)` specialisation of Chebotarev (Sharifi 7.2.3).
- **How**: Case split on `n % 4 = 2`: in the degenerate case writes `n = 2·n'` and applies `dirichlet_AP_two_mul`; otherwise applies `dirichlet_AP_main`.
- **Hypotheses**: `n ≥ 1`; `a` a unit of `ZMod n`.
- **Uses from project**: `dirichlet_AP_two_mul`, `dirichlet_AP_main` (this file).
- **Used by**: unused in file (top-level corollary).
- **Visibility**: public.
- **Lines**: 517–526 (proof ≈ 5 lines).
- **Notes**: none. Uses `lia`.

---

## File Summary

- **Total declarations: 23** — defs: 0 · lemmas+theorems: 23 · instances: 0 · structures/classes/abbrevs/inductives: 0.
  - **Public (9)**: `chebotarev_density`, `ConjClasses_carrier_card_eq_one_of_comm`, `chebotarev_density_of_comm`, `infinite_of_hasDirichletDensity_pos`, `ConjClasses_carrier_card_pos`, `infinite_setOf_frobenius_class`, `ConjClasses_mk_one_carrier_card_eq_one`, `density_split_completely`, `dirichlet_primes_in_AP`.
  - **Private (14)**: `primeIdealZetaSum_eq_add_sub_sdiff`, `hasDirichletDensity_of_finite_symmDiff`, `zmod_eq_of_castHom_eq`, `absNorm_span_nat`, `ratSpan_eq_comap_intSpan`, `ratPrime_eq_span`, `span_nat_isPrime`, `unramifiedIn_cyclotomic_of_coprime`, `frobeniusClass_eq_iff_residue`, `residue_iff_half`, `dirichlet_AP_fibre_diff_image_subset_bad`, `dirichlet_AP_image_diff_fibre_subset_bad`, `dirichlet_AP_main`, `dirichlet_AP_two_mul`.

- **TOP-LEVEL CHEBOTAREV THEOREM**: `Chebotarev.chebotarev_density` (lines 71–87) — Chebotarev's density theorem in conjugacy-class form, density `|C|/|G|`. Notable top-level corollaries in this file: `dirichlet_primes_in_AP` (Dirichlet's AP theorem, density `1/φ(n)`) and `density_split_completely` (split-completely density `1/[L:K]`).

- **Key API (used by ≥3 in-file): `chebotarev_density`** — consumed by `chebotarev_density_of_comm`, `infinite_setOf_frobenius_class`, and `density_split_completely`. No other in-file decl reaches 3 in-file consumers; the next tier is used by exactly 2 each: `frobeniusClass_eq_iff_residue`, `absNorm_span_nat`, `ratSpan_eq_comap_intSpan`, `hasDirichletDensity_of_finite_symmDiff`, `dirichlet_AP_main`.

- **Unused in file (4 terminal/exported corollaries, no in-file consumer)**: `chebotarev_density_of_comm`, `infinite_setOf_frobenius_class`, `density_split_completely`, `dirichlet_primes_in_AP`. (All private lemmas are consumed in-file; `ConjClasses_carrier_card_eq_one_of_comm` is used by `chebotarev_density_of_comm`, so it is NOT unused.)

- **Decls with `sorry`: none.**

- **Decls with `set_option`: none.**

- **Proofs >50 lines (decompose-needed): none.** No proof exceeds 50 lines.

- **Proofs 30–50 lines (long):**
  - `unramifiedIn_cyclotomic_of_coprime` — ≈ 48 lines (280–327). Closest to the 50-line threshold; a `/decompose-proof` candidate if the cap tightens.
  - `dirichlet_AP_main` — ≈ 39 lines (440–478).

- **Imports / dependencies on other Chebotarev modules**: `CebotarevDensity.Abelian` and `CebotarevDensity.FixedFieldDensity`. Referenced-but-upstream decls: `chebotarev_abelian`, `chebotarev_cyclotomic`, `autToPow_frobeniusClass_out`, `density_lift_through_fixedField`, plus the `HasDirichletDensity` / `primeIdealZetaSum` / `frobeniusClass` / `UnramifiedIn` API and `hasDirichletDensity_of_finite`, `primeIdealZetaSum_union_of_disjoint`.
