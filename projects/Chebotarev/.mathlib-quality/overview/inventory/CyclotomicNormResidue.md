# Inventory — `CyclotomicNormResidue.lean`

Path: `projects/Chebotarev/CebotarevDensity/CyclotomicNormResidue.lean`
Namespace: `Chebotarev`. Module header: `@[expose] public section`, `noncomputable section`.
Two arithmetic inputs to Frobenius-fibre equidistribution: the cyclotomic Frobenius as a norm
residue, and "Frobenii generate the Galois group" (CFT-free, via the project's zeta asymptotics).

---

### `theorem cyclotomic_frobenius_acts_as_norm_power`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime m) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) → ∀ ζ : L, ζ ∈ primitiveRoots m L → arithFrobAt (𝓞 K) Gal(L/K) 𝔓 ζ = ζ ^ Ideal.absNorm 𝔭` (under a local `Finite (𝓞 L ⧸ 𝔓)` instance).
- **What**: For `L = K(μ_m)`, the arithmetic Frobenius at a prime `𝔓 ∣ 𝔭` raises every primitive `m`-th root of unity `ζ` to the `N𝔭`-th power (the element-level Frobenius congruence `Frob_𝔭(ζ) = ζ^{N𝔭}`, Sharifi 7.2.1(i)).
- **How**: Pushes the integer-level identity `IsArithFrobAt.apply_of_pow_eq_one` (Frobenius acts as the `card`-power on roots of unity not in `𝔓`) along the embedding `𝓞 L → L`; rewrites the residue-field cardinality as `q = N𝔭` via `Ideal.absNorm_apply`/`Submodule.cardQuot_apply` and `Ideal.LiesOver.over`. The side condition `(m : 𝓞 L) ∉ 𝔓` is proved by contradiction using `Ideal.absNorm_dvd_absNorm_of_le`, `Ideal.absNorm_span_singleton`, `Algebra.norm_algebraMap` and coprimality of `N𝔓` with `m` (`Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver`).
- **Hypotheses**: `K ⊆ L` Galois cyclotomic of conductor `m` (`NeZero m`); `𝔭` a nonzero prime of `K` unramified in `L`; `N𝔭` coprime to `m`; `𝔓` a prime of `L` lying over `𝔭`.
- **Uses from project**: `UnramifiedIn.finite_quotient`, `arithFrobAt`, `UnramifiedIn.ne_bot`, `IsArithFrobAt.arithFrobAt`, `IsArithFrobAt.apply_of_pow_eq_one`.
- **Used by**: `autToPow_frobeniusClass_out`.
- **Visibility**: public.
- **Lines**: 52–88 (proof ~29 lines).
- **Notes**: long (30–50).

---

### `private theorem pow_natModEq_of_pow_eq`
- **Type**: `{S : Type*} [CommRing S] [IsDomain S] {μ : S} {n : ℕ} [NeZero n] (hμ : IsPrimitiveRoot μ n) {a b : ℕ} (h : μ ^ a = μ ^ b) → a ≡ b [MOD n]`
- **What**: Equal powers of a primitive `n`-th root of unity force the exponents to be congruent mod `n` (the easy direction of the power-equality criterion).
- **How**: Rewrites `n = orderOf μ` (`IsPrimitiveRoot.eq_orderOf`) and applies `IsOfFinOrder.pow_eq_pow_iff_modEq`.
- **Hypotheses**: `S` an integral domain; `μ` a primitive `n`-th root of unity with `n ≠ 0`; `μ^a = μ^b`.
- **Uses from project**: `[]`.
- **Used by**: `autToPow_frobeniusClass_out`.
- **Visibility**: private.
- **Lines**: 92–94 (proof ~2 lines).
- **Notes**: none.

---

### `theorem autToPow_frobeniusClass_out`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime m) → hζ.autToPow K ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) = ZMod.unitOfCoprime (Ideal.absNorm 𝔭) hcop`
- **What**: The multiplicative form of the cyclotomic Frobenius law: the cyclotomic character `IsPrimitiveRoot.autToPow : Gal(L/K) →* (ℤ/m)ˣ` sends the Frobenius class representative `(frobeniusClass K L 𝔭).out` to the norm residue `N𝔭 mod m`.
- **How**: Picks a prime `𝔓 ∣ 𝔭` (`exists_prime_liesOver`), shows `frobeniusClass K L 𝔭 = ConjClasses.mk φ` for `φ = arithFrobAt …` (`frobeniusClass_eq_mk_of_isArithFrobAt`), so `.out` is conjugate to `φ`; transports the character value across the conjugacy via `(autToPow).map_isConj` + `isConj_iff_eq`. Then `autToPow_spec` plus the element-level law `cyclotomic_frobenius_acts_as_norm_power` give `ζ^{(autToPow φ).val} = ζ^{N𝔭}`, and `pow_natModEq_of_pow_eq` upgrades this to equality of units in `(ZMod m)ˣ` via `ZMod.natCast_eq_natCast_iff` + `Units.ext`.
- **Hypotheses**: `K ⊆ L` Galois cyclotomic of conductor `m`; `ζ` a primitive `m`-th root of unity; `𝔭` a prime of `K` unramified in `L` with `N𝔭` coprime to `m`.
- **Uses from project**: `exists_prime_liesOver`, `UnramifiedIn.ne_bot`, `UnramifiedIn.finite_quotient`, `arithFrobAt`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `IsArithFrobAt.arithFrobAt`, `cyclotomic_frobenius_acts_as_norm_power`, `pow_natModEq_of_pow_eq`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 100–125 (proof ~19 lines).
- **Notes**: none.

---

### `private theorem smul_algebraMap_eq`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (F : IntermediateField K L) [IsGalois K F] (σ : L ≃ₐ[K] L) (y : 𝓞 F) → σ • (algebraMap (𝓞 F) (𝓞 L) y) = algebraMap (𝓞 F) (𝓞 L) ((σ.restrictNormal F) • y)` (under a local `IsScalarTower K F L`).
- **What**: The integer-ring embedding `𝓞 F → 𝓞 L` intertwines the `Gal(L/K)`-action of `σ` with the `Gal(F/K)`-action of its normal restriction `σ ↾ F`.
- **How**: Checks the identity after the injective embedding `𝓞 L → L` (`RingOfIntegers.ext_iff`): two `smul`/coe bridge lemmas (`smul_distrib_smul`) reduce both sides to scalar `K`-algebra actions on `L`, where `AlgEquiv.restrictNormal_commutes` closes the goal; coe-through-tower handled by `IsScalarTower.algebraMap_apply` and `RingOfIntegers.coe_eq_algebraMap`.
- **Hypotheses**: `F` an intermediate field of `L/K`, Galois over `K`; `σ ∈ Gal(L/K)`; `y ∈ 𝓞 F`.
- **Uses from project**: `[]`.
- **Used by**: `isArithFrobAt_restrictNormal`.
- **Visibility**: private.
- **Lines**: 142–163 (proof ~22 lines, opened with `open scoped Pointwise`).
- **Notes**: none.

---

### `private theorem isArithFrobAt_restrictNormal`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (F : IntermediateField K L) [IsGalois K F] (σ : L ≃ₐ[K] L) (𝔓 : Ideal (𝓞 L)) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) → IsArithFrobAt (𝓞 K) (σ.restrictNormal F) (𝔓.under (𝓞 F))` (under a local `IsScalarTower K F L`).
- **What**: Downward Frobenius restriction: if `σ` is an arithmetic Frobenius at a prime `𝔓` of `L`, its normal restriction `σ ↾ F` is an arithmetic Frobenius at the contracted prime `𝔮 = 𝔓 ∩ 𝓞 F`.
- **How**: Unfolds `IsArithFrobAt` membership at `𝔮 = 𝔓.under (𝓞 F)`, rewrites `Ideal.under_under 𝔓` so the congruence is read modulo `𝔓`, and pushes the `F`-action into the `L`-action via `smul_algebraMap_eq`; then invokes `hσ` at `algebraMap (𝓞 F) (𝓞 L) y`.
- **Hypotheses**: `F` intermediate, Galois over `K`; `σ` an arithmetic Frobenius at `𝔓`.
- **Uses from project**: `smul_algebraMap_eq`.
- **Used by**: `frobeniusClass_fixedField_eq_one`.
- **Visibility**: private.
- **Lines**: 170–181 (proof ~6 lines).
- **Notes**: none.

---

### `private theorem unramifiedIn_intermediateField`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (F : IntermediateField K L) [IsGalois K F] (𝔭 : Ideal (𝓞 K)) (hunr : UnramifiedIn K L 𝔭) → UnramifiedIn K (↥F) 𝔭`
- **What**: A prime of `K` unramified in `L` is also unramified in any intermediate field `F` Galois over `K`.
- **How**: Given a prime `𝔮 ∣ 𝔭` of `F`, picks `𝔓 ∣ 𝔮` of `L` (`exists_prime_liesOver`, with non-bot via `Ideal.ne_bot_of_liesOver_of_ne_bot`), establishes `𝔓 ∣ 𝔭` by `Ideal.under_under`, gets `Algebra.IsUnramifiedAt (𝓞 K) 𝔓` from `hunr.2`, and descends to `𝔮` via `Algebra.IsUnramifiedAt.of_liesOver`.
- **Hypotheses**: `F` intermediate, Galois over `K`; `𝔭` unramified in `L`.
- **Uses from project**: `UnramifiedIn` (`.1`/`.2` projections), `exists_prime_liesOver`.
- **Used by**: `frobeniusClass_fixedField_eq_one`, `finrank_residue_fixedField_eq_one`, `card_primesOver_fixedField_eq_finrank`.
- **Visibility**: private.
- **Lines**: 186–203 (proof ~11 lines).
- **Notes**: long (30–50)? No — proof ~11 lines; flag `none`.

---

### `private theorem frobeniusClass_fixedField_eq_one`
- **Type**: `(K L : Type*) [Field K] … [IsGalois K L] [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K)) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) → frobeniusClass K (↥(IntermediateField.fixedField H)) 𝔭 = ConjClasses.mk 1` (under instances making `fixedField H` Galois over `K`).
- **What**: Step (A), the splitting input: in the abelian case, if the Frobenius representative of an unramified prime `𝔭` lies in `H`, then `𝔭`'s Frobenius class in the fixed field `F = fixedField H` is trivial (`𝔭` splits completely in `F`).
- **How**: With `Gal(L/K)` abelian, conjugate elements are equal (`mul_comm'` + `mul_right_cancel`), so the genuine Frobenius `σ = arithFrobAt 𝔓` equals `(frobeniusClass 𝔭).out`, which lies in `H = fixingSubgroup F` (`IntermediateField.fixingSubgroup_fixedField`). Hence `σ ↾ F = 1` (`IntermediateField.restrictNormalHom_ker`), and by `isArithFrobAt_restrictNormal` it is the `F`-Frobenius at `𝔮 = 𝔓 ∩ 𝓞 F`; `frobeniusClass_eq_mk_of_isArithFrobAt` then identifies the class with `mk (σ↾F) = mk 1`.
- **Hypotheses**: `Gal(L/K)` abelian; `H` a subgroup (abelian ⇒ normal); `𝔭` prime, unramified in `L`, with `(frobeniusClass 𝔭).out ∈ H`.
- **Uses from project**: `IsGalois.of_fixedField_normal_subgroup`, `NumberField.of_intermediateField`, `exists_prime_liesOver`, `UnramifiedIn.ne_bot`, `UnramifiedIn.finite_quotient`, `arithFrobAt`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `IsArithFrobAt.arithFrobAt`, `isArithFrobAt_restrictNormal`, `unramifiedIn_intermediateField`.
- **Used by**: `finrank_residue_fixedField_eq_one`.
- **Visibility**: private.
- **Lines**: 213–250 (proof ~30 lines).
- **Notes**: long (30–50).

---

### `private theorem finrank_residue_fixedField_eq_one`
- **Type**: `(K L : Type*) [Field K] … [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K)) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hmem : ((frobeniusClass K L 𝔭).out …) ∈ H) → ∀ 𝔮 : Ideal (𝓞 ↥(fixedField H)), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 → Module.finrank (𝓞 K ⧸ 𝔮.under (𝓞 K)) (𝓞 ↥(fixedField H) ⧸ 𝔮) = 1`
- **What**: Step (A) residue-degree form: under the same hypotheses, every prime `𝔮 ∣ 𝔭` of the fixed field `F` has residue degree `[κ(𝔮) : κ(𝔭)] = 1`.
- **How**: The `F`-Frobenius class of `𝔭` is trivial (`frobeniusClass_fixedField_eq_one`), so the residue degree equals `orderOf (1 : Gal(F/K)) = 1` via `finrank_residue_eq_orderOf` + `orderOf_one`.
- **Hypotheses**: same as `frobeniusClass_fixedField_eq_one`.
- **Uses from project**: `IsGalois.of_fixedField_normal_subgroup`, `NumberField.of_intermediateField`, `unramifiedIn_intermediateField`, `frobeniusClass_fixedField_eq_one`, `finrank_residue_eq_orderOf`.
- **Used by**: `card_primesOver_fixedField_eq_finrank`, `absNorm_eq_of_liesOver_fixedField`.
- **Visibility**: private.
- **Lines**: 257–278 (proof ~11 lines).
- **Notes**: none.

---

### `private theorem card_primesOver_fixedField_eq_finrank`
- **Type**: `(K L : Type*) [Field K] … [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K)) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hmem : … ∈ H) → Nat.card {𝔮 : Ideal (𝓞 ↥(fixedField H)) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥} = Module.finrank K ↥(fixedField H)`
- **What**: Step (A) count form: under the same hypotheses there are exactly `[F : K]` primes of `𝓞 F` above `𝔭`.
- **How**: From the general count×degree identity `card_primesAbove_mul_finrank_eq` with residue degree `1` (`finrank_residue_fixedField_eq_one`, `mul_one`), and `IsGalois.card_aut_eq_finrank` to turn `Nat.card (aut)` into `finrank`.
- **Hypotheses**: same as `frobeniusClass_fixedField_eq_one`.
- **Uses from project**: `IsGalois.of_fixedField_normal_subgroup`, `NumberField.of_intermediateField`, `unramifiedIn_intermediateField`, `finrank_residue_fixedField_eq_one`, `exists_prime_liesOver`, `UnramifiedIn.ne_bot`, `card_primesAbove_mul_finrank_eq`.
- **Used by**: `finrank_mul_unramified_coprime_le_univ`.
- **Visibility**: private.
- **Lines**: 284–302 (proof ~11 lines).
- **Notes**: none.

---

### `private theorem absNorm_eq_of_liesOver_fixedField`
- **Type**: `(K L : Type*) [Field K] … [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K)) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hmem : … ∈ H) → ∀ 𝔮 : Ideal (𝓞 ↥(fixedField H)), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 → Ideal.absNorm 𝔮 = Ideal.absNorm 𝔭`
- **What**: Step (A) norm form: under the same hypotheses every prime `𝔮 ∣ 𝔭` of `F` has the same absolute norm as `𝔭` (`N𝔮 = N𝔭`).
- **How**: Residue/inertia degree `f(𝔮∣𝔭) = 1` (from `finrank_residue_fixedField_eq_one` via `Ideal.inertiaDeg_algebraMap`) feeds `Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver` with `pow_one`; `𝔮.under (𝓞 K) = 𝔭` by `LiesOver.over`.
- **Hypotheses**: same as `frobeniusClass_fixedField_eq_one`.
- **Uses from project**: `IsGalois.of_fixedField_normal_subgroup`, `NumberField.of_intermediateField`, `finrank_residue_fixedField_eq_one`, `UnramifiedIn.ne_bot`.
- **Used by**: `finrank_mul_unramified_coprime_le_univ`.
- **Visibility**: private.
- **Lines**: 308–331 (proof ~13 lines).
- **Notes**: none.

---

### `private theorem primeIdealZetaSum_unramified_coprime_div_log_tendsto_one`
- **Type** (section vars `K L m`): `→ Filter.Tendsto (fun s : ℝ ↦ primeIdealZetaSum {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m} s / Real.log (1 / (s - 1))) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1)`
- **What**: The coprime-norm unramified prime zeta sum is asymptotic to `log(1/(s-1))` as `s → 1⁺`: dividing it by `log(1/(s-1))` tends to `1`.
- **How**: Splits all nonzero primes into the good set `Uc` and the complementary "bad" set `D` (ramified or non-coprime-norm), which is finite (`finite_ramifiedIn ∪ finite_badPrimes`). The `D`-sum is bounded (`primeIdealZetaSum_le_card_of_finite`), so its ratio → 0 (`squeeze_zero_norm'` against `tendsto_log_one_div_sub_one_atTop` + `Tendsto.div_atTop`); subtracting from the universal asymptotic `primeIdealZetaSum_univ_tendsto_log` and re-congruing via `primeIdealZetaSum_union_of_disjoint` / `primeIdealZetaSum_eq_univ_of_forall_prime_mem` gives `1`.
- **Hypotheses**: `K ⊆ L` Galois number fields; `m ≠ 0`.
- **Uses from project**: `primeIdealZetaSum`, `finite_ramifiedIn`, `finite_badPrimes`, `primeIdealZetaSum_le_card_of_finite`, `primeIdealZetaSum_def`, `tendsto_log_one_div_sub_one_atTop`, `primeIdealZetaSum_univ_tendsto_log`, `primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_eq_univ_of_forall_prime_mem`.
- **Used by**: `finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime`.
- **Visibility**: private.
- **Lines**: 353–402 (proof ~49 lines).
- **Notes**: long (30–50) — ~49 lines, near the 50-line threshold.

---

### `private theorem finite_primesLiesOver_ne_bot`
- **Type** (section vars `K L`, `omit [IsGalois K L] [NeZero m]`): `(F : IntermediateField K L) [IsGalois K F] (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal] → Finite {𝔮 : Ideal (𝓞 ↥F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥}`
- **What**: For `F/K` an intermediate Galois extension and `𝔭` maximal, the nonzero primes of `𝓞 F` lying over `𝔭` form a finite type.
- **How**: They inject into the finite set `𝔭.primesOver (𝓞 F)` (`IsDedekindDomain.primesOver_finite`), via `Finite.of_injective`.
- **Hypotheses**: `F` intermediate, Galois over `K`; `𝔭` maximal.
- **Uses from project**: `[]`.
- **Used by**: `primeIdealZetaSum_under_eq_finrank_mul`.
- **Visibility**: private.
- **Lines**: 407–416 (proof ~7 lines).
- **Notes**: none.

---

### `private theorem primeIdealZetaSum_under_eq_finrank_mul`
- **Type** (section vars `K L m`, `omit [NeZero m]`): `[IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K)) (hsplit : ∀ 𝔭, 𝔭.IsPrime → UnramifiedIn K L 𝔭 → (N𝔭).Coprime m → (Nat.card {primes 𝔮∣𝔭 of F} = [F:K] ∧ ∀ 𝔮∣𝔭, N𝔮 = N𝔭)) {s : ℝ} (hs : 1 < s) → primeIdealZetaSum {𝔮 of F | 𝔮.IsPrime ∧ UnramifiedIn K L (𝔮.under (𝓞 K)) ∧ (N(𝔮.under))·Coprime m} s = (finrank K F : ℝ) * primeIdealZetaSum {𝔭 of K | coprime unram} s`
- **What**: Regrouping/Fubini step: the `F`-prime zeta sum over primes whose contraction to `𝓞 K` is coprime-norm-unramified equals `[F:K] · Σ_{coprime unram 𝔭 of K} N𝔭^{-s}`.
- **How**: Fibres `IV` (good `F`-primes) over `IU` (good `K`-primes) by `𝔮 ↦ 𝔮 ∩ 𝓞 K` using `Equiv.sigmaFiberEquiv`; rewrites the `tsum` as a sigma sum (`Summable.tsum_sigma` with summability transported through the equiv from `summable_prime_absNorm_rpow`) and factors the constant (`tsum_mul_left`). Each fibre is identified with `{primes 𝔮∣𝔭}` (an explicit `Equiv` `hfibeq`), shown finite via `finite_primesLiesOver_ne_bot`; the integrand is constant `N𝔭^{-s}` on the fibre (`hsplit … .2`, the norm-equality), so `tsum_const` + `Nat.card_congr` + `hsplit … .1` (the count `= [F:K]`) yields the factor.
- **Hypotheses**: `Gal(L/K)` abelian; `H` a subgroup; per-coprime-prime split data `hsplit` (count `= [F:K]` and fibre norm-equality); `1 < s`.
- **Uses from project**: `IsGalois.of_fixedField_normal_subgroup`, `NumberField.of_intermediateField`, `primeIdealZetaSum_def`, `summable_prime_absNorm_rpow`, `finite_primesLiesOver_ne_bot`.
- **Used by**: `finrank_mul_unramified_coprime_le_univ`.
- **Visibility**: private.
- **Lines**: 422–481 (proof ~50 lines).
- **Notes**: OVER-50 — needs further /decompose-proof pass. (Body is ~50 lines, 437–481; at/over the threshold — flag for decomposition.)

---

### `private theorem finrank_mul_unramified_coprime_le_univ`
- **Type** (section vars `K L m`, `omit [NeZero m]`): `[IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K)) (hH : ∀ 𝔭, 𝔭.IsPrime → 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 → (N𝔭).Coprime m → ((frobeniusClass K L 𝔭).out …) ∈ H) {s : ℝ} (hs : 1 < s) → (finrank K F : ℝ) * primeIdealZetaSum {coprime unram 𝔭 of K} s ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(fixedField H)))) s`
- **What**: Coprime-restricted fibred zeta comparison: `[F:K] · Σ_{coprime unram 𝔭} N𝔭^{-s} ≤ Σ_{all 𝔮 of F} N𝔮^{-s}`.
- **How**: Builds the `hsplit` data (count via `card_primesOver_fixedField_eq_finrank`, norm via `absNorm_eq_of_liesOver_fixedField`, each fed the `hH` membership through `UnramifiedIn.ne_bot`), rewrites the LHS via `primeIdealZetaSum_under_eq_finrank_mul`, then bounds by the full universal sum with `primeIdealZetaSum_le_of_subset (Set.subset_univ _)`.
- **Hypotheses**: `Gal(L/K)` abelian; `H` containing the Frobenius rep of every nonzero coprime-norm unramified prime; `1 < s`.
- **Uses from project**: `IsGalois.of_fixedField_normal_subgroup`, `NumberField.of_intermediateField`, `card_primesOver_fixedField_eq_finrank`, `absNorm_eq_of_liesOver_fixedField`, `UnramifiedIn.ne_bot`, `primeIdealZetaSum_under_eq_finrank_mul`, `primeIdealZetaSum_le_of_subset`.
- **Used by**: `finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime`.
- **Visibility**: private.
- **Lines**: 490–511 (proof ~12 lines).
- **Notes**: none.

---

### `private theorem finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime`
- **Type** (section vars `K L m`): `[IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K)) (hH : ∀ 𝔭, 𝔭.IsPrime → 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 → (N𝔭).Coprime m → ((frobeniusClass K L 𝔭).out …) ∈ H) → Module.finrank K (IntermediateField.fixedField H) ≤ 1`
- **What**: Coprime-restricted bound on the fixed-field degree: under the coprime Frobenius-membership hypothesis, `[F:K] ≤ 1`.
- **How**: Both ratios `A s / log(1/(s-1))` (coprime `K`-side, `primeIdealZetaSum_unramified_coprime_div_log_tendsto_one`) and `B s / log` (universal `F`-side, `primeIdealZetaSum_univ_tendsto_log`) tend to `1`; the comparison `finrank_mul_unramified_coprime_le_univ` gives `d · (A/log) ≤ B/log` eventually (using `hLpos`), and `le_of_tendsto_of_tendsto` passes to the limit to force `d ≤ 1`.
- **Hypotheses**: `Gal(L/K)` abelian; `H` containing the Frobenius rep of every nonzero coprime-norm unramified prime.
- **Uses from project**: `IsGalois.of_fixedField_normal_subgroup`, `NumberField.of_intermediateField`, `primeIdealZetaSum`, `primeIdealZetaSum_unramified_coprime_div_log_tendsto_one`, `primeIdealZetaSum_univ_tendsto_log`, `tendsto_log_one_div_sub_one_atTop`, `finrank_mul_unramified_coprime_le_univ`.
- **Used by**: `subgroup_eq_top_of_forall_frobenius_mem_of_coprime`.
- **Visibility**: private.
- **Lines**: 518–547 (proof ~30 lines).
- **Notes**: long (30–50).

---

### `theorem subgroup_eq_top_of_forall_frobenius_mem_of_coprime`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m] (H : Subgroup Gal(L/K)) (hH : ∀ 𝔭, 𝔭.IsPrime → 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 → (Ideal.absNorm 𝔭).Coprime m → ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) → H = ⊤`
- **What**: Coprime-restricted "Frobenii generate": a subgroup containing the Frobenius representative of every nonzero unramified prime of coprime norm is the whole `Gal(L/K)` (abelian case).
- **How**: Reduces `H = ⊤` to a cardinality equality (`Subgroup.card_eq_iff_eq_top`); `finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime` + `Module.finrank_pos` give `[F:K] = 1`, then the tower `Module.finrank_mul_finrank` with `IsGalois.card_aut_eq_finrank` and `IntermediateField.finrank_fixedField_eq_card` finish.
- **Hypotheses**: `Gal(L/K)` abelian; `m ≠ 0`; `H` containing the Frobenius rep of every nonzero coprime-norm unramified prime.
- **Uses from project**: `frobeniusClass`, `UnramifiedIn`, `finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime`.
- **Used by**: `subgroup_eq_top_of_forall_frobenius_mem`.
- **Visibility**: public.
- **Lines**: 560–572 (proof ~7 lines).
- **Notes**: none.

---

### `theorem subgroup_eq_top_of_forall_frobenius_mem`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K)) (hH : ∀ 𝔭, 𝔭.IsPrime → 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 → ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) → H = ⊤`
- **What**: Frobenii generate the Galois group (CFT-free, abelian case): a subgroup containing the Frobenius representative of every nonzero unramified prime of `K` is all of `Gal(L/K)`.
- **How**: Specializes `subgroup_eq_top_of_forall_frobenius_mem_of_coprime` at `m = 1` (every norm is coprime to `1`, so the coprimality side-condition is vacuous).
- **Hypotheses**: `Gal(L/K)` abelian; `H` containing the Frobenius rep of every nonzero unramified prime. (Docstring notes the `[IsMulCommutative]` hypothesis was an authorized statement change — the `.out`-only membership only suffices when conjugacy classes are singletons.)
- **Uses from project**: `frobeniusClass`, `UnramifiedIn`, `subgroup_eq_top_of_forall_frobenius_mem_of_coprime`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 592–599 (proof ~2 lines).
- **Notes**: none.

---

## File Summary

**Total declarations: 14** — defs: 0 · lemmas/theorems: 14 · instances: 0.
(0 structures / classes / abbrevs / inductives.)

**Public (5):** `cyclotomic_frobenius_acts_as_norm_power`, `autToPow_frobeniusClass_out`,
`subgroup_eq_top_of_forall_frobenius_mem_of_coprime`, `subgroup_eq_top_of_forall_frobenius_mem`.
(Plus `pow_natModEq_of_pow_eq` private but reused.)
**Private (9):** `pow_natModEq_of_pow_eq`, `smul_algebraMap_eq`, `isArithFrobAt_restrictNormal`,
`unramifiedIn_intermediateField`, `frobeniusClass_fixedField_eq_one`,
`finrank_residue_fixedField_eq_one`, `card_primesOver_fixedField_eq_finrank`,
`absNorm_eq_of_liesOver_fixedField`, `primeIdealZetaSum_unramified_coprime_div_log_tendsto_one`,
`finite_primesLiesOver_ne_bot`, `primeIdealZetaSum_under_eq_finrank_mul`,
`finrank_mul_unramified_coprime_le_univ`,
`finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime`.

**Key API (used by ≥3 in-file):**
- `unramifiedIn_intermediateField` — used by `frobeniusClass_fixedField_eq_one`,
  `finrank_residue_fixedField_eq_one`, `card_primesOver_fixedField_eq_finrank` (3).
- `finrank_residue_fixedField_eq_one` — used by `card_primesOver_fixedField_eq_finrank`,
  `absNorm_eq_of_liesOver_fixedField` (2 in-file; pivotal Step (A) hub, just under the threshold).
- (No other in-file decl reaches 3 internal consumers; the file is a mostly-linear chain feeding
  the two `subgroup_eq_top_*` exits.)

**Unused decls (in this file):** `autToPow_frobeniusClass_out`,
`subgroup_eq_top_of_forall_frobenius_mem` (and `cyclotomic_frobenius_acts_as_norm_power` is used
only internally). These are the file's externally-consumed exits — per the module docstring they
are consumed by `ZetaProduct.lean` (the κ-uniformity transfer) — so "unused in file" ≠ dead.

**Decls with `sorry`:** none.

**Decls with `set_option`:** none. (Non-default attributes/scopes seen: module-level `@[expose]
public section` + `noncomputable section`; `open scoped Pointwise in` on `smul_algebraMap_eq`;
`omit […]` modifiers on `finite_primesLiesOver_ne_bot`, `primeIdealZetaSum_under_eq_finrank_mul`,
`finrank_mul_unramified_coprime_le_univ`.)

**Proofs >50 lines (decompose-needed):**
- `primeIdealZetaSum_under_eq_finrank_mul` — body lines 437–481, **~50 lines** (sigma-fibration +
  fibre-equiv + constancy argument). Flagged OVER-50; candidate for `/decompose-proof` (e.g. extract
  the fibre `Equiv` `hfibeq` and the summability/constancy facts).

**Proofs 30–50 lines (watch):**
- `primeIdealZetaSum_unramified_coprime_div_log_tendsto_one` — ~49 lines (353–402).
- `frobeniusClass_fixedField_eq_one` — ~30 lines (213–250).
- `finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime` — ~30 lines (518–547).
- `cyclotomic_frobenius_acts_as_norm_power` — ~29 lines (52–88), just under.
- `smul_algebraMap_eq` — ~22 lines (142–163).
