# Inventory: PadicLFunctions/IwasawaProof/GaloisAction.lean

File context: RJW §12.1 (TeX 3182–3243) — E12.1. Constructs the Galois action `σ_a = galAut p a n` of `𝒢 = ℤ_[p]ˣ` (via the cyclotomic character) on the cyclotomic tower `K_n` and the norm-compatible unit tower `𝒰_∞ = NormCompatUnits p`, proves reality of `K_n⁺` (fixed field of complex conjugation), norm-/isometry-/`O_n`-equivariance, the substitution-evaluation bridge, and `𝒢`-equivariance of the Coleman map. Namespace `PadicLFunctions.Coleman`, `variable (p : ℕ) [hp : Fact p.Prime]`.

---

### instance instNeZeroPpow
- Type: `instance instNeZeroPpow (n : ℕ) : NeZero (p ^ n)`
- What: Provides the `NeZero (p ^ n)` instance (positivity of `p^n`) needed by cyclotomic-extension machinery.
- How: Wraps `(pow_pos hp.out.pos n).ne'` in the `NeZero` constructor.
- Hypotheses: `p` prime (via `hp`); `n : ℕ`.
- Uses from project: []
- Used by: `isGalois_K` (re-derives it locally though), unused as an explicit instance elsewhere in file (instances resolve implicitly).
- Visibility: public
- Lines: 38–39 (proof ~1 line term)
- Notes: none

### def galAut
- Type: `def galAut (a : ℤ_[p]ˣ) (n : ℕ) : (K p n) ≃ₐ[ℚ_[p]] (K p n)`
- What: The automorphism `σ_a` of `K_n` sending the fixed root `ξ_n ↦ ξ_n^{a mod p^n}`; for `n ≥ 1` it is `(autEquivPow K_n …).symm` of the residue `a mod p^n`, and for `n = 0` it is `AlgEquiv.refl`.
- How: `if 1 ≤ n` branch uses `IsCyclotomicExtension.autEquivPow (K p n) (cyclotomic_irreducible_Qp p hn)` and `PadicMeasure.unitsToZModPow p n a`; else `AlgEquiv.refl`.
- Hypotheses: `a : ℤ_[p]ˣ`, `n : ℕ`; the irreducibility input requires `1 ≤ n`.
- Uses from project: `K`, `cyclotomic_irreducible_Qp`, `PadicMeasure.unitsToZModPow`
- Used by: nearly every theorem in the file (galAut_zetaSys, galAut_neg_one_zetaSys, orderOf_galAut_neg_one, galAut_compat, levelNorm_galAut, norm_galAut, galAut_mem_O, galAutUnit, galAut_evalPi, …)
- Visibility: public
- Lines: 45–49 (proof/body ~5 lines)
- Notes: none

### theorem zetaSys_pow_eq_pow_of_modEq
- Type: `theorem zetaSys_pow_eq_pow_of_modEq {n i j : ℕ} (h : i ≡ j [MOD p ^ n]) : zetaSys p n ^ i = zetaSys p n ^ j`
- What: `ξ_n^i = ξ_n^j` whenever `i ≡ j (mod p^n)`, since the root has order `p^n`; the engine for tower-compatibility exponent reductions.
- How: Lifts `zetaSys p n` to a unit `ζu : ℂ_[p]ˣ`, transports primitivity, then `pow_eq_pow_iff_modEq` with `hζuprim.eq_orderOf`; pushes back through `Units.val_pow_eq_pow_val`.
- Hypotheses: `i ≡ j [MOD p^n]`.
- Uses from project: `zetaSys`, `zetaSys_primitiveRoot`
- Used by: `galAut_neg_one_zetaSys`, `galAut_compat`, `zpPow_zetaSys`
- Visibility: public
- Lines: 53–62 (proof ~9 lines)
- Notes: none

### theorem zetaSysK_primitiveRoot
- Type: `theorem zetaSysK_primitiveRoot (n : ℕ) : IsPrimitiveRoot (⟨zetaSys p n, zetaSys_mem_K p n⟩ : K p n) (p ^ n)`
- What: The fixed root `ξ_n` is a primitive `p^n`-th root of unity inside the subtype `K_n` (transported from `ℂ_[p]` along the injective hom `K_n ↪ ℂ_[p]`).
- How: `IsPrimitiveRoot.coe_submonoidClass_iff` reduces to the `ℂ_[p]`-statement `zetaSys_primitiveRoot p n`.
- Hypotheses: `n : ℕ`.
- Uses from project: `zetaSys`, `zetaSys_mem_K`, `K`, `zetaSys_primitiveRoot`
- Used by: `autToPow_zetaSys_eq`, `galAut_zetaSys`, `isIntegral_zetaSysK`
- Visibility: public
- Lines: 66–69 (proof ~2 lines)
- Notes: none

### theorem autToPow_zetaSys_eq
- Type: `theorem autToPow_zetaSys_eq {n : ℕ} (f : (K p n) ≃ₐ[ℚ_[p]] (K p n)) : (zetaSysK_primitiveRoot p n).autToPow ℚ_[p] f = (zeta_spec (p ^ n) ℚ_[p] (K p n)).autToPow ℚ_[p] f`
- What: The autToPow root-independence bridge (T1201a): the cyclotomic-character value `autToPow` of `f` computed via the project root `ξ_n` agrees with the one computed via mathlib's chosen root `ζ` (used by `autEquivPow`).
- How: Both roots are primitive, so `ζ = ξ_n^c` with `c` coprime to `p^n` (`eq_pow_of_pow_eq_one`, `pow_iff_coprime`); the two character values `m, m'` satisfy `ξ_n^{c·m} = f ζ = ξ_n^{c·m'}`, giving `c·m ≡ c·m' (mod p^n)`; cancel the unit `c` (`IsUnit.mul_left_cancel`) via `autToPow_spec`. Hinges on `IsPrimitiveRoot.autToPow_spec` and `pow_eq_pow_iff_modEq`.
- Hypotheses: `f` a `ℚ_p`-automorphism of `K_n`.
- Uses from project: `K`, `zetaSysK_primitiveRoot`, `zetaSys`, `zetaSys_mem_K`, `zetaSys_primitiveRoot`
- Used by: `galAut_zetaSys`
- Visibility: public
- Lines: 78–115 (proof ~37 lines)
- Notes: long(30-50)

### theorem galAut_zetaSys
- Type: `theorem galAut_zetaSys (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) : (galAut p a n ⟨zetaSys p n, zetaSys_mem_K p n⟩ : ℂ_[p]) = zetaSys p n ^ ((unitsToZModPow p n a : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)).val`
- What: The defining cyclotomic-character property `σ_a(ξ_n) = ξ_n^{(a mod p^n)}`.
- How: `galAut` is `autEquivPow.symm` of the residue `t`, so `autEquivPow (galAut …) = t`; through the bridge `autToPow_zetaSys_eq` and `autToPow_spec` the value is `t`, then coerce to `ℂ_[p]`. Hinges on `IsPrimitiveRoot.autToPow_spec` and `autEquivPow_apply`.
- Hypotheses: `1 ≤ n`.
- Uses from project: `galAut`, `zetaSys`, `zetaSys_mem_K`, `PadicMeasure.unitsToZModPow`, `cyclotomic_irreducible_Qp`, `zetaSysK_primitiveRoot`, `autToPow_zetaSys_eq`
- Used by: `galAut_neg_one_zetaSys`, `galAut_compat`, `galAut_evalPi`
- Visibility: public
- Lines: 121–138 (proof ~14 lines)
- Notes: none

### theorem galAut_neg_one_zetaSys
- Type: `theorem galAut_neg_one_zetaSys {n : ℕ} (hn : 1 ≤ n) : (galAut p (-1) n ⟨zetaSys p n, zetaSys_mem_K p n⟩ : ℂ_[p]) = (zetaSys p n)⁻¹`
- What: Complex conjugation `σ_{-1}` sends `ξ_n ↦ ξ_n⁻¹` (character value `-1`).
- How: `galAut_zetaSys` with `unitsToZModPow (-1) = -1`; then `ξ^{(-1).val} = ξ⁻¹` via `eq_inv_of_mul_eq_one_left` and `zetaSys_pow_eq_pow_of_modEq` with exponent `(-1).val + 1 ≡ 0 (mod p^n)`.
- Hypotheses: `1 ≤ n`.
- Uses from project: `galAut`, `zetaSys`, `zetaSys_mem_K`, `galAut_zetaSys`, `PadicMeasure.unitsToZModPow_coe`, `zetaSys_pow_eq_pow_of_modEq`
- Used by: `orderOf_galAut_neg_one`, `galAut_neg_one_fixes_KPlus`
- Visibility: public
- Lines: 142–153 (proof ~11 lines)
- Notes: none

### instance isGalois_K
- Type: `instance isGalois_K (n : ℕ) : IsGalois ℚ_[p] (K p n)`
- What: `K_n/ℚ_p` is a Galois extension (cyclotomic extension).
- How: `IsCyclotomicExtension.isGalois {p ^ n} ℚ_[p] (K p n)` after a local `NeZero (p^n)`.
- Hypotheses: `n : ℕ`.
- Uses from project: `K`
- Used by: unused in file (instance, resolved implicitly e.g. by fixedField/Galois-correspondence lemmas)
- Visibility: public
- Lines: 156–158 (proof ~2 lines)
- Notes: none

### instance finiteDimensional_K
- Type: `instance finiteDimensional_K (n : ℕ) : FiniteDimensional ℚ_[p] (K p n)`
- What: `K_n` is finite-dimensional over `ℚ_p` (degree `φ(p^n) > 0`).
- How: `Module.finite_of_finrank_pos` with `finrank_K` and `Nat.totient_pos`.
- Hypotheses: `n : ℕ`.
- Uses from project: `K`, `finrank_K`
- Used by: unused in file as explicit reference (instance; note several proofs re-derive the same `haveI` locally rather than relying on it).
- Visibility: public
- Lines: 161–163 (proof ~2 lines)
- Notes: none

### theorem zetaSys_ne_inv
- Type: `theorem zetaSys_ne_inv (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : zetaSys p n ≠ (zetaSys p n)⁻¹`
- What: For `p` odd and `n ≥ 1`, `ξ_n ≠ ξ_n⁻¹` (this is where `p ≠ 2` enters, giving order-2 conjugation).
- How: Else `ξ_n^2 = 1` so `p^n ∣ 2` (`dvd_of_pow_eq_one`); but `p ≥ 3` forces `p^n ≥ 3 > 2`, contradiction via `omega`/`Nat.le_of_dvd`.
- Hypotheses: `p ≠ 2`, `1 ≤ n`.
- Uses from project: `zetaSys`, `zetaSys_primitiveRoot`
- Used by: `orderOf_galAut_neg_one`
- Visibility: public
- Lines: 167–178 (proof ~11 lines)
- Notes: none

### theorem isIntegral_zetaSysK
- Type: `private theorem isIntegral_zetaSysK (n : ℕ) : IsIntegral ℚ_[p] (⟨zetaSys p n, zetaSys_mem_K p n⟩ : K p n)`
- What: `⟨ξ_n,_⟩` is integral over `ℚ_p` inside `K_n` (root of unity).
- How: Exhibits witness polynomial `X^{p^n} − C 1`, monic by `monic_X_pow_sub_C`, with root via `(zetaSysK_primitiveRoot p n).pow_eq_one`.
- Hypotheses: `n : ℕ`.
- Uses from project: `zetaSys`, `zetaSys_mem_K`, `K`, `zetaSysK_primitiveRoot`
- Used by: `adjoin_zetaSysK_eq_top`, `adjoinSimple_zetaSysK_eq_top`, `finrank_K_over_KPlusRestrict_le`
- Visibility: private
- Lines: 181–185 (proof ~3 lines term)
- Notes: none

### theorem adjoin_zetaSysK_eq_top
- Type: `private theorem adjoin_zetaSysK_eq_top (n : ℕ) : Algebra.adjoin ℚ_[p] {(⟨zetaSys p n, zetaSys_mem_K p n⟩ : K p n)} = ⊤`
- What: `K_n = ℚ_p(ξ_n)` as a subalgebra: the generator `ξ_n` adjoins to `⊤`.
- How: Reduces to the `IntermediateField.adjoin` being `⊤` via `adjoin_simple_toSubalgebra_of_isAlgebraic`; then `eq_top_iff` and a `map`-of-adjoin computation (`IntermediateField.adjoin_map`) showing every `y ∈ K_n` is hit.
- Hypotheses: `n : ℕ`.
- Uses from project: `zetaSys`, `zetaSys_mem_K`, `K`, `isIntegral_zetaSysK`
- Used by: `orderOf_galAut_neg_one`, `galAut_compat`
- Visibility: private
- Lines: 189–206 (proof ~17 lines)
- Notes: none

### theorem orderOf_galAut_neg_one
- Type: `theorem orderOf_galAut_neg_one (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : orderOf (galAut p (-1) n) = 2`
- What: `σ_{-1}` has order 2 (`p` odd, `n ≥ 1`): an involution that is non-trivial.
- How: `orderOf_eq_prime`: (i) `σ_{-1}^2 = id` via `AlgHom.ext_of_adjoin_eq_top (adjoin_zetaSysK_eq_top)` checking on `ξ_n` (`(ξ⁻¹)⁻¹ = ξ`, using `galAut_neg_one_zetaSys`, `inv_inv`); (ii) non-triviality from `zetaSys_ne_inv`. Hinges on `AlgHom.ext_of_adjoin_eq_top` and `galAut_neg_one_zetaSys`.
- Hypotheses: `p ≠ 2`, `1 ≤ n`.
- Uses from project: `galAut`, `zetaSys`, `zetaSys_mem_K`, `K`, `galAut_neg_one_zetaSys`, `adjoin_zetaSysK_eq_top`, `zetaSys_ne_inv`
- Used by: `finrank_fixedField_galAut_neg_one`
- Visibility: public
- Lines: 210–239 (proof ~29 lines)
- Notes: none

### abbrev KPlusRestrict
- Type: `noncomputable abbrev KPlusRestrict (n : ℕ) : IntermediateField ℚ_[p] (K p n)`
- What: Realises `K_n⁺` as an intermediate field of `K_n/ℚ_p` (it sits inside `K_n` by `KPlus_le_K`). Reducible so relative-algebra instances resolve.
- How: `IntermediateField.restrict (KPlus_le_K p n)`.
- Hypotheses: `n : ℕ`.
- Uses from project: `K`, `KPlus_le_K`
- Used by: `KPlusRestrict_le_fixedField`, `finrank_K_over_KPlusRestrict_le`, `KPlus_eq_fixedField`, `mem_KPlus_iff_galAut_neg_one_fixed`
- Visibility: public
- Lines: 243–244 (body 1 line)
- Notes: none

### theorem galAut_neg_one_fixes_KPlus
- Type: `theorem galAut_neg_one_fixes_KPlus {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]} (hx : x ∈ KPlus p n) (hxK : x ∈ K p n) : (galAut p (-1) n ⟨x, hxK⟩ : ℂ_[p]) = x`
- What: Reality of `K_n⁺`: complex conjugation `σ_{-1}` fixes every element of `K_n⁺ = ℚ_p(ξ+ξ⁻¹)` pointwise.
- How: `IntermediateField.adjoin_induction` over `KPlus = adjoin ℚ_p {ξ+ξ⁻¹}`: the generator `ξ+ξ⁻¹` is fixed (`galAut_neg_one_zetaSys` + `add_comm`), `algebraMap` elements via `AlgEquiv.commutes`, closure under `+,*,⁻¹`. Hinges on `IntermediateField.adjoin_induction` and `galAut_neg_one_zetaSys`.
- Hypotheses: `1 ≤ n`; `x ∈ KPlus p n` and `x ∈ K p n`.
- Uses from project: `galAut`, `KPlus`, `K`, `zetaSys`, `zetaSys_mem_K`, `galAut_neg_one_zetaSys`, `KPlus_le_K`
- Used by: `KPlusRestrict_le_fixedField`
- Visibility: public
- Lines: 250–301 (proof ~51 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem KPlusRestrict_le_fixedField
- Type: `theorem KPlusRestrict_le_fixedField {n : ℕ} (hn : 1 ≤ n) : KPlusRestrict p n ≤ IntermediateField.fixedField (Subgroup.zpowers (galAut p (-1) n))`
- What: `K_n⁺ ⊆ (K_n)^{⟨σ_{-1}⟩}`: every element of `K_n⁺` lies in the fixed field of complex conjugation (Galois reformulation of reality).
- How: `IntermediateField.le_iff_le` + `Subgroup.zpowers_le` + `mem_fixingSubgroup_iff`, reduced to `galAut_neg_one_fixes_KPlus`.
- Hypotheses: `1 ≤ n`.
- Uses from project: `KPlusRestrict`, `galAut`, `galAut_neg_one_fixes_KPlus`
- Used by: `KPlus_eq_fixedField`
- Visibility: public
- Lines: 306–312 (proof ~6 lines)
- Notes: none

### theorem finrank_fixedField_galAut_neg_one
- Type: `theorem finrank_fixedField_galAut_neg_one (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers (galAut p (-1) n))) (K p n) = 2`
- What: `[K_n : (K_n)^{⟨σ_{-1}⟩}] = 2` (fixed-field degree = subgroup order).
- How: `IntermediateField.finrank_fixedField_eq_card` + `Nat.card_zpowers` + `orderOf_galAut_neg_one`.
- Hypotheses: `p ≠ 2`, `1 ≤ n`.
- Uses from project: `galAut`, `K`, `orderOf_galAut_neg_one`
- Used by: `KPlus_eq_fixedField`
- Visibility: public
- Lines: 316–320 (proof ~2 lines)
- Notes: none

### theorem adjoinSimple_zetaSysK_eq_top
- Type: `private theorem adjoinSimple_zetaSysK_eq_top (n : ℕ) : IntermediateField.adjoin ℚ_[p] {(⟨zetaSys p n, zetaSys_mem_K p n⟩ : K p n)} = ⊤`
- What: `ℚ_p(ξ_n) = K_n` as an intermediate field (the IntermediateField recast of `adjoin_zetaSysK_eq_top`).
- How: `IntermediateField.toSubalgebra_injective` + `adjoin_simple_toSubalgebra_of_isAlgebraic` + `top_toSubalgebra` + `adjoin_zetaSysK_eq_top`.
- Hypotheses: `n : ℕ`.
- Uses from project: `zetaSys`, `zetaSys_mem_K`, `K`, `isIntegral_zetaSysK`, `adjoin_zetaSysK_eq_top`
- Used by: `finrank_K_over_KPlusRestrict_le`
- Visibility: private
- Lines: 324–329 (proof ~5 lines)
- Notes: none

### theorem finrank_K_over_KPlusRestrict_le
- Type: `theorem finrank_K_over_KPlusRestrict_le {n : ℕ} (_hn : 1 ≤ n) : Module.finrank (KPlusRestrict p n) (K p n) ≤ 2`
- What: `[K_n : K_n⁺] ≤ 2`: `ξ_n` is a root of the monic degree-2 polynomial `X² − (ξ+ξ⁻¹)X + 1` over `K_n⁺`, and `K_n = K_n⁺(ξ_n)`.
- How: `adjoin_eq_top_of_adjoin_eq_top` gives `K_n⁺(ξ_n) = ⊤`; `IsIntegral.tower_top`; build `g = X² − C β X + 1` (`monicity!`, `compute_degree!`), show `aeval ξ_K g = 0` (`field_simp`/`ring`); then `IntermediateField.adjoin.finrank` and `minpoly.min` bound `natDegree ≤ 2`. Hinges on `minpoly.min` and `IntermediateField.adjoin.finrank`.
- Hypotheses: `1 ≤ n` (unused except name).
- Uses from project: `KPlusRestrict`, `K`, `zetaSys`, `zetaSys_mem_K`, `zetaSys_primitiveRoot`, `KPlus`, `KPlus_le_K`, `isIntegral_zetaSysK`, `adjoinSimple_zetaSysK_eq_top`
- Used by: `KPlus_eq_fixedField`
- Visibility: public
- Lines: 338–373 (proof ~35 lines)
- Notes: long(30-50); set_option `maxHeartbeats 1600000` and `synthInstance.maxHeartbeats 400000` (lines 331–334)

### theorem KPlus_eq_fixedField
- Type: `theorem KPlus_eq_fixedField (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : KPlusRestrict p n = IntermediateField.fixedField (Subgroup.zpowers (galAut p (-1) n))`
- What: RJW §12 fixed-field characterisation: the maximal totally real subfield `K_n⁺` is exactly the fixed field of complex conjugation `σ_{-1}`.
- How: `IntermediateField.eq_of_le_of_finrank_le'`: containment (`KPlusRestrict_le_fixedField`) plus dimension comparison `[K_n:fixedField] = 2 ≥ [K_n:K_n⁺]` (`finrank_fixedField_galAut_neg_one`, `finrank_K_over_KPlusRestrict_le`).
- Hypotheses: `p ≠ 2`, `1 ≤ n`.
- Uses from project: `KPlusRestrict`, `galAut`, `KPlusRestrict_le_fixedField`, `finrank_fixedField_galAut_neg_one`, `finrank_K_over_KPlusRestrict_le`
- Used by: `mem_KPlus_iff_galAut_neg_one_fixed`
- Visibility: public
- Lines: 383–388 (proof ~5 lines)
- Notes: none

### theorem mem_KPlus_iff_galAut_neg_one_fixed
- Type: `theorem mem_KPlus_iff_galAut_neg_one_fixed (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]} (hxK : x ∈ K p n) : x ∈ KPlus p n ↔ (galAut p (-1) n ⟨x, hxK⟩ : ℂ_[p]) = x`
- What: Membership form: `x ∈ K_n` lies in `K_n⁺` iff fixed by complex conjugation `σ_{-1}`.
- How: `KPlus_eq_fixedField` through `mem_restrict`/`mem_fixedField_iff`; the `zpowers σ_{-1}` quantifier collapses to the generator via `Int.induction_on` on the power (using `hfix`, `hfixinv`).
- Hypotheses: `p ≠ 2`, `1 ≤ n`, `x ∈ K p n`.
- Uses from project: `K`, `KPlus`, `galAut`, `KPlusRestrict`, `KPlus_eq_fixedField`, `KPlus_le_K`
- Used by: `mem_localUnitsOnePlus_iff_galAut_fixed`
- Visibility: public
- Lines: 394–415 (proof ~21 lines)
- Notes: none

### theorem mem_localUnitsOnePlus_iff_galAut_fixed
- Type: `theorem mem_localUnitsOnePlus_iff_galAut_fixed (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) {u : ℂ_[p]ˣ} (hu : u ∈ localUnitsOne p n) : u ∈ localUnitsOnePlus p n ↔ (galAut p (-1) n ⟨(u : ℂ_[p]), _⟩ : ℂ_[p]) = (u : ℂ_[p])`
- What: Unit-level fixed-field criterion (RJW §12.5): a principal unit `u ∈ 𝒰_{n,1}` lies in `𝒰⁺_{n,1}` iff fixed by complex conjugation `σ_{-1}`.
- How: Transports `mem_KPlus_iff_galAut_neg_one_fixed` through `localUnitsOnePlus = localUnitsOne ⊓ localUnitsPlus` (`Subgroup.mem_inf`); `localUnitsPlus` membership reduces to `(u:ℂ_[p]) ∈ K_n⁺`.
- Hypotheses: `p ≠ 2`, `1 ≤ n`, `u ∈ localUnitsOne p n`.
- Uses from project: `localUnitsOne`, `localUnitsOnePlus`, `galAut`, `K`, `KPlus`, `mem_KPlus_iff_galAut_neg_one_fixed`
- Used by: unused in file (terminal API consumed downstream)
- Visibility: public
- Lines: 422–433 (proof ~11 lines)
- Notes: none

### theorem galAut_compat
- Type: `theorem galAut_compat (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]} (hx : x ∈ K p n) : (galAut p a (n + 1) ⟨x, (K_le_succ p n) hx⟩ : ℂ_[p]) = (galAut p a n ⟨x, hx⟩ : ℂ_[p])`
- What: Tower compatibility: `σ_a` at level `n+1` restricts to `σ_a` at level `n` (uniqueness of the automorphism realising the character value).
- How: Two `ℚ_p`-algebra homs `F1, F2 : K_n → ℂ_[p]` agree on `ξ_n`: via `galAut_zetaSys` at both levels, `zetaSys_pow_p` (so `incl ξ_n = ξ_{n+1}^p`), and reduction of exponents mod `p^n` (`unitsToZModPow_le`, `zetaSys_pow_eq_pow_of_modEq`). Then `AlgHom.ext_of_adjoin_eq_top (adjoin_zetaSysK_eq_top)` extends agreement to all of `K_n`. Hinges on `AlgHom.ext_of_adjoin_eq_top` and `PadicMeasure.unitsToZModPow_le`.
- Hypotheses: `1 ≤ n`, `x ∈ K p n`.
- Uses from project: `galAut`, `K`, `K_le_succ`, `zetaSys`, `zetaSys_mem_K`, `zetaSys_pow_p`, `galAut_zetaSys`, `PadicMeasure.unitsToZModPow`, `PadicMeasure.unitsToZModPow_le`, `zetaSys_pow_eq_pow_of_modEq`, `adjoin_zetaSysK_eq_top`
- Used by: `galAutES_apply`, `levelNorm_galAut`
- Visibility: public
- Lines: 437–493 (proof ~56 lines)
- Notes: OVER-50 (needs /decompose-proof)

### def galAutES
- Type: `private def galAutES (a : ℤ_[p]ˣ) {n : ℕ} (_hn : 1 ≤ n) : IntermediateField.extendScalars (K_le_succ p n) ≃+* IntermediateField.extendScalars (K_le_succ p n)`
- What: `σ_a^{(n+1)}` as a ring automorphism of the `K_n`-algebra `extendScalars (K_n ≤ K_{n+1})` (same carrier as `K_{n+1}`), `galAut_compat`-semilinear over `K_n`, packaged as a plain `RingEquiv` for the norm conjugation.
- How: `(galAut p a (n + 1)).toRingEquiv`.
- Hypotheses: `1 ≤ n` (unused except name).
- Uses from project: `galAut`, `K_le_succ`
- Used by: `galAutES_apply`, `levelNorm_galAut`
- Visibility: private
- Lines: 498–501 (body ~1 line)
- Notes: none

### theorem galAutES_apply
- Type: `@[simp] private theorem galAutES_apply (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) (y : … extendScalars …) : ((galAutES p a hn y : …) : ℂ_[p]) = (galAut p a (n + 1) ⟨(y : ℂ_[p]), y.2⟩ : ℂ_[p])`
- What: Coercion simp lemma: the underlying `ℂ_[p]`-value of `galAutES` is `galAut p a (n+1)` applied to the underlying element.
- How: `rfl`.
- Hypotheses: `1 ≤ n`.
- Uses from project: `galAutES`, `galAut`, `K_le_succ`
- Used by: `levelNorm_galAut`
- Visibility: private (simp)
- Lines: 503–507 (proof rfl)
- Notes: none

### theorem levelNorm_galAut
- Type: `theorem levelNorm_galAut (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]} (hx : x ∈ K p (n + 1)) : levelNorm p n (galAut p a (n + 1) ⟨x, hx⟩ : ℂ_[p]) = (galAut p a n ⟨levelNorm p n x, levelNorm_mem p n hx⟩ : ℂ_[p])`
- What: The relative norm is Galois-equivariant: `N_{n+1,n} ∘ σ_a = σ_a ∘ N_{n+1,n}` (RJW TeX 3199).
- How: `σ_a^{(n+1)}` (`galAutES`) is `galAut_compat`-semilinear over `K_n`, so `Algebra.norm_eq_of_equiv_equiv` (with the base twisted by `σ_a^{(n)} = e`) gives `e(N xes) = N(galAutES xes)`; reconciled with `levelNorm_apply`/`levelNorm_mem`. Hinges on `Algebra.norm_eq_of_equiv_equiv` and `galAut_compat`.
- Hypotheses: `1 ≤ n`, `x ∈ K p (n+1)`.
- Uses from project: `levelNorm`, `galAut`, `K`, `levelNorm_mem`, `K_le_succ`, `galAutES`, `galAut_compat`, `galAutES_apply`, `levelNorm_apply`
- Used by: `galNCU`
- Visibility: public
- Lines: 514–557 (proof ~43 lines)
- Notes: long(30-50)

### def restrictAbsK
- Type: `private noncomputable def restrictAbsK (n : ℕ) : AbsoluteValue (K p n) ℝ`
- What: The restriction of the `ℂ_p`-norm to `K_n`, as an `AbsoluteValue` (mirrors the private `Tower.restrictAbs`).
- How: Bundles `toFun y := ‖(y : ℂ_[p])‖` with field-axiom proofs (`norm_mul`, `norm_nonneg`, `norm_eq_zero`, `norm_add_le`).
- Hypotheses: `n : ℕ`.
- Uses from project: `K`
- Used by: `norm_coe_eq_spectralNorm`
- Visibility: private
- Lines: 561–568 (body ~7 lines)
- Notes: none

### theorem norm_coe_eq_spectralNorm
- Type: `private theorem norm_coe_eq_spectralNorm {n : ℕ} (y : K p n) : ‖(y : ℂ_[p])‖ = spectralNorm ℚ_[p] (K p n) y`
- What: The `ℂ_p`-norm of `y ∈ K_n` equals its `ℚ_p`-spectral norm.
- How: `spectralNorm_unique_field_norm_ext` applied to `restrictAbsK`, checking the absolute value agrees with `‖·‖` on `algebraMap ℚ_[p]`-elements.
- Hypotheses: `n : ℕ`.
- Uses from project: `K`, `finrank_K`, `restrictAbsK`
- Used by: `norm_galAut`
- Visibility: private
- Lines: 571–580 (proof ~9 lines)
- Notes: none

### theorem norm_galAut
- Type: `theorem norm_galAut (a : ℤ_[p]ˣ) {n : ℕ} (y : K p n) : ‖(galAut p a n y : ℂ_[p])‖ = ‖(y : ℂ_[p])‖`
- What: `σ_a` is an isometry on `K_n` (RJW TeX 3199, used for `O_n`-preservation): `‖σ_a y‖ = ‖y‖`.
- How: Rewrite both sides via `norm_coe_eq_spectralNorm`; the spectral norm depends only on the minimal polynomial, preserved by the automorphism (`minpoly.algEquiv_eq`).
- Hypotheses: `a : ℤ_[p]ˣ`, `y : K p n`.
- Uses from project: `galAut`, `K`, `norm_coe_eq_spectralNorm`
- Used by: `galAut_mem_O`
- Visibility: public
- Lines: 586–589 (proof ~3 lines)
- Notes: none

### theorem galAut_mem_O
- Type: `theorem galAut_mem_O (a : ℤ_[p]ˣ) {n : ℕ} {y : ℂ_[p]} (hy : y ∈ O p n) : (galAut p a n ⟨y, (Subring.mem_inf.1 hy).1⟩ : ℂ_[p]) ∈ O p n`
- What: `σ_a` preserves `O_n`: if `(y:ℂ_p) ∈ O_n` then so is `σ_a y` (norm preserved, `K_n`-membership automatic).
- How: `O = K ⊓ {‖·‖≤1}` via `Subring.mem_inf`; `K`-membership is the subtype's `.2`, norm bound via `norm_galAut`.
- Hypotheses: `y ∈ O p n`.
- Uses from project: `galAut`, `O`, `norm_galAut`
- Used by: `galNCU`
- Visibility: public
- Lines: 593–599 (proof ~5 lines)
- Notes: none

### theorem isUnit_mkK
- Type: `private theorem isUnit_mkK {n : ℕ} (v : ℂ_[p]ˣ) (hv : (v : ℂ_[p]) ∈ K p n) : IsUnit (⟨(v : ℂ_[p]), hv⟩ : K p n)`
- What: The `K_n`-element `⟨v,_⟩` of a unit `v` of `ℂ_p` lying in `K_n` is a unit of `K_n`.
- How: `isUnit_iff_ne_zero` in the field `K_n`; non-zero since `v` is a unit (`v.ne_zero`).
- Hypotheses: `(v:ℂ_[p]) ∈ K p n`.
- Uses from project: `K`
- Used by: `galAutUnit`, `galAutUnit_val`
- Visibility: private
- Lines: 602–604 (proof ~2 lines term)
- Notes: none

### def galAutUnit
- Type: `noncomputable def galAutUnit (a : ℤ_[p]ˣ) {n : ℕ} (v : ℂ_[p]ˣ) (hv : (v : ℂ_[p]) ∈ K p n) : ℂ_[p]ˣ`
- What: The unit `σ_a v` of `ℂ_p` from a unit `v` whose value lies in `K_n`: `galAut` maps the `K_n`-unit `⟨v,_⟩` to a unit, re-embedded into `ℂ_[p]ˣ`.
- How: `Units.map ((K p n).val.toMonoidHom.comp (galAut p a n).toAlgHom.toMonoidHom) (isUnit_mkK …).unit`.
- Hypotheses: `(v:ℂ_[p]) ∈ K p n`.
- Uses from project: `K`, `galAut`, `isUnit_mkK`
- Used by: `galAutUnit_val`, `galAutUnit_inv_val`, `galNCU`, `colemanSeries_galNCU`
- Visibility: public
- Lines: 609–612 (body ~3 lines)
- Notes: none

### theorem galAutUnit_val
- Type: `@[simp] theorem galAutUnit_val (a : ℤ_[p]ˣ) {n : ℕ} (v : ℂ_[p]ˣ) (hv : (v : ℂ_[p]) ∈ K p n) : ((galAutUnit p a v hv : ℂ_[p]ˣ) : ℂ_[p]) = (galAut p a n ⟨(v : ℂ_[p]), hv⟩ : ℂ_[p])`
- What: The `ℂ_p`-value of `galAutUnit` equals `galAut` of the underlying element.
- How: Unfold `galAutUnit`, `Units.map`, then `IsUnit.unit_spec`; `rfl`.
- Hypotheses: `(v:ℂ_[p]) ∈ K p n`.
- Uses from project: `galAutUnit`, `K`, `galAut`, `isUnit_mkK`
- Used by: `galAutUnit_inv_val`, `galNCU`, `colemanSeries_galNCU`
- Visibility: public (simp)
- Lines: 615–619 (proof ~3 lines)
- Notes: none

### theorem galAutUnit_inv_val
- Type: `@[simp] theorem galAutUnit_inv_val (a : ℤ_[p]ˣ) {n : ℕ} (v : ℂ_[p]ˣ) (hv : (v : ℂ_[p]) ∈ K p n) : (((galAutUnit p a v hv)⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = (galAut p a n ⟨((v : ℂ_[p]))⁻¹, (K p n).inv_mem hv⟩ : ℂ_[p])`
- What: The `ℂ_p`-value of the inverse unit `(galAutUnit)⁻¹` equals `galAut` of `v⁻¹`.
- How: `Units.val_inv_eq_inv_val` + `galAutUnit_val`; rewrite `⟨v,_⟩⁻¹ = ⟨v⁻¹,_⟩` (`IntermediateField.coe_inv`) then `map_inv₀`.
- Hypotheses: `(v:ℂ_[p]) ∈ K p n`.
- Uses from project: `galAutUnit`, `galAut`, `K`, `galAutUnit_val`
- Used by: `galAutUnit_inv_val'`
- Visibility: public (simp)
- Lines: 622–631 (proof ~6 lines)
- Notes: none

### theorem galAutUnit_inv_val'
- Type: `@[simp] theorem galAutUnit_inv_val' (a : ℤ_[p]ˣ) {n : ℕ} (v : ℂ_[p]ˣ) (hv : (v : ℂ_[p]) ∈ K p n) : (((galAutUnit p a v hv : ℂ_[p]ˣ) : ℂ_[p]))⁻¹ = (galAut p a n ⟨((v : ℂ_[p]))⁻¹, (K p n).inv_mem hv⟩ : ℂ_[p])`
- What: Variant: the `ℂ_p`-inverse of the value of `galAutUnit` equals `galAut` of `v⁻¹`.
- How: `← Units.val_inv_eq_inv_val` + `galAutUnit_inv_val`.
- Hypotheses: `(v:ℂ_[p]) ∈ K p n`.
- Uses from project: `galAutUnit`, `galAut`, `K`, `galAutUnit_inv_val`
- Used by: `galNCU`
- Visibility: public (simp)
- Lines: 634–638 (proof ~1 line)
- Notes: none

### def galNCU
- Type: `def galNCU (a : ℤ_[p]ˣ) (u : NormCompatUnits p) : NormCompatUnits p`
- What: The `𝒢`-action `σ_a` on the norm-compatible unit tower `𝒰_∞` (RJW TeX 3201–3204): levelwise `galAut`, well-defined by `galAut_compat` + `levelNorm_galAut`.
- How: Sets `elems n := galAutUnit p a (u.elems n) …`; `mem`/`inv_mem` from `galAut_mem_O` (with `galAutUnit_val`/`galAutUnit_inv_val'`); `compat` from `levelNorm_galAut` + `u.compat`.
- Hypotheses: `a : ℤ_[p]ˣ`, `u : NormCompatUnits p`.
- Uses from project: `NormCompatUnits`, `galAutUnit`, `galAutUnit_val`, `galAutUnit_inv_val'`, `galAut_mem_O`, `levelNorm`, `levelNorm_galAut`
- Used by: `colemanSeries_galNCU`, `Col_galNCU`
- Visibility: public
- Lines: 644–659 (structure-fields proof ~16 lines)
- Notes: none

### def galSubstend
- Type: `noncomputable def galSubstend (a : ℤ_[p]ˣ) : PowerSeries ℤ_[p]`
- What: The substituend `(1+T)^a − 1 ∈ ℤ_[p]⟦T⟧` for `a : ℤ_[p]ˣ` (RJW TeX 3206); `binomialSeries ℤ_[p] (a:ℤ_[p])` minus `1`, constant coeff `0`.
- How: `PowerSeries.binomialSeries ℤ_[p] (a : ℤ_[p]) - 1`.
- Hypotheses: `a : ℤ_[p]ˣ`.
- Uses from project: []
- Used by: `constantCoeff_galSubstend`, `hasSubst_galSubstend`, `galSeries`, `seriesEval_map_galSubstend`, `dlog_galSeries`
- Visibility: public
- Lines: 664–665 (body ~1 line)
- Notes: none

### theorem constantCoeff_galSubstend
- Type: `@[simp] theorem constantCoeff_galSubstend (a : ℤ_[p]ˣ) : PowerSeries.constantCoeff (galSubstend p a) = 0`
- What: The constant coefficient of `galSubstend a` is `0`.
- How: `map_sub` + `binomialSeries_constantCoeff` + `map_one`, then `sub_self`.
- Hypotheses: `a : ℤ_[p]ˣ`.
- Uses from project: `galSubstend`
- Used by: `hasSubst_galSubstend`, `evalPi_galSeries`
- Visibility: public (simp)
- Lines: 668–670 (proof ~2 lines)
- Notes: none

### theorem hasSubst_galSubstend
- Type: `theorem hasSubst_galSubstend (a : ℤ_[p]ˣ) : PowerSeries.HasSubst (galSubstend p a)`
- What: `galSubstend a` is a valid substituend.
- How: `HasSubst.of_constantCoeff_zero'` from `constantCoeff_galSubstend`.
- Hypotheses: `a : ℤ_[p]ˣ`.
- Uses from project: `galSubstend`, `constantCoeff_galSubstend`
- Used by: `evalPi_galSeries`, `dlog_galSeries`
- Visibility: public
- Lines: 672–673 (proof ~1 line term)
- Notes: none

### def galSeries
- Type: `noncomputable def galSeries (a : ℤ_[p]ˣ) (f : PowerSeries ℤ_[p]) : PowerSeries ℤ_[p]`
- What: `σ_a` on power series: `f ↦ f((1+T)^a − 1)` (RJW TeX 3206), realised as `PowerSeries.subst` of `galSubstend a`.
- How: `f.subst (galSubstend p a)`.
- Hypotheses: `a : ℤ_[p]ˣ`, `f : PowerSeries ℤ_[p]`.
- Uses from project: `galSubstend`
- Used by: `evalPi_galSeries`, `colemanSeries_galNCU`, `dlog_galSeries`, `mahlerSymm_galSeries`, `Col_galNCU`
- Visibility: public
- Lines: 677–678 (body ~1 line)
- Notes: none

### theorem norm_coeff_pow_le_one'
- Type: `private theorem norm_coeff_pow_le_one' {G : PowerSeries ℂ_[p]} (hG : ∀ k, ‖PowerSeries.coeff k G‖ ≤ 1) (d k : ℕ) : ‖PowerSeries.coeff k (G ^ d)‖ ≤ 1`
- What: `‖coeff k (G^d)‖ ≤ 1` for an integral-coefficient `G` (re-derivation of `ResidueZeta.norm_coeff_pow_le_one`).
- How: Induction on `d`; the successor step uses `coeff_mul` + ultrametric `norm_sum_le_of_forall_le_of_nonneg` + `mul_le_one₀`.
- Hypotheses: all coefficients of `G` have norm `≤ 1`.
- Uses from project: []
- Used by: `seriesEval_pow_of_integral`, `seriesEval_subst`
- Visibility: private
- Lines: 683–690 (proof ~7 lines)
- Notes: none

### theorem seriesEval_pow_of_integral
- Type: `private theorem seriesEval_pow_of_integral {G : PowerSeries ℂ_[p]} (hG : ∀ k, ‖PowerSeries.coeff k G‖ ≤ 1) {z : ℂ_[p]} (hz : ‖z‖ < 1) (d : ℕ) : seriesEval (G ^ d) z = (seriesEval G z) ^ d`
- What: `seriesEval (G^d) z = (seriesEval G z)^d` for integral `G`, `‖z‖<1` (re-derivation of private `ResidueZeta.seriesEval_pow`).
- How: Induction on `d`; successor uses `seriesEval_mul` with summability from `summable_seriesEval_of_norm_coeff_le_one` (+ `norm_coeff_pow_le_one'`).
- Hypotheses: `G` integral, `‖z‖<1`.
- Uses from project: `seriesEval`, `seriesEval_C`, `seriesEval_mul`, `summable_seriesEval_of_norm_coeff_le_one`, `norm_coeff_pow_le_one'`
- Used by: `seriesEval_subst`
- Visibility: private
- Lines: 694–703 (proof ~7 lines)
- Notes: none

### theorem coeff_pow_eq_zero_of_lt
- Type: `private theorem coeff_pow_eq_zero_of_lt {G : PowerSeries ℂ_[p]} (hG0 : PowerSeries.constantCoeff G = 0) {k n : ℕ} (hkn : k < n) : PowerSeries.coeff k (G ^ n) = 0`
- What: `coeff k (G^n) = 0` for `k < n` when `constantCoeff G = 0` (so `X^n ∣ G^n`).
- How: `X_pow_dvd_iff` + `pow_dvd_pow_of_dvd` of `X ∣ G` (`X_dvd_iff`).
- Hypotheses: `constantCoeff G = 0`, `k < n`.
- Uses from project: []
- Used by: `norm_seriesEval_lt` (indirectly via summability), `seriesEval_subst`
- Visibility: private
- Lines: 706–710 (proof ~4 lines term)
- Notes: none

### theorem norm_seriesEval_lt
- Type: `private theorem norm_seriesEval_lt {G : PowerSeries ℂ_[p]} (hG : ∀ k, ‖PowerSeries.coeff k G‖ ≤ 1) (hG0 : PowerSeries.constantCoeff G = 0) {z : ℂ_[p]} (hz : ‖z‖ < 1) : ‖seriesEval G z‖ < 1`
- What: `‖seriesEval G z‖ ≤ ‖z‖ < 1` when `constantCoeff G = 0` and `G` integral.
- How: `IsUltrametricDist.norm_tsum_le_of_forall_le`: the `k=0` term vanishes (`hG0`), each `k≥1` term `≤ ‖z‖` (`pow_le_one₀`).
- Hypotheses: `G` integral, `constantCoeff G = 0`, `‖z‖<1`.
- Uses from project: `seriesEval`
- Used by: `seriesEval_subst`
- Visibility: private
- Lines: 714–730 (proof ~16 lines)
- Notes: none

### theorem seriesEval_subst
- Type: `private theorem seriesEval_subst {f G : PowerSeries ℂ_[p]} (hf : … ≤ 1) (hG : … ≤ 1) (hG0 : constantCoeff G = 0) {z} (hz : ‖z‖ < 1) : seriesEval (f.subst G) z = seriesEval f (seriesEval G z)`
- What: The subst-evaluation bridge (RJW TeX 3206, generalising `evalPi_phi`): for integral `G` over `ℂ_[p]` with `constantCoeff G = 0`, `seriesEval (f.subst G) z = seriesEval f (seriesEval G z)` at `‖z‖<1`.
- How: Builds the double family `T n k = coeff_n f · coeff_k(G^n) · z^k`, bounds `‖T n k‖ ≤ ‖z‖^k`, proves joint summability (`summable_iff_tendsto_cofinite_zero` + finiteness via `coeff_pow_eq_zero_of_lt` and geometric decay), expands the LHS coefficient (`coeff_subst'`, `finsum`/`tsum` over a finite range), then `Summable.tsum_comm` and `seriesEval_pow_of_integral`. Hinges on `PowerSeries.coeff_subst'`, `Summable.tsum_comm`, `seriesEval_pow_of_integral`.
- Hypotheses: `f, G` integral, `constantCoeff G = 0`, `‖z‖<1`.
- Uses from project: `seriesEval`, `summable_seriesEval_of_norm_coeff_le_one`, `norm_coeff_pow_le_one'`, `seriesEval_pow_of_integral`, `coeff_pow_eq_zero_of_lt`, `norm_seriesEval_lt`
- Used by: `evalPi_galSeries`
- Visibility: private
- Lines: 736–802 (proof ~66 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem continuous_toCp
- Type: `private theorem continuous_toCp : Continuous (toCp p)`
- What: The coefficient inclusion `toCp : ℤ_[p] → ℂ_[p]` is continuous (`ℤ_[p] ↪ ℚ_[p] ↪ ℂ_[p]`).
- How: Unfold `toCp`; composition of `continuous_algebraMap ℚ_[p] ℂ_[p]` with `continuous_subtype_val`.
- Hypotheses: none.
- Uses from project: `toCp`
- Used by: `seriesEval_map_binomialSeries`
- Visibility: private
- Lines: 805–807 (proof ~2 lines)
- Notes: none

### theorem continuous_zpPow_aux
- Type: `private theorem continuous_zpPow_aux {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) : Continuous (zpPow p y)`
- What: `c ↦ zpPow p y c` is continuous in the exponent for a `1`-unit `y` (re-derivation of private `LocalUnits.continuous_zpPow`).
- How: Identifies `zpPow p y` with `PadicInt.addChar_of_value_at_one (y−1) …` (a continuous additive character) via `dif_pos`, then `continuous_addChar_of_value_at_one`.
- Hypotheses: `‖y − 1‖ < 1`.
- Uses from project: `zpPow`
- Used by: `seriesEval_map_binomialSeries`, `zpPow_zetaSys`
- Visibility: private
- Lines: 812–819 (proof ~7 lines)
- Notes: none

### theorem norm_coeff_map_binomialSeries_le_one
- Type: `private theorem norm_coeff_map_binomialSeries_le_one (c : ℤ_[p]) (k : ℕ) : ‖PowerSeries.coeff k (PowerSeries.map (toCp p) (PowerSeries.binomialSeries ℤ_[p] c))‖ ≤ 1`
- What: The pushed-forward binomial coefficients are integral: `‖coeff k (map toCp (binomial c))‖ ≤ 1`.
- How: `coeff_map` + `binomialSeries_coeff` + `norm_toCp`, then `PadicInt.norm_le_one` (`Ring.choose c k ∈ ℤ_[p]`).
- Hypotheses: `c : ℤ_[p]`, `k : ℕ`.
- Uses from project: `toCp`, `norm_toCp`
- Used by: `seriesEval_map_galSubstend`
- Visibility: private
- Lines: 823–826 (proof ~2 lines)
- Notes: none

### theorem seriesEval_map_binomialSeries
- Type: `theorem seriesEval_map_binomialSeries (c : ℤ_[p]) {z : ℂ_[p]} (hz : ‖z‖ < 1) : seriesEval (PowerSeries.map (toCp p) (PowerSeries.binomialSeries ℤ_[p] c)) z = zpPow p (1 + z) c`
- What: `seriesEval` of the binomial series equals `zpPow`: the analytic `(1+z)^c = Σ (c k) z^k` for `‖z‖<1`.
- How: Both sides continuous in `c` (LHS via `continuous_tsum` with uniform `‖z‖^k` bound; RHS via `continuous_zpPow_aux`) and agree on `c ∈ ℕ` (`binomialSeries_nat`/`seriesEval_one_add_X_pow` vs `zpPow_natCast`); `PadicInt.denseRange_natCast.equalizer` extends. Hinges on `PadicInt.denseRange_natCast.equalizer` and `zpPow_natCast`.
- Hypotheses: `‖z‖<1`.
- Uses from project: `seriesEval`, `toCp`, `norm_toCp`, `zpPow`, `zpPow_natCast`, `seriesEval_one_add_X_pow`, `continuous_toCp`, `continuous_zpPow_aux`
- Used by: `seriesEval_map_galSubstend`
- Visibility: public
- Lines: 833–857 (proof ~24 lines)
- Notes: none; `open scoped Topology in`

### theorem zpPow_zetaSys
- Type: `private theorem zpPow_zetaSys {n : ℕ} (hn : 1 ≤ n) (c : ℤ_[p]) : zpPow p (zetaSys p n) c = zetaSys p n ^ ((PadicInt.toZModPow n c : ZMod (p ^ n)).val)`
- What: `zpPow` on a root of unity is the cyclotomic power (`p^n`-periodicity of `ξ_n^·`): `zpPow ξ_n c = ξ_n^{(toZModPow n c).val}`.
- How: Both sides continuous in `c` (RHS locally constant via `isOpen_toZModPow_fiber`; LHS via `continuous_zpPow_aux`) and agree on `c ∈ ℕ` (`zpPow_natCast` vs `zetaSys_pow_eq_pow_of_modEq`); `denseRange_natCast.equalizer`. Hinges on `PadicInt.denseRange_natCast.equalizer` and `zetaSys_pow_eq_pow_of_modEq`.
- Hypotheses: `1 ≤ n`, `c : ℤ_[p]`.
- Uses from project: `zpPow`, `zetaSys`, `zpPow_natCast`, `zetaSys_pow_eq_pow_of_modEq`, `PadicMeasure.isOpen_toZModPow_fiber`, `norm_pi_lt_one`, `pi`, `continuous_zpPow_aux`
- Used by: `seriesEval_map_galSubstend`
- Visibility: private
- Lines: 863–883 (proof ~20 lines)
- Notes: none; `open scoped Topology in`

### theorem seriesEval_map_galSubstend
- Type: `private theorem seriesEval_map_galSubstend (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) : seriesEval (PowerSeries.map (toCp p) (galSubstend p a)) (pi p n) = zetaSys p n ^ ((unitsToZModPow p n a : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)).val - 1`
- What: The substituend evaluates to `σ_a(π_n)`: `(galSubstend a)(π_n) = ξ_n^{a mod p^n} − 1 = σ_a(ξ_n) − 1 = σ_a(π_n)`.
- How: `galSubstend = binomial − 1`, split via `seriesEval_sub`; `seriesEval_C` for the `1`; then `seriesEval_map_binomialSeries` + `1+π_n = ζ_n` + `zpPow_zetaSys` + `unitsToZModPow_coe`.
- Hypotheses: `1 ≤ n`.
- Uses from project: `seriesEval`, `toCp`, `galSubstend`, `pi`, `zetaSys`, `PadicMeasure.unitsToZModPow`, `norm_pi_lt_one`, `seriesEval_sub`, `summable_seriesEval_of_norm_coeff_le_one`, `norm_coeff_map_binomialSeries_le_one`, `seriesEval_C`, `seriesEval_map_binomialSeries`, `zpPow_zetaSys`, `PadicMeasure.unitsToZModPow_coe`
- Used by: `evalPi_galSeries`
- Visibility: private
- Lines: 888–903 (proof ~15 lines)
- Notes: none

### theorem galAut_evalPi
- Type: `private theorem galAut_evalPi (a : ℤ_[p]ˣ) (f : PowerSeries ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) : (galAut p a n ⟨evalPi p f n, …⟩ : ℂ_[p]) = seriesEval (PowerSeries.map (toCp p) f) (zetaSys p n ^ ((unitsToZModPow p n a : …) : …).val - 1)`
- What: `σ_a` (continuous on `K_n`) commutes with the evaluation series of an integral `ℂ_[p]`-coefficient `H = map toCp f` at `π_n`: `σ_a(seriesEval H π_n) = seriesEval H (σ_a π_n)` (`σ_a` fixes the `ℚ_p`-coefficients).
- How: Computes `σ_a(π_n) = ξ_n^t − 1` (`galAut_zetaSys`); `σ_a` fixes each coefficient `c k` (an `algebraMap ℚ_[p]`-element, `AlgEquiv.commutes`); approximates `evalPi` by finite partial sums `S m` in `K_n`, uses continuity of `galAut` (`continuous_of_finiteDimensional`), maps termwise, and passes to the limit (`tendsto_nhds_unique`) with `‖ξ_n^t−1‖<1` (geometric-sum norm bound). Hinges on `AlgEquiv.commutes` and `LinearMap.continuous_of_finiteDimensional`.
- Hypotheses: `1 ≤ n`.
- Uses from project: `galAut`, `evalPi`, `evalPi_mem_O`, `toCp`, `zetaSys`, `zetaSys_primitiveRoot`, `PadicMeasure.unitsToZModPow`, `galAut_zetaSys`, `pi`, `pi_mem_K`, `K`, `finrank_K`, `seriesEval`, `summable_evalPi`, `summable_seriesEval_of_norm_coeff_le_one`, `norm_coeff_map_le_one`, `norm_pi_lt_one`
- Used by: `evalPi_galSeries`
- Visibility: private
- Lines: 909–996 (proof ~87 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem evalPi_galSeries
- Type: `theorem evalPi_galSeries (a : ℤ_[p]ˣ) (f : PowerSeries ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) : evalPi p (galSeries p a f) n = (galAut p a n ⟨evalPi p f n, …⟩ : ℂ_[p])`
- What: The evaluation bridge `evalPi (galSeries a f) n = σ_a(f(π_n))`.
- How: `map_subst` writes `map toCp (galSeries a f) = (map toCp f).subst (map toCp (galSubstend a))`; `seriesEval_subst` reduces to `f((galSubstend a)(π_n))`; inner value is `σ_a(π_n)` (`seriesEval_map_galSubstend`), outer commute is `galAut_evalPi`.
- Hypotheses: `1 ≤ n`.
- Uses from project: `evalPi`, `galSeries`, `galAut`, `evalPi_mem_O`, `toCp`, `galSubstend`, `pi`, `norm_pi_lt_one`, `hasSubst_galSubstend`, `constantCoeff_galSubstend`, `galAut_evalPi`, `seriesEval_subst`, `norm_coeff_map_le_one`, `seriesEval_map_galSubstend`
- Used by: `colemanSeries_galNCU`
- Visibility: public
- Lines: 1002–1016 (proof ~14 lines)
- Notes: none

### theorem colemanSeries_galNCU
- Type: `theorem colemanSeries_galNCU (a : ℤ_[p]ˣ) (u : NormCompatUnits p) : colemanSeries p (galNCU p a u) = galSeries p a (colemanSeries p u)`
- What: The Coleman series intertwines the two actions: `f_{σ_a u} = σ_a f_u` (RJW TeX 3210–3216).
- How: Both sides are `ℤ_[p]`-series agreeing on `evalPi` for every `n≥1` (`evalPi_colemanSeries`, `evalPi_galSeries`, with `(galNCU a u).elems n = σ_a(u_n)`), so equal by `evalPi_injective`.
- Hypotheses: `a : ℤ_[p]ˣ`, `u : NormCompatUnits p`.
- Uses from project: `colemanSeries`, `galNCU`, `galSeries`, `NormCompatUnits`, `evalPi_injective`, `evalPi_colemanSeries`, `evalPi_galSeries`, `galAutUnit`, `galAutUnit_val`
- Used by: `Col_galNCU`
- Visibility: public
- Lines: 1022–1030 (proof ~8 lines)
- Notes: none

### def unitsMulLeftCM
- Type: `def unitsMulLeftCM (a : ℤ_[p]ˣ) : C(ℤ_[p]ˣ, ℤ_[p]ˣ)`
- What: Multiplication by `a` on `ℤ_[p]ˣ` as a continuous self-map; the σ_a action on `Λ(ℤ_[p]ˣ)` is the pushforward along it (RJW TeX 3217–3234).
- How: `⟨fun v => a * v, continuous_const.mul continuous_id⟩`.
- Hypotheses: `a : ℤ_[p]ˣ`.
- Uses from project: []
- Used by: `cancel_a_extendByZero`, `unitsCmul_smul_sigma_eq_pushforward`, `Col_galNCU`
- Visibility: public
- Lines: 1034–1035 (body ~1 line)
- Notes: none

### theorem succ_mul_ringChoose
- Type: `private theorem succ_mul_ringChoose (r : ℤ_[p]) (n : ℕ) : ((n : ℤ_[p]) + 1) * Ring.choose r (n + 1) = (r - (n : ℤ_[p])) * Ring.choose r n`
- What: The descending-Pochhammer recursion for `Ring.choose` over `ℤ_[p]`: `(n+1)·binom(r,n+1) = (r−n)·binom(r,n)`; engine for the binomial-derivative identity.
- How: Expresses `descPochhammer.smeval r` as `factorial • Ring.choose` at `n` and `n+1` (`descPochhammer_eq_factorial_smul_choose`), uses `descPochhammer_succ_right` + `smeval_mul`, then cancels `n!` (`mul_left_cancel₀`) and `linear_combination`.
- Hypotheses: `r : ℤ_[p]`, `n : ℕ`.
- Uses from project: []
- Used by: `one_add_X_mul_derivative_binomialSeries`
- Visibility: private
- Lines: 1040–1057 (proof ~17 lines)
- Notes: none

### theorem coeff_binomialSeries'
- Type: `private theorem coeff_binomialSeries' (r : ℤ_[p]) (k : ℕ) : PowerSeries.coeff k (PowerSeries.binomialSeries ℤ_[p] r) = Ring.choose r k`
- What: `coeff k (binomialSeries r) = binom(r,k)` over `ℤ_[p]` (the `•1` smul is plain multiplication).
- How: `binomialSeries_coeff` + `smul_eq_mul` + `mul_one`.
- Hypotheses: `r : ℤ_[p]`, `k : ℕ`.
- Uses from project: []
- Used by: `one_add_X_mul_derivative_binomialSeries`
- Visibility: private
- Lines: 1061–1063 (proof ~1 line)
- Notes: none

### theorem one_add_X_mul_derivative_binomialSeries
- Type: `private theorem one_add_X_mul_derivative_binomialSeries (r : ℤ_[p]) : (1 + PowerSeries.X) * PowerSeries.derivativeFun (PowerSeries.binomialSeries ℤ_[p] r) = r • PowerSeries.binomialSeries ℤ_[p] r`
- What: The binomial-series derivative identity (RJW TeX 3223, engine of `σ_a`): `(1+T)·((1+T)^r)′ = r·(1+T)^r` formally.
- How: Coefficientwise (`ext n`); splits `X·` shift into `coeff_zero_X_mul`/`coeff_succ_X_mul`, uses `coeff_derivativeFun`, `coeff_binomialSeries'`, the recursion `succ_mul_ringChoose`, then `push_cast`/`linear_combination`.
- Hypotheses: `r : ℤ_[p]`.
- Uses from project: `succ_mul_ringChoose`, `coeff_binomialSeries'`
- Used by: `dlog_galSeries`
- Visibility: private
- Lines: 1068–1089 (proof ~21 lines)
- Notes: none

### theorem subst_inverse_of_isUnit
- Type: `private theorem subst_inverse_of_isUnit {f G : PowerSeries ℤ_[p]} (hf : IsUnit f) (hg : PowerSeries.HasSubst G) : (Ring.inverse f).subst G = Ring.inverse (f.subst G)`
- What: `Ring.inverse` commutes with substitution of a valid substituend for a unit argument (substitution is a ring hom, sending the unit and its inverse to inverse units).
- How: Write `f = ↑v`; let `φ = substAlgHom` (as `MonoidHom`); `Ring.inverse_unit` on both sides, with `φ(v⁻¹) = (Units.map φ v)⁻¹` (`Units.coe_map`/`map_inv`).
- Hypotheses: `f` a unit, `G` a valid substituend.
- Uses from project: []
- Used by: `dlog_galSeries`
- Visibility: private
- Lines: 1094–1106 (proof ~10 lines)
- Notes: none

### theorem dlog_galSeries
- Type: `private theorem dlog_galSeries (a : ℤ_[p]ˣ) {f : PowerSeries ℤ_[p]} (hf : IsUnit f) : dlog p (galSeries p a f) = (a : ℤ_[p]) • galSeries p a (dlog p f)`
- What: The `∂log` chain rule under `σ_a` (RJW TeX 3223): for a unit `f`, `∂log(σ_a f) = a·σ_a(∂log f)`.
- How: Chain rule `derivative_subst` plus the binomial-derivative identity `(1+T)·G′ = a·(1+T)^a` (`one_add_X_mul_derivative_binomialSeries`, with `G = galSubstend a`); substitution being a ring hom (`subst_mul`, `subst_add`, `subst_X`, `subst_inverse_of_isUnit`) moves `1+T`, the inverse, and the `(1+T)^a` factors through; LHS and RHS both reduce to `(a•binomial)·D·I`. Hinges on `PowerSeries.derivative_subst` and `one_add_X_mul_derivative_binomialSeries`.
- Hypotheses: `f` a unit.
- Uses from project: `dlog`, `galSeries`, `galSubstend`, `hasSubst_galSubstend`, `one_add_X_mul_derivative_binomialSeries`, `subst_inverse_of_isUnit`
- Used by: `Col_galNCU`
- Visibility: private
- Lines: 1113–1150 (proof ~37 lines)
- Notes: long(30-50)

### theorem mahlerSymm_galSeries
- Type: `private theorem mahlerSymm_galSeries (a : ℤ_[p]ˣ) (g : PowerSeries ℤ_[p]) : (PadicMeasure.mahlerLinearEquiv p).symm (galSeries p a g) = PadicMeasure.sigma p a ((PadicMeasure.mahlerLinearEquiv p).symm g)`
- What: The inverse Mahler bridge `𝒜⁻¹(σ_a g) = sigma a (𝒜⁻¹ g)` (RJW §3.5.5, TeX 1138, transported to `𝒜⁻¹`): `galSeries a = subst((1+T)^a−1)` is the `z`-twist of the Mahler transform, inverted.
- How: Sets `μ = mahlerLinearEquiv.symm g`; shows `mahlerTransform (sigma a μ) = galSeries a g` via `mahlerTransform_sigma`, then inverts using `LinearEquiv.symm_apply_apply`/`apply_symm_apply`.
- Hypotheses: `a : ℤ_[p]ˣ`, `g : PowerSeries ℤ_[p]`.
- Uses from project: `galSeries`, `galSubstend`, `PadicMeasure.mahlerLinearEquiv`, `PadicMeasure.sigma`, `PadicMeasure.mahlerTransform`, `PadicMeasure.mahlerTransform_sigma`, `PadicMeasure.mahlerLinearEquiv_apply`
- Used by: `Col_galNCU`
- Visibility: private
- Lines: 1155–1164 (proof ~9 lines)
- Notes: none

### theorem cancel_a_extendByZero
- Type: `private theorem cancel_a_extendByZero (a : ℤ_[p]ˣ) (f : C(ℤ_[p]ˣ, ℤ_[p])) : (a : ℤ_[p]) • ((extendByZero p (invCM p * f)).comp (mulCM p (a:ℤ_[p]))) = extendByZero p (invCM p * f.comp (unitsMulLeftCM p a))`
- What: The `a`/`a⁻¹` cancellation at the level of test functions (RJW TeX 3223): on units `w`, both sides give `w⁻¹·f(a·w)` (the `x⁻¹` swallows the `a`); off the units both vanish (`a·x` unit iff `x` unit).
- How: `ext x`, case `IsUnit x`: write `x = w`, unfold `extendByZero_coe_unit`, `invCM`, use `a·a⁻¹ = 1` and `ring`; case `¬IsUnit x`: both `extendByZero` are `0` via `dif_neg` (`a·x` not a unit).
- Hypotheses: `a : ℤ_[p]ˣ`, `f : C(ℤ_[p]ˣ, ℤ_[p])`.
- Uses from project: `PadicMeasure.extendByZero`, `PadicMeasure.invCM`, `PadicMeasure.mulCM`, `PadicMeasure.extendByZero_coe_unit`, `unitsMulLeftCM`
- Used by: `unitsCmul_smul_sigma_eq_pushforward`
- Visibility: private
- Lines: 1171–1208 (proof ~37 lines)
- Notes: long(30-50)

### theorem unitsCmul_smul_sigma_eq_pushforward
- Type: `private theorem unitsCmul_smul_sigma_eq_pushforward (a : ℤ_[p]ˣ) (μ : PadicMeasure p ℤ_[p]) : unitsCmul p (invCM p) (((a:ℤ_[p]) • sigma p a μ).comp (extendByZero p)) = pushforward p (unitsMulLeftCM p a) (unitsCmul p (invCM p) (μ.comp (extendByZero p)))`
- What: The μ-generic measure identity behind `Col_galNCU` (RJW TeX 3217–3234): after the `∂log`/Mahler reductions both `Col(σ_a u)` and `σ_a·Col(u)` reduce to `x⁻¹·Res(a•σ_a μ)` / pushforward of `x⁻¹·Res μ`, agreeing by `cancel_a_extendByZero`.
- How: `LinearMap.ext f`; unfold `pushforward_apply`, `unitsCmul_apply`, `sigma`; the key step rewrites via `← cancel_a_extendByZero` and `map_smul`.
- Hypotheses: `a : ℤ_[p]ˣ`, `μ : PadicMeasure p ℤ_[p]`.
- Uses from project: `PadicMeasure.unitsCmul`, `PadicMeasure.invCM`, `PadicMeasure.sigma`, `PadicMeasure.extendByZero`, `PadicMeasure.pushforward`, `PadicMeasure.pushforward_apply`, `PadicMeasure.unitsCmul_apply`, `unitsMulLeftCM`, `cancel_a_extendByZero`
- Used by: `Col_galNCU`
- Visibility: private
- Lines: 1214–1227 (proof ~7 lines)
- Notes: none

### theorem Col_galNCU
- Type: `theorem Col_galNCU (a : ℤ_[p]ˣ) (u : NormCompatUnits p) : Col p (galNCU p a u) = PadicMeasure.pushforward p (unitsMulLeftCM p a) (Col p u)`
- What: RJW §12.1 Proposition (TeX 3193–3236): the Coleman map is `𝒢`-equivariant, with `σ_a` acting on `Λ(ℤ_[p]ˣ)` by pushforward along multiplication by `a`. (Statement-fix T1201: RHS is the genuine pushforward, not the skeleton placeholder `unitsCmul p 1`.)
- How: Unfold `Col`; chain `colemanSeries_galNCU`, `dlog_galSeries` (`∂log(σ_a f)=a·σ_a ∂log f`), `map_smul`, `mahlerSymm_galSeries`, and finish with `unitsCmul_smul_sigma_eq_pushforward`.
- Hypotheses: `a : ℤ_[p]ˣ`, `u : NormCompatUnits p`.
- Uses from project: `Col`, `galNCU`, `unitsMulLeftCM`, `colemanSeries`, `colemanSeries_galNCU`, `dlog`, `dlog_galSeries`, `colemanSeries_isUnit`, `PadicMeasure.mahlerLinearEquiv`, `mahlerSymm_galSeries`, `unitsCmul_smul_sigma_eq_pushforward`
- Used by: unused in file (terminal §12.1 result)
- Visibility: public
- Lines: 1237–1243 (proof ~6 lines)
- Notes: none

---

## File Summary

**Total declarations: 44** (defs: 7 [`galAut`, `galAutES`, `galAutUnit`, `galNCU`, `galSubstend`, `galSeries`, `unitsMulLeftCM`] + abbrev `KPlusRestrict`; lemmas/theorems: 33; instances: 3 [`instNeZeroPpow`, `isGalois_K`, `finiteDimensional_K`]). Counting the abbrev with defs: 8 def-like, 33 theorem-like, 3 instances.

**Key API (used by ≥3 in-file):**
- `galAut` — the central object, used by ~20 decls.
- `galAutUnit`, `galAutUnit_val` — used by `galNCU`, `colemanSeries_galNCU`, the inv lemmas.
- `galSeries`, `galSubstend` — used across the power-series equivariance chain (≥3 each).
- `zetaSys_pow_eq_pow_of_modEq` — used by 3 (`galAut_neg_one_zetaSys`, `galAut_compat`, `zpPow_zetaSys`).
- `unitsMulLeftCM` — used by 3 (`cancel_a_extendByZero`, `unitsCmul_smul_sigma_eq_pushforward`, `Col_galNCU`).
- `isIntegral_zetaSysK` — used by 3.
- `norm_coeff_pow_le_one'` — used by 3.

**Unused in file (terminal/consumed downstream):** `mem_localUnitsOnePlus_iff_galAut_fixed`, `Col_galNCU`, instances `isGalois_K` / `finiteDimensional_K` (resolved implicitly; several proofs re-derive `FiniteDimensional` locally rather than referencing the instance).

**Declarations with `sorry`: NONE.** (Despite the file header's skeleton note, all bodies are filled.)

**Declarations with TODO: none.**

**set_option:** `finrank_K_over_KPlusRestrict_le` (lines 331–334) carries `maxHeartbeats 1600000` and `synthInstance.maxHeartbeats 400000`.

**Proofs > 50 lines (OVER-50, need /decompose-proof) — count: 5**
1. `galAut_evalPi` — ~87 lines (909–996).
2. `seriesEval_subst` — ~66 lines (736–802).
3. `galAut_compat` — ~56 lines (437–493).
4. `galAut_neg_one_fixes_KPlus` — ~51 lines (250–301).
5. (borderline) none other crosses 50.

**Proofs 30–50 lines (long) — count: 5**
1. `autToPow_zetaSys_eq` — ~37 lines.
2. `levelNorm_galAut` — ~43 lines.
3. `finrank_K_over_KPlusRestrict_le` — ~35 lines.
4. `dlog_galSeries` — ~37 lines.
5. `cancel_a_extendByZero` — ~37 lines.

(Borderline ~29 lines: `orderOf_galAut_neg_one`.)
