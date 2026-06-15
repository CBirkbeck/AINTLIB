# Inventory: ./HasseWeil/Basic.lean

**File summary:** 1294 lines. Defines the `Isogeny` structure (function-field pullback + group homomorphism), the `mulByInt` endomorphism, and the `torsionSubgroup`. The main mathematical content is the proof that `deg([n]) = n²` via a tower-law argument through intermediate fields. No `sorry` in any declaration body. Imports `HasseWeil.MulByIntPullback`.

---

## Structure

### `structure Isogeny`
- **Type**: `{F : Type*} [Field F] [DecidableEq F] (W₁ W₂ : Affine F) [W₁.IsElliptic] [W₂.IsElliptic]`; fields: `pullback : W₂.FunctionField →ₐ[F] W₁.FunctionField`, `toAddMonoidHom : W₁.Point →+ W₂.Point`
- **What**: An isogeny φ : E₁ → E₂ bundling a function-field pullback and a group homomorphism on rational points. The degree is computed (not stored) as `[K(E₁) : φ*K(E₂)]`.
- **How**: Pure data structure; no proof obligation. The design deliberately avoids carrying degree as data to prevent circular reasoning in the Hasse bound proof.
- **Hypotheses**: Both curves elliptic over a field with decidable equality.
- **Uses from project**: none
- **Used by**: essentially every other declaration in the file
- **Visibility**: public
- **Lines**: 63–68
- **Notes**: `n = 0` branch of `mulByInt` produces a junk-value pullback (documented at length in lines 218–245).

---

## Namespace `Isogeny`

### `theorem pullback_injective`
- **Type**: `(φ : Isogeny W₁ W₂) → Function.Injective φ.pullback`
- **What**: Any algebra hom from a field is injective; hence the pullback is injective.
- **How**: `φ.pullback.toRingHom.injective` (one-line, ring hom from field is injective).
- **Hypotheses**: none beyond `Isogeny`.
- **Uses from project**: none
- **Used by**: `mulByIntRangeEquiv`, referenced in `mulByInt_finrank` and `mulByInt_degree`.
- **Visibility**: public
- **Lines**: 77–79 (proof: 1 line)

### `noncomputable def toAlgebra` (@[reducible])
- **Type**: `(φ : Isogeny W₁ W₂) → Algebra W₂.FunctionField W₁.FunctionField`
- **What**: Makes K(E₁) into a K(E₂)-algebra via the pullback; used to define `degree` via `Module.finrank`.
- **How**: `φ.pullback.toRingHom.toAlgebra`.
- **Hypotheses**: none beyond `Isogeny`.
- **Uses from project**: none
- **Used by**: `degree`, `mulByInt_degree`.
- **Visibility**: public
- **Lines**: 85–87 (proof: 1 line)

### `noncomputable def degree`
- **Type**: `(φ : Isogeny W₁ W₂) → ℕ`
- **What**: The degree `[K(E₁) : K(E₂)]` where K(E₁) is a K(E₂)-module via the pullback, computed via `Module.finrank`.
- **How**: `@Module.finrank W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra.toModule`.
- **Hypotheses**: none beyond `Isogeny`.
- **Uses from project**: `toAlgebra`
- **Used by**: `comp_degree`, `comp_degree_pos`, `id_degree`, `mulByInt_degree`, `mulByInt_degree_pos`, `mulByInt_degree_ne_zero`, `Isogeny.zsmul_degree`, `Isogeny.zsmul_degree_pos`.
- **Visibility**: public
- **Lines**: 91–92

### `noncomputable def comp` (set_option maxHeartbeats 400000)
- **Type**: `(ψ : Isogeny W₂ W₃) → (φ : Isogeny W₁ W₂) → Isogeny W₁ W₃`
- **What**: Composition of isogenies: pullback via `AlgHom.comp`, group hom via `AddMonoidHom.comp`.
- **How**: Direct struct construction; the heartbeat bump is due to `AlgHom.comp` synthesis on `FunctionField`.
- **Hypotheses**: none beyond source isogenies.
- **Uses from project**: none (pure mathlib)
- **Used by**: `comp_toAddMonoidHom`, `comp_apply`, `comp_algebraMap_eq`, `comp_degree`, `comp_degree_pos`, `Isogeny.zsmul`.
- **Visibility**: public
- **Lines**: 99–102 (proof: 3 lines)
- **Notes**: `set_option maxHeartbeats 400000` — comment present: "Synthesis of `AlgHom.comp` on `FunctionField` needs extra heartbeats."

### `@[simp] theorem comp_toAddMonoidHom`
- **Type**: `(ψ.comp φ).toAddMonoidHom = ψ.toAddMonoidHom.comp φ.toAddMonoidHom`
- **What**: The `toAddMonoidHom` of a composition is the composition of the individual homs.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 104–105 (proof: rfl)

### `theorem comp_apply`
- **Type**: `(ψ.comp φ).toAddMonoidHom P = ψ.toAddMonoidHom (φ.toAddMonoidHom P)`
- **What**: Pointwise: composition of isogenies composes the point maps.
- **How**: `rfl`.
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 107–108 (proof: rfl)

### `theorem comp_algebraMap_eq`
- **Type**: `(ψ.comp φ).pullback x = φ.pullback (ψ.pullback x)`
- **What**: The algebra map of the composition equals the composition of algebra maps.
- **How**: `rfl`.
- **Uses from project**: none
- **Used by**: `comp_degree` (line 127)
- **Visibility**: public
- **Lines**: 111–113 (proof: rfl)

### `theorem comp_degree` (set_option maxHeartbeats 800000)
- **Type**: `(ψ.comp φ).degree = φ.degree * ψ.degree`
- **What**: Degree multiplicativity: deg(ψ ∘ φ) = deg(φ) · deg(ψ), by the tower law for field extensions.
- **How**: Sets up `IsScalarTower W₃.FunctionField W₂.FunctionField W₁.FunctionField` using `comp_algebraMap_eq` (rfl), uses `Module.Free.of_divisionRing`, then applies `Module.finrank_mul_finrank`.
- **Hypotheses**: none beyond the isogenies.
- **Uses from project**: `comp_algebraMap_eq`
- **Used by**: `comp_degree_pos`, `Isogeny.zsmul_degree`, `Isogeny.zsmul_degree_pos`
- **Visibility**: public
- **Lines**: 119–133 (proof: 15 lines)
- **Notes**: `set_option maxHeartbeats 800000` — comment present: "The tower law for `FunctionField` needs extra heartbeats."

### `theorem comp_degree_pos`
- **Type**: `(hψ : 0 < ψ.degree) → (hφ : 0 < φ.degree) → 0 < (ψ.comp φ).degree`
- **What**: Composition of positive-degree isogenies has positive degree (no zero divisors in End E, degree form).
- **How**: `comp_degree` + `Nat.mul_pos`.
- **Uses from project**: `comp_degree`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 141–145 (proof: 3 lines)

### `noncomputable def id`
- **Type**: `(W : Affine F) [W.IsElliptic] → Isogeny W W`
- **What**: The identity isogeny: pullback = `AlgHom.id`, group hom = `AddMonoidHom.id`.
- **How**: Direct struct.
- **Uses from project**: none
- **Used by**: `id_toAddMonoidHom`, `id_pullback`, `id_degree`
- **Visibility**: public
- **Lines**: 150–152 (proof: 3 lines)

### `@[simp] theorem id_toAddMonoidHom`
- **Type**: `(Isogeny.id W).toAddMonoidHom = AddMonoidHom.id _`
- **How**: `rfl`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 154–155

### `@[simp] theorem id_pullback`
- **Type**: `(Isogeny.id W).pullback = AlgHom.id F W.FunctionField`
- **How**: `rfl`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 157–158

### `@[simp] theorem id_degree`
- **Type**: `(Isogeny.id W).degree = 1`
- **What**: The identity isogeny has degree 1.
- **How**: Unfolds to `Module.finrank W.FunctionField W.FunctionField _ _` with identity algebra, resolved by `Module.finrank_self`.
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 162–166 (proof: 5 lines)

### `def apply`
- **Type**: `(α : Isogeny W₁ W₂) → W₁.Point → W₂.Point`
- **What**: Apply an isogeny to a point (alias for `toAddMonoidHom`).
- **How**: `α.toAddMonoidHom P`.
- **Used by**: `apply_def`, `apply_add`, `apply_zero`, `apply_neg`, `apply_zsmul`, `asAddMonoidHom_apply`
- **Visibility**: public
- **Lines**: 171–172

### `@[simp] theorem apply_def`
- **Type**: `α.apply P = α.toAddMonoidHom P`
- **How**: `rfl`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 174–175

### `@[simp] theorem apply_add`
- **Type**: `α.apply (P + Q) = α.apply P + α.apply Q`
- **How**: `α.toAddMonoidHom.map_add P Q`.
- **Used by**: unused in file (simp)
- **Visibility**: public
- **Lines**: 185–187

### `@[simp] theorem apply_zero`
- **Type**: `α.apply (0 : W₁.Point) = 0`
- **How**: `α.toAddMonoidHom.map_zero`.
- **Used by**: unused in file (simp)
- **Visibility**: public
- **Lines**: 190–192

### `@[simp] theorem apply_neg`
- **Type**: `α.apply (-P) = -α.apply P`
- **How**: `α.toAddMonoidHom.map_neg P`.
- **Used by**: unused in file (simp)
- **Visibility**: public
- **Lines**: 195–197

### `theorem apply_zsmul`
- **Type**: `α.apply (n • P) = n • α.apply P`
- **How**: `α.toAddMonoidHom.map_zsmul P n`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 200–202

### `def asAddMonoidHom`
- **Type**: `(α : Isogeny W₁ W₂) → W₁.Point →+ W₂.Point`
- **What**: Bundles the group hom as a stable named `AddMonoidHom`; trivial wrapper.
- **Used by**: `asAddMonoidHom_apply`
- **Visibility**: public
- **Lines**: 206–207

### `@[simp] theorem asAddMonoidHom_apply`
- **Type**: `α.asAddMonoidHom P = α.apply P`
- **How**: `rfl`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 209–210

---

## `mulByInt` and infrastructure

### `noncomputable def mulByInt`
- **Type**: `(W : Affine F) [W.IsElliptic] → (n : ℤ) → Isogeny W W`
- **What**: The multiplication-by-n endomorphism [n] as an isogeny. Group hom = `zsmulAddGroupHom n`. Pullback = `mulByInt_pullbackAlgHom W n hn` when `n ≠ 0`; junk value `AlgHom.id` when `n = 0`.
- **How**: Direct `if hn : n = 0 then ... else ...` construction using the pullback from `MulByIntPullback`.
- **Hypotheses**: Curve elliptic; `n = 0` branch is a documented junk value (no theorem relies on it without `hn : n ≠ 0`).
- **Uses from project**: `mulByInt_pullbackAlgHom` (from `HasseWeil.MulByIntPullback`), `zsmulAddGroupHom`
- **Used by**: `mulByInt_apply`, `mulByInt_degree`, `mulByInt_degree_pos`, `mulByInt_degree_ne_zero`, `Isogeny.zsmul`, `torsionSubgroup`, `Isogeny.zsmul_degree_pos`
- **Visibility**: public
- **Lines**: 253–257 (proof: 5 lines)
- **Notes**: TODO noted in doc comment: construct pullback concretely via division polynomials; n=0 junk value extensively documented.

### `@[simp] theorem mulByInt_apply`
- **Type**: `(mulByInt W n).toAddMonoidHom P = n • P`
- **How**: `rfl`.
- **Used by**: `mem_torsionSubgroup`
- **Visibility**: public
- **Lines**: 259–260

---

## Private infrastructure section `DegreeInfra`

### `private noncomputable instance mulByInt_coordinateRing_module`
- **Type**: `Module F[X] W.toAffine.CoordinateRing`
- **What**: The coordinate ring is an F[X]-module via the algebra structure.
- **Used by**: `mulByInt_coordinateRing_finite`, `mulByInt_finrank_coordinateRing_eq_two`
- **Visibility**: private
- **Lines**: 277–279

### `private instance mulByInt_coordinateRing_finite`
- **Type**: `Module.Finite F[X] W.toAffine.CoordinateRing`
- **What**: The coordinate ring is finite as F[X]-module; proved via `Module.Finite.of_basis` using `Affine.CoordinateRing.basis`.
- **Uses from project**: `Affine.CoordinateRing.basis` (mathlib)
- **Used by**: `mulByInt_finrank_coordinateRing_eq_two`
- **Visibility**: private
- **Lines**: 281–283

### `private theorem mulByInt_finrank_coordinateRing_eq_two`
- **Type**: `Module.finrank F[X] W.toAffine.CoordinateRing = 2`
- **What**: The Weierstrass coordinate ring has F[X]-rank 2 (basis {1, Y}).
- **How**: `Module.finrank_eq_card_basis (Affine.CoordinateRing.basis W.toAffine)` + `Fintype.card_fin 2`.
- **Uses from project**: `Affine.CoordinateRing.basis` (mathlib)
- **Used by**: `mulByInt_isBaseChange_coordToFunc`, `WeierstrassCurve.degree_coordinateRing_over_polyX`, `mulByInt_finrank_functionField_eq_two`
- **Visibility**: private
- **Lines**: 285–288

### `private noncomputable instance mulByInt_faithfulSMul_poly_ff` (set_option synthInstance.maxHeartbeats 40000)
- **Type**: `FaithfulSMul F[X] W.toAffine.FunctionField`
- **What**: F[X] acts faithfully on the function field (the algebra map F[X]→K(E) is injective).
- **How**: Uses `IsFractionRing.injective` composed with `Affine.CoordinateRing.algebraMap_poly_injective`.
- **Uses from project**: `Affine.CoordinateRing.algebraMap_poly_injective` (mathlib)
- **Used by**: `mulByInt_isLocalization`
- **Visibility**: private
- **Lines**: 291–298 (proof: ~7 lines)
- **Notes**: `set_option synthInstance.maxHeartbeats 40000` — NO-COMMENT.

### `private noncomputable instance mulByInt_algebra_fracRing_ff`
- **Type**: `Algebra (FractionRing F[X]) W.toAffine.FunctionField`
- **What**: The function field is an algebra over the fraction field of F[X].
- **How**: `FractionRing.liftAlgebra`.
- **Used by**: `mulByInt_scalarTower_fracRing`, `mulByInt_finrank_functionField_eq_two`
- **Visibility**: private
- **Lines**: 300–302

### `private noncomputable instance mulByInt_scalarTower_fracRing`
- **Type**: `IsScalarTower F[X] (FractionRing F[X]) W.toAffine.FunctionField`
- **How**: `FractionRing.isScalarTower_liftAlgebra`.
- **Used by**: `mulByInt_isBaseChange_coordToFunc`, `mulByInt_finrank_functionField_eq_two`
- **Visibility**: private
- **Lines**: 304–306

### `private noncomputable instance mulByInt_isIntegral_poly_coord`
- **Type**: `Algebra.IsIntegral F[X] W.toAffine.CoordinateRing`
- **How**: `Algebra.IsIntegral.of_finite` (finite F[X]-module implies integral).
- **Used by**: `mulByInt_isLocalization`
- **Visibility**: private
- **Lines**: 308–310

### `private noncomputable instance mulByInt_faithfulSMul_poly_coord`
- **Type**: `FaithfulSMul F[X] W.toAffine.CoordinateRing`
- **How**: Uses `Affine.CoordinateRing.algebraMap_poly_injective`.
- **Used by**: `mulByInt_isLocalization`
- **Visibility**: private
- **Lines**: 312–316

### `private noncomputable instance mulByInt_isLocalization`
- **Type**: `IsLocalization (Algebra.algebraMapSubmonoid W.toAffine.CoordinateRing (nonZeroDivisors F[X])) W.toAffine.FunctionField`
- **What**: The function field is the localization of the coordinate ring at the image of nonzero divisors of F[X].
- **How**: Uses algebraicity + faithfulness to invoke `IsLocalization.iff_of_le_of_exists_dvd` and `Algebra.IsAlgebraic.isAlgebraic.exists_nonzero_dvd`.
- **Used by**: `mulByInt_isLocalizedModule`
- **Visibility**: private
- **Lines**: 318–334 (proof: ~16 lines)

### `private noncomputable instance mulByInt_isLocalizedModule`
- **Type**: `IsLocalizedModule (nonZeroDivisors F[X]) (IsScalarTower.toAlgHom F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField).toLinearMap`
- **How**: `isLocalizedModule_iff_isLocalization.mpr inferInstance`.
- **Used by**: `mulByInt_isBaseChange_coordToFunc`
- **Visibility**: private
- **Lines**: 336–340

### `private theorem mulByInt_isBaseChange_coordToFunc`
- **Type**: `IsBaseChange (FractionRing F[X]) (IsScalarTower.toAlgHom F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField).toLinearMap`
- **What**: The inclusion of the coordinate ring into the function field is a base change along `F[X] → FractionRing F[X]`.
- **How**: `isLocalizedModule_iff_isBaseChange.mp inferInstance`.
- **Used by**: `mulByInt_finrank_functionField_eq_two`
- **Visibility**: private
- **Lines**: 342–347

### `private theorem mulByInt_finrank_functionField_eq_two`
- **Type**: `Module.finrank (FractionRing F[X]) W.toAffine.FunctionField = 2`
- **What**: The function field has degree 2 over the rational function field K(x).
- **How**: `(mulByInt_isBaseChange_coordToFunc F W).finrank_eq` followed by `mulByInt_finrank_coordinateRing_eq_two`.
- **Uses from project**: `mulByInt_isBaseChange_coordToFunc`, `mulByInt_finrank_coordinateRing_eq_two`
- **Used by**: `WeierstrassCurve.degree_functionField_over_kx`, `mulByInt_finrank` (twice, for h_total and h_intermediate sub-lemmas)
- **Visibility**: private
- **Lines**: 351–354

### `theorem WeierstrassCurve.degree_functionField_over_kx`
- **Type**: `Module.finrank (FractionRing F[X]) W.toAffine.FunctionField = 2`
- **What**: Public name for `mulByInt_finrank_functionField_eq_two` (Silverman III.3.1.1): K(E) is a degree-2 extension of K(x).
- **How**: Direct delegation to the private theorem.
- **Uses from project**: `mulByInt_finrank_functionField_eq_two`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 364–366

### `theorem WeierstrassCurve.degree_coordinateRing_over_polyX`
- **Type**: `Module.finrank F[X] W.toAffine.CoordinateRing = 2`
- **What**: Public name: coordinate ring is a free F[X]-module of rank 2.
- **How**: Delegates to `mulByInt_finrank_coordinateRing_eq_two`.
- **Uses from project**: `mulByInt_finrank_coordinateRing_eq_two`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 371–373

---

## Section `MulByIntFinrank`

### `private noncomputable def mulByIntCompAlgHom`
- **Type**: `{n : ℤ} (hn : n ≠ 0) → FractionRing F[X] →ₐ[F] W.toAffine.FunctionField`
- **What**: The composite algebra hom `[n]* ∘ algebraMap`: sends K(x) into K(E) via pullback of [n], identifying K([n]*x) inside K(E).
- **How**: `(mulByInt_pullbackAlgHom W n hn).comp (IsScalarTower.toAlgHom ...)`.
- **Uses from project**: `mulByInt_pullbackAlgHom`
- **Used by**: `mulByIntFracRange`, `mulByIntFracRange_le_fieldRange`, `mulByIntCompAlgHom_algebraMap_X`, `mulByInt_finrank`
- **Visibility**: private
- **Lines**: 435–438

### `private noncomputable def mulByIntFracRange`
- **Type**: `{n : ℤ} (hn : n ≠ 0) → IntermediateField F W.toAffine.FunctionField`
- **What**: The intermediate field K([n]*x) = image of K(x) under [n]* inside K(E).
- **How**: `(mulByIntCompAlgHom W hn).fieldRange`.
- **Uses from project**: `mulByIntCompAlgHom`
- **Used by**: `mulByIntFracRange_le_fieldRange`, `mulByIntCompAlgHom_algebraMap_X`, `mulByInt_x_mem_mulByIntFracRange`, `mulByIntFracRange_eq_adjoin`, `mulByInt_finrank`
- **Visibility**: private
- **Lines**: 441–443

### `private theorem mulByIntFracRange_le_fieldRange`
- **Type**: `mulByIntFracRange W hn ≤ (mulByInt_pullbackAlgHom W n hn).fieldRange`
- **What**: K([n]*x) is contained in the full image [n]*K(E).
- **How**: Membership unfolding via `mulByIntFracRange`, `mulByIntCompAlgHom`; provides the preimage in `FractionRing F[X]` sent through `IsScalarTower.toAlgHom`.
- **Uses from project**: `mulByIntFracRange`, `mulByIntCompAlgHom`
- **Used by**: `mulByInt_finrank`
- **Visibility**: private
- **Lines**: 447–453

### `private noncomputable def mulByIntRangeEquiv`
- **Type**: `{n : ℤ} (hn : n ≠ 0) → W.toAffine.FunctionField ≃+* (mulByInt_pullbackAlgHom W n hn).fieldRange`
- **What**: The ring equivalence K(E) ≃ [n]*K(E) via the pullback (pullback is injective, so it's an iso onto its image).
- **How**: `AlgEquiv.ofInjective (mulByInt_pullbackAlgHom W n hn) ... .toRingEquiv`.
- **Used by**: `mulByInt_finrank`
- **Visibility**: private
- **Lines**: 456–460

### `private theorem mulByIntCompAlgHom_algebraMap_X`
- **Type**: `mulByIntCompAlgHom W hn (algebraMap F[X] (FractionRing F[X]) Polynomial.X) = mulByInt_x W n`
- **What**: The composite `[n]* ∘ algebraMap` sends the generator X to the x-coordinate formula `mulByInt_x = Φ_n/ΨSq_n`.
- **How**: Unfolds via `mulByInt_pullbackRingHom`, `IsLocalization.lift_eq`, `mulByInt_coordHom`, `AdjoinRoot.lift_mk`, and `mulByInt_xHom`, `mulByInt_x`.
- **Uses from project**: `mulByInt_pullbackAlgHom`, `mulByInt_pullbackRingHom`, `mulByInt_coordHom`, `mulByInt_xHom`, `mulByInt_x`, `mulByIntCompAlgHom`
- **Used by**: `mulByInt_x_mem_mulByIntFracRange`, `mulByIntFracRange_eq_adjoin`
- **Visibility**: private
- **Lines**: 464–491 (proof: ~27 lines)

### `private theorem mulByInt_x_mem_mulByIntFracRange`
- **Type**: `mulByInt_x W n ∈ mulByIntFracRange W hn`
- **What**: The x-coordinate Φ_n/ΨSq_n is in the intermediate field K([n]*x).
- **How**: Provides the witness `algebraMap F[X] (FractionRing F[X]) Polynomial.X` via `mulByIntCompAlgHom_algebraMap_X`.
- **Uses from project**: `mulByIntFracRange`, `mulByIntCompAlgHom_algebraMap_X`
- **Used by**: `mulByInt_finrank` (used in h_mulByInt_x_mem_aR and hj_inv_gen sub-steps)
- **Visibility**: private
- **Lines**: 494–498

### `private theorem adjoin_algebraMap_X_eq_top`
- **Type**: `IntermediateField.adjoin F ({algebraMap F[X] (FractionRing F[X]) Polynomial.X} : Set (FractionRing F[X])) = ⊤`
- **What**: The fraction field FractionRing F[X] is generated over F by the image of X (i.e., FractionRing F[X] = F(X)).
- **How**: Uses `IsFractionRing.div_surjective` to write any element as p/q, then shows algebraMap(p), algebraMap(q) lie in the adjoin via `Polynomial.aeval_mem_adjoin_singleton` with polynomial induction.
- **Hypotheses**: No IsElliptic needed (omit).
- **Uses from project**: none (pure mathlib)
- **Used by**: `mulByIntFracRange_eq_adjoin`
- **Visibility**: private
- **Lines**: 502–532 (proof: 31 lines)
- **Notes**: Proof strictly longer than 30 lines.

### `private theorem mulByIntFracRange_eq_adjoin`
- **Type**: `mulByIntFracRange W hn = IntermediateField.adjoin F ({mulByInt_x W n} : Set W.toAffine.FunctionField)`
- **What**: The intermediate field K([n]*x) equals F adjoin the x-coordinate Φ_n/ΨSq_n.
- **How**: Chains `AlgHom.fieldRange_eq_map`, substitutes `adjoin_algebraMap_X_eq_top`, applies `IntermediateField.adjoin_map` with singleton, then `mulByIntCompAlgHom_algebraMap_X`.
- **Uses from project**: `mulByIntFracRange`, `adjoin_algebraMap_X_eq_top`, `mulByIntCompAlgHom_algebraMap_X`
- **Used by**: `mulByInt_finrank` (for h_mid sub-lemmas)
- **Visibility**: private
- **Lines**: 536–550

### `private theorem max_natDegree_num_denom_mulByInt` (set_option maxHeartbeats 800000)
- **Type**: `max (num(Φ_n/ΨSq_n)).natDegree (denom(Φ_n/ΨSq_n)).natDegree = n.natAbs²`
- **What**: The max of numerator and denominator degrees of the division-polynomial ratio Φ_n/ΨSq_n equals n².
- **How**: Uses `ΨSq_poly_ne_zero`, `isCoprime_Φ_ΨSq`, `Polynomial.isUnit_iff`, then `RatFunc.num_div`, `RatFunc.denom_div`, and normalises via `degree_mulByN_eq_sq` from `MulByIntPullback`.
- **Hypotheses**: `n ≠ 0`, `W.Δ ≠ 0` (obtained from `W.coe_Δ'`), `DecidableEq F` omitted.
- **Uses from project**: `ΨSq_poly_ne_zero`, `isCoprime_Φ_ΨSq`, `degree_mulByN_eq_sq`, `mulByInt_x`, `Φ_ff`, `ΨSq_ff`
- **Used by**: `finrank_ratFunc_mulByInt`
- **Visibility**: private
- **Lines**: 554–586 (proof: 33 lines)
- **Notes**: `set_option maxHeartbeats 800000` — NO-COMMENT. Proof strictly longer than 30 lines.

### `private theorem finrank_ratFunc_mulByInt`
- **Type**: `Module.finrank (IntermediateField.adjoin F ({Φ_n/ΨSq_n} : Set (RatFunc F))) (RatFunc F) = n.natAbs²`
- **What**: [K(x) : K(Φ_n/ΨSq_n)] = n² in RatFunc F (via Lüroth-type degree formula).
- **How**: `RatFunc.finrank_eq_max_natDegree` applied to `max_natDegree_num_denom_mulByInt`.
- **Uses from project**: `max_natDegree_num_denom_mulByInt`
- **Used by**: `mulByInt_finrank` (line 764)
- **Visibility**: private
- **Lines**: 589–596

### `private theorem mulByInt_finrank` (set_option backward.isDefEq.respectTransparency false + set_option maxHeartbeats 1600000)
- **Type**: `Module.finrank (mulByInt_pullbackAlgHom W n hn).fieldRange W.toAffine.FunctionField = n.natAbs²`
- **What**: The function field has degree n² over [n]*K(E): the main algebraic fact driving `mulByInt_degree`.
- **How**: Tower law through K([n]*x) ≤ [n]*K(E) ≤ K(E). Sub-lemma 1 (h_total): [K(E) : K([n]*x)] = 2n² via tower through K(x), using `mulByInt_finrank_functionField_eq_two` for [K(E):K(x)]=2 and `finrank_ratFunc_mulByInt` for [K(x):K([n]*x)]=n², transferred via `Algebra.finrank_eq_of_equiv_equiv` with `FractionRing.algEquiv F[X] (RatFunc F)`. Sub-lemma 2 (h_intermediate): [[n]*K(E) : K([n]*x)] = 2 via `mulByInt_finrank_functionField_eq_two` again with `mulByIntRangeEquiv`. Conclude by `linarith` on `Module.finrank_mul_finrank`.
- **Uses from project**: `mulByIntFracRange_le_fieldRange`, `mulByIntFracRange`, `mulByIntFracRange_eq_adjoin`, `mulByInt_x_mem_mulByIntFracRange`, `mulByInt_finrank_functionField_eq_two`, `finrank_ratFunc_mulByInt`, `mulByIntCompAlgHom`, `mulByIntRangeEquiv`
- **Used by**: `mulByInt_degree`
- **Visibility**: private
- **Lines**: 600–791 (proof: 192 lines, with a large dead-code comment block 792–1115 inside the declaration)
- **Notes**: `set_option backward.isDefEq.respectTransparency false` (NO-COMMENT) and `set_option maxHeartbeats 1600000` (NO-COMMENT). Proof is 192 lines of active code, longest in the file. Lines 792–1115 are a `/-...-/` commented-out alternative proof draft parked inside the declaration.

---

## Public theorems on `mulByInt` degree

### `theorem mulByInt_degree` (set_option backward.isDefEq.respectTransparency false + set_option maxHeartbeats 800000)
- **Type**: `(n : ℤ) → (hn : n ≠ 0) → (mulByInt W n).degree = (n ^ 2).toNat`
- **What**: The degree of [n] is n² (Silverman III.4.2).
- **How**: Reduces to `mulByInt_finrank` by identifying `(mulByInt W n).degree` with the fieldRange finrank via `Algebra.finrank_eq_of_equiv_equiv` (using the `AlgEquiv.ofInjective` and `dif_neg hn` to extract the pullback).
- **Uses from project**: `mulByInt_finrank`, `toAlgebra`
- **Used by**: `mulByInt_degree_pos`, `mulByInt_degree_ne_zero`
- **Visibility**: public
- **Lines**: 1122–1152 (proof: 31 lines)
- **Notes**: `set_option backward.isDefEq.respectTransparency false` (NO-COMMENT) and `set_option maxHeartbeats 800000` (NO-COMMENT). Proof borderline 31 lines.

### `theorem mulByInt_degree_pos`
- **Type**: `(hn : n ≠ 0) → 0 < (mulByInt W n).degree`
- **How**: `mulByInt_degree` + `positivity` on `n^2 > 0` + `omega`.
- **Uses from project**: `mulByInt_degree`
- **Used by**: `mulByInt_degree_ne_zero`, `Isogeny.zsmul_degree_pos`
- **Visibility**: public
- **Lines**: 1158–1162

### `theorem mulByInt_degree_ne_zero`
- **Type**: `(hn : n ≠ 0) → (mulByInt W n).degree ≠ 0`
- **How**: `Nat.pos_iff_ne_zero.mp (mulByInt_degree_pos W hn)`.
- **Uses from project**: `mulByInt_degree_pos`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1166–1168

---

## Section `HomTorsionFree`

### `noncomputable def Isogeny.zsmul`
- **Type**: `(m : ℤ) → (φ : Isogeny W₁ W₂) → Isogeny W₁ W₂`
- **What**: The scalar action m • φ = [m]_{E₂} ∘ φ on Hom(E₁, E₂).
- **How**: `(mulByInt W₂ m).comp φ`.
- **Uses from project**: `mulByInt`, `comp`
- **Used by**: `Isogeny.zsmul_toAddMonoidHom`, `Isogeny.zsmul_apply`, `Isogeny.zsmul_degree`, `Isogeny.zsmul_degree_pos`
- **Visibility**: public
- **Lines**: 1186–1187

### `@[simp] theorem Isogeny.zsmul_toAddMonoidHom`
- **Type**: `(φ.zsmul m).toAddMonoidHom = (mulByInt W₂ m).toAddMonoidHom.comp φ.toAddMonoidHom`
- **How**: `rfl`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1190–1192

### `theorem Isogeny.zsmul_apply`
- **Type**: `(φ.zsmul m).toAddMonoidHom P = m • (φ.toAddMonoidHom P)`
- **How**: `simp [Isogeny.zsmul]`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1195–1197

### `theorem Isogeny.zsmul_degree`
- **Type**: `(φ.zsmul m).degree = φ.degree * (mulByInt W₂ m).degree`
- **How**: `Isogeny.comp_degree _ _`.
- **Uses from project**: `comp_degree`
- **Used by**: `Isogeny.zsmul_degree_pos`
- **Visibility**: public
- **Lines**: 1201–1203

### `theorem Isogeny.zsmul_degree_pos`
- **Type**: `(hφ : 0 < φ.degree) → (hm : m ≠ 0) → 0 < (φ.zsmul m).degree`
- **What**: Hom(E₁, E₂) is torsion-free (degree form): m•φ has positive degree if φ does and m ≠ 0.
- **How**: `Isogeny.zsmul_degree` + `Nat.mul_pos hφ (mulByInt_degree_pos W₂ hm)`.
- **Uses from project**: `Isogeny.zsmul_degree`, `mulByInt_degree_pos`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1210–1214

---

## Torsion subgroup

### `noncomputable def torsionSubgroup`
- **Type**: `(W : Affine F) [W.IsElliptic] → (m : ℤ) → AddSubgroup W.Point`
- **What**: The m-torsion subgroup E[m] = ker([m]) = {P ∈ E : m•P = O}.
- **How**: `(mulByInt W m).toAddMonoidHom.ker`.
- **Uses from project**: `mulByInt`
- **Used by**: `mem_torsionSubgroup`, `torsionSubgroup_one`, `torsionSubgroup_zero`, `torsionSubgroup_neg`, `torsionSubgroup_le_mul`, `torsionSubgroup_finite`, `torsionSubgroup_inf`; also via notation `E[m]`.
- **Visibility**: public
- **Lines**: 1222–1224

### `scoped notation:max E"["m"]"`
- **What**: Notation for `HasseWeil.torsionSubgroup E m`.
- **Lines**: 1226
- **Visibility**: scoped

### `@[simp] theorem mem_torsionSubgroup`
- **Type**: `P ∈ W[m] ↔ m • P = 0`
- **How**: Unfolds via `AddMonoidHom.mem_ker` + `mulByInt_apply`.
- **Uses from project**: `mulByInt_apply`
- **Used by**: `torsionSubgroup_one`, `torsionSubgroup_zero`, `torsionSubgroup_neg`, `torsionSubgroup_le_mul`, `torsionSubgroup_inf`
- **Visibility**: public
- **Lines**: 1228–1231

### `@[simp] theorem torsionSubgroup_one`
- **Type**: `W[(1 : ℤ)] = ⊥`
- **How**: `simp [mem_torsionSubgroup]`.
- **Uses from project**: `mem_torsionSubgroup`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1234–1237

### `@[simp] theorem torsionSubgroup_zero`
- **Type**: `W[(0 : ℤ)] = ⊤`
- **How**: `simp [mem_torsionSubgroup]`.
- **Uses from project**: `mem_torsionSubgroup`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1240–1243

### `theorem torsionSubgroup_neg`
- **Type**: `W[(-m)] = W[m]`
- **How**: `simp only [mem_torsionSubgroup, neg_zsmul, neg_eq_zero]`.
- **Uses from project**: `mem_torsionSubgroup`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1246–1249

### `theorem torsionSubgroup_le_mul`
- **Type**: `W[n] ≤ W[(m * n)]`
- **How**: `simp only [mem_torsionSubgroup]` + `rw [mul_smul, hP, smul_zero]`.
- **Uses from project**: `mem_torsionSubgroup`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1252–1256

### `instance torsionSubgroup_finite`
- **Type**: `[Finite W.Point] → Finite (W[m] : AddSubgroup W.Point)`
- **What**: Over a field with finite point group, every torsion subgroup is finite.
- **How**: `inferInstance` (subgroup of finite group is finite).
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1260–1262

### `theorem torsionSubgroup_inf`
- **Type**: `W[m] ⊓ W[n] = W[(m.gcd n : ℤ)]`
- **What**: The intersection of m- and n-torsion is the gcd-torsion.
- **How**: Forward: Bézout identity `Int.gcd_eq_gcd_ab` + `add_smul`/`mul_smul`; backward: divisibility `Int.gcd_dvd_left`/`gcd_dvd_right` + `mul_smul`.
- **Uses from project**: `mem_torsionSubgroup`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1266–1280 (proof: 15 lines)

---

## Bridge to endomorphism ring

### `def Isogeny.toEnd`
- **Type**: `(α : Isogeny W W) → AddMonoid.End W.Point`
- **What**: Forgets pullback/degree; returns just the group endomorphism.
- **How**: `α.toAddMonoidHom`.
- **Used by**: `Isogeny.toEnd_apply`
- **Visibility**: public
- **Lines**: 1286–1288

### `@[simp] theorem Isogeny.toEnd_apply`
- **Type**: `α.toEnd P = α.toAddMonoidHom P`
- **How**: `rfl`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1290–1292

---

## Summary statistics

| Category | Count |
|---|---|
| Total declarations | 67 |
| Defs (incl. structure, abbrev) | 14 |
| Lemmas/theorems | 43 |
| Instances | 10 |
| Public | 44 |
| Private | 23 |
| Sorries | 0 |
| `set_option maxHeartbeats` occurrences | 5 (4 distinct declarations) |

**Declarations unused within this file** (may be used by importers): `comp_toAddMonoidHom`, `comp_apply`, `comp_degree_pos`, `id_toAddMonoidHom`, `id_pullback`, `id_degree`, `apply_def`, `apply_add`, `apply_zero`, `apply_neg`, `apply_zsmul`, `asAddMonoidHom`, `asAddMonoidHom_apply`, `mulByInt_apply` (used only by `mem_torsionSubgroup`), `WeierstrassCurve.degree_functionField_over_kx`, `WeierstrassCurve.degree_coordinateRing_over_polyX`, `mulByInt_degree_ne_zero`, `Isogeny.zsmul_toAddMonoidHom`, `Isogeny.zsmul_apply`, `Isogeny.zsmul_degree_pos`, `torsionSubgroup_one`, `torsionSubgroup_zero`, `torsionSubgroup_neg`, `torsionSubgroup_le_mul`, `torsionSubgroup_finite`, `torsionSubgroup_inf`, `Isogeny.toEnd`, `Isogeny.toEnd_apply`.
