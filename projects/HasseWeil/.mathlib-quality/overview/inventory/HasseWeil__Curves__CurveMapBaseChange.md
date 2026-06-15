# Inventory: ./HasseWeil/Curves/CurveMapBaseChange.lean

**File summary**: 56 declarations total — 16 defs, 2 abbrevs, 16 instances (all at priority 100000), 22 theorems. No `sorry`. No `set_option maxHeartbeats`. The file builds the base-change infrastructure for function fields of smooth plane curves: `coordRingMap`, `functionFieldMap`, a scalar-extension equivalence `L ⊗_F C.CR ≃ L(C_L).CR`, and the chain `IsFractionRing (L⊗C.CR) (L⊗C.FF)` together with the localization-commutes-with-base-change iso.

---

## Namespace `HasseWeil.Curves.SmoothPlaneCurve` — basic base-change maps

### `noncomputable def coordRingMap`
- **Type**: `(L : Type*) [Field L] [Algebra F L] : C.CoordinateRing →+* (C.baseChange L).CoordinateRing`
- **What**: The ring hom on coordinate rings induced by the base-change `F → L`; concretely `CoordinateRing.map C.toAffine (algebraMap F L)`.
- **How**: One-liner applying `WeierstrassCurve.Affine.CoordinateRing.map`.
- **Hypotheses**: `C : SmoothPlaneCurve F`, `[Field F]`, `[Field L]`, `[Algebra F L]`.
- **Uses from project**: none (uses mathlib `CoordinateRing.map`).
- **Used by**: `coordRingMap_injective`, `functionFieldMap`, `coordRingMap_algebraMap_F`, `coordRingAlgHom`, `baseChangeXImage`, `baseChangeYImage`, `coordCompose`, `coordRingScalarExtFwd`, `fwdPinned`, and many others throughout this file and `WallAGenericRealization.lean`, `OmegaBaseChange.lean`.
- **Visibility**: public
- **Lines**: 40–42, proof length 1
- **Notes**: Key API — used by essentially everything in this file.

### `theorem coordRingMap_injective`
- **Type**: `Function.Injective (C.coordRingMap L)`
- **What**: The base-change ring hom on coordinate rings is injective (since `algebraMap F L` is injective for field extensions).
- **How**: `CoordinateRing.map_injective` applied to `FaithfulSMul.algebraMap_injective F L`.
- **Hypotheses**: As above.
- **Uses from project**: `coordRingMap`.
- **Used by**: `functionFieldMap`, `functionFieldMap_injective`.
- **Visibility**: public
- **Lines**: 44–47, proof length 3

### `noncomputable def functionFieldMap`
- **Type**: `C.FunctionField →+* (C.baseChange L).FunctionField`
- **What**: The induced field hom on function fields, lifted from `coordRingMap` via `IsFractionRing.map`.
- **How**: `IsFractionRing.map (C.coordRingMap_injective L)`.
- **Hypotheses**: As above.
- **Uses from project**: `coordRingMap_injective`.
- **Used by**: `functionFieldMap_injective`, `functionFieldMap_algebraMap`, `functionFieldMap_algebraMap_F`, `functionField_baseChange`, and external files `OmegaBaseChange.lean`, `WallAGenericRealization.lean`.
- **Visibility**: public
- **Lines**: 51–53, proof length 1

### `theorem functionFieldMap_injective`
- **Type**: `Function.Injective (C.functionFieldMap L)`
- **What**: The function-field base-change hom is injective (field homs between fields are injective).
- **How**: `(C.functionFieldMap L).injective` — ring hom from a field.
- **Hypotheses**: As above.
- **Uses from project**: `functionFieldMap`.
- **Used by**: unused within this file (used externally).
- **Visibility**: public
- **Lines**: 55–57, proof length 2

### `@[simp] theorem functionFieldMap_algebraMap`
- **Type**: `C.functionFieldMap L (algebraMap C.CoordinateRing C.FunctionField u) = algebraMap (C.baseChange L).CoordinateRing (C.baseChange L).FunctionField (C.coordRingMap L u)`
- **What**: `functionFieldMap` commutes with the localization structure map (algebraMap from coordinate ring).
- **How**: `IsLocalization.map_eq`.
- **Hypotheses**: As above, `u : C.CoordinateRing`.
- **Uses from project**: `functionFieldMap`.
- **Used by**: `functionFieldMap_algebraMap_F`.
- **Visibility**: public
- **Lines**: 59–65, proof length 5

---

## Namespace `CurveMap.CoordHom` — base change of coordinate ring homs

### `noncomputable def baseChangeXImage`
- **Type**: `(C₁.baseChange L).CoordinateRing`
- **What**: The L-base-changed image of where `cd.toAlgHom` sends the canonical `X`-class of `C₂.CoordinateRing`; this is where X of `(C₂.baseChange L).CR` maps under the base-changed alg hom.
- **How**: Applies `C₁.coordRingMap L` to `cd.toAlgHom (algebraMap (Polynomial F) C₂.CoordinateRing Polynomial.X)`.
- **Hypotheses**: `cd : φ.CoordHom`, `φ : CurveMap C₁ C₂`.
- **Uses from project**: `coordRingMap`.
- **Used by**: `baseChangeInnerAlgHom`, `baseChange_inner_comp_mapRingHom_eq`, `baseChange_eval₂_zero`, `baseChangeAlgHom`.
- **Visibility**: public
- **Lines**: 88–92, proof length 0 (term-mode def)

### `noncomputable def baseChangeYImage`
- **Type**: `(C₁.baseChange L).CoordinateRing`
- **What**: The L-base-changed image of the AdjoinRoot `root` (the Y-generator) of `C₂.CoordinateRing` under `cd.toAlgHom`.
- **How**: Applies `C₁.coordRingMap L` to `cd.toAlgHom (AdjoinRoot.root C₂.toAffine.polynomial)`.
- **Hypotheses**: As for `baseChangeXImage`.
- **Uses from project**: `coordRingMap`.
- **Used by**: `baseChange_eval₂_zero`, `baseChangeAlgHom`.
- **Visibility**: public
- **Lines**: 96–99, proof length 0 (term-mode def)

### `noncomputable def baseChangeInnerAlgHom`
- **Type**: `Polynomial L →ₐ[L] (C₁.baseChange L).CoordinateRing`
- **What**: The `L[X]`-algebra hom needed for `AdjoinRoot.liftAlgHom`: sends X to `baseChangeXImage`. This is `Polynomial.aeval (cd.baseChangeXImage L)`.
- **How**: `Polynomial.aeval`.
- **Hypotheses**: As for `baseChangeXImage`.
- **Uses from project**: `baseChangeXImage`.
- **Used by**: `baseChange_inner_comp_mapRingHom_eq`, `baseChange_eval₂_zero`, `baseChangeAlgHom`.
- **Visibility**: public
- **Lines**: 103–106, proof length 0 (term-mode def)

### `noncomputable abbrev coordCompose`
- **Type**: `C₂.CoordinateRing →+* (C₁.baseChange L).CoordinateRing`
- **What**: The composition `(C₁.coordRingMap L) ∘ cd.toAlgHom`; used as an intermediate in the `AdjoinRoot.liftAlgHom` construction.
- **How**: `(C₁.coordRingMap L).comp cd.toAlgHom.toRingHom`.
- **Hypotheses**: As for `baseChangeXImage`.
- **Uses from project**: `coordRingMap`.
- **Used by**: `baseChange_inner_comp_mapRingHom_eq`, `baseChange_eval₂_zero`.
- **Visibility**: public
- **Lines**: 110–113, proof length 0 (term-mode abbrev)

### `theorem coordRingMap_algebraMap_F`
- **Type**: `C.coordRingMap L (algebraMap F C.CoordinateRing a) = algebraMap F (C.baseChange L).CoordinateRing a`
- **What**: `coordRingMap` commutes with the base-field algebra map — pushing `a : F` through the coordinate ring of `C` or through the base-changed coordinate ring gives the same element.
- **How**: Uses `CoordinateRing.map_mk` to reduce to `AdjoinRoot.mk` expressions, then `Polynomial.map_C` twice; the RHS reduces to `rfl` via the algebra tower.
- **Hypotheses**: `a : F`.
- **Uses from project**: `coordRingMap`.
- **Used by**: `functionFieldMap_algebraMap_F`, `functionField_baseChange`, `baseChange_inner_comp_mapRingHom_eq`, `coordRingAlgHom`.
- **Visibility**: public (in `_root_` namespace)
- **Lines**: 118–137, proof length 20

### `theorem functionFieldMap_algebraMap_F`
- **Type**: `C.functionFieldMap L (algebraMap F C.FunctionField a) = algebraMap F (C.baseChange L).FunctionField a`
- **What**: `functionFieldMap` commutes with the base-field algebra map.
- **How**: Factors through `IsScalarTower.algebraMap_apply`, applies `functionFieldMap_algebraMap` and `coordRingMap_algebraMap_F`.
- **Hypotheses**: `a : F`.
- **Uses from project**: `functionFieldMap`, `functionFieldMap_algebraMap`, `coordRingMap_algebraMap_F`.
- **Used by**: `functionField_baseChange`.
- **Visibility**: public (in `_root_` namespace)
- **Lines**: 145–156, proof length 12

### `noncomputable def functionField_baseChange`
- **Type**: `C.FunctionField →ₐ[F] (C.baseChange L).FunctionField`
- **What**: The base-change inclusion of function fields packaged as an F-algebra hom (not just a ring hom).
- **How**: Wraps `functionFieldMap L` as `AlgHom.toFun`, using `functionFieldMap_algebraMap_F` for the `commutes'` field.
- **Hypotheses**: None beyond the standard.
- **Uses from project**: `functionFieldMap`, `functionFieldMap_algebraMap_F`.
- **Used by**: `functionField_baseChange_apply`; externally by `OmegaBaseChange.lean`.
- **Visibility**: public (in `_root_` namespace)
- **Lines**: 160–164, proof length 3 (structure)

### `@[simp] theorem functionField_baseChange_apply`
- **Type**: `C.functionField_baseChange L f = C.functionFieldMap L f`
- **What**: Definitional unfolding: the F-algebra hom `functionField_baseChange` applied to `f` equals `functionFieldMap L f`.
- **How**: `rfl`.
- **Hypotheses**: `f : C.FunctionField`.
- **Uses from project**: `functionField_baseChange`, `functionFieldMap`.
- **Used by**: unused within this file.
- **Visibility**: public (in `_root_` namespace)
- **Lines**: 166–169, proof length 1

### `theorem baseChange_inner_comp_mapRingHom_eq`
- **Type**: `(cd.baseChangeInnerAlgHom L).toRingHom.comp (Polynomial.mapRingHom (algebraMap F L)) = (cd.coordCompose L).comp (algebraMap (Polynomial F) C₂.CoordinateRing)`
- **What**: Commutativity identity showing that `baseChangeInnerAlgHom` composed with the polynomial-coefficient-map equals `coordCompose` composed with the structure map; this identifies the two routes through the polynomial diagram.
- **How**: `Polynomial.ringHom_ext` splits into the constant (`C a`) and the variable (`X`) cases; the constant case uses `Polynomial.aeval_C`, `AlgHom.commutes`, and `coordRingMap_algebraMap_F`; the variable case uses `Polynomial.aeval_X` and definitional equality.
- **Hypotheses**: `cd : φ.CoordHom`.
- **Uses from project**: `baseChangeInnerAlgHom`, `coordCompose`, `coordRingMap_algebraMap_F`, `baseChangeXImage`.
- **Used by**: `baseChange_eval₂_zero`.
- **Visibility**: public
- **Lines**: 171–205, proof length 35
- **Notes**: Proof is 35 lines (exceeds 30).

### `theorem baseChange_eval₂_zero`
- **Type**: `(C₂.toAffine.baseChange L).toAffine.polynomial.eval₂ (cd.baseChangeInnerAlgHom L).toRingHom (cd.baseChangeYImage L) = 0`
- **What**: The base-changed Weierstrass polynomial evaluates to zero at the proposed image point, verifying that the AdjoinRoot lift is well-defined.
- **How**: Rewrites the base-changed polynomial via `Affine.map_polynomial`, applies `Polynomial.eval₂_map`, then `baseChange_inner_comp_mapRingHom_eq` to factor out `coordCompose`, then `Polynomial.hom_eval₂` to pull out the ring hom, and finally `AdjoinRoot.eval₂_root` to get zero.
- **Hypotheses**: `cd : φ.CoordHom`.
- **Uses from project**: `baseChangeInnerAlgHom`, `baseChangeYImage`, `baseChange_inner_comp_mapRingHom_eq`, `coordCompose`.
- **Used by**: `baseChangeAlgHom`.
- **Visibility**: public
- **Lines**: 207–238, proof length 32
- **Notes**: Proof is 32 lines (exceeds 30). Key step: `Polynomial.hom_eval₂` allows factoring the ring hom out of `eval₂`.

### `noncomputable def baseChangeAlgHom`
- **Type**: `(C₂.baseChange L).CoordinateRing →ₐ[L] (C₁.baseChange L).CoordinateRing`
- **What**: The base-changed L-algebra hom on coordinate rings, lifting `cd.toAlgHom` along `F → L`; constructed via `AdjoinRoot.liftAlgHom`.
- **How**: `AdjoinRoot.liftAlgHom` with the inner hom `baseChangeInnerAlgHom` and value `baseChangeYImage`, justified by `baseChange_eval₂_zero`.
- **Hypotheses**: `cd : φ.CoordHom`.
- **Uses from project**: `baseChangeInnerAlgHom`, `baseChangeYImage`, `baseChange_eval₂_zero`.
- **Used by**: unused within this file; mentioned in comments in `OpenLemmas.lean` as a future target for injectivity.
- **Visibility**: public
- **Lines**: 242–248, proof length 3

---

## Namespace `SmoothPlaneCurve` — scalar-extension equivalence

### `noncomputable def coordRingAlgHom`
- **Type**: `C.CoordinateRing →ₐ[F] (C.baseChange L).CoordinateRing`
- **What**: `coordRingMap` packaged as an F-algebra hom (it commutes with `algebraMap F`, as proved by `coordRingMap_algebraMap_F`).
- **How**: Structure `toRingHom := C.coordRingMap L; commutes' := C.coordRingMap_algebraMap_F L`.
- **Hypotheses**: As standard.
- **Uses from project**: `coordRingMap`, `coordRingMap_algebraMap_F`.
- **Used by**: `coordRingAlgHom_apply`, `coordRingScalarExtFwd`, `fwdPinned`.
- **Visibility**: public
- **Lines**: 267–270, proof length 2

### `@[simp] theorem coordRingAlgHom_apply`
- **Type**: `C.coordRingAlgHom L u = C.coordRingMap L u`
- **What**: Definitional unfolding: `coordRingAlgHom` applied to `u` equals `coordRingMap L u`.
- **How**: `rfl`.
- **Uses from project**: `coordRingAlgHom`, `coordRingMap`.
- **Used by**: `fwdPinned_tmul`.
- **Visibility**: public
- **Lines**: 272–274, proof length 1

---

## Section `PhaseGInstances` — priority-100000 instance pins

### `noncomputable instance (priority := 100000) coordRingAlgebraBase`
- **Type**: `Algebra F C.toAffine.CoordinateRing`
- **What**: Pins the F-algebra structure on the coordinate ring at high priority to win the diamond against the F[X]-base route through `AdjoinRoot W.polynomial`.
- **How**: `inferInstance`.
- **Visibility**: public
- **Lines**: 292–294

### `noncomputable instance (priority := 100000) coordRingModuleBase`
- **Type**: `Module F C.toAffine.CoordinateRing`
- **What**: Pins the F-module structure (from `Algebra.toModule`) at high priority.
- **How**: `Algebra.toModule`.
- **Visibility**: public
- **Lines**: 297–299

### `noncomputable instance (priority := 100000) tensorCoordRingCommRing`
- **Type**: `CommRing (L ⊗[F] C.toAffine.CoordinateRing)`
- **What**: Pins the `CommRing` on `L ⊗[F] C.CR` to unblock signatures mentioning this type.
- **How**: `Algebra.TensorProduct.instCommRing`.
- **Visibility**: public
- **Lines**: 306–309

### `noncomputable instance (priority := 100000) tensorCoordRingLAlgebra`
- **Type**: `Algebra L (L ⊗[F] C.toAffine.CoordinateRing)`
- **What**: Pins the L-algebra structure (left factor) on `L ⊗[F] C.CR`.
- **How**: `Algebra.TensorProduct.leftAlgebra`.
- **Visibility**: public
- **Lines**: 312–315

### `noncomputable instance (priority := 100000) tensorCoordRingFAlgebra`
- **Type**: `Algebra F (L ⊗[F] C.toAffine.CoordinateRing)`
- **What**: Pins the F-algebra structure on `L ⊗[F] C.CR` (canonical `Algebra.TensorProduct.instAlgebra`), compatible with `TensorProduct.ext'`.
- **How**: `Algebra.TensorProduct.instAlgebra`.
- **Visibility**: public
- **Lines**: 323–326

### `noncomputable instance (priority := 100000) tensorCoordRingFLScalarTower`
- **Type**: `IsScalarTower F L (L ⊗[F] C.toAffine.CoordinateRing)`
- **What**: Pins the scalar tower `F → L → L ⊗[F] C.CR`.
- **How**: `inferInstance`.
- **Visibility**: public
- **Lines**: 329–332

### `noncomputable instance (priority := 100000) tensorFunctionFieldFAlgebra`
- **Type**: `Algebra F (L ⊗[F] C.toAffine.FunctionField)`
- **What**: Pins the F-algebra structure on `L ⊗[F] C.FF`.
- **How**: `Algebra.TensorProduct.instAlgebra`.
- **Visibility**: public
- **Lines**: 337–340

### `noncomputable instance (priority := 100000) tensorFunctionFieldFLScalarTower`
- **Type**: `IsScalarTower F L (L ⊗[F] C.toAffine.FunctionField)`
- **What**: Pins the scalar tower `F → L → L ⊗[F] C.FF`.
- **How**: `inferInstance`.
- **Visibility**: public
- **Lines**: 343–346

### `noncomputable instance (priority := 100000) tensorFunctionFieldCommRing`
- **Type**: `CommRing (L ⊗[F] C.toAffine.FunctionField)`
- **What**: Pins the `CommRing` on `L ⊗[F] C.FF`.
- **How**: `Algebra.TensorProduct.instCommRing`.
- **Visibility**: public
- **Lines**: 354–357

### `noncomputable instance (priority := 100000) tensorFunctionFieldLAlgebra`
- **Type**: `Algebra L (L ⊗[F] C.toAffine.FunctionField)`
- **What**: Pins the L-algebra structure (left factor) on `L ⊗[F] C.FF`.
- **How**: `Algebra.TensorProduct.leftAlgebra`.
- **Visibility**: public
- **Lines**: 361–364

### `noncomputable instance (priority := 100000) tensorCoordRingCommRing'`
- **Type**: `CommRing (C.toAffine.CoordinateRing ⊗[F] L)`
- **What**: Pins the `CommRing` on the reversed tensor `C.CR ⊗[F] L` (needed for `Algebra.TensorProduct.isField_of_isAlgebraic` which uses this orientation).
- **How**: `Algebra.TensorProduct.instCommRing`.
- **Visibility**: public
- **Lines**: 375–378

### `noncomputable instance (priority := 100000) tensorCoordRingFAlgebra'`
- **Type**: `Algebra F (C.toAffine.CoordinateRing ⊗[F] L)`
- **What**: Pins the F-algebra on the reversed coordinate-ring tensor.
- **How**: `Algebra.TensorProduct.instAlgebra`.
- **Visibility**: public
- **Lines**: 381–384

### `noncomputable instance (priority := 100000) tensorCoordRingLeftAlgebra'`
- **Type**: `Algebra C.toAffine.CoordinateRing (C.toAffine.CoordinateRing ⊗[F] L)`
- **What**: Pins the `C.CR`-algebra structure (left factor) on `C.CR ⊗[F] L`.
- **How**: `Algebra.TensorProduct.leftAlgebra`.
- **Visibility**: public
- **Lines**: 387–390

### `noncomputable instance (priority := 100000) tensorCoordRingFLeftScalarTower'`
- **Type**: `IsScalarTower F C.toAffine.CoordinateRing (C.toAffine.CoordinateRing ⊗[F] L)`
- **What**: Pins the scalar tower `F → C.CR → C.CR ⊗[F] L`; built explicitly via `IsScalarTower.of_algebraMap_eq` because `inferInstance` fails on this reversed-order path.
- **How**: `IsScalarTower.of_algebraMap_eq fun x => rfl`.
- **Visibility**: public
- **Lines**: 395–398

### `noncomputable instance (priority := 100000) tensorFunctionFieldCommRing'`
- **Type**: `CommRing (C.toAffine.FunctionField ⊗[F] L)`
- **What**: Pins the `CommRing` on the reversed function-field tensor.
- **How**: `Algebra.TensorProduct.instCommRing`.
- **Visibility**: public
- **Lines**: 401–404

### `noncomputable instance (priority := 100000) tensorFunctionFieldFAlgebra'`
- **Type**: `Algebra F (C.toAffine.FunctionField ⊗[F] L)`
- **What**: Pins the F-algebra on the reversed function-field tensor.
- **How**: `Algebra.TensorProduct.instAlgebra`.
- **Visibility**: public
- **Lines**: 407–410

---

## Scalar-extension forward direction and bijectivity

### `noncomputable def coordRingScalarExtFwd`
- **Type**: (inferred) `L ⊗[F] C.toAffine.CoordinateRing →ₐ[L] (C.baseChange L).toAffine.CoordinateRing`
- **What**: The forward direction of the scalar-extension equivalence `L ⊗_F C.CR →ₐ[L] (C.baseChange L).CR`, constructed via `AlgHom.liftEquiv` (universal property of base change). Result type omitted to avoid instance-path mismatches.
- **How**: `AlgHom.liftEquiv F L C.toAffine.CoordinateRing (C.baseChange L).toAffine.CoordinateRing (C.coordRingAlgHom L)`.
- **Uses from project**: `coordRingAlgHom`.
- **Used by**: `coordRingScalarExtFwd_tmul`, `coordRingScalarExtFwd_one_tmul`, `coordRingScalarExtFwd_surjective`, `coordRingScalarExtFwd_injective`, `coordRingScalarExt`.
- **Visibility**: public
- **Lines**: 424–427, proof length 2

### `@[simp] theorem coordRingScalarExtFwd_tmul`
- **Type**: `C.coordRingScalarExtFwd L (l ⊗ₜ u) = l • C.coordRingMap L u`
- **What**: Simplification rule: the forward map on simple tensors acts as left-scalar times `coordRingMap`.
- **How**: `AlgHom.liftEquiv_tmul`.
- **Uses from project**: `coordRingScalarExtFwd`, `coordRingAlgHom`, `coordRingMap`.
- **Used by**: `coordRingScalarExtFwd_one_tmul`, `coordRingScalarExt_tmul`.
- **Visibility**: public
- **Lines**: 429–432, proof length 2

### `@[simp] theorem coordRingScalarExtFwd_one_tmul`
- **Type**: `C.coordRingScalarExtFwd L (1 ⊗ₜ u) = C.coordRingMap L u`
- **What**: Specialization: `coordRingScalarExtFwd L (1 ⊗ₜ u) = coordRingMap L u`.
- **How**: `coordRingScalarExtFwd_tmul` + `one_smul`.
- **Uses from project**: `coordRingScalarExtFwd_tmul`, `coordRingMap`.
- **Used by**: `coordRingScalarExtFwd_surjective`, `coordRingScalarExtFwd_injective`.
- **Visibility**: public
- **Lines**: 435–438, proof length 3

### `theorem coordRingScalarExtFwd_surjective`
- **Type**: `Function.Surjective (C.coordRingScalarExtFwd L)`
- **What**: The forward scalar-extension map is surjective: every element of the base-changed coordinate ring is in the image.
- **How**: Shows the range contains `root W_L.polynomial` (via `coordRingScalarExtFwd_one_tmul` + `CoordinateRing.map_mk` + `Polynomial.map_X`) and the X-generator (similar), then applies `AdjoinRoot.adjoinRoot_eq_top` via `Algebra.adjoin_eq_adjoin_union` and `Polynomial.adjoin_X` to show these generators span the codomain.
- **Hypotheses**: As standard.
- **Uses from project**: `coordRingScalarExtFwd`, `coordRingScalarExtFwd_one_tmul`.
- **Used by**: `coordRingScalarExt`.
- **Visibility**: public
- **Lines**: 456–515, proof length 60
- **Notes**: Proof is 60 lines (exceeds 30). Key mathlib lemma: `Algebra.adjoin_eq_adjoin_union` with `Polynomial.adjoin_X` and `AdjoinRoot.adjoinRoot_eq_top`.

### `theorem coordRingScalarExtFwd_injective`
- **Type**: `Function.Injective (C.coordRingScalarExtFwd L)`
- **What**: The forward scalar-extension map is injective, proved by showing it carries a basis `bLA` of `L ⊗[F] C.CR` (over `L`) to a basis `bD` of `(C.baseChange L).CR` bijectively.
- **How**: Constructs the F-basis `bA` of `C.CR` via `Polynomial.basisMonomials.smulTower CoordinateRing.basis`; induces `bLA` on `L ⊗[F] C.CR` via `Algebra.TensorProduct.basis L bA`; constructs `bD` on `(C.baseChange L).CR` analogously. Shows `coordRingScalarExtFwd` carries `bLA(n,i) ↦ bD(n,i)` using `map_smul`, `Polynomial.map_pow`, `Polynomial.map_X`, and `CoordinateRing.map_mk`. Concludes injectivity via `Basis.equiv ... injective`.
- **Hypotheses**: `classical` (decidability).
- **Uses from project**: `coordRingScalarExtFwd`, `coordRingScalarExtFwd_one_tmul`, `coordRingMap`.
- **Used by**: `coordRingScalarExt`.
- **Visibility**: public
- **Lines**: 538–596, proof length 59
- **Notes**: Proof is 59 lines (exceeds 30). The `hbasis` sub-proof uses `WeierstrassCurve.Affine.CoordinateRing.map_smul`, `CoordinateRing.basis_zero`, `CoordinateRing.basis_one`, `CoordinateRing.map_mk`.

### `noncomputable def coordRingScalarExt`
- **Type**: (inferred) `L ⊗[F] C.toAffine.CoordinateRing ≃ₐ[L] (C.baseChange L).toAffine.CoordinateRing`
- **What**: The scalar-extension `AlgEquiv` on coordinate rings, packaged from the bijectivity of `coordRingScalarExtFwd`. Result type omitted intentionally to avoid `Semiring` diamond.
- **How**: `AlgEquiv.ofBijective (C.coordRingScalarExtFwd L) ⟨inj, surj⟩`.
- **Uses from project**: `coordRingScalarExtFwd`, `coordRingScalarExtFwd_injective`, `coordRingScalarExtFwd_surjective`.
- **Used by**: `coordRingScalarExt_tmul`; mentioned in comments as the basis for the narrowed residual for `functionFieldScalarExt`.
- **Visibility**: public
- **Lines**: 606–608, proof length 2

### `@[simp] theorem coordRingScalarExt_tmul`
- **Type**: `C.coordRingScalarExt L (l ⊗ₜ u) = l • C.coordRingMap L u`
- **What**: `coordRingScalarExt` on simple tensors equals left scalar times `coordRingMap`.
- **How**: `coordRingScalarExtFwd_tmul`.
- **Uses from project**: `coordRingScalarExt`, `coordRingScalarExtFwd_tmul`, `coordRingMap`.
- **Used by**: unused within this file.
- **Visibility**: public
- **Lines**: 610–613, proof length 2

---

## Pinned-instance forward direction (`fwdPinned`)

### `noncomputable def fwdPinned`
- **Type**: `(L ⊗[F] C.toAffine.CoordinateRing) →ₐ[L] (C.baseChange L).toAffine.CoordinateRing`
- **What**: Forward scalar-extension alg hom built against the pinned instances via `Algebra.TensorProduct.lift` (so its domain uses the pinned `CommRing`), needed for `IsFractionRing.algEquivOfAlgEquiv`.
- **How**: `Algebra.TensorProduct.lift (Algebra.ofId L ...) ((C.coordRingAlgHom L).restrictScalars F) (commutativity of images)`.
- **Uses from project**: `coordRingAlgHom`.
- **Used by**: `fwdPinned_tmul`, `fwdPinned_surjective`, `fwdPinned_injective`, `coordRingScalarExtPinned`, `isDomain_tensorCoordRing`.
- **Visibility**: public
- **Lines**: 629–634, proof length 3

### `@[simp] theorem fwdPinned_tmul`
- **Type**: `C.fwdPinned L (l ⊗ₜ u) = l • C.coordRingMap L u`
- **What**: `fwdPinned` on simple tensors: `l ⊗ₜ u ↦ l • coordRingMap u`.
- **How**: `Algebra.TensorProduct.lift_tmul` + `Algebra.ofId_apply` + `Algebra.smul_def`.
- **Uses from project**: `fwdPinned`, `coordRingAlgHom`, `coordRingMap`, `coordRingAlgHom_apply`.
- **Used by**: `fwdPinned_surjective`, `fwdPinned_injective`.
- **Visibility**: public
- **Lines**: 636–641, proof length 5

### `theorem fwdPinned_surjective`
- **Type**: `Function.Surjective (C.fwdPinned L)`
- **What**: `fwdPinned` is surjective, by the same adjoin argument as `coordRingScalarExtFwd_surjective`: root and X-generator are in the range, and they generate the codomain over L.
- **How**: Mirrors `coordRingScalarExtFwd_surjective` with `fwdPinned_tmul` + `one_smul` instead of `coordRingScalarExtFwd_one_tmul`. Uses `AdjoinRoot.adjoinRoot_eq_top` via `Algebra.adjoin_eq_adjoin_union`.
- **Uses from project**: `fwdPinned`, `fwdPinned_tmul`, `coordRingMap`.
- **Used by**: `coordRingScalarExtPinned`.
- **Visibility**: public
- **Lines**: 646–688, proof length 43
- **Notes**: Proof is 43 lines (exceeds 30). Substantial duplication with `coordRingScalarExtFwd_surjective` (the two proofs are almost identical, differing only in which `_tmul` lemma is invoked).

### `theorem fwdPinned_injective`
- **Type**: `Function.Injective (C.fwdPinned L)`
- **What**: `fwdPinned` is injective, by the basis-transport argument: it carries basis `bLA` of `L ⊗[F] C.CR` to basis `bD` of `(C.baseChange L).CR` vector by vector.
- **How**: Exact mirror of `coordRingScalarExtFwd_injective` with `fwdPinned_tmul` + `one_smul` in place of `coordRingScalarExtFwd_one_tmul`. Uses `Polynomial.basisMonomials.smulTower CoordinateRing.basis` for both bases, `CoordinateRing.map_smul`, `Polynomial.map_pow`, `CoordinateRing.map_mk`, `Basis.equiv`.
- **Hypotheses**: `classical`.
- **Uses from project**: `fwdPinned`, `fwdPinned_tmul`, `coordRingMap`.
- **Used by**: `coordRingScalarExtPinned`, `isDomain_tensorCoordRing`.
- **Visibility**: public
- **Lines**: 720–772, proof length 53
- **Notes**: Proof is 53 lines (exceeds 30). Nearly verbatim duplication of `coordRingScalarExtFwd_injective`.

### `noncomputable def coordRingScalarExtPinned`
- **Type**: `(L ⊗[F] C.toAffine.CoordinateRing) ≃ₐ[L] (C.baseChange L).toAffine.CoordinateRing`
- **What**: `fwdPinned` packaged as an `AlgEquiv` (bijective) against the pinned instances; suitable for `IsFractionRing.algEquivOfAlgEquiv`.
- **How**: `AlgEquiv.ofBijective (C.fwdPinned L) ⟨inj, surj⟩`.
- **Uses from project**: `fwdPinned`, `fwdPinned_injective`, `fwdPinned_surjective`.
- **Used by**: `isDomain_tensorCoordRing` (indirectly), `functionField_baseChange_fracEquiv`, and externally by `WallAGenericRealization.lean`.
- **Visibility**: public
- **Lines**: 777–780, proof length 2

### `theorem isDomain_tensorCoordRing`
- **Type**: `IsDomain (L ⊗[F] C.toAffine.CoordinateRing)`
- **What**: `L ⊗[F] C.CR` is an integral domain, transported from the coordinate ring `(C.baseChange L).CR` (a domain) via injectivity of `fwdPinned`.
- **How**: `Function.Injective.isDomain (C.fwdPinned L).toRingHom (C.fwdPinned_injective L)`.
- **Uses from project**: `fwdPinned`, `fwdPinned_injective`.
- **Used by**: `functionField_baseChange_fracEquiv`, `functionField_baseChange_tensorEquiv`, `tensor_functionField_isField`, `tensor_functionField_surj`, `tensor_functionField_isFractionRing`, `functionField_tensor_locBaseChange`.
- **Visibility**: public
- **Lines**: 784–786, proof length 2

---

## Function-field scalar-extension iso

### `noncomputable def functionField_baseChange_fracEquiv`
- **Type**: `FractionRing (L ⊗[F] C.toAffine.CoordinateRing) ≃ₐ[L] (C.baseChange L).toAffine.FunctionField` (with `isDomain_tensorCoordRing` in scope)
- **What**: The function-field base-change iso `FractionRing(L ⊗[F] C.CR) ≃ₐ[L] K(C_L)`, constructed via `IsFractionRing.algEquivOfAlgEquiv` applied to `coordRingScalarExtPinned`.
- **How**: `IsFractionRing.algEquivOfAlgEquiv (C.coordRingScalarExtPinned L)`, with `isDomain_tensorCoordRing` providing the domain instance.
- **Uses from project**: `isDomain_tensorCoordRing`, `coordRingScalarExtPinned`.
- **Used by**: `functionField_baseChange_tensorEquiv`; externally by `WallAGenericRealization.lean`.
- **Visibility**: public
- **Lines**: 798–803, proof length 5

### `noncomputable def functionField_baseChange_tensorEquiv`
- **Type**: `(C.baseChange L).toAffine.FunctionField ≃ₐ[L] FractionRing (L ⊗[F] C.toAffine.CoordinateRing)` (with `isDomain_tensorCoordRing` in scope)
- **What**: The symm of `functionField_baseChange_fracEquiv`: sends `K(C_L)` to `FractionRing(L ⊗[F] C.CR)`. This is the orientation needed by the Route-B degree-transport.
- **How**: `(C.functionField_baseChange_fracEquiv L).symm`.
- **Uses from project**: `isDomain_tensorCoordRing`, `functionField_baseChange_fracEquiv`.
- **Used by**: unused within this file.
- **Visibility**: public
- **Lines**: 819–824, proof length 5

### `noncomputable def tensorFunctionFieldStructureHom`
- **Type**: `(L ⊗[F] C.toAffine.CoordinateRing) →ₐ[L] (L ⊗[F] C.toAffine.FunctionField)`
- **What**: The natural base-changed localization map `L ⊗[F] C.CR →ₐ[L] L ⊗[F] C.FF` (the `lTensor` of the localization map), packaged as an L-algebra hom.
- **How**: `Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom F C.CR C.FF)`.
- **Uses from project**: none (pure mathlib).
- **Used by**: `tensorFunctionFieldAlgebra`, `tensorFunctionFieldStructureHom_injective`, `tensor_functionField_isFractionRing`, `functionField_tensor_locBaseChange`.
- **Visibility**: public
- **Lines**: 830–833, proof length 1

### `noncomputable abbrev tensorFunctionFieldAlgebra`
- **Type**: `Algebra (L ⊗[F] C.toAffine.CoordinateRing) (L ⊗[F] C.toAffine.FunctionField)`
- **What**: The `L ⊗[F] C.CR`-algebra structure on `L ⊗[F] C.FF` via the natural localization map `tensorFunctionFieldStructureHom`. Bundled so residual theorems share one algebra-instance spelling.
- **How**: `(C.tensorFunctionFieldStructureHom L).toRingHom.toAlgebra`.
- **Uses from project**: `tensorFunctionFieldStructureHom`.
- **Used by**: `tensor_functionField_surj`, `tensor_functionField_isFractionRing`, `functionField_tensor_locBaseChange`.
- **Visibility**: public
- **Lines**: 839–841, proof length 0

### `theorem tensorFunctionFieldStructureHom_injective`
- **Type**: `Function.Injective (algebraMap (L ⊗[F] C.toAffine.CoordinateRing) (L ⊗[F] C.toAffine.FunctionField))` (with `tensorFunctionFieldAlgebra` pinned)
- **What**: The base-changed localization structure map is injective, via `Module.Flat.lTensor_preserves_injective_linearMap`: `L/F` is flat (free field extension), so `lTensor L` preserves the injection `C.CR → C.FF`.
- **How**: Defines `gF : C.CR →ₗ[F] C.FF` as the localization map restricted to F-scalars; proves `gF` injective via `IsFractionRing.injective`; proves `lTensor L gF` injective via `Module.Flat.lTensor_preserves_injective_linearMap` (flatness of L over F); shows `tensorFunctionFieldStructureHom` and `lTensor L gF` agree as plain functions by induction on simple tensors (`TensorProduct.induction_on`); concludes by transferring injectivity.
- **Uses from project**: `tensorFunctionFieldStructureHom`, `tensorFunctionFieldAlgebra`.
- **Used by**: `tensor_functionField_isFractionRing`.
- **Visibility**: public
- **Lines**: 863–894, proof length 32
- **Notes**: Proof is 32 lines (exceeds 30). Key lemma: `Module.Flat.lTensor_preserves_injective_linearMap` + `Module.Flat.of_free`.

### `theorem tensor_functionField_isField`
- **Type**: `IsField (L ⊗[F] C.toAffine.FunctionField)` (needs `[Algebra.IsAlgebraic F L]`)
- **What**: The tensor `L ⊗[F] C.FF` is a field, given algebraic `L/F`. This is the geometric-integrality content: `F` is algebraically closed in `C.FF`, so `C.FF ⊗_F L` is a field for algebraic extensions.
- **How**: Sets up `C.CR ⊗[F] L` as a domain (via `Algebra.TensorProduct.comm` applied to `isDomain_tensorCoordRing`); establishes `C.FF ⊗[F] L` as a localization of `C.CR ⊗[F] L` at the image of `(C.CR)⁰` via `IsLocalization.tensorProduct_tensorProduct`; shows `C.FF ⊗[F] L` is a domain via `IsLocalization.isDomain_of_le_nonZeroDivisors`; applies `Algebra.TensorProduct.isField_of_isAlgebraic` (mathlib geometric-integrality lemma) to get `IsField (C.FF ⊗[F] L)`; transports along `Algebra.TensorProduct.comm` to the `L ⊗[F] C.FF` orientation.
- **Hypotheses**: `[Algebra.IsAlgebraic F L]`.
- **Uses from project**: `isDomain_tensorCoordRing`.
- **Used by**: `tensor_functionField_isFractionRing`.
- **Visibility**: public
- **Lines**: 979–1046, proof length 68
- **Notes**: Proof is 68 lines (exceeds 30). Key mathlib lemma: `Algebra.TensorProduct.isField_of_isAlgebraic`, `IsLocalization.tensorProduct_tensorProduct`, `IsLocalization.isDomain_of_le_nonZeroDivisors`. Uses several `letI`/`haveI` local instance bindings to avoid the `AdjoinRoot` diamond in the reversed-order tensor.

### `theorem tensor_functionField_surj`
- **Type**: `∀ z : L ⊗[F] C.FF, ∃ x : ... × nonZeroDivisors ..., z * algebraMap ... x.2 = algebraMap ... x.1` (surjectivity onto fractions)
- **What**: Every element of `L ⊗[F] C.FF` is expressible as a fraction `a/b` with `a : L ⊗[F] C.CR` and `b` a nonzero-divisor; this is the "localization-surjectivity" field of `IsFractionRing`.
- **How**: Induction on `z` via `TensorProduct.induction_on`: zero case trivial; simple tensor `l ⊗ₜ f` uses `IsFractionRing.div_surjective` to write `f = a/b` in `C.FF`, then combines via `Algebra.TensorProduct.tmul_mul_tmul`; addition uses common denominator `dx * dy` via `linear_combination`. The nonzero-divisor property of `1 ⊗ₜ b` is proved using `Module.Flat.rTensor_preserves_injective_linearMap`.
- **Uses from project**: `tensorFunctionFieldAlgebra`, `isDomain_tensorCoordRing`.
- **Used by**: `tensor_functionField_isFractionRing`.
- **Visibility**: public
- **Lines**: 1056–1125, proof length 70
- **Notes**: Proof is 70 lines (exceeds 30). Key lemma: `IsFractionRing.div_surjective`, `Module.Flat.rTensor_preserves_injective_linearMap`.

### `theorem tensor_functionField_isFractionRing`
- **Type**: `@IsFractionRing (L ⊗[F] C.toAffine.CoordinateRing) _ (L ⊗[F] C.toAffine.FunctionField) _ (C.tensorFunctionFieldAlgebra L)` (needs `[Algebra.IsAlgebraic F L]`)
- **What**: `L ⊗[F] C.FF` is the fraction ring of `L ⊗[F] C.CR` (with the pinned algebra structure). Assembles the three components: injectivity of the structure map, surjectivity onto fractions, and injectivity of the algebraMap-equals relation.
- **How**: `rw [IsFractionRing, isLocalization_iff]`; supplies three fields from `tensorFunctionFieldStructureHom_injective`, `tensor_functionField_surj`, and `tensor_functionField_isField` (field ⟹ every nonzero maps to a unit).
- **Hypotheses**: `[Algebra.IsAlgebraic F L]`.
- **Uses from project**: `tensorFunctionFieldAlgebra`, `isDomain_tensorCoordRing`, `tensorFunctionFieldStructureHom_injective`, `tensor_functionField_isField`, `tensor_functionField_surj`.
- **Used by**: `functionField_tensor_locBaseChange`.
- **Visibility**: public
- **Lines**: 1127–1151, proof length 25

### `noncomputable def functionField_tensor_locBaseChange`
- **Type**: `(L ⊗[F] C.toAffine.FunctionField) ≃ₐ[L] FractionRing (L ⊗[F] C.toAffine.CoordinateRing)` (needs `[Algebra.IsAlgebraic F L]`, with `isDomain_tensorCoordRing`)
- **What**: Localization commutes with base change: `L ⊗_F Frac(C.CR) ≃ₐ[L] Frac(L ⊗_F C.CR)`. Constructed via uniqueness of localizations.
- **How**: Applies `IsLocalization.algEquiv` (uniqueness: both `L ⊗ C.FF` and `FractionRing(L ⊗ C.CR)` are localizations of the domain `L ⊗ C.CR` at its nonzero-divisors), restricted to L-scalars via `.restrictScalars L`.
- **Hypotheses**: `[Algebra.IsAlgebraic F L]`.
- **Uses from project**: `isDomain_tensorCoordRing`, `tensorFunctionFieldAlgebra`, `tensor_functionField_isFractionRing`, `tensorFunctionFieldStructureHom`.
- **Used by**: unused within this file; externally by `WallAGenericRealization.lean`.
- **Visibility**: public
- **Lines**: 1176–1192, proof length 17

---

## Summary table

| Declaration | Kind | Lines | Sorry | Long proof |
|---|---|---|---|---|
| `coordRingMap` | def | 40–42 | no | no |
| `coordRingMap_injective` | thm | 44–47 | no | no |
| `functionFieldMap` | def | 51–53 | no | no |
| `functionFieldMap_injective` | thm | 55–57 | no | no |
| `functionFieldMap_algebraMap` | thm | 59–65 | no | no |
| `baseChangeXImage` | def | 88–92 | no | no |
| `baseChangeYImage` | def | 96–99 | no | no |
| `baseChangeInnerAlgHom` | def | 103–106 | no | no |
| `coordCompose` | abbrev | 110–113 | no | no |
| `coordRingMap_algebraMap_F` | thm | 118–137 | no | no |
| `functionFieldMap_algebraMap_F` | thm | 145–156 | no | no |
| `functionField_baseChange` | def | 160–164 | no | no |
| `functionField_baseChange_apply` | thm | 166–169 | no | no |
| `baseChange_inner_comp_mapRingHom_eq` | thm | 171–205 | no | 35 lines |
| `baseChange_eval₂_zero` | thm | 207–238 | no | 32 lines |
| `baseChangeAlgHom` | def | 242–248 | no | no |
| `coordRingAlgHom` | def | 267–270 | no | no |
| `coordRingAlgHom_apply` | thm | 272–274 | no | no |
| `coordRingAlgebraBase` | inst | 292–294 | no | no |
| `coordRingModuleBase` | inst | 297–299 | no | no |
| `tensorCoordRingCommRing` | inst | 306–309 | no | no |
| `tensorCoordRingLAlgebra` | inst | 312–315 | no | no |
| `tensorCoordRingFAlgebra` | inst | 323–326 | no | no |
| `tensorCoordRingFLScalarTower` | inst | 329–332 | no | no |
| `tensorFunctionFieldFAlgebra` | inst | 337–340 | no | no |
| `tensorFunctionFieldFLScalarTower` | inst | 343–346 | no | no |
| `tensorFunctionFieldCommRing` | inst | 354–357 | no | no |
| `tensorFunctionFieldLAlgebra` | inst | 361–364 | no | no |
| `tensorCoordRingCommRing'` | inst | 375–378 | no | no |
| `tensorCoordRingFAlgebra'` | inst | 381–384 | no | no |
| `tensorCoordRingLeftAlgebra'` | inst | 387–390 | no | no |
| `tensorCoordRingFLeftScalarTower'` | inst | 395–398 | no | no |
| `tensorFunctionFieldCommRing'` | inst | 401–404 | no | no |
| `tensorFunctionFieldFAlgebra'` | inst | 407–410 | no | no |
| `coordRingScalarExtFwd` | def | 424–427 | no | no |
| `coordRingScalarExtFwd_tmul` | thm | 429–432 | no | no |
| `coordRingScalarExtFwd_one_tmul` | thm | 435–438 | no | no |
| `coordRingScalarExtFwd_surjective` | thm | 456–515 | no | 60 lines |
| `coordRingScalarExtFwd_injective` | thm | 538–596 | no | 59 lines |
| `coordRingScalarExt` | def | 606–608 | no | no |
| `coordRingScalarExt_tmul` | thm | 610–613 | no | no |
| `fwdPinned` | def | 629–634 | no | no |
| `fwdPinned_tmul` | thm | 636–641 | no | no |
| `fwdPinned_surjective` | thm | 646–688 | no | 43 lines |
| `fwdPinned_injective` | thm | 720–772 | no | 53 lines |
| `coordRingScalarExtPinned` | def | 777–780 | no | no |
| `isDomain_tensorCoordRing` | thm | 784–786 | no | no |
| `functionField_baseChange_fracEquiv` | def | 798–803 | no | no |
| `functionField_baseChange_tensorEquiv` | def | 819–824 | no | no |
| `tensorFunctionFieldStructureHom` | def | 830–833 | no | no |
| `tensorFunctionFieldAlgebra` | abbrev | 839–841 | no | no |
| `tensorFunctionFieldStructureHom_injective` | thm | 863–894 | no | 32 lines |
| `tensor_functionField_isField` | thm | 979–1046 | no | 68 lines |
| `tensor_functionField_surj` | thm | 1056–1125 | no | 70 lines |
| `tensor_functionField_isFractionRing` | thm | 1127–1151 | no | no |
| `functionField_tensor_locBaseChange` | def | 1176–1192 | no | no |
