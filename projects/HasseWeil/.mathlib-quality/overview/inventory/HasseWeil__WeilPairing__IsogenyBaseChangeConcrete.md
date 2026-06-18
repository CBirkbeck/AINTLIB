# Inventory: ./HasseWeil/WeilPairing/IsogenyBaseChangeConcrete.lean

**File**: `HasseWeil/WeilPairing/IsogenyBaseChangeConcrete.lean`  
**Import**: `HasseWeil.WeilPairing.OneSubScaling`  
**Total declarations**: 29  
**Sorries**: 0 (axiom-clean)

---

## Namespace `Twist` (type-synonym machinery, lines 95–147)

### `def Twist`
- **Type**: `{R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B] (_f : B →ₐ[R] B) := B`
- **What**: Type synonym for `B` carrying the `f`-twisted `B`-module structure `b • x = f b * x`.
- **How**: Definitional alias; no proof.
- **Hypotheses**: `B` a semiring over `R`, `f` an `R`-algebra endomorphism.
- **Uses from project**: []
- **Used by**: All `Twist`-namespace declarations and `finrankBaseChange`.
- **Visibility**: public
- **Lines**: 96; 0-line proof (def-by-equation)
- **Notes**: None.

---

### `def Twist.toB`
- **Type**: `(x : Twist f) : B := x`
- **What**: Coercion `Twist f → B`; definitionally the identity.
- **How**: Definitional.
- **Hypotheses**: None (inherits `Twist` context).
- **Uses from project**: []
- **Used by**: `toB_injective`, `toB_ofB`, `smul_toB`, `toB_add`, `smul_toB_of_algebra`, `smul_toB_R`, `ofBₗ`, `finrankBaseChange`.
- **Visibility**: public
- **Lines**: 102; 0-line proof.
- **Notes**: None.

---

### `lemma Twist.toB_injective`
- **Type**: `Function.Injective (toB f)`
- **What**: The coercion `Twist f → B` is injective (trivially, since it is the identity).
- **How**: `fun _ _ h => h`
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `ofBₗ` (proof), `IsScalarTower R B (Twist f)` (proof), `finrankBaseChange` (extensively in sub-goal proofs).
- **Visibility**: public
- **Lines**: 103; 0-line proof.
- **Notes**: Key API — used in 3+ places.

---

### `def Twist.ofB`
- **Type**: `(x : B) : Twist f := x`
- **What**: The inverse coercion `B → Twist f`.
- **How**: Definitional.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `toB_ofB`, `ofB_add`, `ofBₗ`, `finrankBaseChange`.
- **Visibility**: public
- **Lines**: 105; 0-line proof.
- **Notes**: None.

---

### `@[simp] lemma Twist.toB_ofB`
- **Type**: `toB f (ofB f x) = x`
- **What**: Round-trip identity `toB ∘ ofB = id`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `finrankBaseChange` (simp).
- **Visibility**: public
- **Lines**: 106; 0-line proof.
- **Notes**: None.

---

### `instance : AddCommGroup (Twist f)`
- **Type**: `AddCommGroup (Twist f)`
- **What**: `Twist f` inherits the `AddCommGroup` structure of `B`.
- **How**: `inferInstanceAs`.
- **Hypotheses**: `B` a commutative ring.
- **Uses from project**: []
- **Used by**: (instance, used implicitly throughout).
- **Visibility**: public (anonymous instance)
- **Lines**: 108; 0-line proof.
- **Notes**: None.

---

### `noncomputable instance Twist.instModule`
- **Type**: `Module B (Twist f)`
- **What**: The twisted `B`-module on `Twist f`: scalar multiplication is `b • x = f b * x`, built by `RingHom.toModule f.toRingHom`.
- **How**: `RingHom.toModule (R := B) (S := B) f.toRingHom`.
- **Hypotheses**: `B` commutative ring.
- **Uses from project**: []
- **Used by**: `smul_toB`, `smul_toB_of_algebra`, `finrankBaseChange`.
- **Visibility**: public
- **Lines**: 111–112; 2 lines.
- **Notes**: None.

---

### `@[simp] lemma Twist.smul_toB`
- **Type**: `toB f (b • x) = f b * toB f x`
- **What**: Computes the image of the twisted scalar multiplication under `toB`.
- **How**: `rfl`.
- **Hypotheses**: None (follows from `instModule` definition).
- **Uses from project**: []
- **Used by**: `smul_toB_of_algebra`, `finrankBaseChange`.
- **Visibility**: public
- **Lines**: 114; 0-line proof.
- **Notes**: None.

---

### `@[simp] lemma Twist.toB_add`
- **Type**: `toB f (x + y) = toB f x + toB f y`
- **What**: `toB` is additive.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `finrankBaseChange`.
- **Visibility**: public
- **Lines**: 115; 0-line proof.
- **Notes**: None.

---

### `@[simp] lemma Twist.ofB_add`
- **Type**: `ofB f (x + y) = ofB f x + ofB f y`
- **What**: `ofB` is additive.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: (implicit, unused in file as explicit call, but used by simp).
- **Visibility**: public
- **Lines**: 116; 0-line proof.
- **Notes**: Unused in file as explicit call; potential dead code.

---

### `lemma Twist.smul_toB_of_algebra`
- **Type**: For `[IsScalarTower S B (Twist f)]`, `toB f (s • x) = f (algebraMap S B s) * toB f x`
- **What**: Computes the image under `toB` of the `S`-action on `Twist f`, reducing it to the `B`-action via `algebraMap S B`.
- **How**: `algebraMap_smul` plus `smul_toB`.
- **Hypotheses**: `S` a commutative ring with an algebra tower `S → B → Twist f`.
- **Uses from project**: []
- **Used by**: `finrankBaseChange` (the `map_smul'` proof of the forward `A`-linear map `l`).
- **Visibility**: public
- **Lines**: 119–122; 3 lines.
- **Notes**: None.

---

### `noncomputable instance Twist.instModuleR`
- **Type**: `Module R (Twist f)`
- **What**: The `R`-module structure on `Twist f`, obtained by restricting scalars along `algebraMap R B`.
- **How**: `Module.compHom (Twist f) (algebraMap R B)`.
- **Hypotheses**: `B` an `R`-algebra.
- **Uses from project**: []
- **Used by**: `smul_toB_R`, `ofBₗ`, `IsScalarTower` instance.
- **Visibility**: public
- **Lines**: 125; 1 line.
- **Notes**: None.

---

### `@[simp] lemma Twist.smul_toB_R`
- **Type**: `toB f (c • x) = f (algebraMap R B c) * toB f x`
- **What**: Computes the image of the `R`-action on `Twist f` under `toB`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `ofBₗ` proof.
- **Visibility**: public
- **Lines**: 127–128; 2 lines.
- **Notes**: None.

---

### `noncomputable def Twist.ofBₗ`
- **Type**: `B →ₗ[R] Twist f`
- **What**: The map `B → Twist f` (the inverse coercion `ofB`) packaged as an `R`-linear map, using that `f` fixes the image of `R` (i.e., `AlgHom.commutes`).
- **How**: `map_smul'` uses `toB_injective`, `smul_toB_R`, `Algebra.smul_def`, and `AlgHom.commutes`.
- **Hypotheses**: `B` an `R`-algebra.
- **Uses from project**: []
- **Used by**: `finrankBaseChange` (used to build the bilinear map `bil` for the inverse).
- **Visibility**: public
- **Lines**: 131–136; 6-line proof body.
- **Notes**: None.

---

### `instance : IsScalarTower R B (Twist f)`
- **Type**: `IsScalarTower R B (Twist f)`
- **What**: The canonical scalar-tower compatibility: `(c • a) • x = c • (a • x)` for `c : R`, `a : B`, `x : Twist f`.
- **How**: Unfolds using `Algebra.smul_def` and commutativity of scalar multiplication.
- **Hypotheses**: `B` a commutative ring over `R`.
- **Uses from project**: []
- **Used by**: `smul_toB_of_algebra` (typeclass), `finrankBaseChange` (via `iA_TwL_tower`).
- **Visibility**: public (anonymous instance)
- **Lines**: 138–143; 6-line proof body.
- **Notes**: None.

---

### `noncomputable instance Twist.instFree`
- **Type**: `Module.Free B (Twist f)` (for `F : Field`, `B : Field`)
- **What**: `Twist f` is a free `B`-module (since `B` is a division ring, every module is free).
- **How**: `Module.Free.of_divisionRing`.
- **Hypotheses**: `F` and `B` fields.
- **Uses from project**: []
- **Used by**: `finrankBaseChange` (implicitly, needed for `Module.finrank_baseChange` to apply).
- **Visibility**: public
- **Lines**: 145–146; 2 lines.
- **Notes**: The most general signature uses `Field R`, `Field B`; the main use in `finrankBaseChange` takes `A := C.toAffine.FunctionField` which is a field.

---

## Namespace `IsogenyBaseChangeConcrete` (lines 149–390)

### `noncomputable def tensorFunctionFieldEquiv`
- **Type**: `(L ⊗[F] C.toAffine.FunctionField) ≃ₐ[L] (C.baseChange L).toAffine.FunctionField`
- **What**: The scalar-extension isomorphism `Φ : L ⊗_F K(C) ≅ K(C_L)` as an `L`-algebra equivalence, built as the composite of the two shipped isos from `CurveMapBaseChange.lean`.
- **How**: Composes `C.functionField_tensor_locBaseChange L` (from `CurveMapBaseChange.lean`) and `C.functionField_baseChange_fracEquiv L` (also from there) via `AlgEquiv.trans`.
- **Hypotheses**: `C` a smooth plane curve over `F`, `L/F` an algebraic field extension.
- **Uses from project**: `SmoothPlaneCurve.isDomain_tensorCoordRing`, `SmoothPlaneCurve.functionField_tensor_locBaseChange`, `SmoothPlaneCurve.functionField_baseChange_fracEquiv`.
- **Used by**: `baseChangePullback`, `baseChangePullback_apply`, `symm_comp_baseChangePullback`, `finrank_baseChangePullback_eq_finrank_lTensorMap`.
- **Visibility**: public
- **Lines**: 164–167; 3-line body.
- **Notes**: Key API — used in 4+ places in this file. Also used by `WallAGenericRealization.lean`.

---

### `noncomputable def lTensorMap`
- **Type**: `(C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField) → (L ⊗[F] C.toAffine.FunctionField →ₐ[L] L ⊗[F] C.toAffine.FunctionField)`
- **What**: The `L`-linear scalar extension `id_L ⊗ f` of an `F`-algebra endomorphism `f`, defined as `Algebra.TensorProduct.map (AlgHom.id L L) f`.
- **How**: Direct application of `Algebra.TensorProduct.map`.
- **Hypotheses**: `f` an `F`-algebra endomorphism of the function field.
- **Uses from project**: []
- **Used by**: `lTensorMap_tmul`, `baseChangePullback`, `baseChangePullback_apply`, `symm_comp_baseChangePullback`, `finrank_baseChangePullback_eq_finrank_lTensorMap`, `FinrankBaseChange`, `finrankBaseChange`.
- **Visibility**: public
- **Lines**: 177–178; 2-line body.
- **Notes**: Key API — used in 6+ places in this file.

---

### `@[simp] theorem lTensorMap_tmul`
- **Type**: `lTensorMap C L f (l ⊗ₜ u) = l ⊗ₜ f u`
- **What**: The scalar extension acts on pure tensors by applying `f` to the second factor.
- **How**: `simp [lTensorMap]` unfolding `Algebra.TensorProduct.map_tmul`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: (not explicitly called in this file; potential use by downstream files via simp).
- **Visibility**: public
- **Lines**: 181–185; 5-line block including signature.
- **Notes**: Declared as simp lemma; not called explicitly within this file.

---

### `noncomputable def baseChangePullback`
- **Type**: `(C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField) → ((C.baseChange L).toAffine.FunctionField →ₐ[L] (C.baseChange L).toAffine.FunctionField)`
- **What**: The base-changed pullback `Φ ∘ (id_L ⊗ f) ∘ Φ⁻¹ : K(C_L) →ₐ[L] K(C_L)`, an honest `L`-algebra endomorphism requiring no `CoordHom`.
- **How**: Explicit composition of `tensorFunctionFieldEquiv.toAlgHom ∘ lTensorMap C L f ∘ tensorFunctionFieldEquiv.symm.toAlgHom`.
- **Hypotheses**: `f` an `F`-algebra endomorphism of `K(C)`, `L/F` algebraic.
- **Uses from project**: `tensorFunctionFieldEquiv`, `lTensorMap`, `SmoothPlaneCurve.isDomain_tensorCoordRing`.
- **Used by**: `baseChangePullback_apply`, `symm_comp_baseChangePullback`, `finrank_baseChangePullback_eq_finrank_lTensorMap`, `baseChangePullback_finrank_eq`, `oneSubFrobeniusPullback_L`, and downstream files.
- **Visibility**: public
- **Lines**: 192–197; 6-line body.
- **Notes**: Key API — main export of `IsogenyBaseChangeConcrete`.

---

### `theorem baseChangePullback_apply`
- **Type**: `baseChangePullback C L f z = tensorFunctionFieldEquiv C L (lTensorMap C L f ((tensorFunctionFieldEquiv C L).symm z))`
- **What**: Computes `baseChangePullback` pointwise as `Φ(id_L ⊗ f)(Φ⁻¹ z)`.
- **How**: `rfl` (definitional equality).
- **Hypotheses**: None beyond context variables.
- **Uses from project**: `tensorFunctionFieldEquiv`, `lTensorMap`, `baseChangePullback`.
- **Used by**: `symm_comp_baseChangePullback`.
- **Visibility**: public
- **Lines**: 199–204; 6-line block.
- **Notes**: None.

---

### `theorem symm_comp_baseChangePullback`
- **Type**: `(tensorFunctionFieldEquiv C L).symm (baseChangePullback C L f z) = lTensorMap C L f ((tensorFunctionFieldEquiv C L).symm z)`
- **What**: The conjugation square `Φ⁻¹ ∘ baseChangePullback = (id_L ⊗ f) ∘ Φ⁻¹`.
- **How**: `rw [baseChangePullback_apply, AlgEquiv.symm_apply_apply]`.
- **Hypotheses**: None beyond context variables.
- **Uses from project**: `tensorFunctionFieldEquiv`, `lTensorMap`, `baseChangePullback_apply`.
- **Used by**: `finrank_baseChangePullback_eq_finrank_lTensorMap`.
- **Visibility**: public
- **Lines**: 209–214; 6-line block.
- **Notes**: None.

---

### `theorem finrank_baseChangePullback_eq_finrank_lTensorMap`
- **Type**: `@Module.finrank (C.baseChange L).toAffine.FunctionField _ _ (baseChangePullback C L f).toRingHom.toAlgebra.toModule = @Module.finrank (L ⊗[F] C.toAffine.FunctionField) _ _ (lTensorMap C L f).toRingHom.toAlgebra.toModule`
- **What**: The conjugation step: the `K(C_L)`-module finrank via `baseChangePullback f` equals the `L ⊗ K(C)`-module finrank via `id_L ⊗ f`, by transporting finrank along `Φ⁻¹`.
- **How**: `Algebra.finrank_eq_of_equiv_equiv` with `i = j = Φ⁻¹`, with the compatibility square `symm_comp_baseChangePullback`.
- **Hypotheses**: None beyond context variables.
- **Uses from project**: `tensorFunctionFieldEquiv`, `lTensorMap`, `baseChangePullback`, `symm_comp_baseChangePullback`.
- **Used by**: `baseChangePullback_finrank_eq`.
- **Visibility**: public
- **Lines**: 228–244; 17 lines.
- **Notes**: None.

---

### `def FinrankBaseChange`
- **Type**: `(C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField) → Prop`
- **What**: The named proposition asserting that the `L ⊗ K(C)`-module finrank via `id_L ⊗ f` equals the `K(C)`-module finrank via `f` (base change of degree is an isomorphism invariant).
- **How**: Named `Prop` abbreviation (no proof content here).
- **Hypotheses**: None.
- **Uses from project**: `lTensorMap`.
- **Used by**: `finrankBaseChange` (as return type).
- **Visibility**: public
- **Lines**: 254–257; 4 lines.
- **Notes**: Helper `Prop` for readability only.

---

### `theorem finrankBaseChange`
- **Type**: `FinrankBaseChange C L f`
- **What**: Proves that base change `F → L` preserves the degree `[K(C) : f(K(C))]` of the field endomorphism `f`. Constructs an explicit `L ⊗ K(C)`-linear equivalence `(L ⊗ K(C)) ⊗_{K(C)} Twist f ≃ₗ[L ⊗ K(C)] Twist (id_L ⊗ f)` and applies `Module.finrank_baseChange`.
- **How**: Builds a forward map `eFwd = liftBaseChange` of `m ↦ 1 ⊗ m`, an explicit inverse `eInv` via `TensorProduct.lift` of the bilinear map `(s, a) ↦ (s⊗1) ⊗ₜ ofB a`, proves surjectivity (by induction on `L ⊗ K(C)` as a tensor product) and injectivity (via `eInv ∘ toB ∘ eFwd = id` by induction), forms `LinearEquiv.ofBijective`, then applies `Module.finrank_baseChange`.
- **Hypotheses**: `f` an `F`-algebra endomorphism, `L/F` algebraic, fields `F` and `K(C)`.
- **Uses from project**: `FinrankBaseChange` (return type); `Twist.*` namespace extensively.
- **Used by**: `baseChangePullback_finrank_eq`.
- **Visibility**: public
- **Lines**: 271–377; **105-line proof** (longest in file).
- **Notes**: `set_option maxHeartbeats 1600000` (no justifying comment present) + `set_option synthInstance.maxHeartbeats 400000` (no comment); `attribute [local instance] Algebra.TensorProduct.rightAlgebra in`. Proof >30 lines.

---

### `theorem baseChangePullback_finrank_eq`
- **Type**: `@Module.finrank (C.baseChange L).toAffine.FunctionField _ _ (baseChangePullback C L f).toRingHom.toAlgebra.toModule = @Module.finrank C.toAffine.FunctionField _ _ f.toRingHom.toAlgebra.toModule`
- **What**: Full degree preservation: the finrank of `K(C_L)` via `baseChangePullback f` equals the finrank of `K(C)` via `f`. Chains the conjugation step with the base-change-of-finrank fact.
- **How**: `(finrank_baseChangePullback_eq_finrank_lTensorMap C L f).trans (finrankBaseChange C L f)`.
- **Hypotheses**: None beyond context variables.
- **Uses from project**: `finrank_baseChangePullback_eq_finrank_lTensorMap`, `finrankBaseChange`.
- **Used by**: `oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange`.
- **Visibility**: public
- **Lines**: 382–389; 8-line block.
- **Notes**: One-liner proof (`.trans`).

---

## Section `OneSub` (lines 399–493)

### `noncomputable def oneSubFrobeniusPullback_L`
- **Type**: `(hq : 2 ≤ Fintype.card K) → ((W.baseChange L).toAffine.FunctionField →ₐ[L] (W.baseChange L).toAffine.FunctionField)`
- **What**: The concrete base-changed pullback of `1 − π` (the genuine separable isogeny `isogOneSub_negFrobenius`): the conjugate `Φ ∘ (id_L ⊗ (1−π).pullback) ∘ Φ⁻¹`. Supplies the `pullback_L` field of `OneSubScalingData` without any `CoordHom`.
- **How**: `baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) L (isogOneSub_negFrobenius W hq).pullback`.
- **Hypotheses**: `W` an elliptic curve over a finite field `K`, `L/K` an algebraic extension, `2 ≤ #K`.
- **Uses from project**: `baseChangePullback` (from `IsogenyBaseChangeConcrete`); `isogOneSub_negFrobenius` (from `Frobenius.lean`/`AdditionPullback.Frobenius`).
- **Used by**: `oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange`, `mkOneSubScalingDataConcrete`; also downstream `OneSubComapConcrete.lean`, `OneSubDualDivisor.lean`.
- **Visibility**: public
- **Lines**: 412–413; 2-line body.
- **Notes**: Main concrete payoff declaration for `pullback_L`.

---

### `theorem oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange`
- **Type**: `(oneSubFrobeniusIsogBaseChange W p r L (oneSubFrobeniusPullback_L W L hq)).degree = (isogOneSub_negFrobenius W hq).degree`
- **What**: Degree preservation for the concrete base-changed `1 − π`: the degree of the `K̄`-base-change of `1 − π` (built with `oneSubFrobeniusPullback_L`) equals the degree of the original `1 − π` over `K`.
- **How**: Chains `oneSubFrobeniusIsogBaseChange_degree_eq_of_finrank` (from `OneSubScaling.lean`) with `baseChangePullback_finrank_eq` applied to `(isogOneSub_negFrobenius W hq).pullback`.
- **Hypotheses**: `2 ≤ Fintype.card K`, everything from the `section OneSub` variables.
- **Uses from project**: `oneSubFrobeniusIsogBaseChange_degree_eq_of_finrank` (from `OneSubScaling.lean`); `oneSubFrobeniusPullback_L`; `baseChangePullback_finrank_eq`.
- **Used by**: `mkOneSubScalingDataConcrete`; also `OneSubProjOrdTransport.lean`, `OneSubWitnesses.lean`.
- **Visibility**: public
- **Lines**: 421–425; 5-line body.
- **Notes**: None.

---

### `noncomputable def mkOneSubScalingDataConcrete`
- **Type**: `(hq : 2 ≤ Fintype.card K) → finiteKer → hproj → δ → hdc → hsurj → hkerdeg → hcomm' → OneSubScalingData W p r L hq`
- **What**: Assembles a complete `OneSubScalingData` for the genuine base-changed `1 − π`, with `pullback_L` supplied concretely by `oneSubFrobeniusPullback_L` and `hdeg_bc` discharged by `oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange`. The remaining inputs are exactly the genuinely-deep K̄-level geometric residuals (`finiteKer`, `hproj`, `δ`/`hdc`, `hsurj`, `hkerdeg`, `hcomm'`).
- **How**: Direct `OneSubScalingData ... where` record construction, filling `pullback_L` and `hdeg_bc` from the concrete witnesses proved above.
- **Hypotheses**: `IsAlgClosed L`, `IsIntegrallyClosed (SmoothPlaneCurve L).CoordinateRing`, plus the 6 genuinely-deep geometric residuals as explicit parameters.
- **Uses from project**: `OneSubScalingData` (from `OneSubScaling.lean`); `oneSubFrobeniusPullback_L`; `oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange`; `oneSubFrobeniusIsogBaseChange` (from `OneSubScaling.lean`); `weilFunction`, `translateAlgEquivOfPoint`, `mulByInt`, `ProjOrdTransport`.
- **Used by**: `OneSubDualDivisor.lean`.
- **Visibility**: public
- **Lines**: 444–492; 49 lines total (signature 38 lines, body ~11 lines).
- **Notes**: Long signature due to 6 explicit geometric residual hypotheses; body itself is short.
