# Inventory: ./HasseWeil/EC/IsogenyAG.lean

**File**: `HasseWeil/EC/IsogenyAG.lean`
**Lines**: 654
**Imports**: `HasseWeil.Curves.PointFunctor`, `HasseWeil.Curves.Infinity`, `HasseWeil.MulByIntPullback`, `HasseWeil.FrobeniusIsogeny`, `Mathlib.FieldTheory.Finite.Basic`

---

## Summary

This file defines the algebro-geometric isogeny structure for elliptic curves following Silverman III.4.
The central design decision is that `CoordHom` (coordinate-ring lift) is **not** a field of `Isogeny`
but is supplied separately; this accommodates `[n]` whose affine pullback has poles at torsion points.
The `AddMonoidHom` property (Silverman III.4.8) is likewise a theorem, not structural data.

---

## Declarations

---

### `structure Isogeny`

- **Type**: `Isogeny (W₁ W₂ : Affine F) [W₁.IsElliptic] [W₂.IsElliptic]` extends `Curves.CurveMap ⟨W₁⟩ ⟨W₂⟩` with field `pullback_ordAtInfty_nonneg`
- **What**: The isogeny structure between two elliptic Weierstrass curves over `F`. Packages a function-field pullback (from `CurveMap`) together with a basepoint-preservation condition: the pullback of any function regular at ∞ is again regular at ∞.
- **How**: Structure definition; the basepoint condition captures "defined at O" at the level of `ordAtInfty`.
- **Hypotheses**: Both curves must be elliptic (`IsElliptic`).
- **Uses from project**: `Curves.CurveMap`, `Curves.SmoothPlaneCurve.ordAtInfty`
- **Used by**: All subsequent declarations in the file (it is the central type).
- **Visibility**: public
- **Lines**: 66–76, structure body ~11 lines
- **Notes**: The `pullback_ordAtInfty_nonneg` field is weaker than strict `φ(O)=O` (it only requires nonneg→nonneg, not pos→pos). A comment notes this caveat and flags a potential future strengthening.

---

### `theorem pullback_injective`

- **Type**: `(φ : Isogeny W₁ W₂) → Function.Injective φ.toCurveMap.pullback`
- **What**: The function-field pullback of any isogeny is injective.
- **How**: Immediate delegation to `CurveMap.pullback_injective`.
- **Hypotheses**: Both curves elliptic.
- **Uses from project**: `Curves.CurveMap.pullback_injective`
- **Used by**: unused in file (exported API)
- **Visibility**: public
- **Lines**: 83–85, proof length 1 line
- **Notes**: Dead-code candidate within this file; likely used by other files importing IsogenyAG.

---

### `noncomputable abbrev degree`

- **Type**: `(φ : Isogeny W₁ W₂) → ℕ`
- **What**: The degree of an isogeny: the degree `[K(E₁) : φ*K(E₂)]` of the function-field extension. Inherited from `CurveMap`.
- **How**: Transparent abbrev delegating to `φ.toCurveMap.degree`.
- **Hypotheses**: Both curves elliptic.
- **Uses from project**: `CurveMap.degree`
- **Used by**: `compose_degree` (215), `WithHom.degree` (513), `WithHom.compose_degree` (557)
- **Visibility**: public
- **Lines**: 90, 1 line
- **Notes**: None.

---

### `noncomputable abbrev separableDegree`

- **Type**: `(φ : Isogeny W₁ W₂) → ℕ`
- **What**: The separable degree of an isogeny (degree of the separable closure of `φ*K(E₂)` in `K(E₁)`). Inherited from `CurveMap`.
- **How**: Transparent abbrev.
- **Hypotheses**: Both curves elliptic.
- **Uses from project**: `CurveMap.separableDegree`
- **Used by**: unused in file (exported API)
- **Visibility**: public
- **Lines**: 93–94, 1 line
- **Notes**: Dead-code candidate within this file.

---

### `noncomputable abbrev inseparableDegree`

- **Type**: `(φ : Isogeny W₁ W₂) → ℕ`
- **What**: The inseparable degree of an isogeny. Inherited from `CurveMap`.
- **How**: Transparent abbrev.
- **Hypotheses**: Both curves elliptic.
- **Uses from project**: `CurveMap.inseparableDegree`
- **Used by**: unused in file (exported API)
- **Visibility**: public
- **Lines**: 97–98, 1 line
- **Notes**: Dead-code candidate within this file.

---

### `abbrev IsSeparable`

- **Type**: `(φ : Isogeny W₁ W₂) → Prop`
- **What**: Predicate: an isogeny is separable iff its inseparable degree is 1. Inherited from `CurveMap`.
- **How**: Transparent abbrev.
- **Hypotheses**: Both curves elliptic.
- **Uses from project**: `CurveMap.IsSeparable`
- **Used by**: unused in file (exported API)
- **Visibility**: public
- **Lines**: 101, 1 line
- **Notes**: Dead-code candidate within this file.

---

### `abbrev IsPurelyInseparable`

- **Type**: `(φ : Isogeny W₁ W₂) → Prop`
- **What**: Predicate: an isogeny is purely inseparable iff its separable degree is 1. Inherited from `CurveMap`.
- **How**: Transparent abbrev.
- **Hypotheses**: Both curves elliptic.
- **Uses from project**: `CurveMap.IsPurelyInseparable`
- **Used by**: unused in file (exported API)
- **Visibility**: public
- **Lines**: 104–105, 1 line
- **Notes**: Dead-code candidate within this file.

---

### `noncomputable def toPointMap`

- **Type**: `(φ : Isogeny W₁ W₂) → φ.toCurveMap.CoordHom → W₁.Point → W₂.Point`
- **What**: The induced map on rational points, parametrized by an external coordinate-ring witness. Sends `Point.zero` to `Point.zero`; sends an affine point `(x,y)` through `CurveMap.toPointMap` and then promotes via `SmoothPoint.toAffinePoint`.
- **How**: Pattern matching on `Point`; the affine case delegates to `CurveMap.toPointMap coordHom` applied to the smooth-point lift.
- **Hypotheses**: Requires a `CoordHom` witness (external).
- **Uses from project**: `Curves.CurveMap.toPointMap`, `Curves.SmoothPoint.toAffinePoint`
- **Used by**: `toPointMap_zero` (120), `toPointMap_some` (124), `id_toPointMap_zero` (147), `id_toPointMap` (153), `compose_toPointMap_zero` (194), `compose_toPointMap` (201), `toAddMonoidHomOfWitness` (241, via `map_zero'`), `AddHomProperty` (234), `id_AddHomProperty` (256), `compose_AddHomProperty` (263), `frobenius_toPointMap` (327), `id_toAddMonoidHom_apply` (528), `compose_toAddMonoidHom_apply` (547), `frobenius_toAddMonoidHom_apply` (628)
- **Visibility**: public
- **Lines**: 114–118, definition body ~5 lines
- **Notes**: Key API — used by the most declarations in the file (14+).

---

### `@[simp] theorem toPointMap_zero`

- **Type**: `(φ : Isogeny W₁ W₂) → (coordHom : φ.toCurveMap.CoordHom) → φ.toPointMap coordHom .zero = .zero`
- **What**: The induced point map sends the basepoint to the basepoint.
- **How**: `rfl` (holds by definition of `toPointMap`).
- **Hypotheses**: None beyond the isogeny.
- **Uses from project**: `toPointMap`
- **Used by**: `toAddMonoidHomOfWitness` (line 246, as `map_zero'`)
- **Visibility**: public (simp)
- **Lines**: 120–122, proof 1 line
- **Notes**: None.

---

### `@[simp] theorem toPointMap_some`

- **Type**: `(φ : Isogeny W₁ W₂) → (coordHom) → {x y : F} → (h : W₁.Nonsingular x y) → φ.toPointMap coordHom (.some x y h) = (φ.toCurveMap.toPointMap coordHom ⟨x,y,h⟩).toAffinePoint`
- **What**: Unfolds `toPointMap` at an affine point to the `CurveMap.toPointMap` computation.
- **How**: `rfl`.
- **Hypotheses**: None beyond the isogeny and a nonsingular affine point.
- **Uses from project**: `toPointMap`, `CurveMap.toPointMap`
- **Used by**: unused in file (exported simp lemma)
- **Visibility**: public (simp)
- **Lines**: 124–128, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `noncomputable def id`

- **Type**: `(W : Affine F) → [W.IsElliptic] → Isogeny W W`
- **What**: The identity isogeny on `W`. Its pullback is `AlgHom.id`; the basepoint condition holds trivially since the pullback fixes every function.
- **How**: `toCurveMap := Curves.CurveMap.id ⟨W⟩`; `pullback_ordAtInfty_nonneg _ h := h`.
- **Hypotheses**: `W` is elliptic.
- **Uses from project**: `Curves.CurveMap.id`
- **Used by**: `id_toCurveMap` (138), `id_toPointMap_zero` (147), `id_toPointMap` (153), `id_degree` (166), `id_AddHomProperty` (256), `WithHom.id` (518), `id_toAddMonoidHom_apply` (528), `id_compose_toAddMonoidHom` (594), `compose_id_toAddMonoidHom` (600)
- **Visibility**: public
- **Lines**: 134–136, definition body 3 lines
- **Notes**: None.

---

### `@[simp] theorem id_toCurveMap`

- **Type**: `(Isogeny.id W).toCurveMap = Curves.CurveMap.id ⟨W⟩`
- **What**: The underlying `CurveMap` of the identity isogeny is the identity `CurveMap`.
- **How**: `rfl`.
- **Hypotheses**: `W` elliptic.
- **Uses from project**: `id` (Isogeny), `Curves.CurveMap.id`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 138–139, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `noncomputable def idCoordHom`

- **Type**: `(W : Affine F) → [W.IsElliptic] → (Isogeny.id W).toCurveMap.CoordHom`
- **What**: The canonical coordinate-ring witness for the identity isogeny: the identity `AlgHom` on the coordinate ring.
- **How**: Delegates to `Curves.CurveMap.CoordHom.id ⟨W⟩`.
- **Hypotheses**: `W` elliptic.
- **Uses from project**: `id`, `Curves.CurveMap.CoordHom.id`
- **Used by**: `id_toPointMap_zero` (147), `id_toPointMap` (153), `id_AddHomProperty` (256), `WithHom.id` (518), `id_coordHom_eq` (524), `id_toAddMonoidHom_apply` (528)
- **Visibility**: public
- **Lines**: 142–144, definition body 2 lines
- **Notes**: None.

---

### `@[simp] theorem id_toPointMap_zero`

- **Type**: `(Isogeny.id W).toPointMap (idCoordHom W) .zero = .zero`
- **What**: The identity isogeny sends the basepoint to itself.
- **How**: `rfl`.
- **Hypotheses**: `W` elliptic.
- **Uses from project**: `id`, `idCoordHom`, `toPointMap`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 147–148, proof 1 line
- **Notes**: Dead-code candidate within this file (subsumes `toPointMap_zero` for the identity case).

---

### `@[simp] theorem id_toPointMap`

- **Type**: `∀ P : W.Point, (Isogeny.id W).toPointMap (idCoordHom W) P = P`
- **What**: The identity isogeny acts as the identity function on all rational points.
- **How**: Cases on `P`; the `zero` case is `rfl`; the `some` case rewrites via `Curves.CurveMap.toPointMap_id` and `rfl`.
- **Hypotheses**: `W` elliptic. `set_option maxHeartbeats 800000` (no justifying comment).
- **Uses from project**: `id`, `idCoordHom`, `toPointMap`, `Curves.CurveMap.toPointMap_id`
- **Used by**: `id_AddHomProperty` (259, via `simp [id_toPointMap]`), `id_toAddMonoidHom_apply` (530, `exact Isogeny.id_toPointMap W P`)
- **Visibility**: public (simp)
- **Lines**: 153–163, proof ~11 lines
- **Notes**: `set_option maxHeartbeats 800000` at line 150, NO justifying comment present.

---

### `@[simp] theorem id_degree`

- **Type**: `(Isogeny.id W).degree = 1`
- **What**: The identity isogeny has degree 1.
- **How**: `Curves.CurveMap.degree_id ⟨W⟩`.
- **Hypotheses**: `W` elliptic.
- **Uses from project**: `id`, `degree`, `Curves.CurveMap.degree_id`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 166–168, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `noncomputable def compose`

- **Type**: `(ψ : Isogeny W₂ W₃) → (φ : Isogeny W₁ W₂) → Isogeny W₁ W₃`
- **What**: Composition of two isogenies. The pullback composes contravariantly; the basepoint condition composes by applying `φ.pullback_ordAtInfty_nonneg` after `ψ.pullback_ordAtInfty_nonneg`.
- **How**: `toCurveMap := ψ.toCurveMap.comp φ.toCurveMap`; basepoint condition chains the two `nonneg` witnesses.
- **Hypotheses**: Three curves elliptic.
- **Uses from project**: `Curves.CurveMap.comp`
- **Used by**: `compose_toCurveMap` (183), `compose_toPointMap_zero` (194), `compose_toPointMap` (201), `compose_degree` (215), `compose_AddHomProperty` (263–267), `WithHom.compose` (534), `compose_toIsogeny` (540), `compose_coordHom_eq` (543), `compose_toAddMonoidHom_apply` (547), `compose_id_toAddMonoidHom` (600), `id_compose_toAddMonoidHom` (594)
- **Visibility**: public
- **Lines**: 177–181, definition body 5 lines
- **Notes**: Named `compose` rather than `comp` to avoid `Function.comp` dot-notation clash (noted in docstring).

---

### `@[simp] theorem compose_toCurveMap`

- **Type**: `(ψ.compose φ).toCurveMap = ψ.toCurveMap.comp φ.toCurveMap`
- **What**: The underlying `CurveMap` of composed isogenies is the composition of their `CurveMap`s.
- **How**: `rfl`.
- **Uses from project**: `compose`, `Curves.CurveMap.comp`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 183–184, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `noncomputable def composeCoordHom`

- **Type**: `{ψ : Isogeny W₂ W₃} → {φ : Isogeny W₁ W₂} → ψ.toCurveMap.CoordHom → φ.toCurveMap.CoordHom → (ψ.compose φ).toCurveMap.CoordHom`
- **What**: The natural coordinate-ring witness for the composition of two isogenies, given coord-ring witnesses for each factor.
- **How**: `ψ_cd.comp φ_cd` (CoordHom composition from `CurveMap`).
- **Hypotheses**: Three curves elliptic.
- **Uses from project**: `compose`, `Curves.CurveMap.CoordHom.comp`
- **Used by**: `compose_toPointMap_zero` (196), `compose_toPointMap` (203), `compose_AddHomProperty` (267), `WithHom.compose` (537), `compose_coordHom_eq` (544), `compose_toAddMonoidHom_apply` (552)
- **Visibility**: public
- **Lines**: 188–191, definition body 2 lines
- **Notes**: None.

---

### `@[simp] theorem compose_toPointMap_zero`

- **Type**: `(ψ.compose φ).toPointMap (composeCoordHom ψ_cd φ_cd) .zero = ψ.toPointMap ψ_cd (φ.toPointMap φ_cd .zero)`
- **What**: Composition of isogenies acts as composition on the basepoint.
- **How**: `rfl`.
- **Uses from project**: `compose`, `composeCoordHom`, `toPointMap`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 194–197, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `@[simp] theorem compose_toPointMap`

- **Type**: `∀ P : W₁.Point, (ψ.compose φ).toPointMap (composeCoordHom ψ_cd φ_cd) P = ψ.toPointMap ψ_cd (φ.toPointMap φ_cd P)`
- **What**: Composition of isogenies acts as function composition on all rational points.
- **How**: Cases on `P`; the zero case is `rfl`; the affine case rewrites using `Curves.CurveMap.toPointMap_comp`.
- **Hypotheses**: `set_option maxHeartbeats 800000` (no justifying comment).
- **Uses from project**: `compose`, `composeCoordHom`, `toPointMap`, `Curves.CurveMap.toPointMap_comp`
- **Used by**: `compose_AddHomProperty` (269, three times via `rw`), `compose_toAddMonoidHom_apply` (554, via `exact`)
- **Visibility**: public (simp)
- **Lines**: 201–211, proof ~11 lines
- **Notes**: `set_option maxHeartbeats 800000` at line 199, NO justifying comment.

---

### `theorem compose_degree`

- **Type**: `(ψ.compose φ).degree = φ.degree * ψ.degree`
- **What**: Degree multiplicativity: the degree of the composition is the product of the individual degrees.
- **How**: `Curves.CurveMap.degree_comp ψ.toCurveMap φ.toCurveMap` (tower law).
- **Uses from project**: `compose`, `degree`, `Curves.CurveMap.degree_comp`
- **Used by**: `WithHom.compose_degree` (559)
- **Visibility**: public
- **Lines**: 215–217, proof 1 line
- **Notes**: None.

---

### `def AddHomProperty`

- **Type**: `(φ : Isogeny W₁ W₂) → φ.toCurveMap.CoordHom → Prop`
- **What**: The predicate that the induced point map of `φ` (given a coord-ring witness) is a group homomorphism: `∀ P Q, φ.toPointMap coordHom (P + Q) = φ.toPointMap coordHom P + φ.toPointMap coordHom Q`.
- **How**: Definition by explicit universal statement.
- **Hypotheses**: `[DecidableEq F]` (required for `Add W.Point`).
- **Uses from project**: `toPointMap`
- **Used by**: `toAddMonoidHomOfWitness` (241), `id_AddHomProperty` (256), `compose_AddHomProperty` (263–267), `frobenius_AddHomProperty` (382), `WithHom` (field `addHomProp`, 501), `WithHom.id` (519), `WithHom.compose` (538)
- **Visibility**: public
- **Lines**: 234–237, definition body ~4 lines
- **Notes**: None.

---

### `noncomputable def toAddMonoidHomOfWitness`

- **Type**: `(φ : Isogeny W₁ W₂) → (coordHom : φ.toCurveMap.CoordHom) → (h : φ.AddHomProperty coordHom) → W₁.Point →+ W₂.Point`
- **What**: Packages an isogeny + coord witness + group-hom proof into a bundled `AddMonoidHom` on rational points.
- **How**: Constructs the `AddMonoidHom` record: `toFun := φ.toPointMap coordHom`, `map_zero' := φ.toPointMap_zero`, `map_add' := h`.
- **Hypotheses**: `[DecidableEq F]`, both curves elliptic, coord witness, and `AddHomProperty`.
- **Uses from project**: `toPointMap`, `toPointMap_zero`, `AddHomProperty`
- **Used by**: `toAddMonoidHomOfWitness_apply` (251), `WithHom.toAddMonoidHom` (507)
- **Visibility**: public
- **Lines**: 241–247, definition body ~7 lines
- **Notes**: None.

---

### `@[simp] theorem toAddMonoidHomOfWitness_apply`

- **Type**: `φ.toAddMonoidHomOfWitness coordHom h P = φ.toPointMap coordHom P`
- **What**: The bundled `AddMonoidHom` applies as the underlying point map.
- **How**: `rfl`.
- **Uses from project**: `toAddMonoidHomOfWitness`, `toPointMap`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 249–252, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `theorem id_AddHomProperty`

- **Type**: `(Isogeny.id W).AddHomProperty (idCoordHom W)`
- **What**: The identity isogeny satisfies the group-homomorphism property.
- **How**: `simp [id_toPointMap]` — reduces to `P + Q = P + Q` after unfolding the identity.
- **Hypotheses**: `W` elliptic, `[DecidableEq F]`.
- **Uses from project**: `AddHomProperty`, `id`, `idCoordHom`, `id_toPointMap`
- **Used by**: `WithHom.id` (519)
- **Visibility**: public
- **Lines**: 256–259, proof ~4 lines
- **Notes**: None.

---

### `theorem compose_AddHomProperty`

- **Type**: `(hψ : ψ.AddHomProperty ψ_cd) → (hφ : φ.AddHomProperty φ_cd) → (ψ.compose φ).AddHomProperty (composeCoordHom ψ_cd φ_cd)`
- **What**: Composition of group-hom isogenies satisfies the group-hom property.
- **How**: Rewrites via `compose_toPointMap` three times, then applies `hφ` and `hψ`.
- **Hypotheses**: Both isogenies have `AddHomProperty`, `[DecidableEq F]`.
- **Uses from project**: `AddHomProperty`, `compose`, `composeCoordHom`, `compose_toPointMap`
- **Used by**: `WithHom.compose` (538)
- **Visibility**: public
- **Lines**: 263–269, proof ~7 lines
- **Notes**: None.

---

### `noncomputable def Isogeny.frobenius`

- **Type**: `Isogeny W W` (for `W : Affine K`, `K` a finite field)
- **What**: The q-th power Frobenius isogeny on an elliptic curve over a finite field `K` of size `q = #K`. Its pullback is `f ↦ f^q`.
- **How**: `toCurveMap.pullback := FiniteField.frobeniusAlgHom K W.FunctionField`. The basepoint condition uses `FiniteField.coe_frobeniusAlgHom` to express Frobenius as q-power, then `ordAtInfty_pow` (to multiply order by q), then `nsmul_nonneg` to preserve nonnegativity.
- **Hypotheses**: `K` finite field, `[DecidableEq K]`.
- **Uses from project**: `HasseWeil.mulByInt_pullbackAlgHom` (no — uses `FiniteField.frobeniusAlgHom`); project lemma: `Curves.SmoothPlaneCurve.ordAtInfty_pow`
- **Used by**: `frobenius_pullback` (299), `frobenius_degree` (318), `frobenius_toPointMap` (327), `frobenius_AddHomProperty` (382), `frobeniusCoordHom` (306), `WithHom.frobenius` (610), `frobenius_toIsogeny` (617), `frobenius_coordHom_eq` (622), `frobenius_toAddMonoidHom_apply` (628)
- **Visibility**: public
- **Lines**: 285–297, definition body ~13 lines
- **Notes**: Reference: Silverman III.4.6.

---

### `@[simp] theorem Isogeny.frobenius_pullback`

- **Type**: `(Isogeny.frobenius W).toCurveMap.pullback f = f ^ Fintype.card K`
- **What**: The Frobenius pullback is the q-power map on the function field.
- **How**: `congr_fun (FiniteField.coe_frobeniusAlgHom ...) f`.
- **Hypotheses**: `K` finite.
- **Uses from project**: `Isogeny.frobenius`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 299–301, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `noncomputable def Isogeny.frobeniusCoordHom`

- **Type**: `(Isogeny.frobenius W).toCurveMap.CoordHom`
- **What**: The coordinate-ring witness for Frobenius: Frobenius `f ↦ f^q` restricts to the coordinate ring, compatibly with the algebra map.
- **How**: `toAlgHom := FiniteField.frobeniusAlgHom K W.CoordinateRing`; compatibility proved by `FiniteField.coe_frobeniusAlgHom` + `map_pow`.
- **Hypotheses**: `K` finite field.
- **Uses from project**: `Isogeny.frobenius`, `FiniteField.frobeniusAlgHom`
- **Used by**: `frobenius_toPointMap` (327), `frobenius_AddHomProperty` (382), `WithHom.frobenius` (613), `frobenius_coordHom_eq` (622), `frobenius_toAddMonoidHom_apply` (628)
- **Visibility**: public
- **Lines**: 306–314, definition body ~9 lines
- **Notes**: None.

---

### `@[simp] theorem Isogeny.frobenius_degree`

- **Type**: `(Isogeny.frobenius W).degree = Fintype.card K`
- **What**: The Frobenius isogeny has degree `q = #K`.
- **How**: `HasseWeil.frobenius_finrank_functionField K W`.
- **Hypotheses**: `K` finite field.
- **Uses from project**: `Isogeny.frobenius`, `degree`, `HasseWeil.frobenius_finrank_functionField`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 318–320, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `@[simp] theorem Isogeny.frobenius_toPointMap`

- **Type**: `∀ P : W.Point, (Isogeny.frobenius W).toPointMap (Isogeny.frobeniusCoordHom W) P = P`
- **What**: The Frobenius isogeny acts as the identity on K-rational points: `(x^q, y^q) = (x, y)` for `x, y ∈ K` by `FiniteField.pow_card`.
- **How**: Cases on `P`; zero is `rfl`. For an affine point, constructs an auxiliary proof `h_sp_eq` that the produced `SmoothPoint` has the same coordinates by computing `frobeniusAlgHom` on the coordinate-ring generators (`mk W (C X)` and `mk W Y`), rewriting via `coe_frobeniusAlgHom`, `map_pow`, `evalAt_x`/`evalAt_y`, and `FiniteField.pow_card`.
- **Hypotheses**: `K` finite field, `[DecidableEq K]`. `set_option maxHeartbeats 800000` (no justifying comment).
- **Uses from project**: `Isogeny.frobenius`, `frobeniusCoordHom`, `toPointMap`, `Curves.CurveMap.evalAtPullback_apply`, `Curves.SmoothPlaneCurve.evalAt_x`, `Curves.SmoothPlaneCurve.evalAt_y`
- **Used by**: `frobenius_AddHomProperty` (385, via `simp`), `frobenius_toAddMonoidHom_apply` (633, via `exact`)
- **Visibility**: public (simp)
- **Lines**: 327–377, proof ~51 lines
- **Notes**: Longest proof in the file (~51 lines). `set_option maxHeartbeats 800000` at line 322, NO justifying comment. No sorry.

---

### `theorem Isogeny.frobenius_AddHomProperty`

- **Type**: `(Isogeny.frobenius W).AddHomProperty (Isogeny.frobeniusCoordHom W)`
- **What**: The Frobenius isogeny is a group homomorphism on K-rational points (trivially: since it acts as the identity).
- **How**: `simp [Isogeny.frobenius_toPointMap]` — reduces both sides to `P + Q`.
- **Hypotheses**: `K` finite field, `[DecidableEq K]`.
- **Uses from project**: `AddHomProperty`, `frobenius`, `frobeniusCoordHom`, `frobenius_toPointMap`
- **Used by**: `WithHom.frobenius` (615)
- **Visibility**: public
- **Lines**: 382–385, proof ~4 lines
- **Notes**: None.

---

### `abbrev MulByIntBasepoint`

- **Type**: `{n : ℤ} → (hn : n ≠ 0) → Prop`
- **What**: The predicate that `mulByInt_pullbackAlgHom W n hn` preserves nonnegativity of `ordAtInfty`: this is the required basepoint-preservation condition for `[n]`.
- **How**: Abbreviation for the universal statement over function-field elements.
- **Hypotheses**: `[DecidableEq F]`, `n ≠ 0`.
- **Uses from project**: `HasseWeil.mulByInt_pullbackAlgHom`, `Curves.SmoothPlaneCurve.ordAtInfty`
- **Used by**: `Isogeny.mulByIntOfBasepoint` (430), `Isogeny.mulByIntOfBasepoint_pullback` (437)
- **Visibility**: public
- **Lines**: 416–420, 1 line definition
- **Notes**: Commented as pending discharge via `mulByInt_finrank` or valuation extension. The hypothesis is left open (no proof in this file).

---

### `noncomputable def Isogeny.mulByIntOfBasepoint`

- **Type**: `{n : ℤ} → (hn : n ≠ 0) → (h_basepoint : MulByIntBasepoint W hn) → Isogeny W W`
- **What**: The multiplication-by-n isogeny `[n] : E → E` for `n ≠ 0`, given an external basepoint witness. Its pullback is `mulByInt_pullbackAlgHom`.
- **How**: `toCurveMap.pullback := HasseWeil.mulByInt_pullbackAlgHom W n hn`; `pullback_ordAtInfty_nonneg := h_basepoint`.
- **Hypotheses**: `[DecidableEq F]`, `n ≠ 0`, and the basepoint witness `MulByIntBasepoint W hn`.
- **Uses from project**: `MulByIntBasepoint`, `HasseWeil.mulByInt_pullbackAlgHom`
- **Used by**: `mulByIntOfBasepoint_pullback` (438)
- **Visibility**: public
- **Lines**: 430–434, definition body ~5 lines
- **Notes**: No `CoordHom` witness available — `[n]` has poles at torsion points in the affine model. Commented as design-intentional.

---

### `@[simp] theorem Isogeny.mulByIntOfBasepoint_pullback`

- **Type**: `(Isogeny.mulByIntOfBasepoint W hn h_basepoint).toCurveMap.pullback f = HasseWeil.mulByInt_pullbackAlgHom W n hn f`
- **What**: The pullback of the multiplication-by-n isogeny is `mulByInt_pullbackAlgHom`.
- **How**: `rfl`.
- **Hypotheses**: `[DecidableEq F]`, `n ≠ 0`, basepoint witness.
- **Uses from project**: `mulByIntOfBasepoint`, `MulByIntBasepoint`, `HasseWeil.mulByInt_pullbackAlgHom`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 436–439, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `structure WithHom`

- **Type**: `WithHom (W₁ W₂ : Affine F) [W₁.IsElliptic] [W₂.IsElliptic] [DecidableEq F]` with fields `toIsogeny`, `coordHom`, `addHomProp`
- **What**: An isogeny bundled with a coordinate-ring witness and a proof that the induced point map is a group homomorphism. Every `WithHom` yields an `AddMonoidHom` on rational points directly.
- **How**: Structure with three fields packing the isogeny, its coord witness, and the `AddHomProperty` proof.
- **Hypotheses**: `[DecidableEq F]`, both curves elliptic.
- **Uses from project**: `Isogeny`, `AddHomProperty`, `CurveMap.CoordHom`
- **Used by**: `WithHom.toAddMonoidHom` (506), `WithHom.id` (518), `WithHom.compose` (534), `WithHom.frobenius` (610), and all `WithHom.*` theorems.
- **Visibility**: public
- **Lines**: 494–501, structure body ~8 lines
- **Notes**: Central bundle type for the group-hom closure results.

---

### `noncomputable def WithHom.toAddMonoidHom`

- **Type**: `(φ : WithHom W₁ W₂) → W₁.Point →+ W₂.Point`
- **What**: The bundled `AddMonoidHom` derived from a `WithHom` isogeny.
- **How**: Delegates to `φ.toIsogeny.toAddMonoidHomOfWitness φ.coordHom φ.addHomProp`.
- **Hypotheses**: `[DecidableEq F]`, both curves elliptic.
- **Uses from project**: `WithHom`, `toAddMonoidHomOfWitness`
- **Used by**: `toAddMonoidHom_apply` (509), `id_toAddMonoidHom_apply` (528), `compose_toAddMonoidHom_apply` (547), `map_zero` (564), `map_add` (568), `map_neg` (573), `map_sub` (578), `map_zsmul` (583), `map_nsmul` (588), `id_compose_toAddMonoidHom` (594), `compose_id_toAddMonoidHom` (600), `frobenius_toAddMonoidHom_apply` (628)
- **Visibility**: public
- **Lines**: 506–507, definition body 2 lines
- **Notes**: Key API — most heavily used declaration in the `WithHom` namespace.

---

### `@[simp] theorem WithHom.toAddMonoidHom_apply`

- **Type**: `φ.toAddMonoidHom P = φ.toIsogeny.toPointMap φ.coordHom P`
- **What**: Unfolds `toAddMonoidHom` to the underlying point map.
- **How**: `rfl`.
- **Uses from project**: `WithHom.toAddMonoidHom`, `toPointMap`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 509–510, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `noncomputable abbrev WithHom.degree`

- **Type**: `(φ : WithHom W₁ W₂) → ℕ`
- **What**: The degree of a `WithHom` isogeny, inherited from the underlying `Isogeny`.
- **How**: `φ.toIsogeny.degree`.
- **Uses from project**: `WithHom`, `Isogeny.degree`
- **Used by**: unused in file (exported API)
- **Visibility**: public
- **Lines**: 513, 1 line
- **Notes**: Dead-code candidate within this file.

---

### `noncomputable def WithHom.id`

- **Type**: `(W : Affine F) → [W.IsElliptic] → WithHom W W`
- **What**: The identity `WithHom`: packages `Isogeny.id`, `idCoordHom`, and `id_AddHomProperty`.
- **How**: Anonymous constructor `⟨Isogeny.id W, idCoordHom W, id_AddHomProperty W⟩`.
- **Uses from project**: `WithHom`, `Isogeny.id`, `idCoordHom`, `id_AddHomProperty`
- **Used by**: `id_toIsogeny` (521), `id_coordHom_eq` (524), `id_toAddMonoidHom_apply` (528), `id_compose_toAddMonoidHom` (594), `compose_id_toAddMonoidHom` (600)
- **Visibility**: public
- **Lines**: 518–519, definition body 2 lines
- **Notes**: None.

---

### `@[simp] theorem WithHom.id_toIsogeny`

- **Type**: `(WithHom.id W).toIsogeny = Isogeny.id W`
- **What**: The underlying isogeny of the identity `WithHom` is the identity isogeny.
- **How**: `rfl`.
- **Uses from project**: `WithHom.id`, `Isogeny.id`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 521–522, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `@[simp] theorem WithHom.id_coordHom_eq`

- **Type**: `(WithHom.id W).coordHom = idCoordHom W`
- **What**: The coord witness of the identity `WithHom` is `idCoordHom`.
- **How**: `rfl`.
- **Uses from project**: `WithHom.id`, `idCoordHom`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 524–525, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `@[simp] theorem WithHom.id_toAddMonoidHom_apply`

- **Type**: `∀ P, (WithHom.id W).toAddMonoidHom P = P`
- **What**: The identity `WithHom` acts as the identity on all rational points.
- **How**: Reduces to `Isogeny.id_toPointMap W P` via `show`.
- **Uses from project**: `WithHom.id`, `toAddMonoidHom`, `Isogeny.id`, `idCoordHom`, `id_toPointMap`
- **Used by**: `id_compose_toAddMonoidHom` (596), `compose_id_toAddMonoidHom` (602)
- **Visibility**: public (simp)
- **Lines**: 528–531, proof ~4 lines
- **Notes**: None.

---

### `noncomputable def WithHom.compose`

- **Type**: `(ψ : WithHom W₂ W₃) → (φ : WithHom W₁ W₂) → WithHom W₁ W₃`
- **What**: Composition of `WithHom` isogenies.
- **How**: Packages `ψ.toIsogeny.compose φ.toIsogeny`, `composeCoordHom ψ.coordHom φ.coordHom`, and `compose_AddHomProperty ... ψ.addHomProp φ.addHomProp`.
- **Uses from project**: `WithHom`, `Isogeny.compose`, `composeCoordHom`, `compose_AddHomProperty`
- **Used by**: `compose_toIsogeny` (540), `compose_coordHom_eq` (543), `compose_toAddMonoidHom_apply` (547), `compose_degree` (557), `id_compose_toAddMonoidHom` (594), `compose_id_toAddMonoidHom` (600)
- **Visibility**: public
- **Lines**: 534–538, definition body ~5 lines
- **Notes**: None.

---

### `@[simp] theorem WithHom.compose_toIsogeny`

- **Type**: `(ψ.compose φ).toIsogeny = ψ.toIsogeny.compose φ.toIsogeny`
- **What**: The underlying isogeny of composed `WithHom`s is the composition of the underlying isogenies.
- **How**: `rfl`.
- **Uses from project**: `WithHom.compose`, `Isogeny.compose`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 540–541, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `@[simp] theorem WithHom.compose_coordHom_eq`

- **Type**: `(ψ.compose φ).coordHom = composeCoordHom ψ.coordHom φ.coordHom`
- **What**: The coord witness of composed `WithHom`s is the composition of their coord witnesses.
- **How**: `rfl`.
- **Uses from project**: `WithHom.compose`, `composeCoordHom`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 543–544, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `@[simp] theorem WithHom.compose_toAddMonoidHom_apply`

- **Type**: `∀ P, (ψ.compose φ).toAddMonoidHom P = ψ.toAddMonoidHom (φ.toAddMonoidHom P)`
- **What**: The `AddMonoidHom` of a composed `WithHom` is the composition of the individual `AddMonoidHom`s.
- **How**: Reduces to `Isogeny.compose_toPointMap` via `show` + `exact`.
- **Uses from project**: `WithHom.compose`, `toAddMonoidHom`, `composeCoordHom`, `compose_toPointMap`
- **Used by**: `id_compose_toAddMonoidHom` (596), `compose_id_toAddMonoidHom` (602)
- **Visibility**: public (simp)
- **Lines**: 547–554, proof ~8 lines
- **Notes**: None.

---

### `theorem WithHom.compose_degree`

- **Type**: `(ψ.compose φ).degree = φ.degree * ψ.degree`
- **What**: Degree multiplicativity for `WithHom`.
- **How**: `Isogeny.compose_degree ψ.toIsogeny φ.toIsogeny`.
- **Uses from project**: `WithHom.compose`, `WithHom.degree`, `Isogeny.compose_degree`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 557–559, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `@[simp] theorem WithHom.map_zero`

- **Type**: `φ.toAddMonoidHom 0 = 0`
- **What**: A `WithHom` isogeny preserves zero.
- **How**: `φ.toAddMonoidHom.map_zero` (mathlib).
- **Uses from project**: `WithHom.toAddMonoidHom`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 564–565, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `theorem WithHom.map_add`

- **Type**: `φ.toAddMonoidHom (P + Q) = φ.toAddMonoidHom P + φ.toAddMonoidHom Q`
- **What**: A `WithHom` isogeny preserves addition.
- **How**: `φ.toAddMonoidHom.map_add P Q`.
- **Uses from project**: `WithHom.toAddMonoidHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 568–570, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `theorem WithHom.map_neg`

- **Type**: `φ.toAddMonoidHom (-P) = -φ.toAddMonoidHom P`
- **What**: A `WithHom` isogeny preserves negation.
- **How**: `φ.toAddMonoidHom.map_neg P`.
- **Uses from project**: `WithHom.toAddMonoidHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 573–575, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `theorem WithHom.map_sub`

- **Type**: `φ.toAddMonoidHom (P - Q) = φ.toAddMonoidHom P - φ.toAddMonoidHom Q`
- **What**: A `WithHom` isogeny preserves subtraction.
- **How**: `φ.toAddMonoidHom.map_sub P Q`.
- **Uses from project**: `WithHom.toAddMonoidHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 578–580, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `theorem WithHom.map_zsmul`

- **Type**: `φ.toAddMonoidHom (n • P) = n • φ.toAddMonoidHom P` (for `n : ℤ`)
- **What**: A `WithHom` isogeny commutes with integer scalar multiplication.
- **How**: `φ.toAddMonoidHom.map_zsmul P n`.
- **Uses from project**: `WithHom.toAddMonoidHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 583–585, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `theorem WithHom.map_nsmul`

- **Type**: `φ.toAddMonoidHom (n • P) = n • φ.toAddMonoidHom P` (for `n : ℕ`)
- **What**: A `WithHom` isogeny commutes with natural-number scalar multiplication.
- **How**: `φ.toAddMonoidHom.map_nsmul P n`.
- **Uses from project**: `WithHom.toAddMonoidHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 588–590, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `@[simp] theorem WithHom.id_compose_toAddMonoidHom`

- **Type**: `∀ P, ((WithHom.id W₂).compose φ).toAddMonoidHom P = φ.toAddMonoidHom P`
- **What**: Composing with the identity on the right is the identity on the `AddMonoidHom`.
- **How**: `rw [compose_toAddMonoidHom_apply, id_toAddMonoidHom_apply]`.
- **Uses from project**: `WithHom.compose`, `WithHom.id`, `compose_toAddMonoidHom_apply`, `id_toAddMonoidHom_apply`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 594–596, proof ~3 lines
- **Notes**: Dead-code candidate within this file.

---

### `@[simp] theorem WithHom.compose_id_toAddMonoidHom`

- **Type**: `∀ P, (φ.compose (WithHom.id W₁)).toAddMonoidHom P = φ.toAddMonoidHom P`
- **What**: Composing with the identity on the left is the identity on the `AddMonoidHom`.
- **How**: `rw [compose_toAddMonoidHom_apply, id_toAddMonoidHom_apply]`.
- **Uses from project**: `WithHom.compose`, `WithHom.id`, `compose_toAddMonoidHom_apply`, `id_toAddMonoidHom_apply`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 600–602, proof ~3 lines
- **Notes**: Dead-code candidate within this file.

---

### `noncomputable def Isogeny.WithHom.frobenius`

- **Type**: `(W : Affine K) → [K finite field, DecidableEq K, W.IsElliptic] → Isogeny.WithHom W W`
- **What**: The Frobenius isogeny as a bundled `WithHom`.
- **How**: Anonymous constructor `⟨Isogeny.frobenius W, Isogeny.frobeniusCoordHom W, Isogeny.frobenius_AddHomProperty W⟩`.
- **Uses from project**: `Isogeny.frobenius`, `Isogeny.frobeniusCoordHom`, `Isogeny.frobenius_AddHomProperty`
- **Used by**: `frobenius_toIsogeny` (617), `frobenius_coordHom_eq` (622), `frobenius_toAddMonoidHom_apply` (628)
- **Visibility**: public
- **Lines**: 610–615, definition body ~6 lines
- **Notes**: Placed outside the `Isogeny` namespace to allow separate `Fintype K`, `DecidableEq K` typeclass constraints.

---

### `@[simp] theorem Isogeny.WithHom.frobenius_toIsogeny`

- **Type**: `(Isogeny.WithHom.frobenius W).toIsogeny = Isogeny.frobenius W`
- **What**: The underlying isogeny of Frobenius-as-WithHom is the Frobenius isogeny.
- **How**: `rfl`.
- **Uses from project**: `Isogeny.WithHom.frobenius`, `Isogeny.frobenius`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 617–620, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `@[simp] theorem Isogeny.WithHom.frobenius_coordHom_eq`

- **Type**: `(Isogeny.WithHom.frobenius W).coordHom = Isogeny.frobeniusCoordHom W`
- **What**: The coord witness of Frobenius-as-WithHom is `frobeniusCoordHom`.
- **How**: `rfl`.
- **Uses from project**: `Isogeny.WithHom.frobenius`, `Isogeny.frobeniusCoordHom`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 622–625, proof 1 line
- **Notes**: Dead-code candidate within this file.

---

### `@[simp] theorem Isogeny.WithHom.frobenius_toAddMonoidHom_apply`

- **Type**: `∀ P, (Isogeny.WithHom.frobenius W).toAddMonoidHom P = P`
- **What**: Frobenius-as-WithHom acts as the identity on K-rational points.
- **How**: Reduces to `Isogeny.frobenius_toPointMap W P` via `show` + `exact`.
- **Uses from project**: `Isogeny.WithHom.frobenius`, `WithHom.toAddMonoidHom`, `Isogeny.frobeniusCoordHom`, `Isogeny.frobenius_toPointMap`
- **Used by**: unused in file
- **Visibility**: public (simp)
- **Lines**: 628–633, proof ~6 lines
- **Notes**: Dead-code candidate within this file.

---

## Cross-reference summary

**keyApi** (used by 3+ declarations in this file):
- `toPointMap` — used by 14+ declarations
- `AddHomProperty` — used by 7 declarations
- `Isogeny.id` — used by 9 declarations
- `idCoordHom` — used by 6 declarations
- `Isogeny.compose` — used by 11 declarations
- `composeCoordHom` — used by 6 declarations
- `WithHom.toAddMonoidHom` — used by 12+ declarations
- `Isogeny.frobenius` — used by 9 declarations
- `id_toPointMap` — used by 2 (borderline)
- `compose_toPointMap` — used by 2 (borderline)
- `frobenius_toPointMap` — used by 2 (borderline)

**Long proofs (>30 lines)**:
- `frobenius_toPointMap`: ~51 lines (327–377)

**set_option maxHeartbeats**:
- Line 150: 800000, for `id_toPointMap` — NO justifying comment
- Line 199: 800000, for `compose_toPointMap` — NO justifying comment
- Line 322: 800000, for `frobenius_toPointMap` — NO justifying comment

**Sorries**: None.
