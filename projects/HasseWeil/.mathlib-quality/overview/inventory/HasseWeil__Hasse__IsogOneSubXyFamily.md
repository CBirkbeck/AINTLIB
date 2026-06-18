# Inventory: ./HasseWeil/Hasse/IsogOneSubXyFamily.lean

**Total declarations**: 40 (39 theorems + 1 noncomputable def)  
**Lines**: 837  
**Import**: `HasseWeil.AdditionPullback.SilvermanIV14`  
**Sorries**: none  
**set_option maxHeartbeats**: none

---

## Overview

This file discharges the `xy_family` hypothesis needed by the Layer-2 fixed-field theorem for the isogeny `β = isogOneSub_negFrobenius W hq`. The proof strategy unfolds in four stages: (1) witness-parametric reduction to addPullback identities; (2) K-AlgHom distribution over curve formulas; (3) σ-commutation chain connecting Frobenius pullback to q-th powers; (4) curve-group-law identity at W_KE level showing `(P + lift k) - π(P + lift k) = P - π(P)` for K-rational k.

---

### `theorem xy_family_isogOneSub_negFrobenius_of_addPullback_invariance`

- **Type**: Given `h_inv : ∀ k : (isogOneSub_negFrobenius W hq).kernel, τ_k(addPullback_x W negFrob) = addPullback_x W negFrob ∧ τ_k(addPullback_y W negFrob) = addPullback_y W negFrob`, conclude the same with `isogOneSub_negFrobenius.pullback (x_gen W)` and `... (y_gen W)` in place of the explicit addPullback forms.
- **What**: Bridge between the abstract Layer-2 `xy_family` requirement and the concrete addPullback-translation invariance for `isogOneSub_negFrobenius`.
- **How**: Direct rewrite via `isogOneSub_negFrobenius_pullback`, `addPullbackAlgHom_negFrobenius_x_gen_eq`, `addPullbackAlgHom_negFrobenius_y_gen_eq` (from SilvermanIV14), then `exact h_inv k`.
- **Hypotheses**: `K` finite field, `W` elliptic, `hq : 2 ≤ Fintype.card K`.
- **Uses from project**: `isogOneSub_negFrobenius_pullback`, `addPullbackAlgHom_negFrobenius_x_gen_eq`, `addPullbackAlgHom_negFrobenius_y_gen_eq`, `negFrobeniusIsog`
- **Used by**: `xy_family_isogOneSub_negFrobenius_of_addX_addY_invariance`
- **Visibility**: public
- **Lines**: 67–87; proof length 6 lines
- **Notes**: None

---

### `theorem W_KE_map_K_algHom`

- **Type**: `∀ f : FunctionField →ₐ[K] FunctionField, (W_KE W).map f.toRingHom = W_KE W`
- **What**: The base-changed curve `W_KE W` is preserved under any K-AlgHom on the function field.
- **How**: Directly applies `WeierstrassCurve.map_baseChange` with `R = S = K`, `A = B = KE`.
- **Hypotheses**: None beyond `W` elliptic and `K` a field.
- **Uses from project**: `W_KE`
- **Used by**: `map_addX_K_algHom`, `map_negY_K_algHom`, `map_addY_K_algHom`, `map_slope_K_algHom`
- **Visibility**: public
- **Lines**: 100–103; proof length 2 lines (term-mode)
- **Notes**: Used by 4 declarations — key API lemma.

---

### `theorem map_addX_K_algHom`

- **Type**: `∀ f x₁ x₂ ℓ, f ((W_KE W).toAffine.addX x₁ x₂ ℓ) = (W_KE W).toAffine.addX (f x₁) (f x₂) (f ℓ)`
- **What**: K-AlgHoms distribute through the `addX` formula on the base-changed curve.
- **How**: Applies Mathlib's `Affine.map_addX` at RingHom level then rewrites with `W_KE_map_K_algHom`.
- **Hypotheses**: `f : FunctionField →ₐ[K] FunctionField`.
- **Uses from project**: `W_KE_map_K_algHom`, `W_KE`
- **Used by**: `map_addPullback_x_K_algHom`
- **Visibility**: public
- **Lines**: 110–118; proof length 5 lines
- **Notes**: None

---

### `theorem map_negY_K_algHom`

- **Type**: `∀ f x y, f ((W_KE W).toAffine.negY x y) = (W_KE W).toAffine.negY (f x) (f y)`
- **What**: K-AlgHoms distribute through the `negY` (point-negation y-coord) formula.
- **How**: Applies Mathlib's `Affine.map_negY` then rewrites with `W_KE_map_K_algHom`.
- **Hypotheses**: `f : FunctionField →ₐ[K] FunctionField`.
- **Uses from project**: `W_KE_map_K_algHom`, `W_KE`
- **Used by**: unused in file (not referenced internally; not referenced externally in the project)
- **Visibility**: public
- **Lines**: 122–129; proof length 5 lines
- **Notes**: Dead-code candidate — not called by any other declaration in this file or elsewhere in the project.

---

### `theorem map_addY_K_algHom`

- **Type**: `∀ f x₁ x₂ y₁ ℓ, f ((W_KE W).toAffine.addY x₁ x₂ y₁ ℓ) = (W_KE W).toAffine.addY (f x₁) (f x₂) (f y₁) (f ℓ)`
- **What**: K-AlgHoms distribute through the `addY` formula.
- **How**: Applies Mathlib's `Affine.map_addY` then rewrites with `W_KE_map_K_algHom`.
- **Hypotheses**: `f : FunctionField →ₐ[K] FunctionField`.
- **Uses from project**: `W_KE_map_K_algHom`, `W_KE`
- **Used by**: `map_addPullback_y_K_algHom`
- **Visibility**: public
- **Lines**: 133–141; proof length 5 lines
- **Notes**: None

---

### `theorem map_slope_K_algHom`

- **Type**: `∀ f x₁ x₂ y₁ y₂, f ((W_KE W).toAffine.slope x₁ x₂ y₁ y₂) = (W_KE W).toAffine.slope (f x₁) (f x₂) (f y₁) (f y₂)`
- **What**: K-AlgHoms distribute through the `slope` formula.
- **How**: Applies Mathlib's `Affine.map_slope` then rewrites with `W_KE_map_K_algHom`.
- **Hypotheses**: `f : FunctionField →ₐ[K] FunctionField`.
- **Uses from project**: `W_KE_map_K_algHom`, `W_KE`
- **Used by**: `map_addSlope_K_algHom`
- **Visibility**: public
- **Lines**: 145–152; proof length 4 lines
- **Notes**: None

---

### `theorem map_addSlope_K_algHom`

- **Type**: `∀ f α, f (addSlope W α) = (W_KE W).toAffine.slope (f (x_gen W)) (f (α.pullback (x_gen W))) (f (y_gen W)) (f (α.pullback (y_gen W)))`
- **What**: K-AlgHoms distribute through `addSlope W α` by unfolding to `slope` and applying the slope distribution lemma.
- **How**: Unfolds `addSlope`, then applies `map_slope_K_algHom`.
- **Hypotheses**: `f : FunctionField →ₐ[K] FunctionField`, `α : Isogeny W.toAffine W.toAffine`.
- **Uses from project**: `addSlope`, `x_gen`, `y_gen`, `map_slope_K_algHom`, `W_KE`
- **Used by**: `map_addSlope_negFrobeniusIsog_K_algHom`
- **Visibility**: public
- **Lines**: 163–171; proof length 3 lines
- **Notes**: None

---

### `theorem map_addPullback_x_K_algHom`

- **Type**: `∀ f α, f (addPullback_x W α) = (W_KE W).toAffine.addX (f (x_gen W)) (f (α.pullback (x_gen W))) (f (addSlope W α))`
- **What**: K-AlgHoms distribute through `addPullback_x W α` by unfolding and applying `map_addX_K_algHom`.
- **How**: Unfolds `addPullback_x`, applies `map_addX_K_algHom`.
- **Hypotheses**: `f : FunctionField →ₐ[K] FunctionField`, `α : Isogeny W.toAffine W.toAffine`.
- **Uses from project**: `addPullback_x`, `addSlope`, `x_gen`, `map_addX_K_algHom`, `W_KE`
- **Used by**: `map_addPullback_x_negFrobeniusIsog_K_algHom`
- **Visibility**: public
- **Lines**: 175–183; proof length 3 lines
- **Notes**: None

---

### `theorem map_addPullback_y_K_algHom`

- **Type**: `∀ f α, f (addPullback_y W α) = (W_KE W).toAffine.addY (f (x_gen W)) (f (α.pullback (x_gen W))) (f (y_gen W)) (f (addSlope W α))`
- **What**: K-AlgHoms distribute through `addPullback_y W α`.
- **How**: Unfolds `addPullback_y`, applies `map_addY_K_algHom`.
- **Hypotheses**: `f : FunctionField →ₐ[K] FunctionField`, `α : Isogeny W.toAffine W.toAffine`.
- **Uses from project**: `addPullback_y`, `addSlope`, `x_gen`, `y_gen`, `map_addY_K_algHom`, `W_KE`
- **Used by**: `map_addPullback_y_negFrobeniusIsog_K_algHom`
- **Visibility**: public
- **Lines**: 186–193; proof length 3 lines
- **Notes**: None

---

### `theorem map_negFrobeniusIsog_pullback_x_gen_K_algHom`

- **Type**: `∀ f, f ((negFrobeniusIsog W).pullback (x_gen W)) = (f (x_gen W)) ^ Fintype.card K`
- **What**: The σ-commutation for the x-generator: any K-AlgHom applied to the negFrob pullback of x_gen equals the q-th power of the image of x_gen.
- **How**: Rewrites via `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, then `map_pow`.
- **Hypotheses**: `f : FunctionField →ₐ[K] FunctionField`.
- **Uses from project**: `negFrobeniusIsog`, `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `x_gen`
- **Used by**: `map_addSlope_negFrobeniusIsog_K_algHom`, `map_addPullback_x_negFrobeniusIsog_K_algHom`, `map_addPullback_y_negFrobeniusIsog_K_algHom`
- **Visibility**: public
- **Lines**: 209–213; proof length 1 line
- **Notes**: Used by 3 declarations — key API. The key mathematical fact is that Frobenius pullback = q-th power map.

---

### `theorem map_negFrobeniusIsog_pullback_y_gen_K_algHom`

- **Type**: `∀ f, f ((negFrobeniusIsog W).pullback (y_gen W)) = -((f (y_gen W))^q) - a₁·(f (x_gen W))^q - a₃`
- **What**: σ-commutation for the y-generator: K-AlgHom applied to the negFrob pullback of y_gen equals the explicit formula with q-th powers.
- **How**: Rewrites via `negFrobeniusIsog_pullback_y_gen`, then distributes via `map_sub`, `map_neg`, `map_mul`, `map_pow`, `frobeniusIsog_pullback_apply`, and `AlgHom.commutes` (for constant terms a₁, a₃).
- **Hypotheses**: `f : FunctionField →ₐ[K] FunctionField`.
- **Uses from project**: `negFrobeniusIsog`, `negFrobeniusIsog_pullback_y_gen`, `frobeniusIsog_pullback_apply`, `y_gen`, `x_gen`
- **Used by**: `map_addSlope_negFrobeniusIsog_K_algHom`
- **Visibility**: public
- **Lines**: 219–228; proof length 7 lines
- **Notes**: Uses `AlgHom.commutes` to fix the K-scalar coefficients a₁, a₃.

---

### `theorem map_addSlope_negFrobeniusIsog_K_algHom`

- **Type**: `∀ f, f (addSlope W (negFrobeniusIsog W)) = (W_KE W).toAffine.slope (f x_gen) ((f x_gen)^q) (f y_gen) (-(f y_gen)^q - a₁·(f x_gen)^q - a₃)`
- **What**: Assembled explicit formula for the K-AlgHom image of `addSlope W (negFrobeniusIsog W)`, combining slope-distribution and σ-commutation.
- **How**: Rewrites via `map_addSlope_K_algHom`, `map_negFrobeniusIsog_pullback_x_gen_K_algHom`, `map_negFrobeniusIsog_pullback_y_gen_K_algHom`.
- **Hypotheses**: `f : FunctionField →ₐ[K] FunctionField`.
- **Uses from project**: `map_addSlope_K_algHom`, `map_negFrobeniusIsog_pullback_x_gen_K_algHom`, `map_negFrobeniusIsog_pullback_y_gen_K_algHom`, `negFrobeniusIsog`, `W_KE`
- **Used by**: `translateAlgEquivOfPoint_addSlope_negFrobeniusIsog`
- **Visibility**: public
- **Lines**: 239–250; proof length 3 lines
- **Notes**: None

---

### `theorem map_addPullback_x_negFrobeniusIsog_K_algHom`

- **Type**: `∀ f, f (addPullback_x W (negFrobeniusIsog W)) = (W_KE W).toAffine.addX (f x_gen) ((f x_gen)^q) (f (addSlope W (negFrobeniusIsog W)))`
- **What**: Explicit form of K-AlgHom applied to `addPullback_x` for negFrob: the addX formula with q-th power as second x-coordinate.
- **How**: Rewrites via `map_addPullback_x_K_algHom`, `map_negFrobeniusIsog_pullback_x_gen_K_algHom`.
- **Hypotheses**: `f : FunctionField →ₐ[K] FunctionField`.
- **Uses from project**: `map_addPullback_x_K_algHom`, `map_negFrobeniusIsog_pullback_x_gen_K_algHom`, `negFrobeniusIsog`, `W_KE`
- **Used by**: `translateAlgEquivOfPoint_addPullback_x_negFrobeniusIsog`
- **Visibility**: public
- **Lines**: 254–260; proof length 3 lines
- **Notes**: None

---

### `theorem map_addPullback_y_negFrobeniusIsog_K_algHom`

- **Type**: `∀ f, f (addPullback_y W (negFrobeniusIsog W)) = (W_KE W).toAffine.addY (f x_gen) ((f x_gen)^q) (f y_gen) (f (addSlope W (negFrobeniusIsog W)))`
- **What**: Explicit form of K-AlgHom applied to `addPullback_y` for negFrob.
- **How**: Rewrites via `map_addPullback_y_K_algHom`, `map_negFrobeniusIsog_pullback_x_gen_K_algHom`.
- **Hypotheses**: `f : FunctionField →ₐ[K] FunctionField`.
- **Uses from project**: `map_addPullback_y_K_algHom`, `map_negFrobeniusIsog_pullback_x_gen_K_algHom`, `negFrobeniusIsog`, `W_KE`
- **Used by**: `translateAlgEquivOfPoint_addPullback_y_negFrobeniusIsog`
- **Visibility**: public
- **Lines**: 264–270; proof length 3 lines
- **Notes**: None

---

### `theorem translateAlgEquivOfPoint_addPullback_x_negFrobeniusIsog`

- **Type**: `∀ k : W.toAffine.Point, translateAlgEquivOfPoint W k (addPullback_x W (negFrobeniusIsog W)) = (W_KE W).toAffine.addX (τ_k x_gen) ((τ_k x_gen)^q) (τ_k (addSlope W (negFrobeniusIsog W)))`
- **What**: Specialization of the K-AlgHom distribution to `τ_k = translateAlgEquivOfPoint W k` for the x-coord.
- **How**: Directly applies `map_addPullback_x_negFrobeniusIsog_K_algHom` at `f = τ_k.toAlgHom` (term-mode proof).
- **Hypotheses**: `k : W.toAffine.Point`.
- **Uses from project**: `map_addPullback_x_negFrobeniusIsog_K_algHom`, `translateAlgEquivOfPoint`, `negFrobeniusIsog`, `W_KE`
- **Used by**: `xy_family_isogOneSub_negFrobenius_of_addX_addY_invariance`
- **Visibility**: public
- **Lines**: 283–291; proof length 1 line (term-mode)
- **Notes**: None

---

### `theorem translateAlgEquivOfPoint_addPullback_y_negFrobeniusIsog`

- **Type**: `∀ k : W.toAffine.Point, translateAlgEquivOfPoint W k (addPullback_y W (negFrobeniusIsog W)) = (W_KE W).toAffine.addY (τ_k x_gen) ((τ_k x_gen)^q) (τ_k y_gen) (τ_k (addSlope W (negFrobeniusIsog W)))`
- **What**: Specialization to τ_k for the y-coord. Companion of the x version.
- **How**: Directly applies `map_addPullback_y_negFrobeniusIsog_K_algHom` at `f = τ_k.toAlgHom`.
- **Hypotheses**: `k : W.toAffine.Point`.
- **Uses from project**: `map_addPullback_y_negFrobeniusIsog_K_algHom`, `translateAlgEquivOfPoint`, `negFrobeniusIsog`, `W_KE`
- **Used by**: `xy_family_isogOneSub_negFrobenius_of_addX_addY_invariance`
- **Visibility**: public
- **Lines**: 295–304; proof length 1 line (term-mode)
- **Notes**: None

---

### `theorem translateAlgEquivOfPoint_addSlope_negFrobeniusIsog`

- **Type**: `∀ k : W.toAffine.Point, τ_k (addSlope W (negFrobeniusIsog W)) = (W_KE W).toAffine.slope (τ_k x_gen) ((τ_k x_gen)^q) (τ_k y_gen) (-(τ_k y_gen)^q - a₁·(τ_k x_gen)^q - a₃)`
- **What**: τ_k image of `addSlope` for negFrob in explicit slope form. Used to identify the slope ingredient in the addX/addY identities.
- **How**: Directly applies `map_addSlope_negFrobeniusIsog_K_algHom` at `f = τ_k.toAlgHom`.
- **Hypotheses**: `k : W.toAffine.Point`.
- **Uses from project**: `map_addSlope_negFrobeniusIsog_K_algHom`, `translateAlgEquivOfPoint`, `negFrobeniusIsog`, `W_KE`
- **Used by**: `xy_family_addX_unconditional`, `xy_family_addY_unconditional`
- **Visibility**: public
- **Lines**: 308–320; proof length 1 line (term-mode)
- **Notes**: None

---

### `theorem xy_family_isogOneSub_negFrobenius_of_addX_addY_invariance`

- **Type**: Given `h_addX_inv` and `h_addY_inv` (the addX/addY curve identities for all kernel elements), derive the abstract xy_family hypothesis for `isogOneSub_negFrobenius`.
- **What**: Intermediate reducer: from addX/addY identities, derive addPullback invariance, which in turn gives the abstract xy_family.
- **How**: Applies `xy_family_isogOneSub_negFrobenius_of_addPullback_invariance` after rewriting via `translateAlgEquivOfPoint_addPullback_x/y_negFrobeniusIsog`.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K`, `h_addX_inv`, `h_addY_inv` for all kernel elements.
- **Uses from project**: `xy_family_isogOneSub_negFrobenius_of_addPullback_invariance`, `translateAlgEquivOfPoint_addPullback_x_negFrobeniusIsog`, `translateAlgEquivOfPoint_addPullback_y_negFrobeniusIsog`, `isogOneSub_negFrobenius`
- **Used by**: `xy_family_isogOneSub_negFrobenius`
- **Visibility**: public
- **Lines**: 340–368; proof length 8 lines
- **Notes**: None

---

### `theorem frobeniusAlgHom_comp_algebraMap`

- **Type**: `(FiniteField.frobeniusAlgHom K KE).comp (Algebra.ofId K KE) = Algebra.ofId K KE`
- **What**: The composition of the q-th power Frobenius AlgHom with the structure map `K → KE` equals the structure map — i.e., Frobenius fixes K-constants.
- **How**: `ext x` reduces to a definitional equality (Frobenius AlgHom is K-linear, so fixes algebraMap images).
- **Hypotheses**: None beyond `K` a finite field and `KE` the function field.
- **Uses from project**: None (pure Mathlib)
- **Used by**: `frobenius_KE_lift_eq_lift`
- **Visibility**: public
- **Lines**: 379–383; proof length 1 line
- **Notes**: The proof body is just `ext x` with no further steps — relies on definitional equality after applying function extensionality.

---

### `theorem frobenius_KE_lift_eq_lift`

- **Type**: `∀ k : W.toAffine.Point, Affine.Point.map (frobeniusAlgHom K KE) (liftPointToKE W k) = liftPointToKE W k`
- **What**: The Frobenius `Affine.Point.map` fixes the lift of any K-rational point to `W_KE`.
- **How**: Unfolds `liftPointToKE`, then applies `Affine.Point.map_map` to collapse the composition, uses `frobeniusAlgHom_comp_algebraMap` to identify the composite as `Algebra.ofId`, then `rfl`.
- **Hypotheses**: `k : W.toAffine.Point`.
- **Uses from project**: `liftPointToKE`, `frobeniusAlgHom_comp_algebraMap`
- **Used by**: `frobeniusW_KE_lift`
- **Visibility**: public
- **Lines**: 392–402; proof length 7 lines
- **Notes**: None

---

### `noncomputable def frobeniusW_KE`

- **Type**: `(W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point` — the Frobenius as an `AddMonoidHom` on W_KE points.
- **What**: Packages `Affine.Point.map (frobeniusAlgHom K KE)` as an `AddMonoidHom` for clean arithmetic interaction.
- **How**: Definition: `WeierstrassCurve.Affine.Point.map (FiniteField.frobeniusAlgHom K KE)`.
- **Hypotheses**: None.
- **Uses from project**: `W_KE`
- **Used by**: `frobeniusW_KE_lift`, `frobeniusW_KE_add_lift`, `id_sub_frobeniusW_KE_add_lift_eq`, `frobeniusW_KE_some`, `genericPoint_sub_frobeniusW_KE_apply`, `genericPoint_lift_sub_frobeniusW_KE_apply`, `some_sub_frobeniusW_KE_some_apply`, `τ_k_x_gen_ne_frob_τ_k_x_gen`; also used by `GapSpines.lean`, `WallAGeometricRealization.lean`, `PencilCovariance.lean`, `FrobeniusFixedPoint.lean`
- **Visibility**: public
- **Lines**: 419–422; definition
- **Notes**: Widely used externally — a key API export.

---

### `@[simp] theorem frobeniusW_KE_lift`

- **Type**: `∀ k : W.toAffine.Point, frobeniusW_KE W (liftPointToKE W k) = liftPointToKE W k`
- **What**: Frobenius fixes lifted K-rational points; the `@[simp]`-tagged corollary of `frobenius_KE_lift_eq_lift`.
- **How**: Direct application of `frobenius_KE_lift_eq_lift`.
- **Hypotheses**: `k : W.toAffine.Point`.
- **Uses from project**: `frobenius_KE_lift_eq_lift`, `frobeniusW_KE`, `liftPointToKE`
- **Used by**: `frobeniusW_KE_add_lift`
- **Visibility**: public (`@[simp]`)
- **Lines**: 426–428; proof length 1 line
- **Notes**: None

---

### `theorem frobeniusW_KE_add_lift`

- **Type**: `∀ P k, frobeniusW_KE W (P + liftPointToKE W k) = frobeniusW_KE W P + liftPointToKE W k`
- **What**: Frobenius commutes with translation by lifted K-rational points.
- **How**: Uses `AddMonoidHom.map_add` for `frobeniusW_KE`, then `frobeniusW_KE_lift`.
- **Hypotheses**: `P : (W_KE W).toAffine.Point`, `k : W.toAffine.Point`.
- **Uses from project**: `frobeniusW_KE`, `frobeniusW_KE_lift`, `liftPointToKE`
- **Used by**: `id_sub_frobeniusW_KE_add_lift_eq`
- **Visibility**: public
- **Lines**: 433–437; proof length 2 lines
- **Notes**: None

---

### `theorem id_sub_frobeniusW_KE_add_lift_eq`

- **Type**: `∀ P k, (P + liftPointToKE W k) - frobeniusW_KE W (P + liftPointToKE W k) = P - frobeniusW_KE W P`
- **What**: The `id − π` isogeny is translation-invariant under K-rational lifts: `(id − π)(P + lift k) = (id − π)(P)`.
- **How**: Rewrites via `frobeniusW_KE_add_lift` then uses `abel` for group arithmetic.
- **Hypotheses**: `P : (W_KE W).toAffine.Point`, `k : W.toAffine.Point`.
- **Uses from project**: `frobeniusW_KE_add_lift`, `frobeniusW_KE`, `liftPointToKE`
- **Used by**: `genericPoint_lift_sub_frobeniusW_KE_apply`
- **Visibility**: public
- **Lines**: 442–447; proof length 3 lines
- **Notes**: None

---

### `theorem frobeniusW_KE_some`

- **Type**: `∀ x y h, frobeniusW_KE W (Affine.Point.some x y h) = Affine.Point.some (frob x) (frob y) h'`
- **What**: Frobenius acts coordinate-wise on `some` points.
- **How**: Unfolds `frobeniusW_KE`, applies Mathlib's `Affine.Point.map_some`.
- **Hypotheses**: `h : (W_KE W).toAffine.Nonsingular x y`.
- **Uses from project**: `frobeniusW_KE`, `W_KE`
- **Used by**: `genericPoint_sub_frobeniusW_KE_apply`, `some_sub_frobeniusW_KE_some_apply`; also used by `GapSpines.lean`, `WallAGeometricRealization.lean`
- **Visibility**: public
- **Lines**: 459–471; proof length 3 lines
- **Notes**: None

---

### `theorem negY_frob_x_gen_frob_y_gen_eq_negFrob_pullback_y`

- **Type**: `(W_KE W).toAffine.negY (frob (x_gen W)) (frob (y_gen W)) = (negFrobeniusIsog W).pullback (y_gen W)`
- **What**: Identifies the negY of Frobenius-image coords with the negFrob pullback of y_gen.
- **How**: Rewrites via `negFrobeniusIsog_pullback_y_gen`, `frobeniusIsog_pullback_apply` (both coords), `FiniteField.coe_frobeniusAlgHom`; then `unfold negY; rfl`.
- **Hypotheses**: None.
- **Uses from project**: `negFrobeniusIsog`, `negFrobeniusIsog_pullback_y_gen`, `frobeniusIsog_pullback_apply`, `x_gen`, `y_gen`, `W_KE`
- **Used by**: `addPullback_x_negFrobenius_eq_curve_addX`, `addPullback_y_negFrobenius_eq_curve_addY`
- **Visibility**: public
- **Lines**: 477–485; proof length 5 lines
- **Notes**: None

---

### `theorem frob_x_gen_eq_negFrob_pullback_x`

- **Type**: `FiniteField.frobeniusAlgHom K KE (x_gen W) = (negFrobeniusIsog W).pullback (x_gen W)`
- **What**: The Frobenius image of x_gen equals the negFrob pullback of x_gen.
- **How**: Rewrites via `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `FiniteField.coe_frobeniusAlgHom`.
- **Hypotheses**: None.
- **Uses from project**: `negFrobeniusIsog`, `negFrobeniusIsog_pullback_x_gen`, `frobeniusIsog_pullback_apply`, `x_gen`
- **Used by**: `addPullback_x_negFrobenius_eq_curve_addX`, `addPullback_y_negFrobenius_eq_curve_addY`
- **Visibility**: public
- **Lines**: 491–495; proof length 2 lines
- **Notes**: None

---

### `theorem x_gen_ne_frob_x_gen`

- **Type**: `x_gen W ≠ FiniteField.frobeniusAlgHom K KE (x_gen W)`
- **What**: The generic x-coordinate differs from its Frobenius image (transcendence condition needed for point addition).
- **How**: Via contradiction: assumes `x_gen = frob x_gen`, applies `x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero` after rewriting `frobeniusIsog_pullback_apply` and `coe_frobeniusAlgHom`.
- **Hypotheses**: None (consequence of transcendence of x_gen).
- **Uses from project**: `x_gen`, `x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero`, `frobeniusIsog_pullback_apply`
- **Used by**: `genericPoint_sub_frobeniusW_KE_apply`, `τ_k_x_gen_ne_frob_τ_k_x_gen`
- **Visibility**: public
- **Lines**: 501–507; proof length 5 lines
- **Notes**: None

---

### `theorem addPullback_x_negFrobenius_eq_curve_addX`

- **Type**: `addPullback_x W (negFrobeniusIsog W) = (W_KE W).toAffine.addX (x_gen W) (frob (x_gen W)) ((W_KE W).toAffine.slope (x_gen W) (frob (x_gen W)) (y_gen W) ((W_KE W).toAffine.negY (frob (x_gen W)) (frob (y_gen W))))`
- **What**: Re-expresses `addPullback_x` for negFrob in terms of the Frobenius-coord curve-sum formula.
- **How**: Unfolds `addPullback_x` and `addSlope`, then rewrites using `frob_x_gen_eq_negFrob_pullback_x` and `negY_frob_x_gen_frob_y_gen_eq_negFrob_pullback_y` in reverse.
- **Hypotheses**: None.
- **Uses from project**: `addPullback_x`, `addSlope`, `frob_x_gen_eq_negFrob_pullback_x`, `negY_frob_x_gen_frob_y_gen_eq_negFrob_pullback_y`, `negFrobeniusIsog`, `x_gen`, `y_gen`, `W_KE`
- **Used by**: `genericPoint_sub_frobeniusW_KE_apply`, `genericPoint_lift_sub_frobeniusW_KE_apply`
- **Visibility**: public
- **Lines**: 513–525; proof length 3 lines
- **Notes**: None

---

### `theorem addPullback_y_negFrobenius_eq_curve_addY`

- **Type**: `addPullback_y W (negFrobeniusIsog W) = (W_KE W).toAffine.addY (x_gen W) (frob (x_gen W)) (y_gen W) ((W_KE W).toAffine.slope (x_gen W) (frob (x_gen W)) (y_gen W) (negY (frob (x_gen W)) (frob (y_gen W))))`
- **What**: Companion to `addPullback_x_negFrobenius_eq_curve_addX` for the y-coordinate.
- **How**: Same strategy — unfolds addPullback_y, addSlope, rewrites using the two identification lemmas.
- **Hypotheses**: None.
- **Uses from project**: `addPullback_y`, `addSlope`, `frob_x_gen_eq_negFrob_pullback_x`, `negY_frob_x_gen_frob_y_gen_eq_negFrob_pullback_y`, `negFrobeniusIsog`, `x_gen`, `y_gen`, `W_KE`
- **Used by**: `genericPoint_sub_frobeniusW_KE_apply`, `genericPoint_lift_sub_frobeniusW_KE_apply`
- **Visibility**: public
- **Lines**: 529–542; proof length 4 lines
- **Notes**: None

---

### `theorem genericPoint_sub_frobeniusW_KE_apply`

- **Type**: `genericPoint W - frobeniusW_KE W (genericPoint W) = Affine.Point.some (addPullback_x W (negFrobeniusIsog W)) (addPullback_y W (negFrobeniusIsog W)) h_sum`
- **What**: The curve subtraction `genericPoint − Frobenius(genericPoint)` at the W_KE level equals the point whose coordinates are `addPullback_x/y` for negFrob. This is the substantive identification of the `(id − π)` geometric image.
- **How**: Uses `frobeniusW_KE_some` to expand Frobenius on some, converts subtraction to addition of negation via `Affine.Point.neg_some`, applies `Affine.Point.add_of_X_ne` (using `x_gen_ne_frob_x_gen`), then uses `congr 1` with `addPullback_x/y_negFrobenius_eq_curve_addX/Y` to identify coordinates.
- **Hypotheses**: None (the nonsingular witness is built inline using `Affine.nonsingular_add`, `Affine.nonsingular_neg`, `Affine.baseChange_nonsingular`).
- **Uses from project**: `genericPoint`, `frobeniusW_KE`, `frobeniusW_KE_some`, `x_gen_ne_frob_x_gen`, `addPullback_x_negFrobenius_eq_curve_addX`, `addPullback_y_negFrobenius_eq_curve_addY`, `generic_nonsingular`, `addPullback_x`, `addPullback_y`, `negFrobeniusIsog`, `W_KE`
- **Used by**: `genericPoint_lift_sub_frobeniusW_KE_apply`; also used by `GapSpines.lean`, `WallAGeometricRealization.lean`
- **Visibility**: public
- **Lines**: 558–590; proof length ~19 lines (declaration total 33 lines, signature 14 lines)
- **Notes**: Proof > 30 lines (full declaration 34 lines including signature and nonsingular witness term). Key substantive theorem.

---

### `theorem genericPoint_lift_sub_frobeniusW_KE_apply`

- **Type**: `∀ k : W.toAffine.Point, (genericPoint W + liftPointToKE W k) - frobeniusW_KE W (genericPoint W + liftPointToKE W k) = Affine.Point.some (addPullback_x W (negFrobeniusIsog W)) (addPullback_y W (negFrobeniusIsog W)) h_sum`
- **What**: Translation-shifted version: the curve subtraction at `genericPoint + lift k` still equals `some(addPullback_x, addPullback_y)`.
- **How**: Rewrites via `id_sub_frobeniusW_KE_add_lift_eq` to reduce to the un-shifted case, then applies `genericPoint_sub_frobeniusW_KE_apply`.
- **Hypotheses**: `k : W.toAffine.Point`.
- **Uses from project**: `id_sub_frobeniusW_KE_add_lift_eq`, `genericPoint_sub_frobeniusW_KE_apply`, `genericPoint`, `liftPointToKE`, `frobeniusW_KE`, `addPullback_x`, `addPullback_y`, `negFrobeniusIsog`, `W_KE`
- **Used by**: `xy_family_addX_unconditional`, `xy_family_addY_unconditional`
- **Visibility**: public
- **Lines**: 603–620; proof length 3 lines
- **Notes**: None

---

### `theorem translateAlgEquivOfPoint_some_apply_x_gen`

- **Type**: `∀ xk yk h_ns, translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) (x_gen W) = translateX_xy W xk yk`
- **What**: For non-zero K-rational points, τ_k applied to x_gen equals the explicit translation formula `translateX_xy`.
- **How**: Case split on 2-torsion (`yk = negY xk yk`): both branches apply the appropriate `translateAlgEquivOfPoint_some_2tor` or `translateAlgEquivOfPoint_some_nonTor` rewrite, then the corresponding `translateAlgHom_of_2tor_apply_x_gen` or `translateAlgHom_apply_x_gen`.
- **Hypotheses**: `xk yk : K`, `h_ns : W.toAffine.Nonsingular xk yk`.
- **Uses from project**: `translateAlgEquivOfPoint`, `x_gen`, `translateX_xy`, `translateAlgEquivOfPoint_some_2tor`, `translateAlgEquivOfPoint_some_nonTor`, `translateAlgHom_of_2tor_apply_x_gen`, `translateAlgHom_apply_x_gen`
- **Used by**: `genericPoint_add_lift_eq_some`; also used by `PoleDivisorFallback.lean`, `PoleDivisor2Tor.lean`
- **Visibility**: public
- **Lines**: 635–643; proof length 5 lines
- **Notes**: None

---

### `theorem translateAlgEquivOfPoint_some_apply_y_gen`

- **Type**: `∀ xk yk h_ns, translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) (y_gen W) = translateY_xy W xk yk`
- **What**: Companion to `translateAlgEquivOfPoint_some_apply_x_gen` for y_gen.
- **How**: Same case split and lemma pattern.
- **Hypotheses**: `xk yk : K`, `h_ns : W.toAffine.Nonsingular xk yk`.
- **Uses from project**: `translateAlgEquivOfPoint`, `y_gen`, `translateY_xy`, `translateAlgEquivOfPoint_some_2tor`, `translateAlgEquivOfPoint_some_nonTor`, `translateAlgHom_of_2tor_apply_y_gen`, `translateAlgHom_apply_y_gen`
- **Used by**: `genericPoint_add_lift_eq_some`; also used by `PoleDivisorFallback.lean`, `PoleDivisor2Tor.lean`
- **Visibility**: public
- **Lines**: 648–656; proof length 5 lines
- **Notes**: None

---

### `theorem some_sub_frobeniusW_KE_some_apply`

- **Type**: For any `some x y h` with `x ≠ frob x`, `Affine.Point.some x y h - frobeniusW_KE W (Affine.Point.some x y h) = Affine.Point.some (addX(...)) (addY(...)) h_sum`
- **What**: Generalized curve-sum lemma: subtracting Frobenius from any `some` point (at generic coords) yields an explicit `some` in addX/addY form.
- **How**: Converts subtraction to addition of negation, applies `frobeniusW_KE_some` to expand the Frobenius, then `Affine.Point.add_of_X_ne` using `h_x_ne`.
- **Hypotheses**: `x y : FunctionField`, `h : (W_KE W).toAffine.Nonsingular x y`, `h_x_ne : x ≠ frob x`.
- **Uses from project**: `frobeniusW_KE`, `frobeniusW_KE_some`, `W_KE`
- **Used by**: `xy_family_addX_unconditional`, `xy_family_addY_unconditional`
- **Visibility**: public
- **Lines**: 662–699; proof length ~15 lines (declaration total 38 lines including long signature)
- **Notes**: Proof > 30 lines (full declaration 38 lines). Generalizes `genericPoint_sub_frobeniusW_KE_apply` to arbitrary `some` points.

---

### `theorem τ_k_x_gen_ne_frob_τ_k_x_gen`

- **Type**: `∀ k : W.toAffine.Point, translateAlgEquivOfPoint W k (x_gen W) ≠ FiniteField.frobeniusAlgHom K KE (translateAlgEquivOfPoint W k (x_gen W))`
- **What**: The τ_k-translated x_gen is not fixed by Frobenius, needed for the `add_of_X_ne` precondition at translated points.
- **How**: By contradiction: assumes equality, applies injectivity of τ_k, then uses `map_pow` to show τ_k commutes with q-th powers, reducing to `x_gen_ne_frob_x_gen`.
- **Hypotheses**: `k : W.toAffine.Point`.
- **Uses from project**: `translateAlgEquivOfPoint`, `x_gen`, `x_gen_ne_frob_x_gen`
- **Visibility**: public
- **Lines**: 704–718; proof length 11 lines
- **Notes**: None

---

### `theorem genericPoint_add_lift_eq_some`

- **Type**: `∀ k : W.toAffine.Point, ∃ h : (W_KE W).toAffine.Nonsingular (τ_k x_gen) (τ_k y_gen), genericPoint W + liftPointToKE W k = Affine.Point.some (τ_k x_gen) (τ_k y_gen) h`
- **What**: For any K-rational point k, the W_KE-point `genericPoint + lift k` equals `some(τ_k x_gen, τ_k y_gen)` for some nonsingular witness. Establishes the uniform identification needed for the `some.injEq` argument.
- **How**: Case split on `k = 0` vs `k = some xk yk h_ns`. For zero: `lift 0 = 0`, `generic + 0 = generic = some(x_gen, y_gen, h_gen)`, and `τ_0 = id`. For some: applies `genericPoint_add_liftSomePoint` to get the explicit sum, then identifies coordinates via `translateAlgEquivOfPoint_some_apply_x_gen/y_gen`.
- **Hypotheses**: `k : W.toAffine.Point`.
- **Uses from project**: `genericPoint`, `liftPointToKE`, `liftSomePoint`, `liftPointToKE_some`, `genericPoint_add_liftSomePoint`, `translateAlgEquivOfPoint_some_apply_x_gen`, `translateAlgEquivOfPoint_some_apply_y_gen`, `x_gen`, `y_gen`, `translateAlgEquivOfPoint`, `x_gen_sub_const_ne_zero`, `generic_nonsingular`, `W_KE`
- **Used by**: `xy_family_addX_unconditional`, `xy_family_addY_unconditional`
- **Visibility**: public
- **Lines**: 729–762; proof length 26 lines (declaration total 34 lines)
- **Notes**: Proof > 30 lines (full declaration 34 lines). Key step enabling the `some.injEq` argument.

---

### `theorem xy_family_addX_unconditional`

- **Type**: `∀ hq, ∀ k : (isogOneSub_negFrobenius W hq).kernel, (W_KE W).toAffine.addX (τ_k x_gen) ((τ_k x_gen)^q) (τ_k (addSlope W (negFrobeniusIsog W))) = addPullback_x W (negFrobeniusIsog W)`
- **What**: The substantive addX identity for all kernel elements — the x-coordinate part of the xy-family proof, proved unconditionally.
- **How**: Rewrites slope via `translateAlgEquivOfPoint_addSlope_negFrobeniusIsog`, obtains the `some` form via `genericPoint_add_lift_eq_some`, applies `some_sub_frobeniusW_KE_some_apply` at the translated point, combines with `genericPoint_lift_sub_frobeniusW_KE_apply`, and extracts the first component via `Affine.Point.some.injEq`.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K`, `k : (isogOneSub_negFrobenius W hq).kernel`.
- **Uses from project**: `translateAlgEquivOfPoint_addSlope_negFrobeniusIsog`, `genericPoint_add_lift_eq_some`, `some_sub_frobeniusW_KE_some_apply`, `genericPoint_lift_sub_frobeniusW_KE_apply`, `τ_k_x_gen_ne_frob_τ_k_x_gen`, `isogOneSub_negFrobenius`, `addPullback_x`, `negFrobeniusIsog`, `W_KE`
- **Used by**: `xy_family_isogOneSub_negFrobenius`
- **Visibility**: public
- **Lines**: 780–801; proof length 16 lines
- **Notes**: None

---

### `theorem xy_family_addY_unconditional`

- **Type**: `∀ hq, ∀ k : (isogOneSub_negFrobenius W hq).kernel, (W_KE W).toAffine.addY (τ_k x_gen) ((τ_k x_gen)^q) (τ_k y_gen) (τ_k (addSlope W (negFrobeniusIsog W))) = addPullback_y W (negFrobeniusIsog W)`
- **What**: Companion addY identity. The y-coordinate part of the xy-family proof, proved unconditionally.
- **How**: Identical strategy to `xy_family_addX_unconditional`, extracting the second component of `Affine.Point.some.injEq`.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K`, `k : (isogOneSub_negFrobenius W hq).kernel`.
- **Uses from project**: `translateAlgEquivOfPoint_addSlope_negFrobeniusIsog`, `genericPoint_add_lift_eq_some`, `some_sub_frobeniusW_KE_some_apply`, `genericPoint_lift_sub_frobeniusW_KE_apply`, `τ_k_x_gen_ne_frob_τ_k_x_gen`, `isogOneSub_negFrobenius`, `addPullback_y`, `negFrobeniusIsog`, `W_KE`
- **Used by**: `xy_family_isogOneSub_negFrobenius`
- **Visibility**: public
- **Lines**: 804–820; proof length 11 lines
- **Notes**: None

---

### `theorem xy_family_isogOneSub_negFrobenius`

- **Type**: `∀ hq : 2 ≤ Fintype.card K, ∀ k : (isogOneSub_negFrobenius W hq).kernel, (τ_k ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) = (isogOneSub_negFrobenius W hq).pullback (x_gen W)) ∧ (τ_k ((isogOneSub_negFrobenius W hq).pullback (y_gen W)) = (isogOneSub_negFrobenius W hq).pullback (y_gen W))`
- **What**: The main unconditional theorem: for any kernel element k of `isogOneSub_negFrobenius`, translation by k fixes the pullbacks of x_gen and y_gen — the fully discharged `xy_family` hypothesis for the Layer-2 framework.
- **How**: Directly applies `xy_family_isogOneSub_negFrobenius_of_addX_addY_invariance` with the unconditional proofs `xy_family_addX_unconditional` and `xy_family_addY_unconditional`.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K`.
- **Uses from project**: `xy_family_isogOneSub_negFrobenius_of_addX_addY_invariance`, `xy_family_addX_unconditional`, `xy_family_addY_unconditional`, `isogOneSub_negFrobenius`
- **Used by**: `PoleDivisorFallback.lean` (multiple sites), `PoleDivisor2Tor.lean`
- **Visibility**: public
- **Lines**: 825–835; proof length 2 lines (term-mode)
- **Notes**: The file's primary export.

---

## Cross-reference summary

| Declaration | Internal callers |
|---|---|
| `W_KE_map_K_algHom` | 4 (`map_addX`, `map_negY`, `map_addY`, `map_slope`) |
| `map_negFrobeniusIsog_pullback_x_gen_K_algHom` | 3 (`map_addSlope_neg`, `map_addPullback_x_neg`, `map_addPullback_y_neg`) |
| `map_negY_K_algHom` | 0 (unused in file and project) |
