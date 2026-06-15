# Inventory: ./HasseWeil/Pic0/IsogenyClassGroup.lean

**File summary**: 8 declarations (1 structure, 1 noncomputable def `toAlgebra`, 2 theorems in `Isogeny.CoordHom`, 2 noncomputable defs + 2 theorems in `Isogeny`). No `sorry`. No `set_option maxHeartbeats`. All proofs are short. The file is purely infrastructure — it packages the coordinate-ring restriction data and lifts the `ClassGroup.relNorm`/`ClassGroup.map` machinery to the `Isogeny` namespace.

---

## Declarations

---

### `structure Isogeny.CoordHom`

- **Type**: `(α : Isogeny E E) → Type*` — a structure with two fields: `toAlgHom : E.CoordinateRing →ₐ[F] E.CoordinateRing` and `compat : ∀ u, α.pullback (algebraMap R FF u) = algebraMap R FF (toAlgHom u)`.
- **What**: Packages the data of a coordinate-ring restriction for an endomorphism `α : Isogeny E E`: an `F`-algebra endomorphism of `E.CoordinateRing` that is compatible (via `compat`) with the function-field pullback `α.pullback`.
- **How**: Pure structure definition; no proof content.
- **Hypotheses**: None beyond `α : Isogeny E E`.
- **Uses from project**: `Isogeny.pullback` (from `HasseWeil.Basic` / `HasseWeil.Isogeny`).
- **Used by**: `Isogeny.CoordHom.toAlgebra`, `faithfulSMul`, `isTorsionFree`, `classNorm`, `classMap`, `degree_eq_finrank_coordinateRing_of_tower_eq`, `classNorm_comp_classMap`, `classNorm_comp_classMap_degree`; also heavily used in `RouteCGeometric.lean`, `PicDual.lean`, `RouteCTheoremOfSquare.lean`, etc.
- **Visibility**: public
- **Lines**: 74–83, structure (no proof)
- **Notes**: Mirrors `Curves.CurveMap.CoordHom`; the integrality-preservation content of Silverman III.3.4 is deliberately NOT discharged here and is carried as data.

---

### `noncomputable def Isogeny.CoordHom.toAlgebra`

- **Type**: `(ch : α.CoordHom) → Algebra E.CoordinateRing E.CoordinateRing`
- **What**: Constructs the `R`-algebra structure on `R = E.CoordinateRing` induced by `ch.toAlgHom`; uses `ch.toAlgHom.toRingHom.toAlgebra` so the scalar action is `r • x = ch.toAlgHom(r) * x`.
- **How**: One-liner: `ch.toAlgHom.toRingHom.toAlgebra`.
- **Hypotheses**: `ch : α.CoordHom`.
- **Uses from project**: `Isogeny.CoordHom` (field `toAlgHom`).
- **Used by**: `faithfulSMul`, `isTorsionFree`, `classNorm`, `classMap`, `classNorm_comp_classMap`, `classNorm_comp_classMap_degree`, `degree_eq_finrank_coordinateRing_of_tower_eq`; also externally in `PicDual.lean`.
- **Visibility**: public (`@[reducible]`)
- **Lines**: 90–92, trivial (1-line body)
- **Notes**: Marked `@[reducible]` to aid instance resolution. The `toAlgebra` name mirrors `Curves.CurveMap.CoordHom.toAlgebra`.

---

### `theorem Isogeny.CoordHom.faithfulSMul`

- **Type**: `(ch : α.CoordHom) → (hinj : Function.Injective ch.toAlgHom) → letI := ch.toAlgebra; FaithfulSMul E.CoordinateRing E.CoordinateRing`
- **What**: Deduces that `R` acts faithfully on `R` through `ch.toAlgebra`, given injectivity of `ch.toAlgHom`. Needed to satisfy the `FaithfulSMul` hypothesis for the relative norm machinery.
- **How**: Avoids `FaithfulSMul.of_injective` (which would re-trigger the `R → R` instance diamond with `Algebra.id`). Instead: from `r₁ • x = r₂ • x` for all `x`, take `x = 1`, use `Algebra.smul_def` + `mul_one` to get `toAlgHom r₁ = toAlgHom r₂`, then apply `hinj`.
- **Hypotheses**: Injectivity of `ch.toAlgHom`.
- **Uses from project**: `Isogeny.CoordHom.toAlgebra`.
- **Used by**: `isTorsionFree` (via `isTorsionFree hinj`), `classNorm`, `classMap` (both call `ch.isTorsionFree hinj`).
- **Visibility**: public
- **Lines**: 99–105, 6 lines
- **Notes**: The docstring explicitly explains the diamond-avoidance strategy.

---

### `theorem Isogeny.CoordHom.isTorsionFree`

- **Type**: `(ch : α.CoordHom) → (hinj : Function.Injective ch.toAlgHom) → letI := ch.toAlgebra; Module.IsTorsionFree E.CoordinateRing E.CoordinateRing`
- **What**: Deduces that `R` is torsion-free as an `R`-module through `ch.toAlgebra`, given injectivity of `ch.toAlgHom`. Required for `ClassGroup.relNorm` to be defined.
- **How**: For a regular `r ≠ 0`, shows `ch.toAlgHom r ≠ 0` (via `hinj` + `map_zero`), then uses `mul_left_cancel₀` to cancel from `ch.toAlgHom(r) * x = ch.toAlgHom(r) * y`. Avoids `trans_faithfulSMul` (same diamond reason as `faithfulSMul`).
- **Hypotheses**: Injectivity of `ch.toAlgHom`.
- **Uses from project**: `Isogeny.CoordHom.toAlgebra`.
- **Used by**: `classNorm`, `classMap` (both `haveI : Module.IsTorsionFree … := ch.isTorsionFree hinj`).
- **Visibility**: public
- **Lines**: 112–123, 11 lines
- **Notes**: Uses `isRegular_iff_ne_zero` from mathlib.

---

### `noncomputable def Isogeny.classNorm`

- **Type**: `(ch : α.CoordHom) → (hinj : Function.Injective ch.toAlgHom) → (hfin : letI := ch.toAlgebra; Module.Finite E.CoordinateRing E.CoordinateRing) → ClassGroup E.CoordinateRing →* ClassGroup E.CoordinateRing`
- **What**: The relative norm on the ideal class group induced by `ch`: the class-group shadow of the dual isogeny `α̂`. Delegates to `ClassGroup.relNorm` from `ClassGroupNorm.lean`.
- **How**: Sets up instances `Module.IsTorsionFree` (via `ch.isTorsionFree hinj`) and `Module.Finite` (from `hfin`), then calls `ClassGroup.relNorm (R := E.CoordinateRing) (S := E.CoordinateRing)`.
- **Hypotheses**: Injectivity of `ch.toAlgHom`; finiteness of `R` over `R` via `ch.toAlgebra`.
- **Uses from project**: `Isogeny.CoordHom.toAlgebra`, `Isogeny.CoordHom.isTorsionFree`, `ClassGroup.relNorm` (from `ClassGroupNorm.lean`).
- **Used by**: `classNorm_comp_classMap`, `classNorm_comp_classMap_degree`; externally by `PicDual.lean`.
- **Visibility**: public
- **Lines**: 138–144, 5 lines
- **Notes**: `Module.Finite` must be supplied by the caller (instantiable per isogeny); finiteness is not automatically derivable.

---

### `noncomputable def Isogeny.classMap`

- **Type**: `(ch : α.CoordHom) → (hinj : Function.Injective ch.toAlgHom) → (hfin : letI := ch.toAlgebra; Module.Finite E.CoordinateRing E.CoordinateRing) → ClassGroup E.CoordinateRing →* ClassGroup E.CoordinateRing`
- **What**: The ideal extension (class-group shadow of `α` itself) on the ideal class group induced by `ch`. Delegates to `ClassGroup.map` from `ClassGroupNorm.lean`.
- **How**: Mirrors `classNorm`: sets up `Module.IsTorsionFree` and `Module.Finite`, then calls `ClassGroup.map (R := E.CoordinateRing) (S := E.CoordinateRing)`.
- **Hypotheses**: Same as `classNorm`: injectivity of `ch.toAlgHom`, finiteness of `R` over `R` via `ch.toAlgebra`.
- **Uses from project**: `Isogeny.CoordHom.toAlgebra`, `Isogeny.CoordHom.isTorsionFree`, `ClassGroup.map` (from `ClassGroupNorm.lean`).
- **Used by**: `classNorm_comp_classMap`, `classNorm_comp_classMap_degree`; externally by `PicDual.lean`, `RouteCTheoremOfSquare.lean`.
- **Visibility**: public
- **Lines**: 151–157, 6 lines
- **Notes**: The `map` direction is the `R → R` ideal extension `[I] ↦ [I ⊗_R R]`; it is the class-group shadow of `α` (not the dual).

---

### `theorem Isogeny.degree_eq_finrank_coordinateRing_of_tower_eq`

- **Type**: `(ch : α.CoordHom) → (S : Type*) [CommRing S] [Algebra E.CoordinateRing S] [FaithfulSMul ...] [Algebra.IsAlgebraic ...] [NoZeroDivisors S] → (S' : Type*) [CommRing S'] [Algebra E.CoordinateRing S'] [Algebra S S'] [Module E.FunctionField S'] [IsScalarTower ...] [IsScalarTower ...] [IsFractionRing S S'] → (hSR : Module.finrank R S = Module.finrank R R [ch.toAlgebra]) → (hS'FF : Module.finrank FF S' = α.degree) → α.degree = Module.finrank R R [ch.toAlgebra]`
- **What**: Bridges the function-field degree `α.degree` to the coordinate-ring degree `Module.finrank R R` (under `ch.toAlgebra`), working around the same-type instance diamond that prevents a direct application of `Algebra.IsAlgebraic.finrank_of_isFractionRing` with `S = R` and `S' = FF` literally.
- **How**: The caller supplies nominal copies `S` (of `R` with `ch.toAlgebra`) and `S'` (of `FF` with the twisted tower) plus the two finrank-transfer equalities `hSR`, `hS'FF`. The proof is two `rw`s followed by a one-line `exact Algebra.IsAlgebraic.finrank_of_isFractionRing E.CoordinateRing E.FunctionField S S'`.
- **Hypotheses**: `ch : α.CoordHom`; fraction-field tower data for `S → S'` (type copies chosen by caller); finrank-transfer equalities `hSR`, `hS'FF`.
- **Uses from project**: `Isogeny.CoordHom` (for `ch.toAlgebra`); `Algebra.IsAlgebraic.finrank_of_isFractionRing` (from mathlib, applied via `Ramification.lean` infrastructure).
- **Used by**: `classNorm_comp_classMap_degree`; externally by `PicDual.lean` (called as `α.degree_eq_finrank_coordinateRing_of_tower_eq`).
- **Visibility**: public
- **Lines**: 182–194, 3-line proof
- **Notes**: The long docstring (160–181) carefully explains the same-type instance diamond. This is the key "degree bridge" theorem — see `RouteCTheoremOfSquare.lean` line 100.

---

### `theorem Isogeny.classNorm_comp_classMap`

- **Type**: `(ch : α.CoordHom) → (hinj : ...) → (hfin : ...) → (c : ClassGroup E.CoordinateRing) → α.classNorm ch hinj hfin (α.classMap ch hinj hfin c) = c ^ (letI := ch.toAlgebra; @Module.finrank R R _ _ ch.toAlgebra.toModule)`
- **What**: The class-group dual relation: composing the extension map with the relative norm raises a class to the power `finrank R R` (the coordinate-ring degree). This is the class-group shadow of `α̂ ∘ α = [deg α]`, with exponent expressed as the coordinate-ring finrank.
- **How**: Sets up the three instances (`Module.Finite`, `Module.IsTorsionFree`, `ch.toAlgebra`), then delegates to `ClassGroup.relNorm_comp_map` from `ClassGroupNorm.lean`.
- **Hypotheses**: `ch : α.CoordHom`; injectivity and finiteness as for `classNorm`/`classMap`.
- **Uses from project**: `Isogeny.CoordHom.toAlgebra`, `Isogeny.CoordHom.isTorsionFree`, `Isogeny.classNorm`, `Isogeny.classMap`, `ClassGroup.relNorm_comp_map` (from `ClassGroupNorm.lean`).
- **Used by**: `classNorm_comp_classMap_degree`; externally by `PicDual.lean` (line 208).
- **Visibility**: public
- **Lines**: 207–216, 9-line proof
- **Notes**: The exponent is `finrank R R` rather than `α.degree`; the `_degree` variant below provides the latter form.

---

### `theorem Isogeny.classNorm_comp_classMap_degree`

- **Type**: Same as `classNorm_comp_classMap` but with additional fraction-field tower witness hypotheses `(S, S', hSR, hS'FF)`, and conclusion `... = c ^ α.degree`.
- **What**: The class-group dual relation with the exponent expressed as `α.degree` (the function-field degree) instead of `finrank R R`.
- **How**: `rw [α.degree_eq_finrank_coordinateRing_of_tower_eq ch S S' hSR hS'FF]` rewrites the exponent from `α.degree` to `finrank R R`, then applies `classNorm_comp_classMap`.
- **Hypotheses**: `ch : α.CoordHom`; injectivity/finiteness; fraction-field tower witness for the degree bridge (types `S`, `S'` and equalities `hSR`, `hS'FF`).
- **Uses from project**: `Isogeny.degree_eq_finrank_coordinateRing_of_tower_eq`, `Isogeny.classNorm_comp_classMap`.
- **Used by**: Externally by `PicDual.lean` (referenced in docstring lines 188, 213).
- **Visibility**: public
- **Lines**: 226–240, 3-line proof
- **Notes**: Thin wrapper combining the two preceding results; the interesting content is in `degree_eq_finrank_coordinateRing_of_tower_eq` and `classNorm_comp_classMap`.
