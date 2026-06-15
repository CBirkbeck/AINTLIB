# Inventory: ./HasseWeil/Isogeny.lean

**Total declarations**: 7  
**File length**: 97 lines  
**Imports**: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`, `Mathlib.LinearAlgebra.Dimension.Finrank`, `Mathlib.LinearAlgebra.Basis.VectorSpace`

---

## Overview

This file defines a *lightweight* `PullbackIsogeny` structure — an isogeny represented solely by its function-field pullback `φ* : K(E₂) →ₐ[F] K(E₁)`, without the point-level group homomorphism. It is **distinct** from the fuller `Isogeny` structure in `Basic.lean` (which adds `toAddMonoidHom`). The file establishes injectivity of the pullback, defines the degree via `Module.finrank`, and proves degree multiplicativity via the tower law.

**Note**: `PullbackIsogeny` is used by `SeparableDegree.lean`; most of the project uses the richer `Isogeny` (from `Basic.lean`), which duplicates `pullback_injective`, `toAlgebra`, `degree`, `comp`, `comp_algebraMap_eq`, and `comp_degree` nearly verbatim.

---

### `structure PullbackIsogeny`

- **Type**: `(F : Type*) [Field F] (W₁ W₂ : Affine F) [W₁.IsElliptic] [W₂.IsElliptic] : Type` with field `pullback : W₂.FunctionField →ₐ[F] W₁.FunctionField`
- **What**: An isogeny from `E₁` to `E₂` represented purely by the contravariant pullback on function fields, following Silverman III.4. No point-level group homomorphism is stored.
- **How**: Plain structure definition; no proof content.
- **Hypotheses**: `F` a field; `W₁`, `W₂` affine elliptic curves over `F`.
- **Uses from project**: None (only mathlib `Affine F`, `FunctionField`, `AlgHom`).
- **Used by**: `pullback_injective`, `toAlgebra`, `degree`, `comp`, `comp_algebraMap_eq`, `comp_degree` (all in this file); also used in `SeparableDegree.lean`.
- **Visibility**: public
- **Lines**: 38–41
- **Notes**: The `PullbackIsogeny` / `Isogeny` split is a potential duplication smell — `Basic.lean` re-declares essentially the same five lemmas.

---

### `theorem PullbackIsogeny.pullback_injective`

- **Type**: `(φ : PullbackIsogeny F W₁ W₂) → Function.Injective φ.pullback`
- **What**: Every `AlgHom` from a field is injective, since the kernel of a ring hom from a field is trivial.
- **How**: One-liner via `φ.pullback.toRingHom.injective` (mathlib `RingHom.injective` for fields).
- **Hypotheses**: None beyond the structure.
- **Uses from project**: None.
- **Used by**: Referenced in doc-comments; not called inside this file.
- **Visibility**: public
- **Lines**: 49–51, proof 1 line
- **Notes**: Dead code within this file; duplicated nearly verbatim in `Basic.lean:77–79`.

---

### `noncomputable def PullbackIsogeny.toAlgebra`

- **Type**: `(φ : PullbackIsogeny F W₁ W₂) → Algebra W₂.FunctionField W₁.FunctionField`
- **What**: Equips `K(E₁)` with a `K(E₂)`-algebra structure via the pullback `φ*`.
- **How**: `φ.pullback.toRingHom.toAlgebra` — turns the `AlgHom` into an `Algebra` instance.
- **Hypotheses**: None beyond the structure.
- **Uses from project**: `PullbackIsogeny` (via `φ.pullback`).
- **Used by**: `degree`, `comp_degree` (both in this file).
- **Visibility**: public (`@[reducible]`)
- **Lines**: 55–57, proof 1 line
- **Notes**: Marked `@[reducible]` to allow `Module.finrank` to see through it; duplicated in `Basic.lean:85–87`.

---

### `noncomputable def PullbackIsogeny.degree`

- **Type**: `(φ : PullbackIsogeny F W₁ W₂) → ℕ`
- **What**: The degree of the isogeny, defined as the `K(E₂)`-rank `[K(E₁) : φ*K(E₂)]` via `Module.finrank`.
- **How**: `@Module.finrank W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra.toModule` — direct application of `Module.finrank` with the algebra from `toAlgebra`.
- **Hypotheses**: None beyond the structure.
- **Uses from project**: `PullbackIsogeny.toAlgebra`.
- **Used by**: `comp_degree` (in this file).
- **Visibility**: public
- **Lines**: 61–62, proof 1 line
- **Notes**: Duplicated in `Basic.lean:91–92`. The `@` annotation is needed because `toAlgebra.toModule` requires an explicit instance argument.

---

### `noncomputable def PullbackIsogeny.comp`

- **Type**: `(ψ : PullbackIsogeny F W₂ W₃) → (φ : PullbackIsogeny F W₁ W₂) → PullbackIsogeny F W₁ W₃`
- **What**: Composition of isogenies; the pullback of `ψ ∘ φ` is `φ* ∘ ψ*` (contravariance).
- **How**: Structure constructor `{ pullback := φ.pullback.comp ψ.pullback }`.
- **Hypotheses**: None beyond the structures.
- **Uses from project**: `PullbackIsogeny` (two instances).
- **Used by**: `comp_algebraMap_eq`, `comp_degree` (both in this file).
- **Visibility**: public
- **Lines**: 67–69
- **Notes**: `set_option maxHeartbeats 400000` with justifying comment "AlgHom.comp on FunctionField needs extra heartbeats for typeclass synthesis." Duplicated in `Basic.lean:99–102` (which also adds `toAddMonoidHom` composition).

---

### `theorem PullbackIsogeny.comp_algebraMap_eq`

- **Type**: `(ψ : PullbackIsogeny F W₂ W₃) → (φ : PullbackIsogeny F W₁ W₂) → ∀ x : W₃.FunctionField, (ψ.comp φ).pullback x = φ.pullback (ψ.pullback x)`
- **What**: Unfolds the definition of the composed pullback: applying `(ψ ∘ φ)*` to `x` equals `φ*(ψ*(x))`.
- **How**: `rfl` — definitional equality by construction of `comp`.
- **Hypotheses**: None.
- **Uses from project**: `PullbackIsogeny.comp`.
- **Used by**: Not called within this file.
- **Visibility**: public
- **Lines**: 72–74, proof 1 line
- **Notes**: Dead code in this file. Duplicated in `Basic.lean:111–113`.

---

### `theorem PullbackIsogeny.comp_degree`

- **Type**: `(ψ : PullbackIsogeny F W₂ W₃) → (φ : PullbackIsogeny F W₁ W₂) → (ψ.comp φ).degree = φ.degree * ψ.degree`
- **What**: Degree multiplicativity: `deg(ψ ∘ φ) = deg(φ) · deg(ψ)`, following from the tower law for field extensions.
- **How**: Sets up three algebra instances (`inst₁`, `inst₂`, `inst₃`) and the scalar tower `IsScalarTower W₃.FF W₂.FF W₁.FF` via `IsScalarTower.of_algebraMap_eq`, then applies `Module.finrank_mul_finrank` from mathlib.
- **Hypotheses**: None beyond the structures. `Module.Free W₂.FF W₁.FF` is derived automatically from `Module.Free.of_divisionRing`.
- **Uses from project**: `PullbackIsogeny.degree`, `PullbackIsogeny.toAlgebra`, `PullbackIsogeny.comp`.
- **Used by**: Not called within this file.
- **Visibility**: public
- **Lines**: 80–92, proof 13 lines
- **Notes**: `set_option maxHeartbeats 800000` with justifying comment "Degree multiplicativity needs extra heartbeats for the tower law with FunctionField." Duplicated in `Basic.lean:119–133`. The `rfl` proof of the scalar tower is slightly simpler here than in `Basic.lean` (which uses an explicit `change`).
