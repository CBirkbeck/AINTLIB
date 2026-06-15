# Inventory: ./HasseWeil/Curves/GaloisAction.lean

**File**: `HasseWeil/Curves/GaloisAction.lean`  
**Module**: `HasseWeil.Curves.GaloisAction`  
**Imports**: `HasseWeil.Curves.BaseChange`, `HasseWeil.Curves.Divisors`  
**Namespace**: `HasseWeil.Curves.SmoothPlaneCurve` (plus one declaration in `_root_.HasseWeil.Curves.Divisor`)  
**Total lines**: 131

---

## Summary

Defines the Galois group `L ≃ₐ[F] L` action on L-rational points and on divisors of a smooth plane curve, provides the notion of a divisor being defined over `F`, and packages Galois-fixed divisors as an additive subgroup. Closes tickets T-II-INFRA-C-003/004/005.

---

## Declarations

### `theorem baseChange_map_AlgEquiv`

- **Type**: `(σ : L ≃ₐ[F] L) : (C.baseChange L).toAffine.map (σ : L →+* L) = (C.baseChange L).toAffine`
- **What**: The base-changed curve's coefficients are fixed by any `F`-algebra automorphism σ, i.e., applying σ as a ring map to the Weierstrass model returns the same model.
- **How**: `ext` on the Weierstrass coefficient components, then `simp [WeierstrassCurve.map, AlgEquiv.commutes]` — `AlgEquiv.commutes` supplies that σ fixes `F`-algebra-map images (the coefficients of `C.baseChange L` lie in the image of `F`).
- **Hypotheses**: `F` is a field, `L` is an `F`-algebra, `C` is a smooth plane curve over `F`.
- **Uses from project**: `C.baseChange` (from `BaseChange.lean`).
- **Used by**: `mapPoint` (body, line 49).
- **Visibility**: public
- **Lines**: 37–39; proof = 1 line
- **Notes**: —

---

### `noncomputable def mapPoint`

- **Type**: `(σ : L ≃ₐ[F] L) (P : C.pointsOver L) : C.pointsOver L`
- **What**: Applies σ coordinatewise to an L-rational point `(x, y)`, producing a new L-rational point `(σ x, σ y)`; nonsingularity is preserved by `Affine.map_nonsingular`.
- **How**: The `nonsingular` field is obtained by rewriting along `baseChange_map_AlgEquiv` and then using mathlib's `WeierstrassCurve.Affine.map_nonsingular` with `σ.injective`.
- **Hypotheses**: σ is an F-algebra automorphism of L; P is a smooth L-point of `C.baseChange L`.
- **Uses from project**: `baseChange_map_AlgEquiv`, `C.pointsOver` (from `BaseChange.lean`).
- **Used by**: `MulAction` instance (anonymous, line 63), `mapPoint_x`, `mapPoint_y`.
- **Visibility**: public
- **Lines**: 44–51; proof body = 3 lines (term-mode)
- **Notes**: —

---

### `@[simp] theorem mapPoint_x`

- **Type**: `(σ : L ≃ₐ[F] L) (P : C.pointsOver L) : (C.mapPoint L σ P).x = σ P.x`
- **What**: The x-coordinate of `mapPoint σ P` is `σ(P.x)` — this is definitionally true (`rfl`).
- **How**: `rfl`.
- **Hypotheses**: same as `mapPoint`.
- **Uses from project**: `mapPoint`.
- **Used by**: unused in file (simp lemma for callers).
- **Visibility**: public
- **Lines**: 53–54; proof = `rfl`
- **Notes**: —

---

### `@[simp] theorem mapPoint_y`

- **Type**: `(σ : L ≃ₐ[F] L) (P : C.pointsOver L) : (C.mapPoint L σ P).y = σ P.y`
- **What**: The y-coordinate of `mapPoint σ P` is `σ(P.y)` — definitionally true.
- **How**: `rfl`.
- **Hypotheses**: same as `mapPoint`.
- **Uses from project**: `mapPoint`.
- **Used by**: unused in file (simp lemma for callers).
- **Visibility**: public
- **Lines**: 56–57; proof = `rfl`
- **Notes**: —

---

### `noncomputable instance : MulAction (L ≃ₐ[F] L) (C.pointsOver L)`

- **Type**: `MulAction (L ≃ₐ[F] L) (C.pointsOver L)`
- **What**: Makes the Galois group `L ≃ₐ[F] L` act on L-rational affine smooth points by coordinatewise application; verifies the `one_smul` and `mul_smul` axioms.
- **How**: `smul := mapPoint`; `one_smul` uses `AlgEquiv.one_apply` on each coordinate; `mul_smul` uses `AlgEquiv.mul_apply` on each coordinate (compositional action on fields).
- **Hypotheses**: same as `mapPoint`.
- **Uses from project**: `mapPoint` (via `smul` definition), `C.pointsOver`.
- **Used by**: `smul_x`, `smul_y`; `•` notation used in `divisor_mulAction`.
- **Visibility**: public (anonymous instance)
- **Lines**: 62–71; proof body = 8 lines
- **Notes**: —

---

### `@[simp] theorem smul_x`

- **Type**: `(σ : L ≃ₐ[F] L) (P : C.pointsOver L) : (σ • P).x = σ P.x`
- **What**: The x-coordinate of the Galois action equals σ applied to the x-coordinate; `rfl` by definitional unfolding of `smul`.
- **How**: `rfl`.
- **Hypotheses**: same as `mapPoint`.
- **Uses from project**: (the MulAction instance above, implicitly).
- **Used by**: unused in file (simp lemma).
- **Visibility**: public
- **Lines**: 73–74; proof = `rfl`
- **Notes**: —

---

### `@[simp] theorem smul_y`

- **Type**: `(σ : L ≃ₐ[F] L) (P : C.pointsOver L) : (σ • P).y = σ P.y`
- **What**: The y-coordinate of the Galois action equals σ applied to the y-coordinate; `rfl`.
- **How**: `rfl`.
- **Hypotheses**: same as `mapPoint`.
- **Uses from project**: (the MulAction instance above, implicitly).
- **Used by**: unused in file (simp lemma).
- **Visibility**: public
- **Lines**: 76–77; proof = `rfl`
- **Notes**: —

---

### `noncomputable instance divisor_mulAction : MulAction (L ≃ₐ[F] L) (Divisor (C.baseChange L))`

- **Type**: `MulAction (L ≃ₐ[F] L) (Divisor (C.baseChange L))`
- **What**: Makes the Galois group act on divisors by pushing forward the support map: `σ • (Σ n_P [P]) = Σ n_P [σ • P]`, implemented via `Finsupp.mapDomain`.
- **How**: `one_smul` uses `Finsupp.mapDomain_id` after rewriting `(1:AlgEquiv) • ·` to `id`; `mul_smul` uses `Finsupp.mapDomain_comp` after showing the multiplication of automorphisms gives function composition via `mul_smul σ τ P`.
- **Hypotheses**: `C` is a smooth plane curve over `F`, `L` is an `F`-algebra; relies on the MulAction on points.
- **Uses from project**: `Divisor` (from `Divisors.lean`), the anonymous `MulAction` instance on points (for `mul_smul σ τ P`).
- **Used by**: `smulDivisorHom`, `smul_divisor_eq_hom`, `Divisor.IsDefinedOverF`, `divisorF`, `mem_divisorF_iff`.
- **Visibility**: public (named instance)
- **Lines**: 83–94; proof body = 10 lines
- **Notes**: —

---

### `def _root_.HasseWeil.Curves.Divisor.IsDefinedOverF`

- **Type**: `{F} [Field F] {C : SmoothPlaneCurve F} {L} [Field L] [Algebra F L] (D : Divisor (C.baseChange L)) : Prop`
  - Body: `∀ σ : L ≃ₐ[F] L, σ • D = D`
- **What**: A divisor `D` on `C_L` is defined over `F` when it is fixed by every F-algebra automorphism of L — the standard Galois-fixed-divisor condition from Silverman II.3.
- **How**: Direct `Prop` definition, no proof.
- **Hypotheses**: none beyond types.
- **Uses from project**: `Divisor` (from `Divisors.lean`), `divisor_mulAction` (for the `•` notation).
- **Used by**: `divisorF` (carrier), `mem_divisorF_iff`.
- **Visibility**: public (in `_root_.HasseWeil.Curves.Divisor` namespace)
- **Lines**: 99–103; no proof
- **Notes**: Placed in `_root_` namespace so `D.IsDefinedOverF` dot notation is available on `Divisor`.

---

### `noncomputable def smulDivisorHom`

- **Type**: `(σ : L ≃ₐ[F] L) : Divisor (C.baseChange L) →+ Divisor (C.baseChange L)`
- **What**: The Galois action on divisors by σ, packaged as an additive monoid homomorphism using `Finsupp.mapDomain.addMonoidHom`.
- **How**: Direct application of `Finsupp.mapDomain.addMonoidHom (σ • ·)` — no proof needed.
- **Hypotheses**: same as `divisor_mulAction`.
- **Uses from project**: `Divisor` (from `Divisors.lean`), the MulAction on points.
- **Used by**: `smul_divisor_eq_hom`, `divisorF`.
- **Visibility**: public
- **Lines**: 106–108; body = 1 line (term)
- **Notes**: —

---

### `theorem smul_divisor_eq_hom`

- **Type**: `(σ : L ≃ₐ[F] L) (D : Divisor (C.baseChange L)) : σ • D = C.smulDivisorHom L σ D`
- **What**: The Galois action on a divisor D coincides with the additive hom `smulDivisorHom σ` applied to D; this is `rfl` by definition.
- **How**: `rfl`.
- **Hypotheses**: same as `smulDivisorHom`.
- **Uses from project**: `smulDivisorHom`.
- **Used by**: `divisorF` (lines 119, 120, 123).
- **Visibility**: public
- **Lines**: 110–111; proof = `rfl`
- **Notes**: —

---

### `noncomputable def divisorF : AddSubgroup (Divisor (C.baseChange L))`

- **Type**: `AddSubgroup (Divisor (C.baseChange L))`
- **What**: The subgroup of divisors defined over `F` — the Galois-fixed subgroup `Div_F(C)` of Silverman II.3.
- **How**: Carrier is `{D | D.IsDefinedOverF}`; `add_mem'` rewrites along `smul_divisor_eq_hom` and uses `map_add` (AddMonoidHom) + individual Galois-fixedness; `zero_mem'` uses `map_zero`; `neg_mem'` uses `map_neg`.
- **Hypotheses**: same as `divisor_mulAction`.
- **Uses from project**: `Divisor.IsDefinedOverF`, `smulDivisorHom`, `smul_divisor_eq_hom`.
- **Used by**: `mem_divisorF_iff`.
- **Visibility**: public
- **Lines**: 116–124; proof body = 8 lines (structure fields)
- **Notes**: —

---

### `theorem mem_divisorF_iff`

- **Type**: `(D : Divisor (C.baseChange L)) : D ∈ C.divisorF L ↔ D.IsDefinedOverF`
- **What**: Membership in `divisorF L` is equivalent to `IsDefinedOverF`; `Iff.rfl` since the carrier is definitionally equal.
- **How**: `Iff.rfl`.
- **Hypotheses**: same as `divisorF`.
- **Uses from project**: `divisorF`, `Divisor.IsDefinedOverF`.
- **Used by**: unused in file (API lemma for external use).
- **Visibility**: public
- **Lines**: 125–126; proof = `Iff.rfl`
- **Notes**: —

---

## Cross-reference summary

| Declaration | Used by (in file) |
|---|---|
| `baseChange_map_AlgEquiv` | `mapPoint` |
| `mapPoint` | MulAction instance, `mapPoint_x`, `mapPoint_y` |
| `mapPoint_x` | (unused in file) |
| `mapPoint_y` | (unused in file) |
| MulAction on points | `smul_x`, `smul_y`, `divisor_mulAction` |
| `smul_x` | (unused in file) |
| `smul_y` | (unused in file) |
| `divisor_mulAction` | `smulDivisorHom`, `Divisor.IsDefinedOverF`, `smul_divisor_eq_hom`, `divisorF`, `mem_divisorF_iff` |
| `Divisor.IsDefinedOverF` | `divisorF`, `mem_divisorF_iff` |
| `smulDivisorHom` | `smul_divisor_eq_hom`, `divisorF` |
| `smul_divisor_eq_hom` | `divisorF` |
| `divisorF` | `mem_divisorF_iff` |
| `mem_divisorF_iff` | (unused in file) |

---

## Statistics

- **Total declarations**: 13
- **defs** (including `noncomputable def`, `abbrev`, `instance`, `structure`, `def`): 6 (`mapPoint`, anonymous MulAction, `divisor_mulAction`, `smulDivisorHom`, `Divisor.IsDefinedOverF`, `divisorF`)
- **lemmas/theorems**: 7 (`baseChange_map_AlgEquiv`, `mapPoint_x`, `mapPoint_y`, `smul_x`, `smul_y`, `smul_divisor_eq_hom`, `mem_divisorF_iff`)
- **instances**: 2 (anonymous MulAction on points, `divisor_mulAction`)
- **sorries**: none
- **set_option maxHeartbeats**: none
- **long proofs (>30 lines)**: none
- **unused in file**: `mapPoint_x`, `mapPoint_y`, `smul_x`, `smul_y`, `mem_divisorF_iff` (all are simp/API lemmas for external callers)
- **key API** (used by 3+ others in file): `divisor_mulAction` (used by `smulDivisorHom`, `Divisor.IsDefinedOverF`, `smul_divisor_eq_hom`, `divisorF`, `mem_divisorF_iff` — 5 users)
