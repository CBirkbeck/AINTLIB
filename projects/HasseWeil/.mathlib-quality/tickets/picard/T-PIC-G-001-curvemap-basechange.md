# T-PIC-G-001: `CurveMap.baseChange` along F → L

**Status**: OPEN
**Module**: `HasseWeil/Curves/CurveMap.lean` (extension) or new
`HasseWeil/Curves/CurveMapBaseChange.lean`
**Owner**: —
**Estimated lines**: ~80 (including FunctionField base-change lemmas)
**Difficulty**: medium
**Phase**: G (descent infrastructure)

## Depends on

- `HasseWeil/Curves/BaseChange.lean` (DONE) — `SmoothPlaneCurve.baseChange`
- `HasseWeil/Curves/CurveMap.lean` (DONE) — `CurveMap` structure
- Mathlib: `IsScalarTower`, base-change of `FractionRing`, `Algebra.TensorProduct`

## Blocks

- T-PIC-G-002 (Isogeny.AG.baseChange)
- T-PIC-G-003 (CoordHom.baseChange)

## Statement

For a `CurveMap φ : C₁ → C₂` over F and an F-algebra extension L, produce
the base-changed `CurveMap`:

```lean
noncomputable def CurveMap.baseChange (φ : CurveMap C₁ C₂)
    (L : Type*) [Field L] [Algebra F L] :
    CurveMap (C₁.baseChange L) (C₂.baseChange L)
```

with `pullback`, `degree`, etc., compatible with the original via the
canonical embedding `K(C_i) → K(C_i ⊗ L)`.

## Mathematical content

A `CurveMap C₁ C₂` is essentially an algebra hom of function fields
`K(C₂) →+* K(C₁)`. After base-change L/F, this becomes
`K(C₂ ⊗ L) →+* K(C₁ ⊗ L)`.

The key identity needed: `K(C ⊗ L) = K(C) ⊗_F L` (function field
commutes with base change), or at least an F-algebra map
`K(C) ⊗_F L → K(C ⊗ L)`.

For curves: `C ⊗ L = Spec((F[x,y]/W) ⊗ L) = Spec(L[x,y]/W_L)` where
`W_L` is W with coefficients pushed forward via `algebraMap F L`. The
function field is `Frac(L[x,y]/W_L)`, which equals `Frac(F[x,y]/W) ⊗ L`
when L/F is separable (always true for our use: L = AlgebraicClosure F is
separable up to perfect closure issues, irrelevant for char 0; for char p
we need separable closure as L for the descent direction we care about).

## Naming

`CurveMap.baseChange`.

## Generality

`[Field F] [Field L] [Algebra F L]`. No alg-closure of L needed at this
level — L can be any F-algebra field.

## Proof approach

### Step 1: Base-change of `FunctionField`

```lean
noncomputable def SmoothPlaneCurve.functionField_baseChange
    (C : SmoothPlaneCurve F) (L : Type*) [Field L] [Algebra F L] :
    C.FunctionField →ₐ[F] (C.baseChange L).FunctionField
```

Definition: `K(C) → K(C ⊗ L)` is the canonical map sending `f ∈ K(C)` to
its image under the algebra-map-induced ring hom on coordinate rings,
extended to fraction fields.

~30 LOC.

### Step 2: Base-change of `CurveMap`

```lean
noncomputable def CurveMap.baseChange φ L :=
  { pullback := -- compose:
      -- (C₂ ⊗ L).FunctionField → C₂.FunctionField → C₁.FunctionField → (C₁ ⊗ L).FunctionField
      -- but we need it in the OPPOSITE direction... wait.
      ...
    pullback_injective := ...
  }
```

The contravariant nature of `CurveMap` means `(φ.baseChange L).pullback`
is a hom from `(C₂ ⊗ L).FunctionField` to `(C₁ ⊗ L).FunctionField`.
Construct it as the unique L-algebra extension of `φ.pullback` along the
inclusion `K(C_i) → K(C_i ⊗ L)`.

~30 LOC.

### Step 3: Compatibility lemmas

```lean
@[simp] theorem CurveMap.baseChange_pullback_includeFunction
    (φ : CurveMap C₁ C₂) (L : Type*) [Field L] [Algebra F L]
    (f : C₂.FunctionField) :
    (φ.baseChange L).pullback (functionField_baseChange C₂ L f) =
      functionField_baseChange C₁ L (φ.pullback f)
```

The square commutes: pullback ∘ include = include ∘ pullback.

~20 LOC.

## Acceptance criteria

```lean
#print axioms HasseWeil.Curves.CurveMap.baseChange
#print axioms HasseWeil.Curves.CurveMap.baseChange_pullback_includeFunction
```
report only standard axioms. No new sorries.

## Risks

- **Function field base-change** in mathlib: there is no direct lemma
  `Frac(R) ⊗ L = Frac(R ⊗ L)` in full generality. We may need to build
  it explicitly via `IsLocalization.ofIntegralClosure` or
  `Algebra.TensorProduct.localization`. ~20 LOC of bridge.

- **Inseparability concerns**: in characteristic p, base-change to
  `AlgebraicClosure F` may introduce inseparability issues for the
  pullback. For our use (L = AlgebraicClosure F), this is fine because
  we only need the *direction* `K(C_i) → K(C_i ⊗ L)`, which is always
  injective.

- **`@[reducible]` issues** with `SmoothPlaneCurve.baseChange`: ensuring
  `(C.baseChange L).FunctionField` definitionally unfolds nicely may
  require explicit `simp` lemmas.

## Progress log

### 2026-04-29 — foundation shipped, AlgHom-base-change deep-dived

**Shipped** in `HasseWeil/Curves/CurveMapBaseChange.lean` (~50 LOC, axiom-clean):
- `SmoothPlaneCurve.coordRingMap C L : C.CoordinateRing →+* (C.baseChange L).CoordinateRing`
  (= mathlib's `WeierstrassCurve.Affine.CoordinateRing.map`).
- `coordRingMap_injective` — via mathlib's `map_injective` + `algebraMap` injectivity.
- `SmoothPlaneCurve.functionFieldMap C L : C.FunctionField →+* (C.baseChange L).FunctionField`
  (= `IsFractionRing.map` of the coordRingMap).
- `functionFieldMap_injective`.
- `functionFieldMap_algebraMap` — the simp-square identifying
  `functionFieldMap` on `algebraMap`-images with the canonical
  algebraMap of `coordRingMap`.

**Outstanding**: constructing `cd_L.toAlgHom : (C₂.baseChange L).CR →ₐ[L]
(C₁.baseChange L).CR` from `cd.toAlgHom : C₂.CR →ₐ[F] C₁.CR`.

**Investigation findings**:

1. **Tensor product route**: `Algebra.TensorProduct.map (.id F L) cd.toAlgHom :
   L ⊗_F C₂.CR →ₐ[L] L ⊗_F C₁.CR` exists in mathlib. But the iso
   `L ⊗_F C.CR ≅ (C.baseChange L).CR` is NOT directly in mathlib for
   `AdjoinRoot`. Building it would be ~100-150 LOC of new infrastructure
   (potentially upstream-able).

2. **`AdjoinRoot.mapAlgHom` route**: applies to one-variable
   `AdjoinRoot p` where `p ∈ S[X]`, but our `CoordinateRing` is
   `AdjoinRoot W.polynomial` over `R[X]` (two-variable structure).
   Direct application doesn't work.

3. **`AdjoinRoot.lift` + manual L-linearity**: feasible but ~80-120 LOC.
   The X-image and Y-image are `coordRingMap C₁ L (cd.toAlgHom (X_or_Y))`.
   The `eval₂_zero` proof and L-linearity require careful manipulation of
   `Polynomial.map` and `AdjoinRoot` quotient structure.

4. **`extendScalarsOfSurjective`**: requires `algebraMap F L` surjective
   — fails for our case (e.g., F = ℚ, L = AlgebraicClosure ℚ).

**Decision needed**: which route to pursue, or whether to punt to
[IsAlgClosed F]-only B-4-003. See WITNESSES_PLAN.md "Open questions".

**Status**: foundation **DONE**, full ticket **partial** pending route choice.

### 2026-04-29 (cont.) — `CoordHom.baseChangeAlgHom` shipped via direct AdjoinRoot.liftAlgHom

After the initial subagent attempt at the abstract iso route stalled,
took the direct construction route. Shipped in
`HasseWeil/Curves/CurveMapBaseChange.lean` (now 212 LOC, all axiom-clean):

- `SmoothPlaneCurve.coordRingMap_algebraMap_F` — F-side compat lemma.
- `CurveMap.CoordHom.baseChangeXImage` — image of X in
  `(C₁.baseChange L).CR`.
- `CurveMap.CoordHom.baseChangeYImage` — image of Y.
- `CurveMap.CoordHom.baseChangeInnerAlgHom` — the inner `L[X] →ₐ[L]
  target` hom needed for `liftAlgHom`.
- `CurveMap.CoordHom.baseChange_inner_comp_mapRingHom_eq` — naturality
  square for the inner alg-hom.
- `CurveMap.CoordHom.baseChange_eval₂_zero` — Weierstrass equation
  evaluates to zero at the new (X, Y) images.
- **`CurveMap.CoordHom.baseChangeAlgHom`** — the main deliverable:
  `(C₂.baseChange L).CR →ₐ[L] (C₁.baseChange L).CR`.

All 7 declarations depend only on standard axioms.

### Outstanding for full G-001/G-002/G-003

To construct the **full** `CoordHom.baseChange` (the structure version
with `compat` field and a working `CurveMap.baseChange` to attach it to),
we still need:

- `cd.baseChangeAlgHom_injective`: requires faithfully-flat preservation
  of the F-injectivity of `cd.toAlgHom` to L. ~50-80 LOC of mathlib
  wrestling.
- `cd.baseChangeFunctionFieldHom`: extension of `baseChangeAlgHom` to
  function fields via `IsFractionRing.liftAlgHom` (gated on injectivity).
  ~15 LOC once injectivity lands.
- `CurveMap.baseChange` (parametrized by cd): the full structure.
  ~20 LOC.
- `CoordHom.baseChange` (full structure): ~20 LOC.

**Status**: `baseChangeAlgHom` (core data) DONE; structure-level wrapping
deferred pending injectivity proof (~100 LOC follow-up).
