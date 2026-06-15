# T-PIC-G-005: `AddHomProperty.descent_from_isAlgClosed` lemma

**Status**: OPEN
**Module**: `HasseWeil/EC/IsogenyAG/BaseChange.lean` (or `HomProperty.lean`)
**Owner**: —
**Estimated lines**: ~40
**Difficulty**: easy (after G-004)
**Phase**: G (descent infrastructure)

## Depends on

- T-PIC-G-002 (Isogeny.baseChange)
- T-PIC-G-003 (CoordHom.baseChange)
- T-PIC-G-004 (toPointMap_baseChange compatibility)
- `EC/IsogenyAG.lean` — `AddHomProperty` predicate
- `Curves/BaseChange.lean` — `includePoint`

## Blocks

- T-PIC-G-006 (final unconditional B-4-003)

## Statement

The descent lemma: if the base-changed isogeny has the AddHomProperty,
then so does the original.

```lean
theorem AddHomProperty.of_baseChange
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (L : Type*) [Field L] [Algebra F L]
    [(W₁.baseChange L).IsElliptic] [(W₂.baseChange L).IsElliptic]
    (h_inj : Function.Injective (algebraMap F L)) -- automatic for Field/Field
    (h_baseChange : (φ.baseChange L).AddHomProperty (cd.baseChange L)) :
    φ.AddHomProperty cd
```

## Mathematical content

`AddHomProperty φ cd` says: `∀ P Q, φ.toPointMap cd (P + Q) =
φ.toPointMap cd P + φ.toPointMap cd Q`.

Plan:
- `(W₁).Point ↪ (W₁.baseChange L).Point` via `includePoint`.
- The inclusion is a group hom (preserves +, 0).
- The base-changed isogeny's point map agrees with the original's via
  G-004's diagram commute.
- So if base-change is a hom, the original is a hom (restricted via
  inclusion).

## Naming

`AddHomProperty.of_baseChange` or `AddHomProperty.descent`.

## Generality

`[Field F] [Field L] [Algebra F L]`. Crucially, **no `[IsAlgClosed F]`**
on F — that's the whole point of descent.

## Proof approach

```lean
theorem AddHomProperty.of_baseChange φ cd L h_inj h_bc := by
  intro P Q
  -- Goal: φ.toPointMap cd (P + Q) = φ.toPointMap cd P + φ.toPointMap cd Q
  -- Apply includePoint L to both sides — it's injective (h_inj).
  apply (includePoint_injective L).mp
  -- Use that includePoint L is an additive hom
  rw [includePoint_add, includePoint_add]
  -- Use G-004 to swap includePoint and (φ.baseChange L).toPointMap
  rw [← Isogeny.toPointMap_baseChange, ← Isogeny.toPointMap_baseChange,
      ← Isogeny.toPointMap_baseChange]
  -- Now use h_bc directly
  exact h_bc _ _
```

~30 LOC.

## Helper lemmas needed

- `includePoint_zero : includePoint L (0 : W.Point) = 0` (~5 LOC).
- `includePoint_add : includePoint L (P + Q) = includePoint L P +
  includePoint L Q` (~15 LOC, the meaty bit). This is the **statement
  that the inclusion is a group hom** — separate from B-4-003 because
  the inclusion is given by coordinate functions and the group-law
  formulas are universal in the field.
- `includePoint_injective : Function.Injective (includePoint L)` (~5 LOC,
  follows from `algebraMap_injective`).

## Acceptance criteria

```lean
#print axioms HasseWeil.EC.AddHomProperty.of_baseChange
#print axioms includePoint_add
#print axioms includePoint_injective
```
all report only standard axioms.

## Risks

- **`includePoint_add` is mathlib-territory**. Mathlib has
  `WeierstrassCurve.Affine.Point.map_add` (or similar) for the
  base-change of the addition. Need to verify and adapt.

- If `includePoint_add` is hard to extract from mathlib, we may need
  ~30 LOC of explicit chord/tangent compatibility work. Worst case
  ticket inflates to ~70 LOC.

- The `injectivity` of `includePoint` — straightforward via
  `algebraMap_injective F L` (which holds for any extension of fields).

## Progress log
