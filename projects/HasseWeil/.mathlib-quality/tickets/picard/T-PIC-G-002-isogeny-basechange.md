# T-PIC-G-002: `Isogeny.AG.baseChange` along F → L

**Status**: OPEN
**Module**: `HasseWeil/EC/IsogenyAG/BaseChange.lean` (NEW FILE)
**Owner**: —
**Estimated lines**: ~30
**Difficulty**: easy (after G-001)
**Phase**: G (descent infrastructure)

## Depends on

- T-PIC-G-001 (`CurveMap.baseChange`)
- `HasseWeil/EC/IsogenyAG.lean` (DONE)
- Mathlib: `WeierstrassCurve.baseChange_isElliptic` (or analogue)

## Blocks

- T-PIC-G-003 (`CoordHom.baseChange`)
- T-PIC-G-004 (`toPointMap_baseChange`)

## Statement

```lean
noncomputable def Isogeny.baseChange (φ : Isogeny W₁ W₂)
    (L : Type*) [Field L] [Algebra F L]
    [(W₁.baseChange L).IsElliptic] [(W₂.baseChange L).IsElliptic] :
    Isogeny (W₁.baseChange L) (W₂.baseChange L)
```

## Mathematical content

A `Isogeny W₁ W₂` is a `CurveMap ⟨W₁⟩ ⟨W₂⟩` plus the field
`pullback_ordAtInfty_nonneg`. Both base-change naturally.

## Naming

`Isogeny.baseChange`.

## Generality

`[IsElliptic]` for the base-changed curves. For finite fields F = F_q
and L = F̄_q, both are elliptic provided W₁, W₂ are.

## Proof approach

```lean
noncomputable def Isogeny.baseChange (φ : Isogeny W₁ W₂) L :=
  { toCurveMap := φ.toCurveMap.baseChange L                  -- via G-001
    pullback_ordAtInfty_nonneg := by
      -- ord_∞ pulled back via base-change inherits from ord_∞ in F
      ...
  }

@[simp] theorem Isogeny.baseChange_toCurveMap (φ : Isogeny W₁ W₂) L :
    (φ.baseChange L).toCurveMap = φ.toCurveMap.baseChange L := rfl
```

The `pullback_ordAtInfty_nonneg` proof needs to invoke the
`include : K(C) → K(C ⊗ L)` map's compatibility with `ordAtInfty`:
`ordAtInfty (include f) = ordAtInfty f`. ~20 LOC.

## Acceptance criteria

```lean
#print axioms HasseWeil.EC.Isogeny.baseChange
```
reports only standard axioms.

## Risks

- The `IsElliptic` instance for `W.baseChange L` is provided by mathlib
  (`WeierstrassCurve.baseChange_isElliptic` or via the discriminant
  formula). Should "just work" but may need to thread the typeclass.

- The `ordAtInfty` base-change compatibility may need ~20 LOC of
  separate proof if not already in `Curves/Infinity.lean`.

## Progress log
