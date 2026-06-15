# T-PIC-A-004: `σ̄` is a group homomorphism

**Status**: DONE-VIA-PARENT (`picZeroIsoE` is an `AddEquiv` so the underlying
σ̄ is automatically a group hom; axiom-clean)
**Silverman**: III.3.4(c) implicit (σ̄ is a group hom)
**Module**: `HasseWeil/Curves/PicZero.lean`
**Owner**: —
**Estimated lines**: ~40
**Difficulty**: easy
**Phase**: A

## Depends on
- T-PIC-A-003 (`picZeroSum`)

## Blocks
- T-PIC-D-001 (diagram commute)
- T-PIC-F-002 (packaging σ̄ as MulEquiv)

## Statement

Bundle `picZeroSum` as an `AddMonoidHom`:

```lean
/-- The `σ̄ : Pic⁰(E) → E` map packaged as an additive homomorphism. -/
noncomputable def picZeroSumHom : PicProj₀ (⟨W⟩ : SmoothPlaneCurve F) →+ W.Point where
  toFun := picZeroSum W
  map_zero' := ...
  map_add' := ...
```

`map_zero'` is the zero-class case, `map_add'` follows from
`projectiveDivisorSum_add` (T-PIC-A-001) descended to the quotient.

## Mathlib check
Standard `AddMonoidHom` packaging.

## Naming
`picZeroSumHom`.

## Generality
Same as the Phase A defaults.

## Proof approach

Mechanical:
- `map_zero'`: `picZeroSum W 0 = picZeroSum W (Quot.mk 0) = projectiveDivisorSum W 0 = 0`.
- `map_add'`: the quotient projection respects addition; descend
  `projectiveDivisorSum_add`.

## Acceptance criteria

```lean
#print axioms HasseWeil.Curves.picZeroSumHom
```
reports only standard axioms.

## Progress log
