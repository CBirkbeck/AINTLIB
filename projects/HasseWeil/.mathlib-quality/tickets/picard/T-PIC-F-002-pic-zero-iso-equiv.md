# T-PIC-F-002: `σ̄ : Pic⁰(E) ≅ E` packaged as `AddEquiv`

**Status**: DONE (`picZeroEquiv` (alias for `picZeroIsoE`) in
`HasseWeil/Curves/Miller.lean`, axiom-clean — packages Pic⁰(E) ≃+ E
as an AddEquiv via `picZeroIsoE_of_AFInputs` applied to
`afInputs_unconditional`)
**Silverman**: III.3.4 (the iso itself)
**Module**: `HasseWeil/Curves/PicZero.lean`
**Owner**: —
**Estimated lines**: ~30
**Difficulty**: easy (mechanical packaging)
**Phase**: F

## Depends on
- T-PIC-A-004 (`picZeroSumHom`)
- T-PIC-B-001 (`picZeroOfPoint`)
- T-PIC-B-003 (`σ̄ ∘ κ = id`)
- T-PIC-F-001 (`κ ∘ σ̄ = id`)

## Blocks
- T-PIC-F-003 (final B-4-003 closure)

## Statement

```lean
/-- **Silverman III.3.4**: `Pic⁰(E) ≅ E` as additive groups, via the
sum-of-points map σ̄ with inverse κ. -/
noncomputable def picZeroEquiv :
    PicProj₀ (⟨W⟩ : Curves.SmoothPlaneCurve F) ≃+ W.Point where
  toFun := picZeroSum W
  invFun := picZeroOfPoint W
  left_inv := picZeroOfPoint_picZeroSum W   -- T-PIC-F-001
  right_inv := picZeroSum_picZeroOfPoint W  -- T-PIC-B-003
  map_add' := picZeroSumHom W |>.map_add'   -- T-PIC-A-004
```

## Mathlib check
N/A.

## Naming
`picZeroEquiv`.

## Generality
Inherits `[IsAlgClosed F]` from T-PIC-F-001.

## Proof approach

Mechanical AddEquiv packaging from the four sub-results.

## Acceptance criteria

`#print axioms HasseWeil.Curves.picZeroEquiv` reports only standard axioms.

## Progress log
