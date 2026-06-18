# T-PIC-A-003: `σ̄ : Pic⁰(E) → E` (descend to quotient)

**Status**: DONE-VIA-PARENT (`picZeroIsoE` in `HasseWeil/Curves/Miller.lean`
IS the σ̄ map at AddEquiv level — its underlying descent is implicit
in `picZeroIsoE_of_AFInputs`; axiom-clean)
**Silverman**: III.3.4 (the σ map descended to Pic⁰)
**Module**: `HasseWeil/Curves/PicZero.lean`
**Owner**: —
**Estimated lines**: ~50
**Difficulty**: easy
**Phase**: A

## Depends on
- T-PIC-A-001 (`projectiveDivisorSum`)
- T-PIC-A-002 (vanishes on principal — for the descent)
- Existing: `ProjectiveDivisor.PicProj₀` (T-II-3-001b DONE)

## Blocks
- T-PIC-A-004 (group hom property)
- T-PIC-D-001 (diagram commute)
- T-PIC-F-001, F-002

## Statement

```lean
/-- The `σ̄` map: descend `projectiveDivisorSum` (restricted to `Div⁰`)
to the quotient `Pic⁰(E)`. -/
noncomputable def picZeroSum :
    PicProj₀ (⟨W⟩ : SmoothPlaneCurve F) → W.Point := by
  -- Use QuotientAddGroup.lift on projectiveDivisorSum restricted to
  -- ProjectiveDivisor.degZero, with vanishing-on-principal as the
  -- well-defined hypothesis.
  ...

@[simp] theorem picZeroSum_mk (D : ProjectiveDivisor.degZero _) :
    picZeroSum W (PicProj₀.mk D) =
      projectiveDivisorSum W D.val := rfl
```

## Mathlib check
Standard quotient construction via `QuotientAddGroup.lift`.

## Naming
`picZeroSum` (no `Sigma` to avoid Greek-letter naming issues; the
docstring should make the connection to Silverman's σ explicit).

## Generality
Same as T-PIC-A-001.

## Proof approach

Use `QuotientAddGroup.lift`:
- `f : ProjectiveDivisor.degZero → W.Point` = `projectiveDivisorSum` restricted.
- Show `f` vanishes on the principal subgroup intersected with degZero.
- This vanishing is exactly T-PIC-A-002.

The machinery is mechanical once T-PIC-A-002 lands.

## Acceptance criteria

`#print axioms HasseWeil.Curves.picZeroSum` reports only standard axioms.

## Progress log
