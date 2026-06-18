# T-PIC-B-003: `σ̄ ∘ κ = id` (one direction always works)

**Status**: DONE (`sigmaBar_picZeroOfPoint` in
`HasseWeil/Curves/Miller.lean`, axiom-clean — this is the `right_inv`
of `picZeroIsoE`)
**Silverman**: III.3.4(d) (κ inverse to σ̄ on points)
**Module**: `HasseWeil/Curves/PicZero.lean`
**Owner**: —
**Estimated lines**: ~40
**Difficulty**: easy
**Phase**: B

## Depends on
- T-PIC-A-003 (`picZeroSum`)
- T-PIC-B-001 (`picZeroOfPoint`)
- T-PIC-B-002 (basepoint lemma)

## Blocks
- T-PIC-D-001 (diagram commute uses round-trip)
- T-PIC-F-001 (the harder κ ∘ σ̄ = id direction)

## Statement

The "easy direction" of the σ̄ ↔ κ bijection:

```lean
@[simp] theorem picZeroSum_picZeroOfPoint (P : W.Point) :
    picZeroSum W (picZeroOfPoint W P) = P
```

By `picZeroSum_mk`, this reduces to:
- `projectiveDivisorSum W ((P).toProjective − (O).toProjective) = P`
- = `1 • P.toAffinePoint - 1 • 0` (using `projectiveDivisorSum_single`)
- = `P.toAffinePoint`
- = `P` (by definition of `Point.toProjectiveSmoothPoint.toAffinePoint`)

## Mathlib check
Trivial after the underlying defs.

## Naming
`picZeroSum_picZeroOfPoint` — `simp`-tagged.

## Generality
Same as Phase B defaults.

## Proof approach

```lean
@[simp] theorem picZeroSum_picZeroOfPoint (P : W.Point) :
    picZeroSum W (picZeroOfPoint W P) = P := by
  cases P with
  | zero =>
    simp [picZeroOfPoint, picZeroSum, projectiveDivisorSum_single]
  | some x y h =>
    simp [picZeroOfPoint, picZeroSum, projectiveDivisorSum_add,
      projectiveDivisorSum_single, ProjectiveSmoothPoint.toAffinePoint,
      SmoothPoint.toAffinePoint]
```

May need explicit unfolding of `ProjectiveSmoothPoint.toAffinePoint` and
`SmoothPoint.toAffinePoint` (the latter from
`HasseWeil/Curves/PointFunctor.lean`).

## Acceptance criteria

`#print axioms HasseWeil.Curves.picZeroSum_picZeroOfPoint` reports only
standard axioms. Tagged `@[simp]`.

## Progress log
