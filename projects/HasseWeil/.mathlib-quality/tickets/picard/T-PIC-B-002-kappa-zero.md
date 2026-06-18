# T-PIC-B-002: `κ(O) = 0` in `Pic⁰(E)`

**Status**: DONE (subsumed by T-PIC-B-001 — `picZeroOfPoint_zero` lemma in `HasseWeil/Curves/PicZero.lean`, axiom-clean as of 2026-05-13)
**Silverman**: III.3.4(d) — implicit (κ sends basepoint to identity).
**Module**: `HasseWeil/Curves/PicZero.lean`
**Owner**: —
**Estimated lines**: ~30
**Difficulty**: trivial
**Phase**: B

## Depends on
- T-PIC-B-001 (`picZeroOfPoint`)

## Blocks
- T-PIC-B-003 (round-trip identity)

## Statement

```lean
@[simp] theorem picZeroOfPoint_zero :
    picZeroOfPoint W (0 : W.Point) = 0
```

This is `(O) − (O) = 0` as a divisor class.

May already be subsumed by `picZeroOfPoint_zero` in T-PIC-B-001 (it
should be a `@[simp]` lemma there). If so, this ticket is just
verification.

## Mathlib check
Trivial.

## Naming
`picZeroOfPoint_zero`.

## Generality
Same as Phase B defaults.

## Proof approach

Unfold `picZeroOfPoint W 0`:
- `0 : W.Point = .zero`
- `Point.zero.toProjectiveSmoothPoint = .infinity`
- So the divisor is `Finsupp.single .infinity 1 - Finsupp.single .infinity 1 = 0`.
- `PicProj₀.mk 0 = 0`.

`simp [picZeroOfPoint, Point.toProjectiveSmoothPoint, ...]` likely closes.

## Acceptance criteria

`#print axioms HasseWeil.Curves.picZeroOfPoint_zero` reports only standard
axioms. The lemma is tagged `@[simp]`.

## Progress log

- 2026-05-13: Subsumed by T-PIC-B-001 — `picZeroOfPoint_zero` is already
  tagged `@[simp]` in PicZero.lean and axiom-clean. Status flipped to DONE.

