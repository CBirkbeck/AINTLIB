# T-PIC-B-001: `κ : E → Pic⁰(E)`, `P ↦ class of (P) − (O)`

**Status**: DONE (verified axiom-clean 2026-05-13: `kappaDivisor`, `kappaDivisor_degree`, `picZeroOfPoint`, `picZeroOfPoint_zero` all depend only on `[propext, Classical.choice, Quot.sound]`)
**Silverman**: III.3.4(d) (definition of κ)
**Module**: `HasseWeil/Curves/PicZero.lean`
**Owner**: —
**Estimated lines**: ~50
**Difficulty**: easy
**Phase**: B

## Depends on
- T-II-3-001b (DONE) — `ProjectiveDivisor`, `Finsupp.single`
- T-II-3-001b — `ProjectiveDivisor.degZero` and `PicProj₀`
- T-PIC-A-001 (so this Phase B has parallel Phase A foundation)

## Blocks
- T-PIC-B-002, T-PIC-B-003
- T-PIC-D-001 (diagram commute uses κ)
- T-PIC-F-001, F-002

## Statement

```lean
/-- The canonical map `κ : E(F) → Pic⁰(E)` sending `P ↦ class of (P) − (O)`.
On the basepoint `0 : W.Point`, `κ(0) = 0` (the class of `(O) − (O) = 0`). -/
noncomputable def picZeroOfPoint :
    W.Point → PicProj₀ (⟨W⟩ : SmoothPlaneCurve F) :=
  fun P =>
    PicProj₀.mk
      ⟨Finsupp.single P.toProjectiveSmoothPoint 1
        - Finsupp.single ProjectiveSmoothPoint.infinity 1,
       by simp [degree_proof]⟩

@[simp] theorem picZeroOfPoint_zero :
    picZeroOfPoint W 0 = 0 := ...

theorem picZeroOfPoint_some_x_y_h
    (x y : F) (h : W.Nonsingular x y) :
    picZeroOfPoint W (.some x y h) =
      PicProj₀.mk ⟨Finsupp.single (.affine ⟨x, y, h⟩) 1
        - Finsupp.single .infinity 1, ...⟩ := rfl
```

Where `Point.toProjectiveSmoothPoint` is a helper:
- `Point.zero ↦ ProjectiveSmoothPoint.infinity`
- `Point.some x y h ↦ ProjectiveSmoothPoint.affine ⟨x, y, h⟩`

## Mathlib check
Not in mathlib.

## Naming
- `picZeroOfPoint` (the κ map; descriptive over Greek-letter naming)
- `_zero`, `_some_x_y_h` simp/rfl lemmas

## Generality
Same as Phase A: `[Field F] [DecidableEq F] [W.IsElliptic]`.

## Proof approach

Build the underlying divisor `(P) − (O)`, package as
`ProjectiveDivisor.degZero` (degree is 1 + (-1) = 0), then apply the
quotient projection `PicProj₀.mk`.

The `Point.toProjectiveSmoothPoint` helper may need to be added to
`HasseWeil/Curves/ProjectiveDivisor.lean` if it doesn't exist; otherwise
build it locally in `PicZero.lean`.

## Acceptance criteria

`#print axioms HasseWeil.Curves.picZeroOfPoint` reports only standard axioms.

## Progress log

- 2026-05-13: Verified T-PIC-B-001 is shipped. `HasseWeil/Curves/PicZero.lean`
  contains `kappaDivisor`, `kappaDivisor_degree`, `picZeroOfPoint`,
  `picZeroOfPoint_zero`. All axiom-clean. Status flipped to DONE.

