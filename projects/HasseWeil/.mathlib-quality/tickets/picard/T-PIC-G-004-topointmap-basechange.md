# T-PIC-G-004: `toPointMap_baseChange` compatibility square

**Status**: OPEN
**Module**: `HasseWeil/EC/IsogenyAG/BaseChange.lean`
**Owner**: —
**Estimated lines**: ~80
**Difficulty**: medium-hard (the technical core of descent)
**Phase**: G (descent infrastructure)

## Depends on

- T-PIC-G-001, G-002, G-003 (full base-change of Isogeny + CoordHom)
- `Curves/BaseChange.lean:67` — `includePoint`
- `EC/IsogenyAG.lean:114` — `Isogeny.toPointMap`

## Blocks

- T-PIC-G-005 (descent lemma)

## Statement

The fundamental "diagram commutes" identity for descent:

```lean
theorem Isogeny.toPointMap_baseChange
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (L : Type*) [Field L] [Algebra F L]
    [(W₁.baseChange L).IsElliptic] [(W₂.baseChange L).IsElliptic]
    (P : W₁.Point) :
    (φ.baseChange L).toPointMap (cd.baseChange L)
        (Affine.Point.includePoint L P) =
      Affine.Point.includePoint L (φ.toPointMap cd P)
```

(`Affine.Point.includePoint` is the version of `SmoothPlaneCurve.includePoint`
for `WeierstrassCurve.Affine.Point` — may already exist in mathlib as
`Affine.Point.map` or similar.)

## Mathematical content

This says: the point map of the base-changed isogeny, applied to a
"base-changed point", equals the base-change of the original point map's
image. In diagram form:

```
W₁.Point  ──φ.toPointMap cd──▶  W₂.Point
   │                                 │
   │ includePoint L                  │ includePoint L
   ▼                                 ▼
(W₁.baseChange L).Point ─────▶ (W₂.baseChange L).Point
                  (φ.baseChange L).toPointMap (cd.baseChange L)
```

This is the "naturality" of `toPointMap` with respect to base-change. It
holds because `toPointMap` is defined via evaluation of the coordinate
polynomials, and base-change commutes with polynomial evaluation.

## Naming

`Isogeny.toPointMap_baseChange` (or with `commute` suffix).

## Generality

`[Field F] [Field L] [Algebra F L]` plus `[IsElliptic]` on both sides
after base-change.

## Proof approach

Case-split on `P : W₁.Point`:

### Case P = .zero (basepoint)

By `toPointMap_zero` and `includePoint_zero` (the basepoint maps to the
basepoint, both before and after base-change):

```lean
| .zero => by simp [Isogeny.toPointMap_zero, includePoint_zero]
```

~5 LOC.

### Case P = .some x y h (affine point)

Both sides unfold to `(φ.toCurveMap.toPointMap cd ⟨x, y, h⟩).toAffinePoint`
and its base-change, where `toCurveMap.toPointMap` evaluates the
coordinate polynomials at `(x, y)`.

Key identity: for a polynomial `p ∈ F[X, Y]` and `(x, y) ∈ F²`:
`(p.map (algebraMap F L)).evalEval (algebraMap F L x) (algebraMap F L y) =
 algebraMap F L (p.evalEval x y)`.

This is `Polynomial.eval₂_map` applied twice + `AlgHom.commutes`.

```lean
| .some x y h => by
    simp only [Isogeny.toPointMap_some, ...]
    -- Reduce both sides to evalEval comparisons
    -- Apply the polynomial-eval-base-change lemma
    ext
    · exact polynomial_eval_baseChange ...
    · exact polynomial_eval_baseChange ...
```

~50 LOC, plus ~20 LOC for the `polynomial_eval_baseChange` helper if
not already in mathlib.

## Acceptance criteria

```lean
#print axioms HasseWeil.EC.Isogeny.toPointMap_baseChange
```
reports only standard axioms.

## Risks

- The `.toAffinePoint` step (project's bridge from `SmoothPoint` to
  `Affine.Point`) may add complications. Need a similar
  `toAffinePoint_baseChange` compatibility lemma. ~15 LOC extra.

- Mathlib may already have `Affine.Point.map` for base-change of points
  with the relevant functoriality. If so, this ticket simplifies
  significantly. **Pre-flight check**: search mathlib for
  `WeierstrassCurve.Affine.Point.map` before starting.

- The `CoordHom` field structure (per G-003) determines how the proof
  unfolds; mismatch could cost 30+ LOC.

## Progress log
