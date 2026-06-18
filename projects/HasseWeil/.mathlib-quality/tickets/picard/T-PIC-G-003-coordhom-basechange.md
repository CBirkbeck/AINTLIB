# T-PIC-G-003: `CoordHom.baseChange` along F → L

**Status**: OPEN
**Module**: `HasseWeil/EC/IsogenyAG/BaseChange.lean`
**Owner**: —
**Estimated lines**: ~50
**Difficulty**: medium
**Phase**: G (descent infrastructure)

## Depends on

- T-PIC-G-001 (`CurveMap.baseChange`)
- T-PIC-G-002 (`Isogeny.baseChange`)
- `Curves/CurveMap.lean:378` — `CurveMap.CoordHom` structure

## Blocks

- T-PIC-G-004 (`toPointMap_baseChange`)

## Statement

```lean
noncomputable def CurveMap.CoordHom.baseChange
    {φ : CurveMap C₁ C₂} (cd : φ.CoordHom)
    (L : Type*) [Field L] [Algebra F L] :
    (φ.baseChange L).CoordHom
```

## Mathematical content

A `CoordHom φ` provides explicit polynomial data witnessing the curve
map's coordinates: it's a witness that `φ.pullback` is induced by ring
homomorphisms on the coordinate rings (with explicit images of x, y).

After base-change to L, the same coordinate data lifts: if φ sends
`x_2 ↦ p(x_1, y_1)` and `y_2 ↦ q(x_1, y_1)` over F, then `φ_L` sends
`x_2 ↦ algebraMap_F_L applied to p` and `y_2 ↦ algebraMap_F_L applied
to q` over L.

## Naming

`CurveMap.CoordHom.baseChange` and `Isogeny.coordHomBaseChange`.

## Generality

`[Field F] [Field L] [Algebra F L]`. No additional hypotheses.

## Proof approach

The `CoordHom` structure has fields like `xPoly : Polynomial (Polynomial F)`,
`yPoly : Polynomial (Polynomial F)`, and proofs of compatibility with
`φ.pullback`. The base-change applies `Polynomial.map (algebraMap F L)`
to both `xPoly` and `yPoly`, then re-proves compatibility:

```lean
noncomputable def CurveMap.CoordHom.baseChange cd L :=
  { xPoly := cd.xPoly.map (Polynomial.mapAlgHom (algebraMap F L))
    yPoly := cd.yPoly.map (Polynomial.mapAlgHom (algebraMap F L))
    xPoly_eq := by
      -- Compatibility square via algebraMap commuting with eval₂
      ...
    yPoly_eq := by ...
  }
```

The compatibility re-proofs use `Polynomial.eval₂_map`,
`AlgHom.commutes`, and the function-field-base-change-includes lemma
from G-001. ~50 LOC.

## Acceptance criteria

```lean
#print axioms HasseWeil.Curves.CurveMap.CoordHom.baseChange
```
reports only standard axioms.

## Risks

- The exact field structure of `CoordHom` (xPoly, yPoly types) needs to
  be checked against `Curves/CurveMap.lean:378` — the comment above
  describes the typical shape but the actual fields may differ.

- The compatibility re-proofs may explode if `Polynomial.map` doesn't
  commute cleanly with the function-field embedding. Worst case:
  ~80 LOC.

## Progress log
