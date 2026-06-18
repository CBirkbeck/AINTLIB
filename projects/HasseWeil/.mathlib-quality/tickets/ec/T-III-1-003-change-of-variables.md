# T-III-1-003: Change of variables formulas

**Status**: DONE
**Silverman**: III.1.2
**Module**: `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass`
**Owner**: mathlib
**Estimated lines**: 0 (mathlib)
**Difficulty**: trivial
**Stream**: B

## Depends on
- T-III-1-001 (Weierstrass equation)

## Blocks
- T-III-1-007 (iso ⇔ same j)

## Statement (Silverman III.1.2)
The only changes of variables that preserve the Weierstrass form are
`x = u² x' + r`, `y = u³ y' + s u² x' + t` for some `u ∈ K̄*`, `r, s, t ∈ K̄`.
Under such a change, `Δ' = u^{-12} Δ` and `j' = j`.

## Acceptance criteria

Mathlib provides this via `WeierstrassCurve.VariableChange`:
```lean
#check WeierstrassCurve.VariableChange
#check WeierstrassCurve.VariableChange.act
#check WeierstrassCurve.j_variableChange
```

## Notes
- All in mathlib.

## Progress log
- 2026-04-08 [auto] marked DONE
