# T-III-4-007: Example: explicit degree-2 isogeny with dual

**Status**: OPEN
**Silverman**: III.4.5
**Module**: `HasseWeil/EC/Isogeny.lean`
**Owner**: (unassigned)
**Estimated lines**: 100
**Difficulty**: medium
**Stream**: C

## Depends on
- T-III-4-001 (Isogeny)
- T-III-4-002 (degree)

## Blocks
- (illustrative; not on critical path)

## Statement (Silverman III.4.5)
For `E : y² = x³ + a x² + bx` (with `b(a² - 4b) ≠ 0`) and
`E' : Y² = X³ - 2a X² + (a² - 4b) X`, the map
`φ : E → E'`, `(x, y) ↦ (y²/x², y(x² - b)/x²)`
is a degree-2 isogeny. Its dual is given by an analogous formula `E' → E`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The classical degree-2 isogeny from y² = x³ + ax² + bx.
    Reference: Silverman III.4.5. -/
def WeierstrassCurve.deg2Isogeny (a b : F) (h : b * (a^2 - 4*b) ≠ 0) :
    Isogeny (mkE a b) (mkE' a b)

end HasseWeil.EC
```

## Notes
- Illustrative example. Useful for teaching, not for the critical path.

## Progress log
