# T-III-1-009: div(ω) = 0 for the invariant differential (no RR)

**Status**: OPEN
**Silverman**: III.1.5
**Module**: `HasseWeil/EC/Weierstrass.lean` and `HasseWeil/EC/InvariantDiff.lean`
**Owner**: (unassigned)
**Estimated lines**: 200
**Difficulty**: hard (CRITICAL)
**Stream**: B/E

## Depends on
- T-III-1-002 (invariant differential)
- T-II-4-008 (order formula for f·dx)
- T-II-4-010 (div(ω))

## Blocks
- T-III-5-001 (translation invariance)
- T-III-5-002 (additivity)
- T-IV-BRIDGE-001..005

## Statement (Silverman III.1.5)
For an elliptic curve `E` with invariant differential
`ω = dx/(2y + a₁ x + a₃)`,
we have `div(ω) = 0`. In particular, `ω` is holomorphic and nonvanishing on `E`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The invariant differential of an elliptic curve has trivial divisor.
    Reference: Silverman III.1.5. -/
theorem WeierstrassCurve.div_invariantDifferential
    (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] :
    Differentials.divisorOf C E.invariantDifferential (by ...) = 0

end HasseWeil.EC
```

## Notes
- Silverman's normal proof of this uses Riemann-Roch (deg(K_E) = 2g - 2 = 0
  combined with the `0 ≤` from holomorphy, and then nonvanishing follows).
- We MUST avoid Riemann-Roch. Direct proof:
  1. At every affine point `(x₀, y₀)` with `2y₀ + a₁ x₀ + a₃ ≠ 0`, the function
     `2y + a₁ x + a₃` is regular and nonzero, and `dx` is regular nonzero (since
     `x − x₀` is a uniformizer there). So `ord = 0` at such points.
  2. At affine 2-torsion points (where `2y + a₁ x + a₃ = 0`), the function `y - y₀`
     is a uniformizer (because `x` has order 2 at such a point). Use the order
     formula for `dx` from T-II-4-008 to compute `ord(dx) = 1`, balancing the
     pole `ord(2y + a₁ x + a₃) = 1`. Net `ord(ω) = 0`.
  3. At the point at infinity `O`, use the local parameter `z = -x/y` (or `t = z`).
     Then `x = z⁻² + ...`, `y = -z⁻³ + ...`, and `dx = -2 z⁻³ dz + ...`,
     `2y + a₁ x + a₃ = -2 z⁻³ + ...`. So `ω = dz + ...`, hence `ord_O(ω) = 0`.
- This is the central direct calculation that lets us avoid RR.

## Progress log
