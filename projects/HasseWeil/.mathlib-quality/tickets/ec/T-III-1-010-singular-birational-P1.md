# T-III-1-010: Singular Weierstrass curve birational to ℙ¹

**Status**: OPEN
**Silverman**: III.1.6
**Module**: `HasseWeil/EC/Weierstrass.lean`
**Owner**: (unassigned)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: B

## Depends on
- T-III-1-005 (node iff)
- T-III-1-006 (cusp iff)

## Blocks
- T-III-2-007, T-III-2-008 (E_ns ≅ G_a or G_m — optional)

## Statement (Silverman III.1.6)
A singular Weierstrass curve `E` (with `Δ = 0`) is birationally equivalent to
`ℙ¹` over `K̄`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- A singular Weierstrass curve is birational to ℙ¹.
    Reference: Silverman III.1.6. -/
theorem WeierstrassCurve.singular_birational_P1
    (E : WeierstrassCurve F) (hΔ : E.Δ = 0) :
    Nonempty (E.toAffine.FunctionField ≃ₐ[F] RatFunc F)

end HasseWeil.EC
```

## Notes
- Constructive proof via parametrization through the singular point
  `(x₀, y₀)`. Set `t = (y - y₀)/(x - x₀)` and solve.
- Optional for the Hasse-Weil critical path; included for mathlib quality.

## Progress log
