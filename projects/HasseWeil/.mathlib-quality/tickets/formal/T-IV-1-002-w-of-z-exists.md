# T-IV-1-002: w(z) ∈ ℤ[a₁..a₆][[z]] exists

**Status**: PARTIAL (FormalGroup.lean)
**Silverman**: IV.1.1(a)
**Module**: `HasseWeil/FormalGroup/Curve.lean`
**Owner**: (existing)
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-1-001 (z, w defined)
- T-IV-1-005 (Hensel)

## Blocks
- T-IV-1-003 (uniqueness)
- T-IV-1-006 (x(z), y(z))
- T-IV-1-008 (formal addition)

## Statement (Silverman IV.1.1(a))
There exists a unique formal power series
`w(z) = z³(1 + (sum a_n z^n)) ∈ ℤ[a₁..a₆][[z]]`
satisfying `w = z³ + a₁ z w + a₂ z² w + a₃ w² + a₄ z w² + a₆ w³` (the
Weierstrass equation in `(z, w)` coordinates after dehomogenization).

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- The formal power series w(z) ∈ ℤ[a₁..a₆][[z]] expressing w as a series in z.
    Reference: Silverman IV.1.1(a). -/
def WeierstrassCurve.wSeries (E : WeierstrassCurve F) : PowerSeries F

theorem WeierstrassCurve.wSeries_satisfies (E : WeierstrassCurve F) :
    E.wSeries = (PowerSeries.X)^3 + E.a₁ • PowerSeries.X * E.wSeries + ...

end HasseWeil.FormalGroup
```

## Notes
- Existing in `HasseWeil/FormalGroup.lean`. The construction uses Hensel's
  Lemma over the formal power series ring.

## Progress log
- 2026-04-08 [auto] PARTIAL — partial in HasseWeil/FormalGroup.lean
