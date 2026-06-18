# T-V-1-006: |#E(F_q) − q − 1| ≤ 2√q

**Status**: PARTIAL (HasseBound.lean assembled but with sorries elsewhere)
**Silverman**: V.1.1
**Module**: `HasseWeil/Hasse/HasseBound.lean`
**Owner**: (unassigned)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: F

## Depends on
- T-V-1-004 (#E = q + 1 - tr(π))
- T-V-1-005 (Cauchy-Schwarz)
- T-III-6-009 (deg is positive definite QF)

## Blocks
- (FINAL THEOREM)

## Statement (Silverman V.1.1)
For an elliptic curve `E` over `F_q`,
`|#E(F_q) − q − 1| ≤ 2 √q`.

## Acceptance criteria

```lean
namespace HasseWeil.Hasse

/-- Hasse's theorem on elliptic curves over finite fields.
    Reference: Silverman V.1.1. -/
theorem hasse_bound
    (p : ℕ) [hp : Fact p.Prime] (k : ℕ) (E : WeierstrassCurve (ZMod p))
    [Fact (E.Δ ≠ 0)] :
    ((Fintype.card (E.toAffine.Point) : ℤ) - p^k - 1)^2 ≤ 4 * p^k

end HasseWeil.Hasse
```

## Notes
- Assemble:
  1. `tr(π)² ≤ 4q` from Cauchy-Schwarz applied to `(1, π)` viewed as elements
     of `Hom(E, E)` with the `deg` quadratic form.
  2. `#E(F_q) - q - 1 = -tr(π)`, so `(#E - q - 1)² = tr(π)² ≤ 4q`.
- Existing assembly in `HasseWeil/HasseBound.lean`.

## Progress log
- 2026-04-08 [auto] PARTIAL — assembled but depends on resolved sorries elsewhere
