# T-III-1-008: Every j₀ ∈ K̄ has an EC realizing it

**Status**: DONE (mostly mathlib)
**Silverman**: III.1.4(c) cont
**Module**: `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass`
**Owner**: mathlib
**Estimated lines**: 0
**Difficulty**: easy
**Stream**: B

## Depends on
- T-III-1-007 (iso ⇔ same j)

## Blocks
- (informational)

## Statement (Silverman III.1.4(c) cont)
For every `j₀ ∈ K̄`, there exists an elliptic curve over `K̄(j₀)` with
`j`-invariant `j₀`.

## Acceptance criteria

Mathlib provides this construction (canonical curves for j = 0, j = 1728, and
the family for other j). Confirm:
```lean
-- pseudo
example (j₀ : F) : ∃ E : EllipticCurve F, E.j = j₀
```

## Notes
- For `j₀ ≠ 0, 1728`, the curve `Y² = X³ - 3 c X - 2 c` with `c = j₀/(j₀ - 1728)`
  works. For `j₀ = 0` use `Y² = X³ + 1`. For `j₀ = 1728` use `Y² = X³ + X`.
- This is in mathlib in some form via the universal family.

## Progress log
- 2026-04-08 [auto] marked DONE
