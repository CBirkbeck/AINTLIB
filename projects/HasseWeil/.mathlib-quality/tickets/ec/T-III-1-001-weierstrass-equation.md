# T-III-1-001: Weierstrass equation, b's, c's, Δ, j

**Status**: DONE
**Silverman**: III.1
**Module**: `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass`
**Owner**: mathlib
**Estimated lines**: 0 (mathlib)
**Difficulty**: trivial
**Stream**: B

## Depends on
- (mathlib)

## Blocks
- T-III-1-002 (invariant differential)
- T-III-1-004 (nonsingular ⇔ Δ ≠ 0)

## Statement (Silverman III.1)
A **Weierstrass equation** has the form
`Y² + a₁ XY + a₃ Y = X³ + a₂ X² + a₄ X + a₆`,
with auxiliary quantities
- `b₂ = a₁² + 4a₂`, `b₄ = 2a₄ + a₁ a₃`, `b₆ = a₃² + 4a₆`,
  `b₈ = a₁²a₆ - a₁a₃a₄ + 4a₂a₆ + a₂a₃² - a₄²`
- `c₄ = b₂² - 24 b₄`, `c₆ = -b₂³ + 36 b₂ b₄ - 216 b₆`
- discriminant `Δ = -b₂²b₈ - 8b₄³ - 27 b₆² + 9 b₂ b₄ b₆`
- `j = c₄³ / Δ`

## Acceptance criteria

Already in mathlib as `WeierstrassCurve`. Confirm:
```lean
#check WeierstrassCurve
#check @WeierstrassCurve.b₂
#check @WeierstrassCurve.b₄
#check @WeierstrassCurve.b₆
#check @WeierstrassCurve.b₈
#check @WeierstrassCurve.c₄
#check @WeierstrassCurve.c₆
#check @WeierstrassCurve.Δ
#check @WeierstrassCurve.j
```

## Notes
- All present in mathlib. The relationship `4b₈ = b₂b₆ - b₄²` and other
  identities are also there.

## Progress log
- 2026-04-08 [auto] marked DONE — already in mathlib
