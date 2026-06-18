# T-V-1-005: Cauchy-Schwarz for positive definite QF

**Status**: DONE (HasseBound.lean)
**Silverman**: V.1.2
**Module**: `HasseWeil/HasseBound.lean` → `HasseWeil/Hasse/CauchySchwarz.lean`
**Owner**: (existing)
**Estimated lines**: 0 (existing)
**Difficulty**: trivial
**Stream**: F

## Depends on
- (basic linear algebra)

## Blocks
- T-V-1-006 (Hasse bound)

## Statement (Silverman V.1.2)
For a positive definite (integer-valued) quadratic form `q` on an abelian group,
and `x, y` in the group,
`|q(x + y) − q(x) − q(y)| ≤ 2 √(q(x) q(y))`.

## Acceptance criteria

Existing in `HasseWeil/HasseBound.lean`. Confirm:
```lean
#check HasseWeil.cauchySchwarzQF  -- or similar
```

## Progress log
- 2026-04-08 [auto] marked DONE — exists in HasseWeil/HasseBound.lean
