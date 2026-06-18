# T-III-3-001: Elliptic curve = (smooth genus-1 curve, base point)

**Status**: DONE
**Silverman**: III.3 (definition)
**Module**: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine`
**Owner**: mathlib
**Estimated lines**: 0
**Difficulty**: trivial
**Stream**: B

## Depends on
- T-III-1-001 (Weierstrass)

## Blocks
- T-III-3-002, T-III-3-003

## Statement (Silverman III.3 def)
An **elliptic curve** is a pair `(E, O)` where `E` is a smooth projective curve of
genus 1 and `O ∈ E(K)` is a distinguished base point.

We use mathlib's `WeierstrassCurve` structure as the model: every smooth genus-1
curve with a rational point arises from a Weierstrass equation (via Riemann-Roch
in Silverman III.3.1, but we sidestep this by always working with Weierstrass
curves directly).

## Acceptance criteria

```lean
#check EllipticCurve  -- mathlib structure
```

## Notes
- Per the project plan, we do NOT prove the III.3.1 statement that "every smooth
  genus-1 curve is a Weierstrass curve" (which uses RR). We work with Weierstrass
  curves as the model.

## Progress log
- 2026-04-08 [auto] marked DONE
