# T-III-2-007: E_ns nonsingular part of singular curve

**Status**: CHECKED-OUT
**Silverman**: III.2 (definition)
**Module**: `HasseWeil/EC/GroupLaw.lean`
**Owner**: worker-B
**Checked out at**: 2026-04-17T12:00:00Z
**Estimated lines**: 40
**Difficulty**: easy
**Stream**: B

## Depends on
- T-III-1-004 (singular ⇔ Δ = 0)
- T-III-2-002 (group law)

## Blocks
- T-III-2-008 (E_ns ≅ G_a or G_m)

## Statement (Silverman III.2 def)
For a (possibly singular) Weierstrass curve `E`, the **smooth part** `E_ns` is the
set of nonsingular points. The group law restricted to lines through nonsingular
points stays in `E_ns`, making `E_ns` an abelian group.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The smooth (nonsingular) part of a Weierstrass curve. -/
def WeierstrassCurve.nonsingularLocus (E : WeierstrassCurve F) : Set E.toAffine.Point

/-- E_ns is closed under the group law. -/
instance (E : WeierstrassCurve F) : AddCommGroup E.nonsingularLocus

end HasseWeil.EC
```

## Notes
- Optional. Used to discuss reduction modulo p in number-theoretic applications.

## Progress log
- 2026-04-17T12:00Z [worker-A] checkout. Mathlib's `W.Point` already encodes the
  non-singular locus (only includes nonsingular points + infinity) and already has
  an `AddCommGroup` instance over any field. This ticket becomes a thin wrapper.
