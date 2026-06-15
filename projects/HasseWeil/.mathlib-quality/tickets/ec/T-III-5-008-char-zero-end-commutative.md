# T-III-5-008: char 0 ⇒ End E is commutative

**Status**: OPEN
**Silverman**: III.5.6(c)
**Module**: `HasseWeil/EC/InvariantDiff.lean`
**Owner**: (unassigned)
**Estimated lines**: 40
**Difficulty**: easy
**Stream**: B/E

## Depends on
- T-III-5-006 (ring hom End → K̄)
- T-III-5-007 (kernel = inseparable)
- T-III-4-005 (End is integral domain)

## Blocks
- (none in critical path; mathlib quality)

## Statement (Silverman III.5.6(c))
If `char K = 0`, then `End E` is a commutative ring.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- In characteristic zero, the endomorphism ring is commutative.
    Reference: Silverman III.5.6(c). -/
instance WeierstrassCurve.End.commRing
    (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] [CharZero F] :
    CommRing (Isogeny E E)

end HasseWeil.EC
```

## Notes
- In char 0, every nonzero isogeny is separable (no inseparability available).
  So the ring hom `End E → K̄` is injective. Since `K̄` is commutative, so is
  `End E`.

## Progress log
