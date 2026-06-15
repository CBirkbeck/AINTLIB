# T-IV-4-002: Normalized differential

**Status**: REVIEW
**Silverman**: IV.4 def
**Module**: `HasseWeil/FormalGroup/InvariantDiff.lean`
**Owner**: worker-D
**Checked out at**: 2026-04-17T14:00:00Z
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: D

## Depends on
- T-IV-4-001 (InvariantDifferential)

## Blocks
- T-IV-4-003 (unique form)
- T-IV-4-004 (every is aω)

## Statement (Silverman IV.4 def)
An invariant differential `ω = P(T) dT` is **normalized** if `P(0) = 1`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

def InvariantDifferential.IsNormalized {F : FormalGroup R} (ω : InvariantDifferential F) : Prop :=
  (ω.toSeries.coeff R 0) = 1

end HasseWeil.FormalGroup
```

## Progress log
- 2026-04-13 [worker-A] PARTIAL. `invariantDiff_constantCoeff` in Differential.lean
  already proves `P(0) = 1`. The `IsNormalized` predicate is trivial once
  `InvariantDifferential` structure exists (T-IV-4-001).
- 2026-04-17T14:00Z [worker-D] Verified: `InvariantDifferential.IsNormalized`
  defined in `HasseWeil/FormalGroup/InvariantDiff.lean` as
  `η.scalar = 1` where `scalar` is the constant coefficient. This is
  definitionally equal to the ticket's `(ω.toSeries.coeff R 0) = 1`.
  `isNormalized_iff` additionally proves the equivalence with
  `toSeries = F.invariantDiff`. Build clean, standard axioms only.
  Status → REVIEW.
