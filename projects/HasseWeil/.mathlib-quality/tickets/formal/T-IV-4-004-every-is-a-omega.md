# T-IV-4-004: Every invariant differential is aω

**Status**: REVIEW
**Silverman**: IV.4.2 cont
**Module**: `HasseWeil/FormalGroup/InvariantDiff.lean`
**Owner**: worker-D
**Checked out at**: 2026-04-17T14:00:00Z
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: D

## Depends on
- T-IV-4-003 (unique normalized)

## Blocks
- T-IV-4-005 (chain rule)

## Statement (Silverman IV.4.2 second part)
Every invariant differential `η ∈ ω F` is of the form `η = a ω` for a unique
constant `a ∈ R`, where `ω` is the normalized invariant differential.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem InvariantDifferential.eq_smul_normalized (F : FormalGroup R)
    (η : InvariantDifferential F) :
    ∃! a : R, η.toSeries = a • F.normalizedDifferential.toSeries

end HasseWeil.FormalGroup
```

## Notes
- The constant `a` is precisely `η.toSeries.coeff R 0` (the constant term).

## Progress log
- 2026-04-17T14:00Z [worker-D] Verified: `InvariantDifferential.eq_smul_normalized`
  in `HasseWeil/FormalGroup/InvariantDiff.lean` exactly matches the ticket
  signature:
  `∃! a : R, η.toSeries = a • F.normalizedDifferential.toSeries`.
  The uniqueness direction extracts `a = η.scalar` via the constant
  coefficient. Build clean, standard axioms only. Status → REVIEW.
