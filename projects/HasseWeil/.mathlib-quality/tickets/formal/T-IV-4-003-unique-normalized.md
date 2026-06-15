# T-IV-4-003: Unique normalized differential ω = F_X(0,T)⁻¹ dT

**Status**: REVIEW
**Silverman**: IV.4.2
**Module**: `HasseWeil/FormalGroup/InvariantDiff.lean`
**Owner**: worker-D
**Checked out at**: 2026-04-17T14:00:00Z
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-4-002 (normalized)

## Blocks
- T-IV-4-004 (every is aω)
- T-IV-4-005 (chain rule)
- T-IV-BRIDGE-001 (formal ↔ curve)

## Statement (Silverman IV.4.2)
There is a unique normalized invariant differential on `F`, given by
`ω(T) = (∂F/∂X (0, T))⁻¹ dT = (1 + (lower degree terms involving X)|_{X=0}, T) ⁻¹ dT`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- The unique normalized invariant differential.
    Reference: Silverman IV.4.2. -/
noncomputable def FormalGroup.normalizedDifferential (F : FormalGroup R) :
    InvariantDifferential F

theorem FormalGroup.normalizedDifferential_isNormalized (F : FormalGroup R) :
    F.normalizedDifferential.IsNormalized

theorem FormalGroup.normalizedDifferential_unique (F : FormalGroup R)
    (ω : InvariantDifferential F) (h : ω.IsNormalized) :
    ω = F.normalizedDifferential

end HasseWeil.FormalGroup
```

## Notes
- Existing partial implementation: `formalDiff` in `HasseWeil/FormalGroup.lean`.

## Progress log
- 2026-04-08 [auto] PARTIAL — exists in HasseWeil/FormalGroup.lean
- 2026-04-17T14:00Z [worker-D] Verified: `FormalGroup.normalizedDifferential`
  defined in `HasseWeil/FormalGroup/InvariantDiff.lean` with
  `toSeries = F.invariantDiff = invOfUnit F.dX_at_zero 1` and constant
  coefficient 1. `normalizedDifferential_isNormalized` and
  `normalizedDifferential_unique` both exist. Added stronger wrapper
  `normalizedDifferential_unique'` returning full structural equality
  `η = F.normalizedDifferential` (via `InvariantDifferential.ext`
  using proof-irrelevance on the `mul_dX_isConstant` Prop field) to match
  the ticket's exact signature. Build clean, standard axioms only.
  Status → REVIEW.
