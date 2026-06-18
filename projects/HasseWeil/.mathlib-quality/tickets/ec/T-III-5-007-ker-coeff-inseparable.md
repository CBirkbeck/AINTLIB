# T-III-5-007: ker(α ↦ a_α) = inseparable endomorphisms

**Status**: OPEN
**Silverman**: III.5.6(b)
**Module**: `HasseWeil/EC/InvariantDiff.lean`
**Owner**: (unassigned)
**Estimated lines**: 40
**Difficulty**: medium
**Stream**: B/E

## Depends on
- T-III-5-006 (ring hom)
- T-II-4-004 (separable ⇔ pullback nonzero)

## Blocks
- T-III-5-008 (char 0 ⇒ commutative)

## Statement (Silverman III.5.6(b))
`ker(α ↦ a_α)` is exactly the set of inseparable endomorphisms of `E` (including
the zero endomorphism).

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The kernel of the pullback-coefficient hom is the inseparable endomorphisms.
    Reference: Silverman III.5.6(b). -/
theorem WeierstrassCurve.pullbackCoeffHom_ker
    (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] :
    RingHom.ker E.pullbackCoeffHom = { α | α = 0 ∨ ¬ α.IsSeparable }

end HasseWeil.EC
```

## Notes
- `a_α = 0 ⇔ α* ω = 0 ⇔ α* = 0 ⇔ α inseparable or zero` (by T-II-4-004).

## Progress log
