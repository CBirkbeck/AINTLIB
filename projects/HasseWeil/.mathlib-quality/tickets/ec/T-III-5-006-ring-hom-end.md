# T-III-5-006: α ↦ a_α : End E → K̄ is a ring homomorphism

**Status**: OPEN (existing chain rule needed)
**Silverman**: III.5.6(a)
**Module**: `HasseWeil/EC/InvariantDiff.lean`
**Owner**: (unassigned)
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: B/E

## Depends on
- T-III-5-002 (additivity)
- T-III-5-010 (chain rule, already done)

## Blocks
- T-III-5-007 (kernel = inseparable)
- T-III-5-008 (char 0 ⇒ commutative)
- T-III-6-005 (dual additivity)

## Statement (Silverman III.5.6(a))
The map `α ↦ a_α : End E → K̄` defined by `α* ω = a_α · ω` is a (nontrivial)
ring homomorphism.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The pullback coefficient is a ring homomorphism End E → K̄.
    Reference: Silverman III.5.6(a). -/
def WeierstrassCurve.pullbackCoeffHom (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] :
    (Isogeny E E) →+* F

theorem WeierstrassCurve.pullbackCoeffHom_apply (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)]
    (α : Isogeny E E) :
    (E.pullbackCoeffHom α : F) • E.invariantDifferential =
      α.pullback E.invariantDifferential

end HasseWeil.EC
```

## Notes
- Additivity from T-III-5-002.
- Multiplicativity from the chain rule T-III-5-010 (`(αβ)* = β* α*`, so
  `a_{αβ} = a_α · a_β`).
- Currently the chain rule is in `InvariantDifferentialPullback.lean`.

## Progress log
