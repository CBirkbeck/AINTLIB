# T-III-2-009: Translation map τ_Q : E → E as morphism

**Status**: OPEN
**Silverman**: III.4.7 (definition; placed in III.2 here for organizational reasons)
**Module**: `HasseWeil/EC/GroupLaw.lean`
**Owner**: (unassigned)
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: B

## Depends on
- T-III-2-002 (group law)
- T-II-2-001 (rational map ⇒ morphism)

## Blocks
- T-III-4-009 (translation map for isogenies)
- T-III-5-001 (translation invariance of ω)

## Statement (Silverman III.4.7 / definition)
For `Q ∈ E`, the **translation by Q** is the map `τ_Q : E → E`, `P ↦ P + Q`.
This is a morphism of varieties (not just a set map), in fact an isomorphism.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- Translation by a point Q on an elliptic curve.
    Reference: Silverman III.4.7. -/
def WeierstrassCurve.translation (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)]
    (Q : E.toAffine.Point) : E.toAffine →ᵃˡᵍ E.toAffine

@[simp]
lemma WeierstrassCurve.translation_apply (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)]
    (Q P : E.toAffine.Point) :
    E.translation Q P = P + Q

/-- Translation is an isomorphism (with inverse τ_{-Q}). -/
def WeierstrassCurve.translationEquiv (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)]
    (Q : E.toAffine.Point) : E.toAffine ≃ᵃˡᵍ E.toAffine

end HasseWeil.EC
```

## Notes
- The fact that translation is a morphism (not just a function) needs the
  rational-map-extends-to-morphism theorem (T-II-2-001) and that `+` is given by
  rational formulas.

## Progress log
