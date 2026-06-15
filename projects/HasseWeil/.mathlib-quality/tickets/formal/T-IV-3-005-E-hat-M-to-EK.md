# T-IV-3-005: Ê(M) → E(K) injection

**Status**: OPEN
**Silverman**: IV.3.1.3
**Module**: `HasseWeil/FormalGroup/Associated.lean`
**Owner**: (unassigned)
**Estimated lines**: 80
**Difficulty**: hard
**Stream**: D

## Depends on
- T-IV-2-005 (Ê)
- T-IV-3-001 (F(M))
- T-IV-1-006 (x(z), y(z))

## Blocks
- T-IV-BRIDGE-001..005

## Statement (Silverman IV.3.1.3)
Let `K` be a complete discretely valued field with valuation ring `O_K` and
maximal ideal `M`. For `z ∈ M`, the formal series `x(z), y(z)` evaluate to give
a point `(x(z), y(z)) ∈ E(K)`. This defines an injection `Ê(M) → E(K)` whose
image is the **kernel of reduction** `E₁(K) := { P ∈ E(K) : P̄ = O in Ē(F_v) }`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- The injection from the formal group to the curve points.
    Reference: Silverman IV.3.1.3. -/
def WeierstrassCurve.formalGroupToPoint
    (E : WeierstrassCurve K) [IsDiscreteValuationRing O_K]
    [IsAdicComplete (IsLocalRing.maximalIdeal O_K) O_K] :
    E.formalGroup.evalGroup →+ E.toAffine.Point

end HasseWeil.FormalGroup
```

## Notes
- This is the bridge between formal group theory and elliptic curves over local
  fields. Used in IV.6 (DVR-specific results) and the proof of [m]*ω = mω.

## Progress log
