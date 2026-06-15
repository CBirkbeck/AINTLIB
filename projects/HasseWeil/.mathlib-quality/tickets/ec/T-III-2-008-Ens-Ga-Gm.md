# T-III-2-008: E_ns ≅ G_m or G_a (singular)

**Status**: OPEN
**Silverman**: III.2.5
**Module**: `HasseWeil/EC/GroupLaw.lean`
**Owner**: (unassigned)
**Estimated lines**: 80
**Difficulty**: medium
**Stream**: B

## Depends on
- T-III-2-007 (E_ns)
- T-III-1-005 (node iff)
- T-III-1-006 (cusp iff)

## Blocks
- (none in critical path)

## Statement (Silverman III.2.5)
Let `E` be a singular Weierstrass curve.
- If `E` has a node with rational tangent slopes, then `E_ns ≅ G_m = K̄*`.
- If `E` has a node with irrational slopes, then `E_ns` is a twist of `G_m`.
- If `E` has a cusp, then `E_ns ≅ G_a = (K̄, +)`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

theorem WeierstrassCurve.nonsingularLocus_iso_Gm_of_node
    (E : WeierstrassCurve F) (hΔ : E.Δ = 0) (hc : E.c₄ ≠ 0) :
    Nonempty (E.nonsingularLocus ≃+ Multiplicative F)

theorem WeierstrassCurve.nonsingularLocus_iso_Ga_of_cusp
    (E : WeierstrassCurve F) (hΔ : E.Δ = 0) (hc : E.c₄ = 0) :
    Nonempty (E.nonsingularLocus ≃+ Additive F)

end HasseWeil.EC
```

## Notes
- Optional for Hasse-Weil. Standard explicit parametrization.

## Progress log
