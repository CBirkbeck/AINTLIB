# T-III-1-005: Node ⇔ Δ = 0 ∧ c₄ ≠ 0

**Status**: DONE
**Silverman**: III.1.4(b)
**Module**: `HasseWeil/EC/Weierstrass.lean`
**Owner**: (unassigned)
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: B

## Depends on
- T-III-1-001 (Weierstrass equation)

## Blocks
- T-III-2-008 (E_ns ≅ G_m for nodal — optional)

## Statement (Silverman III.1.4(b))
A singular Weierstrass curve `E` has a **node** (i.e. the singularity has two
distinct tangent directions) iff `Δ = 0` and `c₄ ≠ 0`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- A singular Weierstrass curve has a node iff Δ = 0 ∧ c₄ ≠ 0.
    Reference: Silverman III.1.4(b). -/
theorem WeierstrassCurve.hasNode_iff (E : WeierstrassCurve F) :
    E.Δ = 0 ∧ E.c₄ ≠ 0 ↔ E.HasNode

end HasseWeil.EC
```

where `HasNode` is defined as: there exists a singular point with two distinct
tangent directions in `K̄²`.

## Notes
- Standard plane-curve calculation. Reduce to short Weierstrass form when
  possible.
- Used only in characterizing E_ns ≅ G_m for the nodal singular fibre.

## Progress log
- 2026-04-10 [worker-B] Implemented in `HasseWeil/SingularPoint.lean`. Proved
  `hasNode_iff : W.HasNode ↔ W.Δ = 0 ∧ W.c₄ ≠ 0` over AlgClosed fields with char ≠ 2.
  Key results: `Singular` predicate, `tangentConeDisc`, `c₄_eq_tangentConeDisc_sq_of_singular`,
  `exists_singular_of_Δ_eq_zero` (using twoTorsionPolynomial discriminant = 16Δ).
  Zero sorries, clean build. Status: DONE.
