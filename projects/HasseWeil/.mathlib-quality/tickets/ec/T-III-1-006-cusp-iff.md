# T-III-1-006: Cusp ⇔ Δ = 0 ∧ c₄ = 0

**Status**: DONE
**Silverman**: III.1.4(c)
**Module**: `HasseWeil/EC/Weierstrass.lean`
**Owner**: (unassigned)
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: B

## Depends on
- T-III-1-001 (Weierstrass equation)
- T-III-1-005 (node iff)

## Blocks
- T-III-2-008 (E_ns ≅ G_a for cuspidal — optional)

## Statement (Silverman III.1.4(c))
A singular Weierstrass curve `E` has a **cusp** (i.e. one tangent direction with
multiplicity 2) iff `Δ = 0` and `c₄ = 0`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- A singular Weierstrass curve has a cusp iff Δ = 0 ∧ c₄ = 0.
    Reference: Silverman III.1.4(c). -/
theorem WeierstrassCurve.hasCusp_iff (E : WeierstrassCurve F) :
    E.Δ = 0 ∧ E.c₄ = 0 ↔ E.HasCusp

end HasseWeil.EC
```

## Notes
- Complement to T-III-1-005.

## Progress log
- 2026-04-10 [worker-B] Implemented in `HasseWeil/SingularPoint.lean` alongside T-III-1-005.
  `hasCusp_iff : W.HasCusp ↔ W.Δ = 0 ∧ W.c₄ = 0` over AlgClosed fields with char ≠ 2.
  Zero sorries, clean build. Status: DONE.
