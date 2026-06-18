# T-III-3-007: Exact sequence 1 → K* → K(E)* → Div⁰_K(E) → E(K) → 0

**Status**: OPEN
**Silverman**: III.3.5.1
**Module**: `HasseWeil/EC/PicE.lean`
**Owner**: (unassigned)
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: C

## Depends on
- T-II-3-010 (exact sequence for general C)
- T-III-3-004 (Pic⁰(E) ≅ E)

## Blocks
- T-V-1-004 (#E(F_q) = q + 1 - tr(π))

## Statement (Silverman III.3.5.1 / Cor III.3.5.1)
For an elliptic curve `E/K`, there is an exact sequence of abelian groups:
`1 → K̄* → K̄(E)* → Div⁰(E) → E(K̄) → 0`,
where the last map is `D ↦ Σ [n_P] P`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The exact sequence relating K(E)*, divisors, and E(K).
    Reference: Silverman III.3.5.1. -/
theorem WeierstrassCurve.divisor_to_point_exact (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] :
    Function.Exact (...) (...)  -- four pieces of exactness

end HasseWeil.EC
```

## Notes
- This is just T-II-3-010 for `C = E`, combined with T-III-3-004 to identify
  `Pic⁰(E) = E(K̄)`.

## Progress log
