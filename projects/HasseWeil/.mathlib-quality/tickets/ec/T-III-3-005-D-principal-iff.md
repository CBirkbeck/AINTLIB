# T-III-3-005: D principal ⇔ deg D = 0 ∧ Σ[n_P]P = O

**Status**: OPEN
**Silverman**: III.3.5
**Module**: `HasseWeil/EC/PicE.lean`
**Owner**: (unassigned)
**Estimated lines**: 50
**Difficulty**: easy (uses Pic⁰ ≅ E)
**Stream**: C

## Depends on
- T-III-3-004 (Pic⁰ ≅ E)

## Blocks
- T-III-4-016 (factorization of isogenies)

## Statement (Silverman III.3.5)
For a divisor `D = Σ n_P (P) ∈ Div(E)`,
`D is principal ⇔ deg D = 0 ∧ Σ_P [n_P] P = O in E(K̄)`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- A divisor on E is principal iff it has degree 0 and its formal sum equals O.
    Reference: Silverman III.3.5. -/
theorem WeierstrassCurve.divisor_isPrincipal_iff (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)]
    (D : Divisor E.toSmoothPlaneCurve) :
    D.IsPrincipal ↔ D.degree = 0 ∧
      (∑ P in D.support, (D P) • P) = (0 : E.toAffine.Point)

end HasseWeil.EC
```

## Notes
- Direct corollary of T-III-3-004: in `Pic⁰(E)`, the class of `D` is the sum
  `Σ n_P · κ(P) = Σ n_P · P` (after subtracting Σ n_P · (O), which is 0 since
  deg = 0). So `D` is principal iff this sum is 0 in `E`.

## Progress log
