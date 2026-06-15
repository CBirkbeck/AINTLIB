# T-II-3-010: Exact sequence 1 → K̄* → K̄(C)* → Div⁰(C) → Pic⁰(C) → 0

**Status**: OPEN
**Silverman**: II.3.4 (Remark)
**Module**: `HasseWeil/Curves/Divisors.lean`
**Owner**: (unassigned)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: A

## Depends on
- T-II-3-008 (div(f) = 0 iff const)
- T-II-3-009 (deg(div(f)) = 0)
- T-II-3-007 (Pic⁰)

## Blocks
- T-III-3-007 (exact sequence for E)

## Statement (Silverman II.3.4)
For a smooth curve `C/K`, there is an exact sequence of abelian groups:

```
1 → K̄* → K̄(C)* → Div⁰(C) → Pic⁰(C) → 0.
```

The middle map is `f ↦ div(f)`; the rightmost is the natural quotient.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- The fundamental exact sequence of divisors on a curve.
    Reference: Silverman II.3.4. -/
theorem divisor_exact_sequence (C : SmoothPlaneCurve F) :
    Function.Exact (Algebra.toRingHom F C.FunctionField : F → C.FunctionField)
                   (... divisorHom : C.FunctionField → Divisor C) ∧
    Function.Exact (... divisorHom)
                   (... Divisor → Pic⁰ C)

-- Or as four separate statements:
-- (a) injective on the left
-- (b) image of inclusion = kernel of div
-- (c) image of div = ker of quotient (i.e., principal ⊂ Div⁰)
-- (d) quotient is surjective

end HasseWeil.Curves
```

## Notes
- This is just the assembly of T-II-3-008 and T-II-3-009 plus the trivial parts.

## Progress log
