# T-II-4-010: div(ω) for a differential

**Status**: OPEN
**Silverman**: II.4 (definition)
**Module**: `HasseWeil/Curves/Differentials.lean`
**Owner**: (unassigned)
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-4-009 (ord_P = 0 almost everywhere)
- T-II-3-001 (Divisor C)

## Blocks
- T-II-4-011 (holomorphic / nonvanishing)
- T-II-4-012 (canonical class)
- T-III-1-009 (div(ω) = 0 for invariant differential)

## Statement (Silverman II.4 def)
For a nonzero `ω ∈ Ω_C`, the **divisor of ω** is
`div(ω) := Σ_{P ∈ C} ord_P(ω) · (P) ∈ Div(C)`.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- The divisor of a nonzero differential.
    Reference: Silverman II.4. -/
noncomputable def Differentials.divisorOf (C : SmoothPlaneCurve F)
    (ω : Differentials C) (hω : ω ≠ 0) : Divisor C

@[simp]
lemma Differentials.divisorOf_coeff (C : SmoothPlaneCurve F)
    (ω : Differentials C) (hω : ω ≠ 0) (P : C) :
    (Differentials.divisorOf C ω hω) P = (Differentials.ord C P ω).toInt

end HasseWeil.Curves
```

## Notes
- Wrapper for the function `P ↦ ord_P ω`, which has finite support by T-II-4-009.

## Progress log
