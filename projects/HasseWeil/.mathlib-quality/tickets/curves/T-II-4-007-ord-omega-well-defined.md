# T-II-4-007: ord_P(ω) is independent of choice of uniformizer

**Status**: OPEN
**Silverman**: II.4.3(c)
**Module**: `HasseWeil/Curves/Differentials.lean`
**Owner**: (unassigned)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: A

## Depends on
- T-II-4-005 (ω = g·dt)
- T-II-4-006 (df/dt regular)

## Blocks
- T-II-4-008 (formula for ord(f·dx))
- T-II-4-009 (almost all ord = 0)
- T-II-4-010 (div(ω))

## Statement (Silverman II.4.3(c))
For `ω ∈ Ω_C` and `P ∈ C`, the integer
`ord_P(ω) := ord_P(g)` where `ω = g · dt` for any uniformizer `t` at `P`,
is independent of the choice of uniformizer `t`.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- Order of a differential at a point P, defined via any uniformizer.
    Reference: Silverman II.4.3(c). -/
noncomputable def Differentials.ord (C : SmoothPlaneCurve F) (P : C)
    (ω : Differentials C) : ℤ ⊕ {⊤}

/-- The order is independent of the chosen uniformizer.
    Reference: Silverman II.4.3(c). -/
theorem Differentials.ord_independent_of_uniformizer (C : SmoothPlaneCurve F) (P : C)
    (t₁ t₂ : C.FunctionField)
    (ht₁ : C.IsUniformizerAt P t₁) (ht₂ : C.IsUniformizerAt P t₂)
    (ω : Differentials C) :
    C.ord P (Differentials.coeff C P t₁ ht₁ ω) =
    C.ord P (Differentials.coeff C P t₂ ht₂ ω)

end HasseWeil.Curves
```

## Notes
- Two uniformizers `t₁, t₂` at `P` are related by `t₁ = u · t₂` for some unit `u`
  in the local ring. Then `dt₁ = (du · t₂ + u · dt₂) = (t₂ · du/dt₂ + u) dt₂`.
  The factor in parentheses is a unit at `P`, so taking ord gives the same answer.

## Progress log
