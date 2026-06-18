# T-II-4-005: ω = g·dt for unique g, given uniformizer t at P

**Status**: OPEN
**Silverman**: II.4.3(a)
**Module**: `HasseWeil/Curves/Differentials.lean`
**Owner**: (unassigned)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: A

## Depends on
- T-II-4-002 (Ω_C is 1-dimensional)
- T-II-4-003 (dx is a basis)
- T-II-1-003 (uniformizer)

## Blocks
- T-II-4-006 (df/dt regular at P)
- T-II-4-007 (ord_P(ω) well-defined)

## Statement (Silverman II.4.3(a))
Let `P ∈ C` and let `t` be a uniformizer at `P`. Then for every `ω ∈ Ω_C`, there
exists a unique `g ∈ K(C)` such that `ω = g · dt`.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- For a uniformizer t at P, every differential is uniquely g·dt.
    Reference: Silverman II.4.3(a). -/
theorem Differentials.exists_unique_coeff (C : SmoothPlaneCurve F) (P : C)
    (t : C.FunctionField) (ht : C.IsUniformizerAt P t)
    (ω : Differentials C) :
    ∃! g : C.FunctionField, ω = g • Differentials.d t

/-- Coefficient extraction: ω.coeff t is the function g such that ω = g·dt. -/
noncomputable def Differentials.coeff (C : SmoothPlaneCurve F) (P : C)
    (t : C.FunctionField) (ht : C.IsUniformizerAt P t)
    (ω : Differentials C) : C.FunctionField :=
  Classical.choose (Differentials.exists_unique_coeff C P t ht ω)

end HasseWeil.Curves
```

## Notes
- This follows directly from T-II-4-003 once we know `t` is a uniformizer (so
  `K(C)/K(t)` is finite separable, since K(C)/K is finitely generated of trans
  deg 1 and t is non-constant).
- Uniqueness is from `dt ≠ 0`.

## Progress log
