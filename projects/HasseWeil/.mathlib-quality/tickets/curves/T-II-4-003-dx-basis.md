# T-II-4-003: dx is a basis when K(C)/K(x) is finite separable

**Status**: OPEN
**Silverman**: II.4.2(b)
**Module**: `HasseWeil/Curves/Differentials.lean`
**Owner**: (unassigned)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: A

## Depends on
- T-II-4-002 (Ω_C is 1-dimensional)

## Blocks
- T-II-4-005 (write ω = g·dt)
- T-II-4-008 (order of f·dx)

## Statement (Silverman II.4.2(b))
Let `x ∈ K(C)`. Then `dx` is a `K(C)`-basis of `Ω_C` if and only if the field
extension `K(C)/K(x)` is finite and separable.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- dx is a K(C)-basis of Ω_C iff K(C)/K(x) is finite separable.
    Reference: Silverman II.4.2(b). -/
theorem Differentials.dx_isBasis_iff (C : SmoothPlaneCurve F) (x : C.FunctionField) :
    (∀ ω : Differentials C, ∃ g : C.FunctionField, ω = g • Differentials.d x) ∧
    (Differentials.d x ≠ 0) ↔
    (FiniteDimensional (algebraMap F C.FunctionField).range C.FunctionField ∧
     IsSeparable F C.FunctionField)

end HasseWeil.Curves
```

## Notes
- The "if" direction: when K(C)/K(x) is finite separable, the standard derivation
  d/dx extends, hence dx ≠ 0 and generates the 1-dimensional space.
- The "only if" direction: if K(C)/K(x) is inseparable then x is a p-th power and
  dx = 0 in characteristic p.

## Progress log
