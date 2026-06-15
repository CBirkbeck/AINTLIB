# T-II-4-011: Holomorphic and nonvanishing predicates

**Status**: OPEN
**Silverman**: II.4 (definition)
**Module**: `HasseWeil/Curves/Differentials.lean`
**Owner**: (unassigned)
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-4-010 (div(ω))

## Blocks
- T-II-4-012 (canonical divisor class)

## Statement (Silverman II.4)
A differential `ω ∈ Ω_C` is **holomorphic** (or **regular**) at `P` if `ord_P(ω) ≥ 0`,
and **nonvanishing** at `P` if `ord_P(ω) ≤ 0`. It is **holomorphic on C** if
holomorphic at every point, and **nonvanishing on C** similarly.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- A differential is holomorphic at P if ord_P(ω) ≥ 0. -/
def Differentials.IsHolomorphicAt (ω : Differentials C) (P : C) : Prop :=
  0 ≤ Differentials.ord C P ω

/-- A differential is nonvanishing at P if ord_P(ω) ≤ 0. -/
def Differentials.IsNonvanishingAt (ω : Differentials C) (P : C) : Prop :=
  Differentials.ord C P ω ≤ 0

/-- A differential is holomorphic on C if holomorphic at every point. -/
def Differentials.IsHolomorphic (ω : Differentials C) : Prop :=
  ∀ P : C, ω.IsHolomorphicAt P

/-- A differential is nonvanishing on C if nonvanishing at every point. -/
def Differentials.IsNonvanishing (ω : Differentials C) : Prop :=
  ∀ P : C, ω.IsNonvanishingAt P

lemma Differentials.divisorOf_nonneg_iff_holomorphic (ω : Differentials C) (hω : ω ≠ 0) :
    (∀ P, 0 ≤ (Differentials.divisorOf C ω hω) P) ↔ ω.IsHolomorphic

end HasseWeil.Curves
```

## Notes
- Pure wrappers; useful for stating III.1.5 (`ω = dx/(2y+a₁x+a₃)` is both
  holomorphic and nonvanishing on E).

## Progress log
