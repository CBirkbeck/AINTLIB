# T-II-3-007: Pic and Pic⁰

**Status**: DONE (worker-I, 2026-04-20; verified axiom-clean 2026-04-22: `Pic`, `Pic₀` depend only on `[propext, Classical.choice, Quot.sound]`)
**Silverman**: II.3 (definition)
**Module**: `HasseWeil/Curves/Divisors.lean`
**Owner**: worker-I
**Estimated lines**: 30 (delivered ~10 as abbrevs)
**Difficulty**: easy
**Stream**: A

## Progress log

- **2026-04-20** (worker-I): delivered `Pic C := Divisor C ⧸ principalSubgroup`
  and `Pic₀ C := degZero C ⧸ (principalSubgroup.addSubgroupOf (degZero C))` as
  `abbrev`s. The `AddCommGroup` structure is inherited automatically from the
  quotient construction. Axiom-clean (no new axioms).


## Depends on
- T-II-3-003 (Div⁰), T-II-3-006 (principal)

## Blocks
- T-III-3-004 (Pic⁰(E) ≅ E)

## Statement
The **Picard group** (or divisor class group) of `C` is

```
Pic(C) := Div(C) / { principal divisors }.
```

The **degree-zero Picard group** is

```
Pic⁰(C) := Div⁰(C) / { principal divisors }.
```

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- The Picard group of C. -/
def Pic (C : SmoothPlaneCurve F) : Type _ :=
  Divisor C ⧸ Divisor.principalSubgroup C

instance : AddCommGroup (Pic C) := inferInstance

/-- The degree-zero Picard group of C. -/
def Pic₀ (C : SmoothPlaneCurve F) : Type _ :=
  Divisor.degZero C ⧸ (Divisor.principalSubgroup C ⊓ Divisor.degZero C)

instance : AddCommGroup (Pic₀ C) := inferInstance

end HasseWeil.Curves
```

## Notes
- Mathlib has `ClassGroup` for commutative rings; this is the generalization to
  curves. They should match up via the coordinate ring.
- For elliptic curves we already have `Point.toClass : E.Point →+ Additive
  (ClassGroup E.CoordinateRing)` in mathlib.

## Progress log
