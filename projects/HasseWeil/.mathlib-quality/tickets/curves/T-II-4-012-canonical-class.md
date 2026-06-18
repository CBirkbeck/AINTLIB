# T-II-4-012: Canonical divisor class

**Status**: OPEN
**Silverman**: II.4 (definition)
**Module**: `HasseWeil/Curves/Differentials.lean`
**Owner**: (unassigned)
**Estimated lines**: 40
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-4-010 (div(ω))
- T-II-3-007 (Pic C)

## Blocks
- (none in the Hasse-Weil critical path; included for mathlib quality)

## Statement (Silverman II.4)
For any two nonzero `ω₁, ω₂ ∈ Ω_C`, the divisors `div(ω₁)` and `div(ω₂)` are
linearly equivalent. The corresponding class in `Pic(C)` is the **canonical
divisor class** `K_C`.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- Any two divisors of differentials are linearly equivalent.
    Reference: Silverman II.4. -/
theorem Differentials.divisorOf_linearlyEquiv (C : SmoothPlaneCurve F)
    (ω₁ ω₂ : Differentials C) (hω₁ : ω₁ ≠ 0) (hω₂ : ω₂ ≠ 0) :
    (Differentials.divisorOf C ω₁ hω₁) ~_div (Differentials.divisorOf C ω₂ hω₂)

/-- The canonical divisor class K_C ∈ Pic(C). -/
noncomputable def Differentials.canonicalClass (C : SmoothPlaneCurve F)
    [Nonempty (Σ ω : Differentials C, ω ≠ 0)] : Pic C

end HasseWeil.Curves
```

## Notes
- Two differentials differ by a function: `ω₁ = f · ω₂` for some `f ∈ K(C)*`,
  so `div(ω₁) = div(f) + div(ω₂)`, hence linearly equivalent.
- The class is well-defined in `Pic(C)` (NOT in `Pic⁰`, since differentials don't
  in general have degree 0; for elliptic curves they do, see III.1.5).

## Progress log
