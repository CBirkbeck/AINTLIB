# T-IV-1-004: A_n is homogeneous of weight n in the a_i

**Status**: OPEN
**Silverman**: IV.1.1(c)
**Module**: `HasseWeil/FormalGroup/Curve.lean`
**Owner**: (unassigned)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-1-003 (w uniqueness)

## Blocks
- T-IV-1-007 (formal differential)

## Statement (Silverman IV.1.1(c))
Write `w(z) = z³ Σ_{n ≥ 0} A_n z^n` where `A_n ∈ ℤ[a₁..a₆]`. Then `A_n` is a
weighted-homogeneous polynomial in the `a_i` of total weight `n`, where `a_i`
has weight `i`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem WeierstrassCurve.wSeries_coeff_homogeneous (n : ℕ) :
    UniversalWeierstrass.wSeriesCoeff (n + 3) ∈
      MvPolynomial.homogeneousSubmodule {1,2,3,4,6} ℤ n

end HasseWeil.FormalGroup
```

## Notes
- Use the universal Weierstrass curve over `ℤ[a₁,a₂,a₃,a₄,a₆]` with the weight
  grading. The defining equation is weighted-homogeneous, so the iterative
  Hensel construction preserves homogeneity.

## Progress log
