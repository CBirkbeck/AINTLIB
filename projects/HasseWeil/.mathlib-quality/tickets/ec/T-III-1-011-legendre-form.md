# T-III-1-011: Legendre form (char ≠ 2, optional)

**Status**: DONE
**Silverman**: III.1.7
**Module**: `HasseWeil/EC/Weierstrass.lean`
**Owner**: (unassigned)
**Estimated lines**: 80
**Difficulty**: medium
**Stream**: B

## Depends on
- T-III-1-003 (change of variables)

## Blocks
- (none — purely informational)

## Statement (Silverman III.1.7)
Assume `char K ≠ 2`. Every elliptic curve over `K̄` is `K̄`-isomorphic to a curve
in **Legendre form**: `y² = x(x − 1)(x − λ)` for some `λ ∈ K̄ ∖ {0,1}`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- Every elliptic curve in characteristic ≠ 2 is K̄-isomorphic to a curve in
    Legendre form. Reference: Silverman III.1.7. -/
theorem WeierstrassCurve.exists_legendre_form
    [Fact (ringChar F ≠ 2)] (E : EllipticCurve F) :
    ∃ λ : F, λ ≠ 0 ∧ λ ≠ 1 ∧
      Nonempty (E.toAffine ≃ (legendreCurve λ).toAffine)

end HasseWeil.EC
```

## Notes
- Optional. Useful for explicit examples and exam-style computations.

## Progress log
- 2026-04-10 [worker-B] Implemented in `HasseWeil/LegendreForm.lean` (239 lines, 0 sorry).
  Defined `legendreCurve l` (y²=x(x-1)(x-l)), proved `legendreCurve_Δ_ne_zero_iff`,
  and `exists_legendreCurve_iso`: every EC over AlgClosed with char≠2 is isomorphic to
  a Legendre curve via VariableChange. Status: DONE.
