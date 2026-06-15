# T-III-3-004: Pic⁰(E) ≅ E

**Status**: OPEN
**Silverman**: III.3.4
**Module**: `HasseWeil/EC/PicE.lean`
**Owner**: (unassigned)
**Estimated lines**: 100
**Difficulty**: hard (CRITICAL)
**Stream**: C

## Depends on
- T-III-3-003 (P ~ Q ⇒ P = Q)
- T-II-3-007 (Pic⁰)

## Blocks
- T-III-3-005 (D principal iff)
- T-III-3-007 (exact sequence for E)
- T-III-4-010 (every isogeny is hom)
- T-III-6-002 (dual via Pic⁰)

## Statement (Silverman III.3.4)
The map `κ : E(K̄) → Pic⁰(E)`, `P ↦ class of (P) - (O)`, is an isomorphism of
abelian groups.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The fundamental isomorphism Pic⁰(E) ≅ E.
    Reference: Silverman III.3.4. -/
def WeierstrassCurve.picZeroEquiv (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] :
    HasseWeil.Curves.Pic₀ (E.toSmoothPlaneCurve) ≃+ E.toAffine.Point

theorem WeierstrassCurve.picZeroEquiv_apply (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)]
    (P : E.toAffine.Point) :
    E.picZeroEquiv (Quotient.mk _ (Divisor.single P 1 - Divisor.single 0 1)) = P

end HasseWeil.EC
```

## Notes
- This is the key bridge between divisors and the group law on E.
- Mathlib has `WeierstrassCurve.Affine.Point.toClass : E.Point →+ Additive
  (ClassGroup E.CoordinateRing)`. We need to upgrade this to a full isomorphism
  with our `Pic₀`.
- Silverman proves this with RR (Riemann-Roch gives that every degree-0 divisor
  is equivalent to `(P) - (O)`). We avoid RR by:
  - Injectivity from T-III-3-003.
  - Surjectivity from a direct geometric argument: any `D ∈ Div⁰` can be
    rewritten using the explicit `(P) + (Q) ~ (P+Q) + (O)` formula, which comes
    from the line construction in III.2.

## Progress log
