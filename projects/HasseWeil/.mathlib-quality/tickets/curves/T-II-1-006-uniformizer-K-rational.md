# T-II-1-006: K(C) contains uniformizers for K-rational P

**Status**: DONE (verified axiom-clean 2026-04-22: `exists_K_uniformizer` depends only on `[propext, Classical.choice, Quot.sound]`)
**Silverman**: II.1.1.1 (Remark / Exercise 2.16)
**Module**: `HasseWeil/Curves/Valuation.lean`
**Owner**: worker-A
**Checked out at**: 2026-04-17T11:15Z
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-1-001 (DVR)
- T-II-1-003 (uniformizer in K̄(C))

## Blocks
- T-II-1-005 (which assumes a K-rational uniformizer exists)

## Statement (Silverman II.1.1.1 + Exercise 2.16)
If `P ∈ C(K)` (i.e., a K-rational smooth point), then `K(C)` (not just `K̄(C)`)
contains uniformizers for P.

That is, the uniformizer can be chosen with coefficients in the base field K,
not just the algebraic closure.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- For a K-rational smooth point P, there is a uniformizer for P in K(C)
    (the function field over K, not K̄). Reference: Silverman II.1.1.1. -/
theorem exists_K_uniformizer (C : SmoothPlaneCurve F) (P : C.RationalPoint) :
    ∃ t : C.FunctionField, Uniformizer C P.toSmooth t

end HasseWeil.Curves
```

## Notes
- This is essentially Galois descent: if P is K-rational, then the maximal
  ideal at P is Galois-invariant, so it has a generator that's also Galois-
  invariant.
- For Weierstrass curves, an explicit uniformizer at a finite point `(x₀, y₀)`
  is `x - x₀` (or `y - y₀` if `polynomialY` doesn't vanish).

## Progress log

- 2026-04-17T11:15Z [worker-A] checkout. Given that our
  `SmoothPlaneCurve F` carries a single field `F`, `SmoothPoint C` has
  `F`-rational coordinates by construction. The Silverman "K-rational"
  vs. "K̄-rational" distinction collapses here, so the statement is a
  direct corollary of `exists_uniformizer`.
- 2026-04-17T11:20Z [worker-A] Complete.
  - **Deviation from ticket Module field**: landed in
    `Curves/Valuation.lean` next to `exists_uniformizer`.
  - Added `SmoothPlaneCurve.RationalPoint := SmoothPoint` as an alias
    (since every smooth point in this setup is already `F`-rational).
  - Added `SmoothPlaneCurve.exists_K_uniformizer (P : C.RationalPoint) :
    ∃ t, Uniformizer C P t`, proved by delegation to
    `exists_uniformizer`.
  - `lake build HasseWeil.Curves.Valuation` passes, 0 sorries, axiom
    profile is `propext, Classical.choice, Quot.sound`.
  - Future work: when the project grows a true `K ⊂ K̄` distinction,
    `RationalPoint` will need to be refined to pick out genuinely
    `K`-coordinate points rather than being a trivial alias, and
    `exists_K_uniformizer` will require an honest Galois-descent
    proof. The statement signature carries over unchanged.
  - Status → REVIEW.
