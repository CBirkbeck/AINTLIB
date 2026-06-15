# T-II-2-013: K(C^q) = K(C)^q (Frobenius pullback)

**Status**: DONE (EC case in FrobeniusIsogeny.lean)
**Silverman**: II.2.11(a)
**Module**: `HasseWeil/FrobeniusIsogeny.lean` → `HasseWeil/Curves/Maps.lean`
**Owner**: worker-C
**Checked out at**: 2026-04-08
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: A

## Depends on
- T-II-2-012 (Frobenius construction)

## Blocks
- T-II-2-014 (Frobenius purely inseparable)
- T-II-2-015 (deg Frobenius = q)

## Statement (Silverman II.2.11(a))
Let `K` be perfect of characteristic `p > 0`, `q = p^r`, `C/K` a smooth curve,
and `φ : C → C^(q)` the q-power Frobenius. Then

```
φ*(K(C^(q))) = K(C)^q := { f^q : f ∈ K(C) }.
```

## Acceptance criteria

```lean
namespace HasseWeil.Curves

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

/-- The pullback of the Frobenius morphism is the q-th power subfield.
    Reference: Silverman II.2.11(a). -/
theorem Morphism.frobenius_pullback_range (C : SmoothPlaneCurve K) :
    (Morphism.frobenius C).pullback.range =
      Subalgebra.map (frobeniusAlgHom K (Fintype.card K)) ⊤  -- adjusts to {f^q : f ∈ K(C)}

end HasseWeil.Curves
```

## Notes
- This is the curve-level version of "Frobenius pulls back to taking q-th powers".
- For a perfect base field, every element of K is a q-th power, so the
  identification is clean.
- mathlib has `Field.frobenius` and `Polynomial.expand` which capture similar
  structure.

## Progress log
- 2026-04-08 [worker-C] REVIEW. Added `frobeniusIsogeny_pullback_range` to
  `HasseWeil/FrobeniusIsogeny.lean`:
  ```
  Set.range (frobeniusIsogeny K W).pullback =
    Set.range ((· ^ Fintype.card K) : K(E) → K(E))
  ```
  The image of the Frobenius pullback is exactly the set of `q`-th powers in
  `K(E)`. The proof is a one-liner via `frobeniusIsogeny_pullback_apply`.
  Status: REVIEW. The general "curves" formulation is a follow-up under
  T-MIGRATE-007 / general curves refactor.
- 2026-04-10 [worker-A] Verified: `#print axioms frobeniusIsogeny_pullback_range`
  shows only standard axioms. No sorryAx. Status: DONE.
