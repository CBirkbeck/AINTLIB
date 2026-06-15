# T-II-2-015: deg(Frobenius) = q

**Status**: DONE (EC case in FrobeniusIsogeny.lean)
**Silverman**: II.2.11(c)
**Module**: `HasseWeil/FrobeniusIsogeny.lean` → `HasseWeil/Curves/Maps.lean`
**Owner**: worker-C
**Checked out at**: 2026-04-08
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: A

## Depends on
- T-II-2-013 (Frobenius pullback)
- T-II-1-005 (K(C) finite separable over K(t))

## Blocks
- T-II-2-016 (factorization)
- T-III-4-008 (Frobenius isogeny degree — already partial)

## Statement (Silverman II.2.11(c))
For a perfect K of characteristic p > 0 and q = p^r, the Frobenius morphism
`φ : C → C^(q)` has degree `q`.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

/-- The degree of the Frobenius morphism is q = #K.
    Reference: Silverman II.2.11(c). -/
theorem Morphism.frobenius_degree (C : SmoothPlaneCurve K) :
    (Morphism.frobenius C).degree = Fintype.card K

end HasseWeil.Curves
```

## Notes
- Silverman's proof: take K-rational point P and uniformizer t at P. Then
  K(C) = K(C)^q(t), and the minimal polynomial of t over K(C)^q is `T^q - t^q`
  (which has degree q).
- The existing `FrobeniusIsogeny.lean:frobenius_finrank_functionField` SORRY is
  this same theorem, restricted to elliptic curves. Worker handoff says the
  proof outline is in the docstring.

## Progress log
- 2026-04-08 [worker-C] Verified that the EC-specific case is FULLY PROVED in
  `HasseWeil/FrobeniusIsogeny.lean`:
  - `frobenius_finrank_functionField` (line 468): proves `[K(E) : K(E)^q] = q`
    via tower law on `K(E)/K(x)/K(x^q)` and `K(E)/K(E)^q/K(x^q)`.
  - `frobeniusIsogeny_degree` (line 482): direct corollary giving
    `(frobeniusIsogeny K W).degree = Fintype.card K`.
  - The handoff file `HANDOFF.md` listed this as a 1-sorry, but that sorry has
    been closed in subsequent work — `FrobeniusIsogeny.lean` is now sorry-free
    (only one occurrence of "sorry" remains, in a comment at line 81).
  - Build clean.
  - Status: REVIEW. The general "curves" case (perfect K, not necessarily
    finite, for arbitrary smooth plane curves) is a follow-up tracked under
    T-MIGRATE-007 / general curves refactor.
- 2026-04-10 [worker-A] Verified: `#print axioms frobeniusIsogeny_degree` and
  `frobenius_finrank_functionField` show only standard axioms. No sorryAx.
  Status: DONE.
