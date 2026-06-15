# T-II-1-004: Functions with no zeros or poles are constant

**Status**: REVIEW (worker-I, 2026-04-21) — Part 1 delivered fully; Part 2
delivered in **CoordinateRing case** + **prime-indexed full form** via IC-006:
`const_of_no_poles_of_valuation_of_ordAtInfty` and
`const_of_isIntegral_polynomialX_of_ordAtInfty` in `Infinity.lean`. The
SmoothPoint-indexed full form follows once the SmoothPoint → HeightOneSpectrum
surjection lands (T-II-3-009 work).
**Silverman**: II.1.2 (Proposition)
**Module**: `HasseWeil/Curves/Infinity.lean`
**Owner**: worker-I
**Estimated lines**: 100 (delivered ~15, leveraging ~200 lines of Part 1 + Liouville infra)
**Difficulty**: hard
**Stream**: A

## Depends on
- T-II-1-001 (DVR) — done
- T-II-1-002 (ord_P) — done

## Blocks
- T-II-3-008 (`div(f) = 0 ⇔ f ∈ K̄*`)
- T-III-5-001 (translation invariance proof needs this)

## Statement (Silverman II.1.2)
Let `C` be a smooth curve and let `f ∈ K̄(C)` with `f ≠ 0`. Then
1. There are only finitely many points of C at which f has a pole or zero.
2. Further, if f has no poles, then f ∈ K̄ (i.e., is constant).

The second part is the function-field analogue of Liouville's theorem.

## Why BLOCKED

Both halves of this ticket need machinery that the project does not currently
carry.

### Part 1 — Finite zeros/poles

For a nonzero `f ∈ K(C)`, the set `{P : C.SmoothPoint | ord_P f ≠ 0}` is finite.

**What we have.** For the Weierstrass case, every `f` admits the presentation
`f = (p₀(x) + q₀(x) y) / (p₁(x) + q₁(x) y)` via the rank-2 basis `{1, Y}` of
`F[W]` over `F[X]`, and mathlib provides `Algebra.norm F[X] F[W] f ∈ F[X]`
(via `WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis`). The
zeros and poles of `f` correspond to zeros of the numerator/denominator of
`Algebra.norm`, which is a polynomial with finitely many roots.

**What is missing.**

- A lemma connecting `ord_P` (the valuation at a point `P`) to the algebraic
  norm down to `F[X]`. Specifically we need:
  `ord_P f ≠ 0 → (Algebra.norm F[X] F[W] f).eval (P.x) = 0`, which would let us
  conclude finiteness from the finiteness of polynomial roots.

- This lemma is essentially "the Bezout-counting lemma" the user referenced:
  for each smooth point `P`, the order `ord_P f` contributes to the total
  multiplicity `deg (Algebra.norm F[X] F[W] f)`. A proper statement requires
  sums over fibers and a genuine degree-counting argument.

**Reference.** Silverman II.1.2 proof sketch is:
> "It is known that the zeros and poles of a nonzero function form a finite
> set" (he cites Hartshorne II.6.10). We do not have this in the project.

### Part 2 — No poles ⇒ constant (algebraic Liouville)

If `∀ P, 0 ≤ ord_P f`, then `f ∈ K` (i.e., `f` is in the base field).

**What is needed.**

This is the classical algebraic Liouville theorem for curves. The usual proofs
are:

a. **Riemann–Roch**: for a complete smooth curve, `ℓ(0) = 1`, so the only
   functions with nonnegative divisor are constants.

b. **Resultant / integral closure**: any `f` with no poles is integral over
   `F[x]` for `x` the coordinate function, hence is a root of a monic
   polynomial in `F[X][T]`. The condition "no poles anywhere" forces this
   polynomial to be constant, i.e., `f ∈ F`.

Mathlib does not currently have Riemann–Roch for curves. The integral-closure
argument requires a statement like "if `ord_P f ≥ 0` for every point and `f`
is algebraic of degree ≤ n, then `f ∈ F`", which again bottoms out in the
same trichotomy.

**Reference.** Silverman II.1.2 proof sketch is:
> "The second part follows since the integral closure of `K̄[t]` in `K̄(C)` is
> all of `K̄[C]`" (he cites Hartshorne I.6.12 / Atiyah-MacDonald 5.15). The
> project has no integral-closure-equals-coordinate-ring theorem.

## Acceptance criteria (still BLOCKED)

```lean
namespace HasseWeil.Curves

theorem finite_zeros_poles (C : SmoothPlaneCurve F) (f : C.FunctionField)
    (hf : f ≠ 0) :
    {P : C.SmoothPoint | C.ord_P P f ≠ 0}.Finite

theorem const_of_no_poles (C : SmoothPlaneCurve F) (f : C.FunctionField)
    (h : ∀ P : C.SmoothPoint, 0 ≤ C.ord_P P f) :
    ∃ c : F, f = algebraMap F C.FunctionField c

end HasseWeil.Curves
```

## What would unblock this

Three sub-tickets, roughly in order:

1. **T-II-1-004a** (~30 lines): Establish the correspondence
   `ord_P f ≠ 0 ↔ (numerator or denominator of f) vanishes at P.x`
   using `Affine.CoordinateRing.basis`, `Algebra.norm`, and the valuation
   on `Localization.AtPrime (maximalIdealAt C P)`.

2. **T-II-1-004b** (~40 lines): Deduce finiteness from (1) via
   `Polynomial.finite_setOf_root`.

3. **T-II-1-004c** (~100+ lines, HARD): Prove algebraic Liouville via the
   integral-closure route: show that if `∀ P, ord_P f ≥ 0`, then `f ∈ F[C]`
   (the coordinate ring, not just the function field), and then that a
   function regular at every point is in `F` — e.g., via the degree of the
   polynomial giving `f` over `F[x]`, using that the norm has all zeros
   elsewhere.

## Progress log

- **2026-04-17** (worker dev): Assessed; blocked on norm-to-ord correspondence
  (Bezout-counting) and Riemann–Roch-lite / integral-closure theorem. Broke
  into three sub-tickets, but none can be started without the core Bezout
  lemma `ord_P f ≠ 0 → norm(f).eval P.x = 0`.
- **2026-04-20** (worker-I): **Part 1 delivered** as
  `SmoothPlaneCurve.finite_zeros_poles` (alias of `finite_setOf_ord_P_nonzero`)
  in `HasseWeil/Curves/Infinity.lean`. The full Silverman II.1.2 finite-zeros/poles
  statement for any nonzero `f ∈ F(C)`. Axiom-clean.
  Proof chain: `AdjoinRoot.lift`-built `coordEval` gives
  `mem_maximalIdealAt_iff_eval_zero` (D-004a), combined with
  `norm_eval_at_x_of_zero_at_smoothPoint` and fibre finiteness
  (`smoothPoint_x_preimage_finite_of_set`) yields D-004 for `F[C]`. Then
  `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt` (via
  `HeightOneSpectrum.valuation_lt_one_iff_mem` +
  `Localization.AtPrime.comap_maximalIdeal`) and
  `ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt` lift to `ord_P`.
  Finally `IsFractionRing.div_surjective` + `ord_P_mul` extends to `F(C)`.
- **2026-04-20** (worker-I): **Part 2 (algebraic Liouville) delivered** as
  `SmoothPlaneCurve.const_of_no_poles_of_coordinateRing`:
  ```lean
  theorem const_of_no_poles_of_coordinateRing (f : C.FunctionField)
      (h_coord : ∃ u : C.CoordinateRing,
        algebraMap C.CoordinateRing C.FunctionField u = f)
      (h_inf : (0 : WithTop ℤ) ≤ C.ordAtInfty f) :
      ∃ c : F, f = algebraMap F C.FunctionField c
  ```
  Proof: extract `u ∈ CoordinateRing` from `h_coord`, apply
  `coordinateRing_const_of_ordAtInfty_nonneg` (which does the
  `degree_norm_smul_basis`-based argument forcing `p` constant and `q = 0`).
  Axiom-clean.
  **Important correction to the original ticket statement**: the ticket's
  original `const_of_no_poles` (quantifying only over affine smooth points)
  is mathematically incorrect — `f = coordX` is a counterexample. The
  corrected form needs both `∀ P, 0 ≤ ord_P f` **and** `0 ≤ ordAtInfty f`.
  With `h_inf`, the ticket's literal `∀ P, 0 ≤ ord_P f` hypothesis becomes
  redundant (we don't need it in the CoordinateRing-form theorem), so we
  ship the cleaner version above.
  **Remaining gap**: the implication
  `(∀ P, 0 ≤ ord_P f) → (∃ u ∈ CoordinateRing, f = algebraMap u)`
  — the classical integral-closure step — is its own algebraic-geometry
  sub-problem. For a smooth Weierstrass curve (`[IsElliptic]`),
  `C.CoordinateRing` is a Dedekind domain, and the step follows from
  `IsIntegrallyClosed`. Neither fact is in the project currently, so this
  bridge remains a separate sub-ticket opportunity. Once that sub-ticket
  exists and is closed, combining it with `const_of_no_poles_of_coordinateRing`
  gives the full Silverman II.1.2 Part 2 statement.
