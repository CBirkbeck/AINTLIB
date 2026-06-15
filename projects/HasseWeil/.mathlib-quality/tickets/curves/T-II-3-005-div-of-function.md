# T-II-3-005: div(f) for f ∈ K̄(C)*

**Status**: DONE (worker-I, 2026-04-20; verified axiom-clean 2026-04-22: `divisorOf` depends only on `[propext, Classical.choice, Quot.sound]`)
**Silverman**: II.3 (definition)
**Module**: `HasseWeil/Curves/Divisors.lean`
**Owner**: worker-I
**Estimated lines**: 30 (delivered ~55)
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-1-002 (ord_P)
- T-II-1-004 (finite zeros/poles)
- T-II-3-001 (Divisor)

## Blocks
- T-II-3-006 (principal divisors)
- T-II-3-008 (div(f) = 0 ⇔ f ∈ K̄*)
- T-II-3-009 (deg(div f) = 0)

## Statement
For a nonzero rational function `f ∈ K̄(C)*`, the **principal divisor** of `f` is

```
div(f) := Σ_{P ∈ C} ord_P(f) (P).
```

This is well-defined (sum is finite) by Silverman II.1.2 (T-II-1-004).

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- The principal divisor of a rational function.
    Reference: Silverman II.3 (definition). -/
noncomputable def divisorOf (C : SmoothPlaneCurve F) (f : C.FunctionField) :
    Divisor C := sorry  -- via finsupp from the finite ord_P set

theorem divisorOf_zero : divisorOf C (0 : C.FunctionField) = 0
theorem divisorOf_mul (f g : C.FunctionField) (hf : f ≠ 0) (hg : g ≠ 0) :
    divisorOf C (f * g) = divisorOf C f + divisorOf C g

/-- div as a multiplicative homomorphism (units → divisors). -/
noncomputable def divisorHom (C : SmoothPlaneCurve F) :
    C.FunctionFieldˣ →* Divisor C

end HasseWeil.Curves
```

## Notes
- "Multiplicative" means: `div(fg) = div(f) + div(g)`. Source is the unit group
  of K(C) (for nonzero functions). Target is the additive group `Divisor C`.
- The image lives in `Div⁰(C)` by Silverman II.3.1(b) (T-II-3-009).

## Progress log

- **2026-04-20** (worker-I): Delivered in `HasseWeil/Curves/Divisors.lean`
  (~55 lines). Changed `Divisor` from `def` to `abbrev` so `Finsupp.ext`
  fires without manual unfolding (no downstream impact — the existing
  `degree`/`degreeHom` API relied on the `SmoothPoint →₀ ℤ` structure
  already). Definition:
  `divisorOf f := Finsupp.ofSupportFinite (fun P => (ord_P P f).untopD 0) h`
  where `h` uses `finite_setOf_ord_P_nonzero` from `Infinity.lean` (and
  `Set.finite_empty` when `f = 0`). API: `divisorOf_apply` (rfl),
  `divisorOf_zero` (simp), `divisorOf_one` (simp), `divisorOf_mul` (for
  nonzero inputs, via `ord_P_mul` + `WithTop.untopD_coe`), and the monoid
  hom `divisorHom : F(C)ˣ →* Multiplicative (Divisor C)`. All standard
  axioms.
