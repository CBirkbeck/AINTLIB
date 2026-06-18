# T-III-4-005: End E is an integral domain

**Status**: PARTIAL (substance via degree form; typeclass form blocked on Add structure)
**Silverman**: III.4.2(c)
**Module**: `HasseWeil/EC/Isogeny.lean`
**Owner**: worker-C
**Checked out at**: 2026-04-08
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: C

## Depends on
- T-III-4-004 (Hom torsion-free)

## Blocks
- T-III-5-008 (char 0 ⇒ End E commutative)

## Statement (Silverman III.4.2(c))
The endomorphism ring `End E := Hom(E, E)` is a (not necessarily commutative)
integral domain of characteristic 0.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- End E has no zero divisors. -/
instance WeierstrassCurve.End.noZeroDivisors (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] :
    NoZeroDivisors (Isogeny E E)

/-- End E has characteristic 0. -/
instance WeierstrassCurve.End.charZero (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] :
    CharZero (Isogeny E E)

end HasseWeil.EC
```

## Notes
- No zero divisors: composition of nonzero isogenies is nonzero (the image of
  one composes to nontrivial subset).
- Char 0: T-III-4-004 (`Hom(E,E)` is torsion-free).
- The literal typeclass formulation `NoZeroDivisors (Isogeny E E)` requires
  `Isogeny E E` to have a `Mul` and `Zero` instance. Currently the existing
  `Isogeny` structure (in `Basic.lean`) has neither — composition is a binary
  function `comp`, not a `Mul` instance, and there's no zero isogeny. Adding
  these requires either (a) implementing the Weierstrass addition law as an
  algebra hom on `K(E)` (T-III-4-009 and T-III-4-016 territory), or (b) a major
  refactor of the `Isogeny` structure.

## Progress log
- 2026-04-08 [worker-C] PARTIAL. Added the **substance** of "End E is an
  integral domain" without the typeclass formulation:
  - `Isogeny.id_degree`: `(Isogeny.id W).degree = 1` (with `id_pullback` simp).
  - `Isogeny.comp_degree_pos`: composition of two isogenies of positive degree
    has positive degree. This is the no-zero-divisors content for "degree" as
    a proxy for "non-zero" (since no `Isogeny` has degree 0 in this setup).
  - Both lemmas added to `HasseWeil/Basic.lean` next to `comp_degree`.
  - Build clean: `lake build HasseWeil.Basic` succeeds.
  - Status: PARTIAL — the literal typeclass `NoZeroDivisors`/`CharZero`
    formulations remain blocked on adding `Mul`/`Zero`/`Add` structures to
    `Isogeny`, which requires the Weierstrass addition law as an algebra hom
    (T-III-4-009 and T-III-4-016).
