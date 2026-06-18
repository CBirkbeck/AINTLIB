# T-IV-3-003: Ĝ_a(M) = (M, +)

**Status**: DONE
**Silverman**: IV.3.1.1
**Module**: `HasseWeil/FormalGroup/Associated.lean`
**Owner**: (claimed)
**Estimated lines**: 20 (delivered ~100 including multiplicative companion)
**Difficulty**: easy
**Stream**: D

## Depends on
- T-IV-2-003 (Ĝ_a) — DONE
- T-IV-3-001 (F(M)) — DONE (AddCommGroup instance `evalGroup` in `EvalGroup.lean`)

## Blocks
- (informational)

## Statement (Silverman IV.3.1.1)
For the additive formal group `Ĝ_a` (with `F(X,Y) = X + Y`), `Ĝ_a(M)` is just
`(M, +)`, the maximal ideal as an additive group.

## Acceptance criteria (DONE)

Operation-level identity (only `[CommRing R] [IsLocalRing R] [UniformSpace R]`):

```lean
theorem HasseWeil.FormalGroup.evalAdd_additiveFormalGroup
    (x y : IsLocalRing.maximalIdeal R) :
    (additiveFormalGroup R).evalAdd x y = x.1 + y.1
```

Negation (needs full adic-topology hypotheses for `evalAdd_evalNeg`):

```lean
theorem HasseWeil.FormalGroup.evalNeg_additiveFormalGroup
    (hAdic : IsAdic (IsLocalRing.maximalIdeal R))
    (x : IsLocalRing.maximalIdeal R) :
    (additiveFormalGroup R).evalNeg x = -x.1
```

## Delivered bonus (T-IV-3-004 groundwork)

The same file also records the multiplicative analogues:

```lean
theorem evalAdd_multiplicativeFormalGroup (x y : maximalIdeal R) :
    (multiplicativeFormalGroup R).evalAdd x y = x.1 + y.1 + x.1 * y.1

theorem evalAdd_multiplicativeFormalGroup_one_add (x y : maximalIdeal R) :
    1 + (multiplicativeFormalGroup R).evalAdd x y = (1 + x.1) * (1 + y.1)
```

The second realises the Silverman IV.3.1.2 bijection `x ↦ 1 + x` between
`Ĝ_m(M)` and `(1 + M, ·)` at the operation level. Full packaging of T-IV-3-004 as
an `AddEquiv`/`MulEquiv` is left for a follow-up ticket.

## Notes

- Proof strategy: reduce `evalAdd F x y` to polynomial evaluation via
  `MvPowerSeries.eval₂_coe` + `MvPolynomial.eval₂_add` / `eval₂_X` / `eval₂_mul`.
  No topological or completeness hypothesis is needed for the operation-level
  identity; only `UniformSpace R` is required (to make the `evalAdd` function
  itself definable).
- Axiom-clean: `propext, Classical.choice, Quot.sound` only (verified with
  `#print axioms`).

## Progress log

- 2026-04-20 Delivered `HasseWeil/FormalGroup/Associated.lean` (~100 lines):
  `evalAdd_additiveFormalGroup`, `evalNeg_additiveFormalGroup`,
  `evalAdd_multiplicativeFormalGroup`, `evalAdd_multiplicativeFormalGroup_one_add`.
  `lake build HasseWeil.FormalGroup.Associated` passes clean (1820/1820 jobs).
  Axiom-clean.
