# T-IV-2-001: FormalGroup R structure

**Status**: DONE
**Silverman**: IV.2 (definition)
**Module**: `HasseWeil/FormalGroup/Definition.lean`
**Owner**: worker-A
**Checked out at**: 2026-04-08T18:42Z
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: D

## Depends on
- (mathlib power series)

## Blocks
- T-IV-2-002..009

## Statement (Silverman IV.2 def)
A **(one-parameter, commutative) formal group law** over a commutative ring `R`
is a power series `F(X, Y) ∈ R[[X, Y]]` such that
- `F(X, 0) = X` and `F(0, Y) = Y`
- `F(F(X, Y), Z) = F(X, F(Y, Z))` (associativity)
- `F(X, Y) = F(Y, X)` (commutativity)
- There exists a unique `i(X) ∈ R[[X]]` with `F(X, i(X)) = 0`

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- A one-parameter commutative formal group law over R.
    Reference: Silverman IV.2. -/
structure FormalGroup (R : Type*) [CommRing R] where
  formal : MvPowerSeries (Fin 2) R
  unitX : MvPowerSeries.eval₂ ... formal = MvPowerSeries.X 0
  unitY : ... = MvPowerSeries.X 1
  assoc : ...
  comm : ...

end HasseWeil.FormalGroup
```

## Notes
- Existing partial definition in `HasseWeil/FormalGroup.lean`. Refactor needed
  for clean abstract structure.
- mathlib has some related structure in `Mathlib.RingTheory.PowerSeries`.

## Progress log
- 2026-04-08T18:42Z [worker-A] checkout. Old chain #31 → new T-IV-2-001. Plan:
  create `HasseWeil/FormalGroup/Definition.lean` with the abstract `FormalGroup R`
  structure per Silverman IV.2 def. Existing concrete `formalW_coeff`/`formalGroupLaw_coeff`
  in `HasseWeil/FormalGroup.lean` stays for now; will be wrapped into a
  `WeierstrassCurve.formalGroup : FormalGroup R` in T-IV-2-005. The migration
  of the existing monolithic file is a separate ticket (T-MIGRATE-011).
- 2026-04-08T19:00Z [worker-A] Complete. Created `HasseWeil/FormalGroup/Definition.lean`
  (~100 lines with docstrings) defining `FormalGroup R` as a structure with fields
  `toSeries : MvPowerSeries (Fin 2) R`, `lunit` (F(X,0)=X), `runit` (F(0,Y)=Y),
  `assoc` (F(F(X,Y),Z)=F(X,F(Y,Z))), `comm` (F(X,Y)=F(Y,X)). Axioms expressed via
  `MvPowerSeries.subst`. Associativity stated in `MvPowerSeries (Fin 3) R`.
  Inverse `i(T)` is NOT a field — derivable from the axioms via T-IV-2-009.
  `lake build HasseWeil.FormalGroup.Definition` passes, zero sorries, zero custom
  axioms. Full project build still passes (2763 jobs). Status: REVIEW.
