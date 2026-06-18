# T-IV-2-004: Multiplicative formal group Ĝ_m

**Status**: DONE
**Silverman**: IV.2.2
**Module**: `HasseWeil/FormalGroup/Definition.lean`
**Owner**: worker-A
**Checked out at**: 2026-04-08T21:16Z
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: D

## Depends on
- T-IV-2-001 (FormalGroup R)

## Blocks
- T-IV-3-004 (Ĝ_m(M))

## Statement (Silverman IV.2.2)
The **multiplicative formal group** `Ĝ_m` over any ring `R` is given by
`F(X, Y) = X + Y + XY = (1+X)(1+Y) − 1`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- The multiplicative formal group law: F(X, Y) = X + Y + XY.
    Reference: Silverman IV.2.2. -/
def multiplicativeFormalGroup (R : Type*) [CommRing R] : FormalGroup R := {
  formal := MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 0 * MvPowerSeries.X 1
  -- proofs of axioms
}

end HasseWeil.FormalGroup
```

## Notes
- The point: in `R[[X,Y]]`, define `(1+X)(1+Y) - 1 = X + Y + XY`. Associativity
  follows from associativity of multiplication.

## Progress log
- 2026-04-08T21:16Z [worker-A] checkout + complete. Added
  `multiplicativeFormalGroup` in `HasseWeil/FormalGroup/Definition.lean` with
  `toSeries = X 0 + X 1 + X 0 * X 1`. Proofs parallel `additiveFormalGroup` but
  use `subst_mul` in addition to `subst_add`. `ring` closes the final algebraic
  identities. `lake build HasseWeil.FormalGroup.Definition` clean. Standard
  axioms only. Status: DONE.