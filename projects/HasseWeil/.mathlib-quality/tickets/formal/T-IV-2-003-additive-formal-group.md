# T-IV-2-003: Additive formal group Ĝ_a

**Status**: DONE
**Silverman**: IV.2.1
**Module**: `HasseWeil/FormalGroup/Definition.lean`
**Owner**: worker-A
**Checked out at**: 2026-04-08T21:00Z
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: D

## Depends on
- T-IV-2-001 (FormalGroup R)

## Blocks
- T-IV-3-003 (Ĝ_a(M))
- T-IV-5-003 (log iso to Ĝ_a)

## Statement (Silverman IV.2.1)
The **additive formal group** `Ĝ_a` over any ring `R` is given by
`F(X, Y) = X + Y`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- The additive formal group law: F(X, Y) = X + Y.
    Reference: Silverman IV.2.1. -/
def additiveFormalGroup (R : Type*) [CommRing R] : FormalGroup R := {
  formal := MvPowerSeries.X 0 + MvPowerSeries.X 1
  -- proofs of axioms
}

end HasseWeil.FormalGroup
```

## Progress log
- 2026-04-08T21:00Z [worker-A] checkout. Will define `additiveFormalGroup` as
  `FormalGroup R` with `toSeries = X 0 + X 1`. Proofs of unit/assoc/comm are
  straightforward applications of `subst_add`, `subst_X`, `subst_zero` after
  establishing `HasSubst` via `hasSubst_of_constantCoeff_zero`.
- 2026-04-08T21:15Z [worker-A] Complete. Added `additiveFormalGroup` in
  `HasseWeil/FormalGroup/Definition.lean` with `toSeries = X 0 + X 1`. All four
  axioms proved via `MvPowerSeries.subst_add`, `subst_X`, and `ring`/`simp` for
  the resulting ring identities. `HasSubst` established per-case via
  `hasSubst_of_constantCoeff_zero` + `fin_cases`. `lake build
  HasseWeil.FormalGroup.Definition` clean. `#print axioms
  HasseWeil.FormalGroup.additiveFormalGroup` = `[propext, Classical.choice,
  Quot.sound]`. Status: DONE.
