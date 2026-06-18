# T-IV-2-006: [m] : F → F as formal group endomorphism

**Status**: REVIEW (ℕ case; ℤ extension pending T-IV-2-009)
**Silverman**: IV.2 def
**Module**: `HasseWeil/FormalGroup/MulByNat.lean` (ℕ); future `.../MulByInt.lean` for ℤ
**Owner**: worker-G
**Checked out at**: 2026-04-17T17:03Z
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-2-002 (FormalGroupHom)

## Blocks
- T-IV-2-007 ([m](T) = mT + ...)
- T-IV-2-008 (m unit ⇒ [m] iso)

## Statement (Silverman IV.2 def)
For each `m ∈ ℤ`, the iterated `m`-fold sum `[m](T) := T + T + ... + T` (using the
formal addition `F`) is a formal group endomorphism of `F`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- Multiplication-by-m on a formal group. -/
def FormalGroup.mulByInt (F : FormalGroup R) (m : ℤ) : FormalGroupHom F F

end HasseWeil.FormalGroup
```

## Notes
- Existing in `HasseWeil/FormalGroupAssoc.lean`.

## Progress log
- 2026-04-08 [auto] PARTIAL — exists in HasseWeil/FormalGroupAssoc.lean
- 2026-04-17T17:03Z [worker-G] checkout. Goal: complete (2) — package `mulByNatSeries`
  as `FormalGroupHom F F` by proving `preserves_add` (the identity
  `[n](F(X,Y)) = F([n](X), [n](Y))`). Needed to apply chain rule in T-IV-4-006.
- 2026-04-17T17:40Z [worker-G] (2) DONE for `ℕ` case.
  New file `HasseWeil/FormalGroup/MulByNat.lean` (~450 lines) provides:
  * `HasseWeil.FG.mulByNatSeries_preserves_add` — the identity
    `[n](F(X,Y)) = F([n](X), [n](Y))` in `MvPowerSeries (Fin 2) R`.
  * `HasseWeil.FormalGroup.FormalGroup.mulByNatHom F n : FormalGroupHom F F`
    whose underlying series is `mulByNatSeries F n`.
  * Simp lemmas: `mulByNatHom_toSeries`, `coeff_one_mulByNatHom`,
    `mulByNatHom_zero_toSeries`, `mulByNatHom_one_toSeries`.
  Proof strategy: introduced bivariate analogues `fAdd₂_assoc`, `fAdd₂_comm`
  of the univariate `fAdd` lemmas (mirroring the `F.assoc` / `F.comm` subst
  pattern), then derived the interchange law
  `F(F(a,b), F(c,d)) = F(F(a,c), F(b,d))` which powers the induction step.
  Build: `lake build HasseWeil.FormalGroup.MulByNat` succeeds.
  Axiom-clean: `propext, Classical.choice, Quot.sound` only.
  Remaining for full ticket: (1) extend to `ℤ` via formal inverse (requires
  T-IV-2-009, power series compositional invertibility). The ℕ version
  unblocks T-IV-4-006 (char p decomposition) directly since `p : ℕ`. Setting
  Status → REVIEW for the ℕ portion; a follow-up ticket or the original can
  extend to ℤ once T-IV-2-009 lands.
- 2026-04-10 [worker-A] Added abstract definitions to `FormalGroup/Definition.lean`:
  - `FormalGroup.fAdd`: evaluates F(f,g) for power series f,g via `MvPowerSeries.subst`.
  - `FormalGroup.mulByNatSeries`: recursive `[m](T)` for `m : ℕ`.
    `[0] = 0`, `[m+1] = F.fAdd ([m], T)`.
  - Both axiom-clean (propext, Classical.choice, Quot.sound only).
  - Full `lake build` succeeds (2763 jobs), 0 new sorries.
  - Remaining for full ticket: (1) extend to ℤ via formal inverse, (2) prove
    `preserves_add` to package as `FormalGroupHom F F`. The `preserves_add` proof
    requires induction + associativity/commutativity of `MvPowerSeries.subst`,
    which is technically involved (~100 lines, mirroring the additive FG proof
    pattern but abstract).
