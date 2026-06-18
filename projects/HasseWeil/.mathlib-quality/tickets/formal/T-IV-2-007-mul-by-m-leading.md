# T-IV-2-007: [m](T) = m T + O(T²)

**Status**: REVIEW (ℕ case via `mulByNatHom`; ℤ extension pending T-IV-2-009)
**Silverman**: IV.2.3(a)
**Module**: `HasseWeil/FormalGroup/MulByNat.lean`
**Owner**: worker-G
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: D

## Depends on
- T-IV-2-006 ([m] formal endo)

## Blocks
- T-IV-2-008 (m unit ⇒ iso)
- T-IV-BRIDGE-001 (omegaPullbackCoeff = leading)

## Statement (Silverman IV.2.3(a))
The leading coefficient of `[m](T)` (as a power series in `T`) is `m`. That is,
`[m](T) = m T + O(T²)`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem FormalGroup.mulByInt_coeff_one (F : FormalGroup R) (m : ℤ) :
    (F.mulByInt m).toSeries.coeff R 1 = (m : R)

theorem FormalGroup.mulByInt_coeff_zero (F : FormalGroup R) (m : ℤ) :
    (F.mulByInt m).toSeries.coeff R 0 = 0

end HasseWeil.FormalGroup
```

## Notes
- The `pullbackCoeff_mulByInt` SORRY in current code corresponds to this lemma.

## Progress log
- 2026-04-08 [auto] PARTIAL — partial, see pullbackCoeff_mulByInt SORRY
- 2026-04-17T19:30Z [worker-G] ℕ case DONE via `HasseWeil/FormalGroup/MulByNat.lean`:
  * `FormalGroup.coeff_one_mulByNatHom F n : coeff 1 (F.mulByNatHom n).toSeries = (n : R)`
    — the `ℕ` analogue of `FormalGroup.mulByInt_coeff_one`. Tagged `@[simp]`.
  * `FormalGroup.mulByNatHom_zero_toSeries F : (F.mulByNatHom 0).toSeries = 0`
    — implies `coeff 0 = 0`. Tagged `@[simp]`.
  More broadly, every `mulByNatHom F n` has `zero_const : constantCoeff = 0`
  (the `FormalGroupHom` axiom).
  ℤ extension is gated on T-IV-2-009 (compositional inverse).
