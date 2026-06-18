# T-III-5-003: [m]* ω = m·ω

**Status**: PARTIAL (PullbackCoeff.lean has SORRY)
**Silverman**: III.5.3
**Module**: `HasseWeil/PullbackCoeff.lean` → `HasseWeil/EC/InvariantDiff.lean`
**Owner**: (existing)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: B/E

## Depends on
- T-III-5-002 (additivity)

## Blocks
- T-III-5-004 (m ≠ 0 ⇒ [m] separable)
- T-III-5-005 (m + nπ separability criterion)

## Statement (Silverman III.5.3)
For all `m ∈ ℤ`, `[m]* ω = m · ω`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The pullback of the invariant differential along [m] is m·ω.
    Reference: Silverman III.5.3. -/
theorem WeierstrassCurve.mulByInt_pullback_omega
    (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] (m : ℤ) :
    (E.mulByInt m).pullback E.invariantDifferential =
      (m : F) • E.invariantDifferential

end HasseWeil.EC
```

## Notes
- Direct corollary of T-III-5-002 by induction:
  - `[1]* ω = ω`
  - `[m+1]* ω = ([m] + [1])* ω = [m]* ω + [1]* ω = m·ω + ω = (m+1)·ω`
  - and dually for negative m.

## Progress log
- 2026-04-20 [worker-J] Witness form
  `mulByInt_pullbackKaehler_invariantDifferential_of_witness` landed in
  `HasseWeil/Hasse/Separability.lean`: given the coefficient hypothesis
  `omegaPullbackCoeff W [m] = algebraMap K _ m` (discharged by
  `omegaPullbackCoeff_mulByInt` for `m ≠ 0 : ℤ`), concludes
  `[m].pullbackKaehler ω = (m : F) • ω` via
  `Isogeny.pullbackKaehler_invariantDifferential` + `algebraMap_smul`.
  Axiom-hygienic (standard only). Unconditional form for `m = 0`
  remains tied to the `mulByInt 0` placeholder design.
