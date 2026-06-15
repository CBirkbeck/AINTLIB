# T-III-5-004: m ≠ 0 in K ⇒ [m] is finite separable

**Status**: PARTIAL (witness-parametric form landed)
**Silverman**: III.5.4
**Module**: `HasseWeil/Hasse/Separability.lean` (witness form); target
`HasseWeil/EC/InvariantDiff.lean` (unconditional form)
**Owner**: worker-J
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: B/E

## Depends on
- T-III-5-003 ([m]* ω = m·ω)
- T-II-4-004 (separable ⇔ pullback injective)

## Blocks
- T-III-5-005 (m + nπ separable iff p ∤ m)
- T-V-1-002 (1 - π is separable)

## Statement (Silverman III.5.4)
Let `m ∈ ℤ` with `m ≠ 0` in `K`. Then `[m]` is a finite separable isogeny.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- Multiplication-by-m is separable when m is nonzero in K.
    Reference: Silverman III.5.4. -/
theorem WeierstrassCurve.mulByInt_isSeparable
    (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] (m : ℤ) (hm : (m : F) ≠ 0) :
    (E.mulByInt m).IsSeparable

end HasseWeil.EC
```

## Notes
- Proof: by T-II-4-004, separability ⇔ pullback `Ω_E → Ω_E` is nonzero (=
  injective for 1-dim spaces). By T-III-5-003, `[m]* ω = m·ω`. Since `m ≠ 0`
  in `K`, `m·ω ≠ 0`. So the pullback is nonzero.

## Progress log
- 2026-04-20 [worker-J] Witness form `mulByInt_isSeparable_of_witness` added to
  `HasseWeil/Hasse/Separability.lean`. Takes two hypotheses: the ω-pullback
  coefficient `= algebraMap K _ m` (discharged by
  `omegaPullbackCoeff_mulByInt` for `m ≠ 0 : ℤ`, modulo one remaining
  `sorry` in `OmegaPullbackCoeff.lean` / T-IV-BRIDGE-001) and the T-II-4-004
  separability criterion for `[m]`. Axiom-hygienic (propext/Classical.choice/
  Quot.sound only). Unconditional form remains open pending T-II-4-004.
