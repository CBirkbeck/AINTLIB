# T-IV-BRIDGE-002: omegaPullbackCoeff α ∈ range(algebraMap F K(E))

**Status**: PARTIAL ([n] family closed via witness form)
**Silverman**: IV.4 derived
**Module**: `HasseWeil/FormalGroup/Bridge.lean`
**Owner**: (unassigned)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: E

## Depends on
- T-IV-BRIDGE-001 (formal leading coeff)

## Blocks
- T-III-5-006 (ring hom End → K̄, refining target)

## Statement
For any isogeny `α : E → E`, the coefficient `omegaPullbackCoeff α` (which is
a priori an element of `K̄(E)`) actually lies in the image of `K̄ →
K̄(E)` (i.e., is a constant function).

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem WeierstrassCurve.omegaPullbackCoeff_isConstant
    (α : Isogeny E E) :
    HasseWeil.omegaPullbackCoeff α ∈
      (algebraMap F E.toAffine.FunctionField).range

end HasseWeil.FormalGroup
```

## Notes
- This is what lets us refine `omegaPullbackCoeff : End E → K(E)` to
  `pullbackCoeffHom : End E → K̄`.
- Proof: by T-IV-BRIDGE-001, the coeff is the leading coefficient of the formal
  series, which lives in the base ring `R = ℤ[a_i]` (the universal coefficient
  ring), not in `K̄(E)`.

## Progress log
- 2026-04-26 [Claude / worker-A] **Witness form delivered** in
  `HasseWeil/FormalGroupBridge.lean`:
  `omegaPullbackCoeff_isConstant_of_witness` takes the BRIDGE-001 form
  `omegaPullbackCoeff W α = algebraMap F KE c` and produces the
  range-membership statement. Axiom-clean.
  `omegaPullbackCoeff_mulByInt_isConstant` instantiates this for `[n] ≠ 0`,
  using the existing `omegaPullbackCoeff_mulByInt`. Status OPEN → PARTIAL.
  Unconditional form (any α) requires the general BRIDGE-001 to land.
