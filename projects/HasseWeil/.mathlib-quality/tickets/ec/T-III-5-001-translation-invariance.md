# T-III-5-001: τ_Q* ω = ω (translation invariance)

**Status**: PARTIAL (witness-parametric form landed)
**Silverman**: III.5.1
**Module**: `HasseWeil/Hasse/Separability.lean` (witness form); target
`HasseWeil/EC/InvariantDiff.lean` (unconditional form)
**Owner**: worker-J
**Estimated lines**: 100
**Difficulty**: hard
**Stream**: B/E

## Depends on
- T-III-1-009 (div(ω) = 0)
- T-II-3-008 (div(f) = 0 ⇒ const)
- T-III-4-009 (translation map τ_Q)

## Blocks
- T-III-5-002 (additivity)
- T-III-5-006 (ring hom End → K̄)

## Statement (Silverman III.5.1)
For all `Q ∈ E(K̄)`, the pullback `(τ_Q)*ω = ω`, where `ω` is the invariant
differential of `E`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The invariant differential is translation-invariant.
    Reference: Silverman III.5.1. -/
theorem WeierstrassCurve.translation_invariant_omega
    (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] (Q : E.toAffine.Point) :
    Differentials.pullback (E.translation Q).toMorphism _ E.invariantDifferential =
      E.invariantDifferential

end HasseWeil.EC
```

## Notes
- Proof outline:
  1. The space of holomorphic nonvanishing differentials on `E` is
     1-dimensional (over K̄), spanned by `ω` (since `Ω_E` is 1-dim and `div(ω) = 0`).
  2. `τ_Q*` preserves the property of being holomorphic nonvanishing (translation
     is an isomorphism, so it preserves orders of differentials).
  3. Therefore `τ_Q*ω = c(Q) ω` for some `c(Q) ∈ K̄*`.
  4. The map `Q ↦ c(Q)` is a morphism `E → 𝔾_m`. Since `E` is complete and `𝔾_m`
     is affine, this morphism is constant.
  5. At `Q = O`, `τ_O = id`, so `c(O) = 1`. Hence `c(Q) = 1` for all `Q`.

## Progress log
- 2026-04-20 [worker-J] Witness-parametric form
  `translation_pullbackKaehler_invariantDifferential_of_witness` landed at
  `HasseWeil/Hasse/Separability.lean`. Given a witness isogeny `τ` with
  `omegaPullbackCoeff W τ = 1` (the characterizing property of
  translations preserving ω), concludes `τ* ω = ω`. Built on the generic
  `pullbackKaehler_invariantDifferential_of_coeff_witness` which also
  covers III.5.3. Axiom-hygienic (standard only). Unconditional form
  requires proving the coefficient hypothesis for the actual translation
  isogeny `τ_Q`.
