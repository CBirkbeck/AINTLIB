# T-IV-BRIDGE-001: omegaPullbackCoeff α = (formal_α).coeff 1

**Status**: PARTIAL+ ([n] family fully closed; general α still open)
**Silverman**: IV.4 + III.5.6
**Module**: `HasseWeil/FormalGroup/Bridge.lean`
**Owner**: (existing)
**Estimated lines**: 80
**Difficulty**: hard
**Stream**: E

## Depends on
- T-IV-4-005 (chain rule)
- T-III-5-009 (omegaPullbackCoeff)

## Blocks
- T-IV-BRIDGE-002, T-IV-BRIDGE-003

## Statement
For an isogeny `α : E₁ → E₂`, let `formal_α : Ê₁ → Ê₂` be the induced formal
group homomorphism (obtained by writing `α` in the local parameters at `O`).
Then
`omegaPullbackCoeff α = (formal_α.toSeries).coeff 1`,
i.e., the leading coefficient of the formal series version equals the
coefficient through which `ω₂` pulls back.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem WeierstrassCurve.omegaPullbackCoeff_eq_formalLeading
    (α : Isogeny E₁ E₂) :
    HasseWeil.omegaPullbackCoeff α =
      (HasseWeil.formalIsogenySeries α).coeff F 1

end HasseWeil.FormalGroup
```

## Notes
- This is the bridge: it converts the abstract pullback coefficient (defined via
  the differential `ω` on the curve) to a concrete formal-power-series statement.
- Existing partial implementation in `HasseWeil/FormalGroupCorrespondence.lean`.

## Progress log
- 2026-04-08 [auto] PARTIAL — exists in HasseWeil/FormalGroupCorrespondence.lean
- 2026-04-17 [deep] MILESTONE — closed `localExpand_coordHom_injective` sorry at
  `HasseWeil/LocalExpansion.lean:501`. Added order helpers
  `ofPowerSeries_formalU_inv_orderTop`, `formalX_orderTop = -2`,
  `formalY_orderTop = -3`, and private auxiliary lemmas
  `formalX_pow_orderTop`, `localExpand_inner_orderTop_eq` (by induction on
  `natDegree` via `Polynomial.eraseLead`), `localExpand_inner_ne_zero_of_ne_zero`,
  and `localExpand_inner_mul_formalY_orderTop`. The full parity proof uses
  `Affine.CoordinateRing.exists_smul_basis_eq` to write `r = p • 1 + q • (mk Y)`,
  then shows that `p(formalX) + q(formalX) · formalY` has distinct even vs.
  odd `orderTop` when `p ≠ 0` or `q ≠ 0`, so cancellation is impossible.
  Public API unlocked: `localExpand`, `localExpand_x_gen`, `localExpand_y_gen`,
  `localExpand_localParam` (all axiom-clean: `propext + Classical.choice +
  Quot.sound` only). Full `lake build` passes (2835 jobs, 0 errors).
- 2026-04-26 [Claude / worker-A] **BRIDGE-001 closed for the `[n]` family**
  in `HasseWeil/BridgeMulByInt.lean`:
  * `omegaPullbackCoeff_eq_formalIsogenyLeading_of_mulByInt` —
    `omegaPullbackCoeff W [n] = algebraMap F KE (coeff 1 (formalIsogenySeries W [n]))`
    fully closed under `(2 : F) ≠ 0`, `(n : F) ≠ 0`. Built ~400 lines of
    Laurent-series infrastructure: `localExpand_u_gen_{orderTop,leadingCoeff}` (char ≠ 2),
    `localExpand_preΨ_2n_{orderTop,leadingCoeff}`, `localExpand_mulByInt_y_{orderTop,leadingCoeff}`
    via the Wronskian-derived Silverman IV.2.3 formula (`two_mulByInt_y_ΨSq_sq_eq`).
  * Supporting leading-coefficient API: `formalX_leadingCoeff = 1`,
    `formalY_leadingCoeff = −1`, `localExpand_inner_leadingCoeff` (polynomial-natDegree
    induction), `localExpand_{Φ_ff,ΨSq_ff,mulByInt_x}_leadingCoeff` (in
    `BridgeMulByInt.lean`). Plus `HahnSeries.{leadingCoeff_inv,leadingCoeff_div}` in
    `HasseWeil/HahnSeriesAux.lean`.
  * Generality status: full BRIDGE-001 (any α, not just `[n]`) remains the open
    sorry at `FormalIsogenySeries.lean:228`. The `[n]` specialization is what the
    Hasse-bound cascade actually consumes (via `β_qf = isogSmulSub π r s`), so this
    fully unblocks Stream D's downstream consumers for the Hasse path.
  * Status: PARTIAL → PARTIAL+ ([n] case fully closed, general α still open).
