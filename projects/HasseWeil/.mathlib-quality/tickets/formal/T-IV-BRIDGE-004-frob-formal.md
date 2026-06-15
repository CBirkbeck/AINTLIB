# T-IV-BRIDGE-004: Frobenius pulled back to formal group is T^q

**Status**: DONE
**Silverman**: IV.4 + III.5.5
**Module**: `HasseWeil/FormalGroup/Bridge.lean`
**Owner**: (unassigned)
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: E

## Depends on
- T-IV-BRIDGE-001
- T-III-4-008 (Frobenius isogeny)
- T-IV-4-006 ([p](T) decomposition)

## Blocks
- T-III-5-005 (m + nπ separability)
- T-V-1-002 (1 - π separable)

## Statement
For an elliptic curve `E/F_q` with Frobenius `π : E → E`, the formal series
`formal_π(T) = T^q`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem formalIsogenySeries_frobenius
    (E : WeierstrassCurve (ZMod p)) [Fact (E.Δ ≠ 0)] (q : ℕ) (hq : q = p^k) :
    HasseWeil.formalIsogenySeries (E.frobeniusIsogeny q) = PowerSeries.X^q

end HasseWeil.FormalGroup
```

## Notes
- The Frobenius `(x, y) ↦ (x^q, y^q)` translates in the local parameter `z = -x/y`
  to `z^q` (since both `x` and `y` get raised to `q` and the ratio becomes the
  ratio of powers).

## Progress log
- 2026-04-26 [Claude] **CLOSED**: `formalIsogenySeries_frobenius` shipped in
  `HasseWeil/BridgeFrobenius.lean`. Six axiom-clean theorems:
  * `localExpand_localParam_pow (q : ℕ)`: localExpand of `t^q` = `single q 1`
    (uses `localExpand_localParam` + `HahnSeries.single_pow`).
  * `frobeniusIsog_pullback_localParam`: `π.pullback t = t^(card K)`
    (direct from `frobeniusIsog_pullback_apply`).
  * `formalIsogenySeries_frobenius`: `formalIsogenySeries W π = X^(card K)`
    (combines the above + `coeff_X_pow` matching).
  * `coeff_one_formalIsogenySeries_frobenius_of_card_ne_one`: `[T^1]` coeff is 0
    when `card K ≠ 1` (corollary, useful for separability arguments).
  * `omegaPullbackCoeff_frobenius`: `a_π = 0` directly via
    `Derivation.leibniz_pow` + `FiniteField.cast_card_eq_zero` (bypasses
    BRIDGE-001 entirely). This is the Silverman III.5.5 inseparability
    content for Frobenius.
  * `frobenius_pullbackKaehler_invariantDifferential`: `π* ω = 0` (corollary).
  * `not_isSeparable_frobenius_of_witness`: with T-II-4-004's criterion as
    hypothesis, `π` is not separable.
  Status OPEN → DONE. Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
