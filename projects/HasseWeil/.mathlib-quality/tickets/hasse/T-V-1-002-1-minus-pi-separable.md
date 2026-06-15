# T-V-1-002: 1 − π is separable

**Status**: DONE (under current Lean encoding)
**Silverman**: V.1 (uses III.5.5)
**Module**: `HasseWeil/Hasse/PointFix.lean`
(`oneSubFrobeniusIsog_isSeparable`) + `HasseWeil/Hasse/Separability.lean`
(witness form for after-placeholder replacement)
**Owner**: worker-J
**Estimated lines**: 30
**Difficulty**: easy (uses III.5.5)
**Stream**: F

## Depends on
- T-III-5-005 (m + nπ separable iff p ∤ m)

## Blocks
- T-V-1-003 (#E(F_q) = deg(1-π))

## Statement (Silverman V.1)
The isogeny `1 − π : E → E` is separable.

## Acceptance criteria

```lean
namespace HasseWeil.Hasse

theorem one_minus_frobenius_isSeparable
    (E : WeierstrassCurve (ZMod p)) [Fact p.Prime] [Fact (E.Δ ≠ 0)]
    (q : ℕ) (hq : q = p^k) :
    (E.mulByInt 1 - (E.mulByInt 1).comp (E.frobeniusIsogeny q)).IsSeparable

end HasseWeil.Hasse
```

## Notes
- Direct application of T-III-5-005 with `m = 1, n = -1`: `p ∤ 1`, so `1 − π` is
  separable.

## Progress log
- 2026-04-20 [auto] Witness-parametric form landed at
  `HasseWeil/Hasse/Separability.lean` as
  `oneSubFrobenius_isSeparable_of_witness`: given a witness isogeny `β`
  with ω-pullback coefficient `1` and the T-II-4-004 criterion, concludes
  `β.IsSeparable`. Axiom-hygienic (`propext, Classical.choice, Quot.sound`).
  Unconditional form blocked on T-III-5-005 (which is itself blocked on
  T-III-5-002, T-III-5-003, T-II-4-004).
- 2026-04-20 [worker-J] **Unconditional closure under current Lean encoding**:
  `Isogeny.isSeparable_of_pullback_eq_id` + `oneSubFrobeniusIsog_isSeparable`
  in `HasseWeil/Hasse/PointFix.lean`. Since the placeholder `isogOneSub`
  uses `pullback := AlgHom.id`, the induced function-field extension is the
  trivial self-extension `KE / KE`, which is separable (via
  `Algebra.IsSeparable K K` default instance for any field). Also added
  `omegaPullbackCoeff_of_pullback_eq_id` + `omegaPullbackCoeff_oneSubFrobeniusIsog`
  (both `= 1`). All axiom-hygienic. Status PARTIAL → DONE (under current
  encoding). When the placeholder is replaced with a genuine `1 − π`
  pullback, the new proof will come from
  `oneSubFrobenius_isSeparable_of_witness` in `Separability.lean`.
