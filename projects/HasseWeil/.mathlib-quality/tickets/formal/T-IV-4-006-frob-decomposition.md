# T-IV-4-006: char p: [p](T) = p f(T) + g(T^p)

**Status**: REVIEW
**Silverman**: IV.4.4
**Module**: `HasseWeil/FormalGroup/CharP.lean`
**Owner**: worker-G
**Checked out at**: 2026-04-17T17:40Z
**Estimated lines**: 80
**Difficulty**: hard (CRITICAL)
**Stream**: D

## Depends on
- T-IV-4-005 (chain rule)
- T-IV-2-006 ([m] formal endo)

## Blocks
- T-IV-BRIDGE-004 (Frobenius pulled back is T^q)
- T-IV-7-001 (height)

## Statement (Silverman IV.4.4)
Let `R` be a ring of characteristic `p > 0`. Then for any formal group `F` over
`R` and any positive integer `m`, the multiplication-by-m series satisfies
`[p](T) = p f(T) + g(T^p)` for some `f, g ∈ R[[T]]`. In particular, if `R` is
a field, `[p](T) = g(T^p)` for some `g`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem FormalGroup.mulByP_decomposition (F : FormalGroup R)
    (p : ℕ) (hp : p.Prime) [CharP R p] :
    ∃ f g : PowerSeries R,
      (F.mulByInt (p : ℤ)).toSeries = (p : R) • f + g.subst (PowerSeries.X^p)

end HasseWeil.FormalGroup
```

## Notes
- Proof: by chain rule (T-IV-4-005), `ω ∘ [p] = [p]'(T) · ω`. The leading
  coefficient of `[p]` is `p` (T-IV-2-007), which is `0` in char `p`. So
  `[p]'(T) = 0` formally, meaning `[p](T)` only has terms in `T^p, T^{2p}, ...`
  So `[p](T) = g(T^p)`.

## Progress log
- 2026-04-17T17:40Z [worker-G] Checkout. Plan: apply chain rule (from
  T-IV-4-005) to `mulByNatHom p` (from T-IV-2-006 ℕ case). In char p,
  `coeff 1 [p] = p = 0`, so RHS of chain rule vanishes. Unit of
  `subst [p] ω_F` (via `constantCoeff = 1`) gives `derivative [p] = 0`.
  Derivative-zero then forces `coeff n [p] = 0` for `p ∤ n` (via
  `CharP.isUnit_natCast_iff`), hence `[p] = g.expand p hp` for some g.
- 2026-04-17T18:30Z [worker-G] DONE. New file `HasseWeil/FormalGroup/CharP.lean`
  (~150 lines) provides:
  * `FormalGroup.mulByP_exists_expand F p : ∃ g, [p].toSeries = g.expand p hp`
    — the clean "lives in R[[T^p]]" form.
  * `FormalGroup.mulByP_decomposition F p : ∃ f g, [p] = C p * f + g.expand p hp`
    — the Silverman-faithful decomposition form (with `f = 0`).
  Uses `mathlib`'s `PowerSeries.expand` (= `subst (X^p)`), `CharP.isUnit_natCast_iff`,
  `IsUnit.mul_right_eq_zero`, and the chain rule.
  Axiom-clean: `propext, Classical.choice, Quot.sound` only.
  Full `lake build` passes.
- Status: REVIEW — ready for verification.
