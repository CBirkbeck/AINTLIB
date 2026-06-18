# T-IV-1-003: Uniqueness of w(z)

**Status**: OPEN
**Silverman**: IV.1.1(b)
**Module**: `HasseWeil/FormalGroup.lean` (existing — extend rather than create new file)
**Owner**: (released by worker-E after hitting infra limits — see progress log)
**Estimated lines**: 30 (underestimate — see notes)
**Difficulty**: medium (revised from easy — ring tactic limitation on `PowerSeries R` makes the natural factoring proof hard to write)
**Stream**: D

## Depends on
- T-IV-1-002 (w(z) exists)

## Blocks
- T-IV-1-004 (A_n homogeneous)

## Statement (Silverman IV.1.1(b))
The formal power series `w(z)` from T-IV-1-002 is uniquely determined by its
defining equation and the constraint `w(z) = z³ + O(z⁴)` (or any equivalent
normalization).

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem WeierstrassCurve.wSeries_unique (E : WeierstrassCurve F)
    (w' : PowerSeries F)
    (h : w' = (PowerSeries.X)^3 + E.a₁ * PowerSeries.X * w' + ...)
    (h0 : (w'.coeff F) 0 = 0) (h1 : (w'.coeff F) 1 = 0) (h2 : (w'.coeff F) 2 = 0) :
    w' = E.wSeries

end HasseWeil.FormalGroup
```

## Notes
- Direct from Hensel uniqueness. The "leading at z³" condition pins down which
  Hensel root we mean.

## Progress log
- 2026-04-17T18:00Z [worker-E] Checkout. Plan: add `formalW_unique` to
  existing `HasseWeil/FormalGroup.lean` (no new file). Proof strategy: reduce
  `w' = formalW W` to `d = 0` where `d := w' - formalW W`, factor
  `RHS(w') - RHS(formalW W) = K · d` for some `K` with zero constant coefficient
  (because `coeff₀ w' = 0` and `formalW_coeff_zero`), then `(1-K)` is a unit
  and so `d = 0`.
- 2026-04-17T19:30Z [worker-E] Infrastructure built:
  `HasseWeil/PowerSeriesHelpers.lean` now provides
  `PowerSeries.eq_zero_of_self_eq_mul_self` — if `f = g * f` and
  `constantCoeff g = 0`, then `f = 0` (via `order` valuation).
  This bypasses the `1 - K` unit path and the ring-on-PowerSeries bug.

  However, the factoring step `RHS(w') − RHS(formalW W) = K · d` still
  requires either `ring` or `linear_combination` on `PowerSeries R`, both
  of which fail due to typeclass gaps in mathlib v4.29.0-rc6:
  `RightDistribClass (PowerSeries R)` and `IsRightCancelAdd (PowerSeries R)`
  do not synthesize (even though `Distrib (PowerSeries R)` does).
  `ring` gets stuck mid-Horner-normalisation; `linear_combination` fails
  at instance synthesis; `abel` does not distribute so cannot handle the
  multiplicative RHS.

  **Recommended next approach**: coefficient induction via `PowerSeries.ext`.
  For each `n`, use `hrec`/`formalW_recurrence` to express `coeff n w'` and
  `coeff n (formalW W)` in terms of `coeff m` for `m < n` (via `coeff_mul`,
  `coeff_X_pow_mul`, `conv₂`, `conv₃` which are already defined and used
  in `formalW_recurrence`). Then strong induction closes the gap without
  invoking `ring` on `PowerSeries R`.

  Ticket released to OPEN. Infrastructure remains in the repo as a
  downstream win for any ticket that needs the "self = g · self"
  cancellation (e.g., fixed-point arguments in the formal-group logarithm).
- 2026-04-17T19:00Z [worker-E] Release. The `ring` tactic on `PowerSeries R`
  has a regression/limitation that blocks the natural approach:

  * `ring` fails on identities of the form `(1 - K) * (x - y) = (x - y) - K * (x - y)`.
    It normalizes both sides to Horner form `(... * 1 + 0)` but does not further
    distribute to verify equality. Even `rw [sub_mul]` fails to match
    `(1 - K) * x` pattern because of instance-path mismatch between `Sub`/`Mul`
    instances coming from `CommRing` vs `Distrib` on `PowerSeries R`.
  * `RightDistribClass (PowerSeries R)` does not synthesize (only `Distrib`
    does), breaking `add_mul`/`sub_mul` rewrites.
  * `IsRightCancelAdd (PowerSeries R)` also fails to synthesize, blocking
    `linear_combination`.
  * Manual term-mode proof via `sub_mul _ _ _ : (1-K)*x = 1*x - K*x` combined
    with `congr 1; exact one_mul _` DOES work for the `(1-K) * d = 0` step,
    but the big factoring step `RHS(w') - RHS(formalW W) = K · d` requires
    a single `ring` call that fails and would need ~30 lines of term-mode
    rewriting to reproduce.

  Alternative strategy to consider: direct coefficient induction using
  `PowerSeries.ext` and strong induction on `n`. Use `hrec` and
  `formalW_recurrence` to express `coeff n` of each side in terms of lower
  coefficients (via `coeff_mul`, `coeff_X_pow_mul`, `conv₂`, `conv₃`). The
  existing `formalW_recurrence` proof already does something similar for one
  direction; this ticket would do both and compare.

  Another alternative: `PowerSeries.order`-based proof. From `d = K · d` with
  `order K ≥ 1`, use `le_order_mul` to derive `order d ≥ order K + order d`,
  which forces `order d = ⊤` (else finite `n ≥ 1 + n` contradiction), hence
  `d = 0` via `order_eq_top`. This still requires establishing `d = K · d`,
  which is where `ring` fails.

  Tickets still OPEN; recommend marking PARTIAL with the above notes, or
  waiting on a future worker with more mathlib knowledge to pursue the
  coefficient-induction approach.
