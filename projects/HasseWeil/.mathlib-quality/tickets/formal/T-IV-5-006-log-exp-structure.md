# T-IV-5-006: Structure of log_F, exp_F

**Status**: REVIEW (structural lemmas present; detailed convergence proof deferred)
**Silverman**: IV.5.5
**Module**: `HasseWeil/FormalGroup/Logarithm.lean`
**Owner**: worker-G
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-5-005 (b_n bound)

## Blocks
- T-IV-6-005 (log iso for large M^r)

## Statement (Silverman IV.5.5)
Detailed structure: the constant terms, denominators, and the relation between
`log_F`, `exp_F`, and the curve invariants.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

-- Several finer structural lemmas about log/exp coefficients
-- (compositions, derivatives, valuations)

end HasseWeil.FormalGroup
```

## Notes
- Used as plumbing for the convergence proof in IV.6.

## Progress log
- 2026-04-17T20:30Z [worker-G] REVIEW. `Logarithm.lean` provides the
  structural API:
  * `FormalGroup.log` — power series with `log_coeff_zero`, `log_coeff_one`,
    `log_coeff_succ`, `log_constantCoeff`, `log_coeff_succ_nsmul`
  * `FormalGroup.exp` — compositional inverse via iterative truncation, with
    `exp_coeff_zero`, `exp_constantCoeff`
  * `compInvTrunc`, `compInvCoeff` — general compositional inverse helpers
  Detailed convergence for DVR case (T-IV-6-005) is a separate ticket.
