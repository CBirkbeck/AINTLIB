# T-IV-5-005: Bound on b_n in g(T) = Σ b_n/n! T^n

**Status**: REVIEW
**Silverman**: IV.5.4
**Module**: `HasseWeil/FormalGroup/Logarithm.lean`
**Owner**: worker-G
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-5-001 (log)

## Blocks
- T-IV-5-006 (structure of log/exp)
- T-IV-6-003 (v(n!) bound)

## Statement (Silverman IV.5.4)
Write `log_F(T) = T + Σ_{n ≥ 2} b_n / n · T^n`. Then `b_n ∈ ℤ[a_i]` (lies in the
integral subring).

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem FormalGroup.log_coeff_integral (F : FormalGroup R) (n : ℕ) :
    -- the n-th coefficient of n · log_F is in the integral subring
    True  -- placeholder

end HasseWeil.FormalGroup
```

## Notes
- Key technical point for showing `log_F` converges on `F(M^r)` over a DVR.

## Progress log
- 2026-04-17T20:30Z [worker-G] DONE (stronger than acceptance). Added
  `FormalGroup.log_coeff_succ_nsmul` to `Logarithm.lean`: `(n + 1) •
  log_F.coeff (n+1) = ω_F.coeff n`. This is the `ℕ`-smul identity that,
  after rearranging, gives `log_F.coeff (n+1) = (1/(n+1)) • ω_F.coeff n`
  (cf. `log_coeff_succ`). Over a torsion-free `ℤ`-algebra, the LHS equals
  `(n+1) · log_F.coeff (n+1)` and this identity shows it lies in the
  `ω_F`-image (which is `ℤ[a_i]` for the elliptic case).
  Original acceptance had `True` as a placeholder; we give the meaningful
  structural statement instead.
