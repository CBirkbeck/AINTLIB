# T-IV-6-004: Convergence of formal series over DVR

**Status**: OPEN
**Silverman**: IV.6.3
**Module**: `HasseWeil/FormalGroup/DVR.lean`
**Owner**: (unassigned)
**Estimated lines**: 80
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-6-003 (v(n!) bound)

## Blocks
- T-IV-6-005 (log iso for M^r)

## Statement (Silverman IV.6.3)
Let `K` be a complete DVR field. The formal series `log_F` and `exp_F` converge
on suitable subdomains: specifically, on `F(M^r)` for `r > v(p)/(p−1)`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- log_F converges on F(M^r) for r > v(p)/(p-1). -/
theorem FormalGroup.log_converges_on_M_r
    (F : FormalGroup R) [IsDiscreteValuationRing R] [...] (r : ℕ)
    (hr : (r : ℝ) > v_R p / (p - 1)) :
    -- log_F evaluated on F(M^r) converges
    True  -- placeholder

end HasseWeil.FormalGroup
```

## Notes
- The condition `r > v(p)/(p-1)` is the threshold above which log/exp converge.

## Progress log
