# T-IV-6-006: F(M^r) torsion-free for r > v(p)/(p−1)

**Status**: OPEN
**Silverman**: IV.6.5
**Module**: `HasseWeil/FormalGroup/DVR.lean`
**Owner**: (unassigned)
**Estimated lines**: 30
**Difficulty**: easy (corollary)
**Stream**: D

## Depends on
- T-IV-6-005 (log iso for large r)

## Blocks
- (informational)

## Statement (Silverman IV.6.5)
For `r > v(p)/(p−1)`, the group `F(M^r)` is torsion-free.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem FormalGroup.M_r_torsion_free
    (F : FormalGroup R) [IsDiscreteValuationRing R] [...] (r : ℕ)
    (hr : (r : ℝ) > v_R p / (p - 1)) :
    NoZeroSMulDivisors ℤ (F.evalGroup_powerIdeal r)

end HasseWeil.FormalGroup
```

## Notes
- Corollary of T-IV-6-005: `F(M^r) ≅ M^r` (additive group of a torsion-free
  ring), hence torsion-free.

## Progress log
