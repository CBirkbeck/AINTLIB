# T-IV-6-002: F(p ℤ_p) torsion-free for p ≥ 2 (example)

**Status**: OPEN
**Silverman**: IV.6.1.1
**Module**: `HasseWeil/FormalGroup/DVR.lean`
**Owner**: (unassigned)
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: D

## Depends on
- T-IV-6-001 (DVR torsion)
- T-IV-6-006 (F(M^r) torsion-free for r large)

## Blocks
- (informational)

## Statement (Silverman IV.6.1.1)
For `R = ℤ_p` (the p-adic integers), and any formal group `F` over `R`, the
group `F(p ℤ_p)` is torsion-free (assuming `p ≥ 3`; for `p = 2` need `r ≥ 2`).

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem FormalGroup.zp_torsion_free (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (F : FormalGroup (ZMod p)) :
    -- F(p · ℤ_p) is torsion free
    True  -- placeholder

end HasseWeil.FormalGroup
```

## Progress log
