# T-IV-6-005: log_F : F(M^r) ≅ Ĝ_a(M^r) for large r

**Status**: OPEN
**Silverman**: IV.6.4
**Module**: `HasseWeil/FormalGroup/DVR.lean`
**Owner**: (unassigned)
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-5-003 (log iso to Ĝ_a abstractly)
- T-IV-6-004 (convergence)

## Blocks
- T-IV-6-006 (torsion-free for large r)

## Statement (Silverman IV.6.4)
For `r > v(p)/(p−1)`, the formal logarithm gives an isomorphism
`log_F : F(M^r) ≅ Ĝ_a(M^r)`,
the latter being the additive group `(M^r, +)`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem FormalGroup.log_isIso_M_r
    (F : FormalGroup R) [IsDiscreteValuationRing R] [...] (r : ℕ)
    (hr : (r : ℝ) > v_R p / (p - 1)) :
    F.evalGroup_powerIdeal r ≃+ ((IsLocalRing.maximalIdeal R)^r : AddSubgroup R)

end HasseWeil.FormalGroup
```

## Progress log
