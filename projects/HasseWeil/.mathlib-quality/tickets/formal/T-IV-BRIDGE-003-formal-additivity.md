# T-IV-BRIDGE-003: formal_α + formal_β = formal_(α+β)

**Status**: OPEN
**Silverman**: IV.1 + III.5.2
**Module**: `HasseWeil/FormalGroup/Bridge.lean`
**Owner**: (unassigned)
**Estimated lines**: 100
**Difficulty**: hard (CRITICAL for III.5.2)
**Stream**: E

## Depends on
- T-IV-BRIDGE-001
- T-IV-1-008 (formal addition F(z₁, z₂))
- T-III-2-009 (translation map)

## Blocks
- T-III-5-002 (additivity of pullback)

## Statement
For two isogenies `α, β : E₁ → E₂`, the formal-group representation of `α + β`
(as a hom of formal groups `Ê₁ → Ê₂`) is `F_2(formal_α, formal_β)`, where
`F_2` is the formal addition law of `Ê₂`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem formalIsogenySeries_add (α β : Isogeny E₁ E₂) :
    HasseWeil.formalIsogenySeries (α + β) =
      MvPowerSeries.subst (E₂.formalAddition.formal)
        ![HasseWeil.formalIsogenySeries α, HasseWeil.formalIsogenySeries β]

end HasseWeil.FormalGroup
```

## Notes
- This is the missing link: it says that the function-field side of "addition of
  isogenies" goes through the formal addition law of the target curve.
- Once this is established, T-III-5-002 (additivity of `α* ω`) follows by
  combining T-IV-BRIDGE-001 with the chain rule (T-IV-4-005).

## Progress log
