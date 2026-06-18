# T-III-6-004: (λ ∘ φ)^ = φ̂ ∘ λ̂ (functoriality)

**Status**: OPEN
**Silverman**: III.6.2(b)
**Module**: `HasseWeil/EC/DualIsogeny.lean`
**Owner**: (unassigned)
**Estimated lines**: 40
**Difficulty**: easy
**Stream**: C

## Depends on
- T-III-6-001 (dual exists)
- T-III-6-003 (composition formula)

## Blocks
- T-III-6-007 (deg φ̂ = deg φ)

## Statement (Silverman III.6.2(b))
For composable isogenies `φ : E₁ → E₂, λ : E₂ → E₃`,
`(λ ∘ φ)^ = φ̂ ∘ λ̂ : E₃ → E₁`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

theorem Isogeny.dual_comp (φ : Isogeny E₁ E₂) (λ : Isogeny E₂ E₃)
    (hφ : φ ≠ 0) (hλ : λ ≠ 0) :
    (λ.comp φ).dual = φ.dual.comp λ.dual

end HasseWeil.EC
```

## Notes
- Uniqueness from T-III-6-001 + checking the defining equation.

## Progress log
