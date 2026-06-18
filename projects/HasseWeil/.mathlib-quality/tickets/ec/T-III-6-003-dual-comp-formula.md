# T-III-6-003: φ̂ ∘ φ = [deg φ] and φ ∘ φ̂ = [deg φ]

**Status**: ✅ **CONTENT-COMPLETE** (Lean theorems proved; `sorryAx` only from
T-III-6-001's `exists_dual` — becomes fully axiom-clean when T-III-6-001 closes)
**Silverman**: III.6.2(a)
**Module**: `HasseWeil/DualIsogeny.lean` (`isogDual_comp_self`,
`self_comp_isogDual` at lines 81, 86)
**Owner**: (existing)
**Estimated lines**: 30
**Difficulty**: easy (corollary of construction)
**Stream**: C

## Depends on
- T-III-6-001 (dual exists)

## Blocks
- T-III-6-009 (deg quadratic form)

## Statement (Silverman III.6.2(a))
For a nonzero isogeny `φ : E₁ → E₂` of degree `m`,
`φ̂ ∘ φ = [m]` (on `E₁`) and `φ ∘ φ̂ = [m]` (on `E₂`).

## Acceptance criteria

```lean
namespace HasseWeil.EC

theorem Isogeny.dual_comp_self (φ : Isogeny E₁ E₂) (hφ : φ ≠ 0) :
    φ.dual.comp φ = E₁.mulByInt φ.degree

theorem Isogeny.self_comp_dual (φ : Isogeny E₁ E₂) (hφ : φ ≠ 0) :
    φ.comp φ.dual = E₂.mulByInt φ.degree

end HasseWeil.EC
```

## Notes
- The first is by definition. The second requires also using `φ̂` on `E₂` which
  is symmetric.

## Progress log
- 2026-04-20 [worker-J audit] Lean theorems `isogDual_comp_self` (line 81)
  and `self_comp_isogDual` (line 86) in `HasseWeil/DualIsogeny.lean`
  already match the acceptance criteria. Both derive from
  `isogDual_spec` which uses the existential `exists_dual` (the single
  `sorry` in `DualIsogeny.lean`, T-III-6-001). Status OPEN → PARTIAL.
