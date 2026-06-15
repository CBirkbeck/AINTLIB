# T-III-6-008: (φ̂)^ = φ

**Status**: ✅ **CONTENT-COMPLETE** (Lean theorem proved; `sorryAx` only from
T-III-6-001's `exists_dual` — becomes fully axiom-clean when T-III-6-001 closes)
**Silverman**: III.6.2(f)
**Module**: `HasseWeil/DualIsogeny.lean` (`isogDual_isogDual` at line 117)
**Owner**: (existing)
**Estimated lines**: 40
**Difficulty**: medium
**Stream**: C

## Depends on
- T-III-6-007 (deg φ̂ = deg φ)
- T-III-6-001 (uniqueness of dual)

## Blocks
- T-III-6-009 (deg quadratic form)

## Statement (Silverman III.6.2(f))
For any nonzero isogeny `φ : E₁ → E₂`,
`(φ̂)^ = φ`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

theorem Isogeny.dual_dual (φ : Isogeny E₁ E₂) (hφ : φ ≠ 0) :
    φ.dual.dual = φ

end HasseWeil.EC
```

## Notes
- By uniqueness: `(φ̂)^` is the unique isogeny `E₁ → E₂` such that
  `(φ̂)^ ∘ φ̂ = [deg φ̂] = [deg φ]`. But `φ ∘ φ̂ = [deg φ]` too (T-III-6-003 second
  half). By uniqueness, `(φ̂)^ = φ`.

## Progress log
- 2026-04-20 [worker-J audit] Lean theorem `isogDual_isogDual` (line 117)
  in `HasseWeil/DualIsogeny.lean` matches the acceptance criteria.
  Proof uses `isogDual_unique` + `self_comp_isogDual` + `degree_isogDual`.
  Cascades from the single `sorry` in `exists_dual` (T-III-6-001).
  Status OPEN → PARTIAL.
