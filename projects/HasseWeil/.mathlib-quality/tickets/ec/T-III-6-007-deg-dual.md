# T-III-6-007: deg φ̂ = deg φ

**Status**: ✅ **CONTENT-COMPLETE** (Lean theorem proved; `sorryAx` only from
T-III-6-001's `exists_dual` — becomes fully axiom-clean when T-III-6-001 closes)
**Silverman**: III.6.2(e)
**Module**: `HasseWeil/DualIsogeny.lean` (`degree_isogDual` at line 100)
**Owner**: (existing)
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: C

## Depends on
- T-III-6-006 ([m]^ = [m], deg [m] = m²)
- T-III-6-003 (composition formula)

## Blocks
- T-III-6-009 (deg quadratic form)

## Statement (Silverman III.6.2(e))
For any nonzero isogeny `φ : E₁ → E₂`,
`deg φ̂ = deg φ`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

theorem Isogeny.dual_degree (φ : Isogeny E₁ E₂) (hφ : φ ≠ 0) :
    φ.dual.degree = φ.degree

end HasseWeil.EC
```

## Notes
- From `(deg φ)² = deg [deg φ] = deg(φ̂ ∘ φ) = deg φ̂ · deg φ`, divide.

## Progress log
- 2026-04-20 [worker-J audit] Lean theorem `degree_isogDual` (line 100)
  in `HasseWeil/DualIsogeny.lean` matches the acceptance criteria.
  Proof uses `isogDual_comp_self` + `Isogeny.comp_degree` + `mulByInt_degree`
  + `Nat.eq_of_mul_eq_mul_left`. Cascades from the single `sorry` in
  `exists_dual` (T-III-6-001). Status OPEN → PARTIAL.
- 2026-04-20 [worker-A] Re-audit: theorem is fully proved and closes the
  acceptance criteria. The cascading `sorryAx` comes SOLELY from
  `exists_dual` (T-III-6-001's responsibility). Status PARTIAL →
  CONTENT-COMPLETE (becomes fully axiom-clean when T-III-6-001 closes).
