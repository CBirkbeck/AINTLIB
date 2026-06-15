# T-III-4-002: deg, deg_s, deg_i, separable predicate for isogenies

**Status**: DONE (existing — refactor needed)
**Silverman**: III.4 def
**Module**: `HasseWeil/SeparableDegree.lean` + `HasseWeil/Isogeny.lean` → `HasseWeil/EC/Isogeny.lean`
**Owner**: (existing)
**Estimated lines**: 0 (existing)
**Difficulty**: trivial
**Stream**: C

## Depends on
- T-III-4-001 (Isogeny)
- T-II-2-004 (degree types for curve maps)

## Blocks
- T-III-4-010..017
- T-III-5-004..005

## Statement (Silverman III.4 def)
For an isogeny `φ : E₁ → E₂`,
- `deg φ := [K̄(E₁) : φ*K̄(E₂)]` (with `deg 0 := 0`)
- `deg_s φ` separable degree, `deg_i φ` inseparable degree
- `φ.IsSeparable ↔ deg_s φ = deg φ`
- `φ.IsInseparable ↔ deg_s φ = 1`

## Acceptance criteria

Existing in `HasseWeil/SeparableDegree.lean`. Confirm:
```lean
#check HasseWeil.Isogeny.degree
#check HasseWeil.Isogeny.sepDegree
#check HasseWeil.Isogeny.IsSeparable
```

## Progress log
- 2026-04-08 [auto] marked DONE — refactoring tracked under T-MIGRATE-009
