# T-III-1-002: Invariant differential ω = dx/(2y + a₁x + a₃)

**Status**: DONE
**Silverman**: III.1
**Module**: `HasseWeil/InvariantDifferential.lean` → `HasseWeil/EC/InvariantDiff.lean`
**Owner**: (existing)
**Estimated lines**: 0 (existing)
**Difficulty**: easy
**Stream**: B/E

## Depends on
- T-III-1-001 (Weierstrass equation)

## Blocks
- T-III-1-009 (div(ω) = 0)
- T-III-5-001 (translation invariance)

## Statement (Silverman III.1)
For a Weierstrass curve `E : y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`, the
**invariant differential** is
`ω = dx / (2y + a₁ x + a₃) = dy / (3x² + 2 a₂ x + a₄ - a₁ y) ∈ Ω_E`.

## Acceptance criteria

Already implemented in `HasseWeil/InvariantDifferential.lean`. Confirm:
```lean
#check HasseWeil.invariantDifferential
```

## Notes
- The two formulas are equal because of the relation
  `(2y + a₁x + a₃) dy = (3x² + 2a₂x + a₄ - a₁y) dx + ε` from differentiating the
  Weierstrass equation.
- `(2y + a₁x + a₃)` is exactly the partial of the Weierstrass polynomial w.r.t. `y`.

## Progress log
- 2026-04-08 [auto] marked DONE — exists in HasseWeil/InvariantDifferential.lean
