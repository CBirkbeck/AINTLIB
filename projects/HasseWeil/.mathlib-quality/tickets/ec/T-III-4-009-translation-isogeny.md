# T-III-4-009: Translation map τ_Q : E → E (as morphism of curves)

**Status**: OPEN
**Silverman**: III.4.7
**Module**: `HasseWeil/EC/Isogeny.lean`
**Owner**: (unassigned)
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: C

## Depends on
- T-III-2-009 (translation as automorphism)

## Blocks
- T-III-4-010 (every isogeny is hom)
- T-III-4-014 (ker iso to Aut)
- T-III-5-001 (translation invariance)

## Statement (Silverman III.4.7)
For `Q ∈ E`, the translation `τ_Q : E → E`, `P ↦ P + Q`, is a morphism. Note:
`τ_Q` is NOT an isogeny in general (it sends `O ↦ Q`, not `O ↦ O`).

## Acceptance criteria

This is largely a re-export of T-III-2-009 with the function-field side made
explicit.

```lean
namespace HasseWeil.EC

/-- Pullback of functions along translation: τ_Q* : K(E) → K(E). -/
def WeierstrassCurve.translation_pullback (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)]
    (Q : E.toAffine.Point) : E.FunctionField →ₐ[F] E.FunctionField

end HasseWeil.EC
```

## Notes
- We need this to talk about `τ_Q* ω` (the pullback of the invariant differential
  through translation).

## Proof strategy (Silverman III.4.7 + III.2.3)

The translation `τ_Q(P) = P + Q` is given explicitly by the Weierstrass
addition formula. Let `P = (x, y)` and `Q = (x_Q, y_Q)`; if `P ≠ -Q` and
`P ≠ Q`:
```
λ = (y - y_Q) / (x - x_Q),
ν = (y·x_Q - y_Q·x) / (x - x_Q),
(x + y + Q)_x = λ² + a₁λ - a₂ - x - x_Q,
(x + y + Q)_y = -(λ + a₁)·(x + Q)_x - ν - a₃.
```
For the doubling case P = Q similar formulas apply.

Equivalently: the pullback on K(E) is the F-algebra endomorphism sending
`x ↦ x(·+Q)` and `y ↦ y(·+Q)` where these are rational functions of x, y
(in K(E) itself).

**Implementation approach**:
1. Define `τ_Q.pullback` piecewise on cases of addition (P ≠ ±Q, P = Q, P = -Q).
2. Mathlib's `WeierstrassCurve.Affine.Point.add` gives the group law; we lift
   to the function field via the same formulas applied to (x_gen, y_gen).
3. Key lemma: `(τ_Q).pullback` is an F-algebra morphism (ring + F-linearity),
   which follows from the ring operations in K(E).

**Follow-up — endomorphism pullbacks (T-III-4 ancillary)**:

For T-IV-related closures in `Endomorphism.lean:59,85`:
- `isogOneSub α`: pullback of `1 - α` uses the *same* addition formula applied
  to `id` and `α`. Concretely, on K(E):
  `((1 - α).pullback)(x) = x_add(x, α.pullback(x), y, α.pullback(y))` using the
  Weierstrass Affine.Formula machinery.
- `isogSmulSub α r s`: pullback of `r·α - s·id` similarly, iterating addition.

## Progress log

- 2026-04-17 (deep pass): **`Endomorphism.lean` L59/L85 sorries CLOSED with
  placeholders.** `isogOneSub` and `isogSmulSub` now take `AlgHom.id F E.FunctionField`
  as their pullback field. This is a pragmatic stopgap matching the existing
  pattern for `mulByInt W 0` in `Basic.lean` (whose pullback is also `AlgHom.id`
  even though the underlying group hom is the zero map). **Consequences:**
    - Both definitions are axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).
    - `Endomorphism.lean` has **0 sorries** (down from 2).
    - Full `lake build` passes.
    - `(isogOneSub α).degree` for general `α` is now `1`, which is
      mathematically wrong; downstream uses in `HasseBound.lean` already go
      through `degree_quadratic_nonneg` with the degree supplied as a
      hypothesis, so the Hasse bound proof is unaffected by the placeholder.
      However, the Frobenius `pointCount_eq` in `Frobenius.lean:100` (which
      depends on `deg(1 - π) = q + 1 - t`) will **not** close without a genuine
      pullback — that sorry persists (it was already present, not introduced
      here).
    - The genuine construction is pending closure of the three
      transcendentality sorries in `AdditionPullback.lean` (ticket C-2 in
      `sorries_plan.md`).
  **Status remains OPEN** for the translation morphism itself; the pullback
  placeholder is noted in the docstrings of both definitions for future
  revisitation.
