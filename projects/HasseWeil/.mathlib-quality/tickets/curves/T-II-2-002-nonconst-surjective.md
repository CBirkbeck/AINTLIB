# T-II-2-002: Nonconstant morphism is surjective

**Status**: OPEN
**Silverman**: II.2.3 (Theorem)
**Module**: `HasseWeil/Curves/Maps.lean`
**Owner**: (unassigned)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: A

## Depends on
- T-II-2-001 (rational map ⇒ morphism)

## Blocks
- T-II-2-003 (curves ↔ extensions functor)

## Statement (Silverman II.2.3)
Let `φ : C₁ → C₂` be a morphism of curves. Then `φ` is either constant or
surjective.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- A morphism of smooth curves is either constant or surjective.
    Reference: Silverman II.2.3. -/
theorem morphism_const_or_surjective (C₁ C₂ : SmoothPlaneCurve F)
    (φ : Morphism C₁ C₂) :
    IsConst φ ∨ Function.Surjective φ.toFun

end HasseWeil.Curves
```

## Notes
- The image of a complete (= projective) curve under a morphism is closed and
  irreducible. If it's not all of `C₂`, it must be a finite set of points; but
  the curve is irreducible so it's a single point.
- This is a closed-image / closed-map argument; mathlib has facts like
  `IsClosedMap.continuous` etc. via `Scheme.IsClosed`.

## Progress log

- **2026-04-21** (worker-I scoping audit): for the **Hasse bound chain over
  `F_q`**, this ticket is NOT on the critical path:
  `kernel_finite_of_point_finite` in `HasseWeil/EC/IsogenyKernel.lean:154` is
  already unconditional under `[Finite W₁.Point]`, which is implied by
  `[Fintype W.toAffine.Point]` at the call site of
  `hasse_bound_of_all_witnesses`. The ticket remains open as foundational
  curve theory (Silverman II.2.3 is a classical theorem), but its
  downstream use in the Hasse bound chain is already discharged by the
  finite-group fact `Fintype.Point → Finite.kernel`.

  **General-curve delivery** still requires a `somePointMap` on `CurveMap`
  (morphism-level structure not yet in the framework — see T-II-2-008
  progress log for the missing coordinate-ring restriction step). Once
  that lands, the surjectivity argument becomes the closed-map + image-
  irreducible argument from the notes.
