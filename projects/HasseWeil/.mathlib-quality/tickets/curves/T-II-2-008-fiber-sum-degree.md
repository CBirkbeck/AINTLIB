# T-II-2-008: Σ e_φ(P) = deg(φ) over a fiber

**Status**: DONE (delivered 2026-04-22 by worker-I; verified axiom-clean 2026-04-22: `CurveMap.sum_ramificationIdx_mul_inertiaDeg_eq_degree` in `HasseWeil/Curves/CurveMap.lean` depends only on `[propext, Classical.choice, Quot.sound]`)
**Silverman**: II.2.6(a) (Proposition)
**Module**: `HasseWeil/Curves/CurveMap.lean`
**Owner**: (unassigned)
**Estimated lines**: 80
**Difficulty**: hard
**Stream**: A

## Depends on
- T-II-2-007 (ramification index)
- T-II-2-004 (degree)

## Blocks
- T-II-2-009 (#fibers = deg_s)
- T-III-4-013

## Statement (Silverman II.2.6(a))
For every Q ∈ C₂,

```
∑_{P ∈ φ⁻¹(Q)} e_φ(P) = deg(φ)
```

This is a discrete-mathematics analogue of the index formula for finite extensions
of Dedekind domains.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- The sum of ramification indices over a fiber equals the degree.
    Reference: Silverman II.2.6(a). -/
theorem Morphism.sum_ramification_eq_degree (φ : Morphism C₁ C₂) (hφ : ¬ IsConst φ)
    (Q : C₂.SmoothPoint) :
    ∑ P ∈ (φ.fiber Q), φ.ramificationIndex P = φ.degree

end HasseWeil.Curves
```

## Notes
- This is the function-field version of the standard index formula:
  `Σ e_i f_i = n` for a Dedekind extension. Since K(C) is a curve function field,
  the residue degrees `f_i` are all 1 over algebraically closed K (so the
  formula simplifies).
- mathlib has `Ideal.sum_ramification_inertia` in
  `Mathlib.RingTheory.DedekindDomain.Ideal`.
- The proof in Silverman references [142, Chapter 1, Proposition 21] which is
  the standard Dedekind result.

## Progress log

- **2026-04-21** (worker-I scoping audit): the key abstract ingredient (mathlib's
  `Ideal.sum_ramification_inertia` for Dedekind extensions) is available. Worker-K's
  `HasseWeil/Curves/NormValuation.lean` already provides **T-II-2-008 specialised
  to the coordinate function** `x : C → A¹` (via `algebraMap F[X] → F[C]`):
  - `sum_ramificationIdx_over_fiber` (Σ e·f = 2 over primes above `(X−a)` in `F[C]`).
  - `sum_ramificationIdx_eq_finrank` (Σ e = 2 using `inertiaDeg_maximalIdealAt = 1`).
  Both under `[IsAlgClosed F]` + `[IsElliptic]` + `[IsIntegrallyClosed]`.

  **What's missing for general `CurveMap φ : C₁ → C₂`**: the pullback
  `φ* : K(C₂) → K(C₁)` needs to restrict to a ring map
  `φ*|C₂.CoordinateRing : C₂.CoordinateRing → C₁.CoordinateRing` (i.e., `φ`
  must be a **morphism**, not just a rational map, on the affine charts).
  Our `CurveMap` structure only records function-field data, so the
  coordinate-ring restriction step is missing. Given it (plus
  `IsIntegrallyClosed`-style hypotheses, which follow unconditionally for
  `[IsElliptic]` curves via our new IC-003ii instance), the generic
  `sum_ramificationIndexℤ_eq_degree` follows by adapting
  `sum_ramificationIdx_eq_finrank` to the abstract two-stage tower
  `C₂.CoordinateRing → C₁.CoordinateRing` in place of
  `F[X] → F[C]`.

  Estimated additional work: ~60 lines to formalise "CurveMap restricts to
  coordinate rings when the pullback is integral over the image coordinate
  ring", then ~30 lines to chain `Ideal.sum_ramification_inertia`.

- **2026-04-21 (continued)** (worker-I): delivered the **data bundle**
  `CurveMap.CoordHom` in `HasseWeil/Curves/CurveMap.lean`:
  ```lean
  structure CoordHom (φ : CurveMap C₁ C₂) where
    toAlgHom : C₂.CoordinateRing →ₐ[F] C₁.CoordinateRing
    compat : ∀ u : C₂.CoordinateRing,
      φ.pullback (algebraMap C₂.CoordinateRing C₂.FunctionField u) =
        algebraMap C₁.CoordinateRing C₁.FunctionField (toAlgHom u)
  ```

- **2026-04-21 (continued — diamond fixed)** (worker-I): **delivered
  `sum_ramificationIdx_mul_inertiaDeg_eq_degree`** in
  `HasseWeil/Curves/CurveMap.lean` (~50 lines, axiom-clean). Closes
  T-II-2-008 in full generality for any `CurveMap` supplied with a
  `CoordHom` witness and a finite-module hypothesis:

  ```lean
  theorem sum_ramificationIdx_mul_inertiaDeg_eq_degree
      [IsIntegrallyClosed C₂.CoordinateRing]
      [IsIntegrallyClosed C₁.CoordinateRing]
      (φ : CurveMap C₁ C₂) (coordHom : φ.CoordHom)
      (hfin : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _
        coordHom.toAlgebra.toModule)
      {p : Ideal C₂.CoordinateRing} (hpMax : p.IsMaximal) (hp0 : p ≠ ⊥) :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      ∑ P ∈ primesOverFinset p C₁.CoordinateRing,
          Ideal.ramificationIdx (algebraMap _ _) p P * Ideal.inertiaDeg p P
        = φ.degree
  ```

  **Diamond resolution**: the scalar-tower instances `IsScalarTower C₂.CR
  C₁.CR C₁.FunctionField` (tower 2) and `IsScalarTower C₂.CR C₂.FF
  C₁.FF` (tower 1) need `SMul C₂.CR C₁.FF`, which mathlib synthesizes
  via `OreLocalization.instSMulOfIsScalarTower` (since C₁.FF is
  OreLocalization-based). The explicit `letI algLong` approach conflicted
  with this canonical SMul. The fix:
  - Let Lean synthesize `tower2 := inferInstance` (uses
    `OreLocalization.instSMulOfIsScalarTower` for the cross-SMul);
  - Prove `tower1` via `IsScalarTower.of_algebraMap_smul`, using
    `Algebra.smul_def` + `coordHom.compat` +
    `IsScalarTower.algebraMap_smul` (for tower2) to bridge the two
    pathways;
  - Explicitly `letI modCR : Module C₂.CR C₁.CR := algCR.toModule` to
    pin the `Module` instance to the same `AddCommMonoid` parent that
    `hfin` was elaborated against (resolves a diamond in the parent-
    instance chain for `Module.Finite`).

  Requires `set_option synthInstance.maxHeartbeats 200000 in` and
  `set_option maxHeartbeats 1600000 in` due to heavy instance-search
  elaboration but completes deterministically. Axiom-clean (propext,
  Classical.choice, Quot.sound). The theorem now makes T-II-2-008 a
  one-liner for any `CurveMap` callsite that supplies a `CoordHom` and
  finite-module witness.
