/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.InvariantDifferential
import ModularCurves.Moduli.EllCategory

/-!
# Base change of `ω`-bases over the elliptic-curve category (T-OM-B7 ★★)

**(T-E-OMEGA, `/develop --decompose` 2026-07-13, STREAM-OMEGA;
decomposition: `.mathlib-quality/decomposition-omega-r1.md`.)**

The `(Ell/R)`-functoriality of the `S`-bases of `ω_{E/S}`: along a morphism of
`EllObj R` (a cartesian pointed square), a basis of the target's invariant
differential transports to a basis of the source's — `omegaBasisMap`, contravariantly
functorial. This is what makes the ω-rigidified moduli problems of KM Ch. 2/4
(T-E12 `(E, ω)`, T-E14 Legendre) statable as `ModuliProblem R` functors:
`P(X) := {…, b ∈ OmegaBasis X} , P(φ) := omegaBasisMap φ`.

Route: the pulled-back atlas cocycle of the target and the source's own atlas cocycle
are compared chart-against-transported-chart (`LocalPresentation.transport` along the
square + `transVC`/`transUnit` + `Scheme.exists_unit_glue`), producing
`UnitCocycle.Compat` data; `Compat.sectionsEquiv` transports sections and bases.
Functoriality is uniqueness of glued units + `transVC_trans` through the composite
transported presentation.
-/

universe u

open AlgebraicGeometry CategoryTheory Scheme

namespace ModularCurves

variable {R : CommRingCat.{u}}

/-- **(T-OM-B7)** The comparison data between the source's own ω-cocycle and the
pullback of the target's ω-cocycle along a morphism of `Ell/R` (a cartesian pointed
square): mixed-overlap units glued from the transition units of
own-chart-vs-transported-chart comparisons. -/
noncomputable def omegaCompat {X X' : EllObj R} (φ : X' ⟶ X) :
    (omegaCocycle X'.curve.toEllipticCurveGeom).Compat
      ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle φ.baseHom) := by
  sorry

/-- **(T-OM-B7 ★★)** Base change of `ω`-bases along a morphism of `Ell/R`: pull the
compatible unit family back componentwise, then transport through the cocycle
comparison. This is the datum that makes the ω-rigidified moduli problems
(T-E12/T-E14) functors on `(Ell/R)ᵒᵖ`. -/
noncomputable def omegaBasisMap {X X' : EllObj R} (φ : X' ⟶ X) :
    OmegaBasis X.curve.toEllipticCurveGeom → OmegaBasis X'.curve.toEllipticCurveGeom := by
  sorry

/-- **(T-OM-B7)** `omegaBasisMap` at the identity is the identity. -/
theorem omegaBasisMap_id (X : EllObj R) :
    omegaBasisMap (𝟙 X) = id := by
  sorry

/-- **(T-OM-B7)** `omegaBasisMap` is contravariantly functorial. -/
theorem omegaBasisMap_comp {X X' X'' : EllObj R} (φ : X'' ⟶ X') (ψ : X' ⟶ X) :
    omegaBasisMap (φ ≫ ψ) = omegaBasisMap φ ∘ omegaBasisMap ψ := by
  sorry

/-- **(T-OM-B7)** `omegaBasisMap` is equivariant for the global-unit actions (through
the section map of the base morphism) — with `negVC_u`, the inversion morphism scales
bases by `−1`, KM 4.6.2's `{±1}`-action. -/
theorem omegaBasisMap_smul {X X' : EllObj R} (φ : X' ⟶ X) (g : Γ(X.base, ⊤)ˣ)
    (b : OmegaBasis X.curve.toEllipticCurveGeom) :
    omegaBasisMap φ (g • b) =
      Units.map (sectionsMapLE (V := ⊤) (V' := ⊤) φ.baseHom (by simp)).toMonoidHom g •
        omegaBasisMap φ b := by
  sorry

end ModularCurves
