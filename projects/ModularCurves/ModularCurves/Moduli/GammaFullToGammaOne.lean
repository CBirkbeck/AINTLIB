/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.FullLevelGammaOne
import ModularCurves.Moduli.Representability

/-!
# The level-forgetting morphism `[Γ(N)] ⟶ [Γ₁(N)]` (WP-D1b)

`Y₁(N)` is known to be smooth and affine over the base
(`gammaOneNaive_representable`, axiom-verified, `ModularCurve/YOneTatePoint.lean`), while the
corresponding statement for `Y(N)` is still open (`YFull.exists_representing_smooth_affine`).
The route to closing it is to transport smoothness along a finite étale
`Y(N) ⟶ Y₁(N)`, and the first step is the morphism of moduli problems that induces it:
forget `Q`.

A `ModuliProblem` is a presheaf on `(EllObj R)ᵒᵖ`, so this is a natural transformation. Its
components are `(P, Q) ↦ P`; the substance is that `P` really is a `Γ₁(N)`-structure, which
is the counting argument `isNaiveGammaOne_of_isNaiveFullLevel` (WP-D1a). Naturality is free:
both problems transport level structures by `EllHom.pullSection`.

The `N`-invertibility hypothesis enters only through WP-D1a's per-geometric-point form
`(N : k) ≠ 0`; `natCast_ne_zero_of_geometricPoint` derives it from `IsUnit (N : R)`.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace ModularCurves

variable {R : CommRingCat.{u}}

/-- `N` invertible in the base ring stays invertible in the residue field of any geometric
point of any `Ell/R`-object. -/
theorem natCast_ne_zero_of_geometricPoint (X : EllObj R) (N : ℕ) (hinv : IsUnit (N : R))
    (k : Type u) [Field k] (t : Spec (CommRingCat.of k) ⟶ X.base) : (N : k) ≠ 0 := by
  have h0 : NIsInvertible (Spec R) N := by
    rw [NIsInvertible]
    have h := hinv.map (Scheme.ΓSpecIso R).inv.hom
    rwa [map_natCast] at h
  exact (nIsInvertible_spec_iff k N).mp (h0.of_hom (t ≫ X.structMap))

/-- **(WP-D1b)** The level-forgetting morphism of moduli problems `[Γ(N)] ⟶ [Γ₁(N)]`:
`(P, Q) ↦ P`.

Well-definedness is WP-D1a — a naive full level-`N` structure has both members of exact
order `N` at every geometric point, by counting against `|E[N](k̄)| = N²`. Naturality holds
because both problems act on level structures by `EllHom.pullSection`. -/
noncomputable def gammaFullToGammaOne (N : ℕ) [NeZero N] (hinv : IsUnit (N : R)) :
    gammaFullNaiveProblem R N ⟶ gammaOneNaiveProblem R N where
  app X := ↾fun PQ => ⟨PQ.1.1,
    EllipticCurve.isNaiveGammaOne_of_isNaiveFullLevel X.unop.curve
      (fun k _ _ t => natCast_ne_zero_of_geometricPoint X.unop N hinv k t) PQ.2⟩
  naturality X Y f := by
    ext PQ
    rfl

@[simp] theorem gammaFullToGammaOne_app_val (N : ℕ) [NeZero N] (hinv : IsUnit (N : R))
    (X : (EllObj R)ᵒᵖ) (PQ : (gammaFullNaiveProblem R N).obj X) :
    ((gammaFullToGammaOne N hinv).app X PQ).1 = PQ.1.1 := rfl

end ModularCurves
