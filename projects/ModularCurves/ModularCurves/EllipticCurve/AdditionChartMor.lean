/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AdditionChartAway

/-!
# The addition laws as scheme morphisms on each piece (T-W7.0c-c5β, β3 geometric half)

`Spec` of the β3 piece-homs, composed with the chart immersion `Proj.awayι`, gives honest scheme
morphisms into the projective model:

  `addOnYPieceMor : Spec (Localization.Away (lawTwoTriple W i j k)) ⟶ projModel W`

together with its `over R` specification
`addOnYPieceMor ≫ projModelπ W = Spec.map (algebraMap R _)`.
The source is the basic open `D(t_k)` of `Spec (biChartRing W i j)`, which β1's `chartPieceIso`
identifies with the `(i,j)` chart-product open of `E ×_R E`. Ranging over `k`, these are the local
pieces of `addOnY`; the union of the three `D(t_k)` is the regularity open of law 2 on the piece
(the complement of its exceptional divisor — where the triple vanishes identically), i.e. the
piece's contribution to `blOpenY`.
-/

open MvPolynomial ModularCurves AlgebraicGeometry CategoryTheory

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (i j k : Fin 3)
variable [IsJacobsonRing R] [IsDomain (biChartRing W i j)]

/-- **(β3)** The `k`-th piece of `addOnY`: a morphism from the locus where the law-2 triple's
`k`-th coordinate is invertible, into the projective model. -/
noncomputable def addOnYPieceMor (hΔ : IsUnit W.Δ) :
    Spec (CommRingCat.of (Localization.Away (lawTwoTriple W i j k))) ⟶ projModel W :=
  Spec.map (CommRingCat.ofHom (addOnYPieceHom W i j k hΔ).toRingHom) ≫ chartι W k

/-- **(β3)** The `k`-th piece of `addOnZ` (mathlib's addition law). -/
noncomputable def addOnZPieceMor (hΔ : IsUnit W.Δ) :
    Spec (CommRingCat.of (Localization.Away (lawOneTriple W i j k))) ⟶ projModel W :=
  Spec.map (CommRingCat.ofHom (addOnZPieceHom W i j k hΔ).toRingHom) ≫ chartι W k

/-- The `k`-th piece of `addOnY` lies over the base: it is a morphism of `R`-schemes. -/
lemma addOnYPieceMor_projModelπ (hΔ : IsUnit W.Δ) :
    addOnYPieceMor W i j k hΔ ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away (lawTwoTriple W i j k)))) := by
  rw [addOnYPieceMor, Category.assoc, chartι_projModelπ, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  exact (addOnYPieceHom W i j k hΔ).comp_algebraMap

/-- The `k`-th piece of `addOnZ` lies over the base. -/
lemma addOnZPieceMor_projModelπ (hΔ : IsUnit W.Δ) :
    addOnZPieceMor W i j k hΔ ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away (lawOneTriple W i j k)))) := by
  rw [addOnZPieceMor, Category.assoc, chartι_projModelπ, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  exact (addOnZPieceHom W i j k hΔ).comp_algebraMap

end WeierstrassCurve.Projective
