/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.RingTheory.FiniteType
import ModularCurves.EllipticCurve.ModelVCEquivariance

/-!
# Uniqueness of the pointed group structure on a projective Weierstrass model ([U-MODEL])

Over a **noetherian** base, a pointed group structure on a proper flat O-connected scheme
is unique (GIT Cor 6.4 applied to the identity — `abelEnrichment_unique_of_isLocallyNoetherian`
territory). This file removes the noetherian hypothesis **for the projective model**
`projModel W` by spreading out: `R` is the filtered colimit of its finitely generated
`ℤ`-subalgebras (each noetherian), `W` and the two multiplications descend to a stage
(morphism-descent into the finitely presented model — Stacks 01ZC, mathlib
`AffineTransitionLimit`), the group axioms descend (equality-descent), noetherian rigidity
applies at the stage, and the equality base-changes back up.

The keystone consumed by the records-level canonicity primitive (K3): every pointed group
structure on `modelOver W` has the T-G4 multiplication `mulOver W`.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj WeierstrassCurve

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

variable (R : Type u) [CommRing R]

/-! ## The finitely generated `ℤ`-subalgebra system -/

/-- The directed poset of finitely generated `ℤ`-subalgebras of `R`. -/
def fgSys : Type u := {S : Subalgebra ℤ R // S.FG}

namespace fgSys

instance : Preorder (fgSys R) where
  le S T := S.1 ≤ T.1
  le_refl _ := le_refl _
  le_trans _ _ _ h h' := le_trans h h'

instance : IsDirected (fgSys R) (· ≤ ·) where
  directed S T := ⟨⟨S.1 ⊔ T.1, S.2.sup T.2⟩,
    show S.1 ≤ S.1 ⊔ T.1 from le_sup_left, show T.1 ≤ S.1 ⊔ T.1 from le_sup_right⟩

instance : Nonempty (fgSys R) := ⟨⟨⊥, ⟨∅, by simp⟩⟩⟩

noncomputable instance (S : fgSys R) : CommRing ↥S.1 := inferInstance

/-- Each stage is a noetherian ring. -/
instance (S : fgSys R) : IsNoetherianRing ↥S.1 := by
  haveI : Algebra.FiniteType ℤ ↥S.1 := (Subalgebra.fg_iff_finiteType S.1).mp S.2
  exact Algebra.FiniteType.isNoetherianRing ℤ ↥S.1

/-- The stage functor: each finitely generated subalgebra as a `CommRingCat` object. -/
noncomputable def diagram : fgSys R ⥤ CommRingCat.{u} where
  obj S := CommRingCat.of ↥S.1
  map {S T} h := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h)).toRingHom
  map_id S := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    rfl
  map_comp {S T U} f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    rfl

/-- The colimit cocone with apex `R`: the subalgebra inclusions. -/
noncomputable def cocone : Cocone (diagram R) :=
  ⟨CommRingCat.of R,
    ⟨fun S => CommRingCat.ofHom (S.1.val.toRingHom), fun {S T} h => by
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      rfl⟩⟩

/-- `R` is the filtered colimit of its finitely generated `ℤ`-subalgebras. -/
noncomputable def isColimit : IsColimit (cocone R) := by
  haveI : ReflectsColimit (diagram R) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    refine ⟨⟨Algebra.adjoin ℤ {x}, ⟨({x} : Finset R),
      congrArg (Algebra.adjoin ℤ) (Finset.coe_singleton x)⟩⟩,
      ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩, ?_⟩
    rfl
  · intro S x y h
    refine ⟨S, 𝟙 S, ?_⟩
    have hxy : (show ↥S.1 from x) = (show ↥S.1 from y) := Subtype.ext h
    exact congrArg ((diagram R ⋙ forget CommRingCat).map (𝟙 S)) hxy

/-! ## The `Spec` cofiltered system -/

/-- The stage system under `Spec`: a cofiltered diagram of affine schemes with affine
transition maps. -/
noncomputable def specDiagram : (fgSys R)ᵒᵖ ⥤ Scheme.{u} :=
  (diagram R).op ⋙ Scheme.Spec

instance (S : (fgSys R)ᵒᵖ) : IsAffine ((specDiagram R).obj S) :=
  inferInstanceAs (IsAffine (Spec _))

instance {S T : (fgSys R)ᵒᵖ} (f : S ⟶ T) : IsAffineHom ((specDiagram R).map f) :=
  isAffineHom_of_isAffine _

instance (S : (fgSys R)ᵒᵖ) : CompactSpace ((specDiagram R).obj S) := by
  have : IsAffine ((specDiagram R).obj S) := inferInstance
  infer_instance

instance (S : (fgSys R)ᵒᵖ) : QuasiSeparatedSpace ((specDiagram R).obj S) := by
  have : IsAffine ((specDiagram R).obj S) := inferInstance
  infer_instance

/-- The limit cone with apex `Spec R`. -/
noncomputable def specCone : Cone (specDiagram R) :=
  Scheme.Spec.mapCone (cocone R).op

noncomputable def specIsLimit : IsLimit (specCone R) := by
  haveI : PreservesLimitsOfSize.{u, u} Scheme.Spec.{u} :=
    ΓSpec.adjunction.rightAdjoint_preservesLimits
  exact isLimitOfPreserves Scheme.Spec (isColimit R).op

end fgSys

/-! ## K2 roadmap (Y1-CLOSER, boarded v10.141)

Remaining steps to `modelGrpObj_unique`:
1. **W-descent**: `S₀ := adjoin ℤ {a₁,a₂,a₃,a₄,a₆, Δ⁻¹}` (FG), `W₀` over `↥S₀` with
   `W₀.map val = W` and `[W₀.IsElliptic]`.
2. **Sliced system**: `Over.conePost`/`Over.isLimitConePost` at the index `op ⟨S₀⟩` turn
   `specCone/specIsLimit` into a limit cone in `Over (Spec ↥S₀)` with apex
   `Spec R --Spec.map val→ Spec ↥S₀`.
3. **Base-changed systems**: `isLimitOfPreserves (Over.pullback g ⋙ Over.forget _)` of the
   sliced limit, at `g := projModelπ W₀` (the projModel system) and at
   `g :=` the model-square structure (the square system); comparison isos to the
   `projModel (W-at-T)`-spellings via `isPullback_projModelBaseChangeOf` (+ a pasting iso
   for the square).
4. **μ-descent**: `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` at the square
   system into `projModel W₀` (lfp), then `IsPullback.lift` back to a stage multiplication.
5. **Axiom descent**: each group axiom + the unit-pin is an equality of morphisms from
   limit apexes into lfp targets — `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`
   at a further stage.
6. **Stage rigidity**: assemble the stage `GrpObj`, apply the K1-noetherian pattern
   (`isMonHom_left_of_one_comp_eq'` at the pointed `𝟙`) against `modelGrpObj`, conclude
   `μ_T = mulOver`, base-change back up with `mulModelHom_map`.
-/

end ModularCurves
