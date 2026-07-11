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

/-! ## Descending the curve to the first stage -/

section WDescent

variable {R} (W : WeierstrassCurve R) [W.IsElliptic]

/-- The first stage: the coefficients and `Δ⁻¹` generate a finitely generated subalgebra. -/
noncomputable def wStage : fgSys R :=
  ⟨Algebra.adjoin ℤ {W.a₁, W.a₂, W.a₃, W.a₄, W.a₆, ↑W.isUnit_Δ.unit⁻¹},
   Subalgebra.fg_def.mpr ⟨_, Set.toFinite _, rfl⟩⟩

/-- Membership of the six generators. -/
theorem wStage_mem (x : R)
    (hx : x ∈ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆, ↑W.isUnit_Δ.unit⁻¹} : Set R)) :
    x ∈ (wStage W).1 :=
  Algebra.subset_adjoin hx

/-- The curve at the first stage. -/
noncomputable def wZero : WeierstrassCurve ↥(wStage W).1 :=
  ⟨⟨W.a₁, wStage_mem W _ (by simp)⟩, ⟨W.a₂, wStage_mem W _ (by simp)⟩,
   ⟨W.a₃, wStage_mem W _ (by simp)⟩, ⟨W.a₄, wStage_mem W _ (by simp)⟩,
   ⟨W.a₆, wStage_mem W _ (by simp)⟩⟩

/-- The stage curve maps to `W` under the inclusion. -/
theorem wZero_map : (wZero W).map (wStage W).1.val.toRingHom = W := by
  ext <;> rfl

instance : (wZero W).IsElliptic := by
  constructor
  have hval : (wStage W).1.val.toRingHom (wZero W).Δ = W.Δ := by
    rw [← WeierstrassCurve.map_Δ, wZero_map]
  have hmul : (wZero W).Δ * ⟨↑W.isUnit_Δ.unit⁻¹, wStage_mem W _ (by simp)⟩ = 1 := by
    have hinj : Function.Injective (wStage W).1.val.toRingHom := Subtype.val_injective
    apply hinj
    rw [map_mul, hval, map_one]
    show W.Δ * ↑W.isUnit_Δ.unit⁻¹ = 1
    rw [IsUnit.mul_val_inv]
  exact ⟨⟨(wZero W).Δ, _, hmul, (mul_comm _ _).trans hmul⟩, rfl⟩

end WDescent

/-! ## The sliced limit and base-changed systems -/

section Sliced

attribute [local instance] IsCofiltered.isConnected

variable {R} (W : WeierstrassCurve R) [W.IsElliptic]

/-- The first-stage index in the opposite category. -/
noncomputable def wStageOp : (fgSys R)ᵒᵖ := Opposite.op (wStage W)

/-- The sliced stage system: a limit cone in `Over (Spec ↥(wStage W).1)` with apex
`Spec R` (over the inclusion). -/
noncomputable def slicedCone : Cone (Over.post (X := wStageOp W) (fgSys.specDiagram R)) :=
  (Over.conePost (fgSys.specDiagram R) (wStageOp W)).obj (fgSys.specCone R)

noncomputable def slicedIsLimit : IsLimit (slicedCone W) :=
  Over.isLimitConePost _ (fgSys.specIsLimit R)

variable {X : Scheme.{u}} (g : X ⟶ (fgSys.specDiagram R).obj (wStageOp W))

/-- The base-changed stage system along `g`, with apex `pullback g (Spec.map val)`
(as schemes). -/
noncomputable def bcCone : Cone (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
    Over.pullback g ⋙ Over.forget X) :=
  (Over.pullback g ⋙ Over.forget X).mapCone (slicedCone W)

noncomputable def bcIsLimit : IsLimit (bcCone W g) := by
  haveI : IsCofiltered (Over (wStageOp W)) := inferInstance
  haveI : PreservesLimitsOfSize.{u, u} (Over.pullback g) :=
    (Over.mapPullbackAdj g).rightAdjoint_preservesLimits
  exact isLimitOfPreserves (Over.pullback g ⋙ Over.forget X) (slicedIsLimit W)

end Sliced

/-! ## The square base-change pullback -/

section Square

variable {R} (W : WeierstrassCurve R) [W.IsElliptic]

/-- Shorthand: the base-change pullback square of the model along the first-stage
inclusion. -/
noncomputable def wPB : IsPullback
    (projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W))
    (projModelπ W) (projModelπ (wZero W))
    (Spec.map (CommRingCat.ofHom (wStage W).1.val.toRingHom)) :=
  isPullback_projModelBaseChangeOf _ (wZero W) W (wZero_map W)

/-- The base-change square of fibre squares: the square-level comparison morphism is a
pullback over the stage inclusion. -/
theorem hfst : pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W
    (wZero_map W) ≫ Limits.pullback.fst (projModelπ (wZero W)) (projModelπ (wZero W)) =
    Limits.pullback.fst (projModelπ W) (projModelπ W) ≫
      projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) :=
  Limits.pullback.lift_fst _ _ _

theorem hsnd : pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W
    (wZero_map W) ≫ Limits.pullback.snd (projModelπ (wZero W)) (projModelπ (wZero W)) =
    Limits.pullback.snd (projModelπ W) (projModelπ W) ≫
      projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) :=
  Limits.pullback.lift_snd _ _ _

noncomputable def sqIsPullback : IsPullback
    (pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W))
    (pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W)
    (pullback.fst (projModelπ (wZero W)) (projModelπ (wZero W)) ≫ projModelπ (wZero W))
    (Spec.map (CommRingCat.ofHom (wStage W).1.val.toRingHom)) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk ?_ ?_ ?_ ?_ ?_)
  · -- commutativity of the comparison square
    calc pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) ≫
          Limits.pullback.fst (projModelπ (wZero W)) (projModelπ (wZero W)) ≫
            projModelπ (wZero W)
        = (pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) ≫
            Limits.pullback.fst (projModelπ (wZero W)) (projModelπ (wZero W))) ≫
            projModelπ (wZero W) := (Category.assoc _ _ _).symm
      _ = (Limits.pullback.fst (projModelπ W) (projModelπ W) ≫
            projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)) ≫
            projModelπ (wZero W) := by rw [hfst W]
      _ = Limits.pullback.fst (projModelπ W) (projModelπ W) ≫
            (projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) ≫
              projModelπ (wZero W)) := Category.assoc _ _ _
      _ = Limits.pullback.fst (projModelπ W) (projModelπ W) ≫
            (projModelπ W ≫ Spec.map (CommRingCat.ofHom (wStage W).1.val.toRingHom)) := by
          rw [(wPB W).w]
      _ = (Limits.pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W) ≫
            Spec.map (CommRingCat.ofHom (wStage W).1.val.toRingHom) :=
          (Category.assoc _ _ _).symm
  · -- the lift
    intro s
    exact Limits.pullback.lift
      ((wPB W).lift (s.fst ≫ Limits.pullback.fst _ _) s.snd (by
        rw [Category.assoc]; exact s.condition))
      ((wPB W).lift (s.fst ≫ Limits.pullback.snd _ _) s.snd (by
        rw [Category.assoc, ← Limits.pullback.condition]
        exact s.condition))
      (by rw [(wPB W).lift_snd, (wPB W).lift_snd])
  · -- fst-compat
    intro s
    change _ ≫ pullbackMapBaseChangeOf _ _ _ (wZero_map W) = _
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst W, ← Category.assoc, Limits.pullback.lift_fst,
        (wPB W).lift_fst]
    · rw [Category.assoc, hsnd W, ← Category.assoc, Limits.pullback.lift_snd,
        (wPB W).lift_fst]
  · -- snd-compat
    intro s
    exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ projModelπ W) (Limits.pullback.lift_fst _ _ _)).trans
        ((wPB W).lift_snd _ _ _)
  · -- uniqueness
    intro s m h1 h2
    have h1' : m ≫ pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W
        (wZero_map W) = s.fst := h1
    refine Limits.pullback.hom_ext (f := projModelπ W) (g := projModelπ W) ?_ ?_
    · rw [Limits.pullback.lift_fst]
      refine (wPB W).hom_ext ?_ ?_
      · exact (Category.assoc _ _ _).trans <|
          (congrArg (m ≫ ·) (hfst W).symm).trans <|
          (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ Limits.pullback.fst (projModelπ (wZero W)) (projModelπ (wZero W)))
            h1').trans ((wPB W).lift_fst _ _ _).symm
      · exact (Category.assoc _ _ _).trans <| h2.trans ((wPB W).lift_snd _ _ _).symm
    · rw [Limits.pullback.lift_snd]
      refine (wPB W).hom_ext ?_ ?_
      · exact (Category.assoc _ _ _).trans <|
          (congrArg (m ≫ ·) (hsnd W).symm).trans <|
          (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ Limits.pullback.snd (projModelπ (wZero W)) (projModelπ (wZero W)))
            h1').trans ((wPB W).lift_fst _ _ _).symm
      · exact (Category.assoc _ _ _).trans <|
          (congrArg (m ≫ ·) (Limits.pullback.condition (f := projModelπ W)
            (g := projModelπ W)).symm).trans <|
          (Category.assoc _ _ _).symm.trans <| h2.trans ((wPB W).lift_snd _ _ _).symm

end Square

end ModularCurves
