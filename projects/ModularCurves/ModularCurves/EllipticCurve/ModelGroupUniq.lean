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

variable {R} {U : Type u} [CommRing U] (f : U →+* R)
  (W₀ : WeierstrassCurve U) (W : WeierstrassCurve R) (h : W₀.map f = W)
  [W₀.IsElliptic] [W.IsElliptic]

/-- Shorthand: the base-change pullback square of the model. -/
noncomputable def wPB : IsPullback
    (projModelBaseChangeOf f W₀ W h)
    (projModelπ W) (projModelπ W₀)
    (Spec.map (CommRingCat.ofHom f)) :=
  isPullback_projModelBaseChangeOf f W₀ W h

/-- The base-change square of fibre squares: the square-level comparison morphism is a
pullback over the stage inclusion. -/
theorem hfst : pullbackMapBaseChangeOf f W₀ W h ≫
    Limits.pullback.fst (projModelπ W₀) (projModelπ W₀) =
    Limits.pullback.fst (projModelπ W) (projModelπ W) ≫
      projModelBaseChangeOf f W₀ W h :=
  Limits.pullback.lift_fst _ _ _

theorem hsnd : pullbackMapBaseChangeOf f W₀ W h ≫
    Limits.pullback.snd (projModelπ W₀) (projModelπ W₀) =
    Limits.pullback.snd (projModelπ W) (projModelπ W) ≫
      projModelBaseChangeOf f W₀ W h :=
  Limits.pullback.lift_snd _ _ _

noncomputable def sqIsPullback : IsPullback
    (pullbackMapBaseChangeOf f W₀ W h)
    (pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W)
    (pullback.fst (projModelπ W₀) (projModelπ W₀) ≫ projModelπ W₀)
    (Spec.map (CommRingCat.ofHom f)) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk ?_ ?_ ?_ ?_ ?_)
  · -- commutativity of the comparison square
    calc pullbackMapBaseChangeOf f W₀ W h ≫
          Limits.pullback.fst (projModelπ W₀) (projModelπ W₀) ≫
            projModelπ W₀
        = (pullbackMapBaseChangeOf f W₀ W h ≫
            Limits.pullback.fst (projModelπ W₀) (projModelπ W₀)) ≫
            projModelπ W₀ := (Category.assoc _ _ _).symm
      _ = (Limits.pullback.fst (projModelπ W) (projModelπ W) ≫
            projModelBaseChangeOf f W₀ W h) ≫
            projModelπ W₀ := by rw [hfst f W₀ W h]
      _ = Limits.pullback.fst (projModelπ W) (projModelπ W) ≫
            (projModelBaseChangeOf f W₀ W h ≫
              projModelπ W₀) := Category.assoc _ _ _
      _ = Limits.pullback.fst (projModelπ W) (projModelπ W) ≫
            (projModelπ W ≫ Spec.map (CommRingCat.ofHom f)) := by
          rw [(wPB f W₀ W h).w]
      _ = (Limits.pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W) ≫
            Spec.map (CommRingCat.ofHom f) :=
          (Category.assoc _ _ _).symm
  · -- the lift
    intro s
    exact Limits.pullback.lift
      ((wPB f W₀ W h).lift (s.fst ≫ Limits.pullback.fst _ _) s.snd (by
        rw [Category.assoc]; exact s.condition))
      ((wPB f W₀ W h).lift (s.fst ≫ Limits.pullback.snd _ _) s.snd (by
        rw [Category.assoc, ← Limits.pullback.condition]
        exact s.condition))
      (by rw [(wPB f W₀ W h).lift_snd, (wPB f W₀ W h).lift_snd])
  · -- fst-compat
    intro s
    change _ ≫ pullbackMapBaseChangeOf _ _ _ h = _
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst f W₀ W h, ← Category.assoc, Limits.pullback.lift_fst,
        (wPB f W₀ W h).lift_fst]
    · rw [Category.assoc, hsnd f W₀ W h, ← Category.assoc, Limits.pullback.lift_snd,
        (wPB f W₀ W h).lift_fst]
  · -- snd-compat
    intro s
    exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ projModelπ W) (Limits.pullback.lift_fst _ _ _)).trans
        ((wPB f W₀ W h).lift_snd _ _ _)
  · -- uniqueness
    intro s m h1 h2
    have h1' : m ≫ pullbackMapBaseChangeOf f W₀ W h = s.fst := h1
    refine Limits.pullback.hom_ext (f := projModelπ W) (g := projModelπ W) ?_ ?_
    · rw [Limits.pullback.lift_fst]
      refine (wPB f W₀ W h).hom_ext ?_ ?_
      · exact (Category.assoc _ _ _).trans <|
          (congrArg (m ≫ ·) (hfst f W₀ W h).symm).trans <|
          (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ Limits.pullback.fst (projModelπ W₀) (projModelπ W₀))
            h1').trans ((wPB f W₀ W h).lift_fst _ _ _).symm
      · exact (Category.assoc _ _ _).trans <| h2.trans ((wPB f W₀ W h).lift_snd _ _ _).symm
    · rw [Limits.pullback.lift_snd]
      refine (wPB f W₀ W h).hom_ext ?_ ?_
      · exact (Category.assoc _ _ _).trans <|
          (congrArg (m ≫ ·) (hsnd f W₀ W h).symm).trans <|
          (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ Limits.pullback.snd (projModelπ W₀) (projModelπ W₀))
            h1').trans ((wPB f W₀ W h).lift_fst _ _ _).symm
      · exact (Category.assoc _ _ _).trans <|
          (congrArg (m ≫ ·) (Limits.pullback.condition (f := projModelπ W)
            (g := projModelπ W)).symm).trans <|
          (Category.assoc _ _ _).symm.trans <| h2.trans ((wPB f W₀ W h).lift_snd _ _ _).symm

end Square

/-! ## The μ-descent -/

section MuDescent

attribute [local instance] IsCofiltered.isConnected

variable {R} (W : WeierstrassCurve R) [W.IsElliptic]

/-- The structure morphism of the first-stage model square. -/
noncomputable def sqStruct :
    Limits.pullback (projModelπ (wZero W)) (projModelπ (wZero W)) ⟶
      (fgSys.specDiagram R).obj (wStageOp W) :=
  Limits.pullback.fst _ _ ≫ projModelπ (wZero W)

/-- The structural transformation of the base-changed square system. -/
noncomputable def sqT : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
    Over.pullback (sqStruct W) ⋙ Over.forget _) ⟶
    (Functor.const (Over (wStageOp W))).obj ((fgSys.specDiagram R).obj (wStageOp W)) where
  app T := ((Over.pullback (sqStruct W)).obj
    ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T)).hom ≫ sqStruct W
  naturality {T T'} φ := by
    have hw := Over.w ((Over.pullback (sqStruct W)).map
      ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).map φ))
    show _ ≫ _ ≫ sqStruct W = (_ ≫ sqStruct W) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc]
    exact congrArg (· ≫ sqStruct W) hw

example : LocallyOfFinitePresentation (projModelπ (wZero W)) := by
  haveI : SmoothOfRelativeDimension 1 (projModelπ (wZero W)) := projModel_smooth (wZero W)
  haveI hsm : Smooth (projModelπ (wZero W)) :=
    SmoothOfRelativeDimension.smooth (n := 1) (f := projModelπ (wZero W))
  infer_instance

/-- The comparison isomorphism: the `R`-square is the base-changed-square-system's apex. -/
noncomputable def sqComparison :
    Limits.pullback (projModelπ W) (projModelπ W) ≅ (bcCone W (sqStruct W)).pt :=
  (sqIsPullback (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).flip.isoPullback

/-- The transition maps of the base-changed square system are pullbacks of the (affine)
`Spec` transitions. -/
theorem bcSq_transition_isPullback {T T' : Over (wStageOp W)} (φ : T ⟶ T') :
    IsPullback
      ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback (sqStruct W) ⋙ Over.forget _).map φ)
      (Limits.pullback.fst _ _) (Limits.pullback.fst _ _)
      ((fgSys.specDiagram R).map φ.left) := by
  refine IsPullback.of_right ?_ ?_
    ((IsPullback.of_hasPullback ((Over.post (X := wStageOp W)
      (fgSys.specDiagram R)).obj T').hom (sqStruct W)).flip)
  · have hsnd' : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback (sqStruct W) ⋙ Over.forget _).map φ ≫ Limits.pullback.snd _ _ =
        Limits.pullback.snd _ _ :=
      Limits.pullback.lift_snd _ _ _
    have hw : (fgSys.specDiagram R).map φ.left ≫
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T').hom =
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom :=
      Over.w ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).map φ)
    rw [hsnd']
    convert (IsPullback.of_hasPullback ((Over.post (X := wStageOp W)
      (fgSys.specDiagram R)).obj T).hom (sqStruct W)).flip using 2
    all_goals first | rfl | exact hw
  · exact Limits.pullback.lift_fst _ _ _

instance bcSq_transition_affine {T T' : Over (wStageOp W)} (φ : T ⟶ T') :
    IsAffineHom ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _).map φ) :=
 by
  haveI : IsAffine ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).left :=
    inferInstanceAs (IsAffine ((fgSys.specDiagram R).obj T.left))
  haveI : IsAffine ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T').left :=
    inferInstanceAs (IsAffine ((fgSys.specDiagram R).obj T'.left))
  exact MorphismProperty.of_isPullback (bcSq_transition_isPullback W φ).flip
    (isAffineHom_of_isAffine _)

instance sqStruct_proper : IsProper (sqStruct W) := by
  haveI : IsProper (Limits.pullback.fst (projModelπ (wZero W)) (projModelπ (wZero W))) :=
    MorphismProperty.pullback_fst _ _ (projModelπ_isProper (wZero W))
  exact MorphismProperty.comp_mem _ _ _ inferInstance (projModelπ_isProper (wZero W))

instance bcSq_obj_compact (T : Over (wStageOp W)) :
    CompactSpace ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _).obj T) := by
  haveI : UniversallyClosed (sqStruct W) := inferInstance
  haveI : QuasiCompact (sqStruct W) := inferInstance
  haveI : CompactSpace ((Over.post (X := wStageOp W)
      (fgSys.specDiagram R)).obj T).left :=
    inferInstanceAs (CompactSpace ((fgSys.specDiagram R).obj T.left))
  exact inferInstanceAs (CompactSpace ↑(Limits.pullback ((Over.post (X := wStageOp W)
    (fgSys.specDiagram R)).obj T).hom (sqStruct W)))

instance bcSq_obj_qsep (T : Over (wStageOp W)) :
    QuasiSeparatedSpace ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _).obj T) := by
  haveI : IsSeparated (sqStruct W) := inferInstance
  haveI : QuasiSeparated (sqStruct W) := inferInstance
  haveI : QuasiSeparatedSpace ((Over.post (X := wStageOp W)
      (fgSys.specDiagram R)).obj T).left :=
    inferInstanceAs (QuasiSeparatedSpace ((fgSys.specDiagram R).obj T.left))
  exact @quasiSeparatedSpace_of_quasiSeparated _ _
    (Limits.pullback.fst ((Over.post (X := wStageOp W)
      (fgSys.specDiagram R)).obj T).hom (sqStruct W))
    inferInstance (MorphismProperty.pullback_fst _ _ inferInstance)

set_option maxSynthPendingDepth 3 in
/-- **(K2 step 5, μ-descent)** Any multiplication-shaped morphism on the `R`-square
descends to a finitely generated stage, compatibly over the first stage. -/
theorem mu_descends (μl : Limits.pullback (projModelπ W) (projModelπ W) ⟶ projModel W)
    (hμπ : μl ≫ projModelπ W = Limits.pullback.fst _ _ ≫ projModelπ W) :
    ∃ (T : Over (wStageOp W))
      (g' : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback (sqStruct W) ⋙ Over.forget _).obj T ⟶ projModel (wZero W)),
      (bcCone W (sqStruct W)).π.app T ≫ g' =
        (sqComparison W).inv ≫ μl ≫
          projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) ∧
      g' ≫ projModelπ (wZero W) = (sqT W).app T := by
  haveI : SmoothOfRelativeDimension 1 (projModelπ (wZero W)) := projModel_smooth (wZero W)
  haveI : Smooth (projModelπ (wZero W)) :=
    SmoothOfRelativeDimension.smooth (n := 1) (f := projModelπ (wZero W))
  haveI hlfp : LocallyOfFinitePresentation (projModelπ (wZero W)) := by infer_instance
  refine @Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (Over (wStageOp W)) _ _ _
    (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _)
    (sqT W) (projModelπ (wZero W)) (bcCone W (sqStruct W)) (bcIsLimit W (sqStruct W))
    inferInstance hlfp (fun {i j} φ => bcSq_transition_affine W φ)
    (fun T => bcSq_obj_compact W T) (fun T => bcSq_obj_qsep W T)
    ((sqComparison W).inv ≫ μl ≫
      projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)) ?_
  ext T
  show (bcCone W (sqStruct W)).π.app T ≫ (sqT W).app T = _
  -- the cone leg is an `Over SQ₀`-morphism: its structure square collapses the left side
  have hw : (bcCone W (sqStruct W)).π.app T ≫ ((Over.pullback (sqStruct W)).obj
      ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T)).hom =
      Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) :=
    Over.w ((Over.pullback (sqStruct W)).map ((slicedCone W).π.app T))
  have hLHS : (bcCone W (sqStruct W)).π.app T ≫ (sqT W).app T =
      Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) ≫ sqStruct W := by
    show (bcCone W (sqStruct W)).π.app T ≫ (_ ≫ sqStruct W) = _
    rw [← Category.assoc, hw]
    rfl
  rw [hLHS]
  -- the right side collapses along the comparison and the two structure squares
  have hisoinv : (sqComparison W).inv ≫
      (Limits.pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W) =
      Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) :=
    (sqIsPullback (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).flip.isoPullback_inv_fst
  have hRHS : ((sqComparison W).inv ≫ μl ≫
      projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)) ≫
      projModelπ (wZero W) =
      Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) ≫ ((slicedCone W).pt).hom := by
    rw [Category.assoc, Category.assoc,
      (wPB (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).w, ← Category.assoc μl,
      hμπ, Category.assoc, ← Category.assoc, ← Category.assoc]
    rw [show ((sqComparison W).inv ≫ Limits.pullback.fst (projModelπ W) (projModelπ W)) ≫
        projModelπ W = Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) from
      (Category.assoc _ _ _).trans hisoinv]
    rfl
  show _ = ((sqComparison W).inv ≫ μl ≫ projModelBaseChangeOf _ _ _ _) ≫
    projModelπ (wZero W)
  rw [hRHS, ← Limits.pullback.condition]

end MuDescent

end ModularCurves
