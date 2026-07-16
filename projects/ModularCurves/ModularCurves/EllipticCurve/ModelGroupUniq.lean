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
theorem wPB : IsPullback
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

theorem sqIsPullback : IsPullback
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

variable {R} (W : WeierstrassCurve R) [W.IsElliptic] {X : Scheme.{u}}

/-- The structure morphism of the first-stage model square. -/
noncomputable def sqStruct :
    Limits.pullback (projModelπ (wZero W)) (projModelπ (wZero W)) ⟶
      (fgSys.specDiagram R).obj (wStageOp W) :=
  Limits.pullback.fst _ _ ≫ projModelπ (wZero W)

set_option backward.isDefEq.respectTransparency false in
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
    all_goals first | rfl | exact hw | exact iff_of_eq (congrArg _ hw)
  · exact Limits.pullback.lift_fst _ _ _

/-- Generic transition square for the base-changed system along any `g`. -/
theorem bc_transition_isPullback (g : X ⟶ (fgSys.specDiagram R).obj (wStageOp W))
    {T T' : Over (wStageOp W)} (φ : T ⟶ T') :
    IsPullback
      ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback g ⋙ Over.forget _).map φ)
      (Limits.pullback.fst _ _) (Limits.pullback.fst _ _)
      ((fgSys.specDiagram R).map φ.left) := by
  refine IsPullback.of_right ?_ ?_
    ((IsPullback.of_hasPullback ((Over.post (X := wStageOp W)
      (fgSys.specDiagram R)).obj T').hom g).flip)
  · have hsnd' : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback g ⋙ Over.forget _).map φ ≫ Limits.pullback.snd _ _ =
        Limits.pullback.snd _ _ :=
      Limits.pullback.lift_snd _ _ _
    have hw : (fgSys.specDiagram R).map φ.left ≫
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T').hom =
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom :=
      Over.w ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).map φ)
    rw [hsnd']
    convert (IsPullback.of_hasPullback ((Over.post (X := wStageOp W)
      (fgSys.specDiagram R)).obj T).hom g).flip using 2
    all_goals first | rfl | exact hw | exact iff_of_eq (congrArg _ hw)
  · exact Limits.pullback.lift_fst _ _ _

instance bc_transition_affine (g : X ⟶ (fgSys.specDiagram R).obj (wStageOp W))
    {T T' : Over (wStageOp W)} (φ : T ⟶ T') :
    IsAffineHom ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback g ⋙ Over.forget _).map φ) := by
  haveI : IsAffine ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).left :=
    inferInstanceAs (IsAffine ((fgSys.specDiagram R).obj T.left))
  haveI : IsAffine ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T').left :=
    inferInstanceAs (IsAffine ((fgSys.specDiagram R).obj T'.left))
  exact MorphismProperty.of_isPullback (bc_transition_isPullback W g φ).flip
    (isAffineHom_of_isAffine _)

instance bc_obj_compact (g : X ⟶ (fgSys.specDiagram R).obj (wStageOp W))
    [QuasiCompact g] (T : Over (wStageOp W)) :
    CompactSpace ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback g ⋙ Over.forget _).obj T) := by
  haveI : CompactSpace ((Over.post (X := wStageOp W)
      (fgSys.specDiagram R)).obj T).left :=
    inferInstanceAs (CompactSpace ((fgSys.specDiagram R).obj T.left))
  exact inferInstanceAs (CompactSpace ↑(Limits.pullback ((Over.post (X := wStageOp W)
    (fgSys.specDiagram R)).obj T).hom g))

set_option backward.isDefEq.respectTransparency false in
instance bc_obj_qsep (g : X ⟶ (fgSys.specDiagram R).obj (wStageOp W))
    [QuasiSeparated g] (T : Over (wStageOp W)) :
    QuasiSeparatedSpace ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback g ⋙ Over.forget _).obj T) := by
  haveI : QuasiSeparatedSpace ((Over.post (X := wStageOp W)
      (fgSys.specDiagram R)).obj T).left :=
    inferInstanceAs (QuasiSeparatedSpace ((fgSys.specDiagram R).obj T.left))
  exact @quasiSeparatedSpace_of_quasiSeparated _ _
    (Limits.pullback.fst ((Over.post (X := wStageOp W)
      (fgSys.specDiagram R)).obj T).hom g)
    inferInstance inferInstance

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
  haveI : IsProper (projModelπ (wZero W)) := projModelπ_isProper (wZero W)
  haveI : IsProper (Limits.pullback.fst (projModelπ (wZero W)) (projModelπ (wZero W))) :=
    inferInstance
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

set_option backward.isDefEq.respectTransparency false in
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
    inferInstance inferInstance

set_option maxSynthPendingDepth 3 in
set_option backward.isDefEq.respectTransparency false in
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

/-- Generic morphism descent along the base-changed stage system. -/
theorem hom_descends (g : X ⟶ (fgSys.specDiagram R).obj (wStageOp W))
    (hqc : QuasiCompact g) (hqs : QuasiSeparated g)
    {Y : Scheme.{u}} (f : Y ⟶ (fgSys.specDiagram R).obj (wStageOp W))
    (hlfp : LocallyOfFinitePresentation f)
    (t : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback g ⋙ Over.forget _) ⟶
      (Functor.const (Over (wStageOp W))).obj ((fgSys.specDiagram R).obj (wStageOp W)))
    (a : (bcCone W g).pt ⟶ Y)
    (ha : (bcCone W g).π ≫ t = (Functor.const _).map (a ≫ f)) :
    ∃ (T : Over (wStageOp W)) (g' : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback g ⋙ Over.forget _).obj T ⟶ Y),
      (bcCone W g).π.app T ≫ g' = a ∧ g' ≫ f = t.app T := by
  haveI := hqc
  haveI := hqs
  haveI := hlfp
  exact @Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (Over (wStageOp W)) _ _ _
    (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback g ⋙ Over.forget _) t f (bcCone W g) (bcIsLimit W g)
    inferInstance hlfp (fun {i j} φ => bc_transition_affine W g φ)
    (fun T => bc_obj_compact W g T) (fun T => bc_obj_qsep W g T) a ha

/-- Generic equality descent along the base-changed stage system. -/
theorem eq_descends (g : X ⟶ (fgSys.specDiagram R).obj (wStageOp W))
    (hqc : QuasiCompact g) (hqs : QuasiSeparated g)
    {Y : Scheme.{u}} (f : Y ⟶ (fgSys.specDiagram R).obj (wStageOp W))
    (hlft : LocallyOfFiniteType f)
    (t : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback g ⋙ Over.forget _) ⟶
      (Functor.const (Over (wStageOp W))).obj ((fgSys.specDiagram R).obj (wStageOp W)))
    {T : Over (wStageOp W)}
    (u v : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback g ⋙ Over.forget _).obj T ⟶ Y)
    (hu : t.app T = u ≫ f) (hv : t.app T = v ≫ f)
    (huv : (bcCone W g).π.app T ≫ u = (bcCone W g).π.app T ≫ v) :
    ∃ (T' : Over (wStageOp W)) (ψ : T' ⟶ T),
      (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback g ⋙ Over.forget _).map ψ ≫ u =
      (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback g ⋙ Over.forget _).map ψ ≫ v := by
  haveI := hqc
  haveI := hqs
  exact @Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (Over (wStageOp W)) _ _ _
    (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback g ⋙ Over.forget _) t f (bcCone W g) (bcIsLimit W g)
    (fun T => bc_obj_compact W g T) hlft inferInstance
    (fun {i j} φ => bc_transition_affine W g φ) T u v hu hv huv

set_option backward.isDefEq.respectTransparency false in
/-- The structural transformation of any base-changed stage system. -/
noncomputable def bcT (g : X ⟶ (fgSys.specDiagram R).obj (wStageOp W)) :
    (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback g ⋙ Over.forget _) ⟶
    (Functor.const (Over (wStageOp W))).obj ((fgSys.specDiagram R).obj (wStageOp W)) where
  app T := ((Over.pullback g).obj
    ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T)).hom ≫ g
  naturality {T T'} φ := by
    have hw := Over.w ((Over.pullback g).map
      ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).map φ))
    show _ ≫ _ ≫ g = (_ ≫ g) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc]
    exact congrArg (· ≫ g) hw

end MuDescent

/-! ## Stage vocabulary -/

section Stage

variable {R} (W : WeierstrassCurve R) [W.IsElliptic]

/-- The subalgebra of a stage index. -/
noncomputable def stageAlg (T : Over (wStageOp W)) : Subalgebra ℤ R := T.left.unop.1

/-- The inclusion of the first stage into a stage. -/
theorem wStage_le_stage (T : Over (wStageOp W)) : (wStage W).1 ≤ stageAlg W T :=
  leOfHom T.hom.unop

/-- The Weierstrass curve at a stage. -/
noncomputable def stageW (T : Over (wStageOp W)) : WeierstrassCurve ↥(stageAlg W T) :=
  (wZero W).map (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom

/-- The stage curve maps to `W` under the stage inclusion. -/
theorem stageW_map (T : Over (wStageOp W)) :
    (stageW W T).map (stageAlg W T).val.toRingHom = W := by
  show ((wZero W).map _).map _ = W
  rw [WeierstrassCurve.map_map]
  rw [show (stageAlg W T).val.toRingHom.comp
      (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom =
      (wStage W).1.val.toRingHom from rfl]
  exact wZero_map W

/-- The stage curve restricts the first-stage curve. -/
theorem stageW_map₀ (T : Over (wStageOp W)) :
    (wZero W).map (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom = stageW W T :=
  rfl

instance (T : Over (wStageOp W)) : (stageW W T).IsElliptic := by
  constructor
  have h : (stageW W T).Δ =
      (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom (wZero W).Δ := by
    show ((wZero W).map _).Δ = _
    rw [WeierstrassCurve.map_Δ]
  rw [h]
  exact (wZero W).isUnit_Δ.map _

end Stage

/-! ## Stage comparison isomorphisms -/

section StageIso

variable {R} (W : WeierstrassCurve R) [W.IsElliptic]

/-- The stage model against the base-changed system object (at `g := projModelπ (wZero W)`). -/
theorem stageModelPB (T : Over (wStageOp W)) : IsPullback
    (projModelBaseChangeOf (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom
      (wZero W) (stageW W T) rfl)
    (projModelπ (stageW W T)) (projModelπ (wZero W))
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom)) :=
  isPullback_projModelBaseChangeOf _ (wZero W) (stageW W T) rfl

/-- The stage square against the base-changed square system object. -/
theorem stageSqPB (T : Over (wStageOp W)) : IsPullback
    (pullbackMapBaseChangeOf (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom
      (wZero W) (stageW W T) rfl)
    (Limits.pullback.fst (projModelπ (stageW W T)) (projModelπ (stageW W T)) ≫
      projModelπ (stageW W T))
    (Limits.pullback.fst (projModelπ (wZero W)) (projModelπ (wZero W)) ≫
      projModelπ (wZero W))
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom)) :=
  sqIsPullback _ (wZero W) (stageW W T) rfl

end StageIso

/-! ## The inverse descent -/

section IotaDescent

attribute [local instance] IsCofiltered.isConnected

variable {R} (W : WeierstrassCurve R) [W.IsElliptic]

/-- The comparison isomorphism for the plain model system. -/
noncomputable def modelComparison :
    projModel W ≅ (bcCone W (projModelπ (wZero W))).pt :=
  (wPB (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).flip.isoPullback

set_option backward.isDefEq.respectTransparency false in
/-- **(K2, ι-descent)** Any endomorphism-shaped morphism of the model over `R` descends to
a finitely generated stage. -/
theorem iota_descends (il : projModel W ⟶ projModel W)
    (hiπ : il ≫ projModelπ W = projModelπ W) :
    ∃ (T : Over (wStageOp W))
      (i' : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).obj T ⟶ projModel (wZero W)),
      (bcCone W (projModelπ (wZero W))).π.app T ≫ i' =
        (modelComparison W).inv ≫ il ≫
          projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) ∧
      i' ≫ projModelπ (wZero W) = (bcT W (projModelπ (wZero W))).app T := by
  haveI : SmoothOfRelativeDimension 1 (projModelπ (wZero W)) := projModel_smooth (wZero W)
  haveI : Smooth (projModelπ (wZero W)) :=
    SmoothOfRelativeDimension.smooth (n := 1) (f := projModelπ (wZero W))
  haveI : IsProper (projModelπ (wZero W)) := projModelπ_isProper (wZero W)
  haveI : UniversallyClosed (projModelπ (wZero W)) := inferInstance
  haveI hqc : QuasiCompact (projModelπ (wZero W)) := by infer_instance
  haveI hqs : QuasiSeparated (projModelπ (wZero W)) := by infer_instance
  haveI hlfp : LocallyOfFinitePresentation (projModelπ (wZero W)) := by infer_instance
  refine hom_descends W (projModelπ (wZero W)) hqc hqs (projModelπ (wZero W)) hlfp
    (bcT W (projModelπ (wZero W)))
    ((modelComparison W).inv ≫ il ≫
      projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)) ?_
  ext T
  have hw : (bcCone W (projModelπ (wZero W))).π.app T ≫
      ((Over.pullback (projModelπ (wZero W))).obj
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T)).hom =
      Limits.pullback.snd ((slicedCone W).pt).hom (projModelπ (wZero W)) :=
    Over.w ((Over.pullback (projModelπ (wZero W))).map ((slicedCone W).π.app T))
  show (bcCone W (projModelπ (wZero W))).π.app T ≫
      (bcT W (projModelπ (wZero W))).app T =
    ((modelComparison W).inv ≫ il ≫ projModelBaseChangeOf (wStage W).1.val.toRingHom
      (wZero W) W (wZero_map W)) ≫ projModelπ (wZero W)
  have hLHS : (bcCone W (projModelπ (wZero W))).π.app T ≫
      (bcT W (projModelπ (wZero W))).app T =
      Limits.pullback.snd ((slicedCone W).pt).hom (projModelπ (wZero W)) ≫
        projModelπ (wZero W) :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ projModelπ (wZero W)) hw)
  have hRHS : ((modelComparison W).inv ≫ il ≫ projModelBaseChangeOf
      (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)) ≫ projModelπ (wZero W) =
      Limits.pullback.fst ((slicedCone W).pt).hom (projModelπ (wZero W)) ≫
        ((slicedCone W).pt).hom := by
    rw [Category.assoc, Category.assoc,
      (wPB (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).w, ← Category.assoc il,
      hiπ, ← Category.assoc]
    exact congrArg (· ≫ Spec.map (CommRingCat.ofHom (wStage W).1.val.toRingHom))
      ((wPB (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).flip.isoPullback_inv_fst)
  rw [hLHS, hRHS, Limits.pullback.condition]

end IotaDescent

/-! ## The difference morphism and its axis collapses (R-side) -/

section Difference

variable {R} (W : WeierstrassCurve R) [W.IsElliptic]

/-- The two axis inclusions of the model square. -/
noncomputable def axInclL : modelOver W ⟶ modelOver W ⊗ modelOver W :=
  lift (toUnit _ ≫ oneOver W) (𝟙 _)

noncomputable def axInclR : modelOver W ⟶ modelOver W ⊗ modelOver W :=
  lift (𝟙 _) (toUnit _ ≫ oneOver W)

/-- Any pointed group multiplication collapses the left axis to the identity. -/
theorem axInclL_mul (G : GrpObj (modelOver W))
    (hone : (letI := G; (η[modelOver W] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶
      modelOver W)) = oneOver W) :
    axInclL W ≫ (letI := G; (μ[modelOver W] : modelOver W ⊗ modelOver W ⟶ modelOver W)) =
      𝟙 (modelOver W) := by
  letI := G
  have hax : axInclL W = (λ_ (modelOver W)).inv ≫ (η[modelOver W] ▷ modelOver W) := by
    apply CartesianMonoidalCategory.hom_ext
    · show lift (toUnit (modelOver W) ≫ oneOver W) (𝟙 (modelOver W)) ≫ fst _ _ = _
      rw [lift_fst, Category.assoc, whiskerRight_fst, ← Category.assoc,
        show (λ_ (modelOver W)).inv ≫ fst _ _ = toUnit _ from toUnit_unique _ _, hone]
    · show lift (toUnit (modelOver W) ≫ oneOver W) (𝟙 (modelOver W)) ≫ snd _ _ = _
      rw [lift_snd, Category.assoc, whiskerRight_snd,
        show snd (𝟙_ (Over (Spec (CommRingCat.of R)))) (modelOver W) =
          (λ_ (modelOver W)).hom from (leftUnitor_hom _).symm, Iso.inv_hom_id]
  rw [hax, Category.assoc, MonObj.one_mul, Iso.inv_hom_id]

/-- Any pointed group multiplication collapses the right axis to the identity. -/
theorem axInclR_mul (G : GrpObj (modelOver W))
    (hone : (letI := G; (η[modelOver W] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶
      modelOver W)) = oneOver W) :
    axInclR W ≫ (letI := G; (μ[modelOver W] : modelOver W ⊗ modelOver W ⟶ modelOver W)) =
      𝟙 (modelOver W) := by
  letI := G
  have hax : axInclR W = (ρ_ (modelOver W)).inv ≫ (modelOver W ◁ η[modelOver W]) := by
    apply CartesianMonoidalCategory.hom_ext
    · show lift (𝟙 (modelOver W)) (toUnit (modelOver W) ≫ oneOver W) ≫ fst _ _ = _
      rw [lift_fst, Category.assoc, whiskerLeft_fst,
        show fst (modelOver W) (𝟙_ (Over (Spec (CommRingCat.of R)))) =
          (ρ_ (modelOver W)).hom from (rightUnitor_hom _).symm, Iso.inv_hom_id]
    · show lift (𝟙 (modelOver W)) (toUnit (modelOver W) ≫ oneOver W) ≫ snd _ _ = _
      rw [lift_snd, Category.assoc, whiskerLeft_snd, ← Category.assoc,
        show (ρ_ (modelOver W)).inv ≫ snd _ _ = toUnit _ from toUnit_unique _ _, hone]
  rw [hax, Category.assoc, MonObj.mul_one, Iso.inv_hom_id]

end Difference

/-! ## Axis base-change maps -/

section AxisBC

variable {R} (W : WeierstrassCurve R) [W.IsElliptic]

/-- The left axis of the first-stage model, scheme level. -/
noncomputable def axL₀ : projModel (wZero W) ⟶
    Limits.pullback (projModelπ (wZero W)) (projModelπ (wZero W)) :=
  (axInclL (wZero W)).left

theorem axL₀_sqStruct : axL₀ W ≫ sqStruct W = projModelπ (wZero W) := by
  have h1 : axL₀ W ≫ Limits.pullback.fst (projModelπ (wZero W)) (projModelπ (wZero W)) =
      (toUnit (modelOver (wZero W)) ≫ oneOver (wZero W)).left :=
    congrArg CommaMorphism.left
      (lift_fst (toUnit (modelOver (wZero W)) ≫ oneOver (wZero W)) (𝟙 _))
  have h2 : (toUnit (modelOver (wZero W)) ≫ oneOver (wZero W)).left ≫
      projModelπ (wZero W) = projModelπ (wZero W) :=
    Over.w (toUnit (modelOver (wZero W)) ≫ oneOver (wZero W))
  exact ((Category.assoc (axL₀ W)
      (Limits.pullback.fst (projModelπ (wZero W)) (projModelπ (wZero W)))
      (projModelπ (wZero W))).symm.trans
    (congrArg (· ≫ projModelπ (wZero W)) h1)).trans h2

set_option backward.isDefEq.respectTransparency false in
/-- The axis map between the base-changed systems, at a stage. -/
noncomputable def axBC (T : Over (wStageOp W)) :
    (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).obj T ⟶
    (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _).obj T :=
  Limits.pullback.map _ _ _ _ (𝟙 _) (axL₀ W) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, axL₀_sqStruct])

set_option backward.isDefEq.respectTransparency false in
/-- The apex-level axis map. -/
noncomputable def axApex :
    (bcCone W (projModelπ (wZero W))).pt ⟶ (bcCone W (sqStruct W)).pt :=
  Limits.pullback.map _ _ _ _ (𝟙 _) (axL₀ W) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, axL₀_sqStruct])

/-- The cross-cone square: the axis map intertwines the two cone legs. -/
theorem axBC_cone (T : Over (wStageOp W)) :
    (bcCone W (projModelπ (wZero W))).π.app T ≫ axBC W T =
      axApex W ≫ (bcCone W (sqStruct W)).π.app T := by
  refine Limits.pullback.hom_ext ?_ ?_
  · have h1 : axBC W T ≫ Limits.pullback.fst
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.fst _ _ ≫ 𝟙 _ := Limits.pullback.lift_fst _ _ _
    have h2 : (bcCone W (projModelπ (wZero W))).π.app T ≫ Limits.pullback.fst
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom
        (projModelπ (wZero W)) =
        Limits.pullback.fst ((slicedCone W).pt).hom (projModelπ (wZero W)) ≫
          ((slicedCone W).π.app T).left := Limits.pullback.lift_fst _ _ _
    have h3 : (bcCone W (sqStruct W)).π.app T ≫ Limits.pullback.fst
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) ≫
          ((slicedCone W).π.app T).left := Limits.pullback.lift_fst _ _ _
    have h4 : axApex W ≫ Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) =
        Limits.pullback.fst _ _ ≫ 𝟙 _ := Limits.pullback.lift_fst _ _ _
    exact (Category.assoc _ _ _).trans <|
      ((congrArg ((bcCone W (projModelπ (wZero W))).π.app T ≫ ·) h1).trans <|
        ((congrArg ((bcCone W (projModelπ (wZero W))).π.app T ≫ ·)
          (Category.comp_id _)).trans <|
          h2.trans <|
            ((congrArg (· ≫ ((slicedCone W).π.app T).left)
              ((Category.comp_id _).symm.trans h4.symm)).trans <|
              ((Category.assoc _ _ _).trans <|
                (congrArg (axApex W ≫ ·) h3.symm).trans <|
                  (Category.assoc _ _ _).symm))))
  · have h1 : axBC W T ≫ Limits.pullback.snd
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.snd _ _ ≫ axL₀ W := Limits.pullback.lift_snd _ _ _
    have hwM : (bcCone W (projModelπ (wZero W))).π.app T ≫
        Limits.pullback.snd ((Over.post (X := wStageOp W)
          (fgSys.specDiagram R)).obj T).hom (projModelπ (wZero W)) =
        Limits.pullback.snd ((slicedCone W).pt).hom (projModelπ (wZero W)) :=
      Over.w ((Over.pullback (projModelπ (wZero W))).map ((slicedCone W).π.app T))
    have hwSQ : (bcCone W (sqStruct W)).π.app T ≫
        Limits.pullback.snd ((Over.post (X := wStageOp W)
          (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) :=
      Over.w ((Over.pullback (sqStruct W)).map ((slicedCone W).π.app T))
    have h4 : axApex W ≫ Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) =
        Limits.pullback.snd _ _ ≫ axL₀ W := Limits.pullback.lift_snd _ _ _
    exact (Category.assoc _ _ _).trans <|
      (congrArg ((bcCone W (projModelπ (wZero W))).π.app T ≫ ·) h1).trans <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ axL₀ W) hwM).trans <|
      h4.symm.trans <|
      (congrArg (axApex W ≫ ·) hwSQ.symm).trans (Category.assoc _ _ _).symm

/-- Axis naturality under base change, scheme level. -/
theorem axNat : projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W
    (wZero_map W) ≫ axL₀ W =
    (axInclL W).left ≫ pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W
      (wZero_map W) := by
  refine Limits.pullback.hom_ext ?_ ?_
  · -- fst leg: both sides are the zero section after the base
    have hL1 : axL₀ W ≫ Limits.pullback.fst (projModelπ (wZero W)) (projModelπ (wZero W)) =
        (toUnit (modelOver (wZero W)) ≫ oneOver (wZero W)).left :=
      congrArg CommaMorphism.left
        (lift_fst (toUnit (modelOver (wZero W)) ≫ oneOver (wZero W)) (𝟙 _))
    have hR1 : (axInclL W).left ≫ Limits.pullback.fst (projModelπ W) (projModelπ W) =
        (toUnit (modelOver W) ≫ oneOver W).left :=
      congrArg CommaMorphism.left (lift_fst (toUnit (modelOver W) ≫ oneOver W) (𝟙 _))
    have hcompL : (toUnit (modelOver (wZero W)) ≫ oneOver (wZero W)).left =
        projModelπ (wZero W) ≫ projModelZero (wZero W) := by
      show (toUnit (modelOver (wZero W))).left ≫ (oneOver (wZero W)).left = _
      rw [oneOver_left]
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ projModelZero (wZero W)) (Over.w (toUnit (modelOver (wZero W)))))
    have hcompR : (toUnit (modelOver W) ≫ oneOver W).left =
        projModelπ W ≫ projModelZero W := by
      show (toUnit (modelOver W)).left ≫ (oneOver W).left = _
      rw [oneOver_left]
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ projModelZero W) (Over.w (toUnit (modelOver W))))
    calc (projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) ≫
            axL₀ W) ≫ Limits.pullback.fst _ _
        = projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) ≫
            (axL₀ W ≫ Limits.pullback.fst _ _) := Category.assoc _ _ _
      _ = projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) ≫
            (projModelπ (wZero W) ≫ projModelZero (wZero W)) := by rw [hL1, hcompL]
      _ = (projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) ≫
            projModelπ (wZero W)) ≫ projModelZero (wZero W) := (Category.assoc _ _ _).symm
      _ = (projModelπ W ≫ Spec.map (CommRingCat.ofHom (wStage W).1.val.toRingHom)) ≫
            projModelZero (wZero W) := by
          rw [(wPB (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).w]
      _ = projModelπ W ≫ (Spec.map (CommRingCat.ofHom (wStage W).1.val.toRingHom) ≫
            projModelZero (wZero W)) := Category.assoc _ _ _
      _ = projModelπ W ≫ (projModelZero W ≫
            projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)) := by
          rw [projModelZero_baseChangeOf]
      _ = (projModelπ W ≫ projModelZero W) ≫
            projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) :=
          (Category.assoc _ _ _).symm
      _ = (toUnit (modelOver W) ≫ oneOver W).left ≫
            projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) :=
          congrArg (· ≫ projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W
            (wZero_map W)) hcompR.symm
      _ = ((axInclL W).left ≫ Limits.pullback.fst (projModelπ W) (projModelπ W)) ≫
            projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) :=
          congrArg (· ≫ projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W
            (wZero_map W)) hR1.symm
      _ = (axInclL W).left ≫ (Limits.pullback.fst (projModelπ W) (projModelπ W) ≫
            projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)) :=
          Category.assoc _ _ _
      _ = (axInclL W).left ≫ (pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W)
            W (wZero_map W) ≫ Limits.pullback.fst (projModelπ (wZero W))
              (projModelπ (wZero W))) :=
          congrArg ((axInclL W).left ≫ ·)
            (hfst (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).symm
      _ = ((axInclL W).left ≫ pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W)
            W (wZero_map W)) ≫ Limits.pullback.fst _ _ := (Category.assoc _ _ _).symm
  · have hL2 : axL₀ W ≫ Limits.pullback.snd (projModelπ (wZero W)) (projModelπ (wZero W)) =
        𝟙 _ := congrArg CommaMorphism.left
          (lift_snd (toUnit (modelOver (wZero W)) ≫ oneOver (wZero W)) (𝟙 _))
    have hR2 : (axInclL W).left ≫ Limits.pullback.snd (projModelπ W) (projModelπ W) =
        𝟙 _ := congrArg CommaMorphism.left
          (lift_snd (toUnit (modelOver W) ≫ oneOver W) (𝟙 _))
    calc (projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) ≫
            axL₀ W) ≫ Limits.pullback.snd _ _
        = projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) ≫
            (axL₀ W ≫ Limits.pullback.snd _ _) := Category.assoc _ _ _
      _ = projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) := by
          rw [hL2, Category.comp_id]
      _ = (𝟙 ((modelOver W).left)) ≫ projModelBaseChangeOf (wStage W).1.val.toRingHom
            (wZero W) W (wZero_map W) := (Category.id_comp _).symm
      _ = ((axInclL W).left ≫ Limits.pullback.snd (projModelπ W) (projModelπ W)) ≫
            projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) :=
          congrArg (· ≫ projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W
            (wZero_map W)) hR2.symm
      _ = (axInclL W).left ≫ (Limits.pullback.snd (projModelπ W) (projModelπ W) ≫
            projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)) :=
          Category.assoc _ _ _
      _ = (axInclL W).left ≫ (pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W)
            W (wZero_map W) ≫ Limits.pullback.snd (projModelπ (wZero W))
              (projModelπ (wZero W))) :=
          congrArg ((axInclL W).left ≫ ·)
            (hsnd (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).symm
      _ = ((axInclL W).left ≫ pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W)
            W (wZero_map W)) ≫ Limits.pullback.snd _ _ := (Category.assoc _ _ _).symm

/-- The apex comparison square: the apex axis map corresponds to the `R`-level axis
through the two comparison isomorphisms. -/
theorem axApex_comparison :
    (modelComparison W).hom ≫ axApex W = (axInclL W).left ≫ (sqComparison W).hom := by
  refine Limits.pullback.hom_ext ?_ ?_
  · have h1 : axApex W ≫ Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) =
        Limits.pullback.fst _ _ ≫ 𝟙 _ := Limits.pullback.lift_fst _ _ _
    have h2 : (modelComparison W).hom ≫
        Limits.pullback.fst ((slicedCone W).pt).hom (projModelπ (wZero W)) =
        projModelπ W :=
      (wPB (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).flip.isoPullback_hom_fst
    have h3 : (sqComparison W).hom ≫
        Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) =
        Limits.pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W :=
      (sqIsPullback (wStage W).1.val.toRingHom (wZero W) W
        (wZero_map W)).flip.isoPullback_hom_fst
    have h4 : (axInclL W).left ≫ Limits.pullback.fst (projModelπ W) (projModelπ W) ≫
        projModelπ W = projModelπ W := by
      have h5 : (axInclL W).left ≫ Limits.pullback.fst (projModelπ W) (projModelπ W) =
          (toUnit (modelOver W) ≫ oneOver W).left :=
        congrArg CommaMorphism.left (lift_fst (toUnit (modelOver W) ≫ oneOver W) (𝟙 _))
      exact (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ projModelπ W) h5).trans
          (Over.w (toUnit (modelOver W) ≫ oneOver W))
    have hA : ((modelComparison W).hom ≫ axApex W) ≫
        Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) = projModelπ W := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((modelComparison W).hom ≫ ·) h1).trans ?_
      refine (congrArg ((modelComparison W).hom ≫ ·) (Category.comp_id _)).trans h2
    have hB : ((axInclL W).left ≫ (sqComparison W).hom) ≫
        Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) = projModelπ W := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((axInclL W).left ≫ ·) h3).trans h4
    exact hA.trans hB.symm
  · have h1 : axApex W ≫ Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) =
        Limits.pullback.snd _ _ ≫ axL₀ W := Limits.pullback.lift_snd _ _ _
    have h2 : (modelComparison W).hom ≫
        Limits.pullback.snd ((slicedCone W).pt).hom (projModelπ (wZero W)) =
        projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) :=
      (wPB (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).flip.isoPullback_hom_snd
    have h3 : (sqComparison W).hom ≫
        Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) =
        pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) :=
      (sqIsPullback (wStage W).1.val.toRingHom (wZero W) W
        (wZero_map W)).flip.isoPullback_hom_snd
    calc ((modelComparison W).hom ≫ axApex W) ≫
          Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W)
        = (modelComparison W).hom ≫ (axApex W ≫
            Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W)) :=
          Category.assoc _ _ _
      _ = (modelComparison W).hom ≫ (Limits.pullback.snd ((slicedCone W).pt).hom
            (projModelπ (wZero W)) ≫ axL₀ W) := congrArg ((modelComparison W).hom ≫ ·) h1
      _ = ((modelComparison W).hom ≫ Limits.pullback.snd ((slicedCone W).pt).hom
            (projModelπ (wZero W))) ≫ axL₀ W := (Category.assoc _ _ _).symm
      _ = projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) ≫
            axL₀ W := congrArg (· ≫ axL₀ W) h2
      _ = (axInclL W).left ≫ pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W)
            W (wZero_map W) := axNat W
      _ = (axInclL W).left ≫ ((sqComparison W).hom ≫
            Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W)) :=
          congrArg ((axInclL W).left ≫ ·) h3.symm
      _ = ((axInclL W).left ≫ (sqComparison W).hom) ≫
            Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) :=
          (Category.assoc _ _ _).symm

end AxisBC

/-! ## Generic axis naturality and the right-axis mirror -/

section AxisBCR

variable {R} {U : Type u} [CommRing U] (f : U →+* R)
  (W₀ : WeierstrassCurve U) (W : WeierstrassCurve R) (h : W₀.map f = W)
  [W₀.IsElliptic] [W.IsElliptic]

/-- Generic left-axis naturality under base change, scheme level. -/
theorem axNatL_of :
    projModelBaseChangeOf f W₀ W h ≫ (axInclL W₀).left =
    (axInclL W).left ≫ pullbackMapBaseChangeOf f W₀ W h := by
  refine Limits.pullback.hom_ext ?_ ?_
  · have hL1 : (axInclL W₀).left ≫ Limits.pullback.fst (projModelπ W₀) (projModelπ W₀) =
        (toUnit (modelOver W₀) ≫ oneOver W₀).left :=
      congrArg CommaMorphism.left (lift_fst (toUnit (modelOver W₀) ≫ oneOver W₀) (𝟙 _))
    have hR1 : (axInclL W).left ≫ Limits.pullback.fst (projModelπ W) (projModelπ W) =
        (toUnit (modelOver W) ≫ oneOver W).left :=
      congrArg CommaMorphism.left (lift_fst (toUnit (modelOver W) ≫ oneOver W) (𝟙 _))
    have hcompL : (toUnit (modelOver W₀) ≫ oneOver W₀).left =
        projModelπ W₀ ≫ projModelZero W₀ := by
      show (toUnit (modelOver W₀)).left ≫ (oneOver W₀).left = _
      rw [oneOver_left]
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ projModelZero W₀) (Over.w (toUnit (modelOver W₀))))
    have hcompR : (toUnit (modelOver W) ≫ oneOver W).left =
        projModelπ W ≫ projModelZero W := by
      show (toUnit (modelOver W)).left ≫ (oneOver W).left = _
      rw [oneOver_left]
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ projModelZero W) (Over.w (toUnit (modelOver W))))
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (projModelBaseChangeOf f W₀ W h ≫ ·) (hL1.trans hcompL)).trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ projModelZero W₀) (wPB f W₀ W h).w).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (projModelπ W ≫ ·)
      (projModelZero_baseChangeOf f W₀ W h).symm).trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ projModelBaseChangeOf f W₀ W h) hcompR.symm).trans ?_
    refine (congrArg (· ≫ projModelBaseChangeOf f W₀ W h) hR1.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((axInclL W).left ≫ ·) (hfst f W₀ W h).symm).trans ?_
    exact (Category.assoc _ _ _).symm
  · have hL2 : (axInclL W₀).left ≫ Limits.pullback.snd (projModelπ W₀) (projModelπ W₀) =
        𝟙 _ := congrArg CommaMorphism.left
          (lift_snd (toUnit (modelOver W₀) ≫ oneOver W₀) (𝟙 _))
    have hR2 : (axInclL W).left ≫ Limits.pullback.snd (projModelπ W) (projModelπ W) =
        𝟙 _ := congrArg CommaMorphism.left
          (lift_snd (toUnit (modelOver W) ≫ oneOver W) (𝟙 _))
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (projModelBaseChangeOf f W₀ W h ≫ ·) hL2).trans ?_
    refine (Category.comp_id _).trans ?_
    refine ((Category.id_comp _).symm).trans ?_
    refine (congrArg (· ≫ projModelBaseChangeOf f W₀ W h) hR2.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((axInclL W).left ≫ ·) (hsnd f W₀ W h).symm).trans ?_
    exact (Category.assoc _ _ _).symm

/-- Generic right-axis naturality under base change, scheme level. -/
theorem axNatR_of :
    projModelBaseChangeOf f W₀ W h ≫ (axInclR W₀).left =
    (axInclR W).left ≫ pullbackMapBaseChangeOf f W₀ W h := by
  refine Limits.pullback.hom_ext ?_ ?_
  · have hL2 : (axInclR W₀).left ≫ Limits.pullback.fst (projModelπ W₀) (projModelπ W₀) =
        𝟙 _ := congrArg CommaMorphism.left
          (lift_fst (𝟙 _) (toUnit (modelOver W₀) ≫ oneOver W₀))
    have hR2 : (axInclR W).left ≫ Limits.pullback.fst (projModelπ W) (projModelπ W) =
        𝟙 _ := congrArg CommaMorphism.left
          (lift_fst (𝟙 _) (toUnit (modelOver W) ≫ oneOver W))
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (projModelBaseChangeOf f W₀ W h ≫ ·) hL2).trans ?_
    refine (Category.comp_id _).trans ?_
    refine ((Category.id_comp _).symm).trans ?_
    refine (congrArg (· ≫ projModelBaseChangeOf f W₀ W h) hR2.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((axInclR W).left ≫ ·) (hfst f W₀ W h).symm).trans ?_
    exact (Category.assoc _ _ _).symm
  · have hL1 : (axInclR W₀).left ≫ Limits.pullback.snd (projModelπ W₀) (projModelπ W₀) =
        (toUnit (modelOver W₀) ≫ oneOver W₀).left :=
      congrArg CommaMorphism.left (lift_snd (𝟙 _) (toUnit (modelOver W₀) ≫ oneOver W₀))
    have hR1 : (axInclR W).left ≫ Limits.pullback.snd (projModelπ W) (projModelπ W) =
        (toUnit (modelOver W) ≫ oneOver W).left :=
      congrArg CommaMorphism.left (lift_snd (𝟙 _) (toUnit (modelOver W) ≫ oneOver W))
    have hcompL : (toUnit (modelOver W₀) ≫ oneOver W₀).left =
        projModelπ W₀ ≫ projModelZero W₀ := by
      show (toUnit (modelOver W₀)).left ≫ (oneOver W₀).left = _
      rw [oneOver_left]
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ projModelZero W₀) (Over.w (toUnit (modelOver W₀))))
    have hcompR : (toUnit (modelOver W) ≫ oneOver W).left =
        projModelπ W ≫ projModelZero W := by
      show (toUnit (modelOver W)).left ≫ (oneOver W).left = _
      rw [oneOver_left]
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ projModelZero W) (Over.w (toUnit (modelOver W))))
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (projModelBaseChangeOf f W₀ W h ≫ ·) (hL1.trans hcompL)).trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ projModelZero W₀) (wPB f W₀ W h).w).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (projModelπ W ≫ ·)
      (projModelZero_baseChangeOf f W₀ W h).symm).trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ projModelBaseChangeOf f W₀ W h) hcompR.symm).trans ?_
    refine (congrArg (· ≫ projModelBaseChangeOf f W₀ W h) hR1.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((axInclR W).left ≫ ·) (hsnd f W₀ W h).symm).trans ?_
    exact (Category.assoc _ _ _).symm

/-- The right axis of the first-stage model, scheme level. -/
noncomputable def axR₀ : projModel (wZero W) ⟶
    Limits.pullback (projModelπ (wZero W)) (projModelπ (wZero W)) :=
  (axInclR (wZero W)).left

theorem axR₀_sqStruct : axR₀ W ≫ sqStruct W = projModelπ (wZero W) := by
  have h1 : axR₀ W ≫ Limits.pullback.fst (projModelπ (wZero W)) (projModelπ (wZero W)) =
      𝟙 _ := congrArg CommaMorphism.left
        (lift_fst (𝟙 _) (toUnit (modelOver (wZero W)) ≫ oneOver (wZero W)))
  exact ((Category.assoc (axR₀ W)
      (Limits.pullback.fst (projModelπ (wZero W)) (projModelπ (wZero W)))
      (projModelπ (wZero W))).symm.trans
    (congrArg (· ≫ projModelπ (wZero W)) h1)).trans (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
/-- The right-axis map between the base-changed systems, at a stage. -/
noncomputable def axBCR (T : Over (wStageOp W)) :
    (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).obj T ⟶
    (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _).obj T :=
  Limits.pullback.map _ _ _ _ (𝟙 _) (axR₀ W) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, axR₀_sqStruct])

set_option backward.isDefEq.respectTransparency false in
/-- The apex-level right-axis map. -/
noncomputable def axApexR :
    (bcCone W (projModelπ (wZero W))).pt ⟶ (bcCone W (sqStruct W)).pt :=
  Limits.pullback.map _ _ _ _ (𝟙 _) (axR₀ W) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, axR₀_sqStruct])

/-- The cross-cone square for the right axis. -/
theorem axBCR_cone (T : Over (wStageOp W)) :
    (bcCone W (projModelπ (wZero W))).π.app T ≫ axBCR W T =
      axApexR W ≫ (bcCone W (sqStruct W)).π.app T := by
  refine Limits.pullback.hom_ext ?_ ?_
  · have h1 : axBCR W T ≫ Limits.pullback.fst
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.fst _ _ ≫ 𝟙 _ := Limits.pullback.lift_fst _ _ _
    have h2 : (bcCone W (projModelπ (wZero W))).π.app T ≫ Limits.pullback.fst
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom
        (projModelπ (wZero W)) =
        Limits.pullback.fst ((slicedCone W).pt).hom (projModelπ (wZero W)) ≫
          ((slicedCone W).π.app T).left := Limits.pullback.lift_fst _ _ _
    have h3 : (bcCone W (sqStruct W)).π.app T ≫ Limits.pullback.fst
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) ≫
          ((slicedCone W).π.app T).left := Limits.pullback.lift_fst _ _ _
    have h4 : axApexR W ≫ Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) =
        Limits.pullback.fst _ _ ≫ 𝟙 _ := Limits.pullback.lift_fst _ _ _
    exact (Category.assoc _ _ _).trans <|
      ((congrArg ((bcCone W (projModelπ (wZero W))).π.app T ≫ ·) h1).trans <|
        ((congrArg ((bcCone W (projModelπ (wZero W))).π.app T ≫ ·)
          (Category.comp_id _)).trans <|
          h2.trans <|
            ((congrArg (· ≫ ((slicedCone W).π.app T).left)
              ((Category.comp_id _).symm.trans h4.symm)).trans <|
              ((Category.assoc _ _ _).trans <|
                (congrArg (axApexR W ≫ ·) h3.symm).trans <|
                  (Category.assoc _ _ _).symm))))
  · have h1 : axBCR W T ≫ Limits.pullback.snd
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.snd _ _ ≫ axR₀ W := Limits.pullback.lift_snd _ _ _
    have hwM : (bcCone W (projModelπ (wZero W))).π.app T ≫
        Limits.pullback.snd ((Over.post (X := wStageOp W)
          (fgSys.specDiagram R)).obj T).hom (projModelπ (wZero W)) =
        Limits.pullback.snd ((slicedCone W).pt).hom (projModelπ (wZero W)) :=
      Over.w ((Over.pullback (projModelπ (wZero W))).map ((slicedCone W).π.app T))
    have hwSQ : (bcCone W (sqStruct W)).π.app T ≫
        Limits.pullback.snd ((Over.post (X := wStageOp W)
          (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) :=
      Over.w ((Over.pullback (sqStruct W)).map ((slicedCone W).π.app T))
    have h4 : axApexR W ≫ Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) =
        Limits.pullback.snd _ _ ≫ axR₀ W := Limits.pullback.lift_snd _ _ _
    exact (Category.assoc _ _ _).trans <|
      (congrArg ((bcCone W (projModelπ (wZero W))).π.app T ≫ ·) h1).trans <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ axR₀ W) hwM).trans <|
      h4.symm.trans <|
      (congrArg (axApexR W ≫ ·) hwSQ.symm).trans (Category.assoc _ _ _).symm

/-- The apex comparison square for the right axis. -/
theorem axApexR_comparison :
    (modelComparison W).hom ≫ axApexR W = (axInclR W).left ≫ (sqComparison W).hom := by
  refine Limits.pullback.hom_ext ?_ ?_
  · have h1 : axApexR W ≫ Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) =
        Limits.pullback.fst _ _ ≫ 𝟙 _ := Limits.pullback.lift_fst _ _ _
    have h2 : (modelComparison W).hom ≫
        Limits.pullback.fst ((slicedCone W).pt).hom (projModelπ (wZero W)) =
        projModelπ W :=
      (wPB (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).flip.isoPullback_hom_fst
    have h3 : (sqComparison W).hom ≫
        Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) =
        Limits.pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W :=
      (sqIsPullback (wStage W).1.val.toRingHom (wZero W) W
        (wZero_map W)).flip.isoPullback_hom_fst
    have h4 : (axInclR W).left ≫ Limits.pullback.fst (projModelπ W) (projModelπ W) ≫
        projModelπ W = projModelπ W := by
      have h5 : (axInclR W).left ≫ Limits.pullback.fst (projModelπ W) (projModelπ W) =
          𝟙 _ := congrArg CommaMorphism.left
            (lift_fst (𝟙 _) (toUnit (modelOver W) ≫ oneOver W))
      exact (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ projModelπ W) h5).trans (Category.id_comp _)
    have hA : ((modelComparison W).hom ≫ axApexR W) ≫
        Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) = projModelπ W := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((modelComparison W).hom ≫ ·) h1).trans ?_
      refine (congrArg ((modelComparison W).hom ≫ ·) (Category.comp_id _)).trans h2
    have hB : ((axInclR W).left ≫ (sqComparison W).hom) ≫
        Limits.pullback.fst ((slicedCone W).pt).hom (sqStruct W) = projModelπ W := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((axInclR W).left ≫ ·) h3).trans h4
    exact hA.trans hB.symm
  · have h1 : axApexR W ≫ Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) =
        Limits.pullback.snd _ _ ≫ axR₀ W := Limits.pullback.lift_snd _ _ _
    have h2 : (modelComparison W).hom ≫
        Limits.pullback.snd ((slicedCone W).pt).hom (projModelπ (wZero W)) =
        projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) :=
      (wPB (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).flip.isoPullback_hom_snd
    have h3 : (sqComparison W).hom ≫
        Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) =
        pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) :=
      (sqIsPullback (wStage W).1.val.toRingHom (wZero W) W
        (wZero_map W)).flip.isoPullback_hom_snd
    calc ((modelComparison W).hom ≫ axApexR W) ≫
          Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W)
        = (modelComparison W).hom ≫ (axApexR W ≫
            Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W)) :=
          Category.assoc _ _ _
      _ = (modelComparison W).hom ≫ (Limits.pullback.snd ((slicedCone W).pt).hom
            (projModelπ (wZero W)) ≫ axR₀ W) := congrArg ((modelComparison W).hom ≫ ·) h1
      _ = ((modelComparison W).hom ≫ Limits.pullback.snd ((slicedCone W).pt).hom
            (projModelπ (wZero W))) ≫ axR₀ W := (Category.assoc _ _ _).symm
      _ = projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) ≫
            axR₀ W := congrArg (· ≫ axR₀ W) h2
      _ = (axInclR W).left ≫ pullbackMapBaseChangeOf (wStage W).1.val.toRingHom (wZero W)
            W (wZero_map W) :=
          axNatR_of (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)
      _ = (axInclR W).left ≫ ((sqComparison W).hom ≫
            Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W)) :=
          congrArg ((axInclR W).left ≫ ·) h3.symm
      _ = ((axInclR W).left ≫ (sqComparison W).hom) ≫
            Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) :=
          (Category.assoc _ _ _).symm

end AxisBCR

/-! ## Stage bridges: the base-changed system objects against the stage model -/

section StageBridge

variable {R} (W : WeierstrassCurve R) [W.IsElliptic]

/-- The system object's structure map is the Spec of the stage inclusion (definitional). -/
theorem post_obj_hom (T : Over (wStageOp W)) :
    ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom =
    Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom) :=
  rfl

/-- The stage model against the base-changed model system object. -/
noncomputable def stageModelIso (T : Over (wStageOp W)) :
    projModel (stageW W T) ≅
    (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).obj T :=
  (stageModelPB W T).flip.isoPullback

/-- The stage square against the base-changed square system object. -/
noncomputable def stageSqIso (T : Over (wStageOp W)) :
    Limits.pullback (projModelπ (stageW W T)) (projModelπ (stageW W T)) ≅
    (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _).obj T :=
  (stageSqPB W T).flip.isoPullback

/-- Naturality of the left-axis map along stage transitions. -/
theorem axBC_natural {S T : Over (wStageOp W)} (σ : S ⟶ T) :
    (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫ axBC W T =
    axBC W S ≫ (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _).map σ := by
  refine Limits.pullback.hom_ext ?_ ?_
  · have h1 : axBC W T ≫ Limits.pullback.fst
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.fst _ _ ≫ 𝟙 _ := Limits.pullback.lift_fst _ _ _
    have h2 : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫
        Limits.pullback.fst
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom
          (projModelπ (wZero W)) =
        Limits.pullback.fst
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj S).hom
          (projModelπ (wZero W)) ≫
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).map σ).left :=
      Limits.pullback.lift_fst _ _ _
    have h3 : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback (sqStruct W) ⋙ Over.forget _).map σ ≫
        Limits.pullback.fst
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.fst
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj S).hom (sqStruct W) ≫
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).map σ).left :=
      Limits.pullback.lift_fst _ _ _
    have h4 : axBC W S ≫ Limits.pullback.fst
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj S).hom (sqStruct W) =
        Limits.pullback.fst _ _ ≫ 𝟙 _ := Limits.pullback.lift_fst _ _ _
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫ ·) h1).trans ?_
    refine (congrArg ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫ ·)
      (Category.comp_id _)).trans ?_
    refine h2.trans ?_
    refine (congrArg (· ≫ ((Over.post (X := wStageOp W)
      (fgSys.specDiagram R)).map σ).left)
      ((Category.comp_id _).symm.trans h4.symm)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (axBC W S ≫ ·) h3.symm).trans ?_
    exact (Category.assoc _ _ _).symm
  · have h1 : axBC W T ≫ Limits.pullback.snd
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.snd _ _ ≫ axL₀ W := Limits.pullback.lift_snd _ _ _
    have hwM : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫
        Limits.pullback.snd
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom
          (projModelπ (wZero W)) =
        Limits.pullback.snd
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj S).hom
          (projModelπ (wZero W)) :=
      Over.w ((Over.pullback (projModelπ (wZero W))).map
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).map σ))
    have hwSQ : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback (sqStruct W) ⋙ Over.forget _).map σ ≫
        Limits.pullback.snd
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.snd
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj S).hom (sqStruct W) :=
      Over.w ((Over.pullback (sqStruct W)).map
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).map σ))
    have h4 : axBC W S ≫ Limits.pullback.snd
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj S).hom (sqStruct W) =
        Limits.pullback.snd _ _ ≫ axL₀ W := Limits.pullback.lift_snd _ _ _
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫ ·) h1).trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ axL₀ W) hwM).trans ?_
    refine h4.symm.trans ?_
    refine (congrArg (axBC W S ≫ ·) hwSQ.symm).trans ?_
    exact (Category.assoc _ _ _).symm

/-- Naturality of the right-axis map along stage transitions. -/
theorem axBCR_natural {S T : Over (wStageOp W)} (σ : S ⟶ T) :
    (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫ axBCR W T =
    axBCR W S ≫ (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _).map σ := by
  refine Limits.pullback.hom_ext ?_ ?_
  · have h1 : axBCR W T ≫ Limits.pullback.fst
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.fst _ _ ≫ 𝟙 _ := Limits.pullback.lift_fst _ _ _
    have h2 : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫
        Limits.pullback.fst
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom
          (projModelπ (wZero W)) =
        Limits.pullback.fst
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj S).hom
          (projModelπ (wZero W)) ≫
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).map σ).left :=
      Limits.pullback.lift_fst _ _ _
    have h3 : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback (sqStruct W) ⋙ Over.forget _).map σ ≫
        Limits.pullback.fst
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.fst
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj S).hom (sqStruct W) ≫
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).map σ).left :=
      Limits.pullback.lift_fst _ _ _
    have h4 : axBCR W S ≫ Limits.pullback.fst
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj S).hom (sqStruct W) =
        Limits.pullback.fst _ _ ≫ 𝟙 _ := Limits.pullback.lift_fst _ _ _
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫ ·) h1).trans ?_
    refine (congrArg ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫ ·)
      (Category.comp_id _)).trans ?_
    refine h2.trans ?_
    refine (congrArg (· ≫ ((Over.post (X := wStageOp W)
      (fgSys.specDiagram R)).map σ).left)
      ((Category.comp_id _).symm.trans h4.symm)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (axBCR W S ≫ ·) h3.symm).trans ?_
    exact (Category.assoc _ _ _).symm
  · have h1 : axBCR W T ≫ Limits.pullback.snd
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.snd _ _ ≫ axR₀ W := Limits.pullback.lift_snd _ _ _
    have hwM : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫
        Limits.pullback.snd
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom
          (projModelπ (wZero W)) =
        Limits.pullback.snd
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj S).hom
          (projModelπ (wZero W)) :=
      Over.w ((Over.pullback (projModelπ (wZero W))).map
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).map σ))
    have hwSQ : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
        Over.pullback (sqStruct W) ⋙ Over.forget _).map σ ≫
        Limits.pullback.snd
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.snd
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj S).hom (sqStruct W) :=
      Over.w ((Over.pullback (sqStruct W)).map
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).map σ))
    have h4 : axBCR W S ≫ Limits.pullback.snd
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj S).hom (sqStruct W) =
        Limits.pullback.snd _ _ ≫ axR₀ W := Limits.pullback.lift_snd _ _ _
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫ ·) h1).trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ axR₀ W) hwM).trans ?_
    refine h4.symm.trans ?_
    refine (congrArg (axBCR W S ≫ ·) hwSQ.symm).trans ?_
    exact (Category.assoc _ _ _).symm

/-- The stage left axis corresponds to the base-changed left axis through the bridges. -/
theorem stage_axis_bridgeL (T : Over (wStageOp W)) :
    (axInclL (stageW W T)).left ≫ (stageSqIso W T).hom =
    (stageModelIso W T).hom ≫ axBC W T := by
  refine Limits.pullback.hom_ext ?_ ?_
  · have h1 : axBC W T ≫ Limits.pullback.fst
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.fst _ _ ≫ 𝟙 _ := Limits.pullback.lift_fst _ _ _
    have h5 : (axInclL (stageW W T)).left ≫
        Limits.pullback.fst (projModelπ (stageW W T)) (projModelπ (stageW W T)) =
        (toUnit (modelOver (stageW W T)) ≫ oneOver (stageW W T)).left :=
      congrArg CommaMorphism.left
        (lift_fst (toUnit (modelOver (stageW W T)) ≫ oneOver (stageW W T)) (𝟙 _))
    have hA : ((axInclL (stageW W T)).left ≫ (stageSqIso W T).hom) ≫
        Limits.pullback.fst
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        projModelπ (stageW W T) := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((axInclL (stageW W T)).left ≫ ·)
        (stageSqPB W T).flip.isoPullback_hom_fst).trans ?_
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ projModelπ (stageW W T)) h5).trans ?_
      exact Over.w (toUnit (modelOver (stageW W T)) ≫ oneOver (stageW W T))
    have hB : ((stageModelIso W T).hom ≫ axBC W T) ≫
        Limits.pullback.fst
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        projModelπ (stageW W T) := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((stageModelIso W T).hom ≫ ·) h1).trans ?_
      refine (congrArg ((stageModelIso W T).hom ≫ ·) (Category.comp_id _)).trans ?_
      exact (stageModelPB W T).flip.isoPullback_hom_fst
    exact hA.trans hB.symm
  · have h1 : axBC W T ≫ Limits.pullback.snd
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.snd _ _ ≫ axL₀ W := Limits.pullback.lift_snd _ _ _
    have hA : ((axInclL (stageW W T)).left ≫ (stageSqIso W T).hom) ≫
        Limits.pullback.snd
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        projModelBaseChangeOf (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom
          (wZero W) (stageW W T) rfl ≫ (axInclL (wZero W)).left := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((axInclL (stageW W T)).left ≫ ·)
        (stageSqPB W T).flip.isoPullback_hom_snd).trans ?_
      exact (axNatL_of (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom
        (wZero W) (stageW W T) rfl).symm
    have hB : ((stageModelIso W T).hom ≫ axBC W T) ≫
        Limits.pullback.snd
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        projModelBaseChangeOf (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom
          (wZero W) (stageW W T) rfl ≫ (axInclL (wZero W)).left := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((stageModelIso W T).hom ≫ ·) h1).trans ?_
      refine ((Category.assoc _ _ _).symm).trans ?_
      exact congrArg (· ≫ axL₀ W) (stageModelPB W T).flip.isoPullback_hom_snd
    exact hA.trans hB.symm

/-- The stage right axis corresponds to the base-changed right axis through the bridges. -/
theorem stage_axis_bridgeR (T : Over (wStageOp W)) :
    (axInclR (stageW W T)).left ≫ (stageSqIso W T).hom =
    (stageModelIso W T).hom ≫ axBCR W T := by
  refine Limits.pullback.hom_ext ?_ ?_
  · have h1 : axBCR W T ≫ Limits.pullback.fst
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.fst _ _ ≫ 𝟙 _ := Limits.pullback.lift_fst _ _ _
    have h5 : (axInclR (stageW W T)).left ≫
        Limits.pullback.fst (projModelπ (stageW W T)) (projModelπ (stageW W T)) =
        𝟙 _ :=
      congrArg CommaMorphism.left
        (lift_fst (𝟙 _) (toUnit (modelOver (stageW W T)) ≫ oneOver (stageW W T)))
    have hA : ((axInclR (stageW W T)).left ≫ (stageSqIso W T).hom) ≫
        Limits.pullback.fst
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        projModelπ (stageW W T) := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((axInclR (stageW W T)).left ≫ ·)
        (stageSqPB W T).flip.isoPullback_hom_fst).trans ?_
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ projModelπ (stageW W T)) h5).trans ?_
      exact Category.id_comp _
    have hB : ((stageModelIso W T).hom ≫ axBCR W T) ≫
        Limits.pullback.fst
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        projModelπ (stageW W T) := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((stageModelIso W T).hom ≫ ·) h1).trans ?_
      refine (congrArg ((stageModelIso W T).hom ≫ ·) (Category.comp_id _)).trans ?_
      exact (stageModelPB W T).flip.isoPullback_hom_fst
    exact hA.trans hB.symm
  · have h1 : axBCR W T ≫ Limits.pullback.snd
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        Limits.pullback.snd _ _ ≫ axR₀ W := Limits.pullback.lift_snd _ _ _
    have hA : ((axInclR (stageW W T)).left ≫ (stageSqIso W T).hom) ≫
        Limits.pullback.snd
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        projModelBaseChangeOf (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom
          (wZero W) (stageW W T) rfl ≫ (axInclR (wZero W)).left := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((axInclR (stageW W T)).left ≫ ·)
        (stageSqPB W T).flip.isoPullback_hom_snd).trans ?_
      exact (axNatR_of (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom
        (wZero W) (stageW W T) rfl).symm
    have hB : ((stageModelIso W T).hom ≫ axBCR W T) ≫
        Limits.pullback.snd
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T).hom (sqStruct W) =
        projModelBaseChangeOf (Subalgebra.inclusion (wStage_le_stage W T)).toRingHom
          (wZero W) (stageW W T) rfl ≫ (axInclR (wZero W)).left := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((stageModelIso W T).hom ≫ ·) h1).trans ?_
      refine ((Category.assoc _ _ _).symm).trans ?_
      exact congrArg (· ≫ axR₀ W) (stageModelPB W T).flip.isoPullback_hom_snd
    exact hA.trans hB.symm

end StageBridge

/-! ## Rigidity: a map on the square with both axis collapses is constant -/

section AxisRigidity

/-- **(K2 rigidity corollary, GIT 6.3 consumption)** Over a locally noetherian base, a
morphism `A ⊗ A ⟶ G` into a group object which collapses both axes to the unit is the
unit constant. Seesaw (`factor_mul_of_tensor_of_forall_component`) plus Hom-group
algebra. -/
theorem eq_one_of_axis_collapse {S : Scheme.{u}} [IsLocallyNoetherian S]
    {A G : Over S} [GrpObj A] [GrpObj G]
    [IsProper A.hom] [Flat A.hom] (hO : UniversallyOConnected A.hom)
    [IsSeparated G.hom] (q : A ⊗ A ⟶ G)
    (hL : lift (toUnit A ≫ η[A]) (𝟙 A) ≫ q = 1)
    (hR : lift (𝟙 A) (toUnit A ≫ η[A]) ≫ q = 1) : q = 1 := by
  haveI : IsLocallyNoetherian ↑A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have heA : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
  -- every component of the total space contains a fixed point of `η ∘ π`
  have hcorr := connectedComponent_eq_preimage_connectedComponent
    (f := (A.hom.base : _ → ↥S)) A.hom.base.hom.continuous A.hom.isOpenMap A.hom.isClosedMap
    (fun y => isConnected_fibre_of_universallyOConnected hO η[A].left heA y)
  have hπη : ∀ s : ↥S, A.hom.base (η[A].left.base s) = s := fun s => by
    exact congrArg (fun m : S ⟶ S => m.base s) heA
  have hfix : ∀ t : ↥A.left, ∃ b ∈ connectedComponent t,
      η[A].left.base (A.hom.base b) = b := by
    intro t
    refine ⟨η[A].left.base (A.hom.base t), ?_, ?_⟩
    · rw [hcorr t]
      show A.hom.base (η[A].left.base (A.hom.base t)) ∈ connectedComponent (A.hom.base t)
      rw [hπη (A.hom.base t)]
      exact mem_connectedComponent
    · exact congrArg (fun s => η[A].left.base s) (hπη (A.hom.base t))
  -- the seesaw decomposition of `q`
  obtain ⟨g, h, hgh⟩ := factor_mul_of_tensor_of_forall_component hO η[A] η[A] hfix q
  have hF : q = (fst A A ≫ g) * (snd A A ≫ h) := hgh
  -- axis restrictions of the decomposition
  have h1 : (1 : A ⟶ G) = g * (toUnit A ≫ (η[A] ≫ h)) := by
    calc (1 : A ⟶ G) = lift (𝟙 A) (toUnit A ≫ η[A]) ≫ q := hR.symm
      _ = lift (𝟙 A) (toUnit A ≫ η[A]) ≫ ((fst A A ≫ g) * (snd A A ≫ h)) := by rw [hF]
      _ = (lift (𝟙 A) (toUnit A ≫ η[A]) ≫ (fst A A ≫ g))
            * (lift (𝟙 A) (toUnit A ≫ η[A]) ≫ (snd A A ≫ h)) := MonObj.comp_mul _ _ _
      _ = g * (toUnit A ≫ (η[A] ≫ h)) := by
          rw [← Category.assoc, ← Category.assoc, lift_fst, lift_snd, Category.id_comp,
            Category.assoc]
  have h2 : (1 : A ⟶ G) = (toUnit A ≫ (η[A] ≫ g)) * h := by
    calc (1 : A ⟶ G) = lift (toUnit A ≫ η[A]) (𝟙 A) ≫ q := hL.symm
      _ = lift (toUnit A ≫ η[A]) (𝟙 A) ≫ ((fst A A ≫ g) * (snd A A ≫ h)) := by rw [hF]
      _ = (lift (toUnit A ≫ η[A]) (𝟙 A) ≫ (fst A A ≫ g))
            * (lift (toUnit A ≫ η[A]) (𝟙 A) ≫ (snd A A ≫ h)) := MonObj.comp_mul _ _ _
      _ = (toUnit A ≫ (η[A] ≫ g)) * h := by
          rw [← Category.assoc, ← Category.assoc, lift_fst, lift_snd, Category.id_comp,
            Category.assoc]
  -- the unit identity
  have hone : (η[A] ≫ g) * (η[A] ≫ h) = 1 := by
    have h3 : η[A] ≫ (1 : A ⟶ G) = (η[A] ≫ g) * (η[A] ≫ h) := by
      calc η[A] ≫ (1 : A ⟶ G)
          = (η[A] ≫ g) * (η[A] ≫ (toUnit A ≫ (η[A] ≫ h))) := by
            rw [h1]; exact MonObj.comp_mul _ _ _
        _ = (η[A] ≫ g) * (η[A] ≫ h) := by
            congr 1
            rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
    rw [← h3, MonObj.comp_one]
  -- solve for the two factors: both are constant
  have hg_eq : g = (toUnit A ≫ (η[A] ≫ h))⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
  have hh_eq : h = (toUnit A ≫ (η[A] ≫ g))⁻¹ := eq_inv_of_mul_eq_one_right h2.symm
  -- assemble: `q` is the inverse of a constant unit
  calc q = (fst A A ≫ g) * (snd A A ≫ h) := hF
    _ = (fst A A ≫ (toUnit A ≫ (η[A] ≫ h))⁻¹)
          * (snd A A ≫ (toUnit A ≫ (η[A] ≫ g))⁻¹) := by rw [← hg_eq, ← hh_eq]
    _ = (fst A A ≫ toUnit A ≫ (η[A] ≫ h))⁻¹
          * (snd A A ≫ toUnit A ≫ (η[A] ≫ g))⁻¹ := by
        rw [GrpObj.comp_inv, GrpObj.comp_inv]
    _ = (toUnit (A ⊗ A) ≫ (η[A] ≫ h))⁻¹ * (toUnit (A ⊗ A) ≫ (η[A] ≫ g))⁻¹ := by
        have hfstU : fst A A ≫ toUnit A ≫ (η[A] ≫ h) =
            toUnit (A ⊗ A) ≫ (η[A] ≫ h) := by
          rw [← Category.assoc, comp_toUnit]
        have hsndU : snd A A ≫ toUnit A ≫ (η[A] ≫ g) =
            toUnit (A ⊗ A) ≫ (η[A] ≫ g) := by
          rw [← Category.assoc, comp_toUnit]
        rw [hfstU, hsndU]
    _ = ((toUnit (A ⊗ A) ≫ (η[A] ≫ g)) * (toUnit (A ⊗ A) ≫ (η[A] ≫ h)))⁻¹ :=
        (mul_inv_rev _ _).symm
    _ = (toUnit (A ⊗ A) ≫ ((η[A] ≫ g) * (η[A] ≫ h)))⁻¹ := by rw [MonObj.comp_mul]
    _ = ((toUnit (A ⊗ A) ≫ (1 : 𝟙_ (Over S) ⟶ G)))⁻¹ := by rw [hone]
    _ = ((1 : A ⊗ A ⟶ G))⁻¹ := by rw [MonObj.comp_one]
    _ = 1 := inv_one

end AxisRigidity

/-! ## The uniqueness theorem ([U-MODEL]) -/

section Unique

variable {R} (W : WeierstrassCurve R) [W.IsElliptic]

/-- **([U-MODEL], K2)** Any group structure on the projective model with the model zero
section as unit has the T-G4 multiplication — over an ARBITRARY ring. -/
theorem modelGrpObj_unique (G : GrpObj (modelOver W))
    (hone : (letI := G; (η[modelOver W] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶
      modelOver W)) = oneOver W) :
    (letI := G; (μ[modelOver W] : modelOver W ⊗ modelOver W ⟶ modelOver W)) =
      mulOver W := by
  letI := modelGrpObj W
  set μG : modelOver W ⊗ modelOver W ⟶ modelOver W :=
    (letI := G; (μ[modelOver W] : modelOver W ⊗ modelOver W ⟶ modelOver W)) with hμGdef
  show μG = mulOver W
  -- the difference in the Hom-group of the model structure
  set F : modelOver W ⊗ modelOver W ⟶ modelOver W := μG * (mulOver W)⁻¹ with hFdef
  suffices hF1 : F = 1 by
    have h2 := congrArg (· * mulOver W) hF1
    simp only [hFdef] at h2
    rwa [_root_.mul_assoc, inv_mul_cancel, _root_.mul_one, _root_.one_mul] at h2
  -- the two axis collapses of the difference
  have hcolL : (axInclL W).left ≫ F.left =
      (modelOver W).hom ≫ (η[modelOver W] : 𝟙_ _ ⟶ modelOver W).left :=
    comp_mul_inv_left (axInclL W) μG (mulOver W)
      ((axInclL_mul W G hone).trans (axInclL_mul W (modelGrpObj W) rfl).symm)
  have hcolR : (axInclR W).left ≫ F.left =
      (modelOver W).hom ≫ (η[modelOver W] : 𝟙_ _ ⟶ modelOver W).left :=
    comp_mul_inv_left (axInclR W) μG (mulOver W)
      ((axInclR_mul W G hone).trans (axInclR_mul W (modelGrpObj W) rfl).symm)
  -- descend the difference to a stage
  have hFπ : F.left ≫ projModelπ W =
      Limits.pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W :=
    Over.w F
  obtain ⟨T, g', hg'cone, hg'π⟩ := mu_descends W F.left hFπ
  -- the comparison shuffle for the axis
  have hshuffle : axApex W ≫ (sqComparison W).inv =
      (modelComparison W).inv ≫ (axInclL W).left := by
    have h1 := axApex_comparison W
    have h2 := congrArg (fun m => (modelComparison W).inv ≫ m ≫ (sqComparison W).inv) h1
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
      at h2
    exact h2.trans (congrArg ((modelComparison W).inv ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg ((axInclL W).left ≫ ·)
        (Iso.hom_inv_id (sqComparison W))).trans (Category.comp_id _))))
  -- the stage collapse data: u := the axis then the descended difference; v := the
  -- constant zero
  set u : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).obj T ⟶ projModel (wZero W) :=
    axBC W T ≫ g' with hu_def
  set v : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).obj T ⟶ projModel (wZero W) :=
    (bcT W (projModelπ (wZero W))).app T ≫ projModelZero (wZero W) with hv_def
  -- the cone composites agree (the R-collapse transported)
  have hcone_uv : (bcCone W (projModelπ (wZero W))).π.app T ≫ u =
      (bcCone W (projModelπ (wZero W))).π.app T ≫ v := by
    -- the model-side η evaluated
    have hη : (modelOver W).hom ≫
        (η[modelOver W] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ modelOver W).left =
        projModelπ W ≫ projModelZero W := by
      show (modelOver W).hom ≫ (oneOver W).left = _
      rw [oneOver_left]
      show projModelπ W ≫ 𝟙 _ ≫ projModelZero W = _
      rw [Category.id_comp]
    -- the cone-leg structure facts
    have hw : (bcCone W (projModelπ (wZero W))).π.app T ≫
        ((Over.pullback (projModelπ (wZero W))).obj
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T)).hom =
        Limits.pullback.snd ((slicedCone W).pt).hom (projModelπ (wZero W)) :=
      Over.w ((Over.pullback (projModelπ (wZero W))).map ((slicedCone W).π.app T))
    have hinvfst : (modelComparison W).inv ≫ projModelπ W =
        Limits.pullback.fst ((slicedCone W).pt).hom (projModelπ (wZero W)) :=
      (wPB (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).flip.isoPullback_inv_fst
    -- LHS chain (refine-trans style: no calc endpoint unification)
    have hstep : (bcCone W (projModelπ (wZero W))).π.app T ≫ u =
        (Limits.pullback.snd ((slicedCone W).pt).hom (projModelπ (wZero W)) ≫
          projModelπ (wZero W)) ≫ projModelZero (wZero W) := by
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ g') (axBC_cone W T)).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (axApex W ≫ ·) hg'cone).trans ?_
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ (F.left ≫ projModelBaseChangeOf (wStage W).1.val.toRingHom
        (wZero W) W (wZero_map W))) hshuffle).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((modelComparison W).inv ≫ ·)
        ((Category.assoc _ _ _).symm)).trans ?_
      refine (congrArg (fun m => (modelComparison W).inv ≫ m ≫
        projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W))
        hcolL).trans ?_
      refine (congrArg (fun m => (modelComparison W).inv ≫ m ≫
        projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W))
        hη).trans ?_
      refine (congrArg ((modelComparison W).inv ≫ ·) (Category.assoc _ _ _)).trans ?_
      refine (congrArg (fun m => (modelComparison W).inv ≫ projModelπ W ≫ m)
        (projModelZero_baseChangeOf (wStage W).1.val.toRingHom (wZero W) W
          (wZero_map W))).trans ?_
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ (Spec.map (CommRingCat.ofHom (wStage W).1.val.toRingHom) ≫
        projModelZero (wZero W))) hinvfst).trans ?_
      refine ((Category.assoc _ _ _).symm).trans ?_
      exact congrArg (· ≫ projModelZero (wZero W)) Limits.pullback.condition
    have hstepv : (bcCone W (projModelπ (wZero W))).π.app T ≫ v =
        (Limits.pullback.snd ((slicedCone W).pt).hom (projModelπ (wZero W)) ≫
          projModelπ (wZero W)) ≫ projModelZero (wZero W) := by
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ projModelZero (wZero W))
        ((Category.assoc _ _ _).symm)).trans ?_
      exact congrArg (· ≫ projModelZero (wZero W))
        (congrArg (· ≫ projModelπ (wZero W)) hw)
    exact hstep.trans hstepv.symm
  -- the R-axis comparison shuffle
  have hshuffleR : axApexR W ≫ (sqComparison W).inv =
      (modelComparison W).inv ≫ (axInclR W).left := by
    have h1 := axApexR_comparison W
    have h2 := congrArg (fun m => (modelComparison W).inv ≫ m ≫ (sqComparison W).inv) h1
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
      at h2
    exact h2.trans (congrArg ((modelComparison W).inv ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg ((axInclR W).left ≫ ·)
        (Iso.hom_inv_id (sqComparison W))).trans (Category.comp_id _))))
  -- the R-axis collapse datum
  set uR : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).obj T ⟶ projModel (wZero W) :=
    axBCR W T ≫ g' with huR_def
  -- the R-axis cone equation (mirror of `hcone_uv`)
  have hcone_uvR : (bcCone W (projModelπ (wZero W))).π.app T ≫ uR =
      (bcCone W (projModelπ (wZero W))).π.app T ≫ v := by
    have hη : (modelOver W).hom ≫
        (η[modelOver W] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ modelOver W).left =
        projModelπ W ≫ projModelZero W := by
      show (modelOver W).hom ≫ (oneOver W).left = _
      rw [oneOver_left]
      show projModelπ W ≫ 𝟙 _ ≫ projModelZero W = _
      rw [Category.id_comp]
    have hw : (bcCone W (projModelπ (wZero W))).π.app T ≫
        ((Over.pullback (projModelπ (wZero W))).obj
          ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj T)).hom =
        Limits.pullback.snd ((slicedCone W).pt).hom (projModelπ (wZero W)) :=
      Over.w ((Over.pullback (projModelπ (wZero W))).map ((slicedCone W).π.app T))
    have hinvfst : (modelComparison W).inv ≫ projModelπ W =
        Limits.pullback.fst ((slicedCone W).pt).hom (projModelπ (wZero W)) :=
      (wPB (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).flip.isoPullback_inv_fst
    have hstep : (bcCone W (projModelπ (wZero W))).π.app T ≫ uR =
        (Limits.pullback.snd ((slicedCone W).pt).hom (projModelπ (wZero W)) ≫
          projModelπ (wZero W)) ≫ projModelZero (wZero W) := by
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ g') (axBCR_cone W T)).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (axApexR W ≫ ·) hg'cone).trans ?_
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ (F.left ≫ projModelBaseChangeOf (wStage W).1.val.toRingHom
        (wZero W) W (wZero_map W))) hshuffleR).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((modelComparison W).inv ≫ ·)
        ((Category.assoc _ _ _).symm)).trans ?_
      refine (congrArg (fun m => (modelComparison W).inv ≫ m ≫
        projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W))
        hcolR).trans ?_
      refine (congrArg (fun m => (modelComparison W).inv ≫ m ≫
        projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W))
        hη).trans ?_
      refine (congrArg ((modelComparison W).inv ≫ ·) (Category.assoc _ _ _)).trans ?_
      refine (congrArg (fun m => (modelComparison W).inv ≫ projModelπ W ≫ m)
        (projModelZero_baseChangeOf (wStage W).1.val.toRingHom (wZero W) W
          (wZero_map W))).trans ?_
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ (Spec.map (CommRingCat.ofHom (wStage W).1.val.toRingHom) ≫
        projModelZero (wZero W))) hinvfst).trans ?_
      refine ((Category.assoc _ _ _).symm).trans ?_
      exact congrArg (· ≫ projModelZero (wZero W)) Limits.pullback.condition
    have hstepv : (bcCone W (projModelπ (wZero W))).π.app T ≫ v =
        (Limits.pullback.snd ((slicedCone W).pt).hom (projModelπ (wZero W)) ≫
          projModelπ (wZero W)) ≫ projModelZero (wZero W) := by
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ projModelZero (wZero W))
        ((Category.assoc _ _ _).symm)).trans ?_
      exact congrArg (· ≫ projModelZero (wZero W))
        (congrArg (· ≫ projModelπ (wZero W)) hw)
    exact hstep.trans hstepv.symm
  -- instance supply for the descents
  haveI : SmoothOfRelativeDimension 1 (projModelπ (wZero W)) := projModel_smooth (wZero W)
  haveI : Smooth (projModelπ (wZero W)) :=
    SmoothOfRelativeDimension.smooth (n := 1) (f := projModelπ (wZero W))
  haveI : IsProper (projModelπ (wZero W)) := projModelπ_isProper (wZero W)
  haveI : UniversallyClosed (projModelπ (wZero W)) := inferInstance
  haveI hqc : QuasiCompact (projModelπ (wZero W)) := by infer_instance
  haveI hqs : QuasiSeparated (projModelπ (wZero W)) := by infer_instance
  haveI hlfp : LocallyOfFinitePresentation (projModelπ (wZero W)) := by infer_instance
  haveI hlft : LocallyOfFiniteType (projModelπ (wZero W)) := by infer_instance
  -- over-compatibility of the three collapse data
  have hu : (bcT W (projModelπ (wZero W))).app T = u ≫ projModelπ (wZero W) := by
    refine Eq.symm ?_
    show (axBC W T ≫ g') ≫ projModelπ (wZero W) = _
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (axBC W T ≫ ·) hg'π).trans ?_
    show axBC W T ≫ (Limits.pullback.snd _ _ ≫ sqStruct W) = _
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ sqStruct W) (Limits.pullback.lift_snd _ _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (Limits.pullback.snd _ _ ≫ ·) (axL₀_sqStruct W)
  have huR : (bcT W (projModelπ (wZero W))).app T = uR ≫ projModelπ (wZero W) := by
    refine Eq.symm ?_
    show (axBCR W T ≫ g') ≫ projModelπ (wZero W) = _
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (axBCR W T ≫ ·) hg'π).trans ?_
    show axBCR W T ≫ (Limits.pullback.snd _ _ ≫ sqStruct W) = _
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ sqStruct W) (Limits.pullback.lift_snd _ _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (Limits.pullback.snd _ _ ≫ ·) (axR₀_sqStruct W)
  have hv : (bcT W (projModelπ (wZero W))).app T = v ≫ projModelπ (wZero W) := by
    refine Eq.symm ?_
    show ((bcT W (projModelπ (wZero W))).app T ≫ projModelZero (wZero W)) ≫
      projModelπ (wZero W) = _
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((bcT W (projModelπ (wZero W))).app T ≫ ·)
      (projModelZero_projModelπ (wZero W))).trans ?_
    exact Category.comp_id _
  -- descend both collapse equations, then meet at a common stage
  obtain ⟨T₁, ψ₁, hψ₁⟩ := eq_descends W (projModelπ (wZero W)) hqc hqs
    (projModelπ (wZero W)) hlft (bcT W (projModelπ (wZero W))) u v hu hv hcone_uv
  obtain ⟨T₂, ψ₂, hψ₂⟩ := eq_descends W (projModelπ (wZero W)) hqc hqs
    (projModelπ (wZero W)) hlft (bcT W (projModelπ (wZero W))) uR v huR hv hcone_uvR
  obtain ⟨S₂, α, β, hαβ⟩ := IsCofiltered.cospan ψ₁ ψ₂
  set σ : S₂ ⟶ T := α ≫ ψ₁ with hσ_def
  -- both collapse equations hold after the transition to `S₂`
  have hLσ : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫ u =
      (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫ v := by
    show (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map (α ≫ ψ₁) ≫ u = _
    refine (congrArg (· ≫ u) (Functor.map_comp _ _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map α ≫ ·) hψ₁).trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    exact congrArg (· ≫ v) (Functor.map_comp _ _ _).symm
  have hRσ : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫ uR =
      (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫ v := by
    have hswap : σ = β ≫ ψ₂ := hαβ
    rw [hswap]
    refine (congrArg (· ≫ uR) (Functor.map_comp _ _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map β ≫ ·) hψ₂).trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    exact congrArg (· ≫ v) (Functor.map_comp _ _ _).symm
  -- the descended difference and its stage collapse equations
  set g'' : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _).obj S₂ ⟶ projModel (wZero W) :=
    (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _).map σ ≫ g' with hg''_def
  have hbcTσ : (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫
      (bcT W (projModelπ (wZero W))).app T =
      (bcT W (projModelπ (wZero W))).app S₂ :=
    ((bcT W (projModelπ (wZero W))).naturality σ).trans (Category.comp_id _)
  have hLS : axBC W S₂ ≫ g'' =
      (bcT W (projModelπ (wZero W))).app S₂ ≫ projModelZero (wZero W) := by
    show axBC W S₂ ≫ ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _).map σ ≫ g') = _
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ g') (axBC_natural W σ).symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine hLσ.trans ?_
    show (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫
      ((bcT W (projModelπ (wZero W))).app T ≫ projModelZero (wZero W)) = _
    refine ((Category.assoc _ _ _).symm).trans ?_
    exact congrArg (· ≫ projModelZero (wZero W)) hbcTσ
  have hRS : axBCR W S₂ ≫ g'' =
      (bcT W (projModelπ (wZero W))).app S₂ ≫ projModelZero (wZero W) := by
    show axBCR W S₂ ≫ ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _).map σ ≫ g') = _
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ g') (axBCR_natural W σ).symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine hRσ.trans ?_
    show (Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (projModelπ (wZero W)) ⋙ Over.forget _).map σ ≫
      ((bcT W (projModelπ (wZero W))).app T ≫ projModelZero (wZero W)) = _
    refine ((Category.assoc _ _ _).symm).trans ?_
    exact congrArg (· ≫ projModelZero (wZero W)) hbcTσ
  have hg''π : g'' ≫ projModelπ (wZero W) = (sqT W).app S₂ := by
    show ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _).map σ ≫ g') ≫
      projModelπ (wZero W) = _
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Over.post (X := wStageOp W) (fgSys.specDiagram R) ⋙
      Over.pullback (sqStruct W) ⋙ Over.forget _).map σ ≫ ·) hg'π).trans ?_
    exact ((sqT W).naturality σ).trans (Category.comp_id _)
  -- package the descended difference over the stage base
  have hwdS : ((stageSqIso W S₂).hom ≫ g'') ≫ projModelπ (wZero W) =
      (Limits.pullback.fst (projModelπ (stageW W S₂)) (projModelπ (stageW W S₂)) ≫
        projModelπ (stageW W S₂)) ≫
        Spec.map (CommRingCat.ofHom
          (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom) := by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((stageSqIso W S₂).hom ≫ ·) hg''π).trans ?_
    show (stageSqIso W S₂).hom ≫ (Limits.pullback.snd _ _ ≫ sqStruct W) = _
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ sqStruct W)
      (stageSqPB W S₂).flip.isoPullback_hom_snd).trans ?_
    exact (stageSqPB W S₂).w
  set dS : Limits.pullback (projModelπ (stageW W S₂)) (projModelπ (stageW W S₂)) ⟶
      projModel (stageW W S₂) :=
    (stageModelPB W S₂).lift ((stageSqIso W S₂).hom ≫ g'')
      (Limits.pullback.fst _ _ ≫ projModelπ (stageW W S₂)) hwdS with hdS_def
  -- the structural evaluation of the model bridge
  have hbcT_eval : (stageModelIso W S₂).hom ≫ (bcT W (projModelπ (wZero W))).app S₂ =
      projModelπ (stageW W S₂) ≫
        Spec.map (CommRingCat.ofHom
          (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom) := by
    show (stageModelIso W S₂).hom ≫
      (Limits.pullback.snd _ _ ≫ projModelπ (wZero W)) = _
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ projModelπ (wZero W))
      (stageModelPB W S₂).flip.isoPullback_hom_snd).trans ?_
    exact (stageModelPB W S₂).w
  -- the unit constant at the stage, scheme level
  have honeSt_left : (toUnit (modelOver (stageW W S₂)) ≫ oneOver (stageW W S₂)).left =
      projModelπ (stageW W S₂) ≫ projModelZero (stageW W S₂) := by
    show (toUnit (modelOver (stageW W S₂))).left ≫ (oneOver (stageW W S₂)).left = _
    rw [oneOver_left]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ projModelZero (stageW W S₂))
        (Over.w (toUnit (modelOver (stageW W S₂)))))
  -- the left axis collapses the packaged difference
  have hLdS : (axInclL (stageW W S₂)).left ≫ dS =
      projModelπ (stageW W S₂) ≫ projModelZero (stageW W S₂) := by
    refine (stageModelPB W S₂).hom_ext ?_ ?_
    · have hA : ((axInclL (stageW W S₂)).left ≫ dS) ≫
          projModelBaseChangeOf (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom
            (wZero W) (stageW W S₂) rfl =
          (projModelπ (stageW W S₂) ≫
            Spec.map (CommRingCat.ofHom
              (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom)) ≫
            projModelZero (wZero W) := by
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg ((axInclL (stageW W S₂)).left ≫ ·)
          ((stageModelPB W S₂).lift_fst _ _ _)).trans ?_
        refine ((Category.assoc _ _ _).symm).trans ?_
        refine (congrArg (· ≫ g'') (stage_axis_bridgeL W S₂)).trans ?_
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg ((stageModelIso W S₂).hom ≫ ·) hLS).trans ?_
        refine ((Category.assoc _ _ _).symm).trans ?_
        exact congrArg (· ≫ projModelZero (wZero W)) hbcT_eval
      have hB : (projModelπ (stageW W S₂) ≫ projModelZero (stageW W S₂)) ≫
          projModelBaseChangeOf (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom
            (wZero W) (stageW W S₂) rfl =
          (projModelπ (stageW W S₂) ≫
            Spec.map (CommRingCat.ofHom
              (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom)) ≫
            projModelZero (wZero W) := by
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (projModelπ (stageW W S₂) ≫ ·)
          (projModelZero_baseChangeOf
            (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom
            (wZero W) (stageW W S₂) rfl)).trans ?_
        exact (Category.assoc _ _ _).symm
      exact hA.trans hB.symm
    · have hA : ((axInclL (stageW W S₂)).left ≫ dS) ≫ projModelπ (stageW W S₂) =
          projModelπ (stageW W S₂) := by
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg ((axInclL (stageW W S₂)).left ≫ ·)
          ((stageModelPB W S₂).lift_snd _ _ _)).trans ?_
        refine ((Category.assoc _ _ _).symm).trans ?_
        refine (congrArg (· ≫ projModelπ (stageW W S₂))
          (congrArg CommaMorphism.left
            (lift_fst (toUnit (modelOver (stageW W S₂)) ≫ oneOver (stageW W S₂))
              (𝟙 _)))).trans ?_
        exact Over.w (toUnit (modelOver (stageW W S₂)) ≫ oneOver (stageW W S₂))
      have hB : (projModelπ (stageW W S₂) ≫ projModelZero (stageW W S₂)) ≫
          projModelπ (stageW W S₂) = projModelπ (stageW W S₂) := by
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (projModelπ (stageW W S₂) ≫ ·)
          (projModelZero_projModelπ (stageW W S₂))).trans ?_
        exact Category.comp_id _
      exact hA.trans hB.symm
  -- the right axis collapses the packaged difference
  have hRdS : (axInclR (stageW W S₂)).left ≫ dS =
      projModelπ (stageW W S₂) ≫ projModelZero (stageW W S₂) := by
    refine (stageModelPB W S₂).hom_ext ?_ ?_
    · have hA : ((axInclR (stageW W S₂)).left ≫ dS) ≫
          projModelBaseChangeOf (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom
            (wZero W) (stageW W S₂) rfl =
          (projModelπ (stageW W S₂) ≫
            Spec.map (CommRingCat.ofHom
              (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom)) ≫
            projModelZero (wZero W) := by
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg ((axInclR (stageW W S₂)).left ≫ ·)
          ((stageModelPB W S₂).lift_fst _ _ _)).trans ?_
        refine ((Category.assoc _ _ _).symm).trans ?_
        refine (congrArg (· ≫ g'') (stage_axis_bridgeR W S₂)).trans ?_
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg ((stageModelIso W S₂).hom ≫ ·) hRS).trans ?_
        refine ((Category.assoc _ _ _).symm).trans ?_
        exact congrArg (· ≫ projModelZero (wZero W)) hbcT_eval
      have hB : (projModelπ (stageW W S₂) ≫ projModelZero (stageW W S₂)) ≫
          projModelBaseChangeOf (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom
            (wZero W) (stageW W S₂) rfl =
          (projModelπ (stageW W S₂) ≫
            Spec.map (CommRingCat.ofHom
              (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom)) ≫
            projModelZero (wZero W) := by
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (projModelπ (stageW W S₂) ≫ ·)
          (projModelZero_baseChangeOf
            (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom
            (wZero W) (stageW W S₂) rfl)).trans ?_
        exact (Category.assoc _ _ _).symm
      exact hA.trans hB.symm
    · have hA : ((axInclR (stageW W S₂)).left ≫ dS) ≫ projModelπ (stageW W S₂) =
          projModelπ (stageW W S₂) := by
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg ((axInclR (stageW W S₂)).left ≫ ·)
          ((stageModelPB W S₂).lift_snd _ _ _)).trans ?_
        refine ((Category.assoc _ _ _).symm).trans ?_
        refine (congrArg (· ≫ projModelπ (stageW W S₂))
          (congrArg CommaMorphism.left
            (lift_fst (𝟙 _)
              (toUnit (modelOver (stageW W S₂)) ≫ oneOver (stageW W S₂))))).trans ?_
        exact Category.id_comp _
      have hB : (projModelπ (stageW W S₂) ≫ projModelZero (stageW W S₂)) ≫
          projModelπ (stageW W S₂) = projModelπ (stageW W S₂) := by
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (projModelπ (stageW W S₂) ≫ ·)
          (projModelZero_projModelπ (stageW W S₂))).trans ?_
        exact Category.comp_id _
      exact hA.trans hB.symm
  -- the packaged stage difference is the unit constant (noetherian rigidity)
  set qS : modelOver (stageW W S₂) ⊗ modelOver (stageW W S₂) ⟶
      modelOver (stageW W S₂) :=
    Over.homMk dS ((stageModelPB W S₂).lift_snd _ _ _) with hqS_def
  have hq1 : qS = (letI := modelGrpObj (stageW W S₂);
      (1 : modelOver (stageW W S₂) ⊗ modelOver (stageW W S₂) ⟶
        modelOver (stageW W S₂))) := by
    letI := modelGrpObj (stageW W S₂)
    haveI : SmoothOfRelativeDimension 1 (projModelπ (stageW W S₂)) :=
      projModel_smooth (stageW W S₂)
    haveI : Smooth (projModelπ (stageW W S₂)) :=
      SmoothOfRelativeDimension.smooth (n := 1) (f := projModelπ (stageW W S₂))
    haveI : IsProper (modelOver (stageW W S₂)).hom :=
      inferInstanceAs (IsProper (projModelπ (stageW W S₂)))
    haveI : Flat (modelOver (stageW W S₂)).hom :=
      inferInstanceAs (Flat (projModelπ (stageW W S₂)))
    haveI : IsSeparated (modelOver (stageW W S₂)).hom :=
      inferInstanceAs (IsSeparated (projModelπ (stageW W S₂)))
    haveI : IsNoetherianRing ↥(stageAlg W S₂) :=
      inferInstanceAs (IsNoetherianRing ↥(S₂.left.unop.1))
    haveI : IsLocallyNoetherian (Spec (CommRingCat.of ↥(stageAlg W S₂))) := by
      infer_instance
    have hO : UniversallyOConnected (modelOver (stageW W S₂)).hom :=
      (modelEllipticCurve (stageW W S₂)).toEllipticCurveGeom.universallyOConnected
    have hLq : axInclL (stageW W S₂) ≫ qS = 1 := by
      refine Over.OverMorphism.ext ?_
      show (axInclL (stageW W S₂)).left ≫ dS =
        (toUnit (modelOver (stageW W S₂)) ≫ oneOver (stageW W S₂)).left
      exact hLdS.trans honeSt_left.symm
    have hRq : axInclR (stageW W S₂) ≫ qS = 1 := by
      refine Over.OverMorphism.ext ?_
      show (axInclR (stageW W S₂)).left ≫ dS =
        (toUnit (modelOver (stageW W S₂)) ≫ oneOver (stageW W S₂)).left
      exact hRdS.trans honeSt_left.symm
    exact @eq_one_of_axis_collapse _ _ _ _
      (modelGrpObj (stageW W S₂)) (modelGrpObj (stageW W S₂)) _ _ hO _ qS hLq hRq
  -- unpack: the packaged difference is the constant zero composite
  have hdS1 : dS = (Limits.pullback.fst (projModelπ (stageW W S₂))
      (projModelπ (stageW W S₂)) ≫ projModelπ (stageW W S₂)) ≫
      projModelZero (stageW W S₂) := by
    have h := congrArg CommaMorphism.left hq1
    refine h.trans ?_
    show (modelOver (stageW W S₂) ⊗ modelOver (stageW W S₂)).hom ≫
      (oneOver (stageW W S₂)).left = _
    rw [oneOver_left]
    show (Limits.pullback.fst _ _ ≫ projModelπ (stageW W S₂)) ≫
      (𝟙 _ ≫ projModelZero (stageW W S₂)) = _
    rw [Category.id_comp]
    rfl
  -- hence the descended difference is the constant zero composite
  have hg''zero : g'' = (sqT W).app S₂ ≫ projModelZero (wZero W) := by
    have hfstlaw : dS ≫ projModelBaseChangeOf
        (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom
        (wZero W) (stageW W S₂) rfl = (stageSqIso W S₂).hom ≫ g'' :=
      (stageModelPB W S₂).lift_fst _ _ _
    have hconst : (stageSqIso W S₂).hom ≫ g'' =
        ((Limits.pullback.fst (projModelπ (stageW W S₂)) (projModelπ (stageW W S₂)) ≫
          projModelπ (stageW W S₂)) ≫
          Spec.map (CommRingCat.ofHom
            (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom)) ≫
          projModelZero (wZero W) := by
      refine hfstlaw.symm.trans ?_
      refine (congrArg (· ≫ projModelBaseChangeOf
        (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom
        (wZero W) (stageW W S₂) rfl) hdS1).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((Limits.pullback.fst (projModelπ (stageW W S₂))
        (projModelπ (stageW W S₂)) ≫ projModelπ (stageW W S₂)) ≫ ·)
        (projModelZero_baseChangeOf
          (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom
          (wZero W) (stageW W S₂) rfl)).trans ?_
      exact (Category.assoc _ _ _).symm
    have hg''form : g'' = (stageSqIso W S₂).inv ≫
        ((Limits.pullback.fst (projModelπ (stageW W S₂)) (projModelπ (stageW W S₂)) ≫
          projModelπ (stageW W S₂)) ≫
          Spec.map (CommRingCat.ofHom
            (Subalgebra.inclusion (wStage_le_stage W S₂)).toRingHom)) ≫
          projModelZero (wZero W) := by
      have h := congrArg ((stageSqIso W S₂).inv ≫ ·) hconst
      rw [Iso.inv_hom_id_assoc] at h
      exact h
    refine hg''form.trans ?_
    refine (congrArg ((stageSqIso W S₂).inv ≫ ·)
      (congrArg (· ≫ projModelZero (wZero W)) (stageSqPB W S₂).w.symm)).trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ projModelZero (wZero W))
      ((Category.assoc _ _ _).symm)).trans ?_
    refine (congrArg (· ≫ projModelZero (wZero W))
      (congrArg (· ≫ (Limits.pullback.fst (projModelπ (wZero W))
        (projModelπ (wZero W)) ≫ projModelπ (wZero W)))
        (stageSqPB W S₂).flip.isoPullback_inv_snd)).trans ?_
    rfl
  -- transport back to `R`: the difference against the comparison collapses
  have hwS₂ : (bcCone W (sqStruct W)).π.app S₂ ≫
      ((Over.pullback (sqStruct W)).obj
        ((Over.post (X := wStageOp W) (fgSys.specDiagram R)).obj S₂)).hom =
      Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) :=
    Over.w ((Over.pullback (sqStruct W)).map ((slicedCone W).π.app S₂))
  have hFconst : (sqComparison W).inv ≫ F.left ≫
      projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) =
      (Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) ≫ sqStruct W) ≫
        projModelZero (wZero W) := by
    have hLHS₂ : (bcCone W (sqStruct W)).π.app S₂ ≫ (sqT W).app S₂ =
        Limits.pullback.snd ((slicedCone W).pt).hom (sqStruct W) ≫ sqStruct W := by
      show (bcCone W (sqStruct W)).π.app S₂ ≫ (_ ≫ sqStruct W) = _
      refine ((Category.assoc _ _ _).symm).trans ?_
      exact congrArg (· ≫ sqStruct W) hwS₂
    refine hg'cone.symm.trans ?_
    refine (congrArg (· ≫ g') ((bcCone W (sqStruct W)).w σ).symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((bcCone W (sqStruct W)).π.app S₂ ≫ ·) hg''zero).trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    exact congrArg (· ≫ projModelZero (wZero W)) hLHS₂
  -- resolve `F.left` against the constant through the base-change square
  have hFpBC : F.left ≫ projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W
      (wZero_map W) =
      ((Limits.pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W) ≫
        projModelZero W) ≫
        projModelBaseChangeOf (wStage W).1.val.toRingHom (wZero W) W (wZero_map W) := by
    have h := congrArg ((sqComparison W).hom ≫ ·) hFconst
    rw [Iso.hom_inv_id_assoc] at h
    refine h.trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ projModelZero (wZero W))
      ((Category.assoc _ _ _).symm)).trans ?_
    refine (congrArg (· ≫ projModelZero (wZero W)) (congrArg (· ≫ sqStruct W)
      (sqIsPullback (wStage W).1.val.toRingHom (wZero W) W
        (wZero_map W)).flip.isoPullback_hom_snd)).trans ?_
    refine (congrArg (· ≫ projModelZero (wZero W))
      (sqIsPullback (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).w).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Limits.pullback.fst (projModelπ W) (projModelπ W) ≫
      projModelπ W) ≫ ·)
      (projModelZero_baseChangeOf (wStage W).1.val.toRingHom (wZero W) W
        (wZero_map W)).symm).trans ?_
    exact (Category.assoc _ _ _).symm
  have hFπ' : F.left ≫ projModelπ W =
      ((Limits.pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W) ≫
        projModelZero W) ≫ projModelπ W := by
    refine hFπ.trans ?_
    refine Eq.symm ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Limits.pullback.fst (projModelπ W) (projModelπ W) ≫
      projModelπ W) ≫ ·) (projModelZero_projModelπ W)).trans ?_
    exact Category.comp_id _
  have hF1left : F.left = (Limits.pullback.fst (projModelπ W) (projModelπ W) ≫
      projModelπ W) ≫ projModelZero W :=
    (wPB (wStage W).1.val.toRingHom (wZero W) W (wZero_map W)).hom_ext hFpBC hFπ'
  have hone_left : (toUnit (modelOver W ⊗ modelOver W) ≫ oneOver W).left =
      (Limits.pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W) ≫
        projModelZero W := by
    show (modelOver W ⊗ modelOver W).hom ≫ (oneOver W).left = _
    rw [oneOver_left]
    show (Limits.pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W) ≫
      (𝟙 _ ≫ projModelZero W) = _
    rw [Category.id_comp]
  refine Over.OverMorphism.ext ?_
  show F.left = (toUnit (modelOver W ⊗ modelOver W) ≫ oneOver W).left
  exact hF1left.trans hone_left.symm

end Unique

end ModularCurves
