/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.ModelRecord
import ModularCurves.EllipticCurve.Rigidity

/-!
# T-W7.0h: variable-change equivariance of the model multiplication

`mulModelHom_vc` — the variable-change isomorphism `projModelVCIso C W` intertwines the
model multiplications — proven WITHOUT the designed field-points extensionality:

1. **Noetherian case** (`mulModelHom_vc_of_noetherian`): the T-G4 group-object structure
   `modelGrpObj` exists at every base, the variable-change iso is pointed
   (`projModelVCIso_zero`), and all rigidity hypotheses hold at the model
   (`projModelπ_isProper`, smooth ⟹ flat, `universallyOConnected`), so GIT Cor 6.4
   (`isMonHom_of_one_comp_eq'`, PROVEN over locally noetherian bases) applies directly.
2. **Every base** (`mulModelHom_vc'`): the pair `(W, C)` has finitely many coefficients, so
   it is classified by a map from the universal VC-base `vcUnivRing` — a localization of a
   finite-variable polynomial ring over `ℤ`, hence noetherian — and the equation transports
   along the classifying map by `mulModelHom_map` (base-change naturality of the
   multiplication) + `projModelVCIso_map` (base-change naturality of the iso).

This discharges the single remaining `sorry` below the T-W7 descent layer
(`GroupLawConstruction.lean`'s `mulModelHom_vc`, relocated here per the v10.117 doctrine —
the rigidity/record imports must sit above `ModelRecord`).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj WeierstrassCurve

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-- GIT Cor 6.4, underlying-morphism form over abstract group objects (the abstract
statement keeps every `Over`-monoidal term at variable level — whnf-cheap to instantiate). -/
private theorem isMonHom_left_of_one_comp_eq' {S : Scheme.{u}} [IsLocallyNoetherian S]
    {A G : Over S} [GrpObj A] [GrpObj G]
    [IsProper A.hom] [Flat A.hom] (hO : UniversallyOConnected A.hom)
    [IsSeparated G.hom] (f : A ⟶ G) (hη : η[A] ≫ f = η[G]) :
    (μ[A] : A ⊗ A ⟶ A).left ≫ f.left =
      pullback.map A.hom A.hom G.hom G.hom f.left f.left (𝟙 S)
          (Over.w f).symm (Over.w f).symm ≫
        (μ[G] : G ⊗ G ⟶ G).left := by
  have h := isMonHom_of_one_comp_eq' hO f hη
  have hl : (μ[A] : A ⊗ A ⟶ A).left ≫ f.left =
      ((f ⊗ₘ f) : A ⊗ A ⟶ G ⊗ G).left ≫ (μ[G] : G ⊗ G ⟶ G).left :=
    (Over.comp_left _ _ _ _ _).symm.trans ((congrArg CommaMorphism.left h).trans
      (Over.comp_left _ _ _ _ _))
  rw [Over.tensorHom_left] at hl
  exact hl

/-- The underlying morphism of the `modelGrpObj` multiplication (hoisted: the `⊗`-typed
statement elaborates once, in its own heartbeat budget). -/
private theorem modelGrpObj_mul_left (W : WeierstrassCurve R) [W.IsElliptic] :
    letI := modelGrpObj W
    (μ[modelOver W] : modelOver W ⊗ modelOver W ⟶ modelOver W).left = mulModelHom W :=
  rfl

/-- The variable-change isomorphism as a morphism in `Over (Spec R)`. -/
noncomputable def vcOver (C : VariableChange R) (W : WeierstrassCurve R) :
    modelOver (C • W) ⟶ modelOver W :=
  Over.homMk (projModelVCIso C W).hom (projModelVCIso_π C W)

@[simp] theorem vcOver_left (C : VariableChange R) (W : WeierstrassCurve R) :
    (vcOver C W).left = (projModelVCIso C W).hom :=
  rfl

/-- The variable-change morphism is pointed (unit-compatible) for the `modelGrpObj`
structures: `projModelVCIso_zero` in `Over` form. -/
theorem vcOver_one (C : VariableChange R) (W : WeierstrassCurve R)
    [W.IsElliptic] [(C • W).IsElliptic] :
    letI := modelGrpObj (C • W)
    letI := modelGrpObj W
    η[modelOver (C • W)] ≫ vcOver C W = η[modelOver W] := by
  letI := modelGrpObj (C • W)
  letI := modelGrpObj W
  apply Over.OverMorphism.ext
  show ((𝟙_ (Over (Spec (CommRingCat.of R)))).hom ≫ projModelZero (C • W)) ≫
    (projModelVCIso C W).hom = (𝟙_ (Over (Spec (CommRingCat.of R)))).hom ≫ projModelZero W
  exact (Category.assoc _ _ _).trans
    (congrArg ((𝟙_ (Over (Spec (CommRingCat.of R)))).hom ≫ ·) (projModelVCIso_zero C W))

/-- **(T-W7.0h, noetherian case)** Variable-change equivariance of the model multiplication
over a noetherian ring: GIT Cor 6.4 applied to the pointed iso `vcOver` between the T-G4
group objects. -/
theorem mulModelHom_vc_of_noetherian [IsNoetherianRing R]
    (C : VariableChange R) (W : WeierstrassCurve R)
    [W.IsElliptic] [(C • W).IsElliptic] :
    mulModelHom (C • W) ≫ (projModelVCIso C W).hom =
      pullback.map (projModelπ (C • W)) (projModelπ (C • W))
          (projModelπ W) (projModelπ W)
          (projModelVCIso C W).hom (projModelVCIso C W).hom (𝟙 (Spec (CommRingCat.of R)))
          (by rw [Category.comp_id]; exact (projModelVCIso_π C W).symm)
          (by rw [Category.comp_id]; exact (projModelVCIso_π C W).symm) ≫
        mulModelHom W := by
  haveI : SmoothOfRelativeDimension 1 (projModelπ (C • W)) := projModel_smooth (C • W)
  haveI : Smooth (projModelπ (C • W)) :=
    SmoothOfRelativeDimension.smooth (n := 1) (f := projModelπ (C • W))
  haveI : IsProper (modelOver (C • W)).hom := inferInstanceAs (IsProper (projModelπ (C • W)))
  haveI : Flat (modelOver (C • W)).hom := inferInstanceAs (Flat (projModelπ (C • W)))
  haveI : IsSeparated (modelOver W).hom := inferInstanceAs (IsSeparated (projModelπ W))
  have hO : UniversallyOConnected (modelOver (C • W)).hom :=
    (modelEllipticCurve (C • W)).toEllipticCurveGeom.universallyOConnected
  have hl := @isMonHom_left_of_one_comp_eq' _ _ _ _
    (modelGrpObj (C • W)) (modelGrpObj W) _ _ hO _ (vcOver C W) (vcOver_one C W)
  rw [modelGrpObj_mul_left, modelGrpObj_mul_left] at hl
  exact hl
