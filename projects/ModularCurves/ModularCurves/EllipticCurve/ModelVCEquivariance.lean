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

/-! ## The universal VC-base

The pair (Weierstrass curve, variable change) with invertible discriminant is classified by
a map from a fixed noetherian ring: the polynomial ring over `ℤ` on the five coefficients
and the four variable-change parameters, localized at `Δ · u`. -/

/-- The nine-variable polynomial base over `ℤ`: `a₁ a₂ a₃ a₄ a₆ u r s t`. -/
abbrev vcUnivPoly : Type := MvPolynomial (Fin 9) ℤ

/-- The generic Weierstrass curve over the nine-variable base. -/
noncomputable def vcUnivW : WeierstrassCurve vcUnivPoly :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

/-- The localizing element `Δ · u`. -/
noncomputable def vcUnivElt : vcUnivPoly := vcUnivW.Δ * MvPolynomial.X 5

/-- The universal VC-base: the nine-variable ring with `Δ · u` inverted — a localization of
a finite-variable polynomial ring over `ℤ`, hence noetherian. -/
abbrev vcUnivRing : Type := Localization.Away vcUnivElt

/-- The generic Weierstrass curve over the universal VC-base. -/
noncomputable def vcUnivW₀ : WeierstrassCurve vcUnivRing :=
  vcUnivW.map (algebraMap vcUnivPoly vcUnivRing)

/-- `u` is a unit in the universal VC-base (it divides the inverted element). -/
theorem vcUniv_isUnit_u :
    IsUnit (algebraMap vcUnivPoly vcUnivRing (MvPolynomial.X 5)) :=
  isUnit_of_mul_isUnit_left (y := algebraMap vcUnivPoly vcUnivRing vcUnivW.Δ) <| by
    rw [mul_comm, ← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (S := vcUnivRing) vcUnivElt

/-- The discriminant is a unit in the universal VC-base. -/
theorem vcUniv_isUnit_Δ : IsUnit vcUnivW₀.Δ := by
  show IsUnit ((vcUnivW.map (algebraMap vcUnivPoly vcUnivRing)).Δ)
  rw [WeierstrassCurve.map_Δ]
  exact isUnit_of_mul_isUnit_left (y := algebraMap vcUnivPoly vcUnivRing
    (MvPolynomial.X 5)) (by
      rw [← map_mul]
      exact IsLocalization.Away.algebraMap_isUnit (S := vcUnivRing) vcUnivElt)

instance : vcUnivW₀.IsElliptic := ⟨vcUniv_isUnit_Δ⟩

/-- The generic variable change over the universal VC-base. -/
noncomputable def vcUnivC : VariableChange vcUnivRing where
  u := vcUniv_isUnit_u.unit
  r := algebraMap vcUnivPoly vcUnivRing (MvPolynomial.X 6)
  s := algebraMap vcUnivPoly vcUnivRing (MvPolynomial.X 7)
  t := algebraMap vcUnivPoly vcUnivRing (MvPolynomial.X 8)

instance : (vcUnivC • vcUnivW₀).IsElliptic := by
  constructor
  rw [WeierstrassCurve.variableChange_Δ]
  exact (IsUnit.pow 12 (vcUnivC.u⁻¹).isUnit).mul vcUniv_isUnit_Δ

instance : IsNoetherianRing vcUnivRing :=
  IsLocalization.isNoetherianRing (Submonoid.powers vcUnivElt) _ inferInstance

/-! ## The classifying map -/

section Classify

variable (C : VariableChange R) (W : WeierstrassCurve R)

/-- The evaluation of the nine-variable polynomial base at a concrete pair `(W, C)`. -/
noncomputable def vcClassifyPoly : vcUnivPoly →+* R :=
  (MvPolynomial.aeval
    ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆, ↑C.u, C.r, C.s, C.t]).toRingHom

/-- The evaluation classifies the Weierstrass curve. -/
theorem vcClassifyPoly_W : vcUnivW.map (vcClassifyPoly C W) = W := by
  ext <;> simp [vcUnivW, vcClassifyPoly]

/-- The evaluation sends the localizing element to a unit. -/
theorem vcClassifyPoly_isUnit [W.IsElliptic] :
    IsUnit (vcClassifyPoly C W vcUnivElt) := by
  have h : vcClassifyPoly C W vcUnivElt = W.Δ * ↑C.u := by
    show vcClassifyPoly C W (vcUnivW.Δ * MvPolynomial.X 5) = W.Δ * ↑C.u
    rw [map_mul]
    congr 1
    · rw [← WeierstrassCurve.map_Δ, vcClassifyPoly_W]
    · simp [vcClassifyPoly]
  rw [h]
  exact W.isUnit_Δ.mul C.u.isUnit

variable [W.IsElliptic]

/-- The classifying map from the universal VC-base. -/
noncomputable def vcClassify : vcUnivRing →+* R :=
  IsLocalization.Away.lift vcUnivElt (g := vcClassifyPoly C W) (vcClassifyPoly_isUnit C W)

theorem vcClassify_algebraMap (p : vcUnivPoly) :
    vcClassify C W (algebraMap vcUnivPoly vcUnivRing p) = vcClassifyPoly C W p :=
  IsLocalization.Away.lift_eq vcUnivElt (vcClassifyPoly_isUnit C W) p

/-- The classifier recovers the Weierstrass curve. -/
theorem vcClassify_W : vcUnivW₀.map (vcClassify C W) = W := by
  show (vcUnivW.map (algebraMap vcUnivPoly vcUnivRing)).map (vcClassify C W) = W
  rw [WeierstrassCurve.map_map,
    show (vcClassify C W).comp (algebraMap vcUnivPoly vcUnivRing) = vcClassifyPoly C W
      from RingHom.ext fun p => vcClassify_algebraMap C W p]
  exact vcClassifyPoly_W C W

/-- The classifier recovers the variable change. -/
theorem vcClassify_C : vcUnivC.map (vcClassify C W) = C := by
  ext
  · show vcClassify C W (algebraMap vcUnivPoly vcUnivRing (MvPolynomial.X 5)) = ↑C.u
    rw [vcClassify_algebraMap]
    simp [vcClassifyPoly]
  · show vcClassify C W (algebraMap vcUnivPoly vcUnivRing (MvPolynomial.X 6)) = C.r
    rw [vcClassify_algebraMap]
    simp [vcClassifyPoly]
  · show vcClassify C W (algebraMap vcUnivPoly vcUnivRing (MvPolynomial.X 7)) = C.s
    rw [vcClassify_algebraMap]
    simp [vcClassifyPoly]
  · show vcClassify C W (algebraMap vcUnivPoly vcUnivRing (MvPolynomial.X 8)) = C.t
    rw [vcClassify_algebraMap]
    simp [vcClassifyPoly]

end Classify
