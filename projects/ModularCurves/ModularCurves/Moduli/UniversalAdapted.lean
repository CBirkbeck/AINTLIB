/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import ModularCurves.EllipticCurve.ModelRecord
import ModularCurves.Moduli.AdaptedModel
import ModularCurves.Moduli.EllCategory

/-!
# The universal ω-adapted curve and its moduli ring (T-E12, E12-D1)

**(E12-D, STREAM-OMEGA 2026-07-14; board [T-E12] E12-D decompose.)**

The `R`-relative moduli ring of T-E12, `R₁ = R[A₄, A₆][Δ⁻¹]`, and the universal
short-normal-form Weierstrass curve `y² = x³ + A₄x + A₆` over it — the curve that
`M₁ = Spec R₁` will carry as the universal `(E, ω)` (GME Thm 2.2.3; the classical
`ℤ[1/6, g₂, g₃, Δ⁻¹]` presentation differs by the invertible rescaling
`(g₂, g₃) = (−4A₄, −4A₆)`-style; the short form matches `adaptedCoeff₄/₆`,
`Moduli/AdaptedModel.lean`).
-/

universe u

namespace ModularCurves

open MvPolynomial

variable (R : Type u) [CommRing R]

/-- The discriminant polynomial `Δ(A₄, A₆) = −16(4A₄³ + 27A₆²)` of the universal
short Weierstrass curve. -/
noncomputable def shortDeltaPoly : MvPolynomial (Fin 2) R :=
  -16 * (4 * (X 0) ^ 3 + 27 * (X 1) ^ 2)

/-- **(E12-D1)** The T-E12 moduli ring `R₁ = R[A₄, A₆][Δ⁻¹]`. -/
abbrev ModuliRingE12 : Type u :=
  Localization.Away (shortDeltaPoly R)

/-- **(E12-D1)** The universal short-normal-form Weierstrass curve
`y² = x³ + A₄x + A₆` over the moduli ring. -/
noncomputable def universalShortNF : WeierstrassCurve (ModuliRingE12 R) :=
  ⟨0, 0, 0, algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X 0),
    algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X 1)⟩

instance : (universalShortNF R).IsShortNF :=
  ⟨rfl, rfl, rfl⟩

/-- The discriminant of the universal curve is the localized discriminant
polynomial. -/
theorem universalShortNF_Δ :
    (universalShortNF R).Δ =
      algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (shortDeltaPoly R) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, universalShortNF, shortDeltaPoly,
    map_mul, map_add, map_pow, map_neg, map_ofNat]
  ring

/-- **(E12-D1)** The universal curve is elliptic: its discriminant is the localized
unit. -/
instance : (universalShortNF R).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, universalShortNF_Δ]
  exact IsLocalization.Away.algebraMap_isUnit (S := ModuliRingE12 R) (shortDeltaPoly R)


open AlgebraicGeometry CategoryTheory Limits Scheme in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D2c)** The tautological global presentation of the projective model over its
own `Spec`: chart `⊤`, curve `W` base-changed to the section ring, chart isomorphism
the pullback-collapse (extracted from `locallyWeierstrass_projModel`). -/
noncomputable def tautPresentation {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    [W.IsElliptic] :
    LocalPresentation (modelEllipticCurve W).toEllipticCurveGeom
      ⟨⊤, isAffineOpen_top _⟩ := by
  set S := Spec (CommRingCat.of A) with hS
  letI : Algebra A ↑Γ(S, (⊤ : S.Opens)) :=
    (Scheme.ΓSpecIso (.of A)).inv.hom.toAlgebra
  haveI : IsIso (⊤ : S.Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  haveI : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap A ↑Γ(S, (⊤ : S.Opens))))) := by
    have h : CommRingCat.ofHom (algebraMap A ↑Γ(S, (⊤ : S.Opens))) =
        (Scheme.ΓSpecIso (.of A)).inv := rfl
    rw [h]
    infer_instance
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) =
      S.isoSpec.inv := (Scheme.isoSpec_Spec_inv (.of A)).symm
  refine
    { W := W.map (algebraMap A ↑Γ(S, (⊤ : S.Opens)))
      elliptic := inferInstance
      e := asIso (pullback.fst (projModelπ W) (⊤ : S.Opens).ι) ≪≫
        (asIso (pullback.fst (projModelπ W) (Spec.map (CommRingCat.ofHom
          (algebraMap A ↑Γ(S, (⊤ : S.Opens))))))).symm ≪≫
        (isPullback_projModelBaseChange W).isoPullback.symm
      compat_π := ?_
      compat_zero := ?_ }
  · have hcrux : ∀ (h : (⊤ : S.Opens) ∈ S.affineOpens),
        (IsAffineOpen.isoSpec h).hom ≫ Spec.map (CommRingCat.ofHom
          (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) = (⊤ : S.Opens).ι := by
      exact fun h => hφ ▸ isoSpec_hom_comp_isoSpec_inv_top S h
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom
      (algebraMap A ↑Γ(S, (⊤ : S.Opens)))))]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
      IsPullback.isoPullback_inv_snd]
    conv_rhs => erw [hcrux]
    erw [← pullback.condition, IsIso.inv_hom_id_assoc]
    exact pullback.condition
  · have hcrux : (isAffineOpen_top S).isoSpec.inv ≫ (⊤ : S.Opens).ι =
        Spec.map (CommRingCat.ofHom (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) :=
      hφ ▸ (IsAffineOpen.isoSpec_inv_ι _).trans IsAffineOpen.fromSpec_top
    have hcrux_assoc : ∀ {Z : Scheme.{u}} (g : S ⟶ Z),
        (isAffineOpen_top S).isoSpec.inv ≫ (⊤ : S.Opens).ι ≫ g =
          Spec.map (CommRingCat.ofHom
            (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) ≫ g := fun g => by
      rw [← Category.assoc]
      exact congrArg (· ≫ g) hcrux
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc]
    erw [pullback.lift_fst_assoc]
    simp only [Category.assoc]
    conv_lhs => erw [hcrux_assoc]
    erw [← reassoc_of% projModelZero_baseChange W,
      ← (isPullback_projModelBaseChange W).isoPullback_hom_fst_assoc,
      IsIso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

open Scheme in
/-- **(E12-D2 ★)** The universal `(E, ω)`-datum over the moduli base: the projective
model of the universal short-normal-form curve together with the `ω`-basis its
tautological presentation defines. -/
noncomputable def universalOmegaBasis :
    OmegaBasis (modelEllipticCurve (universalShortNF R)).toEllipticCurveGeom :=
  OmegaBasis.ofPresentation rfl (tautPresentation (universalShortNF R))


open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
/-- The structure ring map of an `Ell/R`-object: `R → Γ(Y.base, ⊤)`. -/
noncomputable def EllObj.baseRingHom {R : CommRingCat.{u}} (Y : EllObj R) :
    R →+* Γ(Y.base, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ Y.structMap.appTop).hom

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D3 ★)** The classifying ring map of an `(E, ω)`-datum:
`R[A₄, A₆][Δ⁻¹] → Γ(Y.base, ⊤)`, `A₄ ↦ adaptedCoeff₄, A₆ ↦ adaptedCoeff₆` — the
algebra of GME Thm 2.2.3's classifying morphism `Y.base ⟶ M₁`. -/
noncomputable def classifyingRingHom {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤))) :
    ModuliRingE12 R →+* Γ(Y.base, ⊤) := by
  refine IsLocalization.Away.lift (shortDeltaPoly R)
    (g := eval₂Hom Y.baseRingHom
      ![(adaptedCoeff₄ Y.curve.toEllipticCurveGeom b h2 h3).1,
        (adaptedCoeff₆ Y.curve.toEllipticCurveGeom b h2 h3).1]) ?_
  have hΔ := adaptedDelta_isUnit Y.curve.toEllipticCurveGeom b h2 h3
  rw [show (eval₂Hom Y.baseRingHom
      ![(adaptedCoeff₄ Y.curve.toEllipticCurveGeom b h2 h3).1,
        (adaptedCoeff₆ Y.curve.toEllipticCurveGeom b h2 h3).1]) (shortDeltaPoly R) =
    (-16 : Γ(Y.base, ⊤)) *
      (4 * ((adaptedCoeff₄ Y.curve.toEllipticCurveGeom b h2 h3).1) ^ 3 +
        27 * ((adaptedCoeff₆ Y.curve.toEllipticCurveGeom b h2 h3).1) ^ 2) from by
    simp only [shortDeltaPoly, map_mul, map_add, map_pow, map_neg, map_ofNat,
      eval₂Hom_X']
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]]
  exact hΔ


open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
/-- **(E12-D3 ★)** The classifying morphism of an `(E, ω)`-datum:
`Y.base ⟶ M₁ = Spec R[A₄,A₆][Δ⁻¹]` through the `Γ–Spec` adjunction — GME Thm 2.2.3's
map to the moduli space. -/
noncomputable def classifyingMap {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤))) :
    Y.base ⟶ Spec (CommRingCat.of (ModuliRingE12 R)) :=
  Y.base.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (classifyingRingHom Y b h2 h3))


open AlgebraicGeometry CategoryTheory Scheme LocalPresentation MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- **(E12-D3-E1)** The per-chart coefficient match: specializing the universal curve
along the classifying map, restricted to a chart-supported affine, recovers exactly
the adapted local model. -/
theorem universalShortNF_map_classifying {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤)))
    (V : Y.base.affineOpens) (i : Y.curve.toEllipticCurveGeom.atlas.ι)
    (hVi : V.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U i).1) :
    (universalShortNF R).map
      (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3)) =
      (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi).W := by
  haveI := adaptedLocal_isShortNF Y.curve.toEllipticCurveGeom b h2 h3 V i hVi
  have h4spec := (adaptedCoeff₄ Y.curve.toEllipticCurveGeom b h2 h3).2 V i hVi
  have h6spec := (adaptedCoeff₆ Y.curve.toEllipticCurveGeom b h2 h3).2 V i hVi
  have hlift4 : classifyingRingHom Y b h2 h3
      (algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X 0)) =
    (adaptedCoeff₄ Y.curve.toEllipticCurveGeom b h2 h3).1 := by
    rw [classifyingRingHom]
    rw [IsLocalization.Away.lift_eq]
    simp [eval₂Hom_X']
  have hlift6 : classifyingRingHom Y b h2 h3
      (algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X 1)) =
    (adaptedCoeff₆ Y.curve.toEllipticCurveGeom b h2 h3).1 := by
    rw [classifyingRingHom]
    rw [IsLocalization.Away.lift_eq]
    simp [eval₂Hom_X']
  ext
  · show ((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom)
      (classifyingRingHom Y b h2 h3 (universalShortNF R).a₁) = _
    rw [show (universalShortNF R).a₁ = 0 from rfl, map_zero, map_zero]
    exact ((adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i
      hVi).W.a₁_of_isShortNF).symm
  · show ((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom)
      (classifyingRingHom Y b h2 h3 (universalShortNF R).a₂) = _
    rw [show (universalShortNF R).a₂ = 0 from rfl, map_zero, map_zero]
    exact ((adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i
      hVi).W.a₂_of_isShortNF).symm
  · show ((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom)
      (classifyingRingHom Y b h2 h3 (universalShortNF R).a₃) = _
    rw [show (universalShortNF R).a₃ = 0 from rfl, map_zero, map_zero]
    exact ((adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i
      hVi).W.a₃_of_isShortNF).symm
  · show ((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom)
      (classifyingRingHom Y b h2 h3 (universalShortNF R).a₄) = _
    rw [show (universalShortNF R).a₄ =
      algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X 0) from rfl,
      hlift4]
    exact h4spec
  · show ((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom)
      (classifyingRingHom Y b h2 h3 (universalShortNF R).a₆) = _
    rw [show (universalShortNF R).a₆ =
      algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X 1) from rfl,
      hlift6]
    exact h6spec


open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D3-E2)** The per-chart piece of the classifying `EllHom`: through the
adapted chart isomorphism, the coefficient match, and the model base change. -/
noncomputable def chartPiece {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤)))
    (V : Y.base.affineOpens) (i : Y.curve.toEllipticCurveGeom.atlas.ι)
    (hVi : V.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U i).1) :
    (pullback Y.curve.toEllipticCurveGeom.π V.1.ι : Scheme.{u}) ⟶
      projModel (universalShortNF R) :=
  (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi).e.hom ≫
    eqToHom (congrArg projModel
      (universalShortNF_map_classifying Y b h2 h3 V i hVi).symm) ≫
    projModelBaseChange
      (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3)) (universalShortNF R)


open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- **(E12-D3-E2)** The piece map lies over the restricted classifying map. -/
theorem chartPiece_π {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤)))
    (V : Y.base.affineOpens) (i : Y.curve.toEllipticCurveGeom.atlas.ι)
    (hVi : V.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U i).1) :
    chartPiece Y b h2 h3 V i hVi ≫ projModelπ (universalShortNF R) =
      pullback.snd Y.curve.toEllipticCurveGeom.π V.1.ι ≫ V.2.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom
          (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
            (classifyingRingHom Y b h2 h3))) := by
  have hw : projModelBaseChange
      (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3)) (universalShortNF R) ≫
      projModelπ (universalShortNF R) =
    projModelπ ((universalShortNF R).map
      (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3))) ≫
      Spec.map (CommRingCat.ofHom
        (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
          (classifyingRingHom Y b h2 h3))) := by
    letI : Algebra (ModuliRingE12 R) Γ(Y.base, V.1) :=
      ((((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3))).toAlgebra
    exact (isPullback_projModelBaseChange (universalShortNF R)).w
  rw [chartPiece, Category.assoc, Category.assoc, hw,
    reassoc_of% projModelπ_congr
      (universalShortNF_map_classifying Y b h2 h3 V i hVi).symm]
  rw [← Category.assoc,
    (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi).compat_π,
    Category.assoc]

end ModularCurves
