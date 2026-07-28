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
import ModularCurves.Moduli.OmegaFunctor
import ModularCurves.ForMathlib.PullbackLocalAtTarget
import ModularCurves.ForMathlib.BaseChangeAlongCompat

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

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

set_option synthInstance.maxHeartbeats 6400000
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 6400000

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
set_option maxHeartbeats 6400000 in
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
set_option maxHeartbeats 6400000 in
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


open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(E12-D3-E3b)** The piece maps are compatible with restriction: the classifying
pieces glue. Core: the restricted adapted model IS the smaller adapted model
(`transVC_eq_one_of_isAdapted` through `pointedIso_hom_of_transVC_eq_one`) and the
model base change composes (`projModelBaseChange_comp'`). -/
theorem chartPiece_restrict {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤)))
    (V : Y.base.affineOpens) (i : Y.curve.toEllipticCurveGeom.atlas.ι)
    (hVi : V.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U i).1)
    {O' : Y.base.affineOpens} (h : O'.1 ≤ V.1) :
    restrictTheta h ≫ chartPiece Y b h2 h3 V i hVi =
      chartPiece Y b h2 h3 O' i (h.trans hVi) := by
  -- notation
  set Q := adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi with hQ
  set Q' := adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 O' i (h.trans hVi) with hQ'
  -- the restricted adapted model equals the smaller adapted model, as charts
  have hVC : Q'.transVC (Q.restrict h) = 1 :=
    transVC_eq_one_of_isAdapted
      (adaptedLocal_isAdapted Y.curve.toEllipticCurveGeom b h2 h3 O' i (h.trans hVi))
      ((adaptedLocal_isAdapted Y.curve.toEllipticCurveGeom b h2 h3 V i hVi).restrict h)
      (adaptedLocal_isShortNF Y.curve.toEllipticCurveGeom b h2 h3 O' i (h.trans hVi))
      (isShortNF_map
        (adaptedLocal_isShortNF Y.curve.toEllipticCurveGeom b h2 h3 V i hVi) _)
      (isUnit_ofNat_res h2 O'.1) (isUnit_ofNat_res h3 O'.1)
  have hWeq : (Q.restrict h).W = Q'.W := by
    have := Q'.transVC_smul (Q.restrict h)
    rwa [hVC, one_smul] at this
  have hIso := pointedIso_hom_of_transVC_eq_one hVC
  -- pointedIso = Q'.e.inv ≫ (Q.restrict h).e.hom ⟹ the chart isos compare
  have hE : (Q.restrict h).e.hom =
      Q'.e.hom ≫ eqToHom (congrArg projModel hWeq.symm) := by
    have h1 : Q'.e.inv ≫ (Q.restrict h).e.hom =
        eqToHom (congrArg projModel hWeq.symm) := by
      have h0 := hIso
      rw [show (Q'.pointedIso (Q.restrict h)).hom =
        Q'.e.inv ≫ (Q.restrict h).e.hom from rfl] at h0
      exact h0
    rw [← h1, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  -- the coefficient rings compose
  have hσ : ((Y.base.presheaf.map (homOfLE (le_top : O'.1 ≤ ⊤)).op).hom).comp
      (classifyingRingHom Y b h2 h3) =
    (sectionsMapLE (𝟙 Y.base) h).comp
      (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3)) := by
    rw [sectionsMapLE_id]
    show ((Y.base.presheaf.map (homOfLE (le_top : O'.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3) =
      (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op) ≫
        (Y.base.presheaf.map (homOfLE (show O'.1 ≤ V.1 by simpa using h)).op)).hom).comp
        (classifyingRingHom Y b h2 h3)
    rw [← Functor.map_comp, ← op_comp]
    rfl
  -- assemble
  rw [chartPiece, chartPiece, ← Category.assoc, ← restrict_e_baseChange, hE]
  simp only [Category.assoc]
  rw [cancel_epi (Q'.e.hom)]
  rw [projModelBaseChange_congr'' (sectionsMapLE (𝟙 Y.base) h)
      (universalShortNF_map_classifying Y b h2 h3 V i hVi).symm]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]
  rw [← projModelBaseChange_comp',
    projModelBaseChange_congr_hom hσ.symm (universalShortNF R),
    ← Category.assoc, eqToHom_trans]


open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(E12-D3-E3c)** The piece map does not depend on the chart supporting the affine:
adapted uniqueness at the shared affine. -/
theorem chartPiece_index_congr {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤)))
    (V : Y.base.affineOpens) (i₁ i₂ : Y.curve.toEllipticCurveGeom.atlas.ι)
    (h₁ : V.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U i₁).1)
    (h₂ : V.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U i₂).1) :
    chartPiece Y b h2 h3 V i₁ h₁ = chartPiece Y b h2 h3 V i₂ h₂ := by
  set Q₁ := adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i₁ h₁ with hQ₁
  set Q₂ := adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i₂ h₂ with hQ₂
  have hVC : Q₂.transVC Q₁ = 1 :=
    transVC_eq_one_of_isAdapted
      (adaptedLocal_isAdapted Y.curve.toEllipticCurveGeom b h2 h3 V i₂ h₂)
      (adaptedLocal_isAdapted Y.curve.toEllipticCurveGeom b h2 h3 V i₁ h₁)
      (adaptedLocal_isShortNF Y.curve.toEllipticCurveGeom b h2 h3 V i₂ h₂)
      (adaptedLocal_isShortNF Y.curve.toEllipticCurveGeom b h2 h3 V i₁ h₁)
      (isUnit_ofNat_res h2 V.1) (isUnit_ofNat_res h3 V.1)
  have hWeq : Q₁.W = Q₂.W := by
    have := Q₂.transVC_smul Q₁
    rwa [hVC, one_smul] at this
  have hIso := pointedIso_hom_of_transVC_eq_one hVC
  have hE : Q₁.e.hom = Q₂.e.hom ≫ eqToHom (congrArg projModel hWeq.symm) := by
    have h1 : Q₂.e.inv ≫ Q₁.e.hom = eqToHom (congrArg projModel hWeq.symm) := by
      have h0 := hIso
      rw [show (Q₂.pointedIso Q₁).hom = Q₂.e.inv ≫ Q₁.e.hom from rfl] at h0
      exact h0
    rw [← h1, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [chartPiece, chartPiece, hE]
  simp only [Category.assoc]
  rw [cancel_epi (Q₂.e.hom)]
  simp only [eqToHom_trans_assoc]


open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
/-- **(E12-D3-E3d)** The cover of the total space by the chart-supported affine
pieces. -/
noncomputable def adaptedTotalCover {R : CommRingCat.{u}} (Y : EllObj R) :
    Y.curve.toEllipticCurveGeom.E.OpenCover :=
  Scheme.Cover.mkOfCovers
    {p : Y.base.affineOpens × Y.curve.toEllipticCurveGeom.atlas.ι //
      p.1.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U p.2).1}
    (fun p => pullback Y.curve.toEllipticCurveGeom.π p.1.1.1.ι)
    (fun p => pullback.fst Y.curve.toEllipticCurveGeom.π p.1.1.1.ι)
    (fun x => by
      obtain ⟨i, hxi⟩ := Y.curve.toEllipticCurveGeom.atlas.covers
        (Y.curve.toEllipticCurveGeom.π.base x)
      obtain ⟨V₀, hVaff, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset
        (show Y.curve.toEllipticCurveGeom.π.base x ∈
          (Y.curve.toEllipticCurveGeom.atlas.U i).1 from hxi)
      have hx : x ∈ Set.range (pullback.fst Y.curve.toEllipticCurveGeom.π
          (⟨V₀, hVaff⟩ : Y.base.affineOpens).1.ι).base := by
        rw [Scheme.Pullback.range_fst, Set.mem_preimage, Scheme.Opens.range_ι,
          SetLike.mem_coe]
        exact hxV
      obtain ⟨y, hy⟩ := hx
      exact ⟨⟨⟨⟨V₀, hVaff⟩, i⟩, hVle⟩, y, hy⟩)

open CategoryTheory Limits in
@[simp] theorem adaptedTotalCover_f {R : CommRingCat.{u}} (Y : EllObj R)
    (p : {p : Y.base.affineOpens × Y.curve.toEllipticCurveGeom.atlas.ι //
      p.1.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U p.2).1}) :
    (adaptedTotalCover Y).f p =
      pullback.fst Y.curve.toEllipticCurveGeom.π p.1.1.1.ι := rfl


open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(E12-D3-E3d)** The classifying pieces agree on overlaps: refine the fibre
product by common affines; per-affine two restrictions plus the index congruence. -/
private theorem chartPiece_agree {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤)))
    (p q : {p : Y.base.affineOpens × Y.curve.toEllipticCurveGeom.atlas.ι //
      p.1.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U p.2).1}) :
    pullback.fst ((adaptedTotalCover Y).f p) ((adaptedTotalCover Y).f q) ≫
        chartPiece Y b h2 h3 p.1.1 p.1.2 p.2 =
      pullback.snd ((adaptedTotalCover Y).f p) ((adaptedTotalCover Y).f q) ≫
        chartPiece Y b h2 h3 q.1.1 q.1.2 q.2 := by
  haveI hOIp : IsOpenImmersion ((adaptedTotalCover Y).f p) := by
    rw [adaptedTotalCover_f]; infer_instance
  haveI hOIq : IsOpenImmersion ((adaptedTotalCover Y).f q) := by
    rw [adaptedTotalCover_f]; infer_instance
  -- pointwise choice of a common affine below both charts' affines
  have hchoice : ∀ z : (pullback ((adaptedTotalCover Y).f p)
      ((adaptedTotalCover Y).f q) : Scheme.{u}),
      ∃ (W : Y.base.affineOpens), W.1 ≤ p.1.1.1 ⊓ q.1.1.1 ∧
        Y.curve.toEllipticCurveGeom.π.base
          ((pullback.fst ((adaptedTotalCover Y).f p) ((adaptedTotalCover Y).f q) ≫
            (adaptedTotalCover Y).f p).base z) ∈ W.1 := by
    intro z
    have hsp : Y.curve.toEllipticCurveGeom.π.base
        ((pullback.fst ((adaptedTotalCover Y).f p) ((adaptedTotalCover Y).f q) ≫
          (adaptedTotalCover Y).f p).base z) ∈ p.1.1.1 := by
      have hr : ((pullback.fst ((adaptedTotalCover Y).f p)
          ((adaptedTotalCover Y).f q) ≫ (adaptedTotalCover Y).f p).base z) ∈
          Set.range (pullback.fst Y.curve.toEllipticCurveGeom.π p.1.1.1.ι).base :=
        ⟨(pullback.fst ((adaptedTotalCover Y).f p)
          ((adaptedTotalCover Y).f q)).base z, rfl⟩
      rw [Scheme.Pullback.range_fst] at hr
      simpa [Scheme.Opens.range_ι] using hr
    have hcond : (pullback.fst ((adaptedTotalCover Y).f p)
        ((adaptedTotalCover Y).f q) ≫ (adaptedTotalCover Y).f p).base z =
      (pullback.snd ((adaptedTotalCover Y).f p) ((adaptedTotalCover Y).f q) ≫
        (adaptedTotalCover Y).f q).base z := by
      have := congrArg (fun t => t.base z) (pullback.condition
        (f := (adaptedTotalCover Y).f p) (g := (adaptedTotalCover Y).f q))
      simpa using this
    have hsq : Y.curve.toEllipticCurveGeom.π.base
        ((pullback.fst ((adaptedTotalCover Y).f p) ((adaptedTotalCover Y).f q) ≫
          (adaptedTotalCover Y).f p).base z) ∈ q.1.1.1 := by
      have hr : ((pullback.fst ((adaptedTotalCover Y).f p)
          ((adaptedTotalCover Y).f q) ≫ (adaptedTotalCover Y).f p).base z) ∈
          Set.range (pullback.fst Y.curve.toEllipticCurveGeom.π q.1.1.1.ι).base := by
        rw [hcond]
        exact ⟨(pullback.snd ((adaptedTotalCover Y).f p)
          ((adaptedTotalCover Y).f q)).base z, rfl⟩
      rw [Scheme.Pullback.range_fst] at hr
      simpa [Scheme.Opens.range_ι] using hr
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset
      (show Y.curve.toEllipticCurveGeom.π.base
        ((pullback.fst ((adaptedTotalCover Y).f p) ((adaptedTotalCover Y).f q) ≫
          (adaptedTotalCover Y).f p).base z) ∈ p.1.1.1 ⊓ q.1.1.1 from ⟨hsp, hsq⟩)
    exact ⟨⟨W₀, hWaff⟩, hWle, hxW⟩
  choose W hWle hmem using hchoice
  -- the piece-inclusions into the fibre product
  have hfsteq : ∀ z, (restrictTheta (G := Y.curve.toEllipticCurveGeom)
      ((hWle z).trans inf_le_left) ≫ (adaptedTotalCover Y).f p) =
    restrictTheta ((hWle z).trans inf_le_right) ≫ (adaptedTotalCover Y).f q := by
    intro z
    rw [adaptedTotalCover_f, adaptedTotalCover_f, restrictTheta_fst, restrictTheta_fst]
  let hω : ∀ z, (pullback Y.curve.toEllipticCurveGeom.π (W z).1.ι : Scheme.{u}) ⟶
      pullback ((adaptedTotalCover Y).f p) ((adaptedTotalCover Y).f q) := fun z =>
    pullback.lift (restrictTheta ((hWle z).trans inf_le_left))
      (restrictTheta ((hWle z).trans inf_le_right)) (hfsteq z)
  -- each inclusion is an open immersion (cancel against the composite into `E`)
  have hcomp : ∀ z, hω z ≫ pullback.fst ((adaptedTotalCover Y).f p)
      ((adaptedTotalCover Y).f q) ≫ (adaptedTotalCover Y).f p =
    pullback.fst Y.curve.toEllipticCurveGeom.π (W z).1.ι := by
    intro z
    rw [← Category.assoc, show hω z ≫ pullback.fst ((adaptedTotalCover Y).f p)
        ((adaptedTotalCover Y).f q) =
      restrictTheta ((hWle z).trans inf_le_left) from pullback.lift_fst _ _ _,
      adaptedTotalCover_f, restrictTheta_fst]
  have hmapOI : ∀ z, IsOpenImmersion (hω z) := by
    intro z
    haveI : IsOpenImmersion (pullback.fst ((adaptedTotalCover Y).f p)
        ((adaptedTotalCover Y).f q) ≫ (adaptedTotalCover Y).f p) := inferInstance
    haveI : IsOpenImmersion (hω z ≫ pullback.fst ((adaptedTotalCover Y).f p)
        ((adaptedTotalCover Y).f q) ≫ (adaptedTotalCover Y).f p) := by
      rw [hcomp z]; infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.fst ((adaptedTotalCover Y).f p)
      ((adaptedTotalCover Y).f q) ≫ (adaptedTotalCover Y).f p)
  -- the refining cover and the extension argument
  refine (Scheme.Cover.mkOfCovers
    (X := (pullback ((adaptedTotalCover Y).f p) ((adaptedTotalCover Y).f q) :
      Scheme.{u}))
    (pullback ((adaptedTotalCover Y).f p) ((adaptedTotalCover Y).f q) : Scheme.{u})
    (fun z => pullback Y.curve.toEllipticCurveGeom.π (W z).1.ι)
    (fun z => hω z) ?_ (fun z => hmapOI z)).hom_ext _ _ (fun z => ?_)
  · -- covers, via injectivity of the open-immersion composite into `E`
    intro z
    have hz : (pullback.fst ((adaptedTotalCover Y).f p)
        ((adaptedTotalCover Y).f q) ≫ (adaptedTotalCover Y).f p).base z ∈
      Set.range (pullback.fst Y.curve.toEllipticCurveGeom.π (W z).1.ι).base := by
      rw [Scheme.Pullback.range_fst]
      simpa [Scheme.Opens.range_ι] using hmem z
    obtain ⟨w, hw⟩ := hz
    refine ⟨z, w, ?_⟩
    have hinj : Function.Injective
        ((pullback.fst ((adaptedTotalCover Y).f p) ((adaptedTotalCover Y).f q) ≫
          (adaptedTotalCover Y).f p).base) :=
      (pullback.fst ((adaptedTotalCover Y).f p) ((adaptedTotalCover Y).f q) ≫
        (adaptedTotalCover Y).f p).isOpenEmbedding.injective
    apply hinj
    calc (pullback.fst ((adaptedTotalCover Y).f p) ((adaptedTotalCover Y).f q) ≫
          (adaptedTotalCover Y).f p).base ((hω z).base w)
        = (hω z ≫ pullback.fst ((adaptedTotalCover Y).f p)
            ((adaptedTotalCover Y).f q) ≫ (adaptedTotalCover Y).f p).base w := rfl
      _ = (pullback.fst Y.curve.toEllipticCurveGeom.π (W z).1.ι).base w := by
          rw [hcomp z]
      _ = _ := hw
  · -- per-piece agreement: two restrictions + the index congruence
    show hω z ≫ pullback.fst _ _ ≫ chartPiece Y b h2 h3 p.1.1 p.1.2 p.2 =
      hω z ≫ pullback.snd _ _ ≫ chartPiece Y b h2 h3 q.1.1 q.1.2 q.2
    rw [← Category.assoc, show hω z ≫ pullback.fst ((adaptedTotalCover Y).f p)
        ((adaptedTotalCover Y).f q) =
      restrictTheta ((hWle z).trans inf_le_left) from pullback.lift_fst _ _ _,
      ← Category.assoc, show hω z ≫ pullback.snd ((adaptedTotalCover Y).f p)
        ((adaptedTotalCover Y).f q) =
      restrictTheta ((hWle z).trans inf_le_right) from pullback.lift_snd _ _ _,
      chartPiece_restrict Y b h2 h3 p.1.1 p.1.2 p.2 ((hWle z).trans inf_le_left),
      chartPiece_restrict Y b h2 h3 q.1.1 q.1.2 q.2 ((hWle z).trans inf_le_right),
      chartPiece_index_congr Y b h2 h3 (W z) p.1.2 q.1.2
        (((hWle z).trans inf_le_left).trans p.2)
        (((hWle z).trans inf_le_right).trans q.2)]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
/-- **(E12-D3 ★★)** The classifying morphism upstairs: the chart-glued map from the
total space to the universal projective model — GME Thm 2.2.3's universal comparison. -/
noncomputable def classifyingTop {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤))) :
    Y.curve.toEllipticCurveGeom.E ⟶ projModel (universalShortNF R) :=
  (adaptedTotalCover Y).glueMorphisms
    (fun p => chartPiece Y b h2 h3 p.1.1 p.1.2 p.2)
    (chartPiece_agree Y b h2 h3)

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
@[reassoc]
theorem classifyingTop_piece {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤)))
    (p : {p : Y.base.affineOpens × Y.curve.toEllipticCurveGeom.atlas.ι //
      p.1.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U p.2).1}) :
    (adaptedTotalCover Y).f p ≫ classifyingTop Y b h2 h3 =
      chartPiece Y b h2 h3 p.1.1 p.1.2 p.2 :=
  (adaptedTotalCover Y).ι_glueMorphisms _ _ p


open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(E12-D3-E4)** The glued comparison lies over the classifying map: the base
square of the classifying `EllHom` commutes. -/
theorem classifyingTop_π_w {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤))) :
    classifyingTop Y b h2 h3 ≫ projModelπ (universalShortNF R) =
      Y.curve.toEllipticCurveGeom.π ≫ classifyingMap Y b h2 h3 := by
  refine (adaptedTotalCover Y).hom_ext _ _ (fun p => ?_)
  rw [← Category.assoc, classifyingTop_piece, chartPiece_π]
  have hsplit : Spec.map (CommRingCat.ofHom
      (((Y.base.presheaf.map (homOfLE (le_top : p.1.1.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3))) =
    Spec.map (Y.base.presheaf.map (homOfLE (le_top : p.1.1.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (classifyingRingHom Y b h2 h3)) := by
    rw [← Spec.map_comp]
    rfl
  rw [hsplit,
    show p.1.1.2.isoSpec.hom = p.1.1.1.toSpecΓ from IsAffineOpen.isoSpec_hom _]
  rw [show p.1.1.1.toSpecΓ ≫
      Spec.map (Y.base.presheaf.map (homOfLE (le_top : p.1.1.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (classifyingRingHom Y b h2 h3)) =
    (p.1.1.1.ι ≫ Y.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (classifyingRingHom Y b h2 h3)) from by
    rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]]
  rw [show (p.1.1.1.ι ≫ Y.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (classifyingRingHom Y b h2 h3)) =
    p.1.1.1.ι ≫ classifyingMap Y b h2 h3 from by
    rw [Category.assoc]; rfl]
  rw [← Category.assoc, ← pullback.condition, Category.assoc, adaptedTotalCover_f]


open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
/-- **(E12-D3-E4)** The cover of the base by the chart-supported affines. -/
noncomputable def adaptedBaseCover {R : CommRingCat.{u}} (Y : EllObj R) :
    Y.base.OpenCover :=
  Scheme.Cover.mkOfCovers
    {p : Y.base.affineOpens × Y.curve.toEllipticCurveGeom.atlas.ι //
      p.1.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U p.2).1}
    (fun p => p.1.1.1.toScheme)
    (fun p => p.1.1.1.ι)
    (fun x => by
      obtain ⟨i, hxi⟩ := Y.curve.toEllipticCurveGeom.atlas.covers x
      obtain ⟨V₀, hVaff, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (Y.curve.toEllipticCurveGeom.atlas.U i).1 from hxi)
      exact ⟨⟨⟨⟨V₀, hVaff⟩, i⟩, hVle⟩, ⟨x, hxV⟩, rfl⟩)

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(E12-D3-E4)** The glued comparison respects the zero sections. -/
theorem classifyingTop_zero {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤))) :
    Y.curve.toEllipticCurveGeom.zero ≫ classifyingTop Y b h2 h3 =
      classifyingMap Y b h2 h3 ≫ projModelZero (universalShortNF R) := by
  refine (adaptedBaseCover Y).hom_ext _ _ (fun p => ?_)
  set Q := adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 p.1.1 p.1.2 p.2 with hQ
  -- the zero section factors through the piece
  have hzfac : p.1.1.1.ι ≫ Y.curve.toEllipticCurveGeom.zero =
      pullback.lift (p.1.1.1.ι ≫ Y.curve.toEllipticCurveGeom.zero) (𝟙 _)
        (by rw [Category.assoc, Y.curve.toEllipticCurveGeom.zero_π,
          Category.comp_id, Category.id_comp]) ≫
      (adaptedTotalCover Y).f p := by
    rw [adaptedTotalCover_f, pullback.lift_fst]
  rw [show (adaptedBaseCover Y).f p = p.1.1.1.ι from rfl, ← Category.assoc, hzfac,
    Category.assoc, classifyingTop_piece]
  -- the chart zero-compatibility
  have hz := Q.compat_zero
  have hlift : pullback.lift (p.1.1.1.ι ≫ Y.curve.toEllipticCurveGeom.zero) (𝟙 _)
      (by rw [Category.assoc, Y.curve.toEllipticCurveGeom.zero_π,
        Category.comp_id, Category.id_comp]) ≫ Q.e.hom =
    p.1.1.2.isoSpec.hom ≫ projModelZero Q.W := by
    rw [← Iso.inv_comp_eq, ← Category.assoc]
    exact hz
  rw [chartPiece, ← Category.assoc, hlift]
  -- transport the zero through the coefficient match and the base change
  rw [Category.assoc,
    show projModelZero Q.W = projModelZero ((universalShortNF R).map
        (((Y.base.presheaf.map (homOfLE (le_top : p.1.1.1 ≤ ⊤)).op).hom).comp
          (classifyingRingHom Y b h2 h3))) ≫
      eqToHom (congrArg projModel
        (universalShortNF_map_classifying Y b h2 h3 p.1.1 p.1.2 p.2)) from
      projModelZero_congr
        (universalShortNF_map_classifying Y b h2 h3 p.1.1 p.1.2 p.2).symm]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  -- the base-change square of the zero section
  have hbc : projModelZero ((universalShortNF R).map
      (((Y.base.presheaf.map (homOfLE (le_top : p.1.1.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3))) ≫
      projModelBaseChange
        (((Y.base.presheaf.map (homOfLE (le_top : p.1.1.1 ≤ ⊤)).op).hom).comp
          (classifyingRingHom Y b h2 h3)) (universalShortNF R) =
    Spec.map (CommRingCat.ofHom
      (((Y.base.presheaf.map (homOfLE (le_top : p.1.1.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3))) ≫ projModelZero (universalShortNF R) := by
    letI : Algebra (ModuliRingE12 R) Γ(Y.base, p.1.1.1) :=
      ((((Y.base.presheaf.map (homOfLE (le_top : p.1.1.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3))).toAlgebra
    exact projModelZero_baseChange (universalShortNF R)
  rw [hbc]
  -- the Γ–Spec triangle, as in the π-square
  have hsplit : Spec.map (CommRingCat.ofHom
      (((Y.base.presheaf.map (homOfLE (le_top : p.1.1.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3))) =
    Spec.map (Y.base.presheaf.map (homOfLE (le_top : p.1.1.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (classifyingRingHom Y b h2 h3)) := by
    rw [← Spec.map_comp]
    rfl
  rw [← Category.assoc, hsplit,
    show p.1.1.2.isoSpec.hom = p.1.1.1.toSpecΓ from IsAffineOpen.isoSpec_hom _]
  rw [show p.1.1.1.toSpecΓ ≫
      Spec.map (Y.base.presheaf.map (homOfLE (le_top : p.1.1.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (classifyingRingHom Y b h2 h3)) =
    (p.1.1.1.ι ≫ Y.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (classifyingRingHom Y b h2 h3)) from by
    rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]]
  rw [show (p.1.1.1.ι ≫ Y.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (classifyingRingHom Y b h2 h3)) =
    p.1.1.1.ι ≫ classifyingMap Y b h2 h3 from by rw [Category.assoc]; rfl]
  simp only [Category.assoc]


open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D3-E4)** The classifying map restricted to a chart-supported affine is the
`Spec` of the restricted classifying algebra. -/
theorem restrict_classifyingMap {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤)))
    (V : Y.base.affineOpens) :
    V.1.ι ≫ classifyingMap Y b h2 h3 =
      V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
          (classifyingRingHom Y b h2 h3))) := by
  have hsplit : Spec.map (CommRingCat.ofHom
      (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3))) =
    Spec.map (Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (classifyingRingHom Y b h2 h3)) := by
    rw [← Spec.map_comp]
    rfl
  rw [hsplit, show V.2.isoSpec.hom = V.1.toSpecΓ from IsAffineOpen.isoSpec_hom _,
    ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top, Category.assoc]
  rfl


open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(E12-D3-E4)** The per-chart classifying square is cartesian: the chart
isomorphism square pasted with the model base-change square. -/
theorem chartPiece_isPullback {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤)))
    (V : Y.base.affineOpens) (i : Y.curve.toEllipticCurveGeom.atlas.ι)
    (hVi : V.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U i).1) :
    IsPullback (chartPiece Y b h2 h3 V i hVi)
      (pullback.snd Y.curve.toEllipticCurveGeom.π V.1.ι)
      (projModelπ (universalShortNF R))
      (V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
          (classifyingRingHom Y b h2 h3)))) := by
  set Q := adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi with hQ
  -- left square: the adapted chart isomorphism (with the coefficient match)
  have hleft : IsPullback
      (Q.e.hom ≫ eqToHom (congrArg projModel
        (universalShortNF_map_classifying Y b h2 h3 V i hVi).symm))
      (pullback.snd Y.curve.toEllipticCurveGeom.π V.1.ι)
      (projModelπ ((universalShortNF R).map
        (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
          (classifyingRingHom Y b h2 h3))))
      V.2.isoSpec.hom := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.assoc, projModelπ_congr
      (universalShortNF_map_classifying Y b h2 h3 V i hVi).symm]
    exact Q.compat_π
  -- right square: the model base change
  have hright : IsPullback
      (projModelBaseChange
        (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
          (classifyingRingHom Y b h2 h3)) (universalShortNF R))
      (projModelπ ((universalShortNF R).map
        (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
          (classifyingRingHom Y b h2 h3))))
      (projModelπ (universalShortNF R))
      (Spec.map (CommRingCat.ofHom
        (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
          (classifyingRingHom Y b h2 h3)))) := by
    letI : Algebra (ModuliRingE12 R) Γ(Y.base, V.1) :=
      ((((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3))).toAlgebra
    exact isPullback_projModelBaseChange (universalShortNF R)
  have hpaste := hleft.paste_horiz hright
  rw [show (Q.e.hom ≫ eqToHom (congrArg projModel
      (universalShortNF_map_classifying Y b h2 h3 V i hVi).symm)) ≫
    projModelBaseChange
      (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3)) (universalShortNF R) =
    chartPiece Y b h2 h3 V i hVi from by
    rw [chartPiece, Category.assoc]] at hpaste
  exact hpaste

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(E12-D3-E4 ★★)** The classifying square is cartesian: `Y` is the pullback of the
universal curve along the classifying map — the universality of GME Thm 2.2.3,
geometric half. -/
theorem isPullback_classifyingTop {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤))) :
    IsPullback (classifyingTop Y b h2 h3) Y.curve.toEllipticCurveGeom.π
      (projModelπ (universalShortNF R)) (classifyingMap Y b h2 h3) := by
  refine (isPullback_of_iSup_eq_top (f := Y.curve.toEllipticCurveGeom.π)
    (g := classifyingTop Y b h2 h3) (h := classifyingMap Y b h2 h3)
    (k := projModelπ (universalShortNF R))
    (classifyingTop_π_w Y b h2 h3).symm
    (ι := {p : Y.base.affineOpens × Y.curve.toEllipticCurveGeom.atlas.ι //
      p.1.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U p.2).1})
    (fun p => p.1.1.1) ?_ (fun p => ?_)).flip
  · -- the chart-supported affines cover the base
    rw [eq_top_iff]
    intro x _
    obtain ⟨i, hxi⟩ := Y.curve.toEllipticCurveGeom.atlas.covers x
    obtain ⟨V₀, hVaff, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (Y.curve.toEllipticCurveGeom.atlas.U i).1 from hxi)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨⟨V₀, hVaff⟩, i⟩, hVle⟩, hxV⟩
  · -- the restricted square, through the piece comparison
    set fpre := (Y.curve.toEllipticCurveGeom.π ⁻¹ᵁ p.1.1.1).ι with hfpre
    -- the comparison from the preimage to the pullback piece
    have hcomm : fpre ≫ Y.curve.toEllipticCurveGeom.π =
        (Y.curve.toEllipticCurveGeom.π ∣_ p.1.1.1) ≫ p.1.1.1.ι :=
      (morphismRestrict_ι Y.curve.toEllipticCurveGeom.π p.1.1.1).symm
    set m := pullback.lift fpre (Y.curve.toEllipticCurveGeom.π ∣_ p.1.1.1) hcomm
      with hm
    have hm₁ : m ≫ pullback.fst Y.curve.toEllipticCurveGeom.π p.1.1.1.ι = fpre :=
      pullback.lift_fst _ _ _
    have hm₂ : m ≫ pullback.snd Y.curve.toEllipticCurveGeom.π p.1.1.1.ι =
        Y.curve.toEllipticCurveGeom.π ∣_ p.1.1.1 :=
      pullback.lift_snd _ _ _
    have hmiso : IsIso m := by
      refine (isPullback_morphismRestrict Y.curve.toEllipticCurveGeom.π
        p.1.1.1).flip.isIso_of_isPullback
        (IsPullback.of_hasPullback Y.curve.toEllipticCurveGeom.π p.1.1.1.ι) m hm₁ hm₂
    -- the m-square pasted with the piece square
    have hmsq : IsPullback m (Y.curve.toEllipticCurveGeom.π ∣_ p.1.1.1)
        (pullback.snd Y.curve.toEllipticCurveGeom.π p.1.1.1.ι) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [hm₂, Category.comp_id]⟩
    have hp := hmsq.paste_horiz (chartPiece_isPullback Y b h2 h3 p.1.1 p.1.2 p.2)
    rw [show m ≫ chartPiece Y b h2 h3 p.1.1 p.1.2 p.2 =
        (Y.curve.toEllipticCurveGeom.π ⁻¹ᵁ p.1.1.1).ι ≫ classifyingTop Y b h2 h3 from by
        rw [← classifyingTop_piece Y b h2 h3 p, adaptedTotalCover_f, ← Category.assoc,
          hm₁],
      show (𝟙 _) ≫ p.1.1.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
          (((Y.base.presheaf.map (homOfLE (le_top : p.1.1.1 ≤ ⊤)).op).hom).comp
            (classifyingRingHom Y b h2 h3))) =
        p.1.1.1.ι ≫ classifyingMap Y b h2 h3 from by
        rw [Category.id_comp, ← restrict_classifyingMap]] at hp
    exact hp.flip


open AlgebraicGeometry CategoryTheory Scheme in
/-- **(E12-D4)** The universal `Ell/R`-object: `M₁ = Spec R[A₄,A₆][Δ⁻¹]` carrying the
universal short-normal-form curve. -/
noncomputable def universalEllObj (R : CommRingCat.{u}) : EllObj R where
  base := Spec (CommRingCat.of (ModuliRingE12 R))
  structMap := Spec.map (CommRingCat.ofHom (algebraMap R (ModuliRingE12 R)))
  curve := modelEllipticCurve (universalShortNF R)

open AlgebraicGeometry CategoryTheory Scheme MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D4)** The classifying algebra restricts to the structure algebra on `R`. -/
theorem classifyingRingHom_algebraMap {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤))) (r : R) :
    classifyingRingHom Y b h2 h3 (algebraMap R (ModuliRingE12 R) r) =
      Y.baseRingHom r := by
  have h1 : (algebraMap R (ModuliRingE12 R) r) =
      algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (C r) := by
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) (ModuliRingE12 R)]
    rfl
  rw [h1, classifyingRingHom, IsLocalization.Away.lift_eq]
  simp

open AlgebraicGeometry CategoryTheory Scheme in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(E12-D4)** The classifying map lies over `Spec R`. -/
theorem classifyingMap_structMap {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤))) :
    classifyingMap Y b h2 h3 ≫ (universalEllObj R).structMap = Y.structMap := by
  show (Y.base.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (classifyingRingHom Y b h2 h3))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (ModuliRingE12 R))) = Y.structMap
  rw [Category.assoc, ← Spec.map_comp,
    show CommRingCat.ofHom (algebraMap R (ModuliRingE12 R)) ≫
        CommRingCat.ofHom (classifyingRingHom Y b h2 h3) =
      CommRingCat.ofHom (Y.baseRingHom) from by
      ext r
      exact classifyingRingHom_algebraMap Y b h2 h3 r,
    show CommRingCat.ofHom Y.baseRingHom =
      (Scheme.ΓSpecIso R).inv ≫ Y.structMap.appTop from rfl,
    Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom R,
    ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  exact Category.comp_id _


open AlgebraicGeometry CategoryTheory Scheme in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D4 ★★)** The classifying morphism of an `(E, ω)`-datum in `Ell/R`:
GME Thm 2.2.3's universal property, forward direction. -/
noncomputable def classifyingEllHom {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤))) :
    Y ⟶ universalEllObj R where
  baseHom := classifyingMap Y b h2 h3
  base_w := classifyingMap_structMap Y b h2 h3
  top := classifyingTop Y b h2 h3
  isPullback := isPullback_classifyingTop Y b h2 h3
  zero_w := classifyingTop_zero Y b h2 h3


open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(E12-D4 bridge)** The basis unit is natural under `Ell/R`-transport: the basis
unit of a transported presentation against the pulled basis is the section-comparison
image of the original basis unit (transport-analogue of `basisUnitAt_restrict`). -/
theorem basisUnitAt_transport {R : CommRingCat.{u}} {Y' Y : EllObj R} (φ : Y' ⟶ Y)
    {V : Y.base.affineOpens}
    (P : LocalPresentation Y.curve.toEllipticCurveGeom V)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    {V' : Y'.base.affineOpens} (hV' : V'.1 ≤ φ.baseHom ⁻¹ᵁ V.1) :
    ((P.transport φ.baseHom φ.top φ.isPullback φ.zero_w hV').basisUnitAt
        (omegaBasisMap φ b)).1 =
      Units.map (sectionsMapLE φ.baseHom hV').toMonoidHom (P.basisUnitAt b).1 := by
  refine Scheme.unit_ext_of_res_cover Y'.base
    (fun i' : Y'.curve.toEllipticCurveGeom.atlas.ι =>
      V'.1 ⊓ (Y'.curve.toEllipticCurveGeom.atlas.U i').1) (fun i' => inf_le_left)
    (fun x hxV => by
      obtain ⟨i', hxi⟩ := Y'.curve.toEllipticCurveGeom.atlas.covers x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i', hxV, hxi⟩) (fun i' => ?_)
  rw [((P.transport φ.baseHom φ.top φ.isPullback φ.zero_w hV').basisUnitAt
    (omegaBasisMap φ b)).2 i']
  refine Scheme.unit_ext_of_affine_res Y'.base (fun W' hW' => ?_)
  rw [((P.transport φ.baseHom φ.top φ.isPullback φ.zero_w hV').basisUnitOn
    (omegaBasisMap φ b) i').2 W' hW']
  -- pointwise choice: a Y-chart at the image point and factoring affines
  have hchoice : ∀ w : W'.1, ∃ (j : Y.curve.toEllipticCurveGeom.atlas.ι)
      (WS : Y.base.affineOpens) (T : Y'.base.affineOpens),
      WS.1 ≤ V.1 ⊓ (Y.curve.toEllipticCurveGeom.atlas.U j).1 ∧
      w.1 ∈ T.1 ∧ T.1 ≤ W'.1 ∧ T.1 ≤ φ.baseHom ⁻¹ᵁ WS.1 := by
    intro w
    obtain ⟨j, hj⟩ := Y.curve.toEllipticCurveGeom.atlas.covers (φ.baseHom.base w.1)
    have hwV : φ.baseHom.base w.1 ∈ V.1 := hV' ((hW' w.2).1)
    obtain ⟨WS₀, hWSaff, hfw, hWSle⟩ := exists_isAffineOpen_mem_and_subset
      (show φ.baseHom.base w.1 ∈ V.1 ⊓ (Y.curve.toEllipticCurveGeom.atlas.U j).1 from
        ⟨hwV, hj⟩)
    obtain ⟨T₀, hTaff, hwT, hTle⟩ := exists_isAffineOpen_mem_and_subset
      (show w.1 ∈ W'.1 ⊓ (φ.baseHom ⁻¹ᵁ WS₀) from ⟨w.2, hfw⟩)
    exact ⟨j, ⟨WS₀, hWSaff⟩, ⟨T₀, hTaff⟩, hWSle, hwT,
      hTle.trans inf_le_left, hTle.trans inf_le_right⟩
  choose j WS T hWS hwT hTW' hTpre using hchoice
  refine Scheme.unit_ext_of_res_cover Y'.base (fun w : W'.1 => (T w).1) hTW'
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hwT ⟨x, hx⟩⟩)
    (fun w => ?_)
  rw [Scheme.resUnit_resUnit, Scheme.resUnit_resUnit, map_mul]
  -- RHS: through the appLE-commutation and the Y-side glue spec at `WS w`
  have hRHS : Scheme.resUnit (((hTW' w).trans hW').trans inf_le_left)
      (Units.map (sectionsMapLE φ.baseHom hV').toMonoidHom (P.basisUnitAt b).1) =
    Units.map ((φ.baseHom.appLE (WS w).1 (T w).1 (hTpre w)).hom).toMonoidHom
      (Scheme.resUnit (show (WS w).1 ≤ V.1 from (hWS w).trans inf_le_left)
        (P.basisUnitAt b).1) := by
    rw [show Units.map (sectionsMapLE φ.baseHom hV').toMonoidHom (P.basisUnitAt b).1 =
      Units.map ((φ.baseHom.appLE V.1 V'.1 hV').hom).toMonoidHom
        (P.basisUnitAt b).1 from rfl,
      Scheme.resUnit_map_appLE,
      ← Scheme.map_appLE_resUnit φ.baseHom
        (show (WS w).1 ≤ V.1 from (hWS w).trans inf_le_left) (hTpre w)]
  rw [hRHS]
  -- the Y-side basis unit at `WS w`, through the specs
  have hYspec : Scheme.resUnit (show (WS w).1 ≤ V.1 from (hWS w).trans inf_le_left)
      (P.basisUnitAt b).1 =
    Scheme.resUnit (le_inf le_top ((hWS w).trans inf_le_right)) (b.2 (j w)).unit *
      ((P.restrict ((hWS w).trans inf_le_left)).transUnit
        ((Y.curve.toEllipticCurveGeom.atlas.presentation (j w)).restrict
          ((hWS w).trans inf_le_right))) := by
    rw [show Scheme.resUnit (show (WS w).1 ≤ V.1 from (hWS w).trans inf_le_left)
        (P.basisUnitAt b).1 =
      Scheme.resUnit (show (WS w).1 ≤ V.1 ⊓
          (Y.curve.toEllipticCurveGeom.atlas.U (j w)).1 from
        le_inf ((hWS w).trans inf_le_left) ((hWS w).trans inf_le_right))
        (Scheme.resUnit (inf_le_left : V.1 ⊓
          (Y.curve.toEllipticCurveGeom.atlas.U (j w)).1 ≤ V.1)
          (P.basisUnitAt b).1) from by rw [Scheme.resUnit_resUnit],
      (P.basisUnitAt b).2 (j w), (P.basisUnitOn b (j w)).2 (WS w)
        (le_inf ((hWS w).trans inf_le_left) ((hWS w).trans inf_le_right))]
  rw [hYspec, map_mul]
  -- LHS comparison factor: push the restriction inside and collapse to `T`-level
  rw [← transUnit_restrict _ _ (hTW' w), transUnit_restrict_restrict_left,
    transUnit_transport_restrict_left, transUnit_restrict_restrict_right]
  -- the transported `Y`-chart at `T`
  have hTj : (T w).1 ≤ φ.baseHom ⁻¹ᵁ
      (Y.curve.toEllipticCurveGeom.atlas.U (j w)).1 :=
    (hTpre w).trans
      ((TopologicalSpace.Opens.map φ.baseHom.base).map
        (homOfLE ((hWS w).trans inf_le_right))).le
  set Pj := (Y.curve.toEllipticCurveGeom.atlas.presentation (j w)).transport
    φ.baseHom φ.top φ.isPullback φ.zero_w hTj with hPj
  -- split the comparison through the transported chart
  have h1 : (P.transport φ.baseHom φ.top φ.isPullback φ.zero_w
      (((hTW' w).trans (hW'.trans inf_le_left)).trans hV')).transUnit
      ((Y'.curve.toEllipticCurveGeom.atlas.presentation i').restrict
        (((hTW' w).trans (hW'.trans inf_le_right)))) =
    (P.transport φ.baseHom φ.top φ.isPullback φ.zero_w
        (((hTW' w).trans (hW'.trans inf_le_left)).trans hV')).transUnit Pj *
    Pj.transUnit ((Y'.curve.toEllipticCurveGeom.atlas.presentation i').restrict
      (((hTW' w).trans (hW'.trans inf_le_right)))) :=
    (transUnit_trans _ _ _).symm
  -- the first factor is the section-comparison image (restrict at `WS`, transport)
  have h3 : (P.transport φ.baseHom φ.top φ.isPullback φ.zero_w
      (((hTW' w).trans (hW'.trans inf_le_left)).trans hV')).transUnit Pj =
    Units.map ((φ.baseHom.appLE (WS w).1 (T w).1 (hTpre w)).hom).toMonoidHom
      ((P.restrict ((hWS w).trans inf_le_left)).transUnit
        ((Y.curve.toEllipticCurveGeom.atlas.presentation (j w)).restrict
          ((hWS w).trans inf_le_right))) := by
    rw [hPj, ← transUnit_restrict_pair_transport φ.baseHom φ.top φ.isPullback
        φ.zero_w P (Y.curve.toEllipticCurveGeom.atlas.presentation (j w))
        ((hWS w).trans inf_le_left) ((hWS w).trans inf_le_right) (hTpre w),
      transUnit_transport]
    rfl
  -- the pulled-basis component: `w_res` + the pulled section through `WS`
  have h2 : Scheme.resUnit (hTW' w)
      (Scheme.resUnit (le_inf le_top (hW'.trans inf_le_right))
        (((omegaBasisMap φ b)).2 i').unit) =
    ((Y'.curve.toEllipticCurveGeom.atlas.presentation i').restrict
        ((hTW' w).trans (hW'.trans inf_le_right))).transUnit Pj *
    Units.map ((φ.baseHom.appLE (WS w).1 (T w).1 (hTpre w)).hom).toMonoidHom
      (Scheme.resUnit (le_inf le_top ((hWS w).trans inf_le_right))
        (b.2 (j w)).unit) := by
    refine Units.ext ?_
    simp only [Units.val_mul, Scheme.resUnit_val, Scheme.resLE_resLE, Units.coe_map,
      MonoidHom.coe_coe]
    rw [show (((omegaBasisMap φ b)).2 i').unit.val = (omegaBasisMap φ b).1.1 i' from
      IsUnit.unit_spec _,
      show ((b.2 (j w)).unit : Γ(Y.base, (⊤ : Y.base.Opens) ⊓
        (omegaCocycle Y.curve.toEllipticCurveGeom).U (j w))) = b.1.1 (j w) from
      IsUnit.unit_spec _]
    -- expand the transported component at `(i', j w)` over `T w`
    have hcomp := congrArg (⇑(Scheme.resLE (X := Y'.base)
      (show (T w).1 ≤ (⊤ : Y'.base.Opens) ⊓
          (omegaCocycle Y'.curve.toEllipticCurveGeom).U i' ⊓
          ((omegaCocycle Y.curve.toEllipticCurveGeom).pullbackCocycle
            φ.baseHom).U (j w) from
        le_inf (le_inf le_top ((hTW' w).trans (hW'.trans inf_le_right)))
          ((hTpre w).trans
            ((TopologicalSpace.Opens.map φ.baseHom.base).map
              (homOfLE ((hWS w).trans inf_le_right))).le))))
      ((omegaCompat φ).transportFun_res
        (((omegaCocycle Y.curve.toEllipticCurveGeom).pullbackCocycle
            φ.baseHom).sectionsMap
          (show (⊤ : Y'.base.Opens) ≤ φ.baseHom ⁻¹ᵁ (⊤ : Y.base.Opens) from
            fun x _ => trivial)
          ((omegaCocycle Y.curve.toEllipticCurveGeom).sectionsPullback
            φ.baseHom b.1)) i' (j w))
    simp only [Scheme.resUnit_val, Scheme.resLE_resLE, map_mul] at hcomp
    show Scheme.resLE (hTW' w) (Scheme.resLE (le_inf le_top (hW'.trans inf_le_right))
        (((omegaCompat φ).transportFun
          (((omegaCocycle Y.curve.toEllipticCurveGeom).pullbackCocycle
              φ.baseHom).sectionsMap
            (show (⊤ : Y'.base.Opens) ≤ φ.baseHom ⁻¹ᵁ (⊤ : Y.base.Opens) from
              fun x _ => trivial)
            ((omegaCocycle Y.curve.toEllipticCurveGeom).sectionsPullback
              φ.baseHom b.1))).1 i')) =
      (((Y'.curve.toEllipticCurveGeom.atlas.presentation i').restrict
          ((hTW' w).trans (hW'.trans inf_le_right))).transUnit Pj).val *
      (φ.baseHom.appLE (WS w).1 (T w).1 (hTpre w)).hom
        (Scheme.resLE (le_inf le_top ((hWS w).trans inf_le_right)) (b.1.1 (j w)))
    erw [Scheme.resLE_resLE]
    refine Eq.trans hcomp ?_
    -- identify the two factors
    refine congrArg₂ (· * ·) ?_ ?_
    · -- the `w`-factor is the transition unit `w_res`
      have hw := congrArg Units.val (omegaCompat_w_res φ i' (j w) (T w)
        (le_inf ((hTW' w).trans (hW'.trans inf_le_right))
          ((hTpre w).trans
            ((TopologicalSpace.Opens.map φ.baseHom.base).map
              (homOfLE ((hWS w).trans inf_le_right))).le)))
      simp only [Scheme.resUnit_val] at hw
      rw [show Scheme.resLE (X := Y'.base) _ ((omegaCompat φ).w i' (j w)).val =
        (((Y'.curve.toEllipticCurveGeom.atlas.presentation i').restrict
            ((hTW' w).trans (hW'.trans inf_le_right))).transUnit Pj).val from hw]
    · -- the pulled component through `WS`
      erw [Scheme.resLE_resLE, Scheme.resLE_appLE]
      exact (Scheme.appLE_resLE φ.baseHom
        (le_inf le_top ((hWS w).trans inf_le_right)) _ _).symm
  -- assemble
  rw [h1, h3, h2]
  rw [mul_mul_mul_comm]
  have hcancel : ((Y'.curve.toEllipticCurveGeom.atlas.presentation i').restrict
        ((hTW' w).trans (hW'.trans inf_le_right))).transUnit Pj *
      Pj.transUnit ((Y'.curve.toEllipticCurveGeom.atlas.presentation i').restrict
        ((hTW' w).trans (hW'.trans inf_le_right))) = 1 := by
    rw [transUnit_trans, transUnit_self]
  have hc := congrArg Units.val hcancel
  refine Units.ext ?_
  simp only [Units.val_mul, Units.val_one] at hc ⊢
  linear_combination
    ((Units.map ((φ.baseHom.appLE (WS w).1 (T w).1 (hTpre w)).hom).toMonoidHom
      ((P.restrict ((hWS w).trans inf_le_left)).transUnit
        ((Y.curve.toEllipticCurveGeom.atlas.presentation (j w)).restrict
          ((hWS w).trans inf_le_right)))).val *
     (Units.map ((φ.baseHom.appLE (WS w).1 (T w).1 (hTpre w)).hom).toMonoidHom
      (Scheme.resUnit (le_inf le_top ((hWS w).trans inf_le_right))
        (b.2 (j w)).unit)).val) * hc


open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D4)** Adaptedness is stable under `Ell/R`-transport. -/
theorem IsAdapted.transport {R : CommRingCat.{u}} {Y' Y : EllObj R} (φ : Y' ⟶ Y)
    {V : Y.base.affineOpens}
    {P : LocalPresentation Y.curve.toEllipticCurveGeom V}
    {b : OmegaBasis Y.curve.toEllipticCurveGeom} (hP : P.IsAdapted b)
    {V' : Y'.base.affineOpens} (hV' : V'.1 ≤ φ.baseHom ⁻¹ᵁ V.1) :
    (P.transport φ.baseHom φ.top φ.isPullback φ.zero_w hV').IsAdapted
      (omegaBasisMap φ b) := by
  show ((P.transport φ.baseHom φ.top φ.isPullback φ.zero_w hV').basisUnitAt
    (omegaBasisMap φ b)).1 = 1
  rw [basisUnitAt_transport φ P b hV', hP, map_one]


open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(E12-D4 rt1)** The section comparison of the classifying map is the restricted
classifying algebra (`Spec`-side determination through `restrict_classifyingMap`). -/
theorem sectionsMapLE_classifyingMap {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤)))
    (V : Y.base.affineOpens) (hTop : V.1 ≤ classifyingMap Y b h2 h3 ⁻¹ᵁ
      (⊤ : (Spec (CommRingCat.of (ModuliRingE12 R))).Opens)) :
    (sectionsMapLE (classifyingMap Y b h2 h3) hTop).comp
      ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom) =
    ((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (classifyingRingHom Y b h2 h3) := by
  have hL : V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      ((sectionsMapLE (classifyingMap Y b h2 h3) hTop).comp
        ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom))) =
    V.1.ι ≫ classifyingMap Y b h2 h3 := by
    rw [show CommRingCat.ofHom
        ((sectionsMapLE (classifyingMap Y b h2 h3) hTop).comp
          ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom)) =
      (Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv ≫
        (classifyingMap Y b h2 h3).appLE ⊤ V.1 hTop from rfl,
      Spec.map_comp,
      show V.2.isoSpec.hom = V.1.toSpecΓ from IsAffineOpen.isoSpec_hom _,
      ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc]
    rw [show (⊤ : (Spec (CommRingCat.of (ModuliRingE12 R))).Opens).toSpecΓ ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv =
      (⊤ : (Spec (CommRingCat.of (ModuliRingE12 R))).Opens).ι from by
      rw [Scheme.Opens.toSpecΓ_top, Category.assoc, ← SpecMap_ΓSpecIso_hom,
        ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]]
    rw [Scheme.Hom.resLE_comp_ι]
  have hR : V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      (((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3))) =
    V.1.ι ≫ classifyingMap Y b h2 h3 :=
    (restrict_classifyingMap Y b h2 h3 V).symm
  have hSpec := hL.trans hR.symm
  rw [cancel_epi] at hSpec
  have hofHom := Spec.map_injective hSpec
  exact congrArg CommRingCat.Hom.hom hofHom


open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(E12-D4 rt1-core ★★)** Transporting the tautological chart of the universal
curve along the classifying morphism recovers the adapted local model: the geometric
content of the right-inverse roundtrip. -/
theorem transVC_transport_taut {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤)))
    (V : Y.base.affineOpens) (i : Y.curve.toEllipticCurveGeom.atlas.ι)
    (hVi : V.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U i).1) :
    ((tautPresentation (universalShortNF R)).transport
        (classifyingEllHom Y b h2 h3).baseHom (classifyingEllHom Y b h2 h3).top
        (classifyingEllHom Y b h2 h3).isPullback
        (classifyingEllHom Y b h2 h3).zero_w
        (show V.1 ≤ (classifyingEllHom Y b h2 h3).baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).transVC
      (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi) = 1 := by
  -- the transported chart curve is the adapted model's curve
  have hWeq : ((tautPresentation (universalShortNF R)).transport
      (classifyingEllHom Y b h2 h3).baseHom (classifyingEllHom Y b h2 h3).top
      (classifyingEllHom Y b h2 h3).isPullback (classifyingEllHom Y b h2 h3).zero_w
      (show V.1 ≤ (classifyingEllHom Y b h2 h3).baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).W =
    (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi).W := by
    letI : Algebra (ModuliRingE12 R)
        Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom.toAlgebra
    show ((universalShortNF R).map _).map _ =
      (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi).W
    rw [WeierstrassCurve.map_map,
      show ((sectionsMapLE (classifyingEllHom Y b h2 h3).baseHom
          (show V.1 ≤ (classifyingEllHom Y b h2 h3).baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).comp
        (algebraMap (ModuliRingE12 R)
          Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤))) =
      ((Y.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y b h2 h3) from
      sectionsMapLE_classifyingMap Y b h2 h3 V _]
    exact universalShortNF_map_classifying Y b h2 h3 V i hVi
  refine (transVC_unique _ _ 1 (by rw [one_smul, hWeq]) ?_).symm
  rw [projModelVCIso_one, eqToHom_trans]
  show ((tautPresentation (universalShortNF R)).transport
      (classifyingEllHom Y b h2 h3).baseHom (classifyingEllHom Y b h2 h3).top
      (classifyingEllHom Y b h2 h3).isPullback (classifyingEllHom Y b h2 h3).zero_w
      _).e.inv ≫
    (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi).e.hom = eqToHom _
  rw [Iso.inv_comp_eq]
  letI : Algebra Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤) Γ(Y.base, V.1) :=
    (sectionsMapLE (classifyingEllHom Y b h2 h3).baseHom
      (show V.1 ≤ (classifyingEllHom Y b h2 h3).baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).toAlgebra
  have hkey : ((tautPresentation (universalShortNF R)).transport
      (classifyingEllHom Y b h2 h3).baseHom (classifyingEllHom Y b h2 h3).top
      (classifyingEllHom Y b h2 h3).isPullback (classifyingEllHom Y b h2 h3).zero_w
      (show V.1 ≤ (classifyingEllHom Y b h2 h3).baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).e.hom =
    (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi).e.hom ≫
      eqToHom (congrArg projModel hWeq.symm) := by
    letI : Algebra (ModuliRingE12 R)
        Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom.toAlgebra
    haveI : IsIso (⊤ : (Spec (CommRingCat.of (ModuliRingE12 R))).Opens).ι := by
      rw [← Scheme.topIso_hom]
      infer_instance
    haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap (ModuliRingE12 R)
        Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤)))) := by
      have h : CommRingCat.ofHom (algebraMap (ModuliRingE12 R)
          Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤)) =
        (Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv := rfl
      rw [h]
      infer_instance
    refine (isPullback_projModelBaseChange
      (tautPresentation (universalShortNF R)).W).hom_ext ?_ ?_
    · -- the base-change leg, through `classifyingTop_piece`
      rw [show ((tautPresentation (universalShortNF R)).transport
          (classifyingEllHom Y b h2 h3).baseHom (classifyingEllHom Y b h2 h3).top
          (classifyingEllHom Y b h2 h3).isPullback
          (classifyingEllHom Y b h2 h3).zero_w
          (show V.1 ≤ (classifyingEllHom Y b h2 h3).baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).e.hom ≫
        projModelBaseChange (algebraMap
          Γ(Spec (CommRingCat.of (ModuliRingE12 R)),
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (ModuliRingE12 R))).affineOpens).1) Γ(Y.base, V.1))
          (tautPresentation (universalShortNF R)).W =
        transportTheta (classifyingEllHom Y b h2 h3).baseHom
          (classifyingEllHom Y b h2 h3).top
          (classifyingEllHom Y b h2 h3).isPullback
          (show V.1 ≤ (classifyingEllHom Y b h2 h3).baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial) ≫
          (tautPresentation (universalShortNF R)).e.hom from
        transport_e_baseChange _ _ _ _ _ _]
      rw [show (tautPresentation (universalShortNF R)).e.hom =
        (asIso (pullback.fst (projModelπ (universalShortNF R))
          (⊤ : (Spec (CommRingCat.of (ModuliRingE12 R))).Opens).ι) ≪≫
        (asIso (pullback.fst (projModelπ (universalShortNF R))
          (Spec.map (CommRingCat.ofHom (algebraMap (ModuliRingE12 R)
            Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤)))))).symm ≪≫
        (isPullback_projModelBaseChange (universalShortNF R)).isoPullback.symm).hom
        from rfl]
      simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
      rw [← Category.assoc, ← Category.assoc,
        show (transportTheta (classifyingEllHom Y b h2 h3).baseHom
            (classifyingEllHom Y b h2 h3).top
            (classifyingEllHom Y b h2 h3).isPullback
            (show V.1 ≤ (classifyingEllHom Y b h2 h3).baseHom ⁻¹ᵁ
              (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
                (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial) ≫
          pullback.fst (projModelπ (universalShortNF R))
            (⊤ : (Spec (CommRingCat.of (ModuliRingE12 R))).Opens).ι) =
        pullback.fst Y.curve.toEllipticCurveGeom.π V.1.ι ≫
          (classifyingEllHom Y b h2 h3).top from
        transportTheta_fst _ _ _ _]
      rw [show pullback.fst Y.curve.toEllipticCurveGeom.π V.1.ι ≫
          (classifyingEllHom Y b h2 h3).top =
        chartPiece Y b h2 h3 V i hVi from by
        rw [show (classifyingEllHom Y b h2 h3).top =
          classifyingTop Y b h2 h3 from rfl,
          ← classifyingTop_piece Y b h2 h3 ⟨⟨V, i⟩, hVi⟩, adaptedTotalCover_f]]
      rw [chartPiece]
      simp only [Category.assoc]
      rw [cancel_epi
        ((adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi).e.hom)]
      -- universal side: the base-change chain collapses
      rw [projModelBaseChange_congr_hom
          ((sectionsMapLE_classifyingMap Y b h2 h3 V
            (fun x _ => trivial)).symm)
          (universalShortNF R),
        projModelBaseChange_comp']
      simp only [Category.assoc]
      have htail : projModelBaseChange
            ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom)
            (universalShortNF R) ≫
          inv (pullback.fst (projModelπ (universalShortNF R))
            (Spec.map (CommRingCat.ofHom (algebraMap (ModuliRingE12 R)
              Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤))))) ≫
          (isPullback_projModelBaseChange (universalShortNF R)).isoPullback.inv =
        𝟙 _ := by
        have h0 := (isPullback_projModelBaseChange
          (R' := Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤))
          (universalShortNF R)).isoPullback_hom_fst
        rw [← Category.assoc, Iso.comp_inv_eq, Category.id_comp, IsIso.comp_inv_eq]
        exact h0.symm
      rw [htail, Category.comp_id]
      show eqToHom _ ≫ eqToHom _ ≫
          projModelBaseChange (sectionsMapLE (classifyingMap Y b h2 h3)
            (show V.1 ≤ classifyingMap Y b h2 h3 ⁻¹ᵁ
              (⊤ : (Spec (CommRingCat.of (ModuliRingE12 R))).Opens) from
              fun x _ => trivial))
            ((universalShortNF R).map
              (Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom) =
        eqToHom _ ≫
          projModelBaseChange (sectionsMapLE (classifyingMap Y b h2 h3)
            (show V.1 ≤ classifyingMap Y b h2 h3 ⁻¹ᵁ
              (⊤ : (Spec (CommRingCat.of (ModuliRingE12 R))).Opens) from
              fun x _ => trivial))
            ((universalShortNF R).map
              (Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom)
      rw [eqToHom_trans_assoc]
    · -- the `π` leg
      rw [Category.assoc,
        show eqToHom (congrArg projModel hWeq.symm) ≫
            projModelπ ((tautPresentation (universalShortNF R)).W.map
              (algebraMap Γ(Spec (CommRingCat.of (ModuliRingE12 R)),
                (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
                  (ModuliRingE12 R))).affineOpens).1) Γ(Y.base, V.1))) =
          projModelπ ((adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V
            i hVi).W) from projModelπ_congr hWeq.symm,
        (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi).compat_π]
      exact ((tautPresentation (universalShortNF R)).transport
        (classifyingEllHom Y b h2 h3).baseHom (classifyingEllHom Y b h2 h3).top
        (classifyingEllHom Y b h2 h3).isPullback (classifyingEllHom Y b h2 h3).zero_w
        _).compat_π
  rw [hkey, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
/-- The tautological presentation is adapted to the universal `ω`-basis it induces
(the reflexive-restriction case of `isAdapted_restrict_ofPresentation`). -/
theorem tautPresentation_isAdapted (R : CommRingCat.{u}) :
    (tautPresentation (universalShortNF R)).IsAdapted (universalOmegaBasis R) := by
  have h : ((tautPresentation (universalShortNF R)).restrict
      (le_refl (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
        (ModuliRingE12 R))).affineOpens).1)).IsAdapted (universalOmegaBasis R) :=
    isAdapted_restrict_ofPresentation rfl (tautPresentation (universalShortNF R))
      (le_refl _)
  show ((tautPresentation (universalShortNF R)).basisUnitAt
    (universalOmegaBasis R)).1 = 1
  have h' : (((tautPresentation (universalShortNF R)).restrict
      (le_refl _)).basisUnitAt (universalOmegaBasis R)).1 = 1 := h
  rw [← basisUnitAt_restrict (tautPresentation (universalShortNF R))
    (universalOmegaBasis R) (le_refl _)] at h'
  rw [← h']
  exact (Units.ext (by simp)).symm

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation TopologicalSpace in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(E12-D4 rt1 ★)** Roundtrip: pulling the universal `ω`-basis back along the
classifying morphism recovers the given basis, `(classifyingEllHom Y b)^* ω_univ = b`.
The pulled basis and `b` differ by a global unit `u` (the `𝔾ₘ`-torsor); on every
chart affine the `b`-adapted local model reads off `u`'s restriction as the ratio of
basis units, which is `1` by `transVC_transport_taut` + adaptedness on both sides. -/
theorem omegaBasisMap_classifyingEllHom {R : CommRingCat.{u}} (Y : EllObj R)
    (b : OmegaBasis Y.curve.toEllipticCurveGeom)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤))) :
    omegaBasisMap (classifyingEllHom Y b h2 h3) (universalOmegaBasis R) = b := by
  obtain ⟨u, hu, -⟩ := OmegaBasis.existsUnique_unit_smul b
    (omegaBasisMap (classifyingEllHom Y b h2 h3) (universalOmegaBasis R))
  have h1 : u = 1 := by
    refine Scheme.unit_ext_of_res_cover Y.base
      (fun p : {q : Y.base.affineOpens × Y.curve.toEllipticCurveGeom.atlas.ι //
        q.1.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U q.2).1} => p.1.1.1)
      (fun p => le_top) (fun x _ => ?_) (fun p => ?_)
    · obtain ⟨i, hxi⟩ := Y.curve.toEllipticCurveGeom.atlas.covers x
      obtain ⟨W, hWaff, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hxi
      exact Opens.mem_iSup.mpr ⟨⟨⟨⟨W, hWaff⟩, i⟩, hWU⟩, hxW⟩
    · obtain ⟨⟨V, i⟩, hVi⟩ := p
      -- the transported tautological chart has trivial comparison to the adapted model
      have htu : ((tautPresentation (universalShortNF R)).transport
          (classifyingEllHom Y b h2 h3).baseHom (classifyingEllHom Y b h2 h3).top
          (classifyingEllHom Y b h2 h3).isPullback
          (classifyingEllHom Y b h2 h3).zero_w
          (show V.1 ≤ (classifyingEllHom Y b h2 h3).baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).transUnit
          (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi) = 1 := by
        show (((tautPresentation (universalShortNF R)).transport
          (classifyingEllHom Y b h2 h3).baseHom (classifyingEllHom Y b h2 h3).top
          (classifyingEllHom Y b h2 h3).isPullback
          (classifyingEllHom Y b h2 h3).zero_w
          (show V.1 ≤ (classifyingEllHom Y b h2 h3).baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).transVC
          (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi)).u = 1
        rw [transVC_transport_taut Y b h2 h3 V i hVi]
        rfl
      have hAT : (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i
          hVi).transUnit
          ((tautPresentation (universalShortNF R)).transport
            (classifyingEllHom Y b h2 h3).baseHom (classifyingEllHom Y b h2 h3).top
            (classifyingEllHom Y b h2 h3).isPullback
            (classifyingEllHom Y b h2 h3).zero_w
            (show V.1 ≤ (classifyingEllHom Y b h2 h3).baseHom ⁻¹ᵁ
              (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
                (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)) = 1 := by
        have h := transUnit_trans
          (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi)
          ((tautPresentation (universalShortNF R)).transport
            (classifyingEllHom Y b h2 h3).baseHom (classifyingEllHom Y b h2 h3).top
            (classifyingEllHom Y b h2 h3).isPullback
            (classifyingEllHom Y b h2 h3).zero_w
            (show V.1 ≤ (classifyingEllHom Y b h2 h3).baseHom ⁻¹ᵁ
              (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
                (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial))
          (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi)
        rw [htu, mul_one, transUnit_self] at h
        exact h
      -- the transported chart is adapted to the pulled basis
      have hTad : (((tautPresentation (universalShortNF R)).transport
          (classifyingEllHom Y b h2 h3).baseHom (classifyingEllHom Y b h2 h3).top
          (classifyingEllHom Y b h2 h3).isPullback
          (classifyingEllHom Y b h2 h3).zero_w
          (show V.1 ≤ (classifyingEllHom Y b h2 h3).baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).basisUnitAt
          (omegaBasisMap (classifyingEllHom Y b h2 h3) (universalOmegaBasis R))).1 =
          1 :=
        IsAdapted.transport (classifyingEllHom Y b h2 h3)
          (tautPresentation_isAdapted R) _
      -- hence the adapted model reads the pulled basis with unit 1
      have hkey : ((adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i
          hVi).basisUnitAt
          (omegaBasisMap (classifyingEllHom Y b h2 h3) (universalOmegaBasis R))).1 =
          1 := by
        rw [basisUnitAt_transUnit
          (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi)
          ((tautPresentation (universalShortNF R)).transport
            (classifyingEllHom Y b h2 h3).baseHom (classifyingEllHom Y b h2 h3).top
            (classifyingEllHom Y b h2 h3).isPullback
            (classifyingEllHom Y b h2 h3).zero_w
            (show V.1 ≤ (classifyingEllHom Y b h2 h3).baseHom ⁻¹ᵁ
              (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
                (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial))
          (omegaBasisMap (classifyingEllHom Y b h2 h3) (universalOmegaBasis R)),
          hAT, hTad, one_mul]
      -- compare against the smul computation
      have hsm := basisUnitAt_smul
        (adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i hVi) u b
      rw [hu] at hsm
      have hALb : ((adaptedLocal Y.curve.toEllipticCurveGeom b h2 h3 V i
          hVi).basisUnitAt b).1 = 1 :=
        adaptedLocal_isAdapted Y.curve.toEllipticCurveGeom b h2 h3 V i hVi
      rw [hkey, hALb, mul_one] at hsm
      rw [map_one]
      exact hsm.symm
  rw [← hu, h1]
  exact Subtype.ext (by
    rw [show ((1 : Γ(Y.base, ⊤)ˣ) • b).1 =
      ((1 : Γ(Y.base, ⊤)ˣ)).val • b.1 from rfl, Units.val_one, one_smul])

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D4 rt2a)** For ANY `Ell/R`-morphism `φ` to the universal object, the
transported tautological chart compares trivially with the adapted local model of the
pulled basis: both are adapted to the pulled basis and in short normal form, so
KM 2.2.5 uniqueness (`transVC_eq_one_of_isAdapted`) pins the comparison. -/
theorem transVC_transport_adapted {R : CommRingCat.{u}} {Y : EllObj R}
    (φ : Y ⟶ universalEllObj R)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤)))
    (V : Y.base.affineOpens) (i : Y.curve.toEllipticCurveGeom.atlas.ι)
    (hVi : V.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U i).1) :
    ((tautPresentation (universalShortNF R)).transport
        φ.baseHom φ.top φ.isPullback φ.zero_w
        (show V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).transVC
      (adaptedLocal Y.curve.toEllipticCurveGeom
        (omegaBasisMap φ (universalOmegaBasis R)) h2 h3 V i hVi) = 1 :=
  transVC_eq_one_of_isAdapted
    (IsAdapted.transport φ (tautPresentation_isAdapted R) _)
    (adaptedLocal_isAdapted _ _ h2 h3 V i hVi)
    (isShortNF_map (isShortNF_map
      (inferInstance : (universalShortNF R).IsShortNF) _) _)
    (adaptedLocal_isShortNF _ _ h2 h3 V i hVi)
    (isUnit_ofNat_res h2 V.1) (isUnit_ofNat_res h3 V.1)

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D4 rt2a)** W-form: the transported tautological chart curve IS the adapted
local model curve of the pulled basis. -/
theorem transport_taut_W_eq {R : CommRingCat.{u}} {Y : EllObj R}
    (φ : Y ⟶ universalEllObj R)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤)))
    (V : Y.base.affineOpens) (i : Y.curve.toEllipticCurveGeom.atlas.ι)
    (hVi : V.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U i).1) :
    ((tautPresentation (universalShortNF R)).transport
        φ.baseHom φ.top φ.isPullback φ.zero_w
        (show V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).W =
      (adaptedLocal Y.curve.toEllipticCurveGeom
        (omegaBasisMap φ (universalOmegaBasis R)) h2 h3 V i hVi).W := by
  have h := ((tautPresentation (universalShortNF R)).transport
      φ.baseHom φ.top φ.isPullback φ.zero_w
      (show V.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).transVC_smul
    (adaptedLocal Y.curve.toEllipticCurveGeom
      (omegaBasisMap φ (universalOmegaBasis R)) h2 h3 V i hVi)
  rw [transVC_transport_adapted φ h2 h3 V i hVi, one_smul] at h
  exact h.symm

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D4 rt2b)** e-form: the transported tautological chart isomorphism is the
adapted local model's, up to the induced `eqToHom` — the chart data of `φ` over `V` is
completely pinned by the pulled basis. -/
theorem transport_taut_e_eq {R : CommRingCat.{u}} {Y : EllObj R}
    (φ : Y ⟶ universalEllObj R)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤)))
    (V : Y.base.affineOpens) (i : Y.curve.toEllipticCurveGeom.atlas.ι)
    (hVi : V.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U i).1) :
    ((tautPresentation (universalShortNF R)).transport
        φ.baseHom φ.top φ.isPullback φ.zero_w
        (show V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).e.hom =
      (adaptedLocal Y.curve.toEllipticCurveGeom
          (omegaBasisMap φ (universalOmegaBasis R)) h2 h3 V i hVi).e.hom ≫
        eqToHom (congrArg projModel (transport_taut_W_eq φ h2 h3 V i hVi).symm) := by
  have h := pointedIso_hom_of_transVC_eq_one
    (transVC_transport_adapted φ h2 h3 V i hVi)
  rw [pointedIso, Iso.trans_hom, Iso.symm_hom, Iso.inv_comp_eq] at h
  rw [h, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(E12-D4 rt2a ★)** The classifying algebra of the pulled basis is the algebra of
`φ` itself: any `Ell/R`-morphism to the universal object induces on global sections
exactly the classifying ring map of the basis it pulls back. Generators: `C`-scalars
by `base_w`, and `A₄`/`A₆` by the chartwise `W`-determination `transport_taut_W_eq`. -/
theorem classifyingRingHom_omegaBasisMap {R : CommRingCat.{u}} {Y : EllObj R}
    (φ : Y ⟶ universalEllObj R)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤))) :
    classifyingRingHom Y (omegaBasisMap φ (universalOmegaBasis R)) h2 h3 =
      ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv ≫
        φ.baseHom.appTop).hom := by
  have hψR : ∀ r : R,
      ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv ≫
        φ.baseHom.appTop).hom (algebraMap R (ModuliRingE12 R) r) =
      Y.baseRingHom r := by
    intro r
    have hb : CommRingCat.ofHom (algebraMap R (ModuliRingE12 R)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv ≫
          φ.baseHom.appTop =
        CommRingCat.ofHom Y.baseRingHom := by
      rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop,
        show φ.baseHom ≫ Spec.map (CommRingCat.ofHom
            (algebraMap R (ModuliRingE12 R))) = Y.structMap from φ.base_w]
      rfl
    exact congrArg (fun g => CommRingCat.Hom.hom g r) hb
  -- coefficient naturality on the two generators
  have hcover : (⊤ : Y.base.Opens) ≤
      iSup (fun p : {p : Y.base.affineOpens × Y.curve.toEllipticCurveGeom.atlas.ι //
        p.1.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U p.2).1} => p.1.1.1) := by
    intro x _
    obtain ⟨i, hxi⟩ := Y.curve.toEllipticCurveGeom.atlas.covers x
    obtain ⟨V₀, hVaff, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (Y.curve.toEllipticCurveGeom.atlas.U i).1 from hxi)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨⟨V₀, hVaff⟩, i⟩, hVle⟩, hxV⟩
  have hnat : ∀ j : Fin 2,
      (![(adaptedCoeff₄ Y.curve.toEllipticCurveGeom
          (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1,
        (adaptedCoeff₆ Y.curve.toEllipticCurveGeom
          (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1] j) =
      ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv ≫
        φ.baseHom.appTop).hom
        (algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X j)) := by
    intro j
    refine TopCat.Sheaf.eq_of_locally_eq' Y.base.sheaf
      (fun p : {p : Y.base.affineOpens × Y.curve.toEllipticCurveGeom.atlas.ι //
        p.1.1 ≤ (Y.curve.toEllipticCurveGeom.atlas.U p.2).1} => p.1.1.1) ⊤
      (fun p => homOfLE le_top) hcover _ _ (fun p => ?_)
    show Scheme.resLE le_top
        (![(adaptedCoeff₄ Y.curve.toEllipticCurveGeom
            (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1,
          (adaptedCoeff₆ Y.curve.toEllipticCurveGeom
            (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1] j) =
      Scheme.resLE le_top
        (((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv ≫
          φ.baseHom.appTop).hom
          (algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X j)))
    have hres : Scheme.resLE (le_top : p.1.1.1 ≤ ⊤)
        (((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv ≫
          φ.baseHom.appTop).hom
          (algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X j))) =
        sectionsMapLE φ.baseHom
          (show p.1.1.1 ≤ φ.baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)
          ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom
            (algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X j))) := rfl
    rw [hres]
    fin_cases j
    · show Scheme.resLE le_top
          (![(adaptedCoeff₄ Y.curve.toEllipticCurveGeom
              (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1,
            (adaptedCoeff₆ Y.curve.toEllipticCurveGeom
              (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1] 0) =
        sectionsMapLE φ.baseHom
          (show p.1.1.1 ≤ φ.baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)
          ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom
            (algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X 0)))
      rw [show Scheme.resLE le_top
          (![(adaptedCoeff₄ Y.curve.toEllipticCurveGeom
              (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1,
            (adaptedCoeff₆ Y.curve.toEllipticCurveGeom
              (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1] 0) =
          (adaptedLocal Y.curve.toEllipticCurveGeom
            (omegaBasisMap φ (universalOmegaBasis R)) h2 h3
            p.1.1 p.1.2 p.2).W.a₄ from
          (adaptedCoeff₄ Y.curve.toEllipticCurveGeom
            (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).2 p.1.1 p.1.2 p.2,
        ← transport_taut_W_eq φ h2 h3 p.1.1 p.1.2 p.2]
      rfl
    · show Scheme.resLE le_top
          (![(adaptedCoeff₄ Y.curve.toEllipticCurveGeom
              (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1,
            (adaptedCoeff₆ Y.curve.toEllipticCurveGeom
              (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1] 1) =
        sectionsMapLE φ.baseHom
          (show p.1.1.1 ≤ φ.baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)
          ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom
            (algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X 1)))
      rw [show Scheme.resLE le_top
          (![(adaptedCoeff₄ Y.curve.toEllipticCurveGeom
              (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1,
            (adaptedCoeff₆ Y.curve.toEllipticCurveGeom
              (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1] 1) =
          (adaptedLocal Y.curve.toEllipticCurveGeom
            (omegaBasisMap φ (universalOmegaBasis R)) h2 h3
            p.1.1 p.1.2 p.2).W.a₆ from
          (adaptedCoeff₆ Y.curve.toEllipticCurveGeom
            (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).2 p.1.1 p.1.2 p.2,
        ← transport_taut_W_eq φ h2 h3 p.1.1 p.1.2 p.2]
      rfl
  refine IsLocalization.ringHom_ext (Submonoid.powers (shortDeltaPoly R)) ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
  · show classifyingRingHom Y (omegaBasisMap φ (universalOmegaBasis R)) h2 h3
      (algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (C r)) = _
    rw [show algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (C r) =
        algebraMap R (ModuliRingE12 R) r from by
      rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R)
        (ModuliRingE12 R)]
      rfl]
    rw [classifyingRingHom_algebraMap]
    show Y.baseRingHom r =
      ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv ≫
        φ.baseHom.appTop).hom
        (algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (C r))
    rw [show algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (C r) =
        algebraMap R (ModuliRingE12 R) r from by
      rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R)
        (ModuliRingE12 R)]
      rfl]
    exact (hψR r).symm
  · show classifyingRingHom Y (omegaBasisMap φ (universalOmegaBasis R)) h2 h3
      (algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X j)) = _
    rw [classifyingRingHom, IsLocalization.Away.lift_eq]
    rw [show (eval₂Hom Y.baseRingHom
        ![(adaptedCoeff₄ Y.curve.toEllipticCurveGeom
            (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1,
          (adaptedCoeff₆ Y.curve.toEllipticCurveGeom
            (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1]) (X j) =
      ![(adaptedCoeff₄ Y.curve.toEllipticCurveGeom
          (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1,
        (adaptedCoeff₆ Y.curve.toEllipticCurveGeom
          (omegaBasisMap φ (universalOmegaBasis R)) h2 h3).1] j from
      eval₂Hom_X' _ _ _]
    exact hnat j

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D4 rt2a ★)** BaseHom determination: the classifying map of the pulled
basis IS `φ`'s base morphism (Γ–Spec adjunction + `classifyingRingHom_omegaBasisMap`). -/
theorem classifyingMap_omegaBasisMap {R : CommRingCat.{u}} {Y : EllObj R}
    (φ : Y ⟶ universalEllObj R)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤))) :
    classifyingMap Y (omegaBasisMap φ (universalOmegaBasis R)) h2 h3 = φ.baseHom := by
  show Y.base.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (classifyingRingHom Y (omegaBasisMap φ (universalOmegaBasis R)) h2 h3)) =
    φ.baseHom
  rw [show CommRingCat.ofHom
      (classifyingRingHom Y (omegaBasisMap φ (universalOmegaBasis R)) h2 h3) =
    (Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv ≫ φ.baseHom.appTop from by
    rw [classifyingRingHom_omegaBasisMap φ h2 h3]
    rfl]
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
  show φ.baseHom ≫ (Spec (CommRingCat.of (ModuliRingE12 R))).toSpecΓ ≫
    Spec.map (Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv = φ.baseHom
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  exact Category.comp_id _

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(E12-D4 rt2b ★)** Top determination: the glued classifying comparison of the
pulled basis IS `φ`'s total-space morphism. Per chart-supported affine piece, both
equal the chart piece of the pulled basis: `φ`'s side by `transportTheta_fst` +
`transport_e_baseChange` + the e-determination `transport_taut_e_eq`, with the
algebra leg pinned by `classifyingMap_omegaBasisMap` + `sectionsMapLE_classifyingMap`. -/
theorem classifyingTop_omegaBasisMap {R : CommRingCat.{u}} {Y : EllObj R}
    (φ : Y ⟶ universalEllObj R)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤))) :
    classifyingTop Y (omegaBasisMap φ (universalOmegaBasis R)) h2 h3 = φ.top := by
  letI : Algebra (ModuliRingE12 R)
      Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom.toAlgebra
  haveI : IsIso (⊤ : (Spec (CommRingCat.of (ModuliRingE12 R))).Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap (ModuliRingE12 R)
      Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤)))) := by
    have h : CommRingCat.ofHom (algebraMap (ModuliRingE12 R)
        Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv := rfl
    rw [h]
    infer_instance
  have hfst : pullback.fst (projModelπ (universalShortNF R))
      (⊤ : (Spec (CommRingCat.of (ModuliRingE12 R))).Opens).ι =
      (tautPresentation (universalShortNF R)).e.hom ≫
        (isPullback_projModelBaseChange (universalShortNF R)).isoPullback.hom ≫
        pullback.fst (projModelπ (universalShortNF R))
          (Spec.map (CommRingCat.ofHom (algebraMap (ModuliRingE12 R)
            Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤)))) := by
    rw [show (tautPresentation (universalShortNF R)).e.hom =
      (asIso (pullback.fst (projModelπ (universalShortNF R))
        (⊤ : (Spec (CommRingCat.of (ModuliRingE12 R))).Opens).ι) ≪≫
      (asIso (pullback.fst (projModelπ (universalShortNF R))
        (Spec.map (CommRingCat.ofHom (algebraMap (ModuliRingE12 R)
          Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤)))))).symm ≪≫
      (isPullback_projModelBaseChange (universalShortNF R)).isoPullback.symm).hom
      from rfl]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
      Iso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  refine (adaptedTotalCover Y).hom_ext _ _ (fun p => ?_)
  rw [classifyingTop_piece Y (omegaBasisMap φ (universalOmegaBasis R)) h2 h3 p,
    adaptedTotalCover_f]
  -- now: chartPiece(pulled) = fst ≫ φ.top; unfold the φ-side through the transport
  rw [show pullback.fst Y.curve.toEllipticCurveGeom.π p.1.1.1.ι ≫ φ.top =
    transportTheta φ.baseHom φ.top φ.isPullback
      (show p.1.1.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial) ≫
      pullback.fst (projModelπ (universalShortNF R))
        (⊤ : (Spec (CommRingCat.of (ModuliRingE12 R))).Opens).ι from
    (transportTheta_fst φ.baseHom φ.top φ.isPullback _).symm]
  rw [hfst, ← Category.assoc,
    show transportTheta φ.baseHom φ.top φ.isPullback
        (show p.1.1.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial) ≫
      (tautPresentation (universalShortNF R)).e.hom =
    ((tautPresentation (universalShortNF R)).transport
      φ.baseHom φ.top φ.isPullback φ.zero_w
      (show p.1.1.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).e.hom ≫
      projModelBaseChange (sectionsMapLE φ.baseHom
        (show p.1.1.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial))
        (tautPresentation (universalShortNF R)).W from
    (transport_e_baseChange φ.baseHom φ.top φ.isPullback φ.zero_w
      (tautPresentation (universalShortNF R)) _).symm]
  rw [transport_taut_e_eq φ h2 h3 p.1.1 p.1.2 p.2]
  -- collapse the universal-side chain into a single base change along the composite
  have hσ : (sectionsMapLE φ.baseHom
      (show p.1.1.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).comp
      ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom) =
      ((Y.base.presheaf.map (homOfLE (le_top : p.1.1.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y (omegaBasisMap φ (universalOmegaBasis R)) h2 h3) := by
    rw [sectionsMapLE_congr_hom (classifyingMap_omegaBasisMap φ h2 h3).symm
      (show p.1.1.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)]
    exact sectionsMapLE_classifyingMap Y
      (omegaBasisMap φ (universalOmegaBasis R)) h2 h3 p.1.1 (fun x _ => trivial)
  rw [show projModelBaseChange (sectionsMapLE φ.baseHom
      (show p.1.1.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial))
      (tautPresentation (universalShortNF R)).W =
    projModelBaseChange (sectionsMapLE φ.baseHom
      (show p.1.1.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial))
      ((universalShortNF R).map
        ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom)) from rfl]
  rw [Category.assoc, Category.assoc,
    show (isPullback_projModelBaseChange (universalShortNF R)).isoPullback.hom ≫
      pullback.fst (projModelπ (universalShortNF R))
        (Spec.map (CommRingCat.ofHom (algebraMap (ModuliRingE12 R)
          Γ(Spec (CommRingCat.of (ModuliRingE12 R)), ⊤)))) =
    projModelBaseChange
      ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom)
      (universalShortNF R) from
    (isPullback_projModelBaseChange (universalShortNF R)).isoPullback_hom_fst,
    ← projModelBaseChange_comp', projModelBaseChange_congr_hom hσ
      (universalShortNF R)]
  rw [chartPiece]
  show (adaptedLocal Y.curve.toEllipticCurveGeom
      (omegaBasisMap φ (universalOmegaBasis R)) h2 h3 p.1.1 p.1.2 p.2).e.hom ≫
    eqToHom _ ≫
      projModelBaseChange (((Y.base.presheaf.map (homOfLE
        (le_top : p.1.1.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y (omegaBasisMap φ (universalOmegaBasis R)) h2 h3))
        (universalShortNF R) =
    (adaptedLocal Y.curve.toEllipticCurveGeom
      (omegaBasisMap φ (universalOmegaBasis R)) h2 h3 p.1.1 p.1.2 p.2).e.hom ≫
    (eqToHom _ : projModel (adaptedLocal Y.curve.toEllipticCurveGeom
        (omegaBasisMap φ (universalOmegaBasis R)) h2 h3 p.1.1 p.1.2 p.2).W ⟶
      projModel ((universalShortNF R).map
        ((sectionsMapLE φ.baseHom (show p.1.1.1 ≤ φ.baseHom ⁻¹ᵁ (⟨⊤,
          isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (ModuliRingE12 R))).affineOpens).1 from fun x _ => trivial)).comp
          ((Scheme.ΓSpecIso (CommRingCat.of (ModuliRingE12 R))).inv.hom)))) ≫
    eqToHom _ ≫
      projModelBaseChange (((Y.base.presheaf.map (homOfLE
        (le_top : p.1.1.1 ≤ ⊤)).op).hom).comp
        (classifyingRingHom Y (omegaBasisMap φ (universalOmegaBasis R)) h2 h3))
        (universalShortNF R)
  rw [eqToHom_trans_assoc]

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
/-- **(E12-D4 rt2 ★★)** Uniqueness half of GME Thm 2.2.3: ANY `Ell/R`-morphism to
the universal object is the classifying morphism of the basis it pulls back. With
`omegaBasisMap_classifyingEllHom` (the existence half's roundtrip) this makes
`Y ⟼ (Y ⟶ M₁)` and `Y ⟼ OmegaBasis(Y)` naturally equivalent. -/
theorem classifyingEllHom_omegaBasisMap {R : CommRingCat.{u}} {Y : EllObj R}
    (φ : Y ⟶ universalEllObj R)
    (h2 : IsUnit (2 : Γ(Y.base, ⊤))) (h3 : IsUnit (3 : Γ(Y.base, ⊤))) :
    classifyingEllHom Y (omegaBasisMap φ (universalOmegaBasis R)) h2 h3 = φ :=
  EllHom.ext (classifyingMap_omegaBasisMap φ h2 h3)
    (classifyingTop_omegaBasisMap φ h2 h3)

/-- `2` is a unit whenever `6` is. -/
theorem isUnit_two_of_six {A : Type u} [CommRing A] (h : IsUnit (6 : A)) :
    IsUnit (2 : A) :=
  isUnit_of_mul_isUnit_left (y := (3 : A))
    (by rw [show (2 : A) * 3 = 6 by norm_num]; exact h)

/-- `3` is a unit whenever `6` is. -/
theorem isUnit_three_of_six {A : Type u} [CommRing A] (h : IsUnit (6 : A)) :
    IsUnit (3 : A) :=
  isUnit_of_mul_isUnit_right (x := (2 : A))
    (by rw [show (2 : A) * 3 = 6 by norm_num]; exact h)

open AlgebraicGeometry CategoryTheory Scheme in
/-- If `6` is a unit in `R`, it is a unit in the global sections of every
`Ell/R`-object's base. -/
theorem EllObj.isUnit_six {R : CommRingCat.{u}} (Y : EllObj R)
    (hR : IsUnit (6 : R)) : IsUnit (6 : Γ(Y.base, ⊤)) := by
  have h := hR.map Y.baseRingHom
  rwa [map_ofNat] at h

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
/-- **(T-E12 ★★, GME Thm 2.2.3; KM 2.2.6)** THE REPRESENTABILITY PACKAGE: over a base
ring in which `6` is invertible, the `ω`-moduli problem `[(E, ω)]` is represented by
the universal object `M₁ = Spec R[A₄, A₆][Δ⁻¹]`. The natural bijection sends `φ` to
`φ^* ω_univ`; its inverse is the classifying morphism; the roundtrips are
`omegaBasisMap_classifyingEllHom` and `classifyingEllHom_omegaBasisMap`, and
naturality is the `ω`-transport functoriality `omegaBasisMap_comp`. -/
noncomputable def omegaRepresentableBy (R : CommRingCat.{u}) (hR : IsUnit (6 : R)) :
    (omegaProblem R).RepresentableBy (universalEllObj R) where
  homEquiv {Y} :=
    { toFun := fun φ => omegaBasisMap φ (universalOmegaBasis R)
      invFun := fun b => classifyingEllHom Y b
        (isUnit_two_of_six (Y.isUnit_six hR)) (isUnit_three_of_six (Y.isUnit_six hR))
      left_inv := fun φ => classifyingEllHom_omegaBasisMap φ _ _
      right_inv := fun b => omegaBasisMap_classifyingEllHom Y b _ _ }
  homEquiv_comp f g := omegaBasisMap_comp f g (universalOmegaBasis R)

end ModularCurves
