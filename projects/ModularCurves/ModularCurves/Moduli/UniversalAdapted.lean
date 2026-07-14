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


open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
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
set_option maxHeartbeats 1600000 in
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
set_option maxHeartbeats 3200000 in
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
set_option maxHeartbeats 1600000 in
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

end ModularCurves
