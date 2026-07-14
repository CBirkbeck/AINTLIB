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

end ModularCurves
