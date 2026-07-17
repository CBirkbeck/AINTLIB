/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.AffineSectionDoubling
import ModularCurves.EllipticCurve.AffineSectionSpecPoints
import ModularCurves.Moduli.SectionMarking

/-!
# `RING-DBL`: the scheme-level doubling identity (parts C/D/E)

**(STREAM-OMEGA 2026-07-17, CHARTER-O v10.316.)** The universal-domain proof of
`2 • affineSection p q = affineSection (dblX, dblY)` (KM's banked route,
`decomposition-km-integral.md` [RING-DBL]):

* **[C] the universal base**: the `a₆`-ELIMINATION trick — solving the Weierstrass
  equation for `a₆` presents the universal marked curve over the FREE polynomial ring
  `ℤ[a₁, a₂, a₃, a₄, p, q]` (a domain, no irreducibility argument needed), localized at
  `tangentDen · Δ` (so the tangent denominator AND ellipticity are units).
* **[D]** over that domain, `2 • affineSection` is fibrewise nonzero (the field
  criterion), hence has marked coordinates ([hArb-1/2] pipeline), which the generic
  (fraction-field) fibre pins to `dblX/dblY` by injectivity.
* **[E]** the identity transports to every ring along the classifying map
  (the Stage-D `modelBaseChangeIso` section transport).
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory WeierstrassCurve MvPolynomial

/-! ### [C] the universal doubling base -/

/-- Variables: `0,1,2,3 ↦ a₁,a₂,a₃,a₄`, `4 ↦ p`, `5 ↦ q`. -/
abbrev DblBase : Type := MvPolynomial (Fin 6) ℤ

/-- The `a₆`-elimination: the value of `a₆` making `(p, q)` a curve point. -/
def dblA₆ : DblBase :=
  X 5 ^ 2 + X 0 * X 4 * X 5 + X 2 * X 5 - X 4 ^ 3 - X 1 * X 4 ^ 2 - X 3 * X 4

/-- The universal marked Weierstrass curve (with `a₆` solved out). -/
def dblW : WeierstrassCurve DblBase :=
  ⟨X 0, X 1, X 2, X 3, dblA₆⟩

/-- The tautological marked point lies on the curve. -/
theorem dblW_equation : dblW.toAffine.Equation (X 4) (X 5) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  show (X 5 : DblBase) ^ 2 + X 0 * X 4 * X 5 + X 2 * X 5
    = X 4 ^ 3 + X 1 * X 4 ^ 2 + X 3 * X 4 + dblA₆
  rw [dblA₆]
  ring

/-- The universal localization element: tangent denominator times discriminant. -/
def dblLoc : DblBase := dblW.tangentDen (X 4) (X 5) * dblW.Δ

/-- The universal doubling base: localize away from `tangentDen · Δ`. -/
abbrev DblRing : Type := Localization.Away dblLoc

/-- The universal doubling curve. -/
def dblWu : WeierstrassCurve DblRing :=
  dblW.map (algebraMap DblBase DblRing)

/-- The localization element is nonzero (evaluate at
`a₁ = a₂ = a₄ = 0, a₃ = 1, p = 0, q = 0`: `tangentDen = 1`, `Δ = -27`). -/
theorem dblLoc_ne_zero : dblLoc ≠ 0 := by
  intro hc
  have h := congrArg (MvPolynomial.eval
    (fun i : Fin 6 => if i = 2 then (1 : ℤ) else 0)) hc
  rw [map_zero] at h
  rw [dblLoc, map_mul] at h
  have h1 : MvPolynomial.eval (fun i : Fin 6 => if i = 2 then (1 : ℤ) else 0)
      (dblW.tangentDen (X 4) (X 5)) = 1 := by
    simp [tangentDen, dblW]
  have h2 : MvPolynomial.eval (fun i : Fin 6 => if i = 2 then (1 : ℤ) else 0)
      dblW.Δ = -27 := by
    simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, dblW, dblA₆]
  rw [h1, h2] at h
  norm_num at h

instance : IsDomain DblRing :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors dblLoc_ne_zero)

/-- The tangent denominator is a unit in the universal doubling base. -/
theorem isUnit_dblD :
    IsUnit (dblWu.tangentDen (algebraMap DblBase DblRing (X 4))
      (algebraMap DblBase DblRing (X 5))) := by
  have h : IsUnit (algebraMap DblBase DblRing
      (dblW.tangentDen (X 4) (X 5) * dblW.Δ)) :=
    IsLocalization.Away.algebraMap_isUnit (S := DblRing) dblLoc
  rw [map_mul] at h
  have hden : dblWu.tangentDen (algebraMap DblBase DblRing (X 4))
      (algebraMap DblBase DblRing (X 5))
      = algebraMap DblBase DblRing (dblW.tangentDen (X 4) (X 5)) := by
    simp only [tangentDen, dblWu, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
      map_add, map_mul, map_ofNat]
  rw [hden]
  exact isUnit_of_mul_isUnit_left h

/-- The universal doubling curve is elliptic. -/
instance : dblWu.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  have h : IsUnit (algebraMap DblBase DblRing
      (dblW.tangentDen (X 4) (X 5) * dblW.Δ)) :=
    IsLocalization.Away.algebraMap_isUnit (S := DblRing) dblLoc
  rw [map_mul] at h
  have hΔ : dblWu.Δ = algebraMap DblBase DblRing dblW.Δ := by
    rw [dblWu, WeierstrassCurve.map_Δ]
  rw [hΔ]
  exact isUnit_of_mul_isUnit_right h

/-! ### [E] the additive section transport along a coefficient map -/

section Transport

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
  (W : WeierstrassCurve A) [W.IsElliptic]

set_option backward.isDefEq.respectTransparency false in
/-- **([RING-DBL E] the section transport)** The additive map on model sections induced
by a coefficient ring map: pull along `Spec`, cast the base identity, invert the
base-change point equivalence, and push across the Stage-D pointed comparison. -/
noncomputable def sectionMapHom :
    letI : (W.map (algebraMap A A')).IsElliptic := inferInstance
    (modelEllipticCurve W).Section →+
      (modelEllipticCurve (W.map (algebraMap A A'))).Section :=
  letI : (W.map (algebraMap A A')).IsElliptic := inferInstance
  ((EllipticCurve.pointAddEquiv (modelBaseChangeIso (A' := A') W)
      ((isMonHom_modelBaseChangeIso (A' := A') W).mul_hom)
      (𝟙 (Spec (CommRingCat.of A')))).toAddMonoidHom).comp
    (((EllipticCurve.Point.baseChangeEquiv (E := modelEllipticCurve W)
        (Spec.map (CommRingCat.ofHom (algebraMap A A')))
        (𝟙 (Spec (CommRingCat.of A')))).symm.toAddMonoidHom).comp
      (((EllipticCurve.Point.castBase (modelEllipticCurve W)
          (Category.id_comp (Spec.map (CommRingCat.ofHom
            (algebraMap A A')))).symm).toAddMonoidHom).comp
        (AddMonoidHom.mk' (EllipticCurve.Point.pull (modelEllipticCurve W)
            (Spec.map (CommRingCat.ofHom (algebraMap A A'))))
          (fun P Q => EllipticCurve.Point.pull_add (modelEllipticCurve W) _ P Q))))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([RING-DBL E] the transport value)** The section transport carries affine-point
sections to the affine-point sections of the mapped coordinates (the Stage-D matched
section, as a value of `sectionMapHom`). -/
theorem sectionMapHom_affineSection {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] (W : WeierstrassCurve A) [W.IsElliptic] (p q : A)
    (h : W.toAffine.Equation p q)
    (h' : (W.map (algebraMap A A')).toAffine.Equation (algebraMap A A' p)
      (algebraMap A A' q)) :
    letI : (W.map (algebraMap A A')).IsElliptic := inferInstance
    sectionMapHom (A' := A') W ⟨projModelAffineSection W p q h,
        projModelAffineSection_projModelπ _ _ _ _⟩
      = ⟨projModelAffineSection (W.map (algebraMap A A')) (algebraMap A A' p)
          (algebraMap A A' q) h',
        projModelAffineSection_projModelπ _ _ _ _⟩ := by
  letI : (W.map (algebraMap A A')).IsElliptic := inferInstance
  refine Subtype.ext ?_
  show ((EllipticCurve.Point.asSection (modelEllipticCurve W)
      (Spec.map (CommRingCat.ofHom (algebraMap A A')))
      (EllipticCurve.Point.pull (modelEllipticCurve W)
        (Spec.map (CommRingCat.ofHom (algebraMap A A')))
        ⟨projModelAffineSection W p q h,
          projModelAffineSection_projModelπ _ _ _ _⟩)).1 ≫
      (modelBaseChangeIso (A' := A') W).hom.left) = _
  rw [modelBaseChangeIso_hom_left, Iso.comp_inv_eq]
  refine pullback.hom_ext ?_ ?_
  · refine ((EllipticCurve.Point.asSection_val_fst _ _ _).trans
      (projModelAffineSection_baseChange W p q h h').symm).trans ?_
    exact congrArg (fun m => projModelAffineSection (W.map (algebraMap A A'))
        (algebraMap A A' p) (algebraMap A A' q) h' ≫ m)
      (isPullback_projModelBaseChange (R' := A') W).isoPullback_hom_fst.symm
  · refine ((EllipticCurve.Point.asSection_val_snd _ _ _).trans
      (projModelAffineSection_projModelπ _ _ _ h').symm).trans ?_
    exact congrArg (fun m => projModelAffineSection (W.map (algebraMap A A'))
        (algebraMap A A' p) (algebraMap A A' q) h' ≫ m)
      (isPullback_projModelBaseChange (R' := A') W).isoPullback_hom_snd.symm


end Transport


end ModularCurves
