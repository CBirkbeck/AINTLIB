/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.LegendreDelta

/-!
# The universal Legendre object over `M'₂ = Spec R[λ][(λ(λ−1))⁻¹]` (T-E14-AX1)

**(STREAM-OMEGA 2026-07-14; the T-E12-D replay for KM 4.6.2's Legendre `δ`.)** The
moduli ring `R[λ][(λ(λ−1))⁻¹]`, the universal Legendre curve `y² = x(x−1)(x−λ)` over
it, its ellipticity when `2` is invertible, its tautological chart presentation, the
universal `ω`-basis, and the tautologically marked sections `P = (0,0)`, `Q = (1,0)`
(via `projModelAffineSection`) — the ingredients of KM engine axiom 1 for the
corrected `δ` (`legendreDelta_representable_by_affine`).
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory Limits Scheme MvPolynomial LocalPresentation

variable (R : CommRingCat.{u})

/-- **(T-E14-AX1)** The Legendre parameter polynomial `λ(λ−1)` in `R[λ]`. -/
def legendrePoly : MvPolynomial (Fin 1) R :=
  X 0 * (X 0 - 1)

/-- **(T-E14-AX1)** The T-E14 moduli ring `R[λ][(λ(λ−1))⁻¹]` — KM 4.6.2's
`M'₂` (over `ℤ[1/2]`: `Spec ℤ[1/2][λ][(λ(λ−1))⁻¹]`). -/
abbrev LegendreModuliRing : Type u :=
  Localization.Away (legendrePoly R)

/-- **(T-E14-AX1)** The universal Legendre parameter `λ`. -/
def universalLambda : LegendreModuliRing R :=
  algebraMap (MvPolynomial (Fin 1) R) (LegendreModuliRing R) (X 0)

/-- **(T-E14-AX1)** The universal Legendre curve `y² = x(x−1)(x−λ)` over the moduli
ring. -/
def universalLegendre : WeierstrassCurve (LegendreModuliRing R) :=
  legendreCurve (universalLambda R)

instance : (universalLegendre R).IsCharNeTwoNF :=
  ⟨rfl, rfl⟩

/-- `λ(λ−1)` is invertible in the moduli ring (self-localization). -/
theorem isUnit_universalLambda_mul :
    IsUnit (universalLambda R * (universalLambda R - 1)) := by
  have e1 : algebraMap (MvPolynomial (Fin 1) R) (LegendreModuliRing R)
      (X 0 * (X 0 - 1)) = universalLambda R * (universalLambda R - 1) := by
    rw [map_mul, map_sub, map_one]
    rfl
  rw [show universalLambda R * (universalLambda R - 1) =
    algebraMap (MvPolynomial (Fin 1) R) (LegendreModuliRing R) (legendrePoly R) from
    e1.symm]
  exact IsLocalization.Away.algebraMap_isUnit (S := LegendreModuliRing R)
    (legendrePoly R)

/-- **(T-E14-AX1)** Over `2`-invertible bases the universal Legendre curve is
elliptic: `Δ = 16 λ²(λ−1)²` with both factors units. -/
theorem universalLegendre_isElliptic (hR : IsUnit (2 : R)) :
    (universalLegendre R).IsElliptic := by
  rw [universalLegendre, legendreCurve_isElliptic_iff]
  · exact isUnit_universalLambda_mul R
  · have h2 : IsUnit ((algebraMap R (LegendreModuliRing R)) (2 : R)) := hR.map _
    rwa [map_ofNat] at h2

/-- **(T-E14-AX1)** The universal Legendre `Ell/R`-object: `M'₂` carrying the
universal Legendre curve. -/
def universalLegendreObj (hR : IsUnit (2 : R)) : EllObj R :=
  haveI := universalLegendre_isElliptic R hR
  { base := Spec (CommRingCat.of (LegendreModuliRing R))
    structMap := Spec.map (CommRingCat.ofHom (algebraMap R (LegendreModuliRing R)))
    curve := modelEllipticCurve (universalLegendre R) }

/-- **(T-E14-AX1)** The universally marked section `P = (0, 0)` of the universal
Legendre curve. -/
def universalLegendreP (hR : IsUnit (2 : R)) :
    (universalLegendreObj R hR).curve.Section :=
  ⟨projModelAffineSection (universalLegendre R) 0 0
      (legendreCurve_equation_zero (universalLambda R)),
    projModelAffineSection_projModelπ _ _ _ _⟩

/-- **(T-E14-AX1)** The universally marked section `Q = (1, 0)` of the universal
Legendre curve. -/
def universalLegendreQ (hR : IsUnit (2 : R)) :
    (universalLegendreObj R hR).curve.Section :=
  ⟨projModelAffineSection (universalLegendre R) 1 0
      (legendreCurve_equation_one (universalLambda R)),
    projModelAffineSection_projModelπ _ _ _ _⟩

/-- **(T-E14-AX1)** The universal `ω`-basis of the Legendre object, from the
tautological presentation (mirrors `universalOmegaBasis`). -/
def universalLegendreOmega (hR : IsUnit (2 : R)) :
    OmegaBasis (universalLegendreObj R hR).curve.toEllipticCurveGeom :=
  haveI := universalLegendre_isElliptic R hR
  OmegaBasis.ofPresentation rfl (tautPresentation (universalLegendre R))

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E14-AX1 stage 3 ★)** The tautological presentation marks the affine-point
section at the (mapped) point: the universal marking. Mirrors `tautPresentation`'s
`compat_zero` with `projModelAffineSection_baseChange` in place of
`projModelZero_baseChange`. -/
theorem tautPresentation_marksAt {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    [W.IsElliptic] (p q : A) (h : W.toAffine.Equation p q) :
    (tautPresentation W).MarksAt
      (σ := projModelAffineSection W p q h)
      (projModelAffineSection_projModelπ W p q h)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom p)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom q) := by
  set S := Spec (CommRingCat.of A) with hS
  letI : Algebra A ↑Γ(S, (⊤ : S.Opens)) :=
    (Scheme.ΓSpecIso (.of A)).inv.hom.toAlgebra
  haveI : IsIso (⊤ : S.Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  haveI : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap A ↑Γ(S, (⊤ : S.Opens))))) := by
    have h' : CommRingCat.ofHom (algebraMap A ↑Γ(S, (⊤ : S.Opens))) =
        (Scheme.ΓSpecIso (.of A)).inv := rfl
    rw [h']
    infer_instance
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) =
      S.isoSpec.inv := (Scheme.isoSpec_Spec_inv (.of A)).symm
  refine ⟨WeierstrassCurve.Affine.Equation.map _ h, ?_⟩
  have hcrux : (isAffineOpen_top S).isoSpec.inv ≫ (⊤ : S.Opens).ι =
      Spec.map (CommRingCat.ofHom (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) :=
    hφ ▸ (IsAffineOpen.isoSpec_inv_ι _).trans IsAffineOpen.fromSpec_top
  have hcrux_assoc : ∀ {Z : Scheme.{u}} (g : S ⟶ Z),
      (isAffineOpen_top S).isoSpec.inv ≫ (⊤ : S.Opens).ι ≫ g =
        Spec.map (CommRingCat.ofHom
          (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) ≫ g := fun g => by
    rw [← Category.assoc]
    exact congrArg (· ≫ g) hcrux
  rw [show (tautPresentation W).e.hom =
    (asIso (pullback.fst (projModelπ W) (⊤ : S.Opens).ι) ≪≫
      (asIso (pullback.fst (projModelπ W) (Spec.map (CommRingCat.ofHom
        (algebraMap A ↑Γ(S, (⊤ : S.Opens))))))).symm ≪≫
      (isPullback_projModelBaseChange W).isoPullback.symm).hom from rfl]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc]
  show (isAffineOpen_top S).isoSpec.inv ≫ pullback.lift
      ((⊤ : S.Opens).ι ≫ projModelAffineSection W p q h) (𝟙 _) _ ≫
    pullback.fst (projModelπ W) (⊤ : S.Opens).ι ≫
    inv (pullback.fst (projModelπ W) (Spec.map (CommRingCat.ofHom
      (algebraMap A ↑Γ(S, (⊤ : S.Opens)))))) ≫
    (isPullback_projModelBaseChange W).isoPullback.inv = _
  erw [pullback.lift_fst_assoc]
  simp only [Category.assoc]
  conv_lhs => erw [hcrux_assoc]
  erw [← reassoc_of% projModelAffineSection_baseChange W p q h
      (WeierstrassCurve.Affine.Equation.map _ h),
    ← (isPullback_projModelBaseChange W).isoPullback_hom_fst_assoc,
    IsIso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-AX1 stage 4)** The tautological presentation of the universal Legendre
curve is adapted to the universal `ω`-basis it induces (the curve-generic
`tautPresentation_isAdapted`). -/
theorem tautPresentation_isAdapted_legendre (hR : IsUnit (2 : R)) :
    haveI := universalLegendre_isElliptic R hR
    (tautPresentation (universalLegendre R)).IsAdapted
      (universalLegendreOmega R hR) := by
  haveI := universalLegendre_isElliptic R hR
  have h : ((tautPresentation (universalLegendre R)).restrict
      (le_refl (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
        (LegendreModuliRing R))).affineOpens).1)).IsAdapted
      (universalLegendreOmega R hR) :=
    isAdapted_restrict_ofPresentation rfl (tautPresentation (universalLegendre R))
      (le_refl _)
  show ((tautPresentation (universalLegendre R)).basisUnitAt
    (universalLegendreOmega R hR)).1 = 1
  have h' : (((tautPresentation (universalLegendre R)).restrict
      (le_refl _)).basisUnitAt (universalLegendreOmega R hR)).1 = 1 := h
  rw [← basisUnitAt_restrict (tautPresentation (universalLegendre R))
    (universalLegendreOmega R hR) (le_refl _)] at h'
  rw [← h']
  exact (Units.ext (by simp)).symm

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E14-AX1 stage 4 ★)** The universal Legendre datum: given the naive-full-level
clause for the marked pair (2-torsionness + geometric generation — ticket [T-E14-LVL],
the leaf-(a) `E[2]`-classification input), the tautologically marked pair with the
universal `ω`-basis IS a Legendre datum: the tautological presentation is adapted,
its curve is the Legendre curve of the universal `λ`, and it marks `P` at `(0, 0)`
and `Q` at `(1, 0)`. -/
theorem universalLegendre_isLegendreDatum (hR : IsUnit (2 : R))
    (hL : (universalLegendreObj R hR).curve.IsNaiveFullLevel 2
      (universalLegendreP R hR) (universalLegendreQ R hR)) :
    IsLegendreDatum (universalLegendreObj R hR)
      ⟨⟨universalLegendreP R hR, universalLegendreQ R hR⟩, hL⟩
      (universalLegendreOmega R hR) := by
  haveI := universalLegendre_isElliptic R hR
  haveI : IsAffine (universalLegendreObj R hR).base :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (LegendreModuliRing R))))
  intro s
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial,
    tautPresentation (universalLegendre R),
    (Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom
      (universalLambda R), ?_, ?_, ?_, ?_⟩
  · exact tautPresentation_isAdapted_legendre R hR
  · show (universalLegendre R).map _ = _
    rw [show universalLegendre R = legendreCurve (universalLambda R) from rfl,
      legendreCurve_map]
    rfl
  · have h := tautPresentation_marksAt (universalLegendre R) 0 0
      (legendreCurve_equation_zero (universalLambda R))
    rw [map_zero] at h
    exact h
  · have h := tautPresentation_marksAt (universalLegendre R) 1 0
      (legendreCurve_equation_one (universalLambda R))
    rw [map_one, map_zero] at h
    exact h

section TwoTorsion

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousIdeal HomogeneousLocalization in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-LVL, the negation-fix)** The model negation fixes an affine-point section
whose `y`-coordinate is negation-symmetric (`−q − a₁p − a₃ = q`) — for `2`-torsion
points this is exactly the fibrewise `P = −P`. Mirrors `negModelHom_zero` via
`Proj.fromOfGlobalSections_map`; no `allNeg` rescaling is needed since `Z ↦ Z`. -/
theorem negModelHom_affineSection {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    (p q : A) (h : W.toAffine.Equation p q) (hq : -q - W.a₁ * p - W.a₃ = q) :
    projModelAffineSection W p q h ≫ negModelHom W =
      projModelAffineSection W p q h := by
  have hfeq : ((Scheme.ΓSpecIso (.of A)).inv.hom.comp
        (projModelAffineEval W p q h)).comp (negGradedQuot W).toRingHom =
      (Scheme.ΓSpecIso (.of A)).inv.hom.comp (projModelAffineEval W p q h) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine congrArg (Scheme.ΓSpecIso (.of A)).inv.hom ?_
    rw [show (negGradedQuot W).toRingHom (Ideal.Quotient.mk (projIdeal W).toIdeal a) =
      Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.aeval (negVec W) a) from
      quotientGradingMap_mk _ _ _ _ a]
    rw [projModelAffineEval_mk, projModelAffineEval_mk]
    rw [show (MvPolynomial.aeval (negVec W) a :
        MvPolynomial (Fin 3) A) = MvPolynomial.bind₁ (negVec W) a from by
      rw [MvPolynomial.aeval_eq_bind₁]]
    rw [show MvPolynomial.eval ![p, q, 1] (MvPolynomial.bind₁ (negVec W) a) =
      MvPolynomial.eval (fun i => MvPolynomial.eval ![p, q, 1] (negVec W i)) a from by
      rw [← MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_bind₁]
      rfl]
    refine congrArg (fun v => MvPolynomial.eval v a) ?_
    funext i
    fin_cases i
    · simp [negVec]
    · show MvPolynomial.eval ![p, q, 1] (-MvPolynomial.X 1 -
        MvPolynomial.C W.a₁ * MvPolynomial.X 0 -
        MvPolynomial.C W.a₃ * MvPolynomial.X 2) = q
      simp only [MvPolynomial.eval_sub, MvPolynomial.eval_neg, MvPolynomial.eval_mul,
        MvPolynomial.eval_C, MvPolynomial.eval_X]
      show -q - W.a₁ * p - W.a₃ * 1 = q
      linear_combination hq
    · simp [negVec]
  have key := Proj.fromOfGlobalSections_map (negGradedQuot W)
    (negGradedQuot_irrelevant_le W)
    ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (projModelAffineEval W p q h))
    (projModelAffineEval_irrelevant_map_top W p q h)
    (Proj.irrelevant_map_comp_toRingHom_eq_top (negGradedQuot W)
      (negGradedQuot_irrelevant_le W) _
      (projModelAffineEval_irrelevant_map_top W p q h))
  have congr_from : ∀ (g₁ g₂ : projCoordRing W →+* Γ(Spec (.of A), ⊤))
      (h₁ : (HomogeneousIdeal.irrelevant
          (quotientGrading (projIdeal W))).toIdeal.map g₁ = ⊤)
      (h₂ : (HomogeneousIdeal.irrelevant
          (quotientGrading (projIdeal W))).toIdeal.map g₂ = ⊤)
      (hg : g₁ = g₂),
      Proj.fromOfGlobalSections _ g₁ h₁ = Proj.fromOfGlobalSections _ g₂ h₂ := by
    rintro g₁ g₂ h₁ h₂ rfl
    rfl
  rw [show projModelAffineSection W p q h ≫ negModelHom W =
    Proj.fromOfGlobalSections _
      (((Scheme.ΓSpecIso (.of A)).inv.hom.comp
        (projModelAffineEval W p q h)).comp (negGradedQuot W).toRingHom)
      (Proj.irrelevant_map_comp_toRingHom_eq_top (negGradedQuot W)
        (negGradedQuot_irrelevant_le W) _
        (projModelAffineEval_irrelevant_map_top W p q h)) from key]
  exact congr_from _ _ _ _ hfeq

/-- **(T-E14-LVL)** The universal marked section `P = (0,0)` is negation-fixed:
`a₁ = a₃ = 0` and `y = 0` make the fibrewise `P = −P` an identity. -/
theorem negModelHom_universalLegendreP (hR : IsUnit (2 : R)) :
    (universalLegendreP R hR).1 ≫ negModelHom (universalLegendre R) =
      (universalLegendreP R hR).1 :=
  negModelHom_affineSection (universalLegendre R) 0 0 _ (by
    show -0 - (universalLegendre R).a₁ * 0 - (universalLegendre R).a₃ = 0
    rw [show (universalLegendre R).a₁ = 0 from rfl,
      show (universalLegendre R).a₃ = 0 from rfl]
    ring)

/-- **(T-E14-LVL)** The universal marked section `Q = (1,0)` is negation-fixed. -/
theorem negModelHom_universalLegendreQ (hR : IsUnit (2 : R)) :
    (universalLegendreQ R hR).1 ≫ negModelHom (universalLegendre R) =
      (universalLegendreQ R hR).1 :=
  negModelHom_affineSection (universalLegendre R) 1 0 _ (by
    show -0 - (universalLegendre R).a₁ * 1 - (universalLegendre R).a₃ = 0
    rw [show (universalLegendre R).a₁ = 0 from rfl,
      show (universalLegendre R).a₃ = 0 from rfl]
    ring)

open CategoryTheory.CartesianMonoidalCategory in
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-LVL-a ★)** On the model curve, multiplication by `−1` IS the model
negation: the group-object inverse of `modelGrpObj` is `invOver`, whose underlying
morphism is `negModelHom` (`invOver_left`); `[−1] = (𝟙)⁻¹ = 𝟙 ≫ ι = ι`. -/
theorem modelEllipticCurve_mulByHom_neg_one {A : Type u} [CommRing A]
    (W : WeierstrassCurve A) [W.IsElliptic] :
    (modelEllipticCurve W).mulByHom (-1) = negModelHom W := by
  show ((modelEllipticCurve W).mulBy (-1)).left = negModelHom W
  rw [show (modelEllipticCurve W).mulBy (-1) =
    (letI : Group ((modelEllipticCurve W).asOver ⟶ (modelEllipticCurve W).asOver) :=
      CategoryTheory.Hom.group
     (𝟙 (modelEllipticCurve W).asOver) ^ (-1 : ℤ)) from rfl]
  letI : Group ((modelEllipticCurve W).asOver ⟶ (modelEllipticCurve W).asOver) :=
    CategoryTheory.Hom.group
  rw [zpow_neg_one, CategoryTheory.Hom.inv_def, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-LVL-a ★)** The universally marked `P = (0,0)` is `2`-torsion:
`P = −P` (negation-fix) forces `[2]P = 0`. -/
theorem two_zsmul_universalLegendreP (hR : IsUnit (2 : R)) :
    (2 : ℤ) • universalLegendreP R hR = 0 := by
  haveI := universalLegendre_isElliptic R hR
  have h1 : ((-1 : ℤ) • universalLegendreP R hR :
      (universalLegendreObj R hR).curve.Section).1 = (universalLegendreP R hR).1 := by
    rw [EllipticCurve.point_smul_eq_comp_mulBy]
    rw [show (universalLegendreObj R hR).curve.mulByHom (-1) =
      negModelHom (universalLegendre R) from
      modelEllipticCurve_mulByHom_neg_one (universalLegendre R)]
    exact negModelHom_universalLegendreP R hR
  have h2 : -universalLegendreP R hR = universalLegendreP R hR := by
    rw [← neg_one_zsmul]
    exact Subtype.ext h1
  calc (2 : ℤ) • universalLegendreP R hR
      = universalLegendreP R hR + universalLegendreP R hR := two_zsmul _
    _ = universalLegendreP R hR + -universalLegendreP R hR := by rw [h2]
    _ = 0 := add_neg_cancel _

set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-LVL-a ★)** The universally marked `Q = (1,0)` is `2`-torsion. -/
theorem two_zsmul_universalLegendreQ (hR : IsUnit (2 : R)) :
    (2 : ℤ) • universalLegendreQ R hR = 0 := by
  haveI := universalLegendre_isElliptic R hR
  have h1 : ((-1 : ℤ) • universalLegendreQ R hR :
      (universalLegendreObj R hR).curve.Section).1 = (universalLegendreQ R hR).1 := by
    rw [EllipticCurve.point_smul_eq_comp_mulBy]
    rw [show (universalLegendreObj R hR).curve.mulByHom (-1) =
      negModelHom (universalLegendre R) from
      modelEllipticCurve_mulByHom_neg_one (universalLegendre R)]
    exact negModelHom_universalLegendreQ R hR
  have h2 : -universalLegendreQ R hR = universalLegendreQ R hR := by
    rw [← neg_one_zsmul]
    exact Subtype.ext h1
  calc (2 : ℤ) • universalLegendreQ R hR
      = universalLegendreQ R hR + universalLegendreQ R hR := two_zsmul _
    _ = universalLegendreQ R hR + -universalLegendreQ R hR := by rw [h2]
    _ = 0 := add_neg_cancel _

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-1c)** The variable change carries curve-points to curve-points, in
coordinates: if `(p, q)` lies on `C • W` then `(u²p + r, u³q + su²p + t)` lies on `W`
(the coordinate form of the projective identity `vcMvSubst_polynomial`). -/
theorem equation_smul_image {A : Type u} [CommRing A]
    (C : VariableChange A) (W : WeierstrassCurve A) {p q : A}
    (h : (C • W).toAffine.Equation p q) :
    W.toAffine.Equation ((C.u : A) ^ 2 * p + C.r)
      ((C.u : A) ^ 3 * q + C.s * (C.u : A) ^ 2 * p + C.t) := by
  have hproj : MvPolynomial.eval ![p, q, 1] (C • W).toProjective.polynomial = 0 := by
    rw [WeierstrassCurve.Projective.eval_polynomial]
    have he := (WeierstrassCurve.Affine.equation_iff
      (W := (C • W).toAffine) p q).mp h
    show q ^ 2 * 1 + (C • W).a₁ * p * q * 1 + (C • W).a₃ * q * 1 ^ 2 -
      (p ^ 3 + (C • W).a₂ * p ^ 2 * 1 + (C • W).a₄ * p * 1 ^ 2 +
        (C • W).a₆ * 1 ^ 3) = 0
    linear_combination he
  have hsub : MvPolynomial.eval ![(C.u : A) ^ 2 * p + C.r,
      (C.u : A) ^ 3 * q + C.s * (C.u : A) ^ 2 * p + C.t, 1]
      W.toProjective.polynomial =
    MvPolynomial.eval ![p, q, 1]
      (MvPolynomial.aeval (vcMvSubst C) W.toProjective.polynomial) := by
    rw [show (MvPolynomial.aeval (vcMvSubst C) W.toProjective.polynomial :
        MvPolynomial (Fin 3) A) =
      MvPolynomial.bind₁ (vcMvSubst C) W.toProjective.polynomial from by
      rw [MvPolynomial.aeval_eq_bind₁]]
    rw [show MvPolynomial.eval ![p, q, 1]
        (MvPolynomial.bind₁ (vcMvSubst C) W.toProjective.polynomial) =
      MvPolynomial.eval (fun i => MvPolynomial.eval ![p, q, 1] (vcMvSubst C i))
        W.toProjective.polynomial from by
      rw [← MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_bind₁]
      rfl]
    refine congrArg (fun v => MvPolynomial.eval v W.toProjective.polynomial) ?_
    funext i
    fin_cases i
    · show ((C.u : A) ^ 2 * p + C.r : A) =
        MvPolynomial.eval ![p, q, 1] ((C.u : A) ^ 2 • MvPolynomial.X 0 +
          C.r • MvPolynomial.X 2)
      simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_add,
        MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      show (C.u : A) ^ 2 * p + C.r = (C.u : A) ^ 2 * p + C.r * 1
      ring
    · show ((C.u : A) ^ 3 * q + C.s * (C.u : A) ^ 2 * p + C.t : A) =
        MvPolynomial.eval ![p, q, 1] ((C.u : A) ^ 3 • MvPolynomial.X 1 +
          (C.s * (C.u : A) ^ 2) • MvPolynomial.X 0 + C.t • MvPolynomial.X 2)
      simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_add,
        MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      show _ = (C.u : A) ^ 3 * q + C.s * (C.u : A) ^ 2 * p + C.t * 1
      ring
    · simp [vcMvSubst]
  have hzero : MvPolynomial.eval ![(C.u : A) ^ 2 * p + C.r,
      (C.u : A) ^ 3 * q + C.s * (C.u : A) ^ 2 * p + C.t, 1]
      W.toProjective.polynomial = 0 := by
    rw [hsub, vcMvSubst_polynomial C W]
    rw [show ((C.u : A) ^ 6 • (C • W).toProjective.polynomial :
      MvPolynomial (Fin 3) A) =
      MvPolynomial.C ((C.u : A) ^ 6) * (C • W).toProjective.polynomial from
      MvPolynomial.smul_eq_C_mul _ _]
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, hproj, mul_zero]
  rw [WeierstrassCurve.Projective.eval_polynomial] at hzero
  have hzero' : ((C.u : A) ^ 3 * q + C.s * (C.u : A) ^ 2 * p + C.t) ^ 2 * 1 +
      W.a₁ * ((C.u : A) ^ 2 * p + C.r) *
        ((C.u : A) ^ 3 * q + C.s * (C.u : A) ^ 2 * p + C.t) * 1 +
      W.a₃ * ((C.u : A) ^ 3 * q + C.s * (C.u : A) ^ 2 * p + C.t) * 1 ^ 2 -
      (((C.u : A) ^ 2 * p + C.r) ^ 3 + W.a₂ * ((C.u : A) ^ 2 * p + C.r) ^ 2 * 1 +
        W.a₄ * ((C.u : A) ^ 2 * p + C.r) * 1 ^ 2 + W.a₆ * 1 ^ 3) = 0 := hzero
  rw [WeierstrassCurve.Affine.equation_iff]
  linear_combination hzero'

open HomogeneousIdeal HomogeneousLocalization in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-1a ★)** The variable-change model isomorphism acts on affine-point
sections by the coordinate change: `[p : q : 1]` of `C • W` is carried to
`[u²p + r : u³q + su²p + t : 1]` of `W`. Mirrors `negModelHom_affineSection`
(`projModelVCIso.hom = Proj.map (vcGradedHom C W)`, substitution `vcMvSubst`). -/
theorem projModelVCIso_affineSection {A : Type u} [CommRing A]
    (C : WeierstrassCurve.VariableChange A) (W : WeierstrassCurve A) (p q : A)
    (h : (C • W).toAffine.Equation p q)
    (h' : W.toAffine.Equation ((C.u : A) ^ 2 * p + C.r)
      ((C.u : A) ^ 3 * q + C.s * (C.u : A) ^ 2 * p + C.t)) :
    projModelAffineSection (C • W) p q h ≫ (projModelVCIso C W).hom =
      projModelAffineSection W ((C.u : A) ^ 2 * p + C.r)
        ((C.u : A) ^ 3 * q + C.s * (C.u : A) ^ 2 * p + C.t) h' := by
  have hfeq : ((Scheme.ΓSpecIso (.of A)).inv.hom.comp
        (projModelAffineEval (C • W) p q h)).comp (vcGradedHom C W).toRingHom =
      (Scheme.ΓSpecIso (.of A)).inv.hom.comp
        (projModelAffineEval W ((C.u : A) ^ 2 * p + C.r)
          ((C.u : A) ^ 3 * q + C.s * (C.u : A) ^ 2 * p + C.t) h') := by
    refine RingHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine congrArg (Scheme.ΓSpecIso (.of A)).inv.hom ?_
    rw [show (vcGradedHom C W).toRingHom (Ideal.Quotient.mk (projIdeal W).toIdeal a) =
      Ideal.Quotient.mk (projIdeal (C • W)).toIdeal
        (MvPolynomial.aeval (vcMvSubst C) a) from
      quotientGradingMap_mk _ _ _ _ a]
    rw [projModelAffineEval_mk, projModelAffineEval_mk]
    rw [show (MvPolynomial.aeval (vcMvSubst C) a :
        MvPolynomial (Fin 3) A) = MvPolynomial.bind₁ (vcMvSubst C) a from by
      rw [MvPolynomial.aeval_eq_bind₁]]
    rw [show MvPolynomial.eval ![p, q, 1] (MvPolynomial.bind₁ (vcMvSubst C) a) =
      MvPolynomial.eval (fun i => MvPolynomial.eval ![p, q, 1] (vcMvSubst C i)) a from by
      rw [← MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_bind₁]
      rfl]
    refine congrArg (fun v => MvPolynomial.eval v a) ?_
    funext i
    fin_cases i
    · show MvPolynomial.eval ![p, q, 1] ((C.u : A) ^ 2 • MvPolynomial.X 0 +
        C.r • MvPolynomial.X 2) = (C.u : A) ^ 2 * p + C.r
      simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_add,
        MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      show (C.u : A) ^ 2 * p + C.r * 1 = (C.u : A) ^ 2 * p + C.r
      ring
    · show MvPolynomial.eval ![p, q, 1] ((C.u : A) ^ 3 • MvPolynomial.X 1 +
        (C.s * (C.u : A) ^ 2) • MvPolynomial.X 0 + C.t • MvPolynomial.X 2) =
        (C.u : A) ^ 3 * q + C.s * (C.u : A) ^ 2 * p + C.t
      simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_add,
        MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      show (C.u : A) ^ 3 * q + C.s * (C.u : A) ^ 2 * p + C.t * 1 = _
      ring
    · simp [vcMvSubst]
  have key := Proj.fromOfGlobalSections_map (vcGradedHom C W)
    (vcGradedHom_irrelevant_le C W)
    ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (projModelAffineEval (C • W) p q h))
    (projModelAffineEval_irrelevant_map_top (C • W) p q h)
    (Proj.irrelevant_map_comp_toRingHom_eq_top (vcGradedHom C W)
      (vcGradedHom_irrelevant_le C W) _
      (projModelAffineEval_irrelevant_map_top (C • W) p q h))
  have congr_from : ∀ (g₁ g₂ : projCoordRing W →+* Γ(Spec (.of A), ⊤))
      (h₁ : (HomogeneousIdeal.irrelevant
          (quotientGrading (projIdeal W))).toIdeal.map g₁ = ⊤)
      (h₂ : (HomogeneousIdeal.irrelevant
          (quotientGrading (projIdeal W))).toIdeal.map g₂ = ⊤)
      (hg : g₁ = g₂),
      Proj.fromOfGlobalSections _ g₁ h₁ = Proj.fromOfGlobalSections _ g₂ h₂ := by
    rintro g₁ g₂ h₁ h₂ rfl
    rfl
  rw [show projModelAffineSection (C • W) p q h ≫ (projModelVCIso C W).hom =
    Proj.fromOfGlobalSections _
      (((Scheme.ΓSpecIso (.of A)).inv.hom.comp
        (projModelAffineEval (C • W) p q h)).comp (vcGradedHom C W).toRingHom)
      (Proj.irrelevant_map_comp_toRingHom_eq_top (vcGradedHom C W)
        (vcGradedHom_irrelevant_le C W) _
        (projModelAffineEval_irrelevant_map_top (C • W) p q h)) from key]
  exact congr_from _ _ _ _ hfeq

open HomogeneousIdeal HomogeneousLocalization in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-1b ★)** Affine-point sections determine their coordinates: the
`Z`-chart factorisation is `Spec` of the evaluation, and evaluating the chart
fractions `X/Z`, `Y/Z` reads back `p` and `q`. -/
theorem projModelAffineSection_injective {A : Type u} [CommRing A]
    (W : WeierstrassCurve A) {p₁ q₁ p₂ q₂ : A}
    (h₁ : W.toAffine.Equation p₁ q₁) (h₂ : W.toAffine.Equation p₂ q₂)
    (heq : projModelAffineSection W p₁ q₁ h₁ = projModelAffineSection W p₂ q₂ h₂) :
    p₁ = p₂ ∧ q₁ = q₂ := by
  have hchart : projModelAffineChart W p₁ q₁ h₁ = projModelAffineChart W p₂ q₂ h₂ := by
    rw [← cancel_mono (Proj.awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos),
      projModelAffineChart_fac, projModelAffineChart_fac, heq]
  rw [projModelAffineChart_eq_spec, projModelAffineChart_eq_spec] at hchart
  have hhom : affineChartHom W p₁ q₁ h₁ = affineChartHom W p₂ q₂ h₂ := by
    have := Spec.map_injective hchart
    exact congrArg CommRingCat.Hom.hom this
  constructor
  · have hx := congrArg (fun g => g (HomogeneousLocalization.Away.mk
      (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) 1
      (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X 0))
      (mk_X_mem_quotientGrading_one W 0))) hhom
    simpa only [affineChartHom_mk, projModelAffineEval_mk, MvPolynomial.eval_X,
      Matrix.cons_val_zero] using hx
  · have hy := congrArg (fun g => g (HomogeneousLocalization.Away.mk
      (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) 1
      (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X 1))
      (mk_X_mem_quotientGrading_one W 1))) hhom
    have hy' : (![p₁, q₁, 1] : Fin 3 → A) 1 = (![p₂, q₂, 1] : Fin 3 → A) 1 := by
      simpa only [affineChartHom_mk, projModelAffineEval_mk,
        MvPolynomial.eval_X] using hy
    exact hy'

/-- Affine-point sections transport along equalities of curves. -/
theorem projModelAffineSection_congr {A : Type u} [CommRing A]
    {W₁ W₂ : WeierstrassCurve A} (hW : W₁ = W₂) (p q : A)
    (h : W₁.toAffine.Equation p q) :
    projModelAffineSection W₁ p q h ≫ eqToHom (congrArg projModel hW) =
      projModelAffineSection W₂ p q (hW ▸ h) := by
  cases hW
  rw [eqToHom_refl, Category.comp_id]

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E14-CLS-1 ★★, KM 4.6.2 uniqueness)** Marked adapted Legendre witnesses are
UNIQUE: two `b`-adapted presentations over the same affine whose chart curves are
Legendre and which mark the same section at `x = 0` have comparison `1` and equal
`λ`'s — the `ω` pins `u = 1, s = t = 0` (`transVC_of_isAdapted_charNeTwo`) and the
marking pins `r = 0`. KM's classifying function is well-defined. -/
theorem legendre_witness_transVC_eq_one {S : Scheme.{u}} {G : EllipticCurveGeom S}
    {V : S.affineOpens} {Pr Qr : LocalPresentation G V} {b : OmegaBasis G}
    (hPrAd : Pr.IsAdapted b) (hQrAd : Qr.IsAdapted b)
    {lamP lamQ : Γ(S, V.1)} (hPrW : Pr.W = legendreCurve lamP)
    (hQrW : Qr.W = legendreCurve lamQ)
    {σ : S ⟶ G.E} {hσ : σ ≫ G.π = 𝟙 S}
    (hPrM : Pr.MarksAt hσ 0 0) (hQrM : Qr.MarksAt hσ 0 0)
    (h2 : IsUnit (2 : Γ(S, V.1))) :
    Pr.transVC Qr = 1 ∧ lamP = lamQ := by
  have hPrNF : Pr.W.IsCharNeTwoNF := by rw [hPrW]; infer_instance
  have hQrNF : Qr.W.IsCharNeTwoNF := by rw [hQrW]; infer_instance
  have hC := transVC_of_isAdapted_charNeTwo hPrAd hQrAd hPrNF hQrNF h2
  obtain ⟨hP0, hPeq⟩ := hPrM
  obtain ⟨hQ0, hQeq⟩ := hQrM
  -- the marking chase: both witnesses read `σ` on `Qr`'s chart
  have hchase : projModelAffineSection Pr.W 0 0 hP0 ≫ (Pr.pointedIso Qr).hom =
      projModelAffineSection Qr.W 0 0 hQ0 := by
    rw [← hPeq, ← hQeq]
    show ((V.2.isoSpec.inv ≫ sectionLift G hσ V) ≫ Pr.e.hom) ≫
      (Pr.e.symm ≪≫ Qr.e).hom = _
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc,
      Iso.hom_inv_id_assoc]
    rw [Category.assoc]
  rw [Pr.transVC_spec Qr] at hchase
  have hWeq : Pr.W = Pr.transVC Qr • Qr.W := (Pr.transVC_smul Qr).symm
  rw [← Category.assoc, projModelAffineSection_congr hWeq 0 0 hP0] at hchase
  rw [projModelVCIso_affineSection (Pr.transVC Qr) Qr.W 0 0 (hWeq ▸ hP0)
    (equation_smul_image (Pr.transVC Qr) Qr.W (hWeq ▸ hP0))] at hchase
  -- injectivity reads off the translation
  have hcoords := projModelAffineSection_injective Qr.W _ hQ0 hchase
  have hr : (Pr.transVC Qr).r = 0 := by
    have h := hcoords.1
    rwa [mul_zero, zero_add] at h
  -- assemble `C = 1`
  have hone : Pr.transVC Qr = 1 := by
    rw [hC, hr]
    rfl
  refine ⟨hone, ?_⟩
  -- equal curves force equal `λ`'s
  have hWW : Qr.W = Pr.W := by
    have h := Pr.transVC_smul Qr
    rwa [hone, one_smul] at h
  have hLL : legendreCurve lamQ = legendreCurve lamP := by
    rw [← hPrW, ← hQrW]
    exact hWW
  have h4 := congrArg WeierstrassCurve.a₄ hLL
  rw [legendreCurve_a₄, legendreCurve_a₄] at h4
  exact h4.symm

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-2)** The chart curve of a restricted presentation stays Legendre,
with the restricted parameter. -/
theorem restrict_W_legendre {S : Scheme.{u}} {G : EllipticCurveGeom S}
    {V : S.affineOpens} {Pr : LocalPresentation G V} {lam : Γ(S, V.1)}
    (hW : Pr.W = legendreCurve lam) {V' : S.affineOpens} (h : V'.1 ≤ V.1) :
    (Pr.restrict h).W = legendreCurve (Scheme.resLE h lam) := by
  show Pr.W.map (sectionsMapLE (𝟙 S) (by simpa using h)) = _
  rw [hW, legendreCurve_map]
  exact congrArg legendreCurve
    (congrArg (fun (g : Γ(S, V.1) →+* Γ(S, V'.1)) => g lam)
      (sectionsMapLE_id (by simpa using h)))

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E14-CLS-2 ★)** Witness `λ`-values agree on common affines: restrict both
witnesses and apply the KM 4.6.2 uniqueness. -/
theorem legendre_witness_lam_agree {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    {V₁ V₂ : X.base.affineOpens}
    {Pr₁ : LocalPresentation X.curve.toEllipticCurveGeom V₁}
    {Pr₂ : LocalPresentation X.curve.toEllipticCurveGeom V₂}
    {lam₁ : Γ(X.base, V₁.1)} {lam₂ : Γ(X.base, V₂.1)}
    (hAd₁ : Pr₁.IsAdapted b) (hAd₂ : Pr₂.IsAdapted b)
    (hW₁ : Pr₁.W = legendreCurve lam₁) (hW₂ : Pr₂.W = legendreCurve lam₂)
    (hM₁ : Pr₁.MarksAt L.1.1.2 0 0) (hM₂ : Pr₂.MarksAt L.1.1.2 0 0)
    {W : X.base.affineOpens} (hWV₁ : W.1 ≤ V₁.1) (hWV₂ : W.1 ≤ V₂.1) :
    Scheme.resLE hWV₁ lam₁ = Scheme.resLE hWV₂ lam₂ := by
  have hres₁ := hM₁.restrict hWV₁
  have hres₂ := hM₂.restrict hWV₂
  rw [map_zero] at hres₁ hres₂
  exact (legendre_witness_transVC_eq_one
    (hAd₁.restrict hWV₁) (hAd₂.restrict hWV₂)
    (restrict_W_legendre hW₁ hWV₁) (restrict_W_legendre hW₂ hWV₂)
    hres₁ hres₂ (isUnit_ofNat_res h2 W.1)).2

open LocalPresentation WeierstrassCurve TopologicalSpace in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- **(T-E14-CLS-2 ★★)** The **glued Legendre parameter** of a Legendre datum: the
witness `λ`'s glue to a global section restricting to EVERY witness's parameter
(mirrors `adaptedCoeff₄`; agreement = `legendre_witness_lam_agree`). This is KM
4.6.2's classifying function `λ : S → M'₂`. -/
noncomputable def legendreLambda {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 2) (b : OmegaBasis X.curve.toEllipticCurveGeom)
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    { g : Γ(X.base, ⊤) //
      ∀ (V : X.base.affineOpens)
        (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
        (lam : Γ(X.base, V.1)), Pr.IsAdapted b → Pr.W = legendreCurve lam →
        Pr.MarksAt L.1.1.2 0 0 →
        Scheme.resLE (le_top : V.1 ≤ ⊤) g = lam } := by
  classical
  -- choose a witness at every point
  choose Vx hxVx Prx lamx hAdx hWx hMPx hMQx using hD
  have hcover : (⊤ : X.base.Opens) ≤ iSup (fun x : X.base => (Vx x).1) :=
    fun x _ => Opens.mem_iSup.mpr ⟨x, hxVx x⟩
  have hcoverInf : ∀ (V V' : X.base.Opens), V ⊓ V' ≤
      iSup (fun r : {W : X.base.affineOpens // W.1 ≤ V ⊓ V'} => r.1.1) := by
    intro V V' x hx
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨W₀, hWaff⟩, hWle⟩, hxW⟩
  have hpair : TopCat.Presheaf.IsCompatible X.base.sheaf.1
      (fun x : X.base => (Vx x).1) (fun x => lamx x) := by
    intro x y
    refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
      (fun r : {W : X.base.affineOpens // W.1 ≤ (Vx x).1 ⊓ (Vx y).1} => r.1.1)
      ((Vx x).1 ⊓ (Vx y).1) (fun r => homOfLE r.2) (hcoverInf _ _) _ _ (fun r => ?_)
    show Scheme.resLE r.2 (Scheme.resLE inf_le_left (lamx x)) =
      Scheme.resLE r.2 (Scheme.resLE inf_le_right (lamx y))
    rw [Scheme.resLE_resLE, Scheme.resLE_resLE]
    exact legendre_witness_lam_agree h2 (hAdx x) (hAdx y) (hWx x) (hWx y)
      (hMPx x) (hMPx y) (r.2.trans inf_le_left) (r.2.trans inf_le_right)
  have hglue := TopCat.Sheaf.existsUnique_gluing' X.base.sheaf
    (fun x : X.base => (Vx x).1) ⊤ (fun x => homOfLE le_top) hcover
    (fun x => lamx x) hpair
  refine ⟨hglue.choose, fun V Pr lam hAd hW hMP => ?_⟩
  -- the arbitrary-witness spec, by separation over refined overlaps
  refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
    (fun w : {w : X.base.affineOpens × X.base // w.1.1 ≤ V.1 ⊓ (Vx w.2).1} =>
      w.1.1.1) V.1 (fun w => homOfLE (w.2.trans inf_le_left)) ?_ _ _ (fun w => ?_)
  · intro x hxV
    have hx : x ∈ V.1 ⊓ (Vx x).1 := ⟨hxV, hxVx x⟩
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨⟨W₀, hWaff⟩, x⟩, hWle⟩, hxW⟩
  · obtain ⟨⟨W, x⟩, hWle⟩ := w
    show Scheme.resLE (hWle.trans inf_le_left)
        (Scheme.resLE (le_top : V.1 ≤ ⊤) hglue.choose) =
      Scheme.resLE (hWle.trans inf_le_left) lam
    rw [Scheme.resLE_resLE]
    have hg : Scheme.resLE ((hWle.trans inf_le_right).trans
        (le_top : (Vx x).1 ≤ ⊤)) hglue.choose =
        Scheme.resLE (hWle.trans inf_le_right) (lamx x) := by
      have h : Scheme.resLE (le_top : (Vx x).1 ≤ ⊤) hglue.choose = lamx x :=
        hglue.choose_spec.1 x
      have h' := congrArg (Scheme.resLE (hWle.trans inf_le_right)) h
      rwa [Scheme.resLE_resLE] at h'
    rw [show (hWle.trans inf_le_left).trans (le_top : V.1 ≤ ⊤) =
      ((hWle.trans inf_le_right).trans (le_top : (Vx x).1 ≤ ⊤)) from rfl, hg]
    exact legendre_witness_lam_agree h2 (hAdx x) hAd (hWx x) hW (hMPx x) hMP
      (hWle.trans inf_le_right) (hWle.trans inf_le_left)

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E14-CLS-3 ★)** The glued parameter satisfies the moduli condition:
`λ(λ−1)` is a global unit — chartwise it is the witness's `lam(lam−1)`, a unit by
ellipticity of the witness chart curve (mirrors `adaptedDelta_isUnit`). -/
theorem legendreLambda_isUnit {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 2) (b : OmegaBasis X.curve.toEllipticCurveGeom)
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    IsUnit ((legendreLambda X L b hD h2).1 *
      ((legendreLambda X L b hD h2).1 - 1)) := by
  apply X.base.toRingedSpace.isUnit_of_isUnit_germ
  intro x _
  obtain ⟨V, hxV, Pr, lam, hAd, hW, hMP, hMQ⟩ := hD x
  have hgerm : X.base.presheaf.germ ⊤ x trivial
      ((legendreLambda X L b hD h2).1 * ((legendreLambda X L b hD h2).1 - 1)) =
    X.base.presheaf.germ V.1 x hxV (Scheme.resLE (le_top : V.1 ≤ ⊤)
      ((legendreLambda X L b hD h2).1 * ((legendreLambda X L b hD h2).1 - 1))) := by
    rw [show Scheme.resLE (le_top : V.1 ≤ ⊤) _ =
      (X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom
        ((legendreLambda X L b hD h2).1 *
          ((legendreLambda X L b hD h2).1 - 1)) from rfl]
    exact (X.base.presheaf.germ_res_apply (homOfLE le_top) x hxV _).symm
  rw [hgerm]
  refine IsUnit.map _ ?_
  have hres : Scheme.resLE (le_top : V.1 ≤ ⊤)
      ((legendreLambda X L b hD h2).1 * ((legendreLambda X L b hD h2).1 - 1)) =
      lam * (lam - 1) := by
    have hspec := (legendreLambda X L b hD h2).2 V Pr lam hAd hW hMP
    rw [map_mul, map_sub, map_one, hspec]
  rw [hres]
  have hell : (legendreCurve lam).IsElliptic := by
    rw [← hW]
    exact Pr.elliptic
  rw [← legendreCurve_isElliptic_iff (isUnit_ofNat_res h2 V.1) lam]
  exact hell

end TwoTorsion

end ModularCurves
