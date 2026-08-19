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

open LocalPresentation MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-3 ★)** The classifying ring map of a Legendre datum:
`R[λ][(λ(λ−1))⁻¹] → Γ(X.base, ⊤)`, `λ ↦ legendreLambda` — the algebra of KM 4.6.2's
classifying morphism to `M'₂` (mirrors `classifyingRingHom`). -/
noncomputable def legendreClassifyingRingHom {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 2) (b : OmegaBasis X.curve.toEllipticCurveGeom)
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    LegendreModuliRing R →+* Γ(X.base, ⊤) := by
  refine IsLocalization.Away.lift (legendrePoly R)
    (g := eval₂Hom X.baseRingHom ![(legendreLambda X L b hD h2).1]) ?_
  rw [show (eval₂Hom X.baseRingHom ![(legendreLambda X L b hD h2).1])
      (legendrePoly R) =
    (legendreLambda X L b hD h2).1 * ((legendreLambda X L b hD h2).1 - 1) from by
    rw [show legendrePoly R = MvPolynomial.X 0 * (MvPolynomial.X 0 - 1) from rfl]
    simp only [map_mul, map_sub, map_one, eval₂Hom_X']
    rfl]
  exact legendreLambda_isUnit X L b hD h2

open AlgebraicGeometry CategoryTheory Scheme in
/-- **(T-E14-CLS-3 ★)** The classifying morphism of a Legendre datum:
`X.base ⟶ M'₂ = Spec R[λ][(λ(λ−1))⁻¹]` (mirrors `classifyingMap`). -/
noncomputable def legendreClassifyingMap {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 2) (b : OmegaBasis X.curve.toEllipticCurveGeom)
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    X.base ⟶ Spec (CommRingCat.of (LegendreModuliRing R)) :=
  X.base.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (legendreClassifyingRingHom X L b hD h2))

open AlgebraicGeometry CategoryTheory Scheme MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-3)** The classifying algebra restricts to the structure algebra
(mirrors `classifyingRingHom_algebraMap`). -/
theorem legendreClassifyingRingHom_algebraMap {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 2) (b : OmegaBasis X.curve.toEllipticCurveGeom)
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤))) (r : R) :
    legendreClassifyingRingHom X L b hD h2 (algebraMap R (LegendreModuliRing R) r) =
      X.baseRingHom r := by
  have h1 : (algebraMap R (LegendreModuliRing R) r) =
      algebraMap (MvPolynomial (Fin 1) R) (LegendreModuliRing R) (C r) := by
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 1) R)
      (LegendreModuliRing R)]
    rfl
  rw [h1, legendreClassifyingRingHom, IsLocalization.Away.lift_eq]
  simp

open LocalPresentation MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-4 ★)** The per-witness coefficient match: specializing the universal
Legendre curve along the classifying map, restricted to a witness affine, recovers
exactly the witness chart curve (mirrors `universalShortNF_map_classifying`; the
coefficient input is `legendreLambda`'s universal spec). -/
theorem universalLegendre_map_classifying {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 2) (b : OmegaBasis X.curve.toEllipticCurveGeom)
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (V : X.base.affineOpens)
    (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
    (lam : Γ(X.base, V.1)) (hAd : Pr.IsAdapted b)
    (hW : Pr.W = legendreCurve lam) (hMP : Pr.MarksAt L.1.1.2 0 0) :
    (universalLegendre R).map
      (((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2)) = Pr.W := by
  have hlift : legendreClassifyingRingHom X L b hD h2 (universalLambda R) =
      (legendreLambda X L b hD h2).1 := by
    rw [legendreClassifyingRingHom, universalLambda, IsLocalization.Away.lift_eq]
    simp [eval₂Hom_X']
  have hspec := (legendreLambda X L b hD h2).2 V Pr lam hAd hW hMP
  rw [show (universalLegendre R) = legendreCurve (universalLambda R) from rfl,
    legendreCurve_map, hW]
  refine congrArg legendreCurve ?_
  show ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom)
    (legendreClassifyingRingHom X L b hD h2 (universalLambda R)) = lam
  rw [hlift]
  exact hspec

/-- **(T-E14-CLS-5)** A bundled Legendre witness: an affine with an adapted, marked,
Legendre-charted presentation. The index type of the classifying cover. -/
structure LegendreWitness {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 2) (b : OmegaBasis X.curve.toEllipticCurveGeom) where
  /-- The supporting affine. -/
  V : X.base.affineOpens
  /-- The witness presentation. -/
  Pr : LocalPresentation X.curve.toEllipticCurveGeom V
  /-- The witness Legendre parameter. -/
  lam : Γ(X.base, V.1)
  /-- Adaptedness to the `ω`-basis. -/
  hAd : Pr.IsAdapted b
  /-- The chart curve is Legendre. -/
  hW : Pr.W = legendreCurve lam
  /-- The `P`-marking at `x = 0`. -/
  hMP : Pr.MarksAt L.1.1.2 0 0
  /-- The `Q`-marking at `x = 1`. -/
  hMQ : Pr.MarksAt L.1.2.2 1 0

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-5, ≈E2)** The per-witness piece of the classifying `EllHom`
(mirrors `chartPiece`). -/
noncomputable def legendrePiece {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (w : LegendreWitness X L b) :
    (pullback X.curve.toEllipticCurveGeom.π w.V.1.ι : Scheme.{u}) ⟶
      projModel (universalLegendre R) :=
  w.Pr.e.hom ≫
    eqToHom (congrArg projModel
      (universalLegendre_map_classifying X L b hD h2 w.V w.Pr w.lam
        w.hAd w.hW w.hMP).symm) ≫
    projModelBaseChange
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2)) (universalLegendre R)

section OpaqueProjModelLegendre

/- `projModel` is a `Proj`-of-graded-ring construction; `whnf` chases it inside the
`eqToHom (congrArg projModel _)` transports of `legendrePiece_restrict` without bound (1.6M
heartbeats did not close it on this pin). Opacity is the fix, so the heartbeat raise is
gone; scoped because the `projModel*` API elsewhere in the file needs transparency. -/
set_option allowUnsafeReducibility true in
attribute [local irreducible] ModularCurves.projModel

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-5, ≈E3b)** The piece maps are compatible with restriction: restrict
a witness (adaptedness, Legendre form and markings all restrict) and the piece
restricts (mirrors `chartPiece_restrict`; uniqueness = `legendre_witness_transVC_eq_one`). -/
theorem legendrePiece_restrict {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (w w' : LegendreWitness X L b) (h : w'.V.1 ≤ w.V.1) :
    restrictTheta h ≫ legendrePiece hD h2 w = legendrePiece hD h2 w' := by
  -- the restricted witness equals the smaller witness, as charts
  have hres := w.hMP.restrict h
  rw [map_zero] at hres
  have hVC : w'.Pr.transVC (w.Pr.restrict h) = 1 :=
    (legendre_witness_transVC_eq_one w'.hAd (w.hAd.restrict h) w'.hW
      (restrict_W_legendre w.hW h) w'.hMP hres (isUnit_ofNat_res h2 w'.V.1)).1
  have hWeq : (w.Pr.restrict h).W = w'.Pr.W := by
    have := w'.Pr.transVC_smul (w.Pr.restrict h)
    rwa [hVC, one_smul] at this
  have hIso := pointedIso_hom_of_transVC_eq_one hVC
  have hE : (w.Pr.restrict h).e.hom =
      w'.Pr.e.hom ≫ eqToHom (congrArg projModel hWeq.symm) := by
    have h1 : w'.Pr.e.inv ≫ (w.Pr.restrict h).e.hom =
        eqToHom (congrArg projModel hWeq.symm) := by
      have h0 := hIso
      rw [show (w'.Pr.pointedIso (w.Pr.restrict h)).hom =
        w'.Pr.e.inv ≫ (w.Pr.restrict h).e.hom from rfl] at h0
      exact h0
    rw [← h1, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hσ : ((X.base.presheaf.map (homOfLE (le_top : w'.V.1 ≤ ⊤)).op).hom).comp
      (legendreClassifyingRingHom X L b hD h2) =
    (sectionsMapLE (𝟙 X.base) h).comp
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2)) := by
    rw [sectionsMapLE_id]
    show ((X.base.presheaf.map (homOfLE (le_top : w'.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2) =
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
        (X.base.presheaf.map (homOfLE (show w'.V.1 ≤ w.V.1 by
          simpa using h)).op)).hom).comp
        (legendreClassifyingRingHom X L b hD h2)
    rw [← Functor.map_comp, ← op_comp]
    rfl
  rw [legendrePiece, legendrePiece, ← Category.assoc, ← restrict_e_baseChange, hE]
  simp only [Category.assoc]
  rw [cancel_epi (w'.Pr.e.hom)]
  rw [projModelBaseChange_congr'' (sectionsMapLE (𝟙 X.base) h)
      (universalLegendre_map_classifying X L b hD h2 w.V w.Pr w.lam
        w.hAd w.hW w.hMP).symm]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]
  rw [← projModelBaseChange_comp',
    projModelBaseChange_congr_hom hσ.symm (universalLegendre R),
    ← Category.assoc, eqToHom_trans]

end OpaqueProjModelLegendre

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-5)** Witnesses restrict to smaller affines (all four conditions
restrict). -/
noncomputable def LegendreWitness.restrict {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (w : LegendreWitness X L b) {W : X.base.affineOpens} (h : W.1 ≤ w.V.1) :
    LegendreWitness X L b where
  V := W
  Pr := w.Pr.restrict h
  lam := Scheme.resLE h w.lam
  hAd := w.hAd.restrict h
  hW := restrict_W_legendre w.hW h
  hMP := by
    have hres := w.hMP.restrict h
    rwa [map_zero] at hres
  hMQ := by
    have hres := w.hMQ.restrict h
    rwa [map_one, map_zero] at hres

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
/-- **(T-E14-CLS-5, ≈E3d)** The witness cover of the total space. -/
noncomputable def legendreWitnessCover {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) :
    X.curve.toEllipticCurveGeom.E.OpenCover :=
  Scheme.Cover.mkOfCovers
    (LegendreWitness X L b)
    (fun w => pullback X.curve.toEllipticCurveGeom.π w.V.1.ι)
    (fun w => pullback.fst X.curve.toEllipticCurveGeom.π w.V.1.ι)
    (fun x => by
      obtain ⟨V, hxV, Pr, lam, hAd, hW, hMP, hMQ⟩ := hD
        (X.curve.toEllipticCurveGeom.π.base x)
      have hx : x ∈ Set.range (pullback.fst X.curve.toEllipticCurveGeom.π
          V.1.ι).base := by
        rw [Scheme.Pullback.range_fst, Set.mem_preimage, Scheme.Opens.range_ι,
          SetLike.mem_coe]
        exact hxV
      obtain ⟨y, hy⟩ := hx
      exact ⟨⟨V, Pr, lam, hAd, hW, hMP, hMQ⟩, y, hy⟩)

open CategoryTheory Limits in
@[simp] theorem legendreWitnessCover_f {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (w : LegendreWitness X L b) :
    (legendreWitnessCover hD).f w =
      pullback.fst X.curve.toEllipticCurveGeom.π w.V.1.ι := rfl

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-5, ≈E3c)** The piece map is witness-independent at a fixed affine
(uniqueness of marked adapted Legendre witnesses). -/
theorem legendrePiece_congr {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (w₁ w₂ : LegendreWitness X L b) (hV : w₁.V = w₂.V) :
    legendrePiece hD h2 w₁ =
      eqToHom (by rw [hV]) ≫ legendrePiece hD h2 w₂ := by
  obtain ⟨V₁, Pr₁, lam₁, hAd₁, hW₁, hMP₁, hMQ₁⟩ := w₁
  obtain ⟨V₂, Pr₂, lam₂, hAd₂, hW₂, hMP₂, hMQ₂⟩ := w₂
  obtain rfl : V₁ = V₂ := hV
  rw [eqToHom_refl, Category.id_comp]
  have hVC : Pr₂.transVC Pr₁ = 1 :=
    (legendre_witness_transVC_eq_one hAd₂ hAd₁ hW₂ hW₁ hMP₂ hMP₁
      (isUnit_ofNat_res h2 V₁.1)).1
  have hWeq : Pr₁.W = Pr₂.W := by
    have := Pr₂.transVC_smul Pr₁
    rwa [hVC, one_smul] at this
  have hIso := pointedIso_hom_of_transVC_eq_one hVC
  have hE : Pr₁.e.hom = Pr₂.e.hom ≫ eqToHom (congrArg projModel hWeq.symm) := by
    have h1 : Pr₂.e.inv ≫ Pr₁.e.hom = eqToHom (congrArg projModel hWeq.symm) := by
      have h0 := hIso
      rw [show (Pr₂.pointedIso Pr₁).hom = Pr₂.e.inv ≫ Pr₁.e.hom from rfl] at h0
      exact h0
    rw [← h1, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  show Pr₁.e.hom ≫ _ ≫ _ = Pr₂.e.hom ≫ _ ≫ _
  rw [hE]
  simp only [Category.assoc, eqToHom_trans_assoc]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
private theorem legendrePiece_agree {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (p q : LegendreWitness X L b) :
    pullback.fst ((legendreWitnessCover hD).f p) ((legendreWitnessCover hD).f q) ≫
        legendrePiece hD h2 p =
      pullback.snd ((legendreWitnessCover hD).f p) ((legendreWitnessCover hD).f q) ≫
        legendrePiece hD h2 q := by
  haveI hOIp : IsOpenImmersion ((legendreWitnessCover hD).f p) := by
    rw [legendreWitnessCover_f]; infer_instance
  haveI hOIq : IsOpenImmersion ((legendreWitnessCover hD).f q) := by
    rw [legendreWitnessCover_f]; infer_instance
  have hchoice : ∀ z : (pullback ((legendreWitnessCover hD).f p)
      ((legendreWitnessCover hD).f q) : Scheme.{u}),
      ∃ (W : X.base.affineOpens), W.1 ≤ p.V.1 ⊓ q.V.1 ∧
        X.curve.toEllipticCurveGeom.π.base
          ((pullback.fst ((legendreWitnessCover hD).f p)
            ((legendreWitnessCover hD).f q) ≫
            (legendreWitnessCover hD).f p).base z) ∈ W.1 := by
    intro z
    have hsp : X.curve.toEllipticCurveGeom.π.base
        ((pullback.fst ((legendreWitnessCover hD).f p)
          ((legendreWitnessCover hD).f q) ≫
          (legendreWitnessCover hD).f p).base z) ∈ p.V.1 := by
      have hr : ((pullback.fst ((legendreWitnessCover hD).f p)
          ((legendreWitnessCover hD).f q) ≫ (legendreWitnessCover hD).f p).base z) ∈
          Set.range (pullback.fst X.curve.toEllipticCurveGeom.π p.V.1.ι).base :=
        ⟨(pullback.fst ((legendreWitnessCover hD).f p)
          ((legendreWitnessCover hD).f q)).base z, rfl⟩
      rw [Scheme.Pullback.range_fst] at hr
      simpa [Scheme.Opens.range_ι] using hr
    have hcond : (pullback.fst ((legendreWitnessCover hD).f p)
        ((legendreWitnessCover hD).f q) ≫ (legendreWitnessCover hD).f p).base z =
      (pullback.snd ((legendreWitnessCover hD).f p)
        ((legendreWitnessCover hD).f q) ≫ (legendreWitnessCover hD).f q).base z := by
      have := congrArg (fun t => t.base z) (pullback.condition
        (f := (legendreWitnessCover hD).f p) (g := (legendreWitnessCover hD).f q))
      simpa using this
    have hsq : X.curve.toEllipticCurveGeom.π.base
        ((pullback.fst ((legendreWitnessCover hD).f p)
          ((legendreWitnessCover hD).f q) ≫
          (legendreWitnessCover hD).f p).base z) ∈ q.V.1 := by
      have hr : ((pullback.fst ((legendreWitnessCover hD).f p)
          ((legendreWitnessCover hD).f q) ≫ (legendreWitnessCover hD).f p).base z) ∈
          Set.range (pullback.fst X.curve.toEllipticCurveGeom.π q.V.1.ι).base := by
        rw [hcond]
        exact ⟨(pullback.snd ((legendreWitnessCover hD).f p)
          ((legendreWitnessCover hD).f q)).base z, rfl⟩
      rw [Scheme.Pullback.range_fst] at hr
      simpa [Scheme.Opens.range_ι] using hr
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset
      (show X.curve.toEllipticCurveGeom.π.base
        ((pullback.fst ((legendreWitnessCover hD).f p)
          ((legendreWitnessCover hD).f q) ≫
          (legendreWitnessCover hD).f p).base z) ∈ p.V.1 ⊓ q.V.1 from ⟨hsp, hsq⟩)
    exact ⟨⟨W₀, hWaff⟩, hWle, hxW⟩
  choose W hWle hmem using hchoice
  have hfsteq : ∀ z, (restrictTheta (G := X.curve.toEllipticCurveGeom)
      ((hWle z).trans inf_le_left) ≫ (legendreWitnessCover hD).f p) =
    restrictTheta ((hWle z).trans inf_le_right) ≫ (legendreWitnessCover hD).f q := by
    intro z
    rw [legendreWitnessCover_f, legendreWitnessCover_f, restrictTheta_fst,
      restrictTheta_fst]
  let hω : ∀ z, (pullback X.curve.toEllipticCurveGeom.π (W z).1.ι : Scheme.{u}) ⟶
      pullback ((legendreWitnessCover hD).f p) ((legendreWitnessCover hD).f q) :=
    fun z => pullback.lift (restrictTheta ((hWle z).trans inf_le_left))
      (restrictTheta ((hWle z).trans inf_le_right)) (hfsteq z)
  have hcomp : ∀ z, hω z ≫ pullback.fst ((legendreWitnessCover hD).f p)
      ((legendreWitnessCover hD).f q) ≫ (legendreWitnessCover hD).f p =
    pullback.fst X.curve.toEllipticCurveGeom.π (W z).1.ι := by
    intro z
    rw [← Category.assoc, show hω z ≫ pullback.fst ((legendreWitnessCover hD).f p)
        ((legendreWitnessCover hD).f q) =
      restrictTheta ((hWle z).trans inf_le_left) from pullback.lift_fst _ _ _,
      legendreWitnessCover_f, restrictTheta_fst]
  have hmapOI : ∀ z, IsOpenImmersion (hω z) := by
    intro z
    haveI : IsOpenImmersion (pullback.fst ((legendreWitnessCover hD).f p)
        ((legendreWitnessCover hD).f q) ≫ (legendreWitnessCover hD).f p) :=
      inferInstance
    haveI : IsOpenImmersion (hω z ≫ pullback.fst ((legendreWitnessCover hD).f p)
        ((legendreWitnessCover hD).f q) ≫ (legendreWitnessCover hD).f p) := by
      rw [hcomp z]; infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.fst ((legendreWitnessCover hD).f p)
      ((legendreWitnessCover hD).f q) ≫ (legendreWitnessCover hD).f p)
  refine (Scheme.Cover.mkOfCovers
    (X := (pullback ((legendreWitnessCover hD).f p)
      ((legendreWitnessCover hD).f q) : Scheme.{u}))
    (pullback ((legendreWitnessCover hD).f p) ((legendreWitnessCover hD).f q) :
      Scheme.{u})
    (fun z => pullback X.curve.toEllipticCurveGeom.π (W z).1.ι)
    (fun z => hω z) ?_ (fun z => hmapOI z)).hom_ext _ _ (fun z => ?_)
  · intro z
    have hz : (pullback.fst ((legendreWitnessCover hD).f p)
        ((legendreWitnessCover hD).f q) ≫ (legendreWitnessCover hD).f p).base z ∈
      Set.range (pullback.fst X.curve.toEllipticCurveGeom.π (W z).1.ι).base := by
      rw [Scheme.Pullback.range_fst]
      simpa [Scheme.Opens.range_ι] using hmem z
    obtain ⟨w, hw⟩ := hz
    refine ⟨z, w, ?_⟩
    have hinj : Function.Injective
        ((pullback.fst ((legendreWitnessCover hD).f p)
          ((legendreWitnessCover hD).f q) ≫ (legendreWitnessCover hD).f p).base) :=
      (pullback.fst ((legendreWitnessCover hD).f p)
        ((legendreWitnessCover hD).f q) ≫
        (legendreWitnessCover hD).f p).isOpenEmbedding.injective
    apply hinj
    calc (pullback.fst ((legendreWitnessCover hD).f p)
          ((legendreWitnessCover hD).f q) ≫
          (legendreWitnessCover hD).f p).base ((hω z).base w)
        = (hω z ≫ pullback.fst ((legendreWitnessCover hD).f p)
            ((legendreWitnessCover hD).f q) ≫
            (legendreWitnessCover hD).f p).base w := rfl
      _ = (pullback.fst X.curve.toEllipticCurveGeom.π (W z).1.ι).base w := by
          rw [hcomp z]
      _ = _ := hw
  · show hω z ≫ pullback.fst _ _ ≫ legendrePiece hD h2 p =
      hω z ≫ pullback.snd _ _ ≫ legendrePiece hD h2 q
    rw [← Category.assoc, show hω z ≫ pullback.fst ((legendreWitnessCover hD).f p)
        ((legendreWitnessCover hD).f q) =
      restrictTheta ((hWle z).trans inf_le_left) from pullback.lift_fst _ _ _,
      ← Category.assoc, show hω z ≫ pullback.snd ((legendreWitnessCover hD).f p)
        ((legendreWitnessCover hD).f q) =
      restrictTheta ((hWle z).trans inf_le_right) from pullback.lift_snd _ _ _,
      legendrePiece_restrict hD h2 p (p.restrict ((hWle z).trans inf_le_left))
        ((hWle z).trans inf_le_left),
      legendrePiece_restrict hD h2 q (q.restrict ((hWle z).trans inf_le_right))
        ((hWle z).trans inf_le_right)]
    rw [legendrePiece_congr hD h2 (p.restrict ((hWle z).trans inf_le_left))
      (q.restrict ((hWle z).trans inf_le_right)) rfl, eqToHom_refl,
      Category.id_comp]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
/-- **(T-E14-CLS-5 ★★, ≈E4)** The classifying morphism upstairs: the witness-glued
map from the total space to the universal Legendre model (mirrors `classifyingTop`). -/
noncomputable def legendreTop {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    X.curve.toEllipticCurveGeom.E ⟶ projModel (universalLegendre R) :=
  (legendreWitnessCover hD).glueMorphisms
    (fun w => legendrePiece hD h2 w)
    (legendrePiece_agree hD h2)

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
@[reassoc]
theorem legendreTop_piece {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (w : LegendreWitness X L b) :
    (legendreWitnessCover hD).f w ≫ legendreTop hD h2 =
      legendrePiece hD h2 w :=
  (legendreWitnessCover hD).ι_glueMorphisms _ _ w

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-6, ≈E2-π)** The piece map lies over the restricted classifying map
(mirrors `chartPiece_π`). -/
theorem legendrePiece_π {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (w : LegendreWitness X L b) :
    legendrePiece hD h2 w ≫ projModelπ (universalLegendre R) =
      pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι ≫ w.V.2.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom
          (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
            (legendreClassifyingRingHom X L b hD h2))) := by
  have hw : projModelBaseChange
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2)) (universalLegendre R) ≫
      projModelπ (universalLegendre R) =
    projModelπ ((universalLegendre R).map
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2))) ≫
      Spec.map (CommRingCat.ofHom
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (legendreClassifyingRingHom X L b hD h2))) := by
    letI : Algebra (LegendreModuliRing R) Γ(X.base, w.V.1) :=
      ((((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2))).toAlgebra
    exact (isPullback_projModelBaseChange (universalLegendre R)).w
  rw [legendrePiece, Category.assoc, Category.assoc, hw,
    reassoc_of% projModelπ_congr
      (universalLegendre_map_classifying X L b hD h2 w.V w.Pr w.lam
        w.hAd w.hW w.hMP).symm]
  rw [← Category.assoc, w.Pr.compat_π, Category.assoc]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-6, ≈E4-π ★)** The glued comparison lies over the classifying map
(mirrors `classifyingTop_π_w`). -/
theorem legendreTop_π_w {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    legendreTop hD h2 ≫ projModelπ (universalLegendre R) =
      X.curve.toEllipticCurveGeom.π ≫ legendreClassifyingMap X L b hD h2 := by
  refine (legendreWitnessCover hD).hom_ext _ _ (fun w => ?_)
  rw [← Category.assoc, legendreTop_piece, legendrePiece_π]
  have hsplit : Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2))) =
    Spec.map (X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (legendreClassifyingRingHom X L b hD h2)) := by
    rw [← Spec.map_comp]
    rfl
  rw [hsplit,
    show w.V.2.isoSpec.hom = w.V.1.toSpecΓ from IsAffineOpen.isoSpec_hom _]
  rw [show w.V.1.toSpecΓ ≫
      Spec.map (X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (legendreClassifyingRingHom X L b hD h2)) =
    (w.V.1.ι ≫ X.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (legendreClassifyingRingHom X L b hD h2)) from by
    rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]]
  rw [show (w.V.1.ι ≫ X.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (legendreClassifyingRingHom X L b hD h2)) =
    w.V.1.ι ≫ legendreClassifyingMap X L b hD h2 from by
    rw [Category.assoc]; rfl]
  rw [← Category.assoc, ← pullback.condition, Category.assoc, legendreWitnessCover_f]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
/-- **(T-E14-CLS-6, ≈E4)** The witness cover of the base. -/
noncomputable def legendreBaseCover {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) : X.base.OpenCover :=
  Scheme.Cover.mkOfCovers
    (LegendreWitness X L b)
    (fun w => w.V.1.toScheme)
    (fun w => w.V.1.ι)
    (fun x => by
      obtain ⟨V, hxV, Pr, lam, hAd, hW, hMP, hMQ⟩ := hD x
      exact ⟨⟨V, Pr, lam, hAd, hW, hMP, hMQ⟩, ⟨x, hxV⟩, rfl⟩)

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(T-E14-CLS-6 ★, ≈E4-zero)** The glued comparison respects the zero sections
(mirrors `classifyingTop_zero`). -/
theorem legendreTop_zero {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    X.curve.toEllipticCurveGeom.zero ≫ legendreTop hD h2 =
      legendreClassifyingMap X L b hD h2 ≫ projModelZero (universalLegendre R) := by
  refine (legendreBaseCover hD).hom_ext _ _ (fun w => ?_)
  have hzfac : w.V.1.ι ≫ X.curve.toEllipticCurveGeom.zero =
      pullback.lift (w.V.1.ι ≫ X.curve.toEllipticCurveGeom.zero) (𝟙 _)
        (by rw [Category.assoc, X.curve.toEllipticCurveGeom.zero_π,
          Category.comp_id, Category.id_comp]) ≫
      (legendreWitnessCover hD).f w := by
    rw [legendreWitnessCover_f, pullback.lift_fst]
  rw [show (legendreBaseCover hD).f w = w.V.1.ι from rfl, ← Category.assoc, hzfac,
    Category.assoc, legendreTop_piece]
  have hz := w.Pr.compat_zero
  have hlift : pullback.lift (w.V.1.ι ≫ X.curve.toEllipticCurveGeom.zero) (𝟙 _)
      (by rw [Category.assoc, X.curve.toEllipticCurveGeom.zero_π,
        Category.comp_id, Category.id_comp]) ≫ w.Pr.e.hom =
    w.V.2.isoSpec.hom ≫ projModelZero w.Pr.W := by
    rw [← Iso.inv_comp_eq, ← Category.assoc]
    exact hz
  rw [legendrePiece, ← Category.assoc, hlift]
  rw [Category.assoc,
    show projModelZero w.Pr.W = projModelZero ((universalLegendre R).map
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (legendreClassifyingRingHom X L b hD h2))) ≫
      eqToHom (congrArg projModel
        (universalLegendre_map_classifying X L b hD h2 w.V w.Pr w.lam
          w.hAd w.hW w.hMP)) from
      projModelZero_congr
        (universalLegendre_map_classifying X L b hD h2 w.V w.Pr w.lam
          w.hAd w.hW w.hMP).symm]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hbc : projModelZero ((universalLegendre R).map
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2))) ≫
      projModelBaseChange
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (legendreClassifyingRingHom X L b hD h2)) (universalLegendre R) =
    Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2))) ≫
      projModelZero (universalLegendre R) := by
    letI : Algebra (LegendreModuliRing R) Γ(X.base, w.V.1) :=
      ((((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2))).toAlgebra
    exact projModelZero_baseChange (universalLegendre R)
  rw [hbc]
  have hsplit : Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2))) =
    Spec.map (X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (legendreClassifyingRingHom X L b hD h2)) := by
    rw [← Spec.map_comp]
    rfl
  rw [← Category.assoc, hsplit,
    show w.V.2.isoSpec.hom = w.V.1.toSpecΓ from IsAffineOpen.isoSpec_hom _]
  rw [show w.V.1.toSpecΓ ≫
      Spec.map (X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (legendreClassifyingRingHom X L b hD h2)) =
    (w.V.1.ι ≫ X.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (legendreClassifyingRingHom X L b hD h2)) from by
    rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]]
  rw [show (w.V.1.ι ≫ X.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (legendreClassifyingRingHom X L b hD h2)) =
    w.V.1.ι ≫ legendreClassifyingMap X L b hD h2 from by rw [Category.assoc]; rfl]
  simp only [Category.assoc]

open AlgebraicGeometry CategoryTheory Scheme in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-6, ≈E4)** The classifying map lies over `Spec R` (mirrors
`classifyingMap_structMap`). -/
theorem legendreClassifyingMap_structMap {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (hR : IsUnit (2 : R)) :
    legendreClassifyingMap X L b hD h2 ≫ (universalLegendreObj R hR).structMap =
      X.structMap := by
  show (X.base.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (legendreClassifyingRingHom X L b hD h2))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (LegendreModuliRing R))) = X.structMap
  rw [Category.assoc, ← Spec.map_comp,
    show CommRingCat.ofHom (algebraMap R (LegendreModuliRing R)) ≫
        CommRingCat.ofHom (legendreClassifyingRingHom X L b hD h2) =
      CommRingCat.ofHom (X.baseRingHom) from by
      ext r
      exact legendreClassifyingRingHom_algebraMap X L b hD h2 r,
    show CommRingCat.ofHom X.baseRingHom =
      (Scheme.ΓSpecIso R).inv ≫ X.structMap.appTop from rfl,
    Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom R,
    ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  exact Category.comp_id _

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-6)** The classifying map restricted to a witness affine (mirrors
`restrict_classifyingMap`). -/
theorem restrict_legendreClassifyingMap {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (V : X.base.affineOpens) :
    V.1.ι ≫ legendreClassifyingMap X L b hD h2 =
      V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
          (legendreClassifyingRingHom X L b hD h2))) := by
  have hsplit : Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2))) =
    Spec.map (X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (legendreClassifyingRingHom X L b hD h2)) := by
    rw [← Spec.map_comp]
    rfl
  rw [hsplit, show V.2.isoSpec.hom = V.1.toSpecΓ from IsAffineOpen.isoSpec_hom _,
    ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top, Category.assoc]
  rfl

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-6, ≈E4)** The per-witness classifying square is cartesian (mirrors
`chartPiece_isPullback`). -/
theorem legendrePiece_isPullback {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (w : LegendreWitness X L b) :
    IsPullback (legendrePiece hD h2 w)
      (pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι)
      (projModelπ (universalLegendre R))
      (w.V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (legendreClassifyingRingHom X L b hD h2)))) := by
  have hleft : IsPullback
      (w.Pr.e.hom ≫ eqToHom (congrArg projModel
        (universalLegendre_map_classifying X L b hD h2 w.V w.Pr w.lam
          w.hAd w.hW w.hMP).symm))
      (pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι)
      (projModelπ ((universalLegendre R).map
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (legendreClassifyingRingHom X L b hD h2))))
      w.V.2.isoSpec.hom := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.assoc, projModelπ_congr
      (universalLegendre_map_classifying X L b hD h2 w.V w.Pr w.lam
        w.hAd w.hW w.hMP).symm]
    exact w.Pr.compat_π
  have hright : IsPullback
      (projModelBaseChange
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (legendreClassifyingRingHom X L b hD h2)) (universalLegendre R))
      (projModelπ ((universalLegendre R).map
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (legendreClassifyingRingHom X L b hD h2))))
      (projModelπ (universalLegendre R))
      (Spec.map (CommRingCat.ofHom
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (legendreClassifyingRingHom X L b hD h2)))) := by
    letI : Algebra (LegendreModuliRing R) Γ(X.base, w.V.1) :=
      ((((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2))).toAlgebra
    exact isPullback_projModelBaseChange (universalLegendre R)
  have hpaste := hleft.paste_horiz hright
  rw [show (w.Pr.e.hom ≫ eqToHom (congrArg projModel
      (universalLegendre_map_classifying X L b hD h2 w.V w.Pr w.lam
        w.hAd w.hW w.hMP).symm)) ≫
    projModelBaseChange
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2)) (universalLegendre R) =
    legendrePiece hD h2 w from by
    rw [legendrePiece, Category.assoc]] at hpaste
  exact hpaste

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-6 ★★, ≈E4)** The classifying square is cartesian: `X` is the
pullback of the universal Legendre curve along the classifying map (mirrors
`isPullback_classifyingTop`). -/
theorem isPullback_legendreTop {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    IsPullback (legendreTop hD h2) X.curve.toEllipticCurveGeom.π
      (projModelπ (universalLegendre R)) (legendreClassifyingMap X L b hD h2) := by
  refine (isPullback_of_iSup_eq_top (f := X.curve.toEllipticCurveGeom.π)
    (g := legendreTop hD h2) (h := legendreClassifyingMap X L b hD h2)
    (k := projModelπ (universalLegendre R))
    (legendreTop_π_w hD h2).symm
    (ι := LegendreWitness X L b)
    (fun w => w.V.1) ?_ (fun w => ?_)).flip
  · rw [eq_top_iff]
    intro x _
    obtain ⟨V, hxV, Pr, lam, hAd, hW, hMP, hMQ⟩ := hD x
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨V, Pr, lam, hAd, hW, hMP, hMQ⟩, hxV⟩
  · set fpre := (X.curve.toEllipticCurveGeom.π ⁻¹ᵁ w.V.1).ι with hfpre
    have hcomm : fpre ≫ X.curve.toEllipticCurveGeom.π =
        (X.curve.toEllipticCurveGeom.π ∣_ w.V.1) ≫ w.V.1.ι :=
      (morphismRestrict_ι X.curve.toEllipticCurveGeom.π w.V.1).symm
    set m := pullback.lift fpre (X.curve.toEllipticCurveGeom.π ∣_ w.V.1) hcomm
      with hm
    have hm₁ : m ≫ pullback.fst X.curve.toEllipticCurveGeom.π w.V.1.ι = fpre :=
      pullback.lift_fst _ _ _
    have hm₂ : m ≫ pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι =
        X.curve.toEllipticCurveGeom.π ∣_ w.V.1 :=
      pullback.lift_snd _ _ _
    have hmiso : IsIso m := by
      refine (isPullback_morphismRestrict X.curve.toEllipticCurveGeom.π
        w.V.1).flip.isIso_of_isPullback
        (IsPullback.of_hasPullback X.curve.toEllipticCurveGeom.π w.V.1.ι) m hm₁ hm₂
    have hmsq : IsPullback m (X.curve.toEllipticCurveGeom.π ∣_ w.V.1)
        (pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [hm₂, Category.comp_id]⟩
    have hp := hmsq.paste_horiz (legendrePiece_isPullback hD h2 w)
    rw [show m ≫ legendrePiece hD h2 w =
        (X.curve.toEllipticCurveGeom.π ⁻¹ᵁ w.V.1).ι ≫ legendreTop hD h2 from by
        rw [← legendreTop_piece hD h2 w, legendreWitnessCover_f, ← Category.assoc,
          hm₁],
      show (𝟙 _) ≫ w.V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
          (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
            (legendreClassifyingRingHom X L b hD h2))) =
        w.V.1.ι ≫ legendreClassifyingMap X L b hD h2 from by
        rw [Category.id_comp, ← restrict_legendreClassifyingMap]] at hp
    exact hp.flip

open AlgebraicGeometry CategoryTheory Scheme in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-6 ★★)** The classifying morphism of a Legendre datum in `Ell/R`:
KM 4.6.2's universal property, forward direction (mirrors `classifyingEllHom`). -/
noncomputable def legendreClassifyingEllHom {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (hR : IsUnit (2 : R)) :
    X ⟶ universalLegendreObj R hR where
  baseHom := legendreClassifyingMap X L b hD h2
  base_w := legendreClassifyingMap_structMap hD h2 hR
  top := legendreTop hD h2
  isPullback := isPullback_legendreTop hD h2
  zero_w := legendreTop_zero hD h2

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-7, rt1-level ★)** The marking downstairs: a marked section composed
with the glued comparison is the classifying map followed by the universal marked
section. Per witness affine: the section factors through the piece, the marking reads
it as `[p:q:1]`, and the base-change naturality of affine sections lands on the
universal marked point. -/
theorem section_comp_legendreTop {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    {σ : X.base ⟶ X.curve.toEllipticCurveGeom.E}
    (hσ : σ ≫ X.curve.toEllipticCurveGeom.π = 𝟙 X.base) (p q : LegendreModuliRing R)
    (hpq : (universalLegendre R).toAffine.Equation p q)
    (hmark : ∀ w : LegendreWitness X L b,
      w.Pr.MarksAt hσ
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
          (legendreClassifyingRingHom X L b hD h2 p))
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
          (legendreClassifyingRingHom X L b hD h2 q))) :
    σ ≫ legendreTop hD h2 =
      legendreClassifyingMap X L b hD h2 ≫
        projModelAffineSection (universalLegendre R) p q hpq := by
  refine (legendreBaseCover hD).hom_ext _ _ (fun w => ?_)
  show w.V.1.ι ≫ σ ≫ legendreTop hD h2 = _
  -- factor the section through the piece
  have hfac : w.V.1.ι ≫ σ =
      sectionLift X.curve.toEllipticCurveGeom hσ w.V ≫
        (legendreWitnessCover hD).f w := by
    rw [legendreWitnessCover_f]
    unfold sectionLift
    rw [pullback.lift_fst]
  rw [← Category.assoc, hfac, Category.assoc, legendreTop_piece]
  -- read the marking through the chart
  obtain ⟨hpq', hMeq⟩ := hmark w
  have hMeq' : sectionLift X.curve.toEllipticCurveGeom hσ w.V ≫ w.Pr.e.hom =
      w.V.2.isoSpec.hom ≫ projModelAffineSection w.Pr.W _ _ hpq' := by
    calc sectionLift X.curve.toEllipticCurveGeom hσ w.V ≫ w.Pr.e.hom
        = w.V.2.isoSpec.hom ≫ (w.V.2.isoSpec.inv ≫
            sectionLift X.curve.toEllipticCurveGeom hσ w.V) ≫ w.Pr.e.hom := by
          rw [← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = _ := by rw [hMeq]
  rw [legendrePiece, ← Category.assoc, hMeq']
  -- transport the affine section through the coefficient match and the base change
  rw [Category.assoc, ← Category.assoc (projModelAffineSection w.Pr.W _ _ hpq'),
    projModelAffineSection_congr
      (universalLegendre_map_classifying X L b hD h2 w.V w.Pr w.lam
        w.hAd w.hW w.hMP).symm]
  letI : Algebra (LegendreModuliRing R) Γ(X.base, w.V.1) :=
    ((((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
      (legendreClassifyingRingHom X L b hD h2))).toAlgebra
  have hbc := projModelAffineSection_baseChange (universalLegendre R) p q hpq
    (WeierstrassCurve.Affine.Equation.map (algebraMap (LegendreModuliRing R)
      Γ(X.base, w.V.1)) hpq)
  rw [show projModelAffineSection ((universalLegendre R).map
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2)))
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (legendreClassifyingRingHom X L b hD h2 p))
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (legendreClassifyingRingHom X L b hD h2 q))
      ((universalLegendre_map_classifying X L b hD h2 w.V w.Pr w.lam
        w.hAd w.hW w.hMP).symm ▸ hpq') ≫
      projModelBaseChange
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (legendreClassifyingRingHom X L b hD h2))
        (universalLegendre R) =
    Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2))) ≫
      projModelAffineSection (universalLegendre R) p q hpq from hbc]
  rw [← Category.assoc, ← restrict_legendreClassifyingMap hD h2 w.V,
    Category.assoc]
  rfl

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-7, rt1-level ★★)** Pulling the universal marked `P` back along the
classifying morphism recovers the given `P`. -/
theorem pullSection_legendreClassifyingEllHom_P {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (hR : IsUnit (2 : R)) :
    EllHom.pullSection R (legendreClassifyingEllHom hD h2 hR)
      (universalLegendreP R hR) = L.1.1 := by
  have hdown : L.1.1.1 ≫ legendreTop hD h2 =
      legendreClassifyingMap X L b hD h2 ≫
        projModelAffineSection (universalLegendre R) 0 0
          (legendreCurve_equation_zero (universalLambda R)) := by
    refine section_comp_legendreTop hD h2 L.1.1.2 0 0
      (legendreCurve_equation_zero (universalLambda R)) (fun w => ?_)
    have hz : ((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (legendreClassifyingRingHom X L b hD h2 (0 : LegendreModuliRing R)) =
      (0 : Γ(X.base, w.V.1)) := by rw [map_zero, map_zero]
    rw [hz]
    exact w.hMP
  refine Subtype.ext ?_
  refine (legendreClassifyingEllHom hD h2 hR).isPullback.hom_ext ?_ ?_
  · rw [show (EllHom.pullSection R (legendreClassifyingEllHom hD h2 hR)
        (universalLegendreP R hR)).1 ≫ (legendreClassifyingEllHom hD h2 hR).top =
      (legendreClassifyingEllHom hD h2 hR).baseHom ≫ (universalLegendreP R hR).1
      from (legendreClassifyingEllHom hD h2 hR).isPullback.lift_fst _ _ _]
    show _ = L.1.1.1 ≫ legendreTop hD h2
    rw [hdown]
    rfl
  · rw [show (EllHom.pullSection R (legendreClassifyingEllHom hD h2 hR)
        (universalLegendreP R hR)).1 ≫ X.curve.π = 𝟙 X.base from
      (EllHom.pullSection R (legendreClassifyingEllHom hD h2 hR)
        (universalLegendreP R hR)).2]
    exact L.1.1.2.symm

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-7, rt1-level ★★)** Pulling the universal marked `Q` back along the
classifying morphism recovers the given `Q`. -/
theorem pullSection_legendreClassifyingEllHom_Q {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (hR : IsUnit (2 : R)) :
    EllHom.pullSection R (legendreClassifyingEllHom hD h2 hR)
      (universalLegendreQ R hR) = L.1.2 := by
  have hdown : L.1.2.1 ≫ legendreTop hD h2 =
      legendreClassifyingMap X L b hD h2 ≫
        projModelAffineSection (universalLegendre R) 1 0
          (legendreCurve_equation_one (universalLambda R)) := by
    refine section_comp_legendreTop hD h2 L.1.2.2 1 0
      (legendreCurve_equation_one (universalLambda R)) (fun w => ?_)
    have ho : ((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (legendreClassifyingRingHom X L b hD h2 (1 : LegendreModuliRing R)) =
      (1 : Γ(X.base, w.V.1)) := by rw [map_one, map_one]
    have hz : ((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (legendreClassifyingRingHom X L b hD h2 (0 : LegendreModuliRing R)) =
      (0 : Γ(X.base, w.V.1)) := by rw [map_zero, map_zero]
    rw [ho, hz]
    exact w.hMQ
  refine Subtype.ext ?_
  refine (legendreClassifyingEllHom hD h2 hR).isPullback.hom_ext ?_ ?_
  · rw [show (EllHom.pullSection R (legendreClassifyingEllHom hD h2 hR)
        (universalLegendreQ R hR)).1 ≫ (legendreClassifyingEllHom hD h2 hR).top =
      (legendreClassifyingEllHom hD h2 hR).baseHom ≫ (universalLegendreQ R hR).1
      from (legendreClassifyingEllHom hD h2 hR).isPullback.lift_fst _ _ _]
    show _ = L.1.2.1 ≫ legendreTop hD h2
    rw [hdown]
    rfl
  · rw [show (EllHom.pullSection R (legendreClassifyingEllHom hD h2 hR)
        (universalLegendreQ R hR)).1 ≫ X.curve.π = 𝟙 X.base from
      (EllHom.pullSection R (legendreClassifyingEllHom hD h2 hR)
        (universalLegendreQ R hR)).2]
    exact L.1.2.2.symm

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-7 rt1)** The section comparison of the classifying map is the
restricted classifying algebra (mirrors `sectionsMapLE_classifyingMap`). -/
theorem sectionsMapLE_legendreClassifyingMap {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (V : X.base.affineOpens) (hTop : V.1 ≤ legendreClassifyingMap X L b hD h2 ⁻¹ᵁ
      (⊤ : (Spec (CommRingCat.of (LegendreModuliRing R))).Opens)) :
    (sectionsMapLE (legendreClassifyingMap X L b hD h2) hTop).comp
      ((Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom) =
    ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (legendreClassifyingRingHom X L b hD h2) := by
  have hL : V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      ((sectionsMapLE (legendreClassifyingMap X L b hD h2) hTop).comp
        ((Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom))) =
    V.1.ι ≫ legendreClassifyingMap X L b hD h2 := by
    rw [show CommRingCat.ofHom
        ((sectionsMapLE (legendreClassifyingMap X L b hD h2) hTop).comp
          ((Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom)) =
      (Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv ≫
        (legendreClassifyingMap X L b hD h2).appLE ⊤ V.1 hTop from rfl,
      Spec.map_comp,
      show V.2.isoSpec.hom = V.1.toSpecΓ from IsAffineOpen.isoSpec_hom _,
      ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc]
    rw [show (⊤ : (Spec (CommRingCat.of (LegendreModuliRing R))).Opens).toSpecΓ ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv =
      (⊤ : (Spec (CommRingCat.of (LegendreModuliRing R))).Opens).ι from by
      rw [Scheme.Opens.toSpecΓ_top, Category.assoc, ← SpecMap_ΓSpecIso_hom,
        ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]]
    rw [Scheme.Hom.resLE_comp_ι]
  have hR : V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2))) =
    V.1.ι ≫ legendreClassifyingMap X L b hD h2 :=
    (restrict_legendreClassifyingMap hD h2 V).symm
  have hSpec := hL.trans hR.symm
  rw [cancel_epi] at hSpec
  have hofHom := Spec.map_injective hSpec
  exact congrArg CommRingCat.Hom.hom hofHom

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(T-E14-CLS-7 rt1-core ★★)** Transporting the tautological chart of the
universal Legendre curve along the classifying morphism recovers the witness: the
geometric sign-pinning (mirrors `transVC_transport_taut`). -/
theorem transVC_transport_legendre {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (hR : IsUnit (2 : R)) (w : LegendreWitness X L b) :
    haveI := universalLegendre_isElliptic R hR
    ((tautPresentation (universalLegendre R)).transport
        (legendreClassifyingEllHom hD h2 hR).baseHom (legendreClassifyingEllHom hD h2 hR).top
        (legendreClassifyingEllHom hD h2 hR).isPullback
        (legendreClassifyingEllHom hD h2 hR).zero_w
        (show w.V.1 ≤ (legendreClassifyingEllHom hD h2 hR).baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial)).transVC
      (w.Pr) = 1 := by
  haveI := universalLegendre_isElliptic R hR
  -- the transported chart curve is the witness's curve
  have hWeq : ((tautPresentation (universalLegendre R)).transport
      (legendreClassifyingEllHom hD h2 hR).baseHom (legendreClassifyingEllHom hD h2 hR).top
      (legendreClassifyingEllHom hD h2 hR).isPullback (legendreClassifyingEllHom hD h2 hR).zero_w
      (show w.V.1 ≤ (legendreClassifyingEllHom hD h2 hR).baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial)).W =
    (w.Pr).W := by
    letI : Algebra (LegendreModuliRing R)
        Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom.toAlgebra
    show ((universalLegendre R).map _).map _ =
      (w.Pr).W
    rw [WeierstrassCurve.map_map,
      show ((sectionsMapLE (legendreClassifyingEllHom hD h2 hR).baseHom
          (show w.V.1 ≤ (legendreClassifyingEllHom hD h2 hR).baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial)).comp
        (algebraMap (LegendreModuliRing R)
          Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤))) =
      ((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X L b hD h2) from
      sectionsMapLE_legendreClassifyingMap hD h2 w.V _]
    exact universalLegendre_map_classifying X L b hD h2 w.V w.Pr w.lam w.hAd w.hW w.hMP
  refine (transVC_unique _ _ 1 (by rw [one_smul, hWeq]) ?_).symm
  rw [projModelVCIso_one, eqToHom_trans]
  show ((tautPresentation (universalLegendre R)).transport
      (legendreClassifyingEllHom hD h2 hR).baseHom (legendreClassifyingEllHom hD h2 hR).top
      (legendreClassifyingEllHom hD h2 hR).isPullback (legendreClassifyingEllHom hD h2 hR).zero_w
      _).e.inv ≫
    (w.Pr).e.hom = eqToHom _
  rw [Iso.inv_comp_eq]
  letI : Algebra Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤) Γ(X.base, w.V.1) :=
    (sectionsMapLE (legendreClassifyingEllHom hD h2 hR).baseHom
      (show w.V.1 ≤ (legendreClassifyingEllHom hD h2 hR).baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial)).toAlgebra
  have hkey : ((tautPresentation (universalLegendre R)).transport
      (legendreClassifyingEllHom hD h2 hR).baseHom (legendreClassifyingEllHom hD h2 hR).top
      (legendreClassifyingEllHom hD h2 hR).isPullback (legendreClassifyingEllHom hD h2 hR).zero_w
      (show w.V.1 ≤ (legendreClassifyingEllHom hD h2 hR).baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial)).e.hom =
    (w.Pr).e.hom ≫
      eqToHom (congrArg projModel hWeq.symm) := by
    letI : Algebra (LegendreModuliRing R)
        Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom.toAlgebra
    haveI : IsIso (⊤ : (Spec (CommRingCat.of (LegendreModuliRing R))).Opens).ι := by
      rw [← Scheme.topIso_hom]
      infer_instance
    haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap (LegendreModuliRing R)
        Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤)))) := by
      have h : CommRingCat.ofHom (algebraMap (LegendreModuliRing R)
          Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤)) =
        (Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv := rfl
      rw [h]
      infer_instance
    refine (isPullback_projModelBaseChange
      (tautPresentation (universalLegendre R)).W).hom_ext ?_ ?_
    · -- the base-change leg, through `classifyingTop_piece`
      rw [show ((tautPresentation (universalLegendre R)).transport
          (legendreClassifyingEllHom hD h2 hR).baseHom (legendreClassifyingEllHom hD h2 hR).top
          (legendreClassifyingEllHom hD h2 hR).isPullback
          (legendreClassifyingEllHom hD h2 hR).zero_w
          (show w.V.1 ≤ (legendreClassifyingEllHom hD h2 hR).baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial)).e.hom ≫
        projModelBaseChange (algebraMap
          Γ(Spec (CommRingCat.of (LegendreModuliRing R)),
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (LegendreModuliRing R))).affineOpens).1) Γ(X.base, w.V.1))
          (tautPresentation (universalLegendre R)).W =
        transportTheta (legendreClassifyingEllHom hD h2 hR).baseHom
          (legendreClassifyingEllHom hD h2 hR).top
          (legendreClassifyingEllHom hD h2 hR).isPullback
          (show w.V.1 ≤ (legendreClassifyingEllHom hD h2 hR).baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial) ≫
          (tautPresentation (universalLegendre R)).e.hom from
        transport_e_baseChange _ _ _ _ _ _]
      rw [show (tautPresentation (universalLegendre R)).e.hom =
        (asIso (pullback.fst (projModelπ (universalLegendre R))
          (⊤ : (Spec (CommRingCat.of (LegendreModuliRing R))).Opens).ι) ≪≫
        (asIso (pullback.fst (projModelπ (universalLegendre R))
          (Spec.map (CommRingCat.ofHom (algebraMap (LegendreModuliRing R)
            Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤)))))).symm ≪≫
        (isPullback_projModelBaseChange (universalLegendre R)).isoPullback.symm).hom
        from rfl]
      simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
      rw [← Category.assoc, ← Category.assoc,
        show (transportTheta (legendreClassifyingEllHom hD h2 hR).baseHom
            (legendreClassifyingEllHom hD h2 hR).top
            (legendreClassifyingEllHom hD h2 hR).isPullback
            (show w.V.1 ≤ (legendreClassifyingEllHom hD h2 hR).baseHom ⁻¹ᵁ
              (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
                (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial) ≫
          pullback.fst (projModelπ (universalLegendre R))
            (⊤ : (Spec (CommRingCat.of (LegendreModuliRing R))).Opens).ι) =
        pullback.fst X.curve.toEllipticCurveGeom.π w.V.1.ι ≫
          (legendreClassifyingEllHom hD h2 hR).top from
        transportTheta_fst _ _ _ _]
      rw [show pullback.fst X.curve.toEllipticCurveGeom.π w.V.1.ι ≫
          (legendreClassifyingEllHom hD h2 hR).top =
        legendrePiece hD h2 w from by
        rw [show (legendreClassifyingEllHom hD h2 hR).top =
          legendreTop hD h2 from rfl,
          ← legendreTop_piece hD h2 w, legendreWitnessCover_f]]
      rw [legendrePiece]
      simp only [Category.assoc]
      rw [cancel_epi
        ((w.Pr).e.hom)]
      -- universal side: the base-change chain collapses
      rw [projModelBaseChange_congr_hom
          ((sectionsMapLE_legendreClassifyingMap hD h2 w.V
            (fun x _ => trivial)).symm)
          (universalLegendre R),
        projModelBaseChange_comp']
      simp only [Category.assoc]
      have htail : projModelBaseChange
            ((Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom)
            (universalLegendre R) ≫
          inv (pullback.fst (projModelπ (universalLegendre R))
            (Spec.map (CommRingCat.ofHom (algebraMap (LegendreModuliRing R)
              Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤))))) ≫
          (isPullback_projModelBaseChange (universalLegendre R)).isoPullback.inv =
        𝟙 _ := by
        have h0 := (isPullback_projModelBaseChange
          (R' := Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤))
          (universalLegendre R)).isoPullback_hom_fst
        rw [← Category.assoc, Iso.comp_inv_eq, Category.id_comp, IsIso.comp_inv_eq]
        exact h0.symm
      rw [htail, Category.comp_id]
      show eqToHom _ ≫ eqToHom _ ≫
          projModelBaseChange (sectionsMapLE (legendreClassifyingMap X L b hD h2)
            (show w.V.1 ≤ legendreClassifyingMap X L b hD h2 ⁻¹ᵁ
              (⊤ : (Spec (CommRingCat.of (LegendreModuliRing R))).Opens) from
              fun x _ => trivial))
            ((universalLegendre R).map
              (Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom) =
        eqToHom _ ≫
          projModelBaseChange (sectionsMapLE (legendreClassifyingMap X L b hD h2)
            (show w.V.1 ≤ legendreClassifyingMap X L b hD h2 ⁻¹ᵁ
              (⊤ : (Spec (CommRingCat.of (LegendreModuliRing R))).Opens) from
              fun x _ => trivial))
            ((universalLegendre R).map
              (Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom)
      rw [eqToHom_trans_assoc]
    · -- the `π` leg
      rw [Category.assoc,
        show eqToHom (congrArg projModel hWeq.symm) ≫
            projModelπ ((tautPresentation (universalLegendre R)).W.map
              (algebraMap Γ(Spec (CommRingCat.of (LegendreModuliRing R)),
                (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
                  (LegendreModuliRing R))).affineOpens).1) Γ(X.base, w.V.1))) =
          projModelπ ((w.Pr).W) from projModelπ_congr hWeq.symm,
        (w.Pr).compat_π]
      exact ((tautPresentation (universalLegendre R)).transport
        (legendreClassifyingEllHom hD h2 hR).baseHom (legendreClassifyingEllHom hD h2 hR).top
        (legendreClassifyingEllHom hD h2 hR).isPullback (legendreClassifyingEllHom hD h2 hR).zero_w
        _).compat_π
  rw [hkey, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation TopologicalSpace in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-7 rt1 ★★)** Roundtrip, `ω`-half: pulling the universal Legendre
`ω`-basis back along the classifying morphism recovers the given basis. The ratio
unit reads as the witness-vs-transported-taut transition unit, which is `1` by the
geometric rt1-core. -/
theorem omegaBasisMap_legendreClassifyingEllHom {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    (hR : IsUnit (2 : R)) :
    omegaBasisMap (legendreClassifyingEllHom hD h2 hR)
      (universalLegendreOmega R hR) = b := by
  haveI := universalLegendre_isElliptic R hR
  obtain ⟨u, hu, -⟩ := OmegaBasis.existsUnique_unit_smul b
    (omegaBasisMap (legendreClassifyingEllHom hD h2 hR)
      (universalLegendreOmega R hR))
  have h1 : u = 1 := by
    refine Scheme.unit_ext_of_res_cover X.base
      (fun w : LegendreWitness X L b => w.V.1)
      (fun w => le_top) (fun x _ => ?_) (fun w => ?_)
    · obtain ⟨V, hxV, Pr, lam, hAd, hW, hMP, hMQ⟩ := hD x
      exact Opens.mem_iSup.mpr ⟨⟨V, Pr, lam, hAd, hW, hMP, hMQ⟩, hxV⟩
    · -- the transition unit of the transported taut against the witness is 1
      have htu : ((tautPresentation (universalLegendre R)).transport
          (legendreClassifyingEllHom hD h2 hR).baseHom
          (legendreClassifyingEllHom hD h2 hR).top
          (legendreClassifyingEllHom hD h2 hR).isPullback
          (legendreClassifyingEllHom hD h2 hR).zero_w
          (show w.V.1 ≤ (legendreClassifyingEllHom hD h2 hR).baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (LegendreModuliRing R))).affineOpens).1 from
            fun x _ => trivial)).transUnit (w.Pr) = 1 := by
        show (((tautPresentation (universalLegendre R)).transport
          (legendreClassifyingEllHom hD h2 hR).baseHom
          (legendreClassifyingEllHom hD h2 hR).top
          (legendreClassifyingEllHom hD h2 hR).isPullback
          (legendreClassifyingEllHom hD h2 hR).zero_w
          (show w.V.1 ≤ (legendreClassifyingEllHom hD h2 hR).baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (LegendreModuliRing R))).affineOpens).1 from
            fun x _ => trivial)).transVC (w.Pr)).u = 1
        rw [transVC_transport_legendre hD h2 hR w]
        rfl
      have hAT : (w.Pr).transUnit
          ((tautPresentation (universalLegendre R)).transport
            (legendreClassifyingEllHom hD h2 hR).baseHom
            (legendreClassifyingEllHom hD h2 hR).top
            (legendreClassifyingEllHom hD h2 hR).isPullback
            (legendreClassifyingEllHom hD h2 hR).zero_w
            (show w.V.1 ≤ (legendreClassifyingEllHom hD h2 hR).baseHom ⁻¹ᵁ
              (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
                (LegendreModuliRing R))).affineOpens).1 from
              fun x _ => trivial)) = 1 := by
        have h := transUnit_trans (w.Pr)
          ((tautPresentation (universalLegendre R)).transport
            (legendreClassifyingEllHom hD h2 hR).baseHom
            (legendreClassifyingEllHom hD h2 hR).top
            (legendreClassifyingEllHom hD h2 hR).isPullback
            (legendreClassifyingEllHom hD h2 hR).zero_w
            (show w.V.1 ≤ (legendreClassifyingEllHom hD h2 hR).baseHom ⁻¹ᵁ
              (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
                (LegendreModuliRing R))).affineOpens).1 from
              fun x _ => trivial))
          (w.Pr)
        rw [htu, mul_one, transUnit_self] at h
        exact h
      have hTad : (((tautPresentation (universalLegendre R)).transport
          (legendreClassifyingEllHom hD h2 hR).baseHom
          (legendreClassifyingEllHom hD h2 hR).top
          (legendreClassifyingEllHom hD h2 hR).isPullback
          (legendreClassifyingEllHom hD h2 hR).zero_w
          (show w.V.1 ≤ (legendreClassifyingEllHom hD h2 hR).baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (LegendreModuliRing R))).affineOpens).1 from
            fun x _ => trivial)).basisUnitAt
          (omegaBasisMap (legendreClassifyingEllHom hD h2 hR)
            (universalLegendreOmega R hR))).1 = 1 :=
        IsAdapted.transport (legendreClassifyingEllHom hD h2 hR)
          (tautPresentation_isAdapted_legendre R hR) _
      have hkey : ((w.Pr).basisUnitAt
          (omegaBasisMap (legendreClassifyingEllHom hD h2 hR)
            (universalLegendreOmega R hR))).1 = 1 := by
        rw [basisUnitAt_transUnit (w.Pr)
          ((tautPresentation (universalLegendre R)).transport
            (legendreClassifyingEllHom hD h2 hR).baseHom
            (legendreClassifyingEllHom hD h2 hR).top
            (legendreClassifyingEllHom hD h2 hR).isPullback
            (legendreClassifyingEllHom hD h2 hR).zero_w
            (show w.V.1 ≤ (legendreClassifyingEllHom hD h2 hR).baseHom ⁻¹ᵁ
              (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
                (LegendreModuliRing R))).affineOpens).1 from
              fun x _ => trivial))
          (omegaBasisMap (legendreClassifyingEllHom hD h2 hR)
            (universalLegendreOmega R hR)),
          hAT, hTad, one_mul]
      have hsm := basisUnitAt_smul (w.Pr) u b
      rw [hu] at hsm
      have hALb : ((w.Pr).basisUnitAt b).1 = 1 := w.hAd
      rw [hkey, hALb, mul_one] at hsm
      rw [map_one]
      exact hsm.symm
  rw [← hu, h1]
  exact Subtype.ext (by
    rw [show ((1 : Γ(X.base, ⊤)ˣ) • b).1 =
      ((1 : Γ(X.base, ⊤)ˣ)).val • b.1 from rfl, Units.val_one, one_smul])

section RT2

variable {R : CommRingCat.{u}} {X : EllObj R} {hR : IsUnit (2 : R)}

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-8 rt2 ★)** The transported tautological witness of the pulled datum:
for ANY `Ell/R`-morphism `φ` to the universal Legendre object (with the universal
level clause `hL`), the transported taut chart over any affine is a Legendre witness
of the pulled datum. This is rt2's per-affine determination data. -/
noncomputable def pulledWitness (φ : X ⟶ universalLegendreObj R hR)
    (hL : (universalLegendreObj R hR).curve.IsNaiveFullLevel 2
      (universalLegendreP R hR) (universalLegendreQ R hR))
    (V : X.base.affineOpens) :
    LegendreWitness X
      ((gammaFullNaiveProblem R 2).map (Opposite.op φ)
        ⟨⟨universalLegendreP R hR, universalLegendreQ R hR⟩, hL⟩)
      (omegaBasisMap φ (universalLegendreOmega R hR)) := by
  haveI := universalLegendre_isElliptic R hR
  refine
    { V := V
      Pr := (tautPresentation (universalLegendre R)).transport
        φ.baseHom φ.top φ.isPullback φ.zero_w
        (show V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial)
      lam := sectionsMapLE φ.baseHom
        (show V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial)
        ((Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom
          (universalLambda R))
      hAd := IsAdapted.transport φ (tautPresentation_isAdapted_legendre R hR) _
      hW := ?_
      hMP := ?_
      hMQ := ?_ }
  · show (tautPresentation (universalLegendre R)).W.map _ = _
    rw [show (tautPresentation (universalLegendre R)).W =
      (universalLegendre R).map ((Scheme.ΓSpecIso (CommRingCat.of
        (LegendreModuliRing R))).inv.hom) from rfl]
    rw [show (universalLegendre R) = legendreCurve (universalLambda R) from rfl,
      legendreCurve_map, legendreCurve_map]
    rfl
  · -- the P-marking: transport the universal marking; the pulled section is
    -- DEFINITIONALLY the pullback-lift, so the square is `lift_fst`
    have hmark := tautPresentation_marksAt (universalLegendre R) 0 0
      (legendreCurve_equation_zero (universalLambda R))
    rw [map_zero] at hmark
    have hcomm : (EllHom.pullSection R φ (universalLegendreP R hR)).1 ≫ φ.top =
        φ.baseHom ≫ (universalLegendreP R hR).1 :=
      φ.isPullback.lift_fst _ _ _
    have htr := LocalPresentation.MarksAt.transport φ.baseHom φ.top
      φ.isPullback φ.zero_w hmark
      (EllHom.pullSection R φ (universalLegendreP R hR)).2 hcomm
      (V' := V) (fun x _ => trivial)
    rw [map_zero] at htr
    exact htr
  · have hmark := tautPresentation_marksAt (universalLegendre R) 1 0
      (legendreCurve_equation_one (universalLambda R))
    rw [map_one, map_zero] at hmark
    have hcomm : (EllHom.pullSection R φ (universalLegendreQ R hR)).1 ≫ φ.top =
        φ.baseHom ≫ (universalLegendreQ R hR).1 :=
      φ.isPullback.lift_fst _ _ _
    have htr := LocalPresentation.MarksAt.transport φ.baseHom φ.top
      φ.isPullback φ.zero_w hmark
      (EllHom.pullSection R φ (universalLegendreQ R hR)).2 hcomm
      (V' := V) (fun x _ => trivial)
    rw [map_one, map_zero] at htr
    exact htr

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-8 rt2a ★)** The classifying algebra of the pulled datum is the
algebra of `φ` itself (mirrors `classifyingRingHom_omegaBasisMap`): `C`-scalars via
`base_w`, and the `λ`-generator via the pulled-witness family + `legendreLambda`'s
universal spec. -/
theorem legendreClassifyingRingHom_pulled (φ : X ⟶ universalLegendreObj R hR)
    (hL : (universalLegendreObj R hR).curve.IsNaiveFullLevel 2
      (universalLegendreP R hR) (universalLegendreQ R hR))
    (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    legendreClassifyingRingHom X
      ((gammaFullNaiveProblem R 2).map (Opposite.op φ)
        ⟨⟨universalLegendreP R hR, universalLegendreQ R hR⟩, hL⟩)
      (omegaBasisMap φ (universalLegendreOmega R hR))
      (IsLegendreDatum.map φ
        (universalLegendre_isLegendreDatum R hR hL)
        ((gammaFullNaiveProblem R 2).map (Opposite.op φ)
          ⟨⟨universalLegendreP R hR, universalLegendreQ R hR⟩, hL⟩)
        rfl rfl) h2 =
    ((Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv ≫
      φ.baseHom.appTop).hom := by
  haveI := universalLegendre_isElliptic R hR
  set hD' := IsLegendreDatum.map φ
    (universalLegendre_isLegendreDatum R hR hL)
    ((gammaFullNaiveProblem R 2).map (Opposite.op φ)
      ⟨⟨universalLegendreP R hR, universalLegendreQ R hR⟩, hL⟩)
    rfl rfl with hD'def
  have hψR : ∀ r : R,
      ((Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv ≫
        φ.baseHom.appTop).hom (algebraMap R (LegendreModuliRing R) r) =
      X.baseRingHom r := by
    intro r
    have hb : CommRingCat.ofHom (algebraMap R (LegendreModuliRing R)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv ≫
          φ.baseHom.appTop =
        CommRingCat.ofHom X.baseRingHom := by
      rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop,
        show φ.baseHom ≫ Spec.map (CommRingCat.ofHom
            (algebraMap R (LegendreModuliRing R))) = X.structMap from φ.base_w]
      rfl
    exact congrArg (fun g => CommRingCat.Hom.hom g r) hb
  -- the λ-generator: sheaf-ext over the pulled-witness family
  have hcover : (⊤ : X.base.Opens) ≤
      iSup (fun V : X.base.affineOpens => V.1) := by
    intro x _
    obtain ⟨V₀, hVaff, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.base.Opens) from trivial)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V₀, hVaff⟩, hxV⟩
  have hnat : (legendreLambda X _ _ hD' h2).1 =
      ((Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv ≫
        φ.baseHom.appTop).hom (universalLambda R) := by
    refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
      (fun V : X.base.affineOpens => V.1) ⊤
      (fun V => homOfLE le_top) hcover _ _ (fun V => ?_)
    show Scheme.resLE le_top (legendreLambda X _ _ hD' h2).1 =
      Scheme.resLE le_top
        (((Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv ≫
          φ.baseHom.appTop).hom (universalLambda R))
    have hres : Scheme.resLE (le_top : V.1 ≤ ⊤)
        (((Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv ≫
          φ.baseHom.appTop).hom (universalLambda R)) =
        sectionsMapLE φ.baseHom
          (show V.1 ≤ φ.baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial)
          ((Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom
            (universalLambda R)) := rfl
    rw [hres]
    exact (legendreLambda X _ _ hD' h2).2
      (pulledWitness φ hL V).V (pulledWitness φ hL V).Pr
      (pulledWitness φ hL V).lam (pulledWitness φ hL V).hAd
      (pulledWitness φ hL V).hW (pulledWitness φ hL V).hMP
  refine IsLocalization.ringHom_ext (Submonoid.powers (legendrePoly R)) ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
  · show legendreClassifyingRingHom X _ _ hD' h2
      (algebraMap (MvPolynomial (Fin 1) R) (LegendreModuliRing R) (C r)) = _
    rw [show algebraMap (MvPolynomial (Fin 1) R) (LegendreModuliRing R) (C r) =
        algebraMap R (LegendreModuliRing R) r from by
      rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 1) R)
        (LegendreModuliRing R)]
      rfl]
    rw [legendreClassifyingRingHom_algebraMap]
    exact (hψR r).symm
  · show legendreClassifyingRingHom X _ _ hD' h2
      (algebraMap (MvPolynomial (Fin 1) R) (LegendreModuliRing R)
        (MvPolynomial.X j)) = _
    rw [legendreClassifyingRingHom, IsLocalization.Away.lift_eq]
    rw [show (eval₂Hom X.baseRingHom
        ![(legendreLambda X _ _ hD' h2).1]) (MvPolynomial.X j) =
      ![(legendreLambda X _ _ hD' h2).1] j from eval₂Hom_X' _ _ _]
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    show (legendreLambda X _ _ hD' h2).1 = _
    rw [hnat]
    rfl

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-8 rt2a ★)** BaseHom determination (mirrors
`classifyingMap_omegaBasisMap`). -/
theorem legendreClassifyingMap_pulled (φ : X ⟶ universalLegendreObj R hR)
    (hL : (universalLegendreObj R hR).curve.IsNaiveFullLevel 2
      (universalLegendreP R hR) (universalLegendreQ R hR))
    (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    legendreClassifyingMap X
      ((gammaFullNaiveProblem R 2).map (Opposite.op φ)
        ⟨⟨universalLegendreP R hR, universalLegendreQ R hR⟩, hL⟩)
      (omegaBasisMap φ (universalLegendreOmega R hR))
      (IsLegendreDatum.map φ
        (universalLegendre_isLegendreDatum R hR hL)
        ((gammaFullNaiveProblem R 2).map (Opposite.op φ)
          ⟨⟨universalLegendreP R hR, universalLegendreQ R hR⟩, hL⟩)
        rfl rfl) h2 = φ.baseHom := by
  show X.base.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (legendreClassifyingRingHom X _ _ _ h2)) = φ.baseHom
  rw [show CommRingCat.ofHom
      (legendreClassifyingRingHom X
        ((gammaFullNaiveProblem R 2).map (Opposite.op φ)
          ⟨⟨universalLegendreP R hR, universalLegendreQ R hR⟩, hL⟩)
        (omegaBasisMap φ (universalLegendreOmega R hR))
        (IsLegendreDatum.map φ
          (universalLegendre_isLegendreDatum R hR hL)
          ((gammaFullNaiveProblem R 2).map (Opposite.op φ)
            ⟨⟨universalLegendreP R hR, universalLegendreQ R hR⟩, hL⟩)
          rfl rfl) h2) =
    (Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv ≫
      φ.baseHom.appTop from by
    rw [legendreClassifyingRingHom_pulled φ hL h2]
    rfl]
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
  show φ.baseHom ≫ (Spec (CommRingCat.of (LegendreModuliRing R))).toSpecΓ ≫
    Spec.map (Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv =
    φ.baseHom
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  exact Category.comp_id _

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-8 rt2b ★★)** Top determination: the glued classifying comparison of
the pulled datum IS `φ`'s total-space morphism (mirrors `classifyingTop_omegaBasisMap`;
`legendrePiece_congr` at the pulled witness replaces the e-determination step). -/
theorem legendreTop_pulled (φ : X ⟶ universalLegendreObj R hR)
    (hL : (universalLegendreObj R hR).curve.IsNaiveFullLevel 2
      (universalLegendreP R hR) (universalLegendreQ R hR))
    (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    legendreTop (IsLegendreDatum.map φ
      (universalLegendre_isLegendreDatum R hR hL)
      ((gammaFullNaiveProblem R 2).map (Opposite.op φ)
        ⟨⟨universalLegendreP R hR, universalLegendreQ R hR⟩, hL⟩)
      rfl rfl) h2 = φ.top := by
  haveI := universalLegendre_isElliptic R hR
  set hD' := IsLegendreDatum.map φ
    (universalLegendre_isLegendreDatum R hR hL)
    ((gammaFullNaiveProblem R 2).map (Opposite.op φ)
      ⟨⟨universalLegendreP R hR, universalLegendreQ R hR⟩, hL⟩)
    rfl rfl with hD'def
  letI : Algebra (LegendreModuliRing R)
      Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom.toAlgebra
  haveI : IsIso (⊤ : (Spec (CommRingCat.of (LegendreModuliRing R))).Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap (LegendreModuliRing R)
      Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤)))) := by
    have h : CommRingCat.ofHom (algebraMap (LegendreModuliRing R)
        Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv := rfl
    rw [h]
    infer_instance
  have hfst : pullback.fst (projModelπ (universalLegendre R))
      (⊤ : (Spec (CommRingCat.of (LegendreModuliRing R))).Opens).ι =
      (tautPresentation (universalLegendre R)).e.hom ≫
        (isPullback_projModelBaseChange (universalLegendre R)).isoPullback.hom ≫
        pullback.fst (projModelπ (universalLegendre R))
          (Spec.map (CommRingCat.ofHom (algebraMap (LegendreModuliRing R)
            Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤)))) := by
    rw [show (tautPresentation (universalLegendre R)).e.hom =
      (asIso (pullback.fst (projModelπ (universalLegendre R))
        (⊤ : (Spec (CommRingCat.of (LegendreModuliRing R))).Opens).ι) ≪≫
      (asIso (pullback.fst (projModelπ (universalLegendre R))
        (Spec.map (CommRingCat.ofHom (algebraMap (LegendreModuliRing R)
          Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤)))))).symm ≪≫
      (isPullback_projModelBaseChange (universalLegendre R)).isoPullback.symm).hom
      from rfl]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
      Iso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  refine (legendreWitnessCover hD').hom_ext _ _ (fun w => ?_)
  rw [legendreTop_piece hD' h2 w, legendreWitnessCover_f]
  rw [legendrePiece_congr hD' h2 w (pulledWitness φ hL w.V) rfl, eqToHom_refl,
    Category.id_comp]
  -- now: chartPiece(pulled) = fst ≫ φ.top; unfold the φ-side through the transport
  rw [show pullback.fst X.curve.toEllipticCurveGeom.π w.V.1.ι ≫ φ.top =
    transportTheta φ.baseHom φ.top φ.isPullback
      (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial) ≫
      pullback.fst (projModelπ (universalLegendre R))
        (⊤ : (Spec (CommRingCat.of (LegendreModuliRing R))).Opens).ι from
    (transportTheta_fst φ.baseHom φ.top φ.isPullback _).symm]
  rw [hfst, ← Category.assoc,
    show transportTheta φ.baseHom φ.top φ.isPullback
        (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial) ≫
      (tautPresentation (universalLegendre R)).e.hom =
    ((tautPresentation (universalLegendre R)).transport
      φ.baseHom φ.top φ.isPullback φ.zero_w
      (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial)).e.hom ≫
      projModelBaseChange (sectionsMapLE φ.baseHom
        (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial))
        (tautPresentation (universalLegendre R)).W from
    (transport_e_baseChange φ.baseHom φ.top φ.isPullback φ.zero_w
      (tautPresentation (universalLegendre R)) _).symm]
  -- collapse the universal-side chain into a single base change along the composite
  have hσ : (sectionsMapLE φ.baseHom
      (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial)).comp
      ((Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom) =
      ((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (legendreClassifyingRingHom X _ _ hD' h2) := by
    rw [sectionsMapLE_congr_hom (legendreClassifyingMap_pulled φ hL h2).symm
      (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial)]
    exact sectionsMapLE_legendreClassifyingMap hD' h2 w.V (fun x _ => trivial)
  rw [show projModelBaseChange (sectionsMapLE φ.baseHom
      (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial))
      (tautPresentation (universalLegendre R)).W =
    projModelBaseChange (sectionsMapLE φ.baseHom
      (show w.V.1 ≤ φ.baseHom ⁻¹ᵁ
        (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
          (LegendreModuliRing R))).affineOpens).1 from fun x _ => trivial))
      ((universalLegendre R).map
        ((Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom)) from rfl]
  rw [show (isPullback_projModelBaseChange (universalLegendre R)).isoPullback.hom ≫
      pullback.fst (projModelπ (universalLegendre R))
        (Spec.map (CommRingCat.ofHom (algebraMap (LegendreModuliRing R)
          Γ(Spec (CommRingCat.of (LegendreModuliRing R)), ⊤)))) =
    projModelBaseChange
      ((Scheme.ΓSpecIso (CommRingCat.of (LegendreModuliRing R))).inv.hom)
      (universalLegendre R) from
    (isPullback_projModelBaseChange (universalLegendre R)).isoPullback_hom_fst]
  rw [Category.assoc, ← projModelBaseChange_comp',
    projModelBaseChange_congr_hom hσ (universalLegendre R)]
  rw [legendrePiece]
  rfl


open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
/-- **(T-E14-CLS-8 rt2 ★★★)** Uniqueness half of KM 4.6.2's universal property: ANY
`Ell/R`-morphism to the universal Legendre object is the classifying morphism of the
datum it pulls back. -/
theorem legendreClassifyingEllHom_pulled (φ : X ⟶ universalLegendreObj R hR)
    (hL : (universalLegendreObj R hR).curve.IsNaiveFullLevel 2
      (universalLegendreP R hR) (universalLegendreQ R hR))
    (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    legendreClassifyingEllHom
      (IsLegendreDatum.map φ
        (universalLegendre_isLegendreDatum R hR hL)
        ((gammaFullNaiveProblem R 2).map (Opposite.op φ)
          ⟨⟨universalLegendreP R hR, universalLegendreQ R hR⟩, hL⟩)
        rfl rfl) h2 hR = φ :=
  EllHom.ext (legendreClassifyingMap_pulled φ hL h2) (legendreTop_pulled φ hL h2)

open AlgebraicGeometry CategoryTheory Scheme in
/-- If `2` is a unit in `R`, it is a unit in the global sections of every
`Ell/R`-object's base. -/
theorem EllObj.isUnit_two {R : CommRingCat.{u}} (Y : EllObj R)
    (hR : IsUnit (2 : R)) : IsUnit (2 : Γ(Y.base, ⊤)) := by
  have h := hR.map Y.baseRingHom
  rwa [map_ofNat] at h

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-AX1 ★★★, KM 4.6.2's engine axiom 1, conditional form)** GIVEN the
naive-full-level clause for the universal marked pair (ticket [T-E14-LVL-b]: the
geometric `E[2]`-generation, deferred to the KM keystone), the Legendre `δ` is
representable by the universal Legendre object: the natural bijection sends `φ` to
the pulled datum; its inverse is the classifying morphism; the roundtrips are rt1
and rt2. -/
noncomputable def legendreDeltaRepresentableBy (R : CommRingCat.{u})
    (hR : IsUnit (2 : R))
    (hL : (universalLegendreObj R hR).curve.IsNaiveFullLevel 2
      (universalLegendreP R hR) (universalLegendreQ R hR)) :
    (legendreDeltaProblem R).RepresentableBy (universalLegendreObj R hR) where
  homEquiv {X} :=
    { toFun := fun φ => (legendreDeltaProblem R).map (Opposite.op φ)
        ⟨⟨⟨⟨universalLegendreP R hR, universalLegendreQ R hR⟩, hL⟩,
          universalLegendreOmega R hR⟩,
          universalLegendre_isLegendreDatum R hR hL⟩
      invFun := fun x => legendreClassifyingEllHom x.2
        (X.isUnit_two hR) hR
      left_inv := fun φ => legendreClassifyingEllHom_pulled φ hL (X.isUnit_two hR)
      right_inv := fun x => by
        refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext ?_ ?_)) ?_)
        · exact pullSection_legendreClassifyingEllHom_P x.2 (X.isUnit_two hR) hR
        · exact pullSection_legendreClassifyingEllHom_Q x.2 (X.isUnit_two hR) hR
        · exact omegaBasisMap_legendreClassifyingEllHom x.2 (X.isUnit_two hR) hR }
  homEquiv_comp {X X'} f g :=
    FunctorToTypes.map_comp_apply (legendreDeltaProblem R)
      (Opposite.op g) (Opposite.op f) _

open AlgebraicGeometry CategoryTheory Scheme in
/-- **(T-E14-AX1, conditional discharge ★★★)** KM engine axiom 1 for the corrected
Legendre `δ`, modulo the [T-E14-LVL-b] level clause: the `δ` is representable by an
object with affine base — `M'₂ = Spec R[λ][(λ(λ−1))⁻¹]`. -/
theorem legendreDelta_representable_by_affine_of_level (R : CommRingCat.{u})
    (hR : IsUnit (2 : R))
    (hL : (universalLegendreObj R hR).curve.IsNaiveFullLevel 2
      (universalLegendreP R hR) (universalLegendreQ R hR)) :
    ∃ X : EllObj R, IsAffine X.base ∧
      Nonempty ((legendreDeltaProblem R).RepresentableBy X) :=
  ⟨universalLegendreObj R hR,
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (LegendreModuliRing R)))),
    ⟨legendreDeltaRepresentableBy R hR hL⟩⟩

end RT2

end TwoTorsion

end ModularCurves
