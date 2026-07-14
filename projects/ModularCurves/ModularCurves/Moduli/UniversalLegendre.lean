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

end TwoTorsion

end ModularCurves
