/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.AwayCongr
import ModularCurves.ForMathlib.GradedQuotient
import ModularCurves.ForMathlib.StandardSmoothHypersurface
import ModularCurves.ForMathlib.ProjClosedImmersion
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The projective Weierstrass model as a scheme

Mathlib's `WeierstrassCurve R` is an equation (a tuple `a₁, …, a₆`), not a scheme. This file
fixes the interface between that equation-level API and honest schemes: what it means for a
pointed `R`-scheme to *be* the plane projective model
`Y²Z + a₁XYZ + a₃YZ² = X³ + a₂X²Z + a₄XZ² + a₆Z³` of `W`, with base point `[0:1:0]`.

## Mathematical content

For `W : WeierstrassCurve R` the projective model is the closed subscheme of `ℙ²_R` cut out by
the homogeneous Weierstrass cubic, together with its structure morphism to `Spec R` and the
section at infinity `[0:1:0]`. It is proper, and it is smooth of relative dimension 1 iff `Δ(W)`
is a unit (KM 2.2; Loeffler, *Modular curves*, §3.3, Def 3.3.3; Silverman III.3).

**Construction status.** The model is *CONSTRUCTED* here (2026-07-06, T-A2 — DS1 is no
longer a data-sorry): Hida's route of record (decomposition-gme2 A7.e),
`projModel W = Proj (R[X,Y,Z]/(Weierstrass cubic))` via the quotient grading of
`ForMathlib/GradedQuotient.lean` and mathlib's `Proj` API; `π` is `Proj.toSpecZero`
followed by the degree-zero identification, and the section at infinity `[0:1:0]` is
`Proj.fromOfGlobalSections` at the evaluation `X ↦ 0, Y ↦ 1, Z ↦ 0`. The composite
`zero ≫ π = 𝟙` is PROVED (`projModelZero_projModelπ`). The interface theorem
(`projModel_isWeierstrassModel`: properness/lfp/points) remains T-A2's open spec, with
smoothness (T-A3) via the chartwise Jacobian analysis (GME pp. 114–115).
No downstream file may use `projModel` except through `IsWeierstrassModel`, the theorems
stated here, and the fibrewise bridge `FibrewiseElliptic` (sanctioned raw-iso consumer,
expert review Q2).

## References

* [KM] Katz–Mazur, *Arithmetic moduli of elliptic curves*, Ch. 2.2.
* [Loe] Loeffler, *Modular curves* lecture notes, §3.3.
* [Sil] Silverman, *AEC* III.3.1 (every pointed smooth genus-1 curve over a field is a
  Weierstrass cubic — the Riemann–Roch input, black-boxed by this project).
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-- The `K`-points of an `R`-scheme `X`, for `K` an `R`-algebra: morphisms
`Spec K ⟶ X` over `Spec R`. -/
def SpecPoints (X : Scheme.{u}) (f : X ⟶ Spec (.of R)) (K : Type u) [CommRing K] [Algebra R K] :
    Type u :=
  { g : Spec (.of K) ⟶ X // g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)) }

/-- `IsWeierstrassModel W X f x₀` says that the pointed `R`-scheme `(X, f, x₀)` is *a*
plane projective model of the Weierstrass curve `W`: proper, of finite presentation,
with a section, and — **when `W` is elliptic** — its `K`-points over every `R`-algebra
field `K` biject with the Weierstrass points `(W.baseChange K).toAffine.Point`,
POINTEDLY (`x₀ ↦ 0`).

ADVERSARIAL FIX (2026-07-05, DEF-7): the points clause is (i) guarded by
`W.IsElliptic` — mathlib's `Affine.Point` contains only NONSINGULAR points, so for
singular `W` the honest projective cubic has strictly more `K`-points (cuspidal
`y² = x³` over `𝔽₅`: 6 vs 5) and the unguarded clause was false of the registered
model; and (ii) pointed — the bare `Nonempty (≃)` form did not tie `x₀` to `0` and
pinned nothing. Field-points cannot detect nilpotents, so this interface alone can
NEVER pin the model up to isomorphism (thickening counterexample `V(F)` vs `V(F²)`);
uniqueness additionally requires smoothness — see `isWeierstrassModel_unique`. -/
structure IsWeierstrassModel (W : WeierstrassCurve R) (X : Scheme.{u})
    (f : X ⟶ Spec (.of R)) (x₀ : Spec (.of R) ⟶ X) : Prop where
  isProper : IsProper f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  section_comp : x₀ ≫ f = 𝟙 _
  /-- Pointed `K`-points comparison, for elliptic `W`. -/
  points : ∀ (_ : W.IsElliptic) (K : Type u) [Field K] [Algebra R K],
    ∃ e : SpecPoints X f K ≃ (W.baseChange K).toAffine.Point,
      e ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ x₀, by
        rw [Category.assoc, section_comp, Category.comp_id]⟩ = 0

section ProjModel

open HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous Weierstrass cubic `Y²Z + a₁XYZ + a₃YZ² − (X³ + a₂X²Z + a₄XZ² + a₆Z³)`
is homogeneous of degree `3`. -/
theorem projective_polynomial_isHomogeneous (W : WeierstrassCurve R) :
    W.toProjective.polynomial.IsHomogeneous 3 := by
  have hX : (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) R).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X _ _
  have hY : (MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) R).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X _ _
  have hZ : (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) R).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X _ _
  refine MvPolynomial.IsHomogeneous.sub ?_ ?_
  · exact (((hY.pow 2).mul hZ).add
      ((((MvPolynomial.isHomogeneous_C _ _).mul hX).mul hY).mul hZ)).add
      (((MvPolynomial.isHomogeneous_C _ _).mul hY).mul (hZ.pow 2))
  · exact (((hX.pow 3).add
      (((MvPolynomial.isHomogeneous_C _ _).mul (hX.pow 2)).mul hZ)).add
      (((MvPolynomial.isHomogeneous_C _ _).mul hX).mul (hZ.pow 2))).add
      ((MvPolynomial.isHomogeneous_C _ _).mul (hZ.pow 3))

/-- The homogeneous ideal `(W)` generated by the Weierstrass cubic. -/
noncomputable def projIdeal (W : WeierstrassCurve R) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) R) :=
  ⟨Ideal.span {W.toProjective.polynomial}, Ideal.homogeneous_span _ _ (by
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨3, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (projective_polynomial_isHomogeneous W)⟩)⟩

@[simp]
lemma projIdeal_toIdeal (W : WeierstrassCurve R) :
    (projIdeal W).toIdeal = Ideal.span {W.toProjective.polynomial} :=
  rfl

/-- The homogeneous coordinate ring `R[X,Y,Z]/(W)` of the plane Weierstrass cubic. -/
noncomputable abbrev projCoordRing (W : WeierstrassCurve R) : Type u :=
  MvPolynomial (Fin 3) R ⧸ (projIdeal W).toIdeal

/-- **(T-A2, CONSTRUCTED 2026-07-06 — formerly DS1)** The plane projective model of a
Weierstrass curve, as a scheme over `Spec R`: `Proj` of the homogeneous coordinate ring
`R[X,Y,Z]/(W)`, graded by the quotient grading (`ForMathlib/GradedQuotient.lean`).
Route of record: decomposition-gme2 A7.e (Hida GME §2.2.5).
Consumers must use only `IsWeierstrassModel` facts about it (plus the fibrewise bridge,
expert review Q2). -/
@[reducible] noncomputable def projModel (W : WeierstrassCurve R) : Scheme.{u} :=
  Proj (quotientGrading (projIdeal W))

/-- **(T-A2)** The structure morphism of the projective Weierstrass model:
`Proj.toSpecZero` followed by the degree-zero identification `R → (R[X,Y,Z]/(W))₀`. -/
noncomputable def projModelπ (W : WeierstrassCurve R) : projModel W ⟶ Spec (.of R) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W)))

/-- Evaluation of the homogeneous coordinate ring at the point at infinity `[0:1:0]`. -/
noncomputable def projModelZeroEval (W : WeierstrassCurve R) : projCoordRing W →+* R :=
  Ideal.Quotient.lift _ (MvPolynomial.eval fun i : Fin 3 => if i = 1 then 1 else 0) (by
    intro a ha
    rw [projIdeal_toIdeal, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    have hF : MvPolynomial.eval (fun i : Fin 3 => if i = 1 then 1 else 0)
        W.toProjective.polynomial = 0 := by
      simp [WeierstrassCurve.Projective.polynomial]
    rw [map_mul, hF, zero_mul])

@[simp]
lemma projModelZeroEval_mk (W : WeierstrassCurve R) (p : MvPolynomial (Fin 3) R) :
    projModelZeroEval W (Ideal.Quotient.mk (projIdeal W).toIdeal p) =
      MvPolynomial.eval (fun i : Fin 3 => if i = 1 then 1 else 0) p :=
  Ideal.Quotient.lift_mk _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The class of `Y` lies in the irrelevant ideal of the quotient grading. -/
lemma mk_Y_mem_irrelevant (W : WeierstrassCurve R) :
    Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X 1) ∈
      (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal := by
  show GradedRing.proj (quotientGrading (projIdeal W)) 0
      (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X 1)) = 0
  rw [GradedRing.proj_apply,
    decompose_quotientGrading_mk (projIdeal W)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X _ _)),
    DirectSum.coe_of_apply]
  simp

/-- The evaluation at `[0:1:0]` maps the irrelevant ideal onto the unit ideal. -/
lemma projModelZeroEval_irrelevant_map_top (W : WeierstrassCurve R) :
    (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal.map
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (projModelZeroEval W))
      (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X 1)) = 1 := by
    rw [RingHom.comp_apply, projModelZeroEval_mk]
    simp
  rw [← h1]
  exact Ideal.mem_map_of_mem _ (mk_Y_mem_irrelevant W)

/-- **(T-A2)** The section at infinity `[0:1:0]` of the projective Weierstrass model,
via `Proj.fromOfGlobalSections` at the evaluation `X ↦ 0, Y ↦ 1, Z ↦ 0`. -/
noncomputable def projModelZero (W : WeierstrassCurve R) : Spec (.of R) ⟶ projModel W :=
  Proj.fromOfGlobalSections _
    ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W))
    (projModelZeroEval_irrelevant_map_top W)

/-- **(T-A2, PROVED)** The section at infinity is a section of the structure morphism:
`[0:1:0]` lies over the identity of `Spec R`. -/
@[reassoc (attr := simp)]
theorem projModelZero_projModelπ (W : WeierstrassCurve R) :
    projModelZero W ≫ projModelπ W = 𝟙 _ := by
  have key : (((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
        (projModelZeroEval W)).comp
          (algebraMap (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W))).comp
      (algebraMapGradeZero (projIdeal W)) =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    ext r
    have hmk : algebraMap R (projCoordRing W) r =
        Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.C r) := by
      rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing W),
        RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
    show (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (projModelZeroEval W
        (algebraMap _ (projCoordRing W) (algebraMapGradeZero (projIdeal W) r))) = _
    rw [show (algebraMap (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W))
        (algebraMapGradeZero (projIdeal W) r) = algebraMap R (projCoordRing W) r from rfl,
      hmk, projModelZeroEval_mk]
    simp
  rw [projModelZero, projModelπ]
  simp only [Proj.fromOfGlobalSections_toSpecZero_assoc]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, key, CommRingCat.ofHom_hom]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of R)

/-- Evaluation at `[0:1:0]` retracts the degree-zero inclusion: the composite
`R → (R[X,Y,Z]/(W))₀ → R[X,Y,Z]/(W) → R` is the identity. -/
@[simp]
lemma projModelZeroEval_algebraMapGradeZero (W : WeierstrassCurve R) (r : R) :
    projModelZeroEval W (algebraMap (↥(quotientGrading (projIdeal W) 0))
      (projCoordRing W) (algebraMapGradeZero (projIdeal W) r)) = r := by
  have hmk : algebraMap R (projCoordRing W) r =
      Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.C r) := by
    rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing W),
      RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
  rw [show (algebraMap (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W))
      (algebraMapGradeZero (projIdeal W) r) = algebraMap R (projCoordRing W) r from rfl,
    hmk, projModelZeroEval_mk]
  simp

theorem algebraMapGradeZero_bijective (W : WeierstrassCurve R) :
    Function.Bijective (algebraMapGradeZero (projIdeal W)) := by
  constructor
  · exact Function.LeftInverse.injective (g := fun x =>
      projModelZeroEval W (algebraMap _ (projCoordRing W) x))
      fun r => projModelZeroEval_algebraMapGradeZero W r
  · rintro ⟨x, hx⟩
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp
    have hdeg : p.totalDegree = 0 := Nat.le_zero.mp hp.totalDegree_le
    have hC : p = MvPolynomial.C (MvPolynomial.coeff 0 p) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
    refine ⟨MvPolynomial.coeff 0 p, Subtype.ext ?_⟩
    show algebraMap R (projCoordRing W) _ = Ideal.Quotient.mk (projIdeal W).toIdeal p
    rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing W),
      RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq, ← hC]

/-- The degree-zero part of the homogeneous coordinate ring is `R` itself. -/
noncomputable def gradeZeroRingEquiv (W : WeierstrassCurve R) :
    R ≃+* ↥(quotientGrading (projIdeal W) 0) :=
  RingEquiv.ofBijective _ (algebraMapGradeZero_bijective W)

instance (W : WeierstrassCurve R) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W)))) := by
  have h : CommRingCat.ofHom (algebraMapGradeZero (projIdeal W)) =
      (gradeZeroRingEquiv W).toCommRingCatIso.hom := rfl
  rw [h]
  infer_instance

instance (W : WeierstrassCurve R) :
    Algebra.FiniteType (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W) := by
  haveI h1 : Algebra.FiniteType R (projCoordRing W) :=
    Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ R (projIdeal W).toIdeal)
      (Ideal.Quotient.mkₐ_surjective R _)
  exact Algebra.FiniteType.of_restrictScalars_finiteType R
    (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W)

/-- **(T-A2, PROVED)** The projective Weierstrass model is proper over the base:
mathlib's properness of `Proj` (valuative criterion) composed with the degree-zero
identification. -/
instance projModelπ_isProper (W : WeierstrassCurve R) : IsProper (projModelπ W) := by
  unfold projModelπ
  haveI h1 : IsProper (Proj.toSpecZero (quotientGrading (projIdeal W))) := inferInstance
  haveI h2 : IsProper (Spec.map (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W)))) :=
    inferInstance
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ h1 h2

section Lfp

open HomogeneousLocalization

/-- The class of `X i` in the quotient grading, in degree one. -/
lemma mk_X_mem_quotientGrading_one (W : WeierstrassCurve R) (i : Fin 3) :
    (quotientGradingHom (projIdeal W)) (MvPolynomial.X i) ∈
      quotientGrading (projIdeal W) 1 :=
  mk_mem_quotientGrading _ (MvPolynomial.X_mem_homogeneousSubmodule_one R i)

/-- Finite presentation of each chart of the Weierstrass model over `R`:
the chart of `ℙ²` (a polynomial ring in two variables, via `chartRingEquiv`) modulo
the principal dehomogenised cubic. -/
theorem finitePresentation_awayQuotient (W : WeierstrassCurve R) (i : Fin 3) :
    RingHom.FinitePresentation
      ((HomogeneousLocalization.Away.map (quotientGradingHom (projIdeal W))
        (MvPolynomial.X i)).comp
          ((MvPolynomial.chartRingEquiv R i).symm :
            MvPolynomial {j : Fin 3 // j ≠ i} R →+*
              Away (MvPolynomial.homogeneousSubmodule (Fin 3) R) (MvPolynomial.X i))) := by
  refine RingHom.FinitePresentation.comp_surjective ?_ ?_ ?_
  · -- the chart equivalence is finitely presented (kernel ⊥, surjective)
    exact RingHom.FinitePresentation.of_surjective _
      (MvPolynomial.chartRingEquiv R i).symm.surjective
      (by rw [RingHom.ker_coe_equiv]; exact Submodule.fg_bot)
  · exact away_map_quotientGradingHom_surjective _
      (MvPolynomial.X_mem_homogeneousSubmodule_one R i)
  · rw [ker_away_map_quotientGradingHom (projIdeal W)
      (projective_polynomial_isHomogeneous W) (projIdeal_toIdeal W)
      (MvPolynomial.X_mem_homogeneousSubmodule_one R i)]
    exact Submodule.fg_span_singleton _

/-- Every irrelevant polynomial lies in the ideal generated by the variables. -/
lemma poly_irrelevant_le_idealOfVars :
    (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin 3) R)).toIdeal ≤
      MvPolynomial.idealOfVars (Fin 3) R := by
  intro p hp
  have hp0 : MvPolynomial.coeff 0 p = 0 := by
    have h1 : GradedRing.proj (MvPolynomial.homogeneousSubmodule (Fin 3) R) 0 p = 0 := hp
    rw [GradedRing.proj_apply] at h1
    have h2 : (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 3) R) p 0 :
        MvPolynomial (Fin 3) R) = MvPolynomial.homogeneousComponent 0 p :=
      MvPolynomial.decomposition.decompose'_apply p 0
    rw [h2, MvPolynomial.homogeneousComponent_zero] at h1
    exact MvPolynomial.C_injective _ _ (h1.trans (MvPolynomial.C_0).symm)
  rw [show MvPolynomial.idealOfVars (Fin 3) R =
      MvPolynomial.idealOfVars (Fin 3) R ^ 1 by rw [pow_one],
    MvPolynomial.mem_pow_idealOfVars_iff']
  intro x hx
  have hx0 : x = 0 := by
    have : Finsupp.degree x = 0 := by omega
    exact (Finsupp.degree_eq_zero_iff x).mp this
  rwa [hx0]

/-- The classes of the three variables cut out the irrelevant ideal of the coordinate
ring of the Weierstrass model. -/
lemma quotient_irrelevant_le_span_mk_X (W : WeierstrassCurve R) :
    (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal ≤
      Ideal.span (Set.range fun i : Fin 3 =>
        Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i)) := by
  intro z hz
  have h1 : z ∈ Ideal.map (quotientGradingHom (projIdeal W)).toRingHom
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin 3) R)).toIdeal :=
    quotientGradingHom_irrelevant_le (projIdeal W) hz
  have h2 : Ideal.map (quotientGradingHom (projIdeal W)).toRingHom
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin 3) R)).toIdeal ≤
      Ideal.map (quotientGradingHom (projIdeal W)).toRingHom
        (MvPolynomial.idealOfVars (Fin 3) R) :=
    Ideal.map_mono poly_irrelevant_le_idealOfVars
  have h3 : Ideal.map (quotientGradingHom (projIdeal W)).toRingHom
      (MvPolynomial.idealOfVars (Fin 3) R) =
      Ideal.span (Set.range fun i : Fin 3 =>
        Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i)) := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
    rfl
  exact h3 ▸ h2 h1

/-- The two `R`-structurings of a chart agree: through the degree-zero part, or
through the polynomial chart of `ℙ²`. -/
theorem algebraMap_gradeZero_comp_eq (W : WeierstrassCurve R) (i : Fin 3) :
    (algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
      ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0)) =
      ((HomogeneousLocalization.Away.map (quotientGradingHom (projIdeal W))
          (MvPolynomial.X i)).comp
        ((MvPolynomial.chartRingEquiv R i).symm :
          MvPolynomial {j : Fin 3 // j ≠ i} R →+*
            Away (MvPolynomial.homogeneousSubmodule (Fin 3) R)
              (MvPolynomial.X i))).comp
        (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ i} R)) := by
  refine RingHom.ext fun r => ?_
  have h1 : ((MvPolynomial.chartRingEquiv R i).symm :
      MvPolynomial {j : Fin 3 // j ≠ i} R →+* _)
        (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ i} R) r) =
      MvPolynomial.awayConst R i r := by
    show MvPolynomial.homogenizeAt R i
      (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ i} R) r) = _
    rw [show algebraMap R (MvPolynomial {j : Fin 3 // j ≠ i} R) r =
      MvPolynomial.C r from rfl, MvPolynomial.homogenizeAt, MvPolynomial.eval₂Hom_C]
    rfl
  apply val_injective
  have hR : (HomogeneousLocalization.Away.map (quotientGradingHom (projIdeal W))
      (MvPolynomial.X i) (MvPolynomial.awayConst R i r)).val =
      Localization.mk ((quotientGradingHom (projIdeal W)) (MvPolynomial.C r)) 1 := by
    rw [MvPolynomial.awayConst, Away.map_mk, Away.val_mk]
    exact congrArg _ (Subtype.ext (pow_zero _))
  simp only [RingHom.comp_apply]
  rw [h1, hR, HomogeneousLocalization.algebraMap_eq]
  show Localization.mk ((gradeZeroRingEquiv W r : ↥(quotientGrading (projIdeal W) 0)) :
    projCoordRing W) 1 = _
  have hval : ((gradeZeroRingEquiv W r : ↥(quotientGrading (projIdeal W) 0)) :
      projCoordRing W) = Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.C r) := by
    show algebraMap R (projCoordRing W) r = _
    rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing W),
      RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
  rw [hval]
  rfl

/-- Finite presentation of the canonical map from the degree-zero part into each
chart of the Weierstrass model. -/
theorem fp_algebraMap_gradeZero_away (W : WeierstrassCurve R) (i : Fin 3) :
    RingHom.FinitePresentation (algebraMap (↥(quotientGrading (projIdeal W) 0))
      (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))) := by
  have hEq := algebraMap_gradeZero_comp_eq W i
  have hCfp : RingHom.FinitePresentation
      (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ i} R)) :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hfg : RingHom.FinitePresentation ((algebraMap
      (↥(quotientGrading (projIdeal W) 0))
      (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
      ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) := by
    rw [hEq]
    exact RingHom.FinitePresentation.comp (finitePresentation_awayQuotient W i) hCfp
  have hsymm : RingHom.FinitePresentation
      (((gradeZeroRingEquiv W).symm : ↥(quotientGrading (projIdeal W) 0) →+* R)) :=
    RingHom.FinitePresentation.of_surjective _ (gradeZeroRingEquiv W).symm.surjective
      (by rw [RingHom.ker_coe_equiv]; exact Submodule.fg_bot)
  have hfinal : (algebraMap (↥(quotientGrading (projIdeal W) 0))
      (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))) =
      ((algebraMap _ _).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))).comp
      ((gradeZeroRingEquiv W).symm : ↥(quotientGrading (projIdeal W) 0) →+* R) := by
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.apply_symm_apply]
  rw [hfinal]
  exact RingHom.FinitePresentation.comp hfg hsymm

set_option backward.isDefEq.respectTransparency false in
instance (W : WeierstrassCurve R) :
    LocallyOfFinitePresentation (Proj.toSpecZero (quotientGrading (projIdeal W))) := by
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
    (Proj.iSup_basicOpen_eq_top (quotientGrading (projIdeal W))
      (fun i : Fin 3 => Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i))
      (quotient_irrelevant_le_span_mk_X W))]
  intro i
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation)
    (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W))
      (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i))
      (mk_X_mem_quotientGrading_one W i) one_pos).inv, ← Category.assoc,
    ← Proj.awayι, Proj.awayι_toSpecZero,
    HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact fp_algebraMap_gradeZero_away W i

/-- **(T-A2d, PROVED)** The projective Weierstrass model is locally of finite
presentation over the base. -/
theorem projModelπ_lfp (W : WeierstrassCurve R) :
    LocallyOfFinitePresentation (projModelπ W) := by
  unfold projModelπ
  haveI h1 : LocallyOfFinitePresentation
      (Proj.toSpecZero (quotientGrading (projIdeal W))) := inferInstance
  haveI h2 : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W)))) := by
    haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W)))) :=
      inferInstance
    infer_instance
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ h1 h2

end Lfp

end ProjModel

section Points

open HomogeneousIdeal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every `K`-point of the model factors through one of the three affine charts. -/
lemma specPoint_factors_through_chart (W : WeierstrassCurve R)
    {K : Type u} [Field K] [Algebra R K] (g : Spec (.of K) ⟶ projModel W) :
    ∃ (i : Fin 3) (h : Spec (.of K) ⟶
        Spec (.of (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))))),
      h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W i) one_pos = g := by
  have htop := Proj.iSup_basicOpen_eq_top (quotientGrading (projIdeal W))
    (fun i : Fin 3 => Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i))
    (quotient_irrelevant_le_span_mk_X W)
  have h1 : (⋃ i : Fin 3, ((Proj.basicOpen (quotientGrading (projIdeal W))
      (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i))) :
        Set (Proj (quotientGrading (projIdeal W))))) = Set.univ := by
    have h2 := congrArg
      (fun U : (Proj (quotientGrading (projIdeal W))).Opens =>
        (U : Set (Proj (quotientGrading (projIdeal W))))) htop
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top] at h2
    exact h2
  have hmem : g.base default ∈ ⋃ i : Fin 3,
      ((Proj.basicOpen (quotientGrading (projIdeal W))
        (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i))) :
        Set (Proj (quotientGrading (projIdeal W)))) := by
    rw [h1]
    exact Set.mem_univ _
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  refine ⟨i, IsOpenImmersion.lift
    (Proj.awayι (quotientGrading (projIdeal W)) _
      (mk_X_mem_quotientGrading_one W i) one_pos) g ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  have hy : y = default := Subsingleton.elim _ _
  subst hy
  have hrange : ((Proj.awayι (quotientGrading (projIdeal W)) _
      (mk_X_mem_quotientGrading_one W i) one_pos).opensRange :
      TopologicalSpace.Opens (projModel W)) =
      Proj.basicOpen (quotientGrading (projIdeal W))
        (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i)) :=
    Proj.opensRange_awayι _ _ _ _
  have : g.base default ∈ (Proj.awayι (quotientGrading (projIdeal W)) _
      (mk_X_mem_quotientGrading_one W i) one_pos).opensRange := by
    rw [hrange]
    exact hi
  exact this

/-- The chart of the model as a quotient of the chart of `ℙ²`. -/
noncomputable def chartQuotientEquiv (W : WeierstrassCurve R) (i : Fin 3) :
    (Away (MvPolynomial.homogeneousSubmodule (Fin 3) R) (MvPolynomial.X i) ⧸
      Ideal.span {HomogeneousLocalization.Away.mk
        (MvPolynomial.homogeneousSubmodule (Fin 3) R)
        (MvPolynomial.X_mem_homogeneousSubmodule_one R i) 3 W.toProjective.polynomial
        (by simp [projective_polynomial_isHomogeneous W])}) ≃+*
    Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) :=
  (Ideal.quotEquivOfEq (show Ideal.span _ =
      RingHom.ker (HomogeneousLocalization.Away.map (quotientGradingHom (projIdeal W))
        (MvPolynomial.X i)) from
    (ker_away_map_quotientGradingHom (projIdeal W)
      (projective_polynomial_isHomogeneous W) (projIdeal_toIdeal W)
      (MvPolynomial.X_mem_homogeneousSubmodule_one R i)).symm)).trans
    (RingHom.quotientKerEquivOfSurjective
      (away_map_quotientGradingHom_surjective (projIdeal W)
        (MvPolynomial.X_mem_homogeneousSubmodule_one R i)))

/-- The chart of the model as the plane coordinate ring modulo the dehomogenised
cubic. -/
noncomputable def chartCoordEquiv (W : WeierstrassCurve R) (i : Fin 3) :
    (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial}) ≃+*
    Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) :=
  ((Ideal.quotientEquiv
    (Ideal.span {HomogeneousLocalization.Away.mk
      (MvPolynomial.homogeneousSubmodule (Fin 3) R)
      (MvPolynomial.X_mem_homogeneousSubmodule_one R i) 3 W.toProjective.polynomial
      (by
        rw [smul_eq_mul, mul_one]
        exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (projective_polynomial_isHomogeneous W))})
    (Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
    ((MvPolynomial.chartRingEquiv R i) :
      Away (MvPolynomial.homogeneousSubmodule (Fin 3) R) (MvPolynomial.X i) ≃+*
        MvPolynomial {j : Fin 3 // j ≠ i} R)
    (by
      rw [Ideal.map_span, Set.image_singleton]
      congr 1
      rw [Set.singleton_eq_singleton_iff]
      symm
      show MvPolynomial.dehomogenizeAt R i _ = _
      rw [MvPolynomial.dehomogenizeAt_mk])).symm).trans (chartQuotientEquiv W i)

@[simp]
lemma chartCoordEquiv_mk (W : WeierstrassCurve R) (i : Fin 3)
    (p : MvPolynomial {j : Fin 3 // j ≠ i} R) :
    chartCoordEquiv W i (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial}) p) =
      HomogeneousLocalization.Away.map (quotientGradingHom (projIdeal W))
        (MvPolynomial.X i) (MvPolynomial.homogenizeAt R i p) := by
  unfold chartCoordEquiv
  rw [RingEquiv.trans_apply, Ideal.quotientEquiv_symm_mk]
  unfold chartQuotientEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ _

lemma chartCoordEquiv_mk_C (W : WeierstrassCurve R) (i : Fin 3) (r : R) :
    chartCoordEquiv W i (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
        (MvPolynomial.C r)) =
      (algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))))
        ((gradeZeroRingEquiv W) r) := by
  rw [chartCoordEquiv_mk]
  exact (RingHom.congr_fun (algebraMap_gradeZero_comp_eq W i) r).symm

lemma ringHom_eq_aeval {σ : Type} {K : Type u} [CommRing K] [Algebra R K]
    (χ : MvPolynomial σ R →+* K)
    (hχ : ∀ r, χ (MvPolynomial.C r) = algebraMap R K r)
    (p : MvPolynomial σ R) :
    χ p = MvPolynomial.aeval (fun j => χ (MvPolynomial.X j)) p := by
  have hχ' : ∀ r, χ (algebraMap R (MvPolynomial σ R) r) = algebraMap R K r := by
    intro r
    rw [MvPolynomial.algebraMap_eq]
    exact hχ r
  have h := MvPolynomial.aeval_unique (⟨χ, hχ'⟩ : MvPolynomial σ R →ₐ[R] K)
  calc χ p = (⟨χ, hχ'⟩ : MvPolynomial σ R →ₐ[R] K) p := rfl
    _ = _ := by rw [h]; rfl

lemma chart_hom_aeval (W : WeierstrassCurve R) (i : Fin 3) {K : Type u}
    [CommRing K] [Algebra R K]
    (φ : Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) →+* K)
    (hφ : φ.comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
      ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
      algebraMap R K)
    (p : MvPolynomial {j : Fin 3 // j ≠ i} R) :
    φ (chartCoordEquiv W i (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial}) p)) =
      MvPolynomial.aeval (fun j => φ (chartCoordEquiv W i (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
        (MvPolynomial.X j)))) p := by
  refine ringHom_eq_aeval (φ.comp (((chartCoordEquiv W i) :
    MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial} →+*
      Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))).comp
    (Ideal.Quotient.mk _))) (fun r => ?_) p
  show φ (chartCoordEquiv W i (Ideal.Quotient.mk _ (MvPolynomial.C r))) = _
  rw [chartCoordEquiv_mk_C]
  exact RingHom.congr_fun hφ r

private def ringHomPrecompEquiv {A B C : Type*} [Semiring A] [Semiring B]
    [Semiring C] (e : A ≃+* B) : (B →+* C) ≃ (A →+* C) where
  toFun φ := φ.comp (e : A →+* B)
  invFun ψ := ψ.comp (e.symm : B →+* A)
  left_inv φ := RingHom.ext fun x => by simp
  right_inv ψ := RingHom.ext fun x => by simp

/-- `R`-compatible ring homomorphisms out of `R[u,v]/(F̃)` are the `K`-solutions
of `F̃`. -/
private noncomputable def quotSolutionsEquiv {i : Fin 3}
    (F : MvPolynomial {j : Fin 3 // j ≠ i} R)
    (K : Type u) [CommRing K] [Algebra R K] :
    { ψ : (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸ Ideal.span {F}) →+* K //
      ∀ r, ψ (Ideal.Quotient.mk (Ideal.span {F}) (MvPolynomial.C r)) =
        algebraMap R K r } ≃
    { v : {j : Fin 3 // j ≠ i} → K // MvPolynomial.aeval v F = 0 } where
  toFun ψ := ⟨fun j => ψ.1 (Ideal.Quotient.mk _ (MvPolynomial.X j)), by
    have h0 := ringHom_eq_aeval (ψ.1.comp (Ideal.Quotient.mk (Ideal.span {F})))
      (fun r => ψ.2 r) F
    rw [show (ψ.1.comp (Ideal.Quotient.mk (Ideal.span {F}))) F =
      ψ.1 0 from congrArg ψ.1 (Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton_self _)), map_zero] at h0
    exact h0.symm⟩
  invFun v := ⟨Ideal.Quotient.lift (Ideal.span {F})
      ((MvPolynomial.aeval v.1 : MvPolynomial {j : Fin 3 // j ≠ i} R →ₐ[R] K) :
        MvPolynomial {j : Fin 3 // j ≠ i} R →+* K)
      (fun a ha => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
        simp only [RingHom.coe_coe, map_mul, v.2, zero_mul]), fun r => by
    rw [Ideal.Quotient.lift_mk]
    simp⟩
  left_inv ψ := by
    refine Subtype.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun p => ?_))
    simp only [RingHom.comp_apply, Ideal.Quotient.lift_mk]
    exact (ringHom_eq_aeval (ψ.1.comp (Ideal.Quotient.mk (Ideal.span {F})))
      (fun r => ψ.2 r) p).symm
  right_inv v := by
    refine Subtype.ext (funext fun j => ?_)
    simp only [Ideal.Quotient.lift_mk, RingHom.coe_coe, MvPolynomial.aeval_X]

/-- Ring homomorphisms from a chart of the model, compatible with the `R`-structure,
are the `K`-solutions of the dehomogenised cubic. -/
noncomputable def chartSolutionsEquiv (W : WeierstrassCurve R) (i : Fin 3)
    (K : Type u) [CommRing K] [Algebra R K] :
    { φ : Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
        algebraMap R K } ≃
    { v : {j : Fin 3 // j ≠ i} → K //
      MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial) = 0 } :=
  (Equiv.subtypeEquiv (ringHomPrecompEquiv (chartCoordEquiv W i)) (fun φ => by
    constructor
    · intro h r
      show φ (chartCoordEquiv W i _) = _
      rw [chartCoordEquiv_mk_C]
      exact RingHom.congr_fun h r
    · intro h
      refine RingHom.ext fun r => ?_
      have := h r
      rw [show (ringHomPrecompEquiv (chartCoordEquiv W i) φ)
          (Ideal.Quotient.mk _ (MvPolynomial.C r)) =
          φ (chartCoordEquiv W i (Ideal.Quotient.mk _ (MvPolynomial.C r))) from rfl,
        chartCoordEquiv_mk_C] at this
      exact this)).trans
    (quotSolutionsEquiv (MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial) K)

/-- Restricted to a chart, the structure morphism of the model is `Spec` of the
`R`-structuring of the chart ring. -/
lemma awayι_projModelπ (W : WeierstrassCurve R) (i : Fin 3) :
    Proj.awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))
      (mk_X_mem_quotientGrading_one W i) one_pos ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0)))) := by
  show Proj.awayι _ _ _ _ ≫ Proj.toSpecZero (quotientGrading (projIdeal W)) ≫
    Spec.map (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W))) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The `K`-point of the model attached to an `R`-compatible ring homomorphism out
of the chart ring at `i`. -/
private noncomputable def chartPointOfHom (W : WeierstrassCurve R) (i : Fin 3)
    {K : Type u} [CommRing K] [Algebra R K]
    (φ : { φ : Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
        algebraMap R K }) :
    { g : SpecPoints (projModel W) (projModelπ W) K //
      ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))),
        h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W i) one_pos = g.1 } :=
  ⟨⟨Spec.map (CommRingCat.ofHom φ.1) ≫ Proj.awayι _ _
      (mk_X_mem_quotientGrading_one W i) one_pos, by
    rw [Category.assoc, awayι_projModelπ W i, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, φ.2]⟩, ⟨Spec.map (CommRingCat.ofHom φ.1), rfl⟩⟩

private lemma chartPointOfHom_bijective (W : WeierstrassCurve R) (i : Fin 3)
    {K : Type u} [CommRing K] [Algebra R K] :
    Function.Bijective (chartPointOfHom W i (K := K)) := by
  constructor
  · intro φ₁ φ₂ h
    have h1 : Spec.map (CommRingCat.ofHom φ₁.1) ≫ Proj.awayι _ _
        (mk_X_mem_quotientGrading_one W i) one_pos =
        Spec.map (CommRingCat.ofHom φ₂.1) ≫ Proj.awayι _ _
          (mk_X_mem_quotientGrading_one W i) one_pos :=
      congrArg (fun g => g.1.1) h
    have h2 := Spec.map_injective ((cancel_mono _).mp h1)
    exact Subtype.ext (congrArg CommRingCat.Hom.hom h2)
  · rintro ⟨⟨g, hg⟩, h, hfac⟩
    have hπ : (h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W i) one_pos) ≫ projModelπ W =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      rw [hfac]
      exact hg
    rw [Category.assoc, awayι_projModelπ W i, ← Spec.map_preimage h,
      ← Spec.map_comp] at hπ
    have hcond := congrArg CommRingCat.Hom.hom (Spec.map_injective hπ)
    refine ⟨⟨(Spec.preimage h).hom, hcond⟩, ?_⟩
    refine Subtype.ext (Subtype.ext ?_)
    show Spec.map (CommRingCat.ofHom (Spec.preimage h).hom) ≫ _ = g
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact hfac

/-- `K`-points of the model that factor through chart `i` are the `R`-compatible
ring homomorphisms out of the chart ring. -/
noncomputable def chartHomEquiv (W : WeierstrassCurve R) (i : Fin 3)
    (K : Type u) [CommRing K] [Algebra R K] :
    { g : SpecPoints (projModel W) (projModelπ W) K //
      ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))),
        h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W i) one_pos = g.1 } ≃
    { φ : Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
        algebraMap R K } :=
  (Equiv.ofBijective _ (chartPointOfHom_bijective W i (K := K))).symm

/-- Value-characterisation of `chartHomEquiv`: a chart-factoring point that IS `Spec.map φ`
followed by the chart immersion reads out as `φ`. Public wrapper around the private
`chartPointOfHom` (the equiv's inverse). -/
lemma chartHomEquiv_eq_of_specMap (W : WeierstrassCurve R) (i : Fin 3)
    {K : Type u} [CommRing K] [Algebra R K]
    (g : { g : SpecPoints (projModel W) (projModelπ W) K //
      ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))),
        h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W i) one_pos = g.1 })
    (φ : { φ : Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
        algebraMap R K })
    (hfac : Spec.map (CommRingCat.ofHom φ.1) ≫ Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W i) one_pos = g.1.1) :
    chartHomEquiv W i K g = φ := by
  have hpt : chartPointOfHom W i φ = g := Subtype.ext (Subtype.ext hfac)
  rw [chartHomEquiv, ← hpt]
  exact (Equiv.ofBijective _ (chartPointOfHom_bijective W i (K := K))).symm_apply_apply φ


/-- The chart coordinate `Xⱼ/Xᵢ` is mathlib's localization element for the pair
`(Xᵢ, Xⱼ)`. -/
lemma chartCoordEquiv_mk_X (W : WeierstrassCurve R) (i : Fin 3)
    (j : {j : Fin 3 // j ≠ i}) :
    chartCoordEquiv W i (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
        (MvPolynomial.X j)) =
      HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W i) (mk_X_mem_quotientGrading_one W j.1) := by
  rw [chartCoordEquiv_mk]
  rw [show MvPolynomial.homogenizeAt R i (MvPolynomial.X j) =
    MvPolynomial.awayVar R i j from MvPolynomial.eval₂Hom_X' _ _ _]
  apply val_injective
  rw [MvPolynomial.awayVar, Away.map_mk, Away.val_mk, Away.val_mk]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by ring⟩

set_option backward.isDefEq.respectTransparency false in
/-- A `K`-point of the model sitting in chart `i` lies in chart `j` precisely when
its `j`-th coordinate is nonzero. -/
lemma chartPointOfHom_factors_iff (W : WeierstrassCurve R) (i j : Fin 3)
    {K : Type u} [Field K] [Algebra R K]
    (φ : { φ : Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
        algebraMap R K }) :
    (∃ h' : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)))),
      h' ≫ Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W j) one_pos = (chartPointOfHom W i φ).1.1) ↔
      φ.1 (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W i) (mk_X_mem_quotientGrading_one W j)) ≠ 0 := by
  have hbase : (chartPointOfHom W i φ).1.1 default =
      (Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))
        (mk_X_mem_quotientGrading_one W i) one_pos)
        ((Spec.map (CommRingCat.ofHom φ.1)) default) := by
    show (Spec.map (CommRingCat.ofHom φ.1) ≫ Proj.awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))
      (mk_X_mem_quotientGrading_one W i) one_pos) default = _
    exact Scheme.Hom.comp_apply _ _ _
  have hmem : (chartPointOfHom W i φ).1.1 default ∈
      (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)) :
        Set (Proj (quotientGrading (projIdeal W)))) ↔
      φ.1 (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W i) (mk_X_mem_quotientGrading_one W j)) ≠ 0 := by
    rw [hbase]
    show (Spec.map (CommRingCat.ofHom φ.1)) default ∈
      (Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))
        (mk_X_mem_quotientGrading_one W i) one_pos ⁻¹ᵁ
        Proj.basicOpen (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))) ↔ _
    rw [Proj.awayι_preimage_basicOpen (quotientGrading (projIdeal W))
      (mk_X_mem_quotientGrading_one W i) one_pos
      (mk_X_mem_quotientGrading_one W j) one_pos]
    have hpt := Spec.map_apply (CommRingCat.ofHom φ.1) default
    rw [CommRingCat.hom_ofHom] at hpt
    rw [hpt]
    have hprime : ∀ x : PrimeSpectrum K, x.asIdeal = ⊥ := fun x =>
      (IsSimpleOrder.eq_bot_or_eq_top x.asIdeal).resolve_right x.2.ne_top
    constructor
    · intro hm h0
      refine (PrimeSpectrum.mem_basicOpen _ _).mp hm ?_
      show _ ∈ (PrimeSpectrum.comap φ.1 _).asIdeal
      rw [PrimeSpectrum.comap_asIdeal, hprime, Ideal.mem_comap, Ideal.mem_bot]
      exact h0
    · intro hne
      refine (PrimeSpectrum.mem_basicOpen _ _).mpr fun hm => hne ?_
      rw [show (PrimeSpectrum.comap φ.1 _).asIdeal =
        Ideal.comap φ.1 (PrimeSpectrum.asIdeal _) from PrimeSpectrum.comap_asIdeal ..,
        hprime, Ideal.mem_comap, Ideal.mem_bot] at hm
      exact hm
  constructor
  · rintro ⟨h', hfac⟩
    refine hmem.mp ?_
    have h1 : (chartPointOfHom W i φ).1.1 default =
        (Proj.awayι (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
          (mk_X_mem_quotientGrading_one W j) one_pos) (h' default) := by
      rw [← hfac]
      show (h' ≫ Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
        (mk_X_mem_quotientGrading_one W j) one_pos) default = _
      exact Scheme.Hom.comp_apply _ _ _
    rw [h1]
    have h2 : (Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
        (mk_X_mem_quotientGrading_one W j) one_pos) (h' default) ∈
        (Proj.awayι (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
          (mk_X_mem_quotientGrading_one W j) one_pos).opensRange :=
      Scheme.Hom.mem_opensRange.mpr ⟨h' default, rfl⟩
    rwa [Proj.opensRange_awayι] at h2
  · intro hne
    have hrange : Set.range ⇑(chartPointOfHom W i φ).1.1 ⊆
        Set.range ⇑(Proj.awayι (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
          (mk_X_mem_quotientGrading_one W j) one_pos) := by
      rw [show Set.range ⇑(Proj.awayι (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
          (mk_X_mem_quotientGrading_one W j) one_pos) =
          (Proj.basicOpen (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)) :
            Set (Proj (quotientGrading (projIdeal W)))) from by
        rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]]
      rw [show Set.range ⇑(chartPointOfHom W i φ).1.1 =
        {(chartPointOfHom W i φ).1.1 default} from Set.range_unique]
      rw [Set.singleton_subset_iff]
      exact hmem.mpr hne
    exact ⟨IsOpenImmersion.lift _ _ hrange, IsOpenImmersion.lift_fac _ _ hrange⟩

private lemma aeval_dehomog_two (W : WeierstrassCurve R) {K : Type u} [CommRing K]
    [Algebra R K] (v : {j : Fin 3 // j ≠ 2} → K) :
    MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial) =
      v ⟨1, by decide⟩ ^ 2 + algebraMap R K W.a₁ * v ⟨0, by decide⟩ * v ⟨1, by decide⟩
        + algebraMap R K W.a₃ * v ⟨1, by decide⟩
        - (v ⟨0, by decide⟩ ^ 3 + algebraMap R K W.a₂ * v ⟨0, by decide⟩ ^ 2
          + algebraMap R K W.a₄ * v ⟨0, by decide⟩ + algebraMap R K W.a₆) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 2 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 2 by decide),
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, mul_one, one_pow]

/-- Functions on the two non-`Z` indices are pairs. -/
private def zCoordsEquiv (K : Type u) : ({j : Fin 3 // j ≠ 2} → K) ≃ K × K where
  toFun v := (v ⟨0, by decide⟩, v ⟨1, by decide⟩)
  invFun p j := if j.1 = 0 then p.1 else p.2
  left_inv v := by
    refine funext fun j => ?_
    rcases j with ⟨j, hj⟩
    fin_cases j
    · simp
    · simp
    · exact absurd rfl hj
  right_inv p := by
    refine Prod.ext ?_ ?_
    · simp
    · simp

/-- `Z`-chart solutions are affine Weierstrass points. -/
private noncomputable def zSolutionsToAffine (W : WeierstrassCurve R)
    (K : Type u) [Field K] [Algebra R K] :
    { v : {j : Fin 3 // j ≠ 2} → K //
      MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial) = 0 } ≃
    { p : K × K // (W.baseChange K).toAffine.Equation p.1 p.2 } :=
  Equiv.subtypeEquiv (zCoordsEquiv K) (fun v => by
    rw [aeval_dehomog_two, WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆, zCoordsEquiv, Equiv.coe_fn_mk]
    constructor
    · intro h
      linear_combination h
    · intro h
      linear_combination h)

/-- The affine points of an elliptic curve over a field split as the equation's
solutions plus the point at infinity. -/
private noncomputable def affinePointSplit (W : WeierstrassCurve R)
    (hell : W.IsElliptic) (K : Type u) [Field K] [Algebra R K] :
    (W.baseChange K).toAffine.Point ≃
      { p : K × K // (W.baseChange K).toAffine.Equation p.1 p.2 } ⊕ PUnit.{u + 1} where
  toFun P := match P with
    | .zero => Sum.inr PUnit.unit
    | .some x y h => Sum.inl ⟨(x, y), h.1⟩
  invFun s := match s with
    | .inl p => .some p.1.1 p.1.2 (by
        haveI := hell
        haveI : ((W.baseChange K).toAffine).IsElliptic :=
          inferInstanceAs ((W.map (algebraMap R K)).IsElliptic)
        exact WeierstrassCurve.Affine.equation_iff_nonsingular.mp p.2)
    | .inr _ => .zero
  left_inv P := by cases P <;> rfl
  right_inv s := by rcases s with p | u <;> rfl

/-- Evaluation of the `Y`-chart cubic: `Z + a₁UZ + a₃Z² − (U³ + a₂U²Z + a₄UZ² + a₆Z³)`
in the coordinates `U = X/Y`, `Z = Z/Y`. -/
private lemma aeval_dehomog_one (W : WeierstrassCurve R) {K : Type u} [CommRing K]
    [Algebra R K] (v : {j : Fin 3 // j ≠ 1} → K) :
    MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial) =
      v ⟨2, by decide⟩ + algebraMap R K W.a₁ * v ⟨0, by decide⟩ * v ⟨2, by decide⟩
        + algebraMap R K W.a₃ * v ⟨2, by decide⟩ ^ 2
        - (v ⟨0, by decide⟩ ^ 3
          + algebraMap R K W.a₂ * v ⟨0, by decide⟩ ^ 2 * v ⟨2, by decide⟩
          + algebraMap R K W.a₄ * v ⟨0, by decide⟩ * v ⟨2, by decide⟩ ^ 2
          + algebraMap R K W.a₆ * v ⟨2, by decide⟩ ^ 3) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 1 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (2 : Fin 3) ≠ 1 by decide),
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, mul_one, one_pow, one_mul]

/-- Evaluation of the `X`-chart cubic. Its constant term is `-1`, so no point of the
`X`-chart has vanishing `Z`-coordinate. -/
private lemma aeval_dehomog_zero (W : WeierstrassCurve R) {K : Type u} [CommRing K]
    [Algebra R K] (v : {j : Fin 3 // j ≠ 0} → K) :
    MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial) =
      v ⟨1, by decide⟩ ^ 2 * v ⟨2, by decide⟩
        + algebraMap R K W.a₁ * v ⟨1, by decide⟩ * v ⟨2, by decide⟩
        + algebraMap R K W.a₃ * v ⟨1, by decide⟩ * v ⟨2, by decide⟩ ^ 2
        - (1 + algebraMap R K W.a₂ * v ⟨2, by decide⟩
          + algebraMap R K W.a₄ * v ⟨2, by decide⟩ ^ 2
          + algebraMap R K W.a₆ * v ⟨2, by decide⟩ ^ 3) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 0 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (2 : Fin 3) ≠ 0 by decide),
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_one, mul_one, one_pow]

/-- The `K`-point at infinity `[0:1:0]`, presented as the `Y`-chart point with
coordinates `(U, Z) = (0, 0)`. -/
private noncomputable def infPoint (W : WeierstrassCurve R) (K : Type u) [Field K]
    [Algebra R K] : SpecPoints (projModel W) (projModelπ W) K :=
  (chartPointOfHom W 1 ((chartSolutionsEquiv W 1 K).symm ⟨fun _ => 0, by
    rw [aeval_dehomog_one]
    simp⟩)).1

private lemma infPoint_not_inZ (W : WeierstrassCurve R) (K : Type u) [Field K]
    [Algebra R K] :
    ¬ ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))),
      h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W 2) one_pos = (infPoint W K).1 := by
  intro hfac
  have hne := (chartPointOfHom_factors_iff W 1 2 _).mp hfac
  apply hne
  rw [← chartCoordEquiv_mk_X W 1 ⟨2, by decide⟩]
  have hv : ((chartSolutionsEquiv W 1 K)
      ((chartSolutionsEquiv W 1 K).symm ⟨fun _ => 0, by
        rw [aeval_dehomog_one]; simp⟩)).1 ⟨2, by decide⟩ = 0 := by
    rw [Equiv.apply_symm_apply]
  exact hv

private lemma eq_infPoint_of_not_inZ (W : WeierstrassCurve R) (K : Type u) [Field K]
    [Algebra R K] (g : SpecPoints (projModel W) (projModelπ W) K)
    (hg : ¬ ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))),
      h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W 2) one_pos = g.1) :
    g = infPoint W K := by
  obtain ⟨i, h, hfac⟩ := specPoint_factors_through_chart W g.1
  obtain ⟨φ, hφ⟩ := (chartPointOfHom_bijective W i (K := K)).2 ⟨g, ⟨h, hfac⟩⟩
  have gproj : (chartPointOfHom W i φ).1 = g := congrArg Subtype.val hφ
  rw [← gproj] at hg
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases hi with rfl | rfl | rfl
  · -- the X-chart: impossible, the cubic has constant term -1 there
    exfalso
    have hz : φ.1 (chartCoordEquiv W 0 (Ideal.Quotient.mk _
        (MvPolynomial.X (⟨2, by decide⟩ : {j : Fin 3 // j ≠ 0})))) = 0 := by
      rw [chartCoordEquiv_mk_X W 0 ⟨2, by decide⟩]
      by_contra hne
      exact hg ((chartPointOfHom_factors_iff W 0 2 φ).mpr hne)
    have hv := ((chartSolutionsEquiv W 0 K) φ).2
    have hcomp : ((chartSolutionsEquiv W 0 K) φ).1 =
        fun j : {j : Fin 3 // j ≠ 0} => φ.1 (chartCoordEquiv W 0
          (Ideal.Quotient.mk _ (MvPolynomial.X j))) := rfl
    rw [hcomp, aeval_dehomog_zero] at hv
    simp only [hz, mul_zero, add_zero, zero_add] at hv
    simp at hv
  · -- the Y-chart: the coordinates are forced to (0,0), the point at infinity
    have hz : φ.1 (chartCoordEquiv W 1 (Ideal.Quotient.mk _
        (MvPolynomial.X (⟨2, by decide⟩ : {j : Fin 3 // j ≠ 1})))) = 0 := by
      rw [chartCoordEquiv_mk_X W 1 ⟨2, by decide⟩]
      by_contra hne
      exact hg ((chartPointOfHom_factors_iff W 1 2 φ).mpr hne)
    have hv := ((chartSolutionsEquiv W 1 K) φ).2
    have hcomp : ((chartSolutionsEquiv W 1 K) φ).1 =
        fun j : {j : Fin 3 // j ≠ 1} => φ.1 (chartCoordEquiv W 1
          (Ideal.Quotient.mk _ (MvPolynomial.X j))) := rfl
    rw [hcomp, aeval_dehomog_one, hz] at hv
    have hv3 : φ.1 (chartCoordEquiv W 1 (Ideal.Quotient.mk _
        (MvPolynomial.X (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 1})))) ^ 3 = 0 := by
      linear_combination -hv
    have hu : φ.1 (chartCoordEquiv W 1 (Ideal.Quotient.mk _
        (MvPolynomial.X (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 1})))) = 0 :=
      pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp hv3
    have hsol : (chartSolutionsEquiv W 1 K) φ = ⟨fun _ => 0, by
        rw [aeval_dehomog_one]; simp⟩ := by
      refine Subtype.ext ?_
      rw [hcomp]
      funext j
      rcases j with ⟨j, hj⟩
      fin_cases j
      · exact hu
      · exact absurd rfl hj
      · exact hz
    have hφ0 : φ = (chartSolutionsEquiv W 1 K).symm ⟨fun _ => 0, by
        rw [aeval_dehomog_one]; simp⟩ := by
      rw [← hsol, Equiv.symm_apply_apply]
    rw [← gproj, infPoint, hφ0]
  · -- the Z-chart: contradicts the hypothesis
    exact absurd ⟨Spec.map (CommRingCat.ofHom φ.1), rfl⟩ hg

set_option backward.isDefEq.respectTransparency false in
/-- **(T-A2e)** The pointed `K`-points clause for elliptic `W`: `K`-points of the model
biject with `(W.baseChange K).toAffine.Point`, sending `[0:1:0]` to `0`.
Route: every `Spec K`-point factors through one of the three affine charts (`K` is
local and the `D₊(mk Xᵢ)` cover); chart points are dehomogenised-cubic solutions via
`chartRingEquiv` + `ker_away_map_quotientGradingHom`; the `Z`-chart dichotomy
(`v` unit or `v = 0 ⟹ [0:1:0]`) matches `Affine.Point`'s `some`/`zero`. -/
theorem projModel_points (W : WeierstrassCurve R) (hell : W.IsElliptic)
    (K : Type u) [Field K] [Algebra R K] :
    ∃ e : SpecPoints (projModel W) (projModelπ W) K ≃ (W.baseChange K).toAffine.Point,
      e ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ projModelZero W, by
        rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]⟩ = 0 := by
  classical
  let EZ : { g : SpecPoints (projModel W) (projModelπ W) K //
      ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))),
        h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W 2) one_pos = g.1 } ≃
      { p : K × K // (W.baseChange K).toAffine.Equation p.1 p.2 } :=
    (chartHomEquiv W 2 K).trans ((chartSolutionsEquiv W 2 K).trans
      (zSolutionsToAffine W K))
  let EB : { g : SpecPoints (projModel W) (projModelπ W) K //
      ¬ ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))),
        h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W 2) one_pos = g.1 } ≃ PUnit.{u + 1} :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ⟨infPoint W K, infPoint_not_inZ W K⟩
      left_inv := fun g => Subtype.ext (eq_infPoint_of_not_inZ W K g.1 g.2).symm
      right_inv := fun _ => rfl }
  let e0 : SpecPoints (projModel W) (projModelπ W) K ≃
      (W.baseChange K).toAffine.Point :=
    (Equiv.sumCompl _).symm.trans ((EZ.sumCongr EB).trans
      (affinePointSplit W hell K).symm)
  refine ⟨e0.trans (Equiv.swap (e0 ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
    projModelZero W, by
      rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]⟩) 0), ?_⟩
  rw [Equiv.trans_apply, Equiv.swap_apply_left]

/-! ### T-W7.0f-val: the explicit field-points equivalence and its chartwise values

`projModel_points` above is choice-extracted by its consumers, so it pins no values. Here we
expose the *explicit* bijection `projModelPointsEquivEll` — the same assembly minus the
normalising `swap` (the zero point already lands on `0`, since it lies off the `Z`-chart) — and
prove its values: the zero point `[0:1:0] ↦ 0`, a `Z`-chart point with dehomogenised coordinates
`(x, y) ↦ some x y`, and every off-`Z`-chart point `↦ 0`. The negation/multiplication
specifications (`negModelHom_specPoints`, `mulModelHom_specPoints`) and the group axioms read the
coordinates through these. -/

/-- A `K`-point of the projective model factors through the `Z = X₂`-chart. -/
abbrev InZChart (W : WeierstrassCurve R) {K : Type u} [CommRing K] [Algebra R K]
    (g : SpecPoints (projModel W) (projModelπ W) K) : Prop :=
  ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))),
    h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
      (mk_X_mem_quotientGrading_one W 2) one_pos = g.1

/-- The zero section avoids the `Z`-chart: `X₂` evaluates to `0` at `[0:1:0]`, so the preimage of
the `Z`-chart basic open is empty. (Analogue of `projModelZero_preimage_yChart`, with `1 ↦ 0`.) -/
lemma projModelZero_not_preimage_zChart (W : WeierstrassCurve R) :
    projModelZero W ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) = ⊥ := by
  unfold projModelZero
  rw [Proj.fromOfGlobalSections_preimage_basicOpen (hn := one_pos)
    (hr := mk_X_mem_quotientGrading_one W 2)]
  rw [show ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
      (projModelZeroEval W)) ((quotientGradingHom (projIdeal W))
        (MvPolynomial.X 2)) = 0 from by
    rw [RingHom.comp_apply]
    rw [show (projModelZeroEval W) ((quotientGradingHom (projIdeal W))
        (MvPolynomial.X 2)) = 0 from by
      show (projModelZeroEval W) (Ideal.Quotient.mk _ (MvPolynomial.X 2)) = 0
      rw [projModelZeroEval_mk]
      simp]
    rw [map_zero]]
  simp

/-- The zero `K`-point `[0:1:0]` does not factor through the `Z`-chart. -/
lemma projModelZero_not_inZ (W : WeierstrassCurve R) (K : Type u) [Field K] [Algebra R K] :
    ¬ InZChart W (K := K)
      ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ projModelZero W, by
        rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]⟩ := by
  rintro ⟨h, hfac⟩
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ projModelZero W) default =
      (Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos) (h default) := by
    have hc := congrArg (fun m => m default) hfac.symm
    rw [Scheme.Hom.comp_apply] at hc
    exact hc
  have hin : (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ projModelZero W) default ∈
      Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) := by
    have h2 : (Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos) (h default) ∈
        (Proj.awayι (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W 2) one_pos).opensRange :=
      Scheme.Hom.mem_opensRange.mpr ⟨h default, rfl⟩
    rw [Proj.opensRange_awayι] at h2
    rw [h1]
    exact h2
  rw [Scheme.Hom.comp_apply] at hin
  have hpre : Spec.map (CommRingCat.ofHom (algebraMap R K)) default ∈
      (projModelZero W ⁻¹ᵁ Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) := hin
  rw [projModelZero_not_preimage_zChart] at hpre
  simp at hpre

/-- Membership of the `Z`-chart for a point presented on chart `i`: exactly when the transition
coordinate `X₂/Xᵢ` has nonzero value. Public wrapper of `chartPointOfHom_factors_iff` at `j = 2`,
restated against an explicit factoring. -/
lemma inZChart_iff_of_specMap (W : WeierstrassCurve R) (i : Fin 3)
    {K : Type u} [Field K] [Algebra R K]
    (φ : { φ : Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
        algebraMap R K })
    (g : SpecPoints (projModel W) (projModelπ W) K)
    (hg : Spec.map (CommRingCat.ofHom φ.1) ≫ Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W i) one_pos = g.1) :
    InZChart W g ↔
      φ.1 (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W i) (mk_X_mem_quotientGrading_one W 2)) ≠ 0 := by
  have hpt : chartPointOfHom W i φ = ⟨g, ⟨Spec.map (CommRingCat.ofHom φ.1), hg⟩⟩ :=
    Subtype.ext (Subtype.ext hg)
  have hiff := chartPointOfHom_factors_iff W i 2 φ
  rw [hpt] at hiff
  exact hiff

/-- **(T-W7.1b input)** The `Spec K`-point dichotomy, public form: a `K`-point of the model
that does not factor through the `Z`-chart IS the zero section point (both equal the
canonical infinity point). -/

lemma specPoint_eq_zero_of_not_inZ (W : WeierstrassCurve R) (K : Type u) [Field K]
    [Algebra R K] (g : SpecPoints (projModel W) (projModelπ W) K)
    (hg : ¬ InZChart W g) :
    g.1 = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ projModelZero W := by
  have h1 := eq_infPoint_of_not_inZ W K g hg
  have h2 := eq_infPoint_of_not_inZ W K
    ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ projModelZero W, by
      rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]⟩
    (projModelZero_not_inZ W K)
  have := h1.trans h2.symm
  exact congrArg Subtype.val this

open Classical in
/-- The **explicit** field-points bijection for elliptic `W`: `K`-points of the projective model
correspond to affine Weierstrass points — `Z`-chart points via their dehomogenised coordinates,
the single off-chart point to `[0:1:0] = O`. Unlike `projModel_points`'s choice-extracted
equivalence, this one has computable values (`_zero`, `_some`, `_infinity` below). -/
noncomputable def projModelPointsEquivEll (W : WeierstrassCurve R) (hell : W.IsElliptic)
    (K : Type u) [Field K] [Algebra R K] :
    SpecPoints (projModel W) (projModelπ W) K ≃ (W.baseChange K).toAffine.Point :=
  (Equiv.sumCompl (InZChart W (K := K))).symm.trans
    ((((chartHomEquiv W 2 K).trans ((chartSolutionsEquiv W 2 K).trans
        (zSolutionsToAffine W K))).sumCongr
      ({ toFun := fun _ => PUnit.unit
         invFun := fun _ => ⟨infPoint W K, infPoint_not_inZ W K⟩
         left_inv := fun g => Subtype.ext (eq_infPoint_of_not_inZ W K g.1 g.2).symm
         right_inv := fun _ => rfl } :
        { g : SpecPoints (projModel W) (projModelπ W) K // ¬ InZChart W g } ≃
          PUnit.{u + 1})).trans
      (affinePointSplit W hell K).symm)

/-- Value of the explicit equivalence on an off-`Z`-chart point: the point at infinity `0`. -/
lemma projModelPointsEquivEll_infinity (W : WeierstrassCurve R) (hell : W.IsElliptic)
    (K : Type u) [Field K] [Algebra R K]
    (g : SpecPoints (projModel W) (projModelπ W) K) (hg : ¬ InZChart W g) :
    projModelPointsEquivEll W hell K g = 0 := by
  classical
  unfold projModelPointsEquivEll
  simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hg, Equiv.sumCongr_apply,
    Sum.map_inr]
  rfl

/-- Value of the explicit equivalence at the zero point `[0:1:0]`: the group identity `0`. -/
lemma projModelPointsEquivEll_zero (W : WeierstrassCurve R) (hell : W.IsElliptic)
    (K : Type u) [Field K] [Algebra R K] :
    projModelPointsEquivEll W hell K
      ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ projModelZero W, by
        rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]⟩ = 0 :=
  projModelPointsEquivEll_infinity W hell K _ (projModelZero_not_inZ W K)

/-- Value of the explicit equivalence on a `Z`-chart point: the affine point whose coordinates are
the dehomogenised `Z`-chart solution `(X₀/X₂, X₁/X₂)`. Stated with the coordinates and their
nonsingularity as hypotheses so consumers can supply their own (proof-irrelevant) witness. -/
lemma projModelPointsEquivEll_some (W : WeierstrassCurve R) (hell : W.IsElliptic)
    (K : Type u) [Field K] [Algebra R K]
    (g : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W g)
    (x y : K) (hxy : (W.baseChange K).toAffine.Nonsingular x y)
    (hx : x = (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 ⟨0, by decide⟩)
    (hy : y = (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 ⟨1, by decide⟩) :
    projModelPointsEquivEll W hell K g = WeierstrassCurve.Affine.Point.some x y hxy := by
  classical
  subst hx hy
  unfold projModelPointsEquivEll
  simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hZ, Equiv.sumCongr_apply,
    Sum.map_inl]
  rfl

private lemma aeval_pderiv_dehomog_two_u (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 2} → K) :
    MvPolynomial.aeval v (MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial)) =
      algebraMap R K W.a₁ * v ⟨1, by decide⟩ - (3 * v ⟨0, by decide⟩ ^ 2
        + 2 * algebraMap R K W.a₂ * v ⟨0, by decide⟩ + algebraMap R K W.a₄) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 2 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 2 by decide),
    mul_one, one_pow]
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (show (⟨1, by decide⟩ : {j : Fin 3 // j ≠ 2}) ≠
      ⟨0, by decide⟩ by simp), map_add]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, map_zero, map_one, map_natCast]
  ring

private lemma aeval_pderiv_dehomog_two_v (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 2} → K) :
    MvPolynomial.aeval v (MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial)) =
      2 * v ⟨1, by decide⟩ + algebraMap R K W.a₁ * v ⟨0, by decide⟩
        + algebraMap R K W.a₃ := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 2 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 2 by decide),
    mul_one, one_pow]
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (show (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 2}) ≠
      ⟨1, by decide⟩ by simp), map_add]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, map_zero, map_one, map_natCast]
  ring

/-- **(T-A3a)** Certificate-free Weierstrass Jacobian comaximality: for elliptic `W`,
the dehomogenised cubic and its two partials generate the unit ideal. A maximal ideal
above them would give a singular point of an elliptic curve over its residue field,
contradicting `equation_iff_nonsingular`. -/
theorem span_dehomog_jacobian_eq_top (W : WeierstrassCurve R) [W.IsElliptic] :
    Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial)} = ⊤ := by
  by_contra hne
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ hne
  letI : Field (MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸ m) := Ideal.Quotient.field m
  set q : MvPolynomial {j : Fin 3 // j ≠ 2} R →+*
      MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸ m := Ideal.Quotient.mk m with hq
  letI : Algebra R (MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸ m) :=
    (q.comp (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ 2} R))).toAlgebra
  have haev : ∀ p : MvPolynomial {j : Fin 3 // j ≠ 2} R,
      q p = MvPolynomial.aeval (fun j => q (MvPolynomial.X j)) p :=
    ringHom_eq_aeval q (fun r => rfl)
  set f : R →+* MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸ m :=
    q.comp (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ 2} R)) with hf
  have halg : algebraMap R (MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸ m) = f := rfl
  have hmem : ∀ p ∈ ({MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial)} :
      Set (MvPolynomial {j : Fin 3 // j ≠ 2} R)), q p = 0 := by
    intro p hp
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span hp))
  have h1 : (W.map f).toAffine.Equation (q (MvPolynomial.X ⟨0, by decide⟩))
      (q (MvPolynomial.X ⟨1, by decide⟩)) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    have hF := hmem _ (Set.mem_insert _ _)
    rw [haev, aeval_dehomog_two] at hF
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    linear_combination hF
  have h2 : ¬ (W.map f).toAffine.Nonsingular (q (MvPolynomial.X ⟨0, by decide⟩))
      (q (MvPolynomial.X ⟨1, by decide⟩)) := by
    rw [WeierstrassCurve.Affine.nonsingular_iff']
    rintro ⟨-, hu | hv⟩
    · apply hu
      have hFu := hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      rw [haev, aeval_pderiv_dehomog_two_u] at hFu
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
        WeierstrassCurve.map_a₄]
      linear_combination hFu
    · apply hv
      have hFv := hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
      rw [haev, aeval_pderiv_dehomog_two_v] at hFv
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
      linear_combination hFv
  haveI : ((W.map f).toAffine).IsElliptic := inferInstanceAs ((W.map f).IsElliptic)
  exact h2 (WeierstrassCurve.Affine.equation_iff_nonsingular.mp h1)

private lemma aeval_pderiv_dehomog_one_u (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 1} → K) :
    MvPolynomial.aeval v (MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial)) =
      algebraMap R K W.a₁ * v ⟨2, by decide⟩ - (3 * v ⟨0, by decide⟩ ^ 2
        + 2 * algebraMap R K W.a₂ * v ⟨0, by decide⟩ * v ⟨2, by decide⟩
        + algebraMap R K W.a₄ * v ⟨2, by decide⟩ ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 1 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (2 : Fin 3) ≠ 1 by decide),
    mul_one, one_pow, one_mul]
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (show (⟨2, by decide⟩ : {j : Fin 3 // j ≠ 1}) ≠
      ⟨0, by decide⟩ by simp), map_add]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, map_zero, map_one, map_natCast]
  ring

private lemma aeval_pderiv_dehomog_one_w (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 1} → K) :
    MvPolynomial.aeval v (MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial)) =
      1 + algebraMap R K W.a₁ * v ⟨0, by decide⟩
        + 2 * algebraMap R K W.a₃ * v ⟨2, by decide⟩
        - (algebraMap R K W.a₂ * v ⟨0, by decide⟩ ^ 2
          + 2 * algebraMap R K W.a₄ * v ⟨0, by decide⟩ * v ⟨2, by decide⟩
          + 3 * algebraMap R K W.a₆ * v ⟨2, by decide⟩ ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 1 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (2 : Fin 3) ≠ 1 by decide),
    mul_one, one_pow, one_mul]
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (show (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 1}) ≠
      ⟨2, by decide⟩ by simp), map_add]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, map_zero, map_one, map_natCast]
  ring

private lemma aeval_pderiv_dehomog_zero_s (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 0} → K) :
    MvPolynomial.aeval v (MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial)) =
      2 * v ⟨1, by decide⟩ * v ⟨2, by decide⟩
        + algebraMap R K W.a₁ * v ⟨2, by decide⟩
        + algebraMap R K W.a₃ * v ⟨2, by decide⟩ ^ 2 := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 0 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (2 : Fin 3) ≠ 0 by decide),
    mul_one, one_pow]
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (show (⟨2, by decide⟩ : {j : Fin 3 // j ≠ 0}) ≠
      ⟨1, by decide⟩ by simp), map_add, Derivation.map_one_eq_zero]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, map_zero, map_one, map_natCast]
  ring

private lemma aeval_pderiv_dehomog_zero_t (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 0} → K) :
    MvPolynomial.aeval v (MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial)) =
      v ⟨1, by decide⟩ ^ 2 + algebraMap R K W.a₁ * v ⟨1, by decide⟩
        + 2 * algebraMap R K W.a₃ * v ⟨1, by decide⟩ * v ⟨2, by decide⟩
        - (algebraMap R K W.a₂ + 2 * algebraMap R K W.a₄ * v ⟨2, by decide⟩
          + 3 * algebraMap R K W.a₆ * v ⟨2, by decide⟩ ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 0 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (2 : Fin 3) ≠ 0 by decide),
    mul_one, one_pow]
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (show (⟨1, by decide⟩ : {j : Fin 3 // j ≠ 0}) ≠
      ⟨2, by decide⟩ by simp), map_add, Derivation.map_one_eq_zero]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, map_zero, map_one, map_natCast]
  ring

/-- No affine point of an elliptic curve over a field kills the equation and both
partials. -/
private lemma not_affine_singular (W : WeierstrassCurve R) [W.IsElliptic]
    {K : Type u} [Field K] [Algebra R K] (x y : K)
    (hE : y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x
        + algebraMap R K W.a₆)
    (hx : algebraMap R K W.a₁ * y = 3 * x ^ 2 + 2 * algebraMap R K W.a₂ * x
      + algebraMap R K W.a₄)
    (hy : 2 * y + algebraMap R K W.a₁ * x + algebraMap R K W.a₃ = 0) : False := by
  haveI : ((W.map (algebraMap R K)).toAffine).IsElliptic :=
    inferInstanceAs ((W.map (algebraMap R K)).IsElliptic)
  have h1 : (W.map (algebraMap R K)).toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    linear_combination hE
  have h2 := WeierstrassCurve.Affine.equation_iff_nonsingular.mp h1
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at h2
  rcases h2.2 with h | h
  · exact h (by
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
        WeierstrassCurve.map_a₄]
      linear_combination hx)
  · exact h (by
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
      linear_combination hy)

/-- **(T-A3c)** Jacobian comaximality on the `Y`-chart. -/
theorem span_dehomog_jacobian_eq_top_one (W : WeierstrassCurve R) [W.IsElliptic] :
    Ideal.span {MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial)} = ⊤ := by
  by_contra hne
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ hne
  letI : Field (MvPolynomial {j : Fin 3 // j ≠ 1} R ⧸ m) := Ideal.Quotient.field m
  set q : MvPolynomial {j : Fin 3 // j ≠ 1} R →+*
      MvPolynomial {j : Fin 3 // j ≠ 1} R ⧸ m := Ideal.Quotient.mk m with hq
  letI : Algebra R (MvPolynomial {j : Fin 3 // j ≠ 1} R ⧸ m) :=
    (q.comp (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ 1} R))).toAlgebra
  have haev : ∀ p : MvPolynomial {j : Fin 3 // j ≠ 1} R,
      q p = MvPolynomial.aeval (fun j => q (MvPolynomial.X j)) p :=
    ringHom_eq_aeval q (fun r => rfl)
  have hmem : ∀ p ∈ ({MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial)} :
      Set (MvPolynomial {j : Fin 3 // j ≠ 1} R)), q p = 0 := fun p hp =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span hp))
  set u := q (MvPolynomial.X ⟨0, by decide⟩) with hu
  set w := q (MvPolynomial.X ⟨2, by decide⟩) with hwdef
  have hF := hmem _ (Set.mem_insert _ _)
  have hU := hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hW := hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  rw [haev, aeval_dehomog_one] at hF
  rw [haev, aeval_pderiv_dehomog_one_u] at hU
  rw [haev, aeval_pderiv_dehomog_one_w] at hW
  by_cases hw : w = 0
  · rw [← hu, ← hwdef, hw] at hF hW
    have hu3 : u ^ 3 = 0 := by linear_combination -hF
    have hu0 : u = 0 := pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp hu3
    rw [hu0] at hW
    exact one_ne_zero (by linear_combination hW)
  · rw [← hu, ← hwdef] at hF hU hW
    have hinv : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
    have hcomb : w * (2 + algebraMap R _ W.a₁ * u + algebraMap R _ W.a₃ * w) = 0 := by
      linear_combination 3 * hF - u * hU - w * hW
    have h2aw : 2 + algebraMap R _ W.a₁ * u + algebraMap R _ W.a₃ * w = 0 :=
      (mul_eq_zero.mp hcomb).resolve_left hw
    refine not_affine_singular W (u * w⁻¹) w⁻¹ ?_ ?_ ?_
    · field_simp
      linear_combination hF
    · field_simp
      linear_combination hU
    · field_simp
      linear_combination h2aw

/-- **(T-A3c)** Jacobian comaximality on the `X`-chart. -/
theorem span_dehomog_jacobian_eq_top_zero (W : WeierstrassCurve R) [W.IsElliptic] :
    Ideal.span {MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial)} = ⊤ := by
  by_contra hne
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ hne
  letI : Field (MvPolynomial {j : Fin 3 // j ≠ 0} R ⧸ m) := Ideal.Quotient.field m
  set q : MvPolynomial {j : Fin 3 // j ≠ 0} R →+*
      MvPolynomial {j : Fin 3 // j ≠ 0} R ⧸ m := Ideal.Quotient.mk m with hq
  letI : Algebra R (MvPolynomial {j : Fin 3 // j ≠ 0} R ⧸ m) :=
    (q.comp (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ 0} R))).toAlgebra
  have haev : ∀ p : MvPolynomial {j : Fin 3 // j ≠ 0} R,
      q p = MvPolynomial.aeval (fun j => q (MvPolynomial.X j)) p :=
    ringHom_eq_aeval q (fun r => rfl)
  have hmem : ∀ p ∈ ({MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial)} :
      Set (MvPolynomial {j : Fin 3 // j ≠ 0} R)), q p = 0 := fun p hp =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span hp))
  set sc := q (MvPolynomial.X ⟨1, by decide⟩) with hsc
  set t := q (MvPolynomial.X ⟨2, by decide⟩) with htdef
  have hF := hmem _ (Set.mem_insert _ _)
  have hS := hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hT := hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  rw [haev, aeval_dehomog_zero] at hF
  rw [haev, aeval_pderiv_dehomog_zero_s] at hS
  rw [haev, aeval_pderiv_dehomog_zero_t] at hT
  by_cases ht : t = 0
  · rw [← hsc, ← htdef, ht] at hF
    exact one_ne_zero (by linear_combination -hF)
  · rw [← hsc, ← htdef] at hF hS hT
    have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
    have hcomb : algebraMap R _ W.a₁ * sc * t - 3
        - 2 * algebraMap R _ W.a₂ * t - algebraMap R _ W.a₄ * t ^ 2 = 0 := by
      linear_combination 3 * hF - sc * hS - t * hT
    have hsplit : t * (2 * sc + algebraMap R _ W.a₁ + algebraMap R _ W.a₃ * t) = 0 := by
      linear_combination hS
    have hy0 := (mul_eq_zero.mp hsplit).resolve_left ht
    refine not_affine_singular W t⁻¹ (sc * t⁻¹) ?_ ?_ ?_
    · field_simp
      linear_combination hF
    · field_simp
      linear_combination hcomb
    · field_simp
      linear_combination hy0

/-- The `R`-structuring of a chart factors through the plane-quotient chart
identification. -/
lemma algebraMap_chart_eq (W : WeierstrassCurve R) (i : Fin 3) :
    ((algebraMap (↥(quotientGrading (projIdeal W) 0))
      (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
      ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
      ((chartCoordEquiv W i).toRingHom).comp
        (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})) := by
  refine RingHom.ext fun r => ?_
  show _ = chartCoordEquiv W i (algebraMap R _ r)
  rw [show (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})) r =
      Ideal.Quotient.mk _ (MvPolynomial.C r) from by
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial {j : Fin 3 // j ≠ i} R) _,
      Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]]
  exact (chartCoordEquiv_mk_C W i r).symm

/-- The structure map into each chart of the model is locally standard smooth of
relative dimension 1, for elliptic `W`: the chart is `R[u,v]/(F̃ᵢ)`, covered by the
loci where one of the two partials is invertible (Jacobian comaximality), and each
localized hypersurface is standard smooth. -/
theorem locally_isStandardSmooth_algebraMap_gradeZero_away (W : WeierstrassCurve R)
    [W.IsElliptic] (i : Fin 3) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) := by
  have hg : ((algebraMap (↥(quotientGrading (projIdeal W) 0))
      (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
      ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
      ((chartCoordEquiv W i).toRingHom).comp
        (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})) := by
    refine RingHom.ext fun r => ?_
    show _ = chartCoordEquiv W i (algebraMap R _ r)
    rw [show (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})) r =
        Ideal.Quotient.mk _ (MvPolynomial.C r) from by
      rw [IsScalarTower.algebraMap_apply R (MvPolynomial {j : Fin 3 // j ≠ i} R) _,
        Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]]
    exact (chartCoordEquiv_mk_C W i r).symm
  rw [hg]
  refine (RingHom.locally_respectsIso
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso).1 _
    (chartCoordEquiv W i) ?_
  have hcard : Fintype.card {j : Fin 3 // j ≠ i} = 2 := by
    simp [Fintype.card_subtype_compl]
  have hstep : ∀ j : {j : Fin 3 // j ≠ i},
      RingHom.IsStandardSmoothOfRelativeDimension 1
        ((algebraMap (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
            Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
          (Localization.Away (Ideal.Quotient.mk
            (Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
            (MvPolynomial.pderiv j
              (MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial))))).comp
          (algebraMap R _)) := by
    intro j
    rw [← IsScalarTower.algebraMap_eq R _ (Localization.Away _),
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    have h2 := isStandardSmoothOfRelativeDimension_away_pderiv
      (MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial) j
    rwa [hcard] at h2
  fin_cases i
  · refine ⟨{Ideal.Quotient.mk _ (MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial)),
      Ideal.Quotient.mk _ (MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial))}, ?_, ?_⟩
    · have h3 := congrArg (Ideal.map (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial})))
        (span_dehomog_jacobian_eq_top_zero W)
      rw [Ideal.map_top, Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq,
        Set.image_singleton,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
        Ideal.span_insert_zero] at h3
      exact h3
    · intro t ht
      simp only at ht
      rcases ht with rfl | rfl
      · exact hstep ⟨1, by decide⟩
      · exact hstep ⟨2, by decide⟩
  · refine ⟨{Ideal.Quotient.mk _ (MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial)),
      Ideal.Quotient.mk _ (MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial))}, ?_, ?_⟩
    · have h3 := congrArg (Ideal.map (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial})))
        (span_dehomog_jacobian_eq_top_one W)
      rw [Ideal.map_top, Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq,
        Set.image_singleton,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
        Ideal.span_insert_zero] at h3
      exact h3
    · intro t ht
      simp only at ht
      rcases ht with rfl | rfl
      · exact hstep ⟨0, by decide⟩
      · exact hstep ⟨2, by decide⟩
  · refine ⟨{Ideal.Quotient.mk _ (MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial)),
      Ideal.Quotient.mk _ (MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial))}, ?_, ?_⟩
    · have h3 := congrArg (Ideal.map (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})))
        (span_dehomog_jacobian_eq_top W)
      rw [Ideal.map_top, Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq,
        Set.image_singleton,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
        Ideal.span_insert_zero] at h3
      exact h3
    · intro t ht
      simp only at ht
      rcases ht with rfl | rfl
      · exact hstep ⟨0, by decide⟩
      · exact hstep ⟨1, by decide⟩

set_option backward.isDefEq.respectTransparency false in
/-- The chart inclusion from the degree-zero part is locally standard smooth of
relative dimension 1, for elliptic `W`. -/
theorem locally_isStandardSmooth_algebraMap_gradeZero_away' (W : WeierstrassCurve R)
    [W.IsElliptic] (i : Fin 3) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))) := by
  have h1 := locally_isStandardSmooth_algebraMap_gradeZero_away W i
  have h2 := (RingHom.locally_respectsIso
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso).2 _
    (gradeZeroRingEquiv W).symm h1
  have h3 : ((algebraMap (↥(quotientGrading (projIdeal W) 0))
      (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
      ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))).comp
      ((gradeZeroRingEquiv W).symm.toRingHom) =
      algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))) :=
    RingHom.ext fun x => by
      show algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))
          ((gradeZeroRingEquiv W) ((gradeZeroRingEquiv W).symm.toRingHom x)) =
        algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))) x
      exact congrArg _ ((gradeZeroRingEquiv W).apply_symm_apply x)
  rwa [h3] at h2

set_option backward.isDefEq.respectTransparency false in
/-- The `Proj`-to-degree-zero morphism of the model is smooth of relative
dimension 1, for elliptic `W`. -/
theorem toSpecZero_smoothOfRelativeDimension (W : WeierstrassCurve R)
    [W.IsElliptic] :
    SmoothOfRelativeDimension 1 (Proj.toSpecZero (quotientGrading (projIdeal W))) := by
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @SmoothOfRelativeDimension 1) _
    (Proj.iSup_basicOpen_eq_top (quotientGrading (projIdeal W))
      (fun i : Fin 3 => Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i))
      (quotient_irrelevant_le_span_mk_X W))]
  intro i
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)
    (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W))
      (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i))
      (mk_X_mem_quotientGrading_one W i) one_pos).inv, ← Category.assoc,
    ← Proj.awayι, Proj.awayι_toSpecZero,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact locally_isStandardSmooth_algebraMap_gradeZero_away' W i

/-- **(T-A3)** The projective model of an *elliptic* Weierstrass curve (unit discriminant) is
smooth of relative dimension 1 over the base.
Source: Loeffler §3.3 ("If `Δ(α,β) ∈ Γ(S,O_S)ˣ`, this is an elliptic curve over `S`");
KM 2.2.4; Silverman III.1.4(a). -/
theorem projModel_smooth (W : WeierstrassCurve R) [W.IsElliptic] :
    SmoothOfRelativeDimension 1 (projModelπ W) := by
  haveI h1 := toSpecZero_smoothOfRelativeDimension W
  haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W)))) :=
    inferInstance
  haveI h2 : SmoothOfRelativeDimension 0
      (Spec.map (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W)))) :=
    inferInstance
  have h3 : SmoothOfRelativeDimension (1 + 0)
      (Proj.toSpecZero (quotientGrading (projIdeal W)) ≫
        Spec.map (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W)))) :=
    inferInstance
  exact h3

section BaseChangeGraded

variable {R' : Type u} [CommRing R'] (f : R →+* R')

/-- `MvPolynomial.map` as a graded ring homomorphism for the standard grading. -/
noncomputable def mvMapGraded : GradedRingHom
    (MvPolynomial.homogeneousSubmodule (Fin 3) R)
    (MvPolynomial.homogeneousSubmodule (Fin 3) R') where
  toRingHom := MvPolynomial.map f
  map_mem {_i _x} hx := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (((MvPolynomial.mem_homogeneousSubmodule _ _).mp hx).map f)

lemma projIdeal_le_comap (W : WeierstrassCurve R) :
    (projIdeal W).toIdeal ≤
      (projIdeal (W.map f)).toIdeal.comap (MvPolynomial.map f) := by
  rw [projIdeal_toIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
    Ideal.mem_comap, ← WeierstrassCurve.Projective.map_polynomial]
  exact Ideal.subset_span rfl

/-- The graded base-change homomorphism between the homogeneous coordinate rings of
the Weierstrass models of `W` and `W.map f`. -/
noncomputable def baseChangeGradedHom (W : WeierstrassCurve R) :
    GradedRingHom (quotientGrading (projIdeal W))
      (quotientGrading (projIdeal (W.map f))) :=
  quotientGradingMap (mvMapGraded f) (projIdeal W) (projIdeal (W.map f))
    (projIdeal_le_comap f W)

set_option backward.isDefEq.respectTransparency false in
lemma baseChangeGradedHom_irrelevant_le (W : WeierstrassCurve R) :
    (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal (W.map f)))).toIdeal ≤
      Ideal.map (baseChangeGradedHom f W).toRingHom
        (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal := by
  refine le_trans (quotient_irrelevant_le_span_mk_X (W.map f)) ?_
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  beta_reduce
  have h1 : (Ideal.Quotient.mk (projIdeal (W.map f)).toIdeal
      (MvPolynomial.X i) : projCoordRing (W.map f)) =
      (baseChangeGradedHom f W).toRingHom
        (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i)) := by
    show _ = quotientGradingMap (mvMapGraded f) _ _ _ (Ideal.Quotient.mk _ _)
    rw [quotientGradingMap_mk]
    show _ = Ideal.Quotient.mk _ (MvPolynomial.map f (MvPolynomial.X i))
    rw [MvPolynomial.map_X]
  rw [h1]
  refine Ideal.mem_map_of_mem _ ?_
  show GradedRing.proj (quotientGrading (projIdeal W)) 0
      (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i)) = 0
  rw [GradedRing.proj_apply,
    decompose_quotientGrading_mk (projIdeal W)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (MvPolynomial.isHomogeneous_X _ _)),
    DirectSum.coe_of_apply]
  simp

/-- **(T-A5a)** The base-change morphism between projective Weierstrass models:
`Proj` of the graded base-change homomorphism. -/
noncomputable def projModelBaseChange (W : WeierstrassCurve R) :
    projModel (W.map f) ⟶ projModel W :=
  Proj.map (baseChangeGradedHom f W) (baseChangeGradedHom_irrelevant_le f W)

set_option backward.isDefEq.respectTransparency false in
private lemma bc_ring_square (W : WeierstrassCurve R) {i : ℕ}
    (s : projCoordRing W) (hs : s ∈ quotientGrading (projIdeal W) i) :
    (HomogeneousLocalization.Away.map (baseChangeGradedHom f W) s).comp
      ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W)) s)).comp
        (algebraMapGradeZero (projIdeal W))) =
      (((algebraMap (↥(quotientGrading (projIdeal (W.map f)) 0))
        (Away (quotientGrading (projIdeal (W.map f)))
          ((baseChangeGradedHom f W) s))).comp
        (algebraMapGradeZero (projIdeal (W.map f)))).comp f) := by
  refine RingHom.ext fun r => ?_
  have hmem0 : (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.C r) :
      projCoordRing W) ∈ quotientGrading (projIdeal W) (0 • i) := by
    rw [zero_smul]
    exact mk_mem_quotientGrading _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_C _ _))
  have hL0 : (algebraMap (↥(quotientGrading (projIdeal W) 0))
      (Away (quotientGrading (projIdeal W)) s))
        ((algebraMapGradeZero (projIdeal W)) r) =
      HomogeneousLocalization.Away.mk (quotientGrading (projIdeal W)) hs 0
        (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.C r)) hmem0 := by
    apply val_injective
    rw [HomogeneousLocalization.algebraMap_eq, Away.val_mk]
    show Localization.mk (((algebraMapGradeZero (projIdeal W)) r :
      ↥(quotientGrading (projIdeal W) 0)) : projCoordRing W) 1 = _
    have hval : (((algebraMapGradeZero (projIdeal W)) r :
        ↥(quotientGrading (projIdeal W) 0)) : projCoordRing W) =
        Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.C r) := by
      show algebraMap R (projCoordRing W) r = _
      rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing W),
        RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
    rw [hval]
    exact congrArg _ (Subtype.ext (pow_zero _).symm)
  have hmem0' : (Ideal.Quotient.mk (projIdeal (W.map f)).toIdeal
      (MvPolynomial.C (f r)) : projCoordRing (W.map f)) ∈
      quotientGrading (projIdeal (W.map f)) 0 :=
    mk_mem_quotientGrading _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_C _ _))
  simp only [RingHom.comp_apply]
  rw [hL0, Away.map_mk]
  apply val_injective
  rw [Away.val_mk, HomogeneousLocalization.algebraMap_eq]
  have hbc : (baseChangeGradedHom f W)
      (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.C r)) =
      Ideal.Quotient.mk (projIdeal (W.map f)).toIdeal (MvPolynomial.C (f r)) := by
    show quotientGradingMap (mvMapGraded f) _ _ _ (Ideal.Quotient.mk _ _) = _
    rw [quotientGradingMap_mk]
    show Ideal.Quotient.mk _ (MvPolynomial.map f (MvPolynomial.C r)) = _
    rw [MvPolynomial.map_C]
  show _ = Localization.mk (((algebraMapGradeZero (projIdeal (W.map f))) (f r) :
    ↥(quotientGrading (projIdeal (W.map f)) 0)) : projCoordRing (W.map f)) 1
  have hval' : (((algebraMapGradeZero (projIdeal (W.map f))) (f r) :
      ↥(quotientGrading (projIdeal (W.map f)) 0)) : projCoordRing (W.map f)) =
      Ideal.Quotient.mk (projIdeal (W.map f)).toIdeal (MvPolynomial.C (f r)) := by
    show algebraMap R' (projCoordRing (W.map f)) (f r) = _
    rw [IsScalarTower.algebraMap_eq R' (MvPolynomial (Fin 3) R')
      (projCoordRing (W.map f)), RingHom.comp_apply, Ideal.Quotient.algebraMap_eq,
      MvPolynomial.algebraMap_eq]
  rw [hval', hbc]
  exact congrArg _ (Subtype.ext (pow_zero _))

set_option backward.isDefEq.respectTransparency false in
/-- **(T-A5a)** The base-change square of the model over its structure morphisms. -/
theorem projModelBaseChange_π (W : WeierstrassCurve R) :
    projModelBaseChange f W ≫ projModelπ W =
      projModelπ (W.map f) ≫ Spec.map (CommRingCat.ofHom f) := by
  refine (Proj.mapAffineOpenCover (baseChangeGradedHom f W)
    (baseChangeGradedHom_irrelevant_le f W)).openCover.hom_ext _ _ fun s => ?_
  rw [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  unfold projModelBaseChange projModelπ
  simp only [Category.assoc]
  rw [Proj.awayι_comp_map_assoc]
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp]
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp]
  congr 1
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  · exact congrArg CommRingCat.ofHom (bc_ring_square f W _ s.2.2)
  · exact s.2.2

/-- **(T-A5a)** The comparison morphism from the model of `W.map f` into the base
change of the model of `W`. -/
noncomputable def projModelBaseChangeLift (W : WeierstrassCurve R) :
    projModel (W.map f) ⟶
      Limits.pullback (projModelπ W) (Spec.map (CommRingCat.ofHom f)) :=
  Limits.pullback.lift (projModelBaseChange f W) (projModelπ (W.map f))
    (projModelBaseChange_π f W)

/-- **Functoriality of the projective-model base change.** Base change along a composite factors as
the two base changes: `projModelBaseChange (F.comp G) W = projModelBaseChange F (W.map G) ≫
projModelBaseChange G W` (note `(W.map G).map F = W.map (F.comp G)` definitionally). This is
`Proj.map_comp` applied to the graded base-change homomorphisms, whose composite equals
`baseChangeGradedHom (F.comp G) W` by `MvPolynomial.map_map`. -/
theorem projModelBaseChange_comp (F G : R →+* R) (W : WeierstrassCurve R) :
    projModelBaseChange (F.comp G) W
      = projModelBaseChange F (W.map G) ≫ projModelBaseChange G W := by
  have bmk : ∀ (φ : R →+* R) (W' : WeierstrassCurve R) (p : MvPolynomial (Fin 3) R),
      baseChangeGradedHom φ W' (Ideal.Quotient.mk (projIdeal W').toIdeal p)
        = Ideal.Quotient.mk (projIdeal (W'.map φ)).toIdeal (MvPolynomial.map φ p) :=
    fun φ W' p => HomogeneousIdeal.quotientGradingMap_mk (mvMapGraded φ) (projIdeal W')
      (projIdeal (W'.map φ)) (projIdeal_le_comap φ W') p
  have hgraded : baseChangeGradedHom (F.comp G) W
      = (baseChangeGradedHom F (W.map G)).comp (baseChangeGradedHom G W) := by
    refine GradedRingHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    show baseChangeGradedHom (F.comp G) W (Ideal.Quotient.mk _ a)
      = baseChangeGradedHom F (W.map G) (baseChangeGradedHom G W (Ideal.Quotient.mk _ a))
    rw [bmk, bmk, bmk]
    exact congrArg (Ideal.Quotient.mk _) (MvPolynomial.map_map G F a).symm
  have key := Proj.map_comp (baseChangeGradedHom G W) (baseChangeGradedHom F (W.map G))
    (baseChangeGradedHom_irrelevant_le G W) (baseChangeGradedHom_irrelevant_le F (W.map G))
  refine Eq.trans ?_ key
  show Proj.map (baseChangeGradedHom (F.comp G) W) (baseChangeGradedHom_irrelevant_le (F.comp G) W)
    = Proj.map ((baseChangeGradedHom F (W.map G)).comp (baseChangeGradedHom G W)) _
  congr 1

section TensorComparison

open scoped TensorProduct

variable {R' : Type u} [CommRing R'] [Algebra R R']

/-- Scalar extension identifies the dehomogenised cubics. -/
lemma dehomog_baseChange (W : WeierstrassCurve R) (i : Fin 3) :
    MvPolynomial.map (algebraMap R R')
        (MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial) =
      MvPolynomial.dehomogenizeAux R' i
        (W.map (algebraMap R R')).toProjective.polynomial := by
  rw [show (W.map (algebraMap R R')).toProjective.polynomial =
    MvPolynomial.map (algebraMap R R') W.toProjective.polynomial from
    WeierstrassCurve.Projective.map_polynomial W.toProjective (algebraMap R R')]
  rw [MvPolynomial.dehomogenizeAux_map]

/-- The scalar-extension map between the affine chart quotients. -/
noncomputable def sChartBaseChange (W : WeierstrassCurve R) (i : Fin 3) :
    (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial}) →ₐ[R]
    (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R' i
        (W.map (algebraMap R R')).toProjective.polynomial}) := by
  refine Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ R _).comp
      (MvPolynomial.mapAlgHom (Algebra.ofId R R'))) fun a ha => ?_
  suffices h : Ideal.span {MvPolynomial.dehomogenizeAux R i
      W.toProjective.polynomial} ≤ RingHom.ker ((Ideal.Quotient.mkₐ R _).comp
      (MvPolynomial.mapAlgHom (R := R) (Algebra.ofId R R'))).toRingHom from h ha
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
  show Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R R')
    (MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial)) = 0
  rw [dehomog_baseChange]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

@[simp]
lemma sChartBaseChange_mk (W : WeierstrassCurve R) (i : Fin 3)
    (p : MvPolynomial {j : Fin 3 // j ≠ i} R) :
    sChartBaseChange (R' := R') W i (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R R') p) :=
  rfl

/-- The canonical evaluation into the tensor corner. -/
private noncomputable def sChartTensorInvAux (W : WeierstrassCurve R) (i : Fin 3) :
    MvPolynomial {j : Fin 3 // j ≠ i} R' →ₐ[R']
      (R' ⊗[R] (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})) :=
  MvPolynomial.aeval fun j => (1 : R') ⊗ₜ[R]
    (Ideal.Quotient.mk
      (Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
      (MvPolynomial.X j))

private lemma sChartTensorInvAux_map_algebraMap (W : WeierstrassCurve R) (i : Fin 3)
    (p : MvPolynomial {j : Fin 3 // j ≠ i} R) :
    sChartTensorInvAux (R' := R') W i (MvPolynomial.map (algebraMap R R') p) =
      1 ⊗ₜ[R] (Ideal.Quotient.mk _ p) := by
  rw [sChartTensorInvAux, MvPolynomial.aeval_map_algebraMap]
  have h : (MvPolynomial.aeval (R := R) fun j => ((1 : R') ⊗ₜ[R]
      (Ideal.Quotient.mk (Ideal.span {MvPolynomial.dehomogenizeAux R i
        W.toProjective.polynomial}) (MvPolynomial.X j)))) =
      (Algebra.TensorProduct.includeRight.comp
        (Ideal.Quotient.mkₐ R (Ideal.span {MvPolynomial.dehomogenizeAux R i
          W.toProjective.polynomial}))) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp
  rw [h]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension of the chart quotient as a tensor identification. -/
noncomputable def sChartTensorEquiv (W : WeierstrassCurve R) (i : Fin 3) :
    (R' ⊗[R] (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial}))
      ≃ₐ[R'] (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R' i
        (W.map (algebraMap R R')).toProjective.polynomial}) := by
  refine AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (Algebra.ofId R' _)
      (sChartBaseChange (R' := R') W i) fun _ _ => Commute.all _ _)
    (Ideal.Quotient.liftₐ _ (sChartTensorInvAux W i) fun a ha => ?_) ?_ ?_
  · suffices h : Ideal.span {MvPolynomial.dehomogenizeAux R' i
        (W.map (algebraMap R R')).toProjective.polynomial} ≤
        RingHom.ker (sChartTensorInvAux (R' := R') W i).toRingHom from h ha
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      ← dehomog_baseChange]
    show sChartTensorInvAux (R' := R') W i
      (MvPolynomial.map (algebraMap R R')
        (MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial)) = 0
    rw [sChartTensorInvAux_map_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
      TensorProduct.tmul_zero]
  · -- forward ∘ inverse = id on the R'-side quotient
    refine AlgHom.ext fun x => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h : ∀ q : MvPolynomial {j : Fin 3 // j ≠ i} R',
        (Algebra.TensorProduct.lift (Algebra.ofId R' _)
          (sChartBaseChange (R' := R') W i) fun _ _ => Commute.all _ _)
          (sChartTensorInvAux (R' := R') W i q) = Ideal.Quotient.mk _ q := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C r =>
        rw [sChartTensorInvAux, MvPolynomial.aeval_C, AlgHom.commutes]
        rfl
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p j hp =>
        simp only [sChartTensorInvAux] at hp ⊢
        simp only [map_mul, MvPolynomial.aeval_X, hp,
          Algebra.TensorProduct.lift_tmul, map_one, one_mul,
          sChartBaseChange_mk, MvPolynomial.map_X]
    exact h p
  · -- inverse ∘ forward = id on the tensor side
    refine Algebra.TensorProduct.ext' fun a b => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [AlgHom.comp_apply, AlgHom.id_apply, Algebra.TensorProduct.lift_tmul]
    rw [show (Algebra.ofId R' _) a * (sChartBaseChange (R' := R') W i)
        (Ideal.Quotient.mk _ p) = a • ((sChartBaseChange (R' := R') W i)
        (Ideal.Quotient.mk _ p)) from (Algebra.smul_def a _).symm]
    rw [map_smul, sChartBaseChange_mk]
    rw [show ((Ideal.Quotient.liftₐ _ (sChartTensorInvAux (R' := R') W i) _)
        (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R R') p))) =
        sChartTensorInvAux (R' := R') W i
          (MvPolynomial.map (algebraMap R R') p) from rfl]
    rw [sChartTensorInvAux_map_algebraMap]
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The chart quotients form a pushout square over `R → R'`. -/
lemma isPushout_sChart (W : WeierstrassCurve R) (i : Fin 3) :
    letI : Algebra
        (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
        (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R' i
            (W.map (algebraMap R R')).toProjective.polynomial}) :=
      ((sChartBaseChange (R' := R') W i).toRingHom).toAlgebra
    Algebra.IsPushout R R'
      (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
      (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R' i
          (W.map (algebraMap R R')).toProjective.polynomial}) := by
  letI : Algebra
      (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
      (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R' i
          (W.map (algebraMap R R')).toProjective.polynomial}) :=
    ((sChartBaseChange (R' := R') W i).toRingHom).toAlgebra
  haveI : IsScalarTower R
      (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
      (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R' i
          (W.map (algebraMap R R')).toProjective.polynomial}) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      ((sChartBaseChange (R' := R') W i).commutes r).symm
  refine ⟨IsBaseChange.of_equiv
    (sChartTensorEquiv (R' := R') W i).toLinearEquiv fun x => ?_⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  show sChartTensorEquiv (R' := R') W i
    ((1 : R') ⊗ₜ[R] (Ideal.Quotient.mk _ p)) = _
  show (Algebra.TensorProduct.lift (Algebra.ofId R' _)
    (sChartBaseChange (R' := R') W i) fun _ _ => Commute.all _ _)
    ((1 : R') ⊗ₜ[R] (Ideal.Quotient.mk _ p)) = _
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

/-- The categorical (CommRingCat) pushout square of the chart quotients. -/
lemma isPushout_sChart_commRingCat (W : WeierstrassCurve R) (i : Fin 3) :
    IsPushout
      (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom (algebraMap R
        (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})))
      (CommRingCat.ofHom (algebraMap R'
        (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R' i
            (W.map (algebraMap R R')).toProjective.polynomial})))
      (CommRingCat.ofHom ((sChartBaseChange (R' := R') W i).toRingHom)) := by
  letI : Algebra
      (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
      (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R' i
          (W.map (algebraMap R R')).toProjective.polynomial}) :=
    ((sChartBaseChange (R' := R') W i).toRingHom).toAlgebra
  haveI : IsScalarTower R
      (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
      (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R' i
          (W.map (algebraMap R R')).toProjective.polynomial}) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      ((sChartBaseChange (R' := R') W i).commutes r).symm
  haveI := isPushout_sChart (R' := R') W i
  exact CommRingCat.isPushout_of_isPushout R R' _ _

/-- The `Spec` of the chart square is a pullback: the chart of the base-changed model
is the base change of the chart. -/
lemma isPullback_sChart_spec (W : WeierstrassCurve R) (i : Fin 3) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R'
        (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R' i
            (W.map (algebraMap R R')).toProjective.polynomial}))))
      (Spec.map (CommRingCat.ofHom ((sChartBaseChange (R' := R') W i).toRingHom)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Spec.map (CommRingCat.ofHom (algebraMap R
        (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R i
            W.toProjective.polynomial})))) :=
  AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_sChart_commRingCat (R' := R') W i)

/-- The three-chart affine open cover of the projective Weierstrass model. -/
noncomputable def modelChartCover (W : WeierstrassCurve R) :
    (projModel W).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (quotientGrading (projIdeal W))
    (fun i : Fin 3 => (quotientGradingHom (projIdeal W)) (MvPolynomial.X i))
    (fun i => mk_X_mem_quotientGrading_one W i) (fun _ => one_pos)
    (quotient_irrelevant_le_span_mk_X W)

set_option backward.isDefEq.respectTransparency false in
/-- Each cover piece of the pulled-back model is `Spec` of the base-changed chart
quotient: the pullback square at chart `j`. -/
lemma isPullback_piece (W : WeierstrassCurve R) (j : Fin 3) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (((sChartBaseChange (R' := R') W j).toRingHom).comp
          ((chartCoordEquiv W j).symm.toRingHom))))
      (Spec.map (CommRingCat.ofHom (algebraMap R'
        (MvPolynomial {k : Fin 3 // k ≠ j} R' ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R' j
            (W.map (algebraMap R R')).toProjective.polynomial}))))
      ((modelChartCover W).openCover.f j ≫ projModelπ W)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  have h := (isPullback_sChart_spec (R' := R') W j).flip
  refine h.of_iso (Iso.refl _)
    (asIso (Spec.map ((chartCoordEquiv W j).toCommRingCatIso.inv)))
    (Iso.refl _) (Iso.refl _) ?commfst ?commsnd ?commf ?commg
  case commfst =>
    rw [Iso.refl_hom, Category.id_comp, asIso_hom,
      show (chartCoordEquiv W j).toCommRingCatIso.inv =
        CommRingCat.ofHom ((chartCoordEquiv W j).symm.toRingHom) from rfl,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  case commsnd =>
    rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
  case commg =>
    rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
  case commf =>
    rw [Iso.refl_hom, Category.comp_id, asIso_hom]
    rw [show (modelChartCover W).openCover.f j ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0)))) from
      awayι_projModelπ W j]
    rw [← Spec.map_comp]
    congr 1
    rw [show ((chartCoordEquiv W j).toCommRingCatIso.inv) =
      CommRingCat.ofHom ((chartCoordEquiv W j).symm.toRingHom) from rfl,
      ← CommRingCat.ofHom_comp]
    congr 1
    rw [algebraMap_chart_eq]
    refine RingHom.ext fun r => ?_
    exact ((chartCoordEquiv W j).symm_apply_apply _).symm

set_option backward.isDefEq.respectTransparency false in
lemma baseChangeGradedHom_mk_X (W : WeierstrassCurve R) (j : Fin 3) :
    (baseChangeGradedHom (algebraMap R R') W)
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)) =
      (quotientGradingHom (projIdeal (W.map (algebraMap R R'))))
        (MvPolynomial.X j) := by
  show quotientGradingMap (mvMapGraded (algebraMap R R')) _ _ _
    (Ideal.Quotient.mk _ _) = _
  rw [quotientGradingMap_mk]
  show Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R R') (MvPolynomial.X j)) = _
  rw [MvPolynomial.map_X]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The chart square of the base-change morphism of models is cartesian:
`D₊`-preimages under `Proj.map` are the base-changed charts. -/
lemma isPullback_projModelBaseChange_chart (W : WeierstrassCurve R) (j : Fin 3) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
        (baseChangeGradedHom (algebraMap R R') W)
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)))))
      (Proj.awayι (quotientGrading (projIdeal (W.map (algebraMap R R'))))
        ((baseChangeGradedHom (algebraMap R R') W)
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)))
        ((baseChangeGradedHom (algebraMap R R') W).2
          (mk_X_mem_quotientGrading_one W j)) one_pos)
      (Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
        (mk_X_mem_quotientGrading_one W j) one_pos)
      (projModelBaseChange (algebraMap R R') W) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · exact Proj.awayι_comp_map (baseChangeGradedHom (algebraMap R R') W)
      (baseChangeGradedHom_irrelevant_le (algebraMap R R') W) one_pos _
      (mk_X_mem_quotientGrading_one W j)
  · rw [show projModelBaseChange (algebraMap R R') W =
      Proj.map (baseChangeGradedHom (algebraMap R R') W)
        (baseChangeGradedHom_irrelevant_le (algebraMap R R') W) from rfl]
    rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.map_preimage_basicOpen]

set_option backward.isDefEq.respectTransparency false in
private lemma coverPiece_f_eq (W : WeierstrassCurve R) (j : Fin 3) :
    (Scheme.Pullback.openCoverOfLeft ((modelChartCover W).openCover)
        (projModelπ W) (Spec.map (CommRingCat.ofHom (algebraMap R R')))).f j =
      (Limits.pullbackRightPullbackFstIso (projModelπ W)
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))
        ((modelChartCover W).openCover.f j)).inv ≫
      Limits.pullback.snd ((modelChartCover W).openCover.f j)
        (Limits.pullback.fst (projModelπ W)
          (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc]
    rw [show Limits.pullback.snd ((modelChartCover W).openCover.f j)
        (Limits.pullback.fst (projModelπ W)
          (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
        Limits.pullback.fst (projModelπ W)
          (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
        Limits.pullback.fst ((modelChartCover W).openCover.f j)
          (Limits.pullback.fst (projModelπ W)
            (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          (modelChartCover W).openCover.f j from Limits.pullback.condition.symm]
    rw [← Category.assoc, Limits.pullbackRightPullbackFstIso_inv_fst]
    simp
  · rw [Category.assoc, Limits.pullbackRightPullbackFstIso_inv_snd_snd]
    simp

/-- The first-projection square over a cover piece is cartesian. -/
private lemma isPullback_coverPiece (W : WeierstrassCurve R) (j : Fin 3) :
    IsPullback
      (Limits.pullback.fst ((modelChartCover W).openCover.f j ≫ projModelπ W)
        (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
      ((Scheme.Pullback.openCoverOfLeft ((modelChartCover W).openCover)
        (projModelπ W) (Spec.map (CommRingCat.ofHom (algebraMap R R')))).f j)
      ((modelChartCover W).openCover.f j)
      (Limits.pullback.fst (projModelπ W)
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := by
  rw [coverPiece_f_eq]
  have h0 := IsPullback.of_hasPullback ((modelChartCover W).openCover.f j)
    (Limits.pullback.fst (projModelπ W)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
  refine h0.of_iso (Limits.pullbackRightPullbackFstIso (projModelπ W)
    (Spec.map (CommRingCat.ofHom (algebraMap R R')))
    ((modelChartCover W).openCover.f j)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id]
    exact (Limits.pullbackRightPullbackFstIso_hom_fst _ _ _).symm
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- The wall-crossing identification of the base-changed chart `Spec`s. -/
private noncomputable def thetaIso (W : WeierstrassCurve R) (j : Fin 3) :
    Spec (.of (MvPolynomial {k : Fin 3 // k ≠ j} R' ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R' j
        (W.map (algebraMap R R')).toProjective.polynomial})) ≅
    Spec (.of (Away (quotientGrading (projIdeal (W.map (algebraMap R R'))))
      ((baseChangeGradedHom (algebraMap R R') W)
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))))) :=
  letI : IsIso (CommRingCat.ofHom
      ((chartCoordEquiv (W.map (algebraMap R R')) j).symm.toRingHom)) :=
    ⟨CommRingCat.ofHom ((chartCoordEquiv (W.map (algebraMap R R')) j).toRingHom),
      CommRingCat.hom_ext (RingHom.ext fun x =>
        (chartCoordEquiv (W.map (algebraMap R R')) j).apply_symm_apply x),
      CommRingCat.hom_ext (RingHom.ext fun x =>
        (chartCoordEquiv (W.map (algebraMap R R')) j).symm_apply_apply x)⟩
  asIso (Spec.map (CommRingCat.ofHom
    ((chartCoordEquiv (W.map (algebraMap R R')) j).symm.toRingHom))) ≪≫
  asIso (Spec.map ((awayCongr
    (baseChangeGradedHom_mk_X (R' := R') W j)).toCommRingCatIso.hom))

set_option backward.isDefEq.respectTransparency false in
/-- The graded square of the base change: quotient map after coefficient map. -/
lemma gradedSquare (W : WeierstrassCurve R) :
    (baseChangeGradedHom (algebraMap R R') W).comp
      (quotientGradingHom (projIdeal W)) =
    (quotientGradingHom (projIdeal (W.map (algebraMap R R')))).comp
      (mvMapGraded (algebraMap R R')) := by
  refine GradedRingHom.ext fun x => ?_
  show quotientGradingMap (mvMapGraded (algebraMap R R')) (projIdeal W)
    (projIdeal (W.map (algebraMap R R')))
    (projIdeal_le_comap (algebraMap R R') W)
    (Ideal.Quotient.mk (projIdeal W).toIdeal x) = _
  rw [quotientGradingMap_mk]
  rfl

/-- Elementwise chart naturality of the base change. -/
private lemma bc_chart_value (W : WeierstrassCurve R) (j : Fin 3)
    (p : MvPolynomial {k : Fin 3 // k ≠ j} R) :
    (awayCongr (baseChangeGradedHom_mk_X (R' := R') W j))
      ((HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap R R') W)
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)))
        ((HomogeneousLocalization.Away.map (quotientGradingHom (projIdeal W))
          (MvPolynomial.X j)) (MvPolynomial.homogenizeAt R j p))) =
    (HomogeneousLocalization.Away.map
      (quotientGradingHom (projIdeal (W.map (algebraMap R R'))))
      (MvPolynomial.X j))
      (MvPolynomial.homogenizeAt R' j (MvPolynomial.map (algebraMap R R') p)) := by
  rw [MvPolynomial.homogenizeAt_map, ModularCurves.awayCongr_map]
  exact ModularCurves.awayMap_square
    (f₁ := quotientGradingHom (projIdeal W))
    (g₁ := baseChangeGradedHom (algebraMap R R') W)
    (f₂ := mvMapGraded (algebraMap R R'))
    (g₂ := quotientGradingHom (projIdeal (W.map (algebraMap R R'))))
    (gradedSquare (R' := R') W)
    (MvPolynomial.X j) (MvPolynomial.homogenizeAt R j p)
    (t := (quotientGradingHom (projIdeal (W.map (algebraMap R R'))))
      (MvPolynomial.X j))
    (baseChangeGradedHom_mk_X (R' := R') W j)
    (congrArg (fun z => (quotientGradingHom (projIdeal (W.map (algebraMap R R')))) z)
      (MvPolynomial.map_X (algebraMap R R') j))

/-- Chart naturality of the base change, across the wall: the plane-chart
comparison equals the graded `Away.map` under the two chart identifications. -/
private lemma piece_fst_natural (W : WeierstrassCurve R) (j : Fin 3) :
    Spec.map (CommRingCat.ofHom
      (((sChartBaseChange (R' := R') W j).toRingHom).comp
        ((chartCoordEquiv W j).symm.toRingHom))) =
    (thetaIso (R' := R') W j).hom ≫
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
        (baseChangeGradedHom (algebraMap R R') W)
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)))) := by
  simp only [thetaIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  refine congrArg Spec.map ?_
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  obtain ⟨q, rfl⟩ := (chartCoordEquiv W j).surjective x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  show (sChartBaseChange (R' := R') W j) ((chartCoordEquiv W j).symm
    (chartCoordEquiv W j (Ideal.Quotient.mk _ p))) =
    (chartCoordEquiv (W.map (algebraMap R R')) j).symm
      ((awayCongr (baseChangeGradedHom_mk_X (R' := R') W j))
        ((HomogeneousLocalization.Away.map (baseChangeGradedHom (algebraMap R R') W)
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)))
          (chartCoordEquiv W j (Ideal.Quotient.mk _ p))))
  rw [RingEquiv.symm_apply_apply, sChartBaseChange_mk]
  rw [RingEquiv.eq_symm_apply]
  rw [chartCoordEquiv_mk, chartCoordEquiv_mk]
  exact (bc_chart_value (R' := R') W j p).symm

/-- `Proj.awayι` absorbs the transport along an element equality. -/
private lemma awayι_awayCongr (W' : WeierstrassCurve R') {s t : projCoordRing W'}
    (h : s = t) (hs : s ∈ quotientGrading (projIdeal W') 1) :
    Spec.map ((awayCongr (𝒜 := quotientGrading (projIdeal W'))
        h).toCommRingCatIso.hom) ≫
      Proj.awayι (quotientGrading (projIdeal W')) s hs one_pos =
    Proj.awayι (quotientGrading (projIdeal W')) t (h ▸ hs) one_pos := by
  subst h
  rw [show ((awayCongr (𝒜 := quotientGrading (projIdeal W'))
      (rfl : s = s)).toCommRingCatIso.hom) = 𝟙 _ from rfl]
  rw [Spec.map_id, Category.id_comp]

/-- The chart of the base-changed model over its own structure map, θ-form. -/
private lemma theta_awayι_π (W : WeierstrassCurve R) (j : Fin 3) :
    (thetaIso (R' := R') W j).hom ≫
      Proj.awayι (quotientGrading (projIdeal (W.map (algebraMap R R'))))
        ((baseChangeGradedHom (algebraMap R R') W)
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)))
        ((baseChangeGradedHom (algebraMap R R') W).2
          (mk_X_mem_quotientGrading_one W j)) one_pos ≫
      projModelπ (W.map (algebraMap R R')) =
    Spec.map (CommRingCat.ofHom (algebraMap R'
      (MvPolynomial {k : Fin 3 // k ≠ j} R' ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R' j
          (W.map (algebraMap R R')).toProjective.polynomial}))) := by
  simp only [thetaIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [reassoc_of% (awayι_awayCongr (W.map (algebraMap R R'))
    (baseChangeGradedHom_mk_X (R' := R') W j)
    ((baseChangeGradedHom (algebraMap R R') W).2
      (mk_X_mem_quotientGrading_one W j)))]
  rw [show (baseChangeGradedHom_mk_X (R' := R') W j) ▸
      ((baseChangeGradedHom (algebraMap R R') W).2
        (mk_X_mem_quotientGrading_one W j)) =
      mk_X_mem_quotientGrading_one (W.map (algebraMap R R')) j from rfl]
  rw [awayι_projModelπ (W.map (algebraMap R R')) j]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  rw [algebraMap_chart_eq (W.map (algebraMap R R')) j]
  refine congrArg CommRingCat.ofHom ?_
  refine RingHom.ext fun r => ?_
  show (chartCoordEquiv (W.map (algebraMap R R')) j).symm
    ((chartCoordEquiv (W.map (algebraMap R R')) j) ((algebraMap R' _) r)) = _
  rw [RingEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The lift restricts over each cover piece to the base-changed chart. -/
lemma isPullback_lift_piece (W : WeierstrassCurve R) (j : Fin 3) :
    IsPullback
      ((thetaIso (R' := R') W j).hom ≫
        Proj.awayι (quotientGrading (projIdeal (W.map (algebraMap R R'))))
          ((baseChangeGradedHom (algebraMap R R') W)
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)))
          ((baseChangeGradedHom (algebraMap R R') W).2
            (mk_X_mem_quotientGrading_one W j)) one_pos)
      ((isPullback_piece (R' := R') W j).isoPullback.hom)
      (projModelBaseChangeLift (algebraMap R R') W)
      ((Scheme.Pullback.openCoverOfLeft ((modelChartCover W).openCover)
        (projModelπ W) (Spec.map (CommRingCat.ofHom (algebraMap R R')))).f j) := by
  have hfst : (isPullback_piece (R' := R') W j).isoPullback.hom ≫
      Limits.pullback.fst ((modelChartCover W).openCover.f j ≫ projModelπ W)
        (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
      Spec.map (CommRingCat.ofHom
        (((sChartBaseChange (R' := R') W j).toRingHom).comp
          ((chartCoordEquiv W j).symm.toRingHom))) :=
    (isPullback_piece (R' := R') W j).isoPullback_hom_fst
  have hsnd : (isPullback_piece (R' := R') W j).isoPullback.hom ≫
      Limits.pullback.snd ((modelChartCover W).openCover.f j ≫ projModelπ W)
        (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
      Spec.map (CommRingCat.ofHom (algebraMap R'
        (MvPolynomial {k : Fin 3 // k ≠ j} R' ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R' j
            (W.map (algebraMap R R')).toProjective.polynomial}))) :=
    (isPullback_piece (R' := R') W j).isoPullback_hom_snd
  have hbcfst : (thetaIso (R' := R') W j).hom ≫
      Proj.awayι (quotientGrading (projIdeal (W.map (algebraMap R R'))))
        ((baseChangeGradedHom (algebraMap R R') W)
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)))
        ((baseChangeGradedHom (algebraMap R R') W).2
          (mk_X_mem_quotientGrading_one W j)) one_pos ≫
      projModelBaseChange (algebraMap R R') W =
      Spec.map (CommRingCat.ofHom
        (((sChartBaseChange (R' := R') W j).toRingHom).comp
          ((chartCoordEquiv W j).symm.toRingHom))) ≫
        (modelChartCover W).openCover.f j := by
    rw [show projModelBaseChange (algebraMap R R') W =
      Proj.map (baseChangeGradedHom (algebraMap R R') W)
        (baseChangeGradedHom_irrelevant_le (algebraMap R R') W) from rfl]
    rw [Proj.awayι_comp_map (baseChangeGradedHom (algebraMap R R') W)
      (baseChangeGradedHom_irrelevant_le (algebraMap R R') W) one_pos _
      (mk_X_mem_quotientGrading_one W j)]
    rw [← Category.assoc, ← piece_fst_natural (R' := R') W j]
    rfl
  refine (IsPullback.of_right ?s ?p (isPullback_coverPiece (R' := R') W j)).flip
  case p =>
    refine Limits.pullback.hom_ext ?_ ?_
    · unfold projModelBaseChangeLift
      rw [Category.assoc, Category.assoc, Limits.pullback.lift_fst]
      rw [← (isPullback_coverPiece (R' := R') W j).w]
      rw [← Category.assoc, hfst, Category.assoc, hbcfst]
    · unfold projModelBaseChangeLift
      rw [Category.assoc, Category.assoc, Limits.pullback.lift_snd]
      rw [show (Scheme.Pullback.openCoverOfLeft ((modelChartCover W).openCover)
          (projModelπ W) (Spec.map (CommRingCat.ofHom (algebraMap R R')))).f j ≫
          Limits.pullback.snd (projModelπ W)
            (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
          Limits.pullback.snd ((modelChartCover W).openCover.f j ≫ projModelπ W)
            (Spec.map (CommRingCat.ofHom (algebraMap R R'))) from by
        rw [coverPiece_f_eq (R' := R') W j, Category.assoc,
          Limits.pullbackRightPullbackFstIso_inv_snd_snd]]
      rw [hsnd, Category.assoc]
      exact (theta_awayι_π (R' := R') W j).symm
  case s =>
    rw [show (isPullback_piece (R' := R') W j).isoPullback.hom ≫
        Limits.pullback.fst ((modelChartCover W).openCover.f j ≫ projModelπ W)
          (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
        Spec.map (CommRingCat.ofHom
          (((sChartBaseChange (R' := R') W j).toRingHom).comp
            ((chartCoordEquiv W j).symm.toRingHom))) from hfst]
    rw [show projModelBaseChangeLift (algebraMap R R') W ≫
        Limits.pullback.fst (projModelπ W)
          (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
        projModelBaseChange (algebraMap R R') W from Limits.pullback.lift_fst _ _ _]
    refine (isPullback_projModelBaseChange_chart (R' := R') W j).of_iso
      (thetaIso (R' := R') W j).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      rw [piece_fst_natural (R' := R') W j, ← Category.assoc, Iso.inv_hom_id,
        Category.id_comp]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← Category.assoc,
        Iso.inv_hom_id, Category.id_comp]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem projModelBaseChangeLift_isIso (W : WeierstrassCurve R) :
    IsIso (projModelBaseChangeLift (algebraMap R R') W) := by
  show (MorphismProperty.isomorphisms Scheme)
    (projModelBaseChangeLift (algebraMap R R') W)
  rw [IsZariskiLocalAtTarget.iff_of_openCover
    (P := MorphismProperty.isomorphisms Scheme)
    (Scheme.Pullback.openCoverOfLeft ((modelChartCover W).openCover)
      (projModelπ W) (Spec.map (CommRingCat.ofHom (algebraMap R R'))))]
  intro i
  haveI : DecidableEq ((Scheme.Pullback.openCoverOfLeft (modelChartCover W).openCover
      (projModelπ W) (Spec.map (CommRingCat.ofHom
        (algebraMap R R')))).toPreZeroHypercover.1) :=
    inferInstanceAs (DecidableEq (Fin 3))
  have hcosp : (modelChartCover W).openCover.f i ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0)))) :=
    awayι_projModelπ W i
  have h := isPullback_lift_piece (R' := R') W i
  have hcomp : Scheme.Cover.pullbackHom
      (Scheme.Pullback.openCoverOfLeft ((modelChartCover W).openCover)
        (projModelπ W) (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
      (projModelBaseChangeLift (algebraMap R R') W) i =
      h.isoPullback.inv ≫ (isPullback_piece (R' := R') W i).isoPullback.hom := by
    refine (Iso.eq_inv_comp _).mpr ?_
    exact h.isoPullback_hom_snd
  rw [hcomp]
  exact inferInstanceAs (IsIso (h.isoPullback.symm ≪≫
    (isPullback_piece (R' := R') W i).isoPullback).hom)

/-- **(T-A5a, headline)** The projective model of `W.map f` is the base change of the
projective model of `W` along `Spec f`. -/
theorem isPullback_projModelBaseChange (W : WeierstrassCurve R) :
    IsPullback (projModelBaseChange (algebraMap R R') W)
      (projModelπ (W.map (algebraMap R R'))) (projModelπ W)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  haveI := projModelBaseChangeLift_isIso (R' := R') W
  exact IsPullback.of_iso_pullback ⟨projModelBaseChange_π (algebraMap R R') W⟩
    (asIso (projModelBaseChangeLift (algebraMap R R') W))
    (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)

end TensorComparison

end BaseChangeGraded

/-- The section at infinity lands entirely in the `Y`-chart. -/
lemma projModelZero_preimage_yChart (W : WeierstrassCurve R) :
    projModelZero W ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))) = ⊤ := by
  unfold projModelZero
  rw [Proj.fromOfGlobalSections_preimage_basicOpen (hn := one_pos)
    (hr := mk_X_mem_quotientGrading_one W 1)]
  rw [show ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
      (projModelZeroEval W)) ((quotientGradingHom (projIdeal W))
        (MvPolynomial.X 1)) = 1 from by
    rw [RingHom.comp_apply]
    rw [show (projModelZeroEval W) ((quotientGradingHom (projIdeal W))
        (MvPolynomial.X 1)) = 1 from by
      show (projModelZeroEval W) (Ideal.Quotient.mk _ (MvPolynomial.X 1)) = 1
      rw [projModelZeroEval_mk]
      simp]
    rw [map_one]]
  simp

/-- The chart factorisation of the section at infinity through the `Y`-chart. -/
noncomputable def projModelZeroChart (W : WeierstrassCurve R) :
    Spec (.of R) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))) := by
  have hrange : Set.range ⇑(projModelZero W) ⊆
      Set.range ⇑(Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        (mk_X_mem_quotientGrading_one W 1) one_pos) := by
    rw [show Set.range ⇑(Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        (mk_X_mem_quotientGrading_one W 1) one_pos) =
        (Proj.basicOpen (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)) :
          Set (Proj (quotientGrading (projIdeal W)))) from by
      rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]]
    rintro _ ⟨x, rfl⟩
    have h := projModelZero_preimage_yChart W
    have hx : x ∈ (projModelZero W ⁻¹ᵁ (Proj.basicOpen
        (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))) := by
      rw [h]
      trivial
    exact hx
  exact IsOpenImmersion.lift _ _ hrange

@[reassoc]
lemma projModelZeroChart_fac (W : WeierstrassCurve R) :
    projModelZeroChart W ≫ Proj.awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
      (mk_X_mem_quotientGrading_one W 1) one_pos = projModelZero W :=
  IsOpenImmersion.lift_fac _ _ _

/-- The chart factorisation of the zero section is a retraction of the chart's
`R`-structuring. -/
lemma projModelZeroChart_comp_χ (W : WeierstrassCurve R) :
    projModelZeroChart W ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))).comp
      ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0)))) =
    𝟙 (Spec (.of R)) := by
  rw [← awayι_projModelπ W 1, ← Category.assoc, projModelZeroChart_fac]
  exact projModelZero_projModelπ W

/-- Evaluation of the `Y`-chart at the point at infinity `[0:1:0]`. -/
noncomputable def zeroChartHom (W : WeierstrassCurve R) :
    Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)) →+* R :=
  (Localization.awayLift (projModelZeroEval W)
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
    (isUnit_iff_exists_inv.mpr ⟨1, by
      rw [show (projModelZeroEval W) ((quotientGradingHom (projIdeal W))
          (MvPolynomial.X 1)) = 1 from by
        show (projModelZeroEval W) (Ideal.Quotient.mk _ (MvPolynomial.X 1)) = 1
        rw [projModelZeroEval_mk]
        simp]
      rw [one_mul]⟩)).comp
    (HomogeneousLocalization.valRingHom _)

lemma zeroChartHom_mk (W : WeierstrassCurve R) {i : ℕ}
    (hs : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) ∈
      quotientGrading (projIdeal W) i) (n : ℕ) (a : projCoordRing W)
    (ha : a ∈ quotientGrading (projIdeal W) (n • i)) :
    zeroChartHom W (HomogeneousLocalization.Away.mk _ hs n a ha) =
      projModelZeroEval W a := by
  rw [zeroChartHom, RingHom.comp_apply,
    HomogeneousLocalization.valRingHom_apply, Away.val_mk]
  rw [Localization.awayLift_mk (hv := by
    rw [show (projModelZeroEval W) ((quotientGradingHom (projIdeal W))
        (MvPolynomial.X 1)) = 1 from by
      show (projModelZeroEval W) (Ideal.Quotient.mk _ (MvPolynomial.X 1)) = 1
      rw [projModelZeroEval_mk]
      simp]
    rw [one_mul])]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The piece-level comparison for the glue step. -/
private lemma glue_pieceY (W : WeierstrassCurve R) :
    (Proj.openCoverOfMapIrrelevantEqTop (quotientGrading (projIdeal W))
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W))
      (projModelZeroEval_irrelevant_map_top W)).f
      ⟨1, (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1),
        one_pos, mk_X_mem_quotientGrading_one W 1⟩ ≫
      Spec.map (CommRingCat.ofHom (zeroChartHom W)) ≫
      Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        (mk_X_mem_quotientGrading_one W 1) one_pos =
    Proj.toBasicOpenOfGlobalSections (quotientGrading (projIdeal W))
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W)) rfl
      one_pos (mk_X_mem_quotientGrading_one W 1) ≫
      (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))).ι := by
  rw [show Proj.awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
      (mk_X_mem_quotientGrading_one W 1) one_pos =
      (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        (mk_X_mem_quotientGrading_one W 1) one_pos).inv ≫
      (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))).ι from
    (Proj.basicOpenIsoSpec_inv_ι _ _ _ _).symm]
  rw [Proj.toBasicOpenOfGlobalSections]
  rw [← Category.assoc, ← Category.assoc]
  refine congrArg (· ≫ (Proj.basicOpen (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))).ι) ?_
  rw [Iso.cancel_iso_inv_right]
  rw [show (Proj.openCoverOfMapIrrelevantEqTop (quotientGrading (projIdeal W))
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W))
      (projModelZeroEval_irrelevant_map_top W)).f
      ⟨1, (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1),
        one_pos, mk_X_mem_quotientGrading_one W 1⟩ =
    Scheme.Opens.ι ((Spec (CommRingCat.of R)).basicOpen
      (((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))) from rfl]
  rw [Iso.eq_inv_comp, Scheme.isoOfEq_hom_ι_assoc]
  have hζ : Spec.map (CommRingCat.ofHom (zeroChartHom W)) =
      (Spec (CommRingCat.of R)).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (zeroChartHom W) ≫
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv) := by
    rw [Spec.map_comp, toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]
  rw [hζ, ← morphismRestrict_ι_assoc]
  congr 1
  rw [← basicOpenIsoSpecAway_hom_SpecMap_assoc, Iso.cancel_iso_hom_left, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  have hval : (HomogeneousLocalization.valRingHom
      (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))) :
        Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)) →+*
        Localization.Away ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))) =
      algebraMap _ _ :=
    RingHom.ext fun y => rfl
  rw [zeroChartHom, hval, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))
  rw [IsLocalization.map_comp, RingHom.comp_assoc, IsLocalization.Away.lift_comp,
    RingHom.comp_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The `Spec` of the chart evaluation composed with the chart inclusion is the
section at infinity (the glue step of the zero-leg). -/
lemma spec_zeroChartHom_awayι (W : WeierstrassCurve R) :
    Spec.map (CommRingCat.ofHom (zeroChartHom W)) ≫
      Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        (mk_X_mem_quotientGrading_one W 1) one_pos = projModelZero W := by
  have hone : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
      (projModelZeroEval W)) ((quotientGradingHom (projIdeal W))
        (MvPolynomial.X 1)) = 1 := by
    rw [RingHom.comp_apply]
    rw [show (projModelZeroEval W) ((quotientGradingHom (projIdeal W))
        (MvPolynomial.X 1)) = 1 from by
      show (projModelZeroEval W) (Ideal.Quotient.mk _ (MvPolynomial.X 1)) = 1
      rw [projModelZeroEval_mk]
      simp]
    rw [map_one]
  have htop : (Spec (.of R)).basicOpen
      (((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))) = ⊤ := by
    rw [hone]
    simp
  haveI : IsIso ((Spec (.of R)).basicOpen
      (((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))).ι := by
    rw [htop]
    exact ⟨(Spec (.of R)).topIso.inv, (Spec (.of R)).topIso.hom_inv_id,
      (Spec (.of R)).topIso.inv_hom_id⟩
  rw [← cancel_epi (((Spec (.of R)).basicOpen
      (((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))).ι)]
  show (Proj.openCoverOfMapIrrelevantEqTop (quotientGrading (projIdeal W))
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W))
      (projModelZeroEval_irrelevant_map_top W)).f
      ⟨1, (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1),
        one_pos, mk_X_mem_quotientGrading_one W 1⟩ ≫
      Spec.map (CommRingCat.ofHom (zeroChartHom W)) ≫
      Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        (mk_X_mem_quotientGrading_one W 1) one_pos =
    (Proj.openCoverOfMapIrrelevantEqTop (quotientGrading (projIdeal W))
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W))
      (projModelZeroEval_irrelevant_map_top W)).f
      ⟨1, (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1),
        one_pos, mk_X_mem_quotientGrading_one W 1⟩ ≫ projModelZero W
  conv_rhs => rw [projModelZero, Proj.fromOfGlobalSections]
  rw [Scheme.Cover.ι_glueMorphisms]
  exact glue_pieceY W

/-- The `Y`-chart factorisation of the zero section is `Spec` of the evaluation
at the point at infinity. -/
lemma projModelZeroChart_eq_spec (W : WeierstrassCurve R) :
    projModelZeroChart W = Spec.map (CommRingCat.ofHom (zeroChartHom W)) := by
  rw [← cancel_mono (Proj.awayι (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
    (mk_X_mem_quotientGrading_one W 1) one_pos),
    projModelZeroChart_fac, spec_zeroChartHom_awayι]

/-- The point-at-infinity evaluation is natural in the base ring. -/
lemma projModelZeroEval_baseChangeGradedHom {R' : Type u} [CommRing R'] [Algebra R R']
    (W : WeierstrassCurve R) (x : projCoordRing W) :
    projModelZeroEval (W.map (algebraMap R R'))
      ((baseChangeGradedHom (algebraMap R R') W) x) =
      algebraMap R R' (projModelZeroEval W x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [show ((baseChangeGradedHom (algebraMap R R') W)
      (Ideal.Quotient.mk (projIdeal W).toIdeal p)) =
      Ideal.Quotient.mk (projIdeal (W.map (algebraMap R R'))).toIdeal
        (MvPolynomial.map (algebraMap R R') p) from
    quotientGradingMap_mk _ _ _ _ p]
  rw [projModelZeroEval_mk, projModelZeroEval_mk, MvPolynomial.eval_map]
  have h2 := MvPolynomial.eval₂_comp_left (algebraMap R R') (RingHom.id R)
    (fun i : Fin 3 => if i = 1 then (1 : R) else 0) p
  rw [MvPolynomial.eval₂_id, RingHom.comp_id] at h2
  rw [h2]
  congr 1
  funext i
  by_cases hi : i = 1 <;> simp [hi]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the section at infinity under base change (T-A5b zero-leg). -/
lemma projModelZero_baseChange {R' : Type u} [CommRing R'] [Algebra R R']
    (W : WeierstrassCurve R) :
    projModelZero (W.map (algebraMap R R')) ≫
        projModelBaseChange (algebraMap R R') W =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ projModelZero W := by
  rw [← projModelZeroChart_fac (W.map (algebraMap R R')), Category.assoc]
  rw [show projModelBaseChange (algebraMap R R') W =
    Proj.map (baseChangeGradedHom (algebraMap R R') W)
      (baseChangeGradedHom_irrelevant_le (algebraMap R R') W) from rfl]
  rw [← awayι_awayCongr (W.map (algebraMap R R'))
    (baseChangeGradedHom_mk_X (R' := R') W 1)
    ((baseChangeGradedHom (algebraMap R R') W).2
      (mk_X_mem_quotientGrading_one W 1))]
  rw [Category.assoc]
  rw [Proj.awayι_comp_map (baseChangeGradedHom (algebraMap R R') W)
    (baseChangeGradedHom_irrelevant_le (algebraMap R R') W) one_pos _
    (mk_X_mem_quotientGrading_one W 1)]
  rw [← projModelZeroChart_fac W, ← Category.assoc, ← Category.assoc,
    ← Category.assoc]
  refine congrArg (· ≫ Proj.awayι (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
    (mk_X_mem_quotientGrading_one W 1) one_pos) ?_
  rw [projModelZeroChart_eq_spec, projModelZeroChart_eq_spec,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  refine congrArg Spec.map ?_
  ext x
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 1)
    (x : Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
    Function.comp_apply]
  simp only [RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom, RingHom.coe_coe]
  rw [HomogeneousLocalization.Away.map_mk, awayCongr_mk, zeroChartHom_mk,
    zeroChartHom_mk, projModelZeroEval_baseChangeGradedHom]

end Points

/-- **(T-A2)** The constructed model satisfies its interface.
Source: KM 2.2; Loeffler §3.3 Def 3.3.3. -/
theorem projModel_isWeierstrassModel (W : WeierstrassCurve R) :
    IsWeierstrassModel W (projModel W) (projModelπ W) (projModelZero W) := by
  refine ⟨inferInstance, ?_, projModelZero_projModelπ W, ?_⟩
  · exact projModelπ_lfp W
  · exact fun hell K _ _ => projModel_points W hell K


/-- **⚠ DEPRECATED-FALSE — DO NOT PROVE (coordinator §4, 2026-07-07; v9.4 retirement order).**
This statement is refuted by `b2_log.jsonl` (2026-07-07, T-A4): over `R = ℚ` the 2-isogenous
non-isomorphic positive-rank pair `y² = x³ − 36x` / `y² = x³ + 144x` satisfies all hypotheses
(the points clause is a bare pointed `Equiv` — cardinality only, and isogeny + duals give equal
cardinalities over every field) while the conclusion would force `E ≅ E'`. Kept only as a
tombstone until the owner deletes it; the CORRECT uniqueness is the comparison theorem
**T-W7.1b** (`pointedIso_exists_variableChange`, ModelVariableChange.lean), which supersedes
this (b2 fix-option 3).

**(T-A4, uniqueness of the model — KM 2.2.5 scope)** For **elliptic** `W`, any two
pointed **smooth** models satisfying `IsWeierstrassModel W` are isomorphic over
`Spec R`, compatibly with the base points.

ADVERSARIAL FIX (2026-07-05, DEF-7): ellipticity and smoothness hypotheses are
REQUIRED — without them `V(F)` and its first-order thickening `V(F²)` both satisfy
the field-points interface (reduced `Spec K` cannot see nilpotents) yet are not
isomorphic; KM 2.2.5's uniqueness is among smooth pointed models of an elliptic
curve, and the previous unconditional statement was strictly stronger than the
source and false. Source: KM 2.2.5 ⧗ (Riemann–Roch black box; Hida GME §2.2.6
"Moduli of Weierstrass Type" as interim proof-bearing source). -/
theorem isWeierstrassModel_unique (W : WeierstrassCurve R) [W.IsElliptic]
    {X X' : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} {x₀ : Spec (.of R) ⟶ X} {f' : X' ⟶ Spec (.of R)}
    {x₀' : Spec (.of R) ⟶ X'}
    (hs : SmoothOfRelativeDimension 1 f) (hs' : SmoothOfRelativeDimension 1 f')
    (h : IsWeierstrassModel W X f x₀)
    (h' : IsWeierstrassModel W X' f' x₀') :
    ∃ e : X ≅ X', e.hom ≫ f' = f ∧ x₀ ≫ e.hom = x₀' := by sorry

end ModularCurves
