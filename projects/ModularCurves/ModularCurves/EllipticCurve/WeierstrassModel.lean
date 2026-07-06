import ModularCurves.ForMathlib.GradedQuotient
import ModularCurves.ForMathlib.ProjClosedImmersion
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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

/-- **(T-A2)** The section at infinity `[0:1:0]` of the projective Weierstrass model,
via `Proj.fromOfGlobalSections` at the evaluation `X ↦ 0, Y ↦ 1, Z ↦ 0`. -/
noncomputable def projModelZero (W : WeierstrassCurve R) : Spec (.of R) ⟶ projModel W :=
  Proj.fromOfGlobalSections _
    ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W)) (by
      rw [Ideal.eq_top_iff_one]
      have h1 : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (projModelZeroEval W))
          (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X 1)) = 1 := by
        rw [RingHom.comp_apply, projModelZeroEval_mk]
        simp
      rw [← h1]
      exact Ideal.mem_map_of_mem _ (mk_Y_mem_irrelevant W))

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

private lemma ringHom_eq_aeval {σ : Type} {K : Type u} [CommRing K] [Algebra R K]
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

private lemma chart_hom_aeval (W : WeierstrassCurve R) (i : Fin 3) {K : Type u}
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

set_option backward.isDefEq.respectTransparency false in
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
    simp only [hz, mul_zero, zero_mul, zero_pow, add_zero, zero_add, sub_zero] at hv
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

end Points

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
  sorry

/-- **(T-A2)** The constructed model satisfies its interface.
Source: KM 2.2; Loeffler §3.3 Def 3.3.3. -/
theorem projModel_isWeierstrassModel (W : WeierstrassCurve R) :
    IsWeierstrassModel W (projModel W) (projModelπ W) (projModelZero W) := by
  refine ⟨inferInstance, ?_, projModelZero_projModelπ W, ?_⟩
  · exact projModelπ_lfp W
  · exact fun hell K _ _ => projModel_points W hell K

/-- **(T-A3)** The projective model of an *elliptic* Weierstrass curve (unit discriminant) is
smooth of relative dimension 1 over the base.
Source: Loeffler §3.3 ("If `Δ(α,β) ∈ Γ(S,O_S)ˣ`, this is an elliptic curve over `S`");
KM 2.2.4; Silverman III.1.4(a). -/
theorem projModel_smooth (W : WeierstrassCurve R) [W.IsElliptic] :
    SmoothOfRelativeDimension 1 (projModelπ W) := by sorry

/-- **(T-A4, uniqueness of the model — KM 2.2.5 scope)** For **elliptic** `W`, any two
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
