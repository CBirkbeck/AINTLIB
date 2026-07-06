import ModularCurves.ForMathlib.GradedQuotient
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous

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
noncomputable def projModel (W : WeierstrassCurve R) : Scheme.{u} :=
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

end ProjModel

/-- **(T-A2)** The constructed model satisfies its interface.
Source: KM 2.2; Loeffler §3.3 Def 3.3.3. -/
theorem projModel_isWeierstrassModel (W : WeierstrassCurve R) :
    IsWeierstrassModel W (projModel W) (projModelπ W) (projModelZero W) := by
  refine ⟨inferInstance, ?_, projModelZero_projModelπ W, ?_⟩
  · -- lfp (T-A2d): via the three affine charts `(Away (mk Xᵢ))₀ ≅ R[u,v]/(F̃ᵢ)`
    sorry
  · -- pointed K-points for elliptic W (T-A2e): via the chart description +
    -- mathlib's `Projective.Point.toAffineAddEquiv`
    sorry

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
