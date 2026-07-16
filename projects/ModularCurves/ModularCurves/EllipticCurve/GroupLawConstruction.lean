import ModularCurves.EllipticCurve.PointsDictionary
import ModularCurves.EllipticCurve.ModelVariableChange
import ModularCurves.EllipticCurve.AdditionBaseChange
import ModularCurves.ForMathlib.ProjToSpecZero
import ModularCurves.ForMathlib.ProjFromGlobalSectionsMap
import ModularCurves.ForMathlib.ProjMapScaling
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.RingTheory.Localization.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# The group law on the projective Weierstrass model, uniformly over every ring

**(T-W7 skeleton, lanes P0/P1 — `/develop --decompose` 2026-07-07.)** Negation and
multiplication as *morphisms of schemes* on `projModel W`, for every Weierstrass curve `W`
over every ring `R` (with unit discriminant), via the **Bosma–Lenstra complete system of two
addition laws of bidegree (2,2)** — the laws of the lines `Z = 0` (exceptional locus: the
diagonal) and `Y = 0` (exceptional: `P₁ − P₂ ∈ E ∩ {Y = 0}`), whose exceptional loci are
disjoint over every field since `O = (0:1:0) ∉ {Y = 0}`. The group axioms are stated at the
`Over (Spec R)` monoidal level; their proofs go through the field-points dictionary + the
extensionality principle of `PointsDictionary.lean` over the (reduced, universal) atlas, then
transport to every `R` by the base-change naturality `mulModelHom_map` along the classifying
map — no rigidity, no cohomology.

Sources: Bosma–Lenstra, *Complete systems of two addition laws for elliptic curves*, JNT 53
(1995) 229–240 (Thm 1, Thm 2, §5 formulas; local `refs/`, verbatim quotes in
`.mathlib-quality/tw7-source-quotes.md`); Lange–Ruppert, Invent. Math. 79 (1985); reviewer
round 1 §Q1; audits A2/A5/A6.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  WeierstrassCurve

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-! ## Lane P0: negation -/

-- **(T-W7.0a)** `universalWeierstrass_Δ_ne_zero`, `instance : IsDomain WeierstrassAtlasRing`, and
-- `instance : IsNoetherianRing WeierstrassAtlasRing` were moved upstream to
-- `Moduli/WeierstrassAtlas.lean` (single source; deduplicated per the 2026-07-07 coordinator
-- directive — they existed here and in `Moduli/PointsDictionary.lean`) and are inherited here.

section NegationConstruction

open MvPolynomial HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A graded ring homomorphism maps the irrelevant ideal into the irrelevant ideal. -/
lemma irrelevant_map_le {ι σ τ A B : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
    {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) :
    HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜) ≤ HomogeneousIdeal.irrelevant ℬ := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map,
    Ideal.map_le_iff_le_comap, HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi x hx
  exact HomogeneousIdeal.mem_irrelevant_of_mem _ hi (f.map_mem hx)

/-- Equality of `Proj.map`s from equal graded homomorphisms (the irrelevant-ideal
hypotheses are propositions, so they may differ). Shared helper, also consumed by
`EllipticCurve/NegModelBaseChange.lean` (which imports this file). -/
lemma Proj_map_congr {A B σ τ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    {f g : 𝒜 →+*ᵍ ℬ} (h : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    Proj.map f hf = Proj.map g hg := by subst h; rfl

/-- The negation substitution vector on `R[X,Y,Z]`: `X ↦ X`, `Y ↦ −Y − a₁X − a₃Z`,
`Z ↦ Z` (Silverman III.2.3 — the involution of the plane cubic fixing the `x`-coordinate). -/
noncomputable def negVec (W : WeierstrassCurve R) : Fin 3 → MvPolynomial (Fin 3) R :=
  ![X 0, -X 1 - C W.a₁ * X 0 - C W.a₃ * X 2, X 2]

/-- Each entry of the negation substitution is homogeneous of degree `1`. -/
lemma negVec_isHomogeneous (W : WeierstrassCurve R) (i : Fin 3) :
    (negVec W i).IsHomogeneous 1 := by
  fin_cases i <;>
    simp only [negVec]
  · exact isHomogeneous_X R 0
  · exact ((isHomogeneous_X R 1).neg.sub ((isHomogeneous_X R 0).C_mul W.a₁)).sub
      ((isHomogeneous_X R 2).C_mul W.a₃)
  · exact isHomogeneous_X R 2

/-- Negation fixes the Weierstrass cubic *exactly*: substituting `Y ↦ −Y−a₁X−a₃Z` (and
`X, Z` unchanged) leaves the projective polynomial invariant. -/
lemma negVec_polynomial (W : WeierstrassCurve R) :
    aeval (negVec W) W.toProjective.polynomial = W.toProjective.polynomial := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, negVec,
    MvPolynomial.algebraMap_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The negation substitution is an involution on each variable. -/
lemma negVec_involutive (W : WeierstrassCurve R) (i : Fin 3) :
    aeval (negVec W) (negVec W i) = X i := by
  fin_cases i
  · show aeval (negVec W) (negVec W 0) = X 0
    simp [negVec]
  · show aeval (negVec W) (negVec W 1) = X 1
    rw [negVec]
    simp only [Matrix.cons_val_one, Matrix.head_cons, map_sub, map_mul, map_neg, aeval_X,
      aeval_C, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      MvPolynomial.algebraMap_eq]
    ring
  · show aeval (negVec W) (negVec W 2) = X 2
    simp [negVec]

/-- The negation ring endomorphism is an involution on all of `R[X,Y,Z]`. -/
lemma negRingHom_involutive (W : WeierstrassCurve R) (p : MvPolynomial (Fin 3) R) :
    aeval (negVec W) (aeval (negVec W) p) = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, aeval_X, map_mul, hp, negVec_involutive]

/-- The negation as a graded ring endomorphism of the homogeneous coordinate ring
`R[X,Y,Z]` (degree-preserving because each substituted variable is homogeneous of
degree `1`). -/
noncomputable def negGradedPoly (W : WeierstrassCurve R) :
    homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) R where
  toRingHom := (aeval (negVec W)).toRingHom
  map_mem {n x} hx := by
    have h := ((mem_homogeneousSubmodule _ _).mp hx).aeval (negVec W) (negVec_isHomogeneous W)
    rw [one_mul] at h
    exact (mem_homogeneousSubmodule _ _).mpr h

/-- Negation maps the Weierstrass ideal into itself (in fact fixes its generator). -/
lemma negGradedPoly_comap (W : WeierstrassCurve R) :
    (projIdeal W).toIdeal ≤ (projIdeal W).toIdeal.comap (negGradedPoly W).toRingHom := by
  rw [projIdeal_toIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
    Ideal.mem_comap]
  show aeval (negVec W) W.toProjective.polynomial ∈ _
  rw [negVec_polynomial]
  exact Ideal.mem_span_singleton_self _

/-- The negation as a graded ring endomorphism of the quotient coordinate ring
`R[X,Y,Z]/(W)`. -/
noncomputable def negGradedQuot (W : WeierstrassCurve R) :
    quotientGrading (projIdeal W) →+*ᵍ quotientGrading (projIdeal W) :=
  quotientGradingMap (negGradedPoly W) (projIdeal W) (projIdeal W) (negGradedPoly_comap W)

/-- The negation endomorphism of the quotient coordinate ring is an involution. -/
lemma negGradedQuot_involutive (W : WeierstrassCurve R) (x : projCoordRing W) :
    negGradedQuot W (negGradedQuot W x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [negGradedQuot, quotientGradingMap_mk, quotientGradingMap_mk]
  exact congrArg (Ideal.Quotient.mk _) (negRingHom_involutive W a)

/-- The negation endomorphism composed with itself is the identity. -/
lemma negGradedQuot_comp_self (W : WeierstrassCurve R) :
    (negGradedQuot W).comp (negGradedQuot W) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x ↦ negGradedQuot_involutive W x

/-- The irrelevant-ideal hypothesis of `Proj.map` for negation, discharged via the
involution: `f` maps the irrelevant ideal into itself, and `f = f⁻¹`. -/
lemma negGradedQuot_irrelevant_le (W : WeierstrassCurve R) :
    (quotientGrading (projIdeal W))₊ ≤
      ((quotientGrading (projIdeal W))₊).map (negGradedQuot W) := by
  conv_lhs => rw [← HomogeneousIdeal.map_id (I := (quotientGrading (projIdeal W))₊),
    ← negGradedQuot_comp_self W, HomogeneousIdeal.map_comp]
  exact HomogeneousIdeal.map_mono _ (irrelevant_map_le (negGradedQuot W))

/-- Negation fixes the degree-`0` structural image of `R`: restricting `negGradedQuot` to
degree `0` and precomposing with the base map `algebraMapGradeZero` recovers the base map
(negation is an `R`-algebra endomorphism — it fixes constants). This is the ring-level input
that makes `negModelHom` a morphism over `Spec R`. -/
lemma negGradedQuot_algebraMapGradeZero (W : WeierstrassCurve R) :
    (gradedRingHomZero (negGradedQuot W)).comp (algebraMapGradeZero (projIdeal W)) =
      algebraMapGradeZero (projIdeal W) := by
  refine RingHom.ext fun r ↦ Subtype.ext ?_
  simp only [RingHom.coe_comp, Function.comp_apply, gradedRingHomZero_coe]
  show negGradedQuot W (algebraMap R (projCoordRing W) r) = algebraMap R (projCoordRing W) r
  have hmk : algebraMap R (projCoordRing W) r =
      Ideal.Quotient.mk (projIdeal W).toIdeal (C r) := by
    rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing W),
      RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
  rw [hmk, negGradedQuot, quotientGradingMap_mk]
  exact congrArg (Ideal.Quotient.mk _)
    (show aeval (negVec W) (C r) = C r by rw [aeval_C, MvPolynomial.algebraMap_eq])

/-! ### The `(−1)`-rescaling `ρ`: negate all variables

`ρ = allNegGradedQuot` (`X, Y, Z ↦ −X, −Y, −Z`, i.e. `a ↦ (−1)^{deg a} a`) is the auxiliary
graded automorphism through which `negModelHom_zero` discharges the projective rescaling
`[0:−1:0] = [0:1:0]`. Built exactly parallel to `negGradedQuot`. -/

/-- Negate all three variables `X, Y, Z ↦ −X, −Y, −Z` — the `(−1)`-rescaling. -/
noncomputable def allNegVec (_W : WeierstrassCurve R) : Fin 3 → MvPolynomial (Fin 3) R :=
  ![-X 0, -X 1, -X 2]

lemma allNegVec_isHomogeneous (W : WeierstrassCurve R) (i : Fin 3) :
    (allNegVec W i).IsHomogeneous 1 := by
  fin_cases i <;>
    simp only [allNegVec]
  · exact (isHomogeneous_X R 0).neg
  · exact (isHomogeneous_X R 1).neg
  · exact (isHomogeneous_X R 2).neg

/-- Negating all variables sends the (degree-`3`, odd) Weierstrass cubic to its negative,
hence maps the Weierstrass ideal into itself. -/
lemma allNegVec_polynomial (W : WeierstrassCurve R) :
    aeval (allNegVec W) W.toProjective.polynomial = -W.toProjective.polynomial := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, allNegVec,
    MvPolynomial.algebraMap_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

lemma allNegVec_involutive (W : WeierstrassCurve R) (i : Fin 3) :
    aeval (allNegVec W) (allNegVec W i) = X i := by
  fin_cases i
  · show aeval (allNegVec W) (allNegVec W 0) = X 0
    simp [allNegVec]
  · show aeval (allNegVec W) (allNegVec W 1) = X 1
    simp [allNegVec]
  · show aeval (allNegVec W) (allNegVec W 2) = X 2
    simp [allNegVec]

lemma allNegRingHom_involutive (W : WeierstrassCurve R) (p : MvPolynomial (Fin 3) R) :
    aeval (allNegVec W) (aeval (allNegVec W) p) = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, aeval_X, map_mul, hp, allNegVec_involutive]

/-- Negate-all-variables as a graded endomorphism of `R[X,Y,Z]`. -/
noncomputable def allNegGradedPoly (W : WeierstrassCurve R) :
    homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) R where
  toRingHom := (aeval (allNegVec W)).toRingHom
  map_mem {n x} hx := by
    have h := ((mem_homogeneousSubmodule _ _).mp hx).aeval (allNegVec W)
      (allNegVec_isHomogeneous W)
    rw [one_mul] at h
    exact (mem_homogeneousSubmodule _ _).mpr h

lemma allNegGradedPoly_comap (W : WeierstrassCurve R) :
    (projIdeal W).toIdeal ≤ (projIdeal W).toIdeal.comap (allNegGradedPoly W).toRingHom := by
  rw [projIdeal_toIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
    Ideal.mem_comap]
  show aeval (allNegVec W) W.toProjective.polynomial ∈ _
  rw [allNegVec_polynomial]
  exact neg_mem (Ideal.mem_span_singleton_self _)

/-- The `(−1)`-rescaling automorphism `ρ` of the quotient coordinate ring. -/
noncomputable def allNegGradedQuot (W : WeierstrassCurve R) :
    quotientGrading (projIdeal W) →+*ᵍ quotientGrading (projIdeal W) :=
  quotientGradingMap (allNegGradedPoly W) (projIdeal W) (projIdeal W) (allNegGradedPoly_comap W)

lemma allNegGradedQuot_involutive (W : WeierstrassCurve R) (x : projCoordRing W) :
    allNegGradedQuot W (allNegGradedQuot W x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [allNegGradedQuot, quotientGradingMap_mk, quotientGradingMap_mk]
  exact congrArg (Ideal.Quotient.mk _) (allNegRingHom_involutive W a)

lemma allNegGradedQuot_comp_self (W : WeierstrassCurve R) :
    (allNegGradedQuot W).comp (allNegGradedQuot W) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x ↦ allNegGradedQuot_involutive W x

lemma allNegGradedQuot_irrelevant_le (W : WeierstrassCurve R) :
    (quotientGrading (projIdeal W))₊ ≤
      ((quotientGrading (projIdeal W))₊).map (allNegGradedQuot W) := by
  conv_lhs => rw [← HomogeneousIdeal.map_id (I := (quotientGrading (projIdeal W))₊),
    ← allNegGradedQuot_comp_self W, HomogeneousIdeal.map_comp]
  exact HomogeneousIdeal.map_mono _ (irrelevant_map_le (allNegGradedQuot W))

/-- On global sections, evaluation at infinity kills the difference between the two negations:
`projModelZeroEval ∘ negGradedQuot = projModelZeroEval ∘ allNegGradedQuot` — both are evaluation
at `(0, −1, 0)`. This is the ring-level identity feeding the `negModelHom_zero` route. -/
lemma projModelZeroEval_neg_eq_allNeg (W : WeierstrassCurve R) :
    (projModelZeroEval W).comp (negGradedQuot W).toRingHom =
      (projModelZeroEval W).comp (allNegGradedQuot W).toRingHom := by
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [RingHom.comp_apply]
  show projModelZeroEval W (negGradedQuot W (Ideal.Quotient.mk _ p)) =
    projModelZeroEval W (allNegGradedQuot W (Ideal.Quotient.mk _ p))
  rw [negGradedQuot, allNegGradedQuot, quotientGradingMap_mk, quotientGradingMap_mk,
    projModelZeroEval_mk, projModelZeroEval_mk]
  show (aeval (fun i : Fin 3 ↦ if i = 1 then (1 : R) else 0)) (aeval (negVec W) p) =
       (aeval (fun i : Fin 3 ↦ if i = 1 then (1 : R) else 0)) (aeval (allNegVec W) p)
  rw [comp_aeval_apply, comp_aeval_apply]
  refine congrArg (fun g ↦ aeval g p) (funext fun i ↦ ?_)
  fin_cases i <;>
    simp [negVec, allNegVec]

/-- The "negate all variables" substitution scales a degree-`d` homogeneous polynomial by
`(-1)^d`. -/
lemma allNegVec_smul_of_homogeneous (W : WeierstrassCurve R) {d : ℕ}
    {p : MvPolynomial (Fin 3) R} (hp : p.IsHomogeneous d) :
    aeval (allNegVec W) p = (-1 : MvPolynomial (Fin 3) R) ^ d * p := by
  have hv : (allNegVec W) = (fun i : Fin 3 ↦ -X i) := by
    funext i; fin_cases i <;> simp [allNegVec]
  rw [hv]
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv ↦ ?_
  have hvdeg : v.degree = d := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hv) (hp.coeff_eq_zero h)
  have hprod : (v.prod fun i e ↦ (-X i : MvPolynomial (Fin 3) R) ^ e)
      = (-1) ^ d * v.prod (fun i e ↦ (X i) ^ e) := by
    simp only [Finsupp.prod]
    rw [Finset.prod_congr rfl (fun i _ ↦ neg_pow (X i : MvPolynomial (Fin 3) R) (v i)),
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hvdeg]
  rw [aeval_monomial, algebraMap_eq, monomial_eq, hprod]
  ring

/-- `allNegGradedQuot` scales a degree-`d` homogeneous class by `(-1)^d`: the `hscale`
hypothesis feeding `Proj.map_negScaling_eq_id`. -/
lemma allNegGradedQuot_scale (W : WeierstrassCurve R) (d : ℕ) {a : projCoordRing W}
    (ha : a ∈ (quotientGrading (projIdeal W)) d) :
    allNegGradedQuot W a = (-1 : projCoordRing W) ^ d * a := by
  obtain ⟨p, hp, hmap⟩ := Submodule.mem_map.mp ha
  have ha_eq : a = Ideal.Quotient.mk (projIdeal W).toIdeal p := hmap.symm
  rw [ha_eq, allNegGradedQuot, quotientGradingMap_mk]
  show Ideal.Quotient.mk (projIdeal W).toIdeal (aeval (allNegVec W) p) =
    (-1) ^ d * Ideal.Quotient.mk (projIdeal W).toIdeal p
  rw [allNegVec_smul_of_homogeneous W ((mem_homogeneousSubmodule _ _).mp hp),
    map_mul, map_pow, map_neg, map_one]

/-- **(T-W7.0b-ρ)** `Proj.map` of the "negate all variables" automorphism is the identity:
rescaling every homogeneous coordinate by `−1` fixes each point of `Proj` projectively. -/
theorem allNeg_map_id (W : WeierstrassCurve R) :
    Proj.map (allNegGradedQuot W) (allNegGradedQuot_irrelevant_le W) = 𝟙 (projModel W) :=
  Proj.map_negScaling_eq_id (allNegGradedQuot W) (allNegGradedQuot_irrelevant_le W)
    (allNegGradedQuot_scale W)

end NegationConstruction

/-- **(T-W7.0b)** Negation on the projective Weierstrass model: the projectivisation of
`(x, y) ↦ (x, −y − a₁x − a₃)` (denominator-free, hence a morphism outright; linear on the
infinity chart), realised as the `Proj` endomorphism induced by the graded coordinate-ring
endomorphism `X ↦ X, Y ↦ −Y−a₁X−a₃Z, Z ↦ Z`. Source: Silverman III.2; mathlib `Affine.negY`. -/
noncomputable def negModelHom (W : WeierstrassCurve R) : projModel W ⟶ projModel W :=
  Proj.map (negGradedQuot W) (negGradedQuot_irrelevant_le W)

/-- **(T-W7.0b-π)** Negation is a morphism over `Spec R`. -/
@[reassoc]
theorem negModelHom_π (W : WeierstrassCurve R) :
    negModelHom W ≫ projModelπ W = projModelπ W := by
  rw [negModelHom, projModelπ, ← Category.assoc,
    map_comp_toSpecZero (negGradedQuot W) (negGradedQuot_irrelevant_le W), Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, negGradedQuot_algebraMapGradeZero]

/-- **(T-W7.0b-invol)** Negation is an involution. -/
theorem negModelHom_negModelHom (W : WeierstrassCurve R) :
    negModelHom W ≫ negModelHom W = 𝟙 (projModel W) := by
  rw [negModelHom, ← Proj.map_comp]
  exact (Proj_map_congr (negGradedQuot_comp_self W) _ _).trans Proj.map_id

section
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial HomogeneousIdeal HomogeneousLocalization

/-- **(T-W7.0b-zero)** Negation fixes the point at infinity. The point at infinity is fixed
only PROJECTIVELY: `projModelZeroEval ∘ negGradedQuot` is evaluation at `(0,−1,0)` (the `−1`
from `Y ↦ −Y`), not at `(0,1,0)`; the two affine representatives of `O` differ by the unit
`−1`. The rescaling is discharged through the "negate all variables" automorphism `allNeg`,
using naturality of `Proj.fromOfGlobalSections` under `Proj.map` (`fromOfGlobalSections_map`),
the ring identity `projModelZeroEval_neg_eq_allNeg`, and `allNeg_map_id`
(`Proj.map allNeg = 𝟙`). Source: Silverman III.2.3. -/
theorem negModelHom_zero (W : WeierstrassCurve R) :
    projModelZero W ≫ negModelHom W = projModelZero W := by
  have key := Proj.fromOfGlobalSections_map (negGradedQuot W) (negGradedQuot_irrelevant_le W)
    ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W))
    (projModelZeroEval_irrelevant_map_top W)
    (Proj.irrelevant_map_comp_toRingHom_eq_top (negGradedQuot W) (negGradedQuot_irrelevant_le W) _
      (projModelZeroEval_irrelevant_map_top W))
  have key2 := Proj.fromOfGlobalSections_map (allNegGradedQuot W) (allNegGradedQuot_irrelevant_le W)
    ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W))
    (projModelZeroEval_irrelevant_map_top W)
    (Proj.irrelevant_map_comp_toRingHom_eq_top (allNegGradedQuot W)
      (allNegGradedQuot_irrelevant_le W) _ (projModelZeroEval_irrelevant_map_top W))
  have hfeq : ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W)).comp
        (negGradedQuot W).toRingHom =
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W)).comp
        (allNegGradedQuot W).toRingHom := by
    rw [RingHom.comp_assoc, projModelZeroEval_neg_eq_allNeg, ← RingHom.comp_assoc]
  have congr_from : ∀ (g₁ g₂ : projCoordRing W →+* Γ(Spec (.of R), ⊤))
      (h₁ : (HomogeneousIdeal.irrelevant
          (HomogeneousIdeal.quotientGrading (projIdeal W))).toIdeal.map g₁ = ⊤)
      (h₂ : (HomogeneousIdeal.irrelevant
          (HomogeneousIdeal.quotientGrading (projIdeal W))).toIdeal.map g₂ = ⊤),
      g₁ = g₂ →
      Proj.fromOfGlobalSections (HomogeneousIdeal.quotientGrading (projIdeal W)) g₁ h₁ =
        Proj.fromOfGlobalSections (HomogeneousIdeal.quotientGrading (projIdeal W)) g₂ h₂ := by
    rintro g₁ g₂ h₁ h₂ rfl; rfl
  rw [negModelHom, projModelZero, key,
    ← Category.comp_id (Proj.fromOfGlobalSections (HomogeneousIdeal.quotientGrading (projIdeal W))
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W))
      (projModelZeroEval_irrelevant_map_top W)), ← allNeg_map_id W, key2]
  exact congr_from _ _ _ _ hfeq

/-- Negation fixes the class of `X₂ = Z` in the quotient coordinate ring (`negVec` fixes `X 2`).
Foundational fact behind chart-preservation (`inZChart_comp_negModelHom`). -/
lemma negGradedQuot_mk_X2 (W : WeierstrassCurve R) :
    negGradedQuot W (quotientGradingHom (projIdeal W) (X 2)) =
      quotientGradingHom (projIdeal W) (X 2) := by
  rw [quotientGradingHom_apply, negGradedQuot, quotientGradingMap_mk]
  refine congrArg (Ideal.Quotient.mk _) ?_
  show aeval (negVec W) (X 2) = X 2
  simp [negVec]

/-- `negModelHom` preserves the `Z`-chart basic open `D₊(X₂)`: since negation fixes `X₂`, the
`Proj.map` preimage of `D₊(X₂)` is `D₊(X₂)` again (`Proj.map_preimage_basicOpen` +
`negGradedQuot_mk_X2`). The geometric heart of chart-preservation. -/
lemma negModelHom_preimage_basicOpen_X2 (W : WeierstrassCurve R) :
    negModelHom W ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W))
        (quotientGradingHom (projIdeal W) (X 2))) =
      Proj.basicOpen (quotientGrading (projIdeal W))
        (quotientGradingHom (projIdeal W) (X 2)) := by
  rw [negModelHom, Proj.map_preimage_basicOpen]
  exact congrArg (Proj.basicOpen _) (negGradedQuot_mk_X2 W)

/-- A field point is in the `Z`-chart iff its base point lands in the range of the affine
`Z`-chart `Proj.awayι(X₂)`. Forward: the factoring morphism's image lies in the range; backward:
`IsOpenImmersion.lift` (the domain `Spec K` is a single point, `Subsingleton`). The
open-immersion factoring criterion specialised to `awayι(X₂)`. -/
lemma inZChart_iff_opensRange (W : WeierstrassCurve R) (K : Type u) [Field K] [Algebra R K]
    (g : SpecPoints (projModel W) (projModelπ W) K) :
    InZChart W g ↔ g.1.base default ∈ (Proj.awayι (quotientGrading (projIdeal W)) _
      (mk_X_mem_quotientGrading_one W 2) one_pos).opensRange := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h.base default, ?_⟩
    rw [← hh, Scheme.Hom.comp_base]
    rfl
  · intro hmem
    refine ⟨IsOpenImmersion.lift (Proj.awayι (quotientGrading (projIdeal W)) _
      (mk_X_mem_quotientGrading_one W 2) one_pos) g.1 ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨y, rfl⟩
    have hy : y = default := Subsingleton.elim _ _
    subst hy
    exact hmem

set_option backward.isDefEq.respectTransparency.types false in
/-- **(L1 — T-W7.0b-points leaf)** Negation preserves the `Z`-chart: a field point is in the
`Z`-chart iff its `negModelHom`-image is. Via `inZChart_iff_opensRange` both sides reduce to
base-point membership in `D₊(X₂)` (`Proj.opensRange_awayι`), then
`(g.1 ≫ neg)⁻¹ᵁ D₊(X₂) = g.1⁻¹ᵁ (neg⁻¹ᵁ D₊(X₂)) = g.1⁻¹ᵁ D₊(X₂)` by `Scheme.Hom.comp_preimage`
and `negModelHom_preimage_basicOpen_X2`.
NOTE: this stays at the opens level (`basicOpen`, a fixed type) — `awayι 𝒜 s` and `awayι 𝒜 (neg s)`
have DIFFERENT domain types `Spec(Away 𝒜 s)` vs `Spec(Away 𝒜 (neg s))`, so their `=` does not
typecheck. -/
lemma inZChart_comp_negModelHom (W : WeierstrassCurve R) (K : Type u) [Field K] [Algebra R K]
    (g : SpecPoints (projModel W) (projModelπ W) K)
    (hcomp : (g.1 ≫ negModelHom W) ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    InZChart W (⟨g.1 ≫ negModelHom W, hcomp⟩ : SpecPoints (projModel W) (projModelπ W) K) ↔
      InZChart W g := by
  rw [inZChart_iff_opensRange, inZChart_iff_opensRange, Proj.opensRange_awayι,
    ← Scheme.Hom.mem_preimage, ← Scheme.Hom.mem_preimage]
  show default ∈ (g.1 ≫ negModelHom W) ⁻¹ᵁ _ ↔ default ∈ g.1 ⁻¹ᵁ _
  rw [Scheme.Hom.comp_preimage, negModelHom_preimage_basicOpen_X2]

/-! ### (L2) The `Z`-chart coordinate formula `(x, y) ↦ (x, negY x y)`

`negModelHom` acts on the `X₂`-chart as the ring endomorphism `negChartMap` (negate the numerator
by `negGradedQuot`, transported back along `negGradedQuot X₂ = X₂`); on dehomogenised coordinates
this is `X₀/X₂ ↦ X₀/X₂`, `X₁/X₂ ↦ (−X₁−a₁X₀−a₃X₂)/X₂`. -/

lemma negGradedQuot_mk_X0 (W : WeierstrassCurve R) :
    negGradedQuot W (quotientGradingHom (projIdeal W) (X 0)) =
      quotientGradingHom (projIdeal W) (X 0) := by
  rw [quotientGradingHom_apply, negGradedQuot, quotientGradingMap_mk]
  refine congrArg (Ideal.Quotient.mk _) ?_
  show aeval (negVec W) (X 0) = X 0
  simp [negVec]

lemma negGradedQuot_mk_X1 (W : WeierstrassCurve R) :
    negGradedQuot W (quotientGradingHom (projIdeal W) (X 1)) =
      quotientGradingHom (projIdeal W) (-X 1 - C W.a₁ * X 0 - C W.a₃ * X 2) := by
  rw [quotientGradingHom_apply, quotientGradingHom_apply, negGradedQuot, quotientGradingMap_mk]
  refine congrArg (Ideal.Quotient.mk _) ?_
  show aeval (negVec W) (X 1) = -X 1 - C W.a₁ * X 0 - C W.a₃ * X 2
  simp [negVec]

/-- The negation's action on the `X₂`-chart ring `Away X₂`, as a ring endomorphism:
`Away.map (negGradedQuot W)` followed by the transport `Away (neg X₂) ≃ Away X₂`. -/
noncomputable def negChartMap (W : WeierstrassCurve R) :
    Away (quotientGrading (projIdeal W)) (quotientGradingHom (projIdeal W) (X 2)) →+*
    Away (quotientGrading (projIdeal W)) (quotientGradingHom (projIdeal W) (X 2)) :=
  (awayCongr (negGradedQuot_mk_X2 W)).toRingHom.comp
    (Away.map (negGradedQuot W) (quotientGradingHom (projIdeal W) (X 2)))

private lemma awayι_awayCongr_local (W : WeierstrassCurve R)
    {s t : projCoordRing W} (h : s = t) (hs : s ∈ quotientGrading (projIdeal W) 1) :
    Spec.map (CommRingCat.ofHom
        (awayCongr (𝒜 := quotientGrading (projIdeal W)) h).toRingHom) ≫
      Proj.awayι (quotientGrading (projIdeal W)) s hs one_pos =
    Proj.awayι (quotientGrading (projIdeal W)) t (h ▸ hs) one_pos := by
  subst h
  rw [show (awayCongr (𝒜 := quotientGrading (projIdeal W)) (rfl : s = s)).toRingHom =
      RingHom.id _ from by rw [awayCongr_rfl]; rfl]
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- **(L2b)** The chart-level negation intertwines the `X₂`-chart inclusion with `negModelHom`. -/
lemma awayι_X2_negModelHom (W : WeierstrassCurve R) :
    Spec.map (CommRingCat.ofHom (negChartMap W)) ≫
      Proj.awayι (quotientGrading (projIdeal W)) (quotientGradingHom (projIdeal W) (X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos =
    Proj.awayι (quotientGrading (projIdeal W)) (quotientGradingHom (projIdeal W) (X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos ≫ negModelHom W := by
  rw [negChartMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    ← Proj.awayι_comp_map (negGradedQuot W) (negGradedQuot_irrelevant_le W) one_pos
      (quotientGradingHom (projIdeal W) (X 2)) (mk_X_mem_quotientGrading_one W 2),
    ← Category.assoc, awayι_awayCongr_local W (negGradedQuot_mk_X2 W) _, negModelHom]

/-- The morphism recovered from a chart ring hom via `chartHomEquiv.symm` (unfolds the
`chartPointOfHom` construction). -/
lemma chartHomEquiv_symm_coe (W : WeierstrassCurve R) (i : Fin 3) {K : Type u}
    [CommRing K] [Algebra R K]
    (φ : { φ : Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
        algebraMap R K }) :
    ((chartHomEquiv W i K).symm φ).1.1 =
      Spec.map (CommRingCat.ofHom φ.1) ≫ Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W i) one_pos :=
  rfl

/-- The `Z`-chart coordinate value is the chart ring hom applied to `Xⱼ/X₂`. -/
lemma coord_val (W : WeierstrassCurve R) (K : Type u) [Field K] [Algebra R K]
    (g : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W g)
    (j : {j : Fin 3 // j ≠ 2}) :
    (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 j =
      (chartHomEquiv W 2 K ⟨g, hZ⟩).1 (chartCoordEquiv W 2
        (Ideal.Quotient.mk _ (MvPolynomial.X j))) :=
  rfl

/-- The composite `P.1 ≫ negModelHom W` is again a `K`-point (negation commutes with the
structure map `projModelπ`). Factored out as a single named proof so that every occurrence of
`⟨P.1 ≫ negModelHom W, ·⟩` is *syntactically* identical — this keeps `rw` from unfolding the heavy
`chartHomEquiv` during its occurrence search (proof-irrelevant `by rw` terms differ per site and
force `isDefEq` to whnf the equiv, which times out). -/
private lemma negComp_π (W : WeierstrassCurve R) (K : Type u) [Field K] [Algebra R K]
    (P : SpecPoints (projModel W) (projModelπ W) K) :
    (P.1 ≫ negModelHom W) ≫ projModelπ W = Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [Category.assoc, negModelHom_π, P.2]

/-- **(L2a)** The composite `g ≫ negModelHom`'s chart ring hom factors as `φ_g ∘ negChartMap`. -/
lemma chartHom_negModelHom (W : WeierstrassCurve R) (K : Type u) [Field K] [Algebra R K]
    (g : SpecPoints (projModel W) (projModelπ W) K)
    (hZ : InZChart W g)
    (hZ' : InZChart W (⟨g.1 ≫ negModelHom W, negComp_π W K g⟩ :
      SpecPoints (projModel W) (projModelπ W) K)) :
    (chartHomEquiv W 2 K ⟨⟨g.1 ≫ negModelHom W, negComp_π W K g⟩,
        hZ'⟩).1 =
      (chartHomEquiv W 2 K ⟨g, hZ⟩).1.comp (negChartMap W) := by
  set φP := chartHomEquiv W 2 K ⟨g, hZ⟩ with hφP
  set φQ := chartHomEquiv W 2 K ⟨⟨g.1 ≫ negModelHom W, negComp_π W K g⟩, hZ'⟩ with hφQ
  have hPfac : Spec.map (CommRingCat.ofHom φP.1) ≫ Proj.awayι (quotientGrading (projIdeal W)) _
      (mk_X_mem_quotientGrading_one W 2) one_pos = g.1 := by
    rw [← chartHomEquiv_symm_coe W 2 φP, hφP, Equiv.symm_apply_apply]
  have hQfac : Spec.map (CommRingCat.ofHom φQ.1) ≫ Proj.awayι (quotientGrading (projIdeal W)) _
      (mk_X_mem_quotientGrading_one W 2) one_pos = g.1 ≫ negModelHom W := by
    rw [← chartHomEquiv_symm_coe W 2 φQ, hφQ, Equiv.symm_apply_apply]
  have hψfac : Spec.map (CommRingCat.ofHom (φP.1.comp (negChartMap W))) ≫
      Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W 2) one_pos = g.1 ≫ negModelHom W := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, awayι_X2_negModelHom,
      ← Category.assoc, hPfac]
  have hmono := hQfac.trans hψfac.symm
  have hcancel := (cancel_mono (Proj.awayι (quotientGrading (projIdeal W))
    (quotientGradingHom (projIdeal W) (X 2)) (mk_X_mem_quotientGrading_one W 2) one_pos)).mp hmono
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hcancel)

/-- `negChartMap` on an `X₂`-chart normal form: the numerator is negated by `negGradedQuot`. -/
lemma negChartMap_mk (W : WeierstrassCurve R) (n : ℕ) (a : projCoordRing W)
    (ha : a ∈ quotientGrading (projIdeal W) (n • 1)) :
    negChartMap W (Away.mk (quotientGrading (projIdeal W))
        (mk_X_mem_quotientGrading_one W 2) n a ha) =
      Away.mk (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) n
        (negGradedQuot W a) (GradedRingHom.map_mem (negGradedQuot W) ha) := by
  rw [negChartMap, RingHom.comp_apply, Away.map_mk, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    awayCongr_mk]

/-- Numerator congruence for the `X₂`-chart `Away.mk` normal form. -/
lemma away_mk_num_congr (W : WeierstrassCurve R) {n : ℕ} {a b : projCoordRing W}
    (ha : a ∈ quotientGrading (projIdeal W) (n • 1)) (hab : a = b) :
    Away.mk (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) n a ha =
      Away.mk (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) n b
        (hab ▸ ha) := by
  subst hab; rfl

/-- **(V0)** `negChartMap` fixes the `X₀/X₂` chart coordinate. -/
lemma negChartMap_coord0 (W : WeierstrassCurve R) :
    negChartMap W (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (X (⟨0, by decide⟩ :
        {j : Fin 3 // j ≠ 2})))) =
      chartCoordEquiv W 2 (Ideal.Quotient.mk _ (X (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 2}))) := by
  rw [chartCoordEquiv_mk_X, Away.isLocalizationElem, negChartMap_mk]
  refine (away_mk_num_congr W _ ?_).trans rfl
  rw [map_pow, negGradedQuot_mk_X0]

set_option backward.isDefEq.respectTransparency.types false in
/-- **(V1)** `negChartMap` sends the `X₁/X₂` chart coordinate to `(−X₁−a₁X₀−a₃X₂)/X₂`, i.e. the
dehomogenised `negY` substitution. -/
lemma negChartMap_coord1 (W : WeierstrassCurve R) :
    negChartMap W (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (X (⟨1, by decide⟩ :
        {j : Fin 3 // j ≠ 2})))) =
      chartCoordEquiv W 2 (Ideal.Quotient.mk _
        (-X (⟨1, by decide⟩ : {j : Fin 3 // j ≠ 2})
          - C W.a₁ * X ⟨0, by decide⟩ - C W.a₃)) := by
  rw [chartCoordEquiv_mk_X, Away.isLocalizationElem, negChartMap_mk]
  refine (away_mk_num_congr W _ (by rw [map_pow, pow_one, negGradedQuot_mk_X1])).trans ?_
  simp only [map_sub, map_mul, map_neg, chartCoordEquiv_mk_X, chartCoordEquiv_mk_C,
    Away.isLocalizationElem]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_sub, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_neg, Away.val_mk, HomogeneousLocalization.algebraMap_eq,
    HomogeneousLocalization.fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    HomogeneousLocalization.val_mk, pow_one, Localization.mk_mul,
    Localization.neg_mk]
  rw [Localization.sub_mk, Localization.sub_mk, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  have hbridge : ∀ r : R, (↑((gradeZeroRingEquiv W) r) : projCoordRing W) =
      quotientGradingHom (projIdeal W) (C r) := by
    intro r
    rw [show (gradeZeroRingEquiv W) r = algebraMapGradeZero (projIdeal W) r from rfl,
      coe_algebraMapGradeZero, quotientGradingHom_apply,
      IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing W),
      RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
  simp only [hbridge]
  norm_num [Submonoid.coe_mul, OneMemClass.coe_one]
  ring

/-- The dehomogenised `Z`-chart cubic evaluated at a coordinate vector is the affine Weierstrass
equation in `(v₀, v₁)`. (Local copy of the `private` `aeval_dehomog_two`.) -/
private lemma aeval_dehomog_two' (W : WeierstrassCurve R) {K : Type u} [CommRing K]
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

/-- The `Z`-chart coordinates of a point satisfy the affine Weierstrass equation. -/
private lemma negModelHom_zEquation (W : WeierstrassCurve R) (K : Type u) [Field K] [Algebra R K]
    (P : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W P) :
    (W.baseChange K).toAffine.Equation
      ((chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨P, hZ⟩)).1 ⟨0, by decide⟩)
      ((chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨P, hZ⟩)).1 ⟨1, by decide⟩) := by
  have h2 := (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨P, hZ⟩)).2
  rw [aeval_dehomog_two'] at h2
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  linear_combination h2

set_option backward.isDefEq.respectTransparency.types false in
/-- The composite's `Z`-chart `X₀`-coordinate equals the original's (negation fixes `X₀`).
`simp only` (not `rw`): the goal mixes `chartSolutionsEquiv`- and `chartHomEquiv`-headed terms, and
`rw`'s kabstract has no discrimination-tree pre-filter — it would `isDefEq` the `chartHomEquiv`
pattern against the heavy `chartSolutionsEquiv` coords and time out whnf-ing them. -/
private lemma negModelHom_zCoord0 (W : WeierstrassCurve R) (K : Type u) [Field K] [Algebra R K]
    (P : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W P)
    (hZ' : InZChart W (⟨P.1 ≫ negModelHom W, negComp_π W K P⟩ :
      SpecPoints (projModel W) (projModelπ W) K)) :
    (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K
        ⟨⟨P.1 ≫ negModelHom W, negComp_π W K P⟩, hZ'⟩)).1
        ⟨0, by decide⟩ =
      (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨P, hZ⟩)).1 ⟨0, by decide⟩ := by
  simp only [coord_val, chartHom_negModelHom W K P hZ hZ', RingHom.comp_apply, negChartMap_coord0]

set_option backward.isDefEq.respectTransparency.types false in
/-- The composite's `Z`-chart `X₁`-coordinate is `negY` of the original coordinates. `simp only`
front (see `negModelHom_zCoord0`): it rewrites both the composite's coordinate and the two `negY`
arguments into `φ_P`-of-chart-coordinate form, so no `chartSolutionsEquiv`-vs-`chartHomEquiv`
`isDefEq` ever fires; the remaining `chart_hom_aeval`/`negY`/`ring` steps then run over
`φ_P`-atoms. -/
private lemma negModelHom_zCoord1 (W : WeierstrassCurve R) (K : Type u) [Field K] [Algebra R K]
    (P : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W P)
    (hZ' : InZChart W (⟨P.1 ≫ negModelHom W, negComp_π W K P⟩ :
      SpecPoints (projModel W) (projModelπ W) K)) :
    (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K
        ⟨⟨P.1 ≫ negModelHom W, negComp_π W K P⟩, hZ'⟩)).1
        ⟨1, by decide⟩ =
      (W.baseChange K).toAffine.negY
        ((chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨P, hZ⟩)).1 ⟨0, by decide⟩)
        ((chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨P, hZ⟩)).1 ⟨1, by decide⟩) := by
  simp only [coord_val, chartHom_negModelHom W K P hZ hZ', RingHom.comp_apply, negChartMap_coord1]
  rw [chart_hom_aeval W 2 _ (chartHomEquiv W 2 K ⟨P, hZ⟩).2, WeierstrassCurve.Affine.negY]
  simp only [map_sub, map_neg, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

/-- **(T-W7.0b-points)** On field points, `negModelHom` is mathlib's affine negation through the
dictionary. UNBLOCKED (P2 landed the real `projModelPointsEquiv` + `_zero`/`_some`). ROUTE:
`by_cases hZ : InZChart W P`, using `inZChart_comp_negModelHom` (L1) both ways.
• `¬InZChart` (infinity): `projModelPointsEquivEll_infinity` gives `projModelPointsEquiv W K P = 0`
  and (via L1) `= 0` on the composite, so LHS `= 0 = -0 =` RHS (`neg_zero`).
• `InZChart` (Z-chart): `projModelPointsEquiv_some` gives `P ↦ some x y`; the composite `↦ some x
  (negY x y)` by the **coordinate leaf L2** (`negModelHom` acts on `Z`-chart coords as
  `X₀/X₂↦X₀/X₂`, `X₁/X₂↦(−X₁−a₁X₀−a₃X₂)/X₂`, traced through `chartHomEquiv`/`chartSolutionsEquiv`
  precomposed with `HomogeneousLocalization.Away.map (negGradedQuot W)`); and RHS
  `-(some x y) = some x (W.negY x y)` by `Affine.Point.neg_some` (`negY x y = −y−a₁x−a₃`).
  `Nonsingular` witnesses are proof-irrelevant. Source: Silverman III.2.3; `Affine.negY`. -/
theorem negModelHom_specPoints (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [Algebra R K]
    (P : SpecPoints (projModel W) (projModelπ W) K) :
    projModelPointsEquiv W K
        ⟨P.1 ≫ negModelHom W, negComp_π W K P⟩ =
      -(projModelPointsEquiv W K P) := by
  by_cases hZ : InZChart W P
  · -- Z-chart case: coordinate leaf L2. `negModelHom` acts on the dehomogenised `Z`-chart
    -- coordinates as `X₀/X₂ ↦ X₀/X₂`, `X₁/X₂ ↦ (−X₁ − a₁X₀ − a₃X₂)/X₂`, so the composite's
    -- coordinates are `(x, W.negY x y)`; then `projModelPointsEquiv_some` on both sides and
    -- `Affine.Point.neg_some` (`negY x y = −y − a₁x − a₃`) finish.
    have hZ' : InZChart W (⟨P.1 ≫ negModelHom W, negComp_π W K P⟩ :
        SpecPoints (projModel W) (projModelπ W) K) :=
      (inZChart_comp_negModelHom W K P _).mpr hZ
    have : ((W.baseChange K).toAffine).IsElliptic :=
      inferInstanceAs ((W.map (algebraMap R K)).IsElliptic)
    have hxy := WeierstrassCurve.Affine.equation_iff_nonsingular.mp (negModelHom_zEquation W K P hZ)
    simp only [projModelPointsEquiv_some W K P hZ _ _ hxy rfl rfl,
      projModelPointsEquiv_some W K
        ⟨P.1 ≫ negModelHom W, negComp_π W K P⟩ hZ' _ _
        ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr hxy)
        (negModelHom_zCoord0 W K P hZ hZ').symm (negModelHom_zCoord1 W K P hZ hZ').symm,
      WeierstrassCurve.Affine.Point.neg_some]
  · -- Infinity case: off the `Z`-chart, `P` is the point at infinity `[0:1:0]` (its morphism is
    -- the zero section), which `negModelHom` fixes (`negModelHom_zero`); both sides are `0`.
    have hP : P.1 = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ projModelZero W :=
      specPoint_eq_zero_of_not_inZ W K P hZ
    have hRHS : projModelPointsEquiv W K P = 0 := by
      rw [← projModelPointsEquiv_zero W K]
      exact congrArg (projModelPointsEquiv W K) (Subtype.ext hP)
    have hLHS : projModelPointsEquiv W K
        ⟨P.1 ≫ negModelHom W, negComp_π W K P⟩ = 0 := by
      rw [← projModelPointsEquiv_zero W K]
      refine congrArg (projModelPointsEquiv W K) (Subtype.ext ?_)
      show P.1 ≫ negModelHom W = _
      rw [hP, Category.assoc, negModelHom_zero]
    rw [hLHS, hRHS]
    exact WeierstrassCurve.Affine.Point.neg_zero.symm

end

/-! ## Lane P1: the Bosma–Lenstra two-law multiplication -/

/-- **(T-W7.0c·c1-Z, the open)** The regularity open of the `Z = 0` addition law on
`E ×_R E`: the complement of its exceptional divisor, which over every field is exactly the
locus `P₁ ≠ P₂` (B–L Thm 2 at the line `Z = 0`: exceptional ⟺ `P₁ − P₂ ∈ E ∩ {Z=0} = {O}`).
Source: B–L Thm 2 + "lines y = 0, z = 0" (quotes file). -/
noncomputable def blOpenZ (W : WeierstrassCurve R) :
    (pullback (projModelπ W) (projModelπ W)).Opens :=
  WeierstrassCurve.Projective.blOpenZ W

/-- **(T-W7.0c·c1-Y, the open)** The regularity open of the `Y = 0` addition law: over every
field, the locus `P₁ − P₂ ∉ E ∩ {Y = 0}` (contains the diagonal and the infinity loci since
`O ∉ {Y=0}`). Source: B–L Thm 2 at the line `Y = 0`. -/
noncomputable def blOpenY (W : WeierstrassCurve R) :
    (pullback (projModelπ W) (projModelπ W)).Opens :=
  WeierstrassCurve.Projective.blOpenY W

/-- **(T-W7.0c·c1-Z, the morphism)** The `Z = 0` addition law as a morphism on its
regularity open: the explicit bidegree-(2,2) polynomial triple of B–L §5. Source: B–L §5
(transcribe from the PDF at implementation; CAS-verify each polynomial first). -/
noncomputable def addOnZ (W : WeierstrassCurve R) [W.IsElliptic] :
    (blOpenZ W).toScheme ⟶ projModel W :=
  (blOpenZ W).ι ≫
    mulModelHomBC (classifyRingHomU W) universalWeierstrassLocU
      universalWeierstrassLocU.isUnit_Δ W (universalWeierstrassLocU_map_classifyRingHomU W)

/-- **(T-W7.0c·c1-Y, the morphism)** The `Y = 0` addition law as a morphism on its
regularity open. Source: B–L §5. -/
noncomputable def addOnY (W : WeierstrassCurve R) [W.IsElliptic] :
    (blOpenY W).toScheme ⟶ projModel W :=
  (blOpenY W).ι ≫
    mulModelHomBC (classifyRingHomU W) universalWeierstrassLocU
      universalWeierstrassLocU.isUnit_Δ W (universalWeierstrassLocU_map_classifyRingHomU W)

/-- **(T-W7.0c·c2)** The two regularity opens cover the product: the exceptional divisors
are disjoint over every field (their common zero would be a point with `P₁ − P₂ = O` and
`P₁ − P₂ ∈ {Y = 0}`, but `O ∉ {Y = 0}`), and coverage is a fibrewise/topological statement.
Source: B–L Thm 2 + p. 230–231 ("any two distinct lines … intersect outside E(k)"). -/
theorem blOpen_cover (W : WeierstrassCurve R) [W.IsElliptic] :
    blOpenZ W ⊔ blOpenY W = ⊤ :=
  WeierstrassCurve.Projective.blOpenZ_sup_blOpenY_eq_top W W.isUnit_Δ

/-- **(T-W7.0c·c3)** The two laws agree on the overlap: a polynomial identity modulo the two
curve relations, bidegree-(2,2)-by-(2,2), over `ℤ[a₁,…,a₆]` — discharged by
`linear_combination` with precomputed cofactors, split per coordinate. NO `maxHeartbeats`.
Source: B–L Thm 2 (both laws compute the group law where defined, so they agree on points;
the scheme-level identity is the §5 polynomial identity). -/
theorem addOn_agree (W : WeierstrassCurve R) [W.IsElliptic] :
    (pullback (projModelπ W) (projModelπ W)).homOfLE inf_le_left ≫ addOnZ W =
      (pullback (projModelπ W) (projModelπ W)).homOfLE inf_le_right ≫ addOnY W :=
  restrict_inf_agree _ (blOpenZ W) (blOpenY W)

/-- **(T-W7.0c·c4)** THE multiplication morphism on the projective Weierstrass model, glued
from the two Bosma–Lenstra addition laws. Source: B–L Thm 1 (two laws suffice — and are
necessary: no single law is total); glue via `Scheme.Cover.glueMorphisms`-style plumbing on
the two-open cover. -/
noncomputable def mulModelHom (W : WeierstrassCurve R) [W.IsElliptic] :
    pullback (projModelπ W) (projModelπ W) ⟶ projModel W :=
  mulModelHomBC (classifyRingHomU W) universalWeierstrassLocU
    universalWeierstrassLocU.isUnit_Δ W (universalWeierstrassLocU_map_classifyRingHomU W)

/-- **(T-W7.0c·c4-Z-spec)** `mulModelHom` restricts to the `Z`-law on its open. -/
theorem blOpenZ_ι_mulModelHom (W : WeierstrassCurve R) [W.IsElliptic] :
    (blOpenZ W).ι ≫ mulModelHom W = addOnZ W :=
  rfl

/-- **(T-W7.0c·c4-Y-spec)** `mulModelHom` restricts to the `Y`-law on its open. -/
theorem blOpenY_ι_mulModelHom (W : WeierstrassCurve R) [W.IsElliptic] :
    (blOpenY W).ι ≫ mulModelHom W = addOnY W :=
  rfl

/-- **(T-W7.0d)** Multiplication is a morphism over `Spec R`. Source: the B–L triples are
bihomogeneous with coefficients in `R` — the composite to `Spec R` is the structure map on
each piece. -/
@[reassoc]
theorem mulModelHom_π (W : WeierstrassCurve R) [W.IsElliptic] :
    mulModelHom W ≫ projModelπ W =
      pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W :=
  mulModelHomBC_projModelπ (classifyRingHomU W) universalWeierstrassLocU
    universalWeierstrassLocU.isUnit_Δ W (universalWeierstrassLocU_map_classifyRingHomU W)

/- **(T-W7.0c·c6, the spec)** `mulModelHom_specPoints` — on field points, `mulModelHom` is
mathlib's `Point.add` through the dictionary. PROVEN downstream in `AdditionSpecPoints.lean`
(the evaluation layer needs the two-law descent + atlas keystone machinery built there;
this file only defines the morphism). -/

/-- **(T-W7.0c·nat)** Base-change naturality of the multiplication morphism: the B–L
polynomial data has coefficients entering polynomially, so `mulModelHom` commutes with base
change along any ring map. This is the transport that carries the universal-atlas group
axioms to every ring (audit A6: universality-by-instantiation). Source: B–L p. 231
("coefficients … enter polynomially into all formulae … the same formulae can be used …
over commutative rings"). -/
theorem mulModelHom_map {R' : Type u} [CommRing R'] (f : R →+* R')
    (W : WeierstrassCurve R) [W.IsElliptic] [(W.map f).IsElliptic] :
    mulModelHom (W.map f) ≫ projModelBaseChange f W =
      pullback.map (projModelπ (W.map f)) (projModelπ (W.map f))
          (projModelπ W) (projModelπ W)
          (projModelBaseChange f W) (projModelBaseChange f W)
          (Spec.map (CommRingCat.ofHom f))
          (projModelBaseChange_π f W).symm (projModelBaseChange_π f W).symm ≫
        mulModelHom W :=
  (congrArg (· ≫ projModelBaseChange f W)
    (mulModelHomBC_congr (classifyRingHomU (W.map f)) (f.comp (classifyRingHomU W))
      (classifyRingHomU_map f W) universalWeierstrassLocU universalWeierstrassLocU.isUnit_Δ
      (W.map f) (universalWeierstrassLocU_map_classifyRingHomU (W.map f))
      (by rw [← WeierstrassCurve.map_map, universalWeierstrassLocU_map_classifyRingHomU W]))).trans
    (mulModelHomBC_map (classifyRingHomU W) f universalWeierstrassLocU
      universalWeierstrassLocU.isUnit_Δ W (universalWeierstrassLocU_map_classifyRingHomU W))

/-! ## Lane P1 (join with P0/P2): the group axioms at the `Over (Spec R)` level -/

variable (W : WeierstrassCurve R) [W.IsElliptic]

/-- The model as an object of `Over (Spec R)`. -/
noncomputable abbrev modelOver (W : WeierstrassCurve R) : Over (Spec (CommRingCat.of R)) :=
  Over.mk (projModelπ W)

/-- **(T-W7.0g-mul)** The multiplication as an `Over`-morphism from the cartesian tensor
(whose underlying scheme is the fibre product). -/
noncomputable def mulOver : modelOver W ⊗ modelOver W ⟶ modelOver W :=
  Over.homMk (mulModelHom W) (mulModelHom_π W)

/-- **(T-W7.0g-mul-left)** The underlying scheme morphism of `mulOver` is `mulModelHom`. -/
theorem mulOver_left : (mulOver W).left = mulModelHom W :=
  rfl

/-- **(T-W7.0g-one)** The unit as an `Over`-morphism, via the zero section. Its underlying
morphism is the structure map of the monoidal unit followed by the zero section; the `Over`
compatibility is `zero ≫ π = 𝟙` (`projModelZero_projModelπ`). -/
noncomputable def oneOver : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ modelOver W :=
  Over.homMk ((𝟙_ (Over (Spec (CommRingCat.of R)))).hom ≫ projModelZero W) <| by
    show ((𝟙_ (Over (Spec (CommRingCat.of R)))).hom ≫ projModelZero W) ≫ projModelπ W =
      (𝟙_ (Over (Spec (CommRingCat.of R)))).hom
    rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]

omit [W.IsElliptic] in
/-- **(T-W7.0g-one-left)** The underlying morphism of the unit is the zero section
(precomposed with the structure map of the monoidal unit). -/
theorem oneOver_left :
    (oneOver W).left = (𝟙_ (Over (Spec (CommRingCat.of R)))).hom ≫ projModelZero W :=
  rfl

/-- **(T-W7.0g-inv)** The inverse as an `Over`-morphism, via `negModelHom`. The `Over`
compatibility is `negModelHom ≫ π = π` (`negModelHom_π`). -/
noncomputable def invOver : modelOver W ⟶ modelOver W :=
  Over.homMk (negModelHom W) (negModelHom_π W)

omit [W.IsElliptic] in
/-- **(T-W7.0g-inv-left)** The underlying morphism of the inverse is `negModelHom`. -/
theorem invOver_left : (invOver W).left = negModelHom W :=
  rfl

/-! ## Lane P1 (with P3): variable-change equivariance -/

/- **(T-W7.0h)** `mulModelHom_vc` — global variable-change equivariance of the
multiplication morphism — is PROVEN in `EllipticCurve/ModelVCEquivariance.lean` (which
must sit above `ModelRecord.lean`/`Rigidity.lean`: the proof is GIT Cor 6.4 at the T-G4
group objects over the noetherian universal VC-base, transported along the classifying
map). Statement relocated verbatim per the v10.117 doctrine. -/

end ModularCurves
