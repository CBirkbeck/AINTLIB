import ModularCurves.EllipticCurve.PointsDictionary
import ModularCurves.EllipticCurve.ModelVariableChange
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
hypotheses are propositions, so they may differ). -/
private lemma Proj_map_congr {A B σ τ : Type u} [CommRing A] [SetLike σ A]
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
    simp only [negVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
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
  GradedRingHom.ext fun x => negGradedQuot_involutive W x

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
  refine RingHom.ext fun r => Subtype.ext ?_
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
noncomputable def allNegVec (W : WeierstrassCurve R) : Fin 3 → MvPolynomial (Fin 3) R :=
  ![-X 0, -X 1, -X 2]

lemma allNegVec_isHomogeneous (W : WeierstrassCurve R) (i : Fin 3) :
    (allNegVec W i).IsHomogeneous 1 := by
  fin_cases i <;>
    simp only [allNegVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
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
  GradedRingHom.ext fun x => allNegGradedQuot_involutive W x

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
  refine RingHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [RingHom.comp_apply]
  show projModelZeroEval W (negGradedQuot W (Ideal.Quotient.mk _ p)) =
    projModelZeroEval W (allNegGradedQuot W (Ideal.Quotient.mk _ p))
  rw [negGradedQuot, allNegGradedQuot, quotientGradingMap_mk, quotientGradingMap_mk,
    projModelZeroEval_mk, projModelZeroEval_mk]
  show (aeval (fun i : Fin 3 => if i = 1 then (1 : R) else 0)) (aeval (negVec W) p) =
       (aeval (fun i : Fin 3 => if i = 1 then (1 : R) else 0)) (aeval (allNegVec W) p)
  rw [comp_aeval_apply, comp_aeval_apply]
  refine congrArg (fun g => aeval g p) (funext fun i => ?_)
  fin_cases i <;>
    simp [negVec, allNegVec]

/-- The "negate all variables" substitution scales a degree-`d` homogeneous polynomial by
`(-1)^d`. -/
lemma allNegVec_smul_of_homogeneous (W : WeierstrassCurve R) {d : ℕ}
    {p : MvPolynomial (Fin 3) R} (hp : p.IsHomogeneous d) :
    aeval (allNegVec W) p = (-1 : MvPolynomial (Fin 3) R) ^ d * p := by
  have hv : (allNegVec W) = (fun i : Fin 3 => -X i) := by
    funext i; fin_cases i <;> simp [allNegVec]
  rw [hv]
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hvdeg : v.degree = d := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hv) (hp.coeff_eq_zero h)
  have hprod : (v.prod fun i e => (-X i : MvPolynomial (Fin 3) R) ^ e)
      = (-1) ^ d * v.prod (fun i e => (X i) ^ e) := by
    simp only [Finsupp.prod]
    rw [Finset.prod_congr rfl (fun i _ => neg_pow (X i : MvPolynomial (Fin 3) R) (v i)),
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

end

/-- **(T-W7.0b-points)** On field points, `negModelHom` is mathlib's negation through the
dictionary. Source: `Affine.negY` vs the projectivised formula; `projModelPointsEquiv`. -/
theorem negModelHom_specPoints (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [Algebra R K]
    (P : SpecPoints (projModel W) (projModelπ W) K) :
    projModelPointsEquiv W K
        ⟨P.1 ≫ negModelHom W, by rw [Category.assoc, negModelHom_π, P.2]⟩ =
      -(projModelPointsEquiv W K P) := by
  -- BLOCKED on P2 (T-W7.0f): `projModelPointsEquiv` is currently an opaque `sorry` in
  -- `PointsDictionary.lean`, so nothing can be proved about its values (`sorry x` vs `-(sorry y)`
  -- are unrelatable). Provable once P2 lands the real field-points dictionary together with its
  -- chartwise characterisation — then this is the projectivised `Affine.negY` computation
  -- `(x, y) ↦ (x, −y−a₁x−a₃)` read through the dictionary. Do NOT close before P2 lands.
  sorry

/-! ## Lane P1: the Bosma–Lenstra two-law multiplication -/

/-- **(T-W7.0c·c1-Z, the open)** The regularity open of the `Z = 0` addition law on
`E ×_R E`: the complement of its exceptional divisor, which over every field is exactly the
locus `P₁ ≠ P₂` (B–L Thm 2 at the line `Z = 0`: exceptional ⟺ `P₁ − P₂ ∈ E ∩ {Z=0} = {O}`).
Source: B–L Thm 2 + "lines y = 0, z = 0" (quotes file). -/
noncomputable def blOpenZ (W : WeierstrassCurve R) :
    (pullback (projModelπ W) (projModelπ W)).Opens :=
  sorry

/-- **(T-W7.0c·c1-Y, the open)** The regularity open of the `Y = 0` addition law: over every
field, the locus `P₁ − P₂ ∉ E ∩ {Y = 0}` (contains the diagonal and the infinity loci since
`O ∉ {Y=0}`). Source: B–L Thm 2 at the line `Y = 0`. -/
noncomputable def blOpenY (W : WeierstrassCurve R) :
    (pullback (projModelπ W) (projModelπ W)).Opens :=
  sorry

/-- **(T-W7.0c·c1-Z, the morphism)** The `Z = 0` addition law as a morphism on its
regularity open: the explicit bidegree-(2,2) polynomial triple of B–L §5. Source: B–L §5
(transcribe from the PDF at implementation; CAS-verify each polynomial first). -/
noncomputable def addOnZ (W : WeierstrassCurve R) [W.IsElliptic] :
    (blOpenZ W).toScheme ⟶ projModel W :=
  sorry

/-- **(T-W7.0c·c1-Y, the morphism)** The `Y = 0` addition law as a morphism on its
regularity open. Source: B–L §5. -/
noncomputable def addOnY (W : WeierstrassCurve R) [W.IsElliptic] :
    (blOpenY W).toScheme ⟶ projModel W :=
  sorry

/-- **(T-W7.0c·c2)** The two regularity opens cover the product: the exceptional divisors
are disjoint over every field (their common zero would be a point with `P₁ − P₂ = O` and
`P₁ − P₂ ∈ {Y = 0}`, but `O ∉ {Y = 0}`), and coverage is a fibrewise/topological statement.
Source: B–L Thm 2 + p. 230–231 ("any two distinct lines … intersect outside E(k)"). -/
theorem blOpen_cover (W : WeierstrassCurve R) [W.IsElliptic] :
    blOpenZ W ⊔ blOpenY W = ⊤ := by
  sorry

/-- **(T-W7.0c·c3)** The two laws agree on the overlap: a polynomial identity modulo the two
curve relations, bidegree-(2,2)-by-(2,2), over `ℤ[a₁,…,a₆]` — discharged by
`linear_combination` with precomputed cofactors, split per coordinate. NO `maxHeartbeats`.
Source: B–L Thm 2 (both laws compute the group law where defined, so they agree on points;
the scheme-level identity is the §5 polynomial identity). -/
theorem addOn_agree (W : WeierstrassCurve R) [W.IsElliptic] :
    (pullback (projModelπ W) (projModelπ W)).homOfLE inf_le_left ≫ addOnZ W =
      (pullback (projModelπ W) (projModelπ W)).homOfLE inf_le_right ≫ addOnY W := by
  sorry

/-- **(T-W7.0c·c4)** THE multiplication morphism on the projective Weierstrass model, glued
from the two Bosma–Lenstra addition laws. Source: B–L Thm 1 (two laws suffice — and are
necessary: no single law is total); glue via `Scheme.Cover.glueMorphisms`-style plumbing on
the two-open cover. -/
noncomputable def mulModelHom (W : WeierstrassCurve R) [W.IsElliptic] :
    pullback (projModelπ W) (projModelπ W) ⟶ projModel W :=
  sorry

/-- **(T-W7.0c·c4-Z-spec)** `mulModelHom` restricts to the `Z`-law on its open. -/
theorem blOpenZ_ι_mulModelHom (W : WeierstrassCurve R) [W.IsElliptic] :
    (blOpenZ W).ι ≫ mulModelHom W = addOnZ W := by
  sorry

/-- **(T-W7.0c·c4-Y-spec)** `mulModelHom` restricts to the `Y`-law on its open. -/
theorem blOpenY_ι_mulModelHom (W : WeierstrassCurve R) [W.IsElliptic] :
    (blOpenY W).ι ≫ mulModelHom W = addOnY W := by
  sorry

/-- **(T-W7.0d)** Multiplication is a morphism over `Spec R`. Source: the B–L triples are
bihomogeneous with coefficients in `R` — the composite to `Spec R` is the structure map on
each piece. -/
@[reassoc]
theorem mulModelHom_π (W : WeierstrassCurve R) [W.IsElliptic] :
    mulModelHom W ≫ projModelπ W =
      pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  sorry

/-- **(T-W7.0c·c6, the spec)** On field points, `mulModelHom` is mathlib's `Point.add`
through the dictionary — for EVERY pair (the B–L laws compute the chord–tangent sum wherever
each is defined, and the two opens cover). This single spec is what every group axiom
consumes. Source: B–L Thm 2 ("addition law" = computes the sum in `E(K)`); mathlib
`Affine.Point.add`; §5 formulas vs `Affine.slope`/`addX`/`addY` on the secant locus. -/
theorem mulModelHom_specPoints (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [DecidableEq K] [Algebra R K]
    (P Q : SpecPoints (projModel W) (projModelπ W) K) :
    projModelPointsEquiv W K
        ⟨pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ mulModelHom W, by
          rw [Category.assoc, mulModelHom_π, ← Category.assoc, pullback.lift_fst, P.2]⟩ =
      projModelPointsEquiv W K P + projModelPointsEquiv W K Q := by
  sorry

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
        mulModelHom W := by
  sorry

/-! ## Lane P1 (join with P0/P2): the group axioms at the `Over (Spec R)` level -/

variable (W : WeierstrassCurve R) [W.IsElliptic]

/-- The model as an object of `Over (Spec R)`. -/
noncomputable abbrev modelOver (W : WeierstrassCurve R) : Over (Spec (CommRingCat.of R)) :=
  Over.mk (projModelπ W)

/-- **(T-W7.0g-mul)** The multiplication as an `Over`-morphism from the cartesian tensor
(whose underlying scheme is the fibre product). -/
noncomputable def mulOver : modelOver W ⊗ modelOver W ⟶ modelOver W :=
  sorry

/-- **(T-W7.0g-mul-left)** The underlying scheme morphism of `mulOver` is `mulModelHom`. -/
theorem mulOver_left : (mulOver W).left = mulModelHom W := by
  sorry

/-- **(T-W7.0g-one)** The unit as an `Over`-morphism, via the zero section. -/
noncomputable def oneOver : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ modelOver W :=
  sorry

/-- **(T-W7.0g-one-left)** The underlying morphism of the unit is the zero section
(precomposed with the structure map of the monoidal unit). -/
theorem oneOver_left :
    (oneOver W).left = (𝟙_ (Over (Spec (CommRingCat.of R)))).hom ≫ projModelZero W := by
  sorry

/-- **(T-W7.0g-inv)** The inverse as an `Over`-morphism, via `negModelHom`. -/
noncomputable def invOver : modelOver W ⟶ modelOver W :=
  sorry

/-- **(T-W7.0g-inv-left)** The underlying morphism of the inverse is `negModelHom`. -/
theorem invOver_left : (invOver W).left = negModelHom W := by
  sorry

/-- **(T-W7.0g-assoc)** Associativity, as the monoid-object equation in `Over (Spec R)`.
Proof route: over the universal atlas by field-points extensionality + the dictionary +
mathlib's `add_assoc` on `Affine.Point`; then for every `R` by instantiating the naturality
`mulModelHom_map` along the classifying map. Source: reviewer round 1 §Q4/Q5; audit A5/A6;
GIT-free, cohomology-free. -/
theorem mulOver_assoc :
    (mulOver W ▷ modelOver W) ≫ mulOver W =
      (α_ (modelOver W) (modelOver W) (modelOver W)).hom ≫
        (modelOver W ◁ mulOver W) ≫ mulOver W := by
  sorry

/-- **(T-W7.0g-one-mul)** Left unit law. -/
theorem oneOver_mulOver :
    (oneOver W ▷ modelOver W) ≫ mulOver W = (λ_ (modelOver W)).hom := by
  sorry

/-- **(T-W7.0g-mul-one)** Right unit law. -/
theorem mulOver_oneOver :
    (modelOver W ◁ oneOver W) ≫ mulOver W = (ρ_ (modelOver W)).hom := by
  sorry

/-- **(T-W7.0g-comm)** Commutativity. -/
theorem mulOver_comm :
    (β_ (modelOver W) (modelOver W)).hom ≫ mulOver W = mulOver W := by
  sorry

/-- **(T-W7.0g-inv-law)** The left inverse law. -/
theorem invOver_mulOver :
    lift (invOver W) (𝟙 (modelOver W)) ≫ mulOver W = toUnit (modelOver W) ≫ oneOver W := by
  sorry

/-! ## Lane P1 (with P3): variable-change equivariance -/

/-- **(T-W7.0h)** Global variable-change equivariance of the multiplication morphism:
the model isomorphism of a variable change intertwines the two glued multiplications —
including the diagonal, anti-diagonal and infinity loci (reviewer round 1 caveat: the affine
cocycle alone is not enough). Proof route: field-points extensionality over the universal
VC-base `R ⊗ ℤ[u^±, r, s, t]` (a domain) + the affine cocycle (`pointEquiv` machinery,
project, DONE) at points. Source: audit item 8; `ForMathlib/AffinePointVariableChange`. -/
theorem mulModelHom_vc (C : VariableChange R) (W : WeierstrassCurve R)
    [W.IsElliptic] [(C • W).IsElliptic] :
    mulModelHom (C • W) ≫ (projModelVCIso C W).hom =
      pullback.map (projModelπ (C • W)) (projModelπ (C • W))
          (projModelπ W) (projModelπ W)
          (projModelVCIso C W).hom (projModelVCIso C W).hom (𝟙 (Spec (CommRingCat.of R)))
          (by rw [Category.comp_id]; exact (projModelVCIso_π C W).symm)
          (by rw [Category.comp_id]; exact (projModelVCIso_π C W).symm) ≫
        mulModelHom W := by
  sorry

end ModularCurves
