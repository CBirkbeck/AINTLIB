import ModularCurves.Moduli.WeierstrassAtlas
import ModularCurves.EllipticCurve.WeierstrassModel
import Mathlib.RingTheory.Localization.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# T-W7 P0 — the universal atlas ring, and the negation morphism on the projective model

Part of the constructive group-scheme structure on the universal Weierstrass curve
(Stream W, tickets **T-W7.0a** and **T-W7.0b**).

## The atlas ring is a domain (T-W7.0a)

The coefficient-with-discriminant-inverted ring `WeierstrassAtlasRing = ℤ[a₁,…,a₆][Δ⁻¹]` is an
integral domain: it is the localization of the polynomial domain `MvPolynomial (Fin 5) ℤ` away
from the (nonzero) universal discriminant `Δ`. This domain property is the foundation of the
generic-point method used throughout T-W7: the group-law axioms over the atlas are proved by
evaluating at the single generic point `η` of the integral scheme
`U = Spec ℤ[a₁,…,a₆][Δ⁻¹]`.

## The negation morphism (T-W7.0b)

For any `W : WeierstrassCurve R` the *negation* `[X:Y:Z] ↦ [X : −Y−a₁X−a₃Z : Z]` is the
classical involution of the plane cubic that fixes the `x`-coordinate (Silverman III.2.3). It
is induced by the graded ring endomorphism of the homogeneous coordinate ring sending
`X ↦ X, Y ↦ −Y−a₁X−a₃Z, Z ↦ Z`; this endomorphism is degree-preserving (each image is
homogeneous of degree `1`) and fixes the Weierstrass cubic *exactly*
(`negGradedPoly_polynomial`), so it descends to the quotient coordinate ring and induces a
`Proj` endomorphism via mathlib's `Proj.map`.

## Main results

* `universalWeierstrass_Δ_ne_zero` / `IsDomain WeierstrassAtlasRing` (T-W7.0a).
* `negHom W : projModel W ⟶ projModel W`, the negation morphism (T-W7.0b), together with
  `negHom_projModelπ` (`negHom W ≫ π = π`), `negHom_involutive` (`negHom W ≫ negHom W = 𝟙`),
  and `projModelZero_negHom` (`[0:1:0]` is fixed).
-/

open AlgebraicGeometry CategoryTheory WeierstrassCurve MvPolynomial HomogeneousIdeal

universe u

namespace ModularCurves

/-- The universal discriminant `Δ ∈ ℤ[a₁,…,a₆]` is nonzero: specialising the coefficients to
the elliptic curve `y² = x³ − x` (`a₄ = −1`, other `aᵢ = 0`) sends `Δ` to `64 ≠ 0`. -/
theorem universalWeierstrass_Δ_ne_zero : universalWeierstrass.Δ ≠ 0 := by
  intro hΔ
  have key : (universalWeierstrass.map
      (MvPolynomial.eval (![0, 0, 0, -1, 0] : Fin 5 → ℤ))).Δ = 64 := by
    have e2 : (![0, 0, 0, -1, 0] : Fin 5 → ℤ) 2 = 0 := by decide
    have e3 : (![0, 0, 0, -1, 0] : Fin 5 → ℤ) 3 = -1 := by decide
    have e4 : (![0, 0, 0, -1, 0] : Fin 5 → ℤ) 4 = 0 := by decide
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.map, universalWeierstrass,
      MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, e2, e3, e4]
    norm_num
  rw [WeierstrassCurve.map_Δ, hΔ, map_zero] at key
  norm_num at key

/-- **(T-W7.0a)** The Weierstrass atlas ring `ℤ[a₁,…,a₆][Δ⁻¹]` is an integral domain — a
localization of the polynomial domain `MvPolynomial (Fin 5) ℤ` at the powers of the nonzero
discriminant. -/
instance instIsDomainWeierstrassAtlasRing : IsDomain WeierstrassAtlasRing :=
  have hle : Submonoid.powers universalWeierstrass.Δ ≤
      nonZeroDivisors (MvPolynomial (Fin 5) ℤ) :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero universalWeierstrass_Δ_ne_zero)
  IsLocalization.isDomain_localization hle

/-! ## T-W7.0b — the negation morphism -/

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

section Negation

variable {R : Type u} [CommRing R]

open HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

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

/-- **(T-W7.0b)** The negation morphism `[X:Y:Z] ↦ [X : −Y−a₁X−a₃Z : Z]` on the plane
projective Weierstrass model, as a `Proj` endomorphism (Silverman III.2.3). It is
denominator-free and linear on the chart at infinity. -/
noncomputable def negHom (W : WeierstrassCurve R) : projModel W ⟶ projModel W :=
  Proj.map (negGradedQuot W) (negGradedQuot_irrelevant_le W)

/-- **(T-W7.0b)** Negation is an involution: `[N] = [−1]` squares to the identity. -/
theorem negHom_involutive (W : WeierstrassCurve R) : negHom W ≫ negHom W = 𝟙 _ := by
  rw [negHom, ← Proj.map_comp]
  exact (Proj_map_congr (negGradedQuot_comp_self W) _ _).trans Proj.map_id

end Negation

end ModularCurves
