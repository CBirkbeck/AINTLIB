/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleFiltration
import ModularCurves.ForMathlib.AffinePointVariableChange
import ModularCurves.ForMathlib.ProjToSpecZero
import ModularCurves.ForMathlib.ProjMapScaling
import ModularCurves.ForMathlib.ProjFromGlobalSectionsMap

/-!
# Variable changes on the projective Weierstrass model, and the comparison theorem

**(T-W7 skeleton, lanes P3/P5 — `/develop --decompose` 2026-07-07.)** The action of
`WeierstrassCurve.VariableChange` on projective models (`projModelVCIso`, the projectivisation
of `(x, y) ↦ (u²x + r, u³y + su²x + t)`), its pointedness, faithfulness — and the
**comparison theorem** (T-W7.1b, audit A1): every pointed isomorphism of projective
Weierstrass models over an arbitrary ring is induced by a unique variable change. This is the
dependency the round-1 reviewer reply missed; without it, chart-overlap agreement of the
glued group law would circularly require canonicity. It is also fix-option (3) of the prior
B2 on `isWeierstrassModel_unique` (b2_log 2026-07-07), here WITHOUT BB-RR: the proof route is
the pole filtration of `PoleFiltration.lean`.

Sources: audit A1 (`expert-review/2026-07-07-tw7/integration.md`); KM §2.2/Deligne
*Formulaire*-style statement, proof re-derived uniformly (pole filtration + freeness).
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve HomogeneousIdeal

universe u

namespace ModularCurves

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- Homogenized `ivcX`/`ivcY` substitution `X ↦ u²X+rZ, Y ↦ u³Y+su²X+tZ, Z ↦ Z` — the
projectivisation of the coordinate change, on the polynomial ring. -/
noncomputable def vcMvSubst (C : VariableChange R) : Fin 3 → MvPolynomial (Fin 3) R :=
  ![(↑C.u : R) ^ 2 • MvPolynomial.X 0 + C.r • MvPolynomial.X 2,
    (↑C.u : R) ^ 3 • MvPolynomial.X 1 + (C.s * (↑C.u : R) ^ 2) • MvPolynomial.X 0
      + C.t • MvPolynomial.X 2,
    MvPolynomial.X 2]

/-- **(crux)** The projective variable-change substitution scales the homogeneous Weierstrass
cubic of `W` by `u⁶`, turning it into that of `C • W` (the projective form of the affine
`equation_smul` identity). This is the algebraic heart of `projModelVCIso`. -/
theorem vcMvSubst_polynomial (C : VariableChange R) (W : WeierstrassCurve R) :
    MvPolynomial.aeval (vcMvSubst C) W.toProjective.polynomial
      = (↑C.u : R) ^ 6 • (C • W).toProjective.polynomial := by
  have hu : (↑C.u : R) * ↑C.u⁻¹ = 1 := Units.mul_inv C.u
  have huinv : ∀ m n : ℕ, n ≤ m → (↑C.u : R) ^ m * (↑C.u⁻¹ : R) ^ n = (↑C.u : R) ^ (m - n) := by
    intro m n hnm
    conv_lhs => rw [show m = (m - n) + n from (Nat.sub_add_cancel hnm).symm]
    rw [pow_add, mul_assoc, ← mul_pow, hu, one_pow, mul_one]
  have Cl1 : ((MvPolynomial.C (↑C.u : R)) ^ 6 : MvPolynomial (Fin 3) R) * MvPolynomial.C
    ((C • W).a₁)
      = (MvPolynomial.C (↑C.u : R)) ^ 5 * (MvPolynomial.C W.a₁ + 2 * MvPolynomial.C C.s) := by
    have inner : (↑C.u : R) ^ 6 * (C • W).a₁ = (↑C.u : R) ^ 5 * (W.a₁ + 2 * C.s) := by
      rw [variableChange_a₁, ← pow_one (↑C.u⁻¹ : R), ← mul_assoc, huinv 6 1 (by norm_num)]
    rw [← map_pow, ← map_mul, inner]; simp only [map_mul, map_pow, map_add, map_ofNat]
  have Cl2 : ((MvPolynomial.C (↑C.u : R)) ^ 6 : MvPolynomial (Fin 3) R) * MvPolynomial.C
    ((C • W).a₂)
      = (MvPolynomial.C (↑C.u : R)) ^ 4 *
        (MvPolynomial.C W.a₂ - MvPolynomial.C C.s * MvPolynomial.C W.a₁
        + 3 * MvPolynomial.C C.r - MvPolynomial.C C.s ^ 2) := by
    have inner : (↑C.u : R) ^ 6 * (C • W).a₂
        = (↑C.u : R) ^ 4 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) := by
      rw [variableChange_a₂, ← mul_assoc, huinv 6 2 (by norm_num)]
    rw [← map_pow, ← map_mul, inner]; simp only [map_mul, map_pow, map_add, map_sub, map_ofNat]
  have Cl3 : ((MvPolynomial.C (↑C.u : R)) ^ 6 : MvPolynomial (Fin 3) R) * MvPolynomial.C
    ((C • W).a₃)
      = (MvPolynomial.C (↑C.u : R)) ^ 3 *
        (MvPolynomial.C W.a₃ + MvPolynomial.C C.r * MvPolynomial.C W.a₁
        + 2 * MvPolynomial.C C.t) := by
    have inner : (↑C.u : R) ^ 6 * (C • W).a₃ = (↑C.u : R) ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) := by
      rw [variableChange_a₃, ← mul_assoc, huinv 6 3 (by norm_num)]
    rw [← map_pow, ← map_mul, inner]; simp only [map_mul, map_pow, map_add, map_ofNat]
  have Cl4 : ((MvPolynomial.C (↑C.u : R)) ^ 6 : MvPolynomial (Fin 3) R) * MvPolynomial.C
    ((C • W).a₄)
      = (MvPolynomial.C (↑C.u : R)) ^ 2 *
        (MvPolynomial.C W.a₄ - MvPolynomial.C C.s * MvPolynomial.C W.a₃
        + 2 * MvPolynomial.C C.r * MvPolynomial.C W.a₂
        - (MvPolynomial.C C.t + MvPolynomial.C C.r * MvPolynomial.C C.s) * MvPolynomial.C W.a₁
        + 3 * MvPolynomial.C C.r ^ 2 - 2 * MvPolynomial.C C.s * MvPolynomial.C C.t) := by
    have inner : (↑C.u : R) ^ 6 * (C • W).a₄
        = (↑C.u : R) ^ 2 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁
          + 3 * C.r ^ 2 - 2 * C.s * C.t) := by
      rw [variableChange_a₄, ← mul_assoc, huinv 6 4 (by norm_num)]
    rw [← map_pow, ← map_mul, inner]; simp only [map_mul, map_pow, map_add, map_sub, map_ofNat]
  have Cl6 : ((MvPolynomial.C (↑C.u : R)) ^ 6 : MvPolynomial (Fin 3) R) * MvPolynomial.C
    ((C • W).a₆)
      = MvPolynomial.C W.a₆ + MvPolynomial.C C.r * MvPolynomial.C W.a₄
        + MvPolynomial.C C.r ^ 2 * MvPolynomial.C W.a₂ + MvPolynomial.C C.r ^ 3
        - MvPolynomial.C C.t * MvPolynomial.C W.a₃ - MvPolynomial.C C.t ^ 2
        - MvPolynomial.C C.r * MvPolynomial.C C.t * MvPolynomial.C W.a₁ := by
    have inner : (↑C.u : R) ^ 6 * (C • W).a₆
        = W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
          - C.r * C.t * W.a₁ := by
      rw [variableChange_a₆, ← mul_assoc, huinv 6 6 (by norm_num), pow_zero, one_mul]
    rw [← map_pow, ← map_mul, inner]; simp only [map_mul, map_pow, map_add, map_sub]
  simp only [WeierstrassCurve.Projective.polynomial, vcMvSubst,
    map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, MvPolynomial.algebraMap_eq,
    MvPolynomial.smul_eq_C_mul]
  linear_combination
    -(MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) * Cl1
      - (MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2) * Cl3
      + (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2) * Cl2
      + (MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2) * Cl4 + (MvPolynomial.X 2 ^ 3) * Cl6

/-- Each generator of the projective variable-change substitution is homogeneous of degree 1
(the substitution is linear), so `aeval (vcMvSubst C)` preserves the grading. -/
lemma vcMvSubst_isHomogeneous (C : VariableChange R) (j : Fin 3) :
    (vcMvSubst C j).IsHomogeneous 1 := by
  fin_cases j <;>
    simp only [vcMvSubst,
      MvPolynomial.smul_eq_C_mul]
  · exact (MvPolynomial.isHomogeneous_C_mul_X (R := R) _ _).add
      (MvPolynomial.isHomogeneous_C_mul_X (R := R) _ _)
  · exact ((MvPolynomial.isHomogeneous_C_mul_X (R := R) _ _).add
      (MvPolynomial.isHomogeneous_C_mul_X (R := R) _ _)).add
      (MvPolynomial.isHomogeneous_C_mul_X (R := R) _ _)
  · exact MvPolynomial.isHomogeneous_X (R := R) _

/-- The projective variable-change substitution as a graded ring homomorphism of the standard
grading on `MvPolynomial (Fin 3) R`. -/
noncomputable def vcMvGraded (C : VariableChange R) :
    GradedRingHom (MvPolynomial.homogeneousSubmodule (Fin 3) R)
      (MvPolynomial.homogeneousSubmodule (Fin 3) R) where
  toRingHom := (MvPolynomial.aeval (vcMvSubst C)).toRingHom
  map_mem {i x} hx := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hx ⊢
    have h := hx.aeval (vcMvSubst C) (vcMvSubst_isHomogeneous C)
    rwa [one_mul] at h

/-- The substitution carries the homogeneous Weierstrass ideal of `W` into that of `C • W`
(from the crux `vcMvSubst_polynomial`: the cubic maps to a unit multiple of the new cubic). -/
lemma projIdeal_le_comap_vc (C : VariableChange R) (W : WeierstrassCurve R) :
    (projIdeal W).toIdeal ≤
      (projIdeal (C • W)).toIdeal.comap (vcMvGraded C).toRingHom := by
  rw [projIdeal_toIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
  show MvPolynomial.aeval (vcMvSubst C) W.toProjective.polynomial ∈ _
  rw [vcMvSubst_polynomial, MvPolynomial.smul_eq_C_mul, projIdeal_toIdeal]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-- The graded homomorphism between the homogeneous coordinate rings of the projective models
of `W` and `C • W` induced by the variable change — the analogue of `baseChangeGradedHom`. -/
noncomputable def vcGradedHom (C : VariableChange R) (W : WeierstrassCurve R) :
    GradedRingHom (quotientGrading (projIdeal W)) (quotientGrading (projIdeal (C • W))) :=
  quotientGradingMap (vcMvGraded C) (projIdeal W) (projIdeal (C • W)) (projIdeal_le_comap_vc C W)

/-- The variable-change substitution and its inverse (via `C⁻¹`) compose to the identity
on the polynomial generators. -/
theorem vcMvSubst_comp_inv (C : VariableChange R) (j : Fin 3) :
    MvPolynomial.aeval (vcMvSubst C) (vcMvSubst C⁻¹ j) = MvPolynomial.X j := by
  have hupow : ∀ n : ℕ, (MvPolynomial.C (↑C.u⁻¹ : R) : MvPolynomial (Fin 3) R) ^ n
      * MvPolynomial.C (↑C.u : R) ^ n = 1 := by
    intro n; rw [← mul_pow, ← map_mul, Units.inv_mul, map_one, one_pow]
  fin_cases j
  · show MvPolynomial.aeval (vcMvSubst C) (vcMvSubst C⁻¹ (0 : Fin 3)) = MvPolynomial.X (0 : Fin 3)
    simp only [vcMvSubst, VariableChange.inv_def, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val, map_add, map_sub, map_mul, map_pow,
      map_neg, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.smul_eq_C_mul,
      MvPolynomial.algebraMap_eq]
    linear_combination MvPolynomial.X (0 : Fin 3) * hupow 2
  · show MvPolynomial.aeval (vcMvSubst C) (vcMvSubst C⁻¹ (1 : Fin 3)) = MvPolynomial.X (1 : Fin 3)
    simp only [vcMvSubst, VariableChange.inv_def, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, map_add, map_sub, map_mul, map_pow,
      map_neg, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.smul_eq_C_mul,
      MvPolynomial.algebraMap_eq]
    linear_combination MvPolynomial.X (1 : Fin 3) * hupow 3
  · show MvPolynomial.aeval (vcMvSubst C) (vcMvSubst C⁻¹ (2 : Fin 3)) = MvPolynomial.X (2 : Fin 3)
    simp only [vcMvSubst, VariableChange.inv_def, Fin.isValue,
      Matrix.cons_val, MvPolynomial.aeval_X]

/-- Reverse composition on generators, free via `inv_inv`. -/
theorem vcMvSubst_inv_comp (C : VariableChange R) (j : Fin 3) :
    MvPolynomial.aeval (vcMvSubst C⁻¹) (vcMvSubst C j) = MvPolynomial.X j := by
  have h := vcMvSubst_comp_inv C⁻¹ j
  rwa [inv_inv] at h

/-- Ring-level: the two substitutions compose to the identity `AlgHom`. -/
theorem vcMvSubst_comp_inv_algHom (C : VariableChange R) :
    (MvPolynomial.aeval (vcMvSubst C)).comp (MvPolynomial.aeval (vcMvSubst C⁻¹))
      = AlgHom.id R (MvPolynomial (Fin 3) R) := by
  rw [MvPolynomial.comp_aeval]; simp only [vcMvSubst_comp_inv]; exact MvPolynomial.aeval_X_left

theorem vcMvSubst_inv_comp_algHom (C : VariableChange R) :
    (MvPolynomial.aeval (vcMvSubst C⁻¹)).comp (MvPolynomial.aeval (vcMvSubst C))
      = AlgHom.id R (MvPolynomial (Fin 3) R) := by
  rw [MvPolynomial.comp_aeval]; simp only [vcMvSubst_inv_comp]; exact MvPolynomial.aeval_X_left

/-- The inverse-direction ideal containment, via `C⁻¹ • (C • W) = W`. -/
lemma projIdeal_le_comap_vc_inv (C : VariableChange R) (W : WeierstrassCurve R) :
    (projIdeal (C • W)).toIdeal ≤ (projIdeal W).toIdeal.comap (vcMvGraded C⁻¹).toRingHom := by
  have h := projIdeal_le_comap_vc C⁻¹ (C • W)
  rwa [inv_smul_smul] at h

/-- The inverse graded homomorphism of quotient coordinate rings, induced by `C⁻¹`. -/
noncomputable def vcGradedHomInv (C : VariableChange R) (W : WeierstrassCurve R) :
    GradedRingHom (quotientGrading (projIdeal (C • W))) (quotientGrading (projIdeal W)) :=
  quotientGradingMap (vcMvGraded C⁻¹) (projIdeal (C • W)) (projIdeal W)
    (projIdeal_le_comap_vc_inv C W)

lemma vcGradedHom_comp_inv_apply (C : VariableChange R) (W : WeierstrassCurve R)
    (x : projCoordRing (C • W)) : vcGradedHom C W (vcGradedHomInv C W x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [vcGradedHomInv, vcGradedHom, quotientGradingMap_mk, quotientGradingMap_mk]
  refine congrArg (Ideal.Quotient.mk _) ?_
  show MvPolynomial.aeval (vcMvSubst C) (MvPolynomial.aeval (vcMvSubst C⁻¹) a) = a
  rw [← AlgHom.comp_apply, vcMvSubst_comp_inv_algHom, AlgHom.id_apply]

lemma vcGradedHom_inv_comp_apply (C : VariableChange R) (W : WeierstrassCurve R)
    (x : projCoordRing W) : vcGradedHomInv C W (vcGradedHom C W x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [vcGradedHom, vcGradedHomInv, quotientGradingMap_mk, quotientGradingMap_mk]
  refine congrArg (Ideal.Quotient.mk _) ?_
  show MvPolynomial.aeval (vcMvSubst C⁻¹) (MvPolynomial.aeval (vcMvSubst C) a) = a
  rw [← AlgHom.comp_apply, vcMvSubst_inv_comp_algHom, AlgHom.id_apply]

/-- The forward and inverse variable-change graded homs compose to the identity. -/
lemma vcGradedHom_comp_inv (C : VariableChange R) (W : WeierstrassCurve R) :
    (vcGradedHom C W).comp (vcGradedHomInv C W) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => vcGradedHom_comp_inv_apply C W x

lemma vcGradedHom_inv_comp (C : VariableChange R) (W : WeierstrassCurve R) :
    (vcGradedHomInv C W).comp (vcGradedHom C W) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => vcGradedHom_inv_comp_apply C W x

/-- A graded ring homomorphism maps the irrelevant ideal into the irrelevant ideal. -/
private lemma irrelevant_map_le {ι σ τ A B : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
    {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) :
    HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜) ≤ HomogeneousIdeal.irrelevant ℬ := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map,
    Ideal.map_le_iff_le_comap, HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi x hx
  exact HomogeneousIdeal.mem_irrelevant_of_mem _ hi (f.map_mem hx)

/-- The irrelevant-ideal hypothesis of `Proj.map` for the forward variable-change hom,
discharged via the inverse: `f = (f⁻¹)⁻¹` maps the irrelevant ideal onto itself. -/
lemma vcGradedHom_irrelevant_le (C : VariableChange R) (W : WeierstrassCurve R) :
    (quotientGrading (projIdeal (C • W)))₊ ≤
      ((quotientGrading (projIdeal W))₊).map (vcGradedHom C W) := by
  conv_lhs => rw [← HomogeneousIdeal.map_id (I := (quotientGrading (projIdeal (C • W)))₊),
    ← vcGradedHom_comp_inv C W, HomogeneousIdeal.map_comp]
  exact HomogeneousIdeal.map_mono _ (irrelevant_map_le (vcGradedHomInv C W))

lemma vcGradedHomInv_irrelevant_le (C : VariableChange R) (W : WeierstrassCurve R) :
    (quotientGrading (projIdeal W))₊ ≤
      ((quotientGrading (projIdeal (C • W)))₊).map (vcGradedHomInv C W) := by
  conv_lhs => rw [← HomogeneousIdeal.map_id (I := (quotientGrading (projIdeal W))₊),
    ← vcGradedHom_inv_comp C W, HomogeneousIdeal.map_comp]
  exact HomogeneousIdeal.map_mono _ (irrelevant_map_le (vcGradedHom C W))

/-- Equality of `Proj.map`s from equal graded homomorphisms (the irrelevant-ideal
hypotheses are propositions, so they may differ). -/
private lemma Proj_map_congr {A B σ τ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    {f g : 𝒜 →+*ᵍ ℬ} (h : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    Proj.map f hf = Proj.map g hg := by subst h; rfl

/-- **(T-W7.0h-i)** The isomorphism of projective Weierstrass models induced by a variable
change `C = (u, r, s, t)`: the projectivisation of the affine coordinate change
`(x, y) ↦ (u²x + r, u³y + su²x + t)` (mathlib's `VariableChange` convention), an isomorphism
`projModel (C • W) ≅ projModel W`. Source: Silverman III.3.1(b) (projective form); the graded
ring map mirrors `baseChangeGradedHom`. -/
noncomputable def projModelVCIso (C : VariableChange R) (W : WeierstrassCurve R) :
    projModel (C • W) ≅ projModel W where
  hom := Proj.map (vcGradedHom C W) (vcGradedHom_irrelevant_le C W)
  inv := Proj.map (vcGradedHomInv C W) (vcGradedHomInv_irrelevant_le C W)
  hom_inv_id := by
    rw [← Proj.map_comp]
    exact (Proj_map_congr (vcGradedHom_comp_inv C W) _ _).trans Proj.map_id
  inv_hom_id := by
    rw [← Proj.map_comp]
    exact (Proj_map_congr (vcGradedHom_inv_comp C W) _ _).trans Proj.map_id

/-- The variable-change hom fixes the degree-`0` structural image of `R` (it fixes constants),
landing in the target curve's `R`-structure — the ring-level input making `projModelVCIso` a
morphism over `Spec R`. -/
lemma vcGradedHom_algebraMapGradeZero (C : VariableChange R) (W : WeierstrassCurve R) :
    (gradedRingHomZero (vcGradedHom C W)).comp (algebraMapGradeZero (projIdeal W)) =
      algebraMapGradeZero (projIdeal (C • W)) := by
  refine RingHom.ext fun r => Subtype.ext ?_
  simp only [RingHom.coe_comp, Function.comp_apply, gradedRingHomZero_coe]
  show vcGradedHom C W (algebraMap R (projCoordRing W) r) = algebraMap R (projCoordRing (C • W)) r
  have hmk : ∀ V : WeierstrassCurve R, algebraMap R (projCoordRing V) r =
      Ideal.Quotient.mk (projIdeal V).toIdeal (MvPolynomial.C r) := fun V => by
    rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing V),
      RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
  rw [hmk W, hmk (C • W), vcGradedHom, quotientGradingMap_mk]
  exact congrArg (Ideal.Quotient.mk _)
    (show MvPolynomial.aeval (vcMvSubst C) (MvPolynomial.C r) = MvPolynomial.C r by
      rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq])

/-- **(T-W7.0h-i, π-compatibility)** `projModelVCIso` is a morphism over `Spec R`. -/
theorem projModelVCIso_π (C : VariableChange R) (W : WeierstrassCurve R) :
    (projModelVCIso C W).hom ≫ projModelπ W = projModelπ (C • W) := by
  show Proj.map (vcGradedHom C W) (vcGradedHom_irrelevant_le C W) ≫ projModelπ W =
    projModelπ (C • W)
  simp only [projModelπ]
  rw [← Category.assoc,
    map_comp_toSpecZero (vcGradedHom C W) (vcGradedHom_irrelevant_le C W), Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, vcGradedHom_algebraMapGradeZero]

/-! ### The unit-rescaling automorphism `μ = u³`: projective triviality of `[0:u³:0] = [0:1:0]`

The variable change scales the leading `Y`-coordinate at infinity by `u³`
(`projModelZeroEval (C • W) ∘ vcGradedHom C W` is evaluation at `(0, u³, 0)`, not `(0, 1, 0)`).
That rescaling is discharged through the "scale all coordinates by the unit `μ`" automorphism
`allScaleGradedQuot`, generalising `GroupLawConstruction`'s `−1`-rescaling `allNeg` to an
arbitrary unit; `Proj.map` of it is the identity by `Proj.map_degScaling_eq_id`. -/

/-- Uniform rescaling of all three homogeneous coordinates by a unit `μ`. -/
noncomputable def allScaleVec (μ : Rˣ) : Fin 3 → MvPolynomial (Fin 3) R :=
  ![(μ : R) • MvPolynomial.X 0, (μ : R) • MvPolynomial.X 1, (μ : R) • MvPolynomial.X 2]

lemma allScaleVec_isHomogeneous (μ : Rˣ) (i : Fin 3) :
    (allScaleVec μ i : MvPolynomial (Fin 3) R).IsHomogeneous 1 := by
  fin_cases i <;>
    simp only [allScaleVec,
      MvPolynomial.smul_eq_C_mul]
  · exact MvPolynomial.isHomogeneous_C_mul_X (R := R) _ _
  · exact MvPolynomial.isHomogeneous_C_mul_X (R := R) _ _
  · exact MvPolynomial.isHomogeneous_C_mul_X (R := R) _ _

/-- Scaling all variables by `μ` sends the degree-`3` Weierstrass cubic to `μ³` times itself. -/
lemma allScaleVec_polynomial (μ : Rˣ) (W : WeierstrassCurve R) :
    MvPolynomial.aeval (allScaleVec μ) W.toProjective.polynomial
      = (μ : R) ^ 3 • W.toProjective.polynomial := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    allScaleVec, MvPolynomial.algebraMap_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, MvPolynomial.smul_eq_C_mul]
  ring

lemma allScaleVec_comp_inv (μ : Rˣ) (i : Fin 3) :
    MvPolynomial.aeval (allScaleVec μ) (allScaleVec μ⁻¹ i) = MvPolynomial.X i := by
  fin_cases i
  · show MvPolynomial.aeval (allScaleVec μ) (allScaleVec μ⁻¹ (0 : Fin 3))
        = MvPolynomial.X (0 : Fin 3)
    simp [allScaleVec, smul_smul, Units.inv_mul]
  · show MvPolynomial.aeval (allScaleVec μ) (allScaleVec μ⁻¹ (1 : Fin 3))
        = MvPolynomial.X (1 : Fin 3)
    simp [allScaleVec, smul_smul, Units.inv_mul]
  · show MvPolynomial.aeval (allScaleVec μ) (allScaleVec μ⁻¹ (2 : Fin 3))
        = MvPolynomial.X (2 : Fin 3)
    simp [allScaleVec, smul_smul, Units.inv_mul]

lemma allScaleRingHom_comp_inv (μ : Rˣ) (p : MvPolynomial (Fin 3) R) :
    MvPolynomial.aeval (allScaleVec μ) (MvPolynomial.aeval (allScaleVec μ⁻¹) p) = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, MvPolynomial.aeval_X, map_mul, hp, allScaleVec_comp_inv]

/-- The uniform rescaling as a graded endomorphism of `R[X,Y,Z]`. -/
noncomputable def allScaleGradedPoly (μ : Rˣ) :
    MvPolynomial.homogeneousSubmodule (Fin 3) R →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin 3) R where
  toRingHom := (MvPolynomial.aeval (allScaleVec μ)).toRingHom
  map_mem {n x} hx := by
    have h := ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hx).aeval (allScaleVec μ)
      (allScaleVec_isHomogeneous μ)
    rw [one_mul] at h
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr h

lemma allScaleGradedPoly_comap (μ : Rˣ) (W : WeierstrassCurve R) :
    (projIdeal W).toIdeal ≤ (projIdeal W).toIdeal.comap (allScaleGradedPoly μ).toRingHom := by
  rw [projIdeal_toIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
  show MvPolynomial.aeval (allScaleVec μ) W.toProjective.polynomial ∈ _
  rw [allScaleVec_polynomial, MvPolynomial.smul_eq_C_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- The unit-rescaling automorphism of the quotient coordinate ring (`μ = u³` at infinity). -/
noncomputable def allScaleGradedQuot (μ : Rˣ) (W : WeierstrassCurve R) :
    quotientGrading (projIdeal W) →+*ᵍ quotientGrading (projIdeal W) :=
  quotientGradingMap (allScaleGradedPoly μ) (projIdeal W) (projIdeal W)
    (allScaleGradedPoly_comap μ W)

lemma allScaleGradedQuot_comp_inv_apply (μ : Rˣ) (W : WeierstrassCurve R) (x : projCoordRing W) :
    allScaleGradedQuot μ W (allScaleGradedQuot μ⁻¹ W x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [allScaleGradedQuot, allScaleGradedQuot, quotientGradingMap_mk, quotientGradingMap_mk]
  exact congrArg (Ideal.Quotient.mk _) (allScaleRingHom_comp_inv μ a)

lemma allScaleGradedQuot_comp_inv (μ : Rˣ) (W : WeierstrassCurve R) :
    (allScaleGradedQuot μ W).comp (allScaleGradedQuot μ⁻¹ W) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => allScaleGradedQuot_comp_inv_apply μ W x

lemma allScaleGradedQuot_irrelevant_le (μ : Rˣ) (W : WeierstrassCurve R) :
    (quotientGrading (projIdeal W))₊ ≤
      ((quotientGrading (projIdeal W))₊).map (allScaleGradedQuot μ W) := by
  conv_lhs => rw [← HomogeneousIdeal.map_id (I := (quotientGrading (projIdeal W))₊),
    ← allScaleGradedQuot_comp_inv μ W, HomogeneousIdeal.map_comp]
  exact HomogeneousIdeal.map_mono _ (irrelevant_map_le (allScaleGradedQuot μ⁻¹ W))

/-- Uniform rescaling scales a degree-`d` homogeneous polynomial by `μᵈ`. -/
lemma allScaleVec_smul_of_homogeneous (μ : Rˣ) {d : ℕ} {p : MvPolynomial (Fin 3) R}
    (hp : p.IsHomogeneous d) :
    MvPolynomial.aeval (allScaleVec μ) p = MvPolynomial.C ((μ : R) ^ d) * p := by
  have hv : (allScaleVec μ) = (fun i : Fin 3 => MvPolynomial.C (μ : R) * MvPolynomial.X i) := by
    funext i; fin_cases i <;> simp [allScaleVec, MvPolynomial.smul_eq_C_mul]
  rw [hv]
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hvdeg : v.degree = d := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hv) (hp.coeff_eq_zero h)
  have hprod : (v.prod fun i e =>
        (MvPolynomial.C (μ : R) * MvPolynomial.X i : MvPolynomial (Fin 3) R) ^ e)
      = MvPolynomial.C ((μ : R) ^ d) * v.prod (fun i e => (MvPolynomial.X i) ^ e) := by
    simp only [Finsupp.prod]
    rw [Finset.prod_congr rfl
        (fun i _ => mul_pow (MvPolynomial.C (μ : R)) (MvPolynomial.X i) (v i)),
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hvdeg,
      ← map_pow]
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.monomial_eq, hprod]
  ring

/-- `allScaleGradedQuot μ` scales a degree-`d` homogeneous class by `μᵈ`: the `hscale` hypothesis
feeding `Proj.map_degScaling_eq_id`. -/
lemma allScaleGradedQuot_scale (μ : Rˣ) (W : WeierstrassCurve R) (d : ℕ) {a : projCoordRing W}
    (ha : a ∈ (quotientGrading (projIdeal W)) d) :
    allScaleGradedQuot μ W a = (algebraMap R (projCoordRing W) (μ : R)) ^ d * a := by
  obtain ⟨p, hp, hmap⟩ := Submodule.mem_map.mp ha
  have ha_eq : a = Ideal.Quotient.mk (projIdeal W).toIdeal p := hmap.symm
  rw [ha_eq, allScaleGradedQuot, quotientGradingMap_mk]
  show Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.aeval (allScaleVec μ) p) =
    (algebraMap R (projCoordRing W) (μ : R)) ^ d * Ideal.Quotient.mk (projIdeal W).toIdeal p
  rw [allScaleVec_smul_of_homogeneous μ ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp),
    map_mul, ← map_pow]
  congr 1

/-- **(T-W7.0h-i-μ)** `Proj.map` of the unit-rescaling automorphism is the identity: rescaling
every homogeneous coordinate by a unit fixes each point of `Proj` projectively. -/
theorem allScale_map_id (μ : Rˣ) (W : WeierstrassCurve R) :
    Proj.map (allScaleGradedQuot μ W) (allScaleGradedQuot_irrelevant_le μ W) = 𝟙 (projModel W) :=
  Proj.map_degScaling_eq_id (allScaleGradedQuot μ W)
    (Units.map (algebraMap R (projCoordRing W)).toMonoidHom μ)
    (allScaleGradedQuot_scale μ W)
    (allScaleGradedQuot_irrelevant_le μ W)

/-- On global sections, evaluation at infinity absorbs the variable change into the `u³`
rescaling: `projModelZeroEval (C • W) ∘ vcGradedHom C W = projModelZeroEval W ∘ allScale u³`
(both are evaluation at `(0, u³, 0)`). This is the ring-level identity feeding
`projModelVCIso_zero`. -/
lemma projModelZeroEval_vc_eq_allScale (C : VariableChange R) (W : WeierstrassCurve R) :
    (projModelZeroEval (C • W)).comp (vcGradedHom C W).toRingHom =
      (projModelZeroEval W).comp (allScaleGradedQuot (C.u ^ 3) W).toRingHom := by
  refine RingHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [RingHom.comp_apply]
  show projModelZeroEval (C • W) (vcGradedHom C W (Ideal.Quotient.mk _ p)) =
    projModelZeroEval W (allScaleGradedQuot (C.u ^ 3) W (Ideal.Quotient.mk _ p))
  rw [vcGradedHom, allScaleGradedQuot, quotientGradingMap_mk, quotientGradingMap_mk,
    projModelZeroEval_mk, projModelZeroEval_mk]
  show (MvPolynomial.aeval (fun i : Fin 3 => if i = 1 then (1 : R) else 0))
        (MvPolynomial.aeval (vcMvSubst C) p) =
      (MvPolynomial.aeval (fun i : Fin 3 => if i = 1 then (1 : R) else 0))
        (MvPolynomial.aeval (allScaleVec (C.u ^ 3)) p)
  rw [MvPolynomial.comp_aeval_apply, MvPolynomial.comp_aeval_apply]
  refine congrArg (fun g => MvPolynomial.aeval g p) (funext fun i => ?_)
  fin_cases i <;>
    simp [vcMvSubst, allScaleVec, Units.val_pow_eq_pow_val]

/-- **(T-W7.0h-i, pointedness)** `projModelVCIso` carries the point at infinity to the point
at infinity ( `[0:1:0]` is fixed by the projectivised coordinate change). The change scales the
leading `Y` at infinity by `u³`; the rescaling `[0:u³:0] = [0:1:0]` is discharged through the
unit-rescaling automorphism `allScale u³` (`allScale_map_id`), via naturality of
`Proj.fromOfGlobalSections` under `Proj.map`. -/
theorem projModelVCIso_zero (C : VariableChange R) (W : WeierstrassCurve R) :
    projModelZero (C • W) ≫ (projModelVCIso C W).hom = projModelZero W := by
  show projModelZero (C • W) ≫ Proj.map (vcGradedHom C W) (vcGradedHom_irrelevant_le C W) =
    projModelZero W
  have key := Proj.fromOfGlobalSections_map (vcGradedHom C W) (vcGradedHom_irrelevant_le C W)
    ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval (C • W)))
    (projModelZeroEval_irrelevant_map_top (C • W))
    (Proj.irrelevant_map_comp_toRingHom_eq_top (vcGradedHom C W) (vcGradedHom_irrelevant_le C W) _
      (projModelZeroEval_irrelevant_map_top (C • W)))
  have key2 := Proj.fromOfGlobalSections_map (allScaleGradedQuot (C.u ^ 3) W)
    (allScaleGradedQuot_irrelevant_le (C.u ^ 3) W)
    ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W))
    (projModelZeroEval_irrelevant_map_top W)
    (Proj.irrelevant_map_comp_toRingHom_eq_top (allScaleGradedQuot (C.u ^ 3) W)
      (allScaleGradedQuot_irrelevant_le (C.u ^ 3) W) _ (projModelZeroEval_irrelevant_map_top W))
  have hfeq : ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval (C • W))).comp
        (vcGradedHom C W).toRingHom =
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W)).comp
        (allScaleGradedQuot (C.u ^ 3) W).toRingHom := by
    rw [RingHom.comp_assoc, projModelZeroEval_vc_eq_allScale, ← RingHom.comp_assoc]
  have congr_from : ∀ (g₁ g₂ : projCoordRing W →+* Γ(Spec (.of R), ⊤))
      (h₁ : (HomogeneousIdeal.irrelevant
          (HomogeneousIdeal.quotientGrading (projIdeal W))).toIdeal.map g₁ = ⊤)
      (h₂ : (HomogeneousIdeal.irrelevant
          (HomogeneousIdeal.quotientGrading (projIdeal W))).toIdeal.map g₂ = ⊤),
      g₁ = g₂ →
      Proj.fromOfGlobalSections (HomogeneousIdeal.quotientGrading (projIdeal W)) g₁ h₁ =
        Proj.fromOfGlobalSections (HomogeneousIdeal.quotientGrading (projIdeal W)) g₂ h₂ := by
    rintro g₁ g₂ h₁ h₂ rfl; rfl
  rw [projModelZero, projModelZero, key,
    ← Category.comp_id (Proj.fromOfGlobalSections (HomogeneousIdeal.quotientGrading (projIdeal W))
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W))
      (projModelZeroEval_irrelevant_map_top W)), ← allScale_map_id (C.u ^ 3) W, key2]
  exact congr_from _ _ _ _ hfeq

/-- **Base-change naturality of the substitution**: applying the coefficient map `f` to the
variable-change substitution for `C` gives the substitution for the base-changed `C.map f`. -/
lemma vcMvSubst_map {R' : Type u} [CommRing R'] (f : R →+* R') (C : VariableChange R) (i : Fin 3) :
    MvPolynomial.map f (vcMvSubst C i) = vcMvSubst (C.map f) i := by
  fin_cases i
  · show MvPolynomial.map f (vcMvSubst C (0 : Fin 3)) = vcMvSubst (C.map f) (0 : Fin 3)
    simp only [vcMvSubst, VariableChange.map_u, VariableChange.map_r, Fin.isValue,
      Matrix.cons_val_zero,
      MvPolynomial.smul_eq_C_mul, map_add, map_mul, map_pow, MvPolynomial.map_C,
      MvPolynomial.map_X, Units.coe_map, MonoidHom.coe_coe]
  · show MvPolynomial.map f (vcMvSubst C (1 : Fin 3)) = vcMvSubst (C.map f) (1 : Fin 3)
    simp only [vcMvSubst, VariableChange.map_u, VariableChange.map_r, VariableChange.map_s,
      VariableChange.map_t, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      MvPolynomial.smul_eq_C_mul, map_add, map_mul, map_pow,
      MvPolynomial.map_C, MvPolynomial.map_X, Units.coe_map, MonoidHom.coe_coe]
  · show MvPolynomial.map f (vcMvSubst C (2 : Fin 3)) = vcMvSubst (C.map f) (2 : Fin 3)
    simp only [vcMvSubst, Fin.isValue,
      Matrix.cons_val, MvPolynomial.map_X]

set_option backward.isDefEq.respectTransparency.types false in
/-- HEq-based transport: an `eqToHom` from a curve equality absorbs into `Proj.map`, bridged
by an `HEq` of the graded homs. -/
private lemma projMap_transport_heq {R' : Type u} [CommRing R'] (W : WeierstrassCurve R)
    {V V' : WeierstrassCurve R'} (e : V' = V)
    (g : GradedRingHom (quotientGrading (projIdeal W)) (quotientGrading (projIdeal V)))
    (hg : (quotientGrading (projIdeal V))₊ ≤ ((quotientGrading (projIdeal W))₊).map g)
    (g' : GradedRingHom (quotientGrading (projIdeal W)) (quotientGrading (projIdeal V')))
    (hg' : (quotientGrading (projIdeal V'))₊ ≤ ((quotientGrading (projIdeal W))₊).map g')
    (hgg : HEq g g') :
    Proj.map g hg = eqToHom (congrArg projModel e.symm) ≫ Proj.map g' hg' := by
  subst e
  obtain rfl := eq_of_heq hgg
  simp

/-- `HEq` of graded homs into coordinate rings of equal curves, from pointwise `HEq`. -/
private lemma gradedHom_heq {R' : Type u} [CommRing R'] (W : WeierstrassCurve R)
    {V V' : WeierstrassCurve R'} (e : V = V')
    (g : GradedRingHom (quotientGrading (projIdeal W)) (quotientGrading (projIdeal V)))
    (g' : GradedRingHom (quotientGrading (projIdeal W)) (quotientGrading (projIdeal V')))
    (h : ∀ x, HEq (g x) (g' x)) : HEq g g' := by
  subst e
  exact heq_of_eq (GradedRingHom.ext fun x => eq_of_heq (h x))

/-- `HEq` of quotient classes from an equality of the underlying curves. -/
private lemma mk_heq {R' : Type u} [CommRing R'] {V V' : WeierstrassCurve R'} (e : V = V')
    (q : MvPolynomial (Fin 3) R') :
    HEq (Ideal.Quotient.mk (projIdeal V).toIdeal q)
      (Ideal.Quotient.mk (projIdeal V').toIdeal q) := by
  subst e; rfl

/-- The coefficient map commutes with the variable-change substitution (general polynomial). -/
lemma map_aeval_vcMvSubst {R' : Type u} [CommRing R'] (f : R →+* R') (C : VariableChange R)
    (p : MvPolynomial (Fin 3) R) :
    MvPolynomial.map f (MvPolynomial.aeval (vcMvSubst C) p) =
      MvPolynomial.aeval (vcMvSubst (C.map f)) (MvPolynomial.map f p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp only [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.map_X, hp, vcMvSubst_map]

set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-W7.0h-i, base-change naturality — coordinator §2-P5)** `projModelVCIso` is natural
under base change of the ground ring: base-changing then applying the base-changed variable
change agrees with applying the variable change then base-changing (`map_variableChange`
identifies the two source models). Consumed by the `classifyRingHom` transport in the
group-law descent (`T-W7.0h`), which reduces a chart's variable change to the universal one. -/
theorem projModelVCIso_map {R' : Type u} [CommRing R'] [Algebra R R']
    (C : VariableChange R) (W : WeierstrassCurve R) :
    projModelBaseChange (algebraMap R R') (C • W) ≫ (projModelVCIso C W).hom =
      eqToHom (by rw [map_variableChange]) ≫
        (projModelVCIso (C.map (algebraMap R R')) (W.map (algebraMap R R'))).hom ≫
          projModelBaseChange (algebraMap R R') W := by
  have e : (C.map (algebraMap R R')) • (W.map (algebraMap R R')) = (C • W).map (algebraMap R R') :=
    map_variableChange ..
  show Proj.map (baseChangeGradedHom (algebraMap R R') (C • W)) _ ≫
      Proj.map (vcGradedHom C W) _ =
    eqToHom (by rw [map_variableChange]) ≫
      Proj.map (vcGradedHom (C.map (algebraMap R R')) (W.map (algebraMap R R'))) _ ≫
        Proj.map (baseChangeGradedHom (algebraMap R R') W) _
  rw [← Proj.map_comp, ← Proj.map_comp]
  refine projMap_transport_heq W e _ _ _ _ (gradedHom_heq W e.symm _ _ fun x => ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  show HEq (baseChangeGradedHom (algebraMap R R') (C • W)
      (vcGradedHom C W (Ideal.Quotient.mk _ a)))
    (vcGradedHom (C.map (algebraMap R R')) (W.map (algebraMap R R'))
      (baseChangeGradedHom (algebraMap R R') W (Ideal.Quotient.mk _ a)))
  rw [vcGradedHom, baseChangeGradedHom, quotientGradingMap_mk, quotientGradingMap_mk,
    baseChangeGradedHom, vcGradedHom, quotientGradingMap_mk, quotientGradingMap_mk]
  exact (mk_heq e.symm _).trans
    (heq_of_eq (congrArg _ (map_aeval_vcMvSubst (algebraMap R R') C a)))

/-- The identity variable-change substitution is the identity family `X`. -/
lemma vcMvSubst_one : vcMvSubst (1 : VariableChange R) = MvPolynomial.X := by
  funext i
  fin_cases i <;>
    simp [vcMvSubst, WeierstrassCurve.VariableChange.one_def, Units.val_one, one_pow, one_smul,
      zero_smul, add_zero]

/-- `aeval` at the identity variable-change substitution is the identity. -/
lemma aeval_vcMvSubst_one (p : MvPolynomial (Fin 3) R) :
    MvPolynomial.aeval (vcMvSubst (1 : VariableChange R)) p = p := by
  rw [vcMvSubst_one, MvPolynomial.aeval_X_left, AlgHom.id_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-- **(map_id support, [REQ→A-lane])** The identity variable change induces the identity model
isomorphism (the `_one` cocycle law, sibling of `projModelVCIso_mul`): `projModelVCIso 1 W` is
`eqToHom` of `1 • W = W`. -/
theorem projModelVCIso_one (W : WeierstrassCurve R) :
    (projModelVCIso (1 : VariableChange R) W).hom = eqToHom (by rw [one_smul]) := by
  have e : W = (1 : VariableChange R) • W := (one_smul _ W).symm
  rw [show (projModelVCIso 1 W).hom
        = Proj.map (vcGradedHom 1 W) (vcGradedHom_irrelevant_le 1 W) from rfl,
    projMap_transport_heq W e (vcGradedHom 1 W) (vcGradedHom_irrelevant_le 1 W)
      (GradedRingHom.id (quotientGrading (projIdeal W))) (le_of_eq (by simp))
      (gradedHom_heq W e.symm _ _ (fun x => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [vcGradedHom, quotientGradingMap_mk]
        exact (mk_heq e.symm _).trans (heq_of_eq (congrArg _ (aeval_vcMvSubst_one a)))))]
  rw [Proj.map_id, Category.comp_id]

/-- **Substitution cocycle**: the group product of variable changes composes the substitutions. -/
lemma vcMvSubst_mul (C C' : VariableChange R) (i : Fin 3) :
    vcMvSubst (C * C') i = MvPolynomial.aeval (vcMvSubst C) (vcMvSubst C' i) := by
  fin_cases i
  · show vcMvSubst (C * C') (0 : Fin 3) = MvPolynomial.aeval (vcMvSubst C) (vcMvSubst C'
    (0 : Fin 3))
    simp only [vcMvSubst, VariableChange.mul_def, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val, MvPolynomial.smul_eq_C_mul, map_add,
      map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
      Units.val_mul]
    ring
  · show vcMvSubst (C * C') (1 : Fin 3) = MvPolynomial.aeval (vcMvSubst C) (vcMvSubst C'
    (1 : Fin 3))
    simp only [vcMvSubst, VariableChange.mul_def, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, MvPolynomial.smul_eq_C_mul, map_add,
      map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
      Units.val_mul]
    ring
  · show vcMvSubst (C * C') (2 : Fin 3) = MvPolynomial.aeval (vcMvSubst C) (vcMvSubst C'
    (2 : Fin 3))
    simp only [vcMvSubst, Fin.isValue,
      Matrix.cons_val, MvPolynomial.aeval_X]

/-- Ring-level substitution cocycle on a general polynomial. -/
lemma aeval_vcMvSubst_mul (C C' : VariableChange R) (p : MvPolynomial (Fin 3) R) :
    MvPolynomial.aeval (vcMvSubst (C * C')) p =
      MvPolynomial.aeval (vcMvSubst C) (MvPolynomial.aeval (vcMvSubst C') p) := by
  conv_rhs => rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  exact congrArg MvPolynomial.aeval (funext fun i => vcMvSubst_mul C C' i)

/-- **(T-W7.0h-i, cocycle)** The model isomorphisms compose according to the
`VariableChange` group law (contravariantly on the acted curve). Source: the affine cocycle
`vcX_comp`/`vcY_comp` (`ForMathlib/AffinePointVariableChange`, DONE), projectivised. -/
theorem projModelVCIso_mul (C C' : VariableChange R) (W : WeierstrassCurve R) :
    (projModelVCIso (C * C') W).hom =
      (eqToHom (by rw [mul_smul])) ≫ (projModelVCIso C (C' • W)).hom ≫
        (projModelVCIso C' W).hom := by
  have e : C • (C' • W) = (C * C') • W := (mul_smul C C' W).symm
  show Proj.map (vcGradedHom (C * C') W) _ =
    eqToHom (by rw [mul_smul]) ≫ Proj.map (vcGradedHom C (C' • W)) _ ≫
      Proj.map (vcGradedHom C' W) _
  rw [← Proj.map_comp]
  refine projMap_transport_heq W e _ _ _ _ (gradedHom_heq W e.symm _ _ fun x => ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  show HEq (vcGradedHom (C * C') W (Ideal.Quotient.mk _ a))
    (vcGradedHom C (C' • W) (vcGradedHom C' W (Ideal.Quotient.mk _ a)))
  rw [vcGradedHom, quotientGradingMap_mk, vcGradedHom, vcGradedHom, quotientGradingMap_mk,
    quotientGradingMap_mk]
  exact (mk_heq e.symm _).trans (heq_of_eq (congrArg _ (aeval_vcMvSubst_mul C C' a)))

/-- **(T-W7.1b-a, Z2)** Every point of the model outside the `Z`-chart lies on the zero
section: take the residue-field point and apply the `Spec K`-dichotomy
(`specPoint_eq_zero_of_not_inZ`). -/
lemma mem_range_zero_of_not_mem_zChart {W : WeierstrassCurve R}
    {p : projModel W} (hp : p ∉ Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) :
    p ∈ Set.range (projModelZero W).base := by
  letI algInst : Algebra R ↑((projModel W).residueField p) :=
    ((Spec.preimage ((projModel W).fromSpecResidueField p ≫ projModelπ W)).hom).toAlgebra
  have hcompat : (projModel W).fromSpecResidueField p ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom (algebraMap R ↑((projModel W).residueField p))) := by
    rw [show CommRingCat.ofHom (algebraMap R ↑((projModel W).residueField p)) =
      Spec.preimage ((projModel W).fromSpecResidueField p ≫ projModelπ W) from rfl,
      Spec.map_preimage]
  obtain ⟨s₀⟩ : Nonempty (Spec (CommRingCat.of ((projModel W).residueField p))) :=
    inferInstance
  have hg : ¬ @InZChart R _ W ↑((projModel W).residueField p) _ algInst
      ⟨(projModel W).fromSpecResidueField p, hcompat⟩ := by
    rintro ⟨h, hfac⟩
    apply hp
    have h1 : ((projModel W).fromSpecResidueField p) s₀ =
        (Proj.awayι (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W 2) one_pos) (h s₀) := by
      have hc := congrArg (fun m => m s₀) hfac.symm
      rw [Scheme.Hom.comp_apply] at hc
      exact hc
    have h2 : (Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos) (h s₀) ∈
        (Proj.awayι (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W 2) one_pos).opensRange :=
      Scheme.Hom.mem_opensRange.mpr ⟨h s₀, rfl⟩
    rw [Proj.opensRange_awayι] at h2
    rw [Scheme.fromSpecResidueField_apply] at h1
    rw [h1]
    exact h2
  have hzero := @specPoint_eq_zero_of_not_inZ R _ W ↑((projModel W).residueField p) _ algInst
    ⟨(projModel W).fromSpecResidueField p, hcompat⟩ hg
  refine ⟨(Spec.map (CommRingCat.ofHom
    (algebraMap R ↑((projModel W).residueField p)))) s₀, ?_⟩
  have happ := congrArg (fun m => m s₀) hzero
  rw [show (projModelZero W).base ((Spec.map (CommRingCat.ofHom
      (algebraMap R ↑((projModel W).residueField p)))) s₀) =
    (Spec.map (CommRingCat.ofHom (algebraMap R ↑((projModel W).residueField p))) ≫
      projModelZero W) s₀ from rfl]
  rw [← happ]
  exact Scheme.fromSpecResidueField_apply p s₀

/-- **(T-W7.1b-a, Z3)** The zero section misses the `Z`-chart. -/
lemma not_mem_zChart_of_mem_range_zero {W : WeierstrassCurve R}
    {p : projModel W} (hp : p ∈ Set.range (projModelZero W).base) :
    p ∉ Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) := by
  obtain ⟨y, rfl⟩ := hp
  intro hmem
  have h1 : y ∈ projModelZero W ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) := hmem
  rw [projModelZero_not_preimage_zChart] at h1
  simp at h1

/-- **(T-W7.1b-a, Z4)** A pointed isomorphism of models preserves the affine (`Z`-chart)
part: the preimage of the `Z`-chart is the `Z`-chart. -/
lemma pointedIso_preimage_zChart {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))) =
    Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) := by
  have hezinv : projModelZero W' ≫ e.inv = projModelZero W := by
    rw [← hez, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext p
  constructor
  · intro hmem
    by_contra hp
    obtain ⟨y, hy⟩ := mem_range_zero_of_not_mem_zChart hp
    have h1 : e.hom.base p = (projModelZero W') y := by
      rw [← hy, show e.hom.base ((projModelZero W) y) =
        (projModelZero W ≫ e.hom) y from rfl, hez]
    exact not_mem_zChart_of_mem_range_zero ⟨y, h1.symm⟩ hmem
  · intro hmem
    by_contra hp
    have hp' : e.hom.base p ∉ Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)) := hp
    obtain ⟨y, hy⟩ := mem_range_zero_of_not_mem_zChart hp'
    have h1 : p = (projModelZero W) y := by
      have h2 : e.inv.base (e.hom.base p) = p := by
        have := congrArg (fun m => m p) e.hom_inv_id
        rw [Scheme.Hom.comp_apply] at this
        exact this
      rw [← h2, ← hy, show e.inv.base ((projModelZero W') y) =
        (projModelZero W' ≫ e.inv) y from rfl, hezinv]
    exact not_mem_zChart_of_mem_range_zero ⟨y, h1.symm⟩ hmem

/-- **(T-W7.1b-b1, the Γ-piece)** The section-ring equivalence of the affine charts induced
by a pointed isomorphism: `e.app` at the `Z`-chart, transported along
`pointedIso_preimage_zChart`. -/
noncomputable def pointedIsoΓ {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    Γ(projModel W', Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))) ≃+*
    Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) :=
  haveI : IsIso (e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)))) :=
    Scheme.Hom.isIso_app _ _ (by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
  ((asIso (e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))))).trans
    ((projModel W).presheaf.mapIso
      (eqToIso (pointedIso_preimage_zChart e hez).symm).op)).commRingCatIsoToRingEquiv

/-- `pointedIsoΓ` applied to a section: `e.hom.app` on the `Z`-chart followed by the presheaf
restriction along the preimage-equality. The element-level characterization used to relate
`pointedIsoΓ` to `appLE` without unfolding the equivalence. -/
lemma pointedIsoΓ_apply {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (w : ↑Γ(projModel W', Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)))) :
    pointedIsoΓ e hez w =
      (((projModel W).presheaf.map (eqToHom
        (pointedIso_preimage_zChart e hez).symm).op).hom)
        ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)))).hom w) := by
  refine (congrArg (fun ψ : _ →+* _ => ψ w)
    (Iso.commRingCatIsoToRingEquiv_toRingHom
      ((asIso (e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))))).trans
        ((projModel W).presheaf.mapIso (eqToIso
          (pointedIso_preimage_zChart e hez).symm).op)))).trans ?_
  rw [Iso.trans_hom]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rfl

/-- The transport of the restricted structure section along a pointed isomorphism. -/
lemma pointedIsoΓ_structure_section {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') (r : R) :
    (pointedIsoΓ e hez) (((projModel W').presheaf.map (homOfLE le_top).op).hom
      (((projModelπ W').appTop).hom
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom r))) =
    ((projModel W).presheaf.map (homOfLE le_top).op).hom
      (((projModelπ W).appTop).hom
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom r)) := by
  -- `π`-compatibility at the level of global sections
  have hπtop : ∀ u, (e.hom.appTop).hom (((projModelπ W').appTop).hom u) =
      ((projModelπ W).appTop).hom u := by
    intro u
    have := congrArg (fun φ => CommRingCat.Hom.hom φ u)
      (congrArg Scheme.Hom.appTop heπ)
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  -- naturality of `e.app` against restriction from `⊤`
  have hnat : ∀ w, (e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)))).hom
        (((projModel W').presheaf.map (homOfLE le_top).op).hom w) =
      ((projModel W).presheaf.map (homOfLE (le_top (a := e.hom ⁻¹ᵁ Proj.basicOpen
        (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))))).op).hom
        ((e.hom.appTop).hom w) := by
    intro w
    have hthis := congrArg (fun φ => CommRingCat.Hom.hom φ w)
      (e.hom.c.naturality (homOfLE (le_top (a := Proj.basicOpen
        (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))))).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hthis
    exact hthis
  -- unfold `pointedIsoΓ` and fuse the two restriction arrows
  show ((projModel W).presheaf.map (eqToHom
      (pointedIso_preimage_zChart e hez).symm).op).hom
    ((e.hom.app _).hom (((projModel W').presheaf.map (homOfLE le_top).op).hom
      (((projModelπ W').appTop).hom
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom r)))) = _
  rw [hnat, hπtop]
  have hfuse : (projModel W).presheaf.map (homOfLE le_top).op ≫
      (projModel W).presheaf.map (eqToHom
        (pointedIso_preimage_zChart e hez).symm).op =
      (projModel W).presheaf.map (homOfLE le_top).op := by
    rw [← Functor.map_comp]
    exact congrArg (projModel W).presheaf.map (Quiver.Hom.unop_inj
      (Subsingleton.elim _ _))
  have := congrArg (fun φ => CommRingCat.Hom.hom φ
    (((projModelπ W).appTop).hom
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom r))) hfuse
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this

/-- The `algebraMap`-compatibility of the induced coordinate-ring equivalence. -/
private lemma pointedIsoCoord_algebraMap {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') (r : R) :
    (chartZRingEquiv W) (((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).commRingCatIsoToRingEquiv).symm
      ((pointedIsoΓ e hez) ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W'))
          ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W' 2) one_pos).commRingCatIsoToRingEquiv
        ((chartZRingEquiv W').symm
          (algebraMap R W'.toAffine.CoordinateRing r))))) =
    algebraMap R W.toAffine.CoordinateRing r := by
  have h1 : (chartZRingEquiv W').symm (algebraMap R W'.toAffine.CoordinateRing r) =
      (HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal W'))
        (Submonoid.powers ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))))
        ((algebraMapGradeZero (projIdeal W')) r) := by
    rw [← chartZRingEquiv_fromZero W' r, RingEquiv.symm_apply_apply]
  have h2 : (Proj.basicOpenIsoAway (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W' 2) one_pos).commRingCatIsoToRingEquiv
      ((HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal W'))
        (Submonoid.powers ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))))
        ((algebraMapGradeZero (projIdeal W')) r)) =
      ((projModel W').presheaf.map (homOfLE le_top).op).hom
        (((projModelπ W').appTop).hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom r)) := by
    have hsq := structure_section_square_apply W' _
      (mk_X_mem_quotientGrading_one W' 2) one_pos r
    exact (congrArg (Proj.basicOpenIsoAway (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W' 2) one_pos).commRingCatIsoToRingEquiv
      hsq.symm).trans (awayToSection_inv_cancelZ W' _)
  have h4 : ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos).commRingCatIsoToRingEquiv).symm
      (((projModel W).presheaf.map (homOfLE le_top).op).hom
        (((projModelπ W).appTop).hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom r))) =
      (HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal W))
        (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
        ((algebraMapGradeZero (projIdeal W)) r) :=
    structure_section_square_apply W _ (mk_X_mem_quotientGrading_one W 2) one_pos r
  have step1 := congrArg (fun z => (chartZRingEquiv W)
    (((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).commRingCatIsoToRingEquiv).symm
      ((pointedIsoΓ e hez) ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W'))
          ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W' 2) one_pos).commRingCatIsoToRingEquiv z)))) h1
  have step2 := congrArg (fun z => (chartZRingEquiv W)
    (((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).commRingCatIsoToRingEquiv).symm
      ((pointedIsoΓ e hez) z))) h2
  have step3 := congrArg (fun z => (chartZRingEquiv W)
    (((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).commRingCatIsoToRingEquiv).symm z))
    (pointedIsoΓ_structure_section e heπ hez r)
  have step4 := congrArg (chartZRingEquiv W) h4
  exact (((step1.trans step2).trans step3).trans step4).trans
    (chartZRingEquiv_fromZero W r)

/-- **(T-W7.1b-b1, coordinator §2)** A pointed isomorphism of projective models restricts to
the affine parts (it preserves the complement of the zero section) and hence induces an
`R`-algebra isomorphism of the affine coordinate rings. DESIGN-DERIVED (audit A1 b1; no
verbatim source — KM is image-only). -/
noncomputable def pointedIsoCoordEquiv {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    W'.toAffine.CoordinateRing ≃ₐ[R] W.toAffine.CoordinateRing :=
  AlgEquiv.ofRingEquiv
    (f := (chartZRingEquiv W').symm.trans
      (((Proj.basicOpenIsoAway (quotientGrading (projIdeal W'))
          ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W' 2) one_pos).commRingCatIsoToRingEquiv).trans
        ((pointedIsoΓ e hez).trans
          (((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
            (mk_X_mem_quotientGrading_one W 2) one_pos).commRingCatIsoToRingEquiv).symm.trans
            (chartZRingEquiv W)))))
    (fun r => pointedIsoCoord_algebraMap e heπ hez r)

/-- The fixed `R`-algebra chart identification `CoordinateRing W ≃+* Γ(projModel W, Z-chart)`
(via `chartZRingEquiv` and the `X₂`-basic-open localization iso). Independent of any pointed
isomorphism: it is the fixed conjugator through which `pointedIsoCoordEquiv` factors, so the
induced-map interface (`pointedIsoCoordEquiv_apply`) never exposes the four-fold chart
composite — that giant term stays sealed inside this single named equivalence. -/
noncomputable def coordRingToZSection (W : WeierstrassCurve R) :
    W.toAffine.CoordinateRing ≃+*
      Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) :=
  (chartZRingEquiv W).symm.trans
    (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos).commRingCatIsoToRingEquiv

/-- **Whnf-free interface for `pointedIsoCoordEquiv`.** The induced coordinate isomorphism,
applied to a point, factors as the fixed chart identifications `coordRingToZSection` around
the `Γ`-level pointed map `pointedIsoΓ`. Proved by `rfl` while the chart isos are reducible;
this is the only unfolding the downstream faithfulness proofs need, and its RHS is small (the
four-fold chart composite stays sealed inside `coordRingToZSection`). -/
lemma pointedIsoCoordEquiv_apply {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (x : W'.toAffine.CoordinateRing) :
    pointedIsoCoordEquiv e heπ hez x =
      (coordRingToZSection W).symm (pointedIsoΓ e hez (coordRingToZSection W' x)) :=
  rfl

/-- The chart point of a prime containing `t` lies on the zero section. -/
lemma chartPointOf_mem_range_zero {W : WeierstrassCurve R}
    (P : Ideal (AdjoinRoot (infChartCubic W))) [P.IsPrime]
    (ht : infChartTElem W ∈ P) :
    chartPointOf W P ∈ Set.range (projModelZero W).base :=
  mem_range_zero_of_not_mem_zChart (chartPointOf_not_mem_chartZ W P ht)

/-- A pointed isomorphism carries the chart point of a section prime into the `Y`-chart of
the target model (the image lies on the target zero section, which the `Y`-chart contains). -/
lemma pointedIso_chartPointOf_mem_chartY {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (P : Ideal (AdjoinRoot (infChartCubic W))) [P.IsPrime]
    (ht : infChartTElem W ∈ P) :
    e.hom.base (chartPointOf W P) ∈ Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)) := by
  obtain ⟨y, hy⟩ := chartPointOf_mem_range_zero P ht
  have h1 : e.hom.base (chartPointOf W P) = (projModelZero W') y := by
    rw [← hy, show e.hom.base ((projModelZero W) y) =
      (projModelZero W ≫ e.hom) y from rfl, hez]
  rw [h1]
  have h2 : (y : Spec (CommRingCat.of R)) ∈ (projModelZero W' ⁻¹ᵁ
      (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) := by
    rw [projModelZero_preimage_yChart]
    trivial
  exact h2

/-- The basic open of the `t`-section lies in the `Z`-chart: its complement in the `Y`-chart
is the zero section, on which `t` vanishes. -/
lemma basicOpen_tSection_le_chartZ {W : WeierstrassCurve R} :
    (projModel W).basicOpen ((chartYSectionsRingEquiv W).symm (infChartTElem W)) ≤
      Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) := by
  intro q hq
  by_contra hq2
  obtain ⟨y, hy⟩ := mem_range_zero_of_not_mem_zChart hq2
  rw [← hy] at hq
  exact zero_not_mem_basicOpen_tSection W y hq

/-- **The chart overlap is the basic open of the `t`-section** — the key identification
turning overlap sections into a localization of `Y`-chart sections. -/
lemma chartY_inf_chartZ_eq_basicOpen_tSection (W : WeierstrassCurve R) :
    Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)) ⊓
      Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) =
    (projModel W).basicOpen ((chartYSectionsRingEquiv W).symm (infChartTElem W)) :=
  le_antisymm (chartY_inf_chartZ_le_basicOpen_tSection W)
    (le_inf ((projModel W).basicOpen_le _) basicOpen_tSection_le_chartZ)

/-- The `Y`-chart transport of a pointed isomorphism: pull back `Y'`-chart functions of the
target model along `e` and restrict to an open below the chart preimage. -/
noncomputable def pointedIsoChartTransport {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W') {V : (projModel W).Opens}
    (hV : V ≤ e.hom ⁻¹ᵁ Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) :
    AdjoinRoot (infChartCubic W') →+* ↑Γ(projModel W, V) :=
  ((((projModel W).presheaf.map (homOfLE hV).op).hom).comp
    ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom)).comp
    ((chartYSectionsRingEquiv W').symm :
      AdjoinRoot (infChartCubic W') →+* _)

/-- The basic open of a transported chart function: the chart preimage of the source basic
open, cut to `V`. -/
lemma pointedIsoChartTransport_basicOpen {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W') {V : (projModel W).Opens}
    (hV : V ≤ e.hom ⁻¹ᵁ Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))
    (b' : AdjoinRoot (infChartCubic W')) :
    (projModel W).basicOpen (pointedIsoChartTransport e hV b') =
      V ⊓ e.hom ⁻¹ᵁ ((projModel W').basicOpen
        ((chartYSectionsRingEquiv W').symm b')) := by
  have h1 : pointedIsoChartTransport e hV b' =
      ((projModel W).presheaf.map (homOfLE hV).op)
        ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
          ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))))
          ((chartYSectionsRingEquiv W').symm b')) := rfl
  rw [h1, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]

/-- **Unit augmentations transport to chart-point neighbourhoods**: if `aug'(b')` is a unit,
the chart point of any section prime lies in the basic open of the transported `b'`. -/
lemma chartPointOf_mem_basicOpen_transport {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    {V : (projModel W).Opens}
    (hV : V ≤ e.hom ⁻¹ᵁ Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))
    (P : Ideal (AdjoinRoot (infChartCubic W))) [P.IsPrime]
    (ht : infChartTElem W ∈ P) (hpV : chartPointOf W P ∈ V)
    (b' : AdjoinRoot (infChartCubic W')) (hb' : IsUnit (infChartAug W' b')) :
    chartPointOf W P ∈ (projModel W).basicOpen
      (pointedIsoChartTransport e hV b') := by
  rw [pointedIsoChartTransport_basicOpen]
  refine ⟨hpV, ?_⟩
  obtain ⟨y, hy⟩ := chartPointOf_mem_range_zero P ht
  show e.hom.base (chartPointOf W P) ∈ (projModel W').basicOpen
    ((chartYSectionsRingEquiv W').symm b')
  have h1 : e.hom.base (chartPointOf W P) = (projModelZero W').base y := by
    rw [← hy, show e.hom.base ((projModelZero W) y) =
      (projModelZero W ≫ e.hom) y from rfl, hez]
  rw [h1, zero_mem_basicOpen_chartYSection_iff]
  intro hmem
  exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hb')

/-- The coordinate transport factors through the `Z`-chart sections transport. -/
lemma pointedIsoCoordEquiv_sections {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (a' : W'.toAffine.CoordinateRing) :
    (chartZSectionsRingEquiv W).symm (pointedIsoCoordEquiv e heπ hez a') =
      pointedIsoΓ e hez ((chartZSectionsRingEquiv W').symm a') :=
  (RingEquiv.symm_apply_eq _).mpr rfl

/-- The transported overlap sits inside the transported `Y'`-chart. -/
private lemma overlapPreimage_le_chartYPreimage {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W') :
    e.hom ⁻¹ᵁ Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)) ≤
    e.hom ⁻¹ᵁ Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)) :=
  ((TopologicalSpace.Opens.map e.hom.base).map (homOfLE (Proj.basicOpen_mono _
    ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))
    ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
      (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)) ⟨_, rfl⟩))).le

/-- The transported overlap sits inside the `Z`-chart of the target model. -/
private lemma overlapPreimage_le_chartZ {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    e.hom ⁻¹ᵁ Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)) ≤
    Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) :=
  le_of_le_of_eq ((TopologicalSpace.Opens.map e.hom.base).map (homOfLE (Proj.basicOpen_mono _
    ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
    ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
      (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
    ⟨_, mul_comm ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))⟩))).le
    (pointedIso_preimage_zChart e hez)

/-- **The overlap equation transports along a pointed isomorphism**: a `t'`-cleared relation
between a `Y'`-chart function `b'` and a `Z'`-chart function `a'` becomes, after `e.app` and
restriction to the transported overlap, the same relation between the transported `b'` and
`Φ a'`. All geometry of the comparison is concentrated here. -/
lemma pointedIso_overlap_sections_equation {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (a' : W'.toAffine.CoordinateRing) (b' d' : AdjoinRoot (infChartCubic W')) (j : ℕ)
    (h : algebraMap (AdjoinRoot (infChartCubic W'))
        (Localization.Away (infChartTElem W')) b' =
      overlapMap W' a' *
        algebraMap (AdjoinRoot (infChartCubic W'))
          (Localization.Away (infChartTElem W')) d' ^ j) :
    ((projModel W).presheaf.map (homOfLE (overlapPreimage_le_chartYPreimage e)).op).hom
      ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom
        ((chartYSectionsRingEquiv W').symm b')) =
    ((projModel W).presheaf.map (homOfLE (overlapPreimage_le_chartZ e hez)).op).hom
      ((chartZSectionsRingEquiv W).symm (pointedIsoCoordEquiv e heπ hez a')) *
    (((projModel W).presheaf.map (homOfLE (overlapPreimage_le_chartYPreimage e)).op).hom
      ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom
        ((chartYSectionsRingEquiv W').symm d'))) ^ j := by
  have h1 := overlap_sections_equation_of_loc W' a' b' d' j h
  have h2 := congrArg ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
    ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
      (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)))).hom) h1
  rw [map_mul, map_pow] at h2
  have hnatY : ∀ w' : Γ(projModel W', Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))),
      (e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
          (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)))).hom
        (((projModel W').presheaf.map (homOfLE
          (Proj.basicOpen_mono _ ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))
            ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
              (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)) ⟨_, rfl⟩)).op).hom w') =
      ((projModel W).presheaf.map (homOfLE (overlapPreimage_le_chartYPreimage e)).op).hom
        ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
          ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom w') := by
    intro w'
    have hnat := congrArg (fun φ => CommRingCat.Hom.hom φ w')
      (Scheme.Hom.naturality e.hom ((homOfLE
        (Proj.basicOpen_mono _ ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))
          ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
            (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)) ⟨_, rfl⟩)).op))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
    rw [hnat]
    exact congrArg (fun ψ => (CommRingCat.Hom.hom ((projModel W).presheaf.map ψ))
      ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom w'))
      (Subsingleton.elim _ _)
  have hΦ : ((projModel W).presheaf.map
      (homOfLE (overlapPreimage_le_chartZ e hez)).op).hom
      ((chartZSectionsRingEquiv W).symm (pointedIsoCoordEquiv e heπ hez a')) =
      (e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
          (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)))).hom
        (((projModel W').presheaf.map (homOfLE
          (Proj.basicOpen_mono _ ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
            ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
              (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
            ⟨_, mul_comm ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))
              ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))⟩)).op).hom
          ((chartZSectionsRingEquiv W').symm a')) := by
    have hΓ0 := congrArg (fun ψ : _ →+* _ => ψ ((chartZSectionsRingEquiv W').symm a'))
      (Iso.commRingCatIsoToRingEquiv_toRingHom
        ((asIso (e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
          ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))))).trans
          ((projModel W).presheaf.mapIso
            (eqToIso (pointedIso_preimage_zChart e hez).symm).op)))
    have hΓ : pointedIsoΓ e hez ((chartZSectionsRingEquiv W').symm a') =
        ((projModel W).presheaf.map
          (eqToIso (pointedIso_preimage_zChart e hez).symm).op.hom).hom
          ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
            ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)))).hom
            ((chartZSectionsRingEquiv W').symm a')) := by
      refine hΓ0.trans ?_
      rw [Iso.trans_hom]
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      rfl
    have c1 := congrArg (fun z => ((projModel W).presheaf.map
      (homOfLE (overlapPreimage_le_chartZ e hez)).op).hom z)
      (pointedIsoCoordEquiv_sections e heπ hez a')
    have c2 := congrArg (fun z => ((projModel W).presheaf.map
      (homOfLE (overlapPreimage_le_chartZ e hez)).op).hom z) hΓ
    have hfuse := congrArg (fun φ => CommRingCat.Hom.hom φ
      ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)))).hom
        ((chartZSectionsRingEquiv W').symm a')))
      ((projModel W).presheaf.map_comp
        ((eqToIso (pointedIso_preimage_zChart e hez).symm).op.hom)
        ((homOfLE (overlapPreimage_le_chartZ e hez)).op))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hfuse
    have c4 := congrArg (fun ψ => (CommRingCat.Hom.hom ((projModel W).presheaf.map ψ))
      ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)))).hom
        ((chartZSectionsRingEquiv W').symm a')))
      (Subsingleton.elim
        ((eqToIso (pointedIso_preimage_zChart e hez).symm).op.hom ≫
          (homOfLE (overlapPreimage_le_chartZ e hez)).op)
        (((TopologicalSpace.Opens.map e.hom.base).map (homOfLE
          (Proj.basicOpen_mono _ ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
            ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
              (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
            ⟨_, mul_comm ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))
              ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))⟩))).op))
    have hnatZ := congrArg (fun φ => CommRingCat.Hom.hom φ
      ((chartZSectionsRingEquiv W').symm a'))
      (Scheme.Hom.naturality e.hom ((homOfLE
        (Proj.basicOpen_mono _ ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
          ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
            (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
          ⟨_, mul_comm ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))
            ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))⟩)).op))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnatZ
    exact c1.trans (c2.trans (hfuse.symm.trans (c4.trans hnatZ.symm)))
  exact ((hnatY ((chartYSectionsRingEquiv W').symm b')).symm).trans
    (h2.trans (congrArg₂ (· * ·) hΦ.symm
      (congrArg (· ^ j) (hnatY ((chartYSectionsRingEquiv W').symm d')))))

/-- The zero section of `W` lands in the transported `Y'`-chart. -/
private lemma zero_le_preimage_pointedPreimage {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    (⊤ : (Spec (CommRingCat.of R)).Opens) ≤
      (projModelZero W) ⁻¹ᵁ (e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) := by
  intro x _
  have h1 : e.hom.base ((projModelZero W).base x) = (projModelZero W').base x := by
    rw [show e.hom.base ((projModelZero W) x) =
      (projModelZero W ≫ e.hom) x from rfl, hez]
  have h2 : x ∈ (projModelZero W') ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) := by
    rw [projModelZero_preimage_yChart W']
    trivial
  show e.hom.base ((projModelZero W).base x) ∈ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))
  rw [h1]
  exact h2

/-- **(ForMathlib-grade)** A factorisation `z ≫ f = z'` induces the factorisation of top
`appLE`s: `f^* ≫ z^* = z'^*`. Stated for opaque morphisms so instantiation at large
composites stays kernel-cheap. -/
lemma appLE_appLE_of_comp_eq {X Y Z : Scheme.{u}} (z : Z ⟶ X) (f : X ⟶ Y)
    (z' : Z ⟶ Y) (hfz : z ≫ f = z') (U : Y.Opens)
    (h₂ : ⊤ ≤ z ⁻¹ᵁ (f ⁻¹ᵁ U)) (h : ⊤ ≤ z' ⁻¹ᵁ U) :
    f.appLE U (f ⁻¹ᵁ U) le_rfl ≫ z.appLE (f ⁻¹ᵁ U) ⊤ h₂ = z'.appLE U ⊤ h := by
  subst hfz
  exact Scheme.Hom.appLE_comp_appLE z f U (f ⁻¹ᵁ U) ⊤ le_rfl h₂

/-- **Pointed transports respect the zero sections at the `Y`-charts** (morphism level,
`appLE` form): pulling back along `e` and then along the zero section of `W` is pulling back
along the zero section of `W'`. -/
lemma pointedIso_zero_appLE_chartY {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    e.hom.appLE (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) (e.hom ⁻¹ᵁ (Proj.basicOpen
          (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) le_rfl ≫
      (projModelZero W).appLE (e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) ⊤
        (zero_le_preimage_pointedPreimage e hez) =
    (projModelZero W').appLE (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) ⊤
        (le_of_eq (projModelZero_preimage_yChart W').symm) :=
  appLE_appLE_of_comp_eq (projModelZero W) e.hom (projModelZero W') hez (Proj.basicOpen
    (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))
    (zero_le_preimage_pointedPreimage e hez)
    (le_of_eq (projModelZero_preimage_yChart W').symm)

/-- The `le_rfl`-`appLE` of a morphism agrees with `app`, elementwise. -/
private lemma appLE_le_rfl_apply {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (w' : Γ(projModel W', Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) :
    ((e.hom.appLE (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) (e.hom ⁻¹ᵁ (Proj.basicOpen
          (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) le_rfl).hom) w' =
    ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom) w' := by
  have h2 : (homOfLE (le_rfl : e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) ≤ e.hom ⁻¹ᵁ (Proj.basicOpen
          (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))))).op =
      𝟙 (Opposite.op (e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))))) := Subsingleton.elim _ _
  have h3 := congrArg (fun ψ => (CommRingCat.Hom.hom
    ((projModel W).presheaf.map ψ)) (((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom) w')) h2
  refine h3.trans ?_
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (((e.hom.app (Proj.basicOpen (quotientGrading
    (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom) w'))
    ((projModel W).presheaf.map_id (Opposite.op (e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading
      (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))))))

/-- **The zero-section value of a transported chart function is the source augmentation**:
`zero^*(e^*(section of b')) = aug'(b')`. -/
lemma pointedIso_zero_val_chartYSection {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (b' : AdjoinRoot (infChartCubic W')) :
    (((projModelZero W).appLE (e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) ⊤
        (zero_le_preimage_pointedPreimage e hez)).hom)
      ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom
          ((chartYSectionsRingEquiv W').symm b')) =
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom (infChartAug W' b') := by
  have h1 := congrArg (fun φ => CommRingCat.Hom.hom φ
    ((chartYSectionsRingEquiv W').symm b')) (pointedIso_zero_appLE_chartY e hez)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
  have h2 := congrArg ((((projModelZero W).appLE (e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading
    (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) ⊤
    (zero_le_preimage_pointedPreimage e hez))).hom)
    (appLE_le_rfl_apply e ((chartYSectionsRingEquiv W').symm b'))
  exact (h2.symm.trans h1).trans (projModelZero_appLE_chartYSection W' b')

private lemma map_appLE_val {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens}
    {V : X.Opens} (i : U' ≤ U) (e : V ≤ f ⁻¹ᵁ U') (e' : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    ((f.appLE U' V e).hom) ((Y.presheaf.map (homOfLE i).op).hom x) =
      ((f.appLE U V e').hom) x := by
  have h := congrArg (fun φ => CommRingCat.Hom.hom φ x)
    (Scheme.Hom.map_appLE f e (homOfLE i).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h

private lemma appLE_map_val {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (i : V' ≤ V) (e' : V' ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    ((X.presheaf.map (homOfLE i).op).hom) ((f.appLE U V e).hom x) =
      ((f.appLE U V' e').hom) x := by
  have h := congrArg (fun φ => CommRingCat.Hom.hom φ x)
    (Scheme.Hom.appLE_map f e (homOfLE i).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h

/-- The localized zero-pullback of a `Y`-chart function on a basic open is the restricted
augmentation. -/
lemma zero_appLE_basicOpen_chartYSection (W : WeierstrassCurve R)
    (r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))) (b : AdjoinRoot
          (infChartCubic W)) :
    (((projModelZero W).appLE ((projModel W).basicOpen r)
        ((projModelZero W) ⁻¹ᵁ (projModel W).basicOpen r) le_rfl).hom)
      (((projModel W).presheaf.map
        (homOfLE ((projModel W).basicOpen_le r)).op).hom
        ((chartYSectionsRingEquiv W).symm b)) =
    (((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom)
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom (infChartAug W b)) := by
  refine (map_appLE_val (projModelZero W) ((projModel W).basicOpen_le r) le_rfl
    (le_top.trans (le_of_eq (projModelZero_preimage_yChart W).symm))
    ((chartYSectionsRingEquiv W).symm b)).trans ?_
  refine ((appLE_map_val (projModelZero W)
    (le_of_eq (projModelZero_preimage_yChart W).symm) le_top
    (le_top.trans (le_of_eq (projModelZero_preimage_yChart W).symm))
    ((chartYSectionsRingEquiv W).symm b)).symm).trans ?_
  exact congrArg (((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom)
    (projModelZero_appLE_chartYSection W b)

/-- The localized zero-pullback of a transported chart function on a basic open is the
restricted source augmentation. -/
lemma pointedIso_zero_appLE_basicOpen {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    {V : (projModel W).Opens} (hV : V ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))))
    (b' : AdjoinRoot (infChartCubic W')) :
    (((projModelZero W).appLE V ((projModelZero W) ⁻¹ᵁ V) le_rfl).hom)
      (pointedIsoChartTransport e hV b') =
    (((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom)
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom (infChartAug W' b')) := by
  refine (map_appLE_val (projModelZero W) hV le_rfl
    (le_top.trans (zero_le_preimage_pointedPreimage e hez))
    ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom
          ((chartYSectionsRingEquiv W').symm b'))).trans ?_
  refine ((appLE_map_val (projModelZero W)
    (zero_le_preimage_pointedPreimage e hez) le_top
    (le_top.trans (zero_le_preimage_pointedPreimage e hez))
    ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom
          ((chartYSectionsRingEquiv W').symm b'))).symm).trans ?_
  exact congrArg (((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom)
    (pointedIso_zero_val_chartYSection e hez b')

/-- Vanishing of a restricted global section of `Spec R` on the zero-preimage of a chart
basic open kills the corresponding `R`-element after a power of the augmented equation. -/
private lemma aug_pow_kill_of_res_eq_zero (W : WeierstrassCurve R)
    (r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))) (A : R)
    (h : (((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom)
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom A) =
      (0 : ↑Γ(Spec (CommRingCat.of R), (projModelZero W) ⁻¹ᵁ (projModel W).basicOpen r))) :
    ∃ m : ℕ, (infChartAug W (chartYSectionsRingEquiv W r)) ^ m * A = 0 := by
  set g₀ : ↑Γ(Spec (CommRingCat.of R), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom
      (infChartAug W (chartYSectionsRingEquiv W r)) with hg₀
  have hval : (((projModelZero W).appLE (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))) ⊤
      (le_of_eq (projModelZero_preimage_yChart W).symm)).hom) r = g₀ := by
    have := projModelZero_appLE_chartYSection W (chartYSectionsRingEquiv W r)
    rw [RingEquiv.symm_apply_apply] at this
    exact this
  have hopen : (projModelZero W) ⁻¹ᵁ (projModel W).basicOpen r =
      (Spec (CommRingCat.of R)).basicOpen g₀ := by
    rw [Scheme.preimage_basicOpen]
    have hbo : (Spec (CommRingCat.of R)).basicOpen
        ((((projModelZero W).appLE (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))) ⊤
          (le_of_eq (projModelZero_preimage_yChart W).symm)).hom) r) =
        (Spec (CommRingCat.of R)).basicOpen
          ((projModelZero W).app (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))) r) := by
      show (Spec (CommRingCat.of R)).basicOpen
        (((Spec (CommRingCat.of R)).presheaf.map (homOfLE
          (le_of_eq (projModelZero_preimage_yChart W).symm)).op).hom
          ((projModelZero W).app (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))) r)) = _
      rw [Scheme.basicOpen_res]
      exact top_inf_eq _
    rw [← hbo, hval]
  haveI := (isAffineOpen_top (Spec (CommRingCat.of R))).isLocalization_basicOpen g₀
  have h' : (algebraMap (↑Γ(Spec (CommRingCat.of R), ⊤))
      (↑Γ(Spec (CommRingCat.of R), (Spec (CommRingCat.of R)).basicOpen g₀)))
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom A) = 0 := by
    show (((Spec (CommRingCat.of R)).presheaf.map (homOfLE
      ((Spec (CommRingCat.of R)).basicOpen_le g₀)).op).hom)
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom A) = 0
    have htrans := congrArg (fun ψ =>
      (CommRingCat.Hom.hom ((Spec (CommRingCat.of R)).presheaf.map ψ))
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom A))
      (Subsingleton.elim ((homOfLE ((Spec (CommRingCat.of R)).basicOpen_le g₀)).op)
        ((homOfLE le_top).op ≫ (eqToHom hopen.symm).op))
    refine htrans.trans ?_
    have hsplit := congrArg (fun φ => CommRingCat.Hom.hom φ
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom A))
      ((Spec (CommRingCat.of R)).presheaf.map_comp (homOfLE le_top).op
        (eqToHom hopen.symm).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hsplit
    refine hsplit.trans ?_
    rw [h, map_zero]
  obtain ⟨⟨u, hu⟩, hkill⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers g₀)
    (↑Γ(Spec (CommRingCat.of R), (Spec (CommRingCat.of R)).basicOpen g₀))
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom A)).mp h'
  obtain ⟨m, hm⟩ := hu
  refine ⟨m, ?_⟩
  have hR := congrArg (((Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom) hkill
  rw [map_zero, map_mul] at hR
  have hcancelA : ((Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom A) = A := by
    have := congrArg (fun φ => CommRingCat.Hom.hom φ A)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] at this
    exact this
  have hcancelG : ((Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom u =
      (infChartAug W (chartYSectionsRingEquiv W r)) ^ m := by
    rw [← hm, hg₀]
    rw [map_pow]
    have := congrArg (fun φ => CommRingCat.Hom.hom φ
      (infChartAug W (chartYSectionsRingEquiv W r)))
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] at this
    rw [this]
  rw [hcancelA, hcancelG] at hR
  exact hR

private lemma span_pair_map_mem {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {x a b : A} (h : x ∈ Ideal.span {a, b}) :
    φ x ∈ Ideal.span {φ a, φ b} := by
  obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp h
  refine Ideal.mem_span_pair.mpr ⟨φ c, φ d, ?_⟩
  rw [← map_mul, ← map_mul, ← map_add, hcd]

private lemma mem_of_eq_of_mem {S : Type u} [CommRing S] {I : Ideal S} {a b : S}
    (h : a = b) (hb : b ∈ I) : a ∈ I := h ▸ hb

private lemma transport_mem_span_aux (W : WeierstrassCurve R)
    (r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
    (x : ↑Γ(projModel W, (projModel W).basicOpen r))
    (b₀ : ↑Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))) (k : ℕ)
    (hb₀ : x * (algebraMap (↑Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
      (↑Γ(projModel W, (projModel W).basicOpen r))) (r ^ k) =
      (algebraMap (↑Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
        (↑Γ(projModel W, (projModel W).basicOpen r))) b₀)
    (hAkill : ∃ m : ℕ, (infChartAug W (chartYSectionsRingEquiv W r)) ^ m *
      infChartAug W (chartYSectionsRingEquiv W b₀) = 0) :
    x ∈ Ideal.span
      {((projModel W).presheaf.map
          (homOfLE ((projModel W).basicOpen_le r)).op).hom
          ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W))),
        ((projModel W).presheaf.map
          (homOfLE ((projModel W).basicOpen_le r)).op).hom
          ((chartYSectionsRingEquiv W).symm (infChartTElem W))} := by
  haveI := (Proj.isAffineOpen_basicOpen (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
    (mk_X_mem_quotientGrading_one W 1) one_pos).isLocalization_basicOpen r
  obtain ⟨m, hm⟩ := hAkill
  have hker : (chartYSectionsRingEquiv W r) ^ m * chartYSectionsRingEquiv W b₀ ∈
      Ideal.span {AdjoinRoot.root (infChartCubic W), infChartTElem W} := by
    rw [← ker_infChartAug W]
    show infChartAug W _ = 0
    rw [map_mul, map_pow]
    exact hm
  obtain ⟨cs, ct, hct⟩ := Ideal.mem_span_pair.mp hker
  have hfwd : chartYSectionsRingEquiv W (r ^ m * b₀) =
      (chartYSectionsRingEquiv W r) ^ m * chartYSectionsRingEquiv W b₀ :=
    (map_mul (chartYSectionsRingEquiv W) (r ^ m) b₀).trans
      (congrArg₂ (· * ·) (map_pow (chartYSectionsRingEquiv W) r m) rfl)
  have hBeq : r ^ m * b₀ = (chartYSectionsRingEquiv W).symm
      (cs * AdjoinRoot.root (infChartCubic W) + ct * infChartTElem W) :=
    (RingEquiv.symm_apply_apply (chartYSectionsRingEquiv W) (r ^ m * b₀)).symm.trans
      (congrArg (chartYSectionsRingEquiv W).symm (hfwd.trans hct.symm))
  have hsymm : (chartYSectionsRingEquiv W).symm
      (cs * AdjoinRoot.root (infChartCubic W) + ct * infChartTElem W) =
      (chartYSectionsRingEquiv W).symm cs *
        (chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W)) +
      (chartYSectionsRingEquiv W).symm ct *
        (chartYSectionsRingEquiv W).symm (infChartTElem W) :=
    (map_add (chartYSectionsRingEquiv W).symm _ _).trans
      (congrArg₂ (· + ·) (map_mul (chartYSectionsRingEquiv W).symm _ _)
        (map_mul (chartYSectionsRingEquiv W).symm _ _))
  have hspan : algebraMap (↑Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
      (↑Γ(projModel W, (projModel W).basicOpen r)) (r ^ m * b₀) ∈ Ideal.span
      {((projModel W).presheaf.map
          (homOfLE ((projModel W).basicOpen_le r)).op).hom
          ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W))),
        ((projModel W).presheaf.map
          (homOfLE ((projModel W).basicOpen_le r)).op).hom
          ((chartYSectionsRingEquiv W).symm (infChartTElem W))} := by
    refine mem_of_eq_of_mem (congrArg (algebraMap _ _) (hBeq.trans hsymm)) ?_
    refine mem_of_eq_of_mem (map_add (algebraMap (↑Γ(projModel W, Proj.basicOpen (quotientGrading
      (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
      (↑Γ(projModel W, (projModel W).basicOpen r)) : _ →+* _) _ _) ?_
    refine Ideal.add_mem _ ?_ ?_
    · refine mem_of_eq_of_mem (map_mul (algebraMap (↑Γ(projModel W, Proj.basicOpen (quotientGrading
      (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
        (↑Γ(projModel W, (projModel W).basicOpen r)) : _ →+* _) _ _) ?_
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
    · refine mem_of_eq_of_mem (map_mul (algebraMap (↑Γ(projModel W, Proj.basicOpen (quotientGrading
      (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
        (↑Γ(projModel W, (projModel W).basicOpen r)) : _ →+* _) _ _) ?_
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span
        (Set.mem_insert_of_mem _ rfl))
  have heq : x * algebraMap (↑Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
      (↑Γ(projModel W, (projModel W).basicOpen r)) (r ^ (k + m)) =
      algebraMap (↑Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
        (↑Γ(projModel W, (projModel W).basicOpen r)) (r ^ m * b₀) := by
    refine (congrArg (x * ·) (by rw [pow_add, map_mul])).trans ?_
    refine (mul_assoc _ _ _).symm.trans ?_
    refine (congrArg (· * algebraMap _ _ (r ^ m)) hb₀).trans ?_
    refine (map_mul _ _ _).symm.trans ?_
    exact congrArg (algebraMap _ _) (mul_comm b₀ (r ^ m))
  have hpow : IsUnit (algebraMap (↑Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
      (↑Γ(projModel W, (projModel W).basicOpen r)) (r ^ (k + m))) := by
    rw [map_pow]
    exact (IsLocalization.map_units (M := Submonoid.powers r) _
      ⟨r, 1, pow_one r⟩).pow _
  obtain ⟨v, hv⟩ := hpow
  have h1 : x * ↑v = algebraMap (↑Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
      (↑Γ(projModel W, (projModel W).basicOpen r)) (r ^ m * b₀) := by
    rw [hv]
    exact heq
  have h2 := congrArg (· * (↑v⁻¹ : ↑Γ(projModel W, (projModel W).basicOpen r))) h1
  have h3 : x = algebraMap (↑Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
      (↑Γ(projModel W, (projModel W).basicOpen r)) (r ^ m * b₀) *
      (↑v⁻¹ : ↑Γ(projModel W, (projModel W).basicOpen r)) :=
    (v.mul_inv_cancel_right x).symm.trans h2
  exact mem_of_eq_of_mem h3 (Ideal.mul_mem_right _ _ hspan)

/-- **Transported augmentation-kernel elements lie in the localized section ideal**: if
`aug'(b') = 0`, then on any basic open of the `Y`-chart inside the transported `Y'`-chart the
transport of `b'` lies in the ideal generated by (the restrictions of) `s` and `t`. This is
the scheme-theoretic vanishing of transports along the zero section. -/
lemma pointedIsoChartTransport_mem_span_of_aug_eq_zero {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
    (hr : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))))
    {b' : AdjoinRoot (infChartCubic W')} (hb' : infChartAug W' b' = 0) :
    pointedIsoChartTransport e hr b' ∈ Ideal.span
      {((projModel W).presheaf.map
          (homOfLE ((projModel W).basicOpen_le r)).op).hom
          ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W))),
        ((projModel W).presheaf.map
          (homOfLE ((projModel W).basicOpen_le r)).op).hom
          ((chartYSectionsRingEquiv W).symm (infChartTElem W))} := by
  haveI := (Proj.isAffineOpen_basicOpen (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
    (mk_X_mem_quotientGrading_one W 1) one_pos).isLocalization_basicOpen r
  obtain ⟨⟨b₀, u⟩, hb₀⟩ := IsLocalization.surj (Submonoid.powers r)
    (pointedIsoChartTransport e hr b')
  obtain ⟨k, hk⟩ := u.2
  rw [← hk] at hb₀
  have hzero : (((projModelZero W).appLE ((projModel W).basicOpen r)
      ((projModelZero W) ⁻¹ᵁ (projModel W).basicOpen r) le_rfl).hom)
      (pointedIsoChartTransport e hr b') = 0 := by
    refine (pointedIso_zero_appLE_basicOpen e hez hr b').trans ?_
    rw [hb', map_zero, map_zero]
  have hz0 := congrArg ((((projModelZero W).appLE ((projModel W).basicOpen r)
    ((projModelZero W) ⁻¹ᵁ (projModel W).basicOpen r) le_rfl)).hom) hb₀
  have hz : (((projModelZero W).appLE ((projModel W).basicOpen r)
      ((projModelZero W) ⁻¹ᵁ (projModel W).basicOpen r) le_rfl).hom)
      ((algebraMap (↑Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
        (↑Γ(projModel W, (projModel W).basicOpen r))) b₀) = 0 := by
    refine (hz0.symm.trans ?_)
    refine (map_mul _ _ _).trans ?_
    rw [hzero, zero_mul]
  have halg : (((projModelZero W).appLE ((projModel W).basicOpen r)
      ((projModelZero W) ⁻¹ᵁ (projModel W).basicOpen r) le_rfl).hom)
      ((algebraMap (↑Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
        (↑Γ(projModel W, (projModel W).basicOpen r))) b₀) =
      (((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom)
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom
          (infChartAug W (chartYSectionsRingEquiv W b₀))) := by
    have hc := zero_appLE_basicOpen_chartYSection W r (chartYSectionsRingEquiv W b₀)
    rw [RingEquiv.symm_apply_apply] at hc
    exact hc
  have hzres := halg.symm.trans hz
  exact transport_mem_span_aux W r _ b₀ k hb₀
    (aug_pow_kill_of_res_eq_zero W r _ hzres)

/-- The zero-compatibility of the inverse of a pointed isomorphism. -/
lemma pointedIso_hez_symm {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    projModelZero W' ≫ e.symm.hom = projModelZero W := by
  show projModelZero W' ≫ e.inv = projModelZero W
  rw [← hez, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- The base-compatibility of the inverse of a pointed isomorphism. -/
lemma pointedIso_heπ_symm {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W) :
    e.symm.hom ≫ projModelπ W = projModelπ W' := by
  show e.inv ≫ projModelπ W = projModelπ W'
  rw [← heπ, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- **(ForMathlib-grade)** Sections round-trip along a split pair, after restriction: if
`f ≫ g = 𝟙` then `res ∘ f^* ∘ g^* = res`. Opaque morphisms keep instantiation kernel-cheap. -/
lemma app_app_res_of_comp_eq_id {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : f ≫ g = 𝟙 X) (U : X.Opens) {V : X.Opens} (hV : V ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U))
    (hVU : V ≤ U) (w : Γ(X, U)) :
    ((X.presheaf.map (homOfLE hV).op).hom)
      (((f.app (g ⁻¹ᵁ U)).hom) (((g.app U).hom) w)) =
    ((X.presheaf.map (homOfLE hVU).op).hom) w := by
  have hcomp := congrArg (fun z => ((X.presheaf.map (homOfLE hV).op).hom) z)
    (congrArg (fun φ => CommRingCat.Hom.hom φ w) (Scheme.Hom.comp_app f g U))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hcomp
  refine hcomp.symm.trans ?_
  have hLE : (((f ≫ g).appLE U V (hV.trans (le_of_eq rfl))).hom) w =
      ((X.presheaf.map (homOfLE hV).op).hom) ((((f ≫ g).app U).hom) w) := rfl
  refine hLE.symm.trans ?_
  have hz : ∀ (h : X ⟶ X) (hh : f ≫ g = h) (h' : V ≤ h ⁻¹ᵁ U),
      (((f ≫ g).appLE U V (by rw [hh]; exact h')).hom) w =
      ((h.appLE U V h').hom) w := by
    intro h hh h'
    subst hh
    rfl
  refine (hz (𝟙 X) hfg hVU).trans ?_
  rfl

/-- Chart transports are compatible with restriction. -/
lemma pointedIsoChartTransport_res {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W') {V V' : (projModel W).Opens}
    (hV' : V' ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) (hVV' : V ≤ V')
    (b' : AdjoinRoot (infChartCubic W')) :
    (((projModel W).presheaf.map (homOfLE hVV').op).hom)
      (pointedIsoChartTransport e hV' b') =
    pointedIsoChartTransport e (hVV'.trans hV') b' := by
  have hfuse := congrArg (fun φ => CommRingCat.Hom.hom φ
    ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom
          ((chartYSectionsRingEquiv W').symm b')))
    ((projModel W).presheaf.map_comp (homOfLE hV').op (homOfLE hVV').op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hfuse
  refine hfuse.symm.trans ?_
  exact congrArg (fun ψ => (CommRingCat.Hom.hom ((projModel W).presheaf.map ψ))
    ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom
          ((chartYSectionsRingEquiv W').symm b')))
    (Subsingleton.elim _ _)

/-- **Refinement with an invertible transported section unit**: every section prime admits a
basic open inside the transported `Y'`-chart, avoiding the prime, on which the transported
`U'` is a unit. -/
lemma exists_basicOpen_transport_unit {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (P : Ideal (AdjoinRoot (infChartCubic W))) [P.IsPrime]
    (ht : infChartTElem W ∈ P) :
    ∃ (r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
      (hr : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))),
      chartYSectionsRingEquiv W r ∉ P ∧
      IsUnit (pointedIsoChartTransport e hr (sectionUnitElem W')) := by
  have hp1 : chartPointOf W P ∈ Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)) :=
    chartPointOf_mem_chartY W P
  have hpe : chartPointOf W P ∈ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) :=
    pointedIso_chartPointOf_mem_chartY e hez P ht
  obtain ⟨r₁, hr₁le, hpr₁⟩ := (Proj.isAffineOpen_basicOpen
    (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
    (mk_X_mem_quotientGrading_one W 1) one_pos).exists_basicOpen_le
    ⟨chartPointOf W P, hpe⟩ hp1
  have hpU : chartPointOf W P ∈ (projModel W).basicOpen
      (pointedIsoChartTransport e hr₁le (sectionUnitElem W')) := by
    refine chartPointOf_mem_basicOpen_transport e hez hr₁le P ht hpr₁ _ ?_
    rw [infChartAug_sectionUnitElem W']
    exact isUnit_one
  obtain ⟨r₂, hr₂le, hpr₂⟩ := (Proj.isAffineOpen_basicOpen
    (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
    (mk_X_mem_quotientGrading_one W 1) one_pos).exists_basicOpen_le
    ⟨chartPointOf W P, hpU⟩ hp1
  have hr₂le' : (projModel W).basicOpen r₂ ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading
    (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) :=
    le_trans (hr₂le.trans ((projModel W).basicOpen_le _)) hr₁le
  refine ⟨r₂, hr₂le', (chartPointOf_mem_basicOpen_iff W P r₂).mp hpr₂, ?_⟩
  have hres : pointedIsoChartTransport e hr₂le' (sectionUnitElem W') =
      (((projModel W).presheaf.map (homOfLE hr₂le).op).hom)
        ((((projModel W).presheaf.map (homOfLE ((projModel W).basicOpen_le
          (pointedIsoChartTransport e hr₁le (sectionUnitElem W')))).op).hom)
          (pointedIsoChartTransport e hr₁le (sectionUnitElem W'))) := by
    have h1 := pointedIsoChartTransport_res e hr₁le
      (((projModel W).basicOpen_le (pointedIsoChartTransport e hr₁le
        (sectionUnitElem W')))) (sectionUnitElem W')
    have h2 := pointedIsoChartTransport_res e
      ((((projModel W).basicOpen_le (pointedIsoChartTransport e hr₁le
        (sectionUnitElem W')))).trans hr₁le) hr₂le (sectionUnitElem W')
    refine ?_
    rw [h1, h2]
  rw [hres]
  refine IsUnit.map _ ?_
  exact AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen
    (X := (projModel W).toLocallyRingedSpace.toRingedSpace)
    (pointedIsoChartTransport e hr₁le (sectionUnitElem W'))

/-- Pushing a mirror transport back through `e` restricts to the plain section. -/
private lemma transport_symm_roundtrip {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    {r' : Γ(projModel W', Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))}
    (hr'le : (projModel W').basicOpen r' ≤ e.symm.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading
      (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
    {r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))}
    (hrleE : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ ((projModel W').basicOpen r'))
    (hrleU : (projModel W).basicOpen r ≤ (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
    (b : AdjoinRoot (infChartCubic W)) :
    (((projModel W).presheaf.map (homOfLE hrleE).op).hom)
      ((e.hom.app ((projModel W').basicOpen r')).hom
        (pointedIsoChartTransport e.symm hr'le b)) =
    (((projModel W).presheaf.map (homOfLE hrleU).op).hom)
      ((chartYSectionsRingEquiv W).symm b) := by
  have hnat := congrArg (fun φ => CommRingCat.Hom.hom φ
    ((e.symm.hom.app (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))).hom
          ((chartYSectionsRingEquiv W).symm b)))
    (Scheme.Hom.naturality e.hom ((homOfLE hr'le).op))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
  have hstep1 : (((projModel W).presheaf.map (homOfLE hrleE).op).hom)
      ((e.hom.app ((projModel W').basicOpen r')).hom
        (pointedIsoChartTransport e.symm hr'le b)) =
      (((projModel W).presheaf.map (homOfLE hrleE).op).hom)
      ((((projModel W).presheaf.map ((TopologicalSpace.Opens.map e.hom.base).map
        (homOfLE hr'le)).op).hom)
        ((e.hom.app (e.symm.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))).hom
          ((e.symm.hom.app (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))).hom
          ((chartYSectionsRingEquiv W).symm b)))) :=
    congrArg (((projModel W).presheaf.map (homOfLE hrleE).op).hom) hnat
  refine hstep1.trans ?_
  have hfuse := congrArg (fun φ => CommRingCat.Hom.hom φ
    ((e.hom.app (e.symm.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))).hom
      ((e.symm.hom.app (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))).hom
          ((chartYSectionsRingEquiv W).symm b))))
    (((projModel W).presheaf.map_comp
      ((TopologicalSpace.Opens.map e.hom.base).map (homOfLE hr'le)).op
      (homOfLE hrleE).op).symm)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hfuse
  refine hfuse.trans ?_
  have hVle : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ (e.inv ⁻¹ᵁ (Proj.basicOpen (quotientGrading
    (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))) := by
    intro x hx
    show e.inv.base (e.hom.base x) ∈ (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))
    have h2 : e.inv.base (e.hom.base x) = x := by
      have := congrArg (fun m => m x) e.hom_inv_id
      rw [Scheme.Hom.comp_apply] at this
      exact this
    rw [h2]
    exact hrleU hx
  have halign := congrArg (fun ψ => (CommRingCat.Hom.hom
    ((projModel W).presheaf.map ψ))
    ((e.hom.app (e.symm.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))).hom
      ((e.symm.hom.app (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))).hom
          ((chartYSectionsRingEquiv W).symm b))))
    (Subsingleton.elim
      ((((TopologicalSpace.Opens.map e.hom.base).map (homOfLE hr'le)).op) ≫
        (homOfLE hrleE).op) ((homOfLE hVle).op))
  refine halign.trans ?_
  exact app_app_res_of_comp_eq_id e.hom e.inv e.hom_inv_id (Proj.basicOpen (quotientGrading
    (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))) hVle hrleU
    ((chartYSectionsRingEquiv W).symm b)

/-- Transports of restricted chart generators are transports at the smaller open. -/
private lemma transport_res_of_chartY_gen {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    {r' : Γ(projModel W', Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W'))
          (MvPolynomial.X 1)))} {r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))}
    (hrleE : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ ((projModel W').basicOpen r'))
    (hrle' : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))))
    (b' : AdjoinRoot (infChartCubic W')) :
    (((projModel W).presheaf.map (homOfLE hrleE).op).hom)
      ((e.hom.app ((projModel W').basicOpen r')).hom
        ((((projModel W').presheaf.map (homOfLE
          ((projModel W').basicOpen_le r')).op).hom)
          ((chartYSectionsRingEquiv W').symm b'))) =
    pointedIsoChartTransport e hrle' b' := by
  have hnat := congrArg (fun φ => CommRingCat.Hom.hom φ
    ((chartYSectionsRingEquiv W').symm b'))
    (Scheme.Hom.naturality e.hom ((homOfLE ((projModel W').basicOpen_le r')).op))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
  refine (congrArg (((projModel W).presheaf.map (homOfLE hrleE).op).hom) hnat).trans ?_
  have hfuse := congrArg (fun φ => CommRingCat.Hom.hom φ
    ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom
          ((chartYSectionsRingEquiv W').symm b')))
    (((projModel W).presheaf.map_comp
      ((TopologicalSpace.Opens.map e.hom.base).map (homOfLE
        ((projModel W').basicOpen_le r'))).op (homOfLE hrleE).op).symm)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hfuse
  refine hfuse.trans ?_
  exact congrArg (fun ψ => (CommRingCat.Hom.hom ((projModel W).presheaf.map ψ))
    ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom
          ((chartYSectionsRingEquiv W').symm b')))
    (Subsingleton.elim _ _)

private lemma mirror_span_aux {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    {r' : Γ(projModel W', Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))}
    (hr'le : (projModel W').basicOpen r' ≤ e.symm.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading
      (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
    {r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))}
    (hrleE : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ ((projModel W').basicOpen r'))
    (hrle' : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))))
    (hmirror : pointedIsoChartTransport e.symm hr'le
        (AdjoinRoot.root (infChartCubic W)) ∈ Ideal.span
      {(((projModel W').presheaf.map (homOfLE
          ((projModel W').basicOpen_le r')).op).hom)
          ((chartYSectionsRingEquiv W').symm (AdjoinRoot.root (infChartCubic W'))),
        (((projModel W').presheaf.map (homOfLE
          ((projModel W').basicOpen_le r')).op).hom)
          ((chartYSectionsRingEquiv W').symm (infChartTElem W'))}) :
    (((projModel W).presheaf.map
      (homOfLE ((projModel W).basicOpen_le r)).op).hom
      ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W)))) ∈
    Ideal.span {pointedIsoChartTransport e hrle' (AdjoinRoot.root (infChartCubic W')),
      pointedIsoChartTransport e hrle' (infChartTElem W')} := by
  obtain ⟨cs', ct', hct'⟩ := Ideal.mem_span_pair.mp hmirror
  set χe : ↑Γ(projModel W', (projModel W').basicOpen r') →+*
      ↑Γ(projModel W, (projModel W).basicOpen r) :=
    ((((projModel W).presheaf.map (homOfLE hrleE).op).hom).comp
      ((e.hom.app ((projModel W').basicOpen r')).hom)) with hχdef
  have hχS : χe ((((projModel W').presheaf.map (homOfLE
      ((projModel W').basicOpen_le r')).op).hom)
      ((chartYSectionsRingEquiv W').symm (AdjoinRoot.root (infChartCubic W')))) =
      pointedIsoChartTransport e hrle' (AdjoinRoot.root (infChartCubic W')) :=
    transport_res_of_chartY_gen e hrleE hrle' (AdjoinRoot.root (infChartCubic W'))
  have hχT : χe ((((projModel W').presheaf.map (homOfLE
      ((projModel W').basicOpen_le r')).op).hom)
      ((chartYSectionsRingEquiv W').symm (infChartTElem W'))) =
      pointedIsoChartTransport e hrle' (infChartTElem W') :=
    transport_res_of_chartY_gen e hrleE hrle' (infChartTElem W')
  have hχL : χe (pointedIsoChartTransport e.symm hr'le
      (AdjoinRoot.root (infChartCubic W))) =
      (((projModel W).presheaf.map
        (homOfLE ((projModel W).basicOpen_le r)).op).hom)
        ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W))) :=
    transport_symm_roundtrip e hr'le hrleE ((projModel W).basicOpen_le r)
      (AdjoinRoot.root (infChartCubic W))
  have himg0 := congrArg χe hct'
  have hexp := (map_add χe
      (cs' * (((projModel W').presheaf.map (homOfLE
        ((projModel W').basicOpen_le r')).op).hom)
        ((chartYSectionsRingEquiv W').symm (AdjoinRoot.root (infChartCubic W'))))
      (ct' * (((projModel W').presheaf.map (homOfLE
        ((projModel W').basicOpen_le r')).op).hom)
        ((chartYSectionsRingEquiv W').symm (infChartTElem W')))).trans
    (congrArg₂ (· + ·)
      (map_mul χe cs' ((((projModel W').presheaf.map (homOfLE
        ((projModel W').basicOpen_le r')).op).hom)
        ((chartYSectionsRingEquiv W').symm (AdjoinRoot.root (infChartCubic W')))))
      (map_mul χe ct' ((((projModel W').presheaf.map (homOfLE
        ((projModel W').basicOpen_le r')).op).hom)
        ((chartYSectionsRingEquiv W').symm (infChartTElem W')))))
  have hfinal : (((projModel W).presheaf.map
      (homOfLE ((projModel W).basicOpen_le r)).op).hom)
      ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W))) =
      χe cs' * pointedIsoChartTransport e hrle' (AdjoinRoot.root (infChartCubic W')) +
      χe ct' * pointedIsoChartTransport e hrle' (infChartTElem W') :=
    hχL.symm.trans (himg0.symm.trans (hexp.trans (congrArg₂ (· + ·)
      (congrArg (χe cs' * ·) hχS) (congrArg (χe ct' * ·) hχT))))
  refine mem_of_eq_of_mem hfinal ?_
  exact Ideal.add_mem _
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))

/-- **The mirror inclusion**: near a section prime, the `W`-side coordinate `s` lies in the
ideal generated by the transported `s'` and `t'` — the geometric heart of "pointed
isomorphisms preserve the order of vanishing along the section". -/
lemma exists_basicOpen_root_mem_span_transport {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (P : Ideal (AdjoinRoot (infChartCubic W))) [P.IsPrime]
    (ht : infChartTElem W ∈ P) :
    ∃ (r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
      (hr : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))),
      chartYSectionsRingEquiv W r ∉ P ∧
      IsUnit (pointedIsoChartTransport e hr (sectionUnitElem W')) ∧
      (((projModel W).presheaf.map
        (homOfLE ((projModel W).basicOpen_le r)).op).hom
        ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W)))) ∈
      Ideal.span {pointedIsoChartTransport e hr (AdjoinRoot.root (infChartCubic W')),
        pointedIsoChartTransport e hr (infChartTElem W')} := by
  classical
  -- the W'-side point and its refinement
  have hp1 : chartPointOf W P ∈ Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)) :=
    chartPointOf_mem_chartY W P
  have hpe' : e.hom.base (chartPointOf W P) ∈ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) :=
    pointedIso_chartPointOf_mem_chartY e hez P ht
  have hpinv : e.hom.base (chartPointOf W P) ∈ e.symm.hom ⁻¹ᵁ
      (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))) := by
    show e.inv.base (e.hom.base (chartPointOf W P)) ∈
      Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
    have h2 : e.inv.base (e.hom.base (chartPointOf W P)) = chartPointOf W P := by
      have := congrArg (fun m => m (chartPointOf W P)) e.hom_inv_id
      rw [Scheme.Hom.comp_apply] at this
      exact this
    rw [h2]
    exact hp1
  obtain ⟨r', hr'le, hpr'⟩ := (Proj.isAffineOpen_basicOpen
    (quotientGrading (projIdeal W'))
    ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))
    (mk_X_mem_quotientGrading_one W' 1) one_pos).exists_basicOpen_le
    ⟨e.hom.base (chartPointOf W P), hpinv⟩ hpe'
  -- the mirror span in Γ(X', bo r')
  have hmirror := pointedIsoChartTransport_mem_span_of_aug_eq_zero e.symm
    (pointedIso_hez_symm e hez) r' hr'le (infChartAug_root W)
  -- refine on the W-side inside bo(r-unit) ∩ e⁻¹bo(r')
  obtain ⟨r₀, hr₀le, hr₀P, hr₀U⟩ := exists_basicOpen_transport_unit e hez P ht
  have hpr₀ : chartPointOf W P ∈ (projModel W).basicOpen r₀ :=
    (chartPointOf_mem_basicOpen_iff W P r₀).mpr hr₀P
  have hpe2 : chartPointOf W P ∈ (projModel W).basicOpen r₀ ⊓
      e.hom ⁻¹ᵁ ((projModel W').basicOpen r') := by
    refine ⟨hpr₀, ?_⟩
    show e.hom.base (chartPointOf W P) ∈ (projModel W').basicOpen r'
    exact hpr'
  obtain ⟨r, hrle, hpr⟩ := (Proj.isAffineOpen_basicOpen
    (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
    (mk_X_mem_quotientGrading_one W 1) one_pos).exists_basicOpen_le
    ⟨chartPointOf W P, hpe2⟩ hp1
  have hrle₀ : (projModel W).basicOpen r ≤ (projModel W).basicOpen r₀ :=
    hrle.trans inf_le_left
  have hrleE : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ
      ((projModel W').basicOpen r') := hrle.trans inf_le_right
  have hrle' : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading
    (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) :=
    hrle₀.trans hr₀le
  refine ⟨r, hrle', (chartPointOf_mem_basicOpen_iff W P r).mp hpr, ?_, ?_⟩
  · have hres := pointedIsoChartTransport_res e hr₀le hrle₀ (sectionUnitElem W')
    rw [← hres]
    exact hr₀U.map _
  · exact mirror_span_aux e hr'le hrleE hrle' hmirror

/-- **The division pack**: a basic open avoiding the prime on which all four division
inputs hold — both section units invertible and `s` in the transported span. -/
lemma exists_basicOpen_division_pack {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (P : Ideal (AdjoinRoot (infChartCubic W))) [P.IsPrime]
    (ht : infChartTElem W ∈ P) :
    ∃ (r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
      (hr : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))),
      chartYSectionsRingEquiv W r ∉ P ∧
      IsUnit (pointedIsoChartTransport e hr (sectionUnitElem W')) ∧
      IsUnit ((((projModel W).presheaf.map
        (homOfLE ((projModel W).basicOpen_le r)).op).hom)
        ((chartYSectionsRingEquiv W).symm (sectionUnitElem W))) ∧
      (((projModel W).presheaf.map
        (homOfLE ((projModel W).basicOpen_le r)).op).hom
        ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W)))) ∈
      Ideal.span {pointedIsoChartTransport e hr (AdjoinRoot.root (infChartCubic W')),
        pointedIsoChartTransport e hr (infChartTElem W')} := by
  obtain ⟨r₀, hr₀, hr₀P, hr₀U, hr₀span⟩ :=
    exists_basicOpen_root_mem_span_transport e hez P ht
  have hUP : sectionUnitElem W ∉ P := by
    intro hU
    have hker : sectionUnitElem W - 1 ∈ P := by
      have h1 := sectionUnitElem_sub_one_mem W
      have h2 : Ideal.span {AdjoinRoot.root (infChartCubic W), infChartTElem W} ≤ P := by
        rw [Ideal.span_le]
        rintro x (rfl | rfl)
        · exact root_mem_of_tel_mem W P ht
        · exact ht
      exact h2 h1
    have hone : (1 : AdjoinRoot (infChartCubic W)) ∈ P := by
      have := P.sub_mem hU hker
      simpa using this
    exact (inferInstance : P.IsPrime).ne_top
      (Ideal.eq_top_of_isUnit_mem P hone isUnit_one)
  have hpU : chartPointOf W P ∈ (projModel W).basicOpen
      ((chartYSectionsRingEquiv W).symm (sectionUnitElem W)) := by
    rw [chartPointOf_mem_basicOpen_iff, RingEquiv.apply_symm_apply]
    exact hUP
  have hpr₀ : chartPointOf W P ∈ (projModel W).basicOpen r₀ :=
    (chartPointOf_mem_basicOpen_iff W P r₀).mpr hr₀P
  obtain ⟨r, hrle, hpr⟩ := (Proj.isAffineOpen_basicOpen
    (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
    (mk_X_mem_quotientGrading_one W 1) one_pos).exists_basicOpen_le
    ⟨chartPointOf W P, show chartPointOf W P ∈ (projModel W).basicOpen r₀ ⊓
      (projModel W).basicOpen ((chartYSectionsRingEquiv W).symm (sectionUnitElem W))
      from ⟨hpr₀, hpU⟩⟩ (chartPointOf_mem_chartY W P)
  have hrle₀ : (projModel W).basicOpen r ≤ (projModel W).basicOpen r₀ :=
    hrle.trans inf_le_left
  have hrleU : (projModel W).basicOpen r ≤ (projModel W).basicOpen
      ((chartYSectionsRingEquiv W).symm (sectionUnitElem W)) :=
    hrle.trans inf_le_right
  have hr' : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) := hrle₀.trans hr₀
  refine ⟨r, hr', (chartPointOf_mem_basicOpen_iff W P r).mp hpr, ?_, ?_, ?_⟩
  · have hres := pointedIsoChartTransport_res e hr₀ hrle₀ (sectionUnitElem W')
    rw [← hres]
    exact hr₀U.map _
  · have hunit0 : IsUnit ((((projModel W).presheaf.map (homOfLE
        ((projModel W).basicOpen_le ((chartYSectionsRingEquiv W).symm
          (sectionUnitElem W)))).op).hom)
        ((chartYSectionsRingEquiv W).symm (sectionUnitElem W))) :=
      AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen
        (X := (projModel W).toLocallyRingedSpace.toRingedSpace)
        ((chartYSectionsRingEquiv W).symm (sectionUnitElem W))
    have hpush := hunit0.map (((projModel W).presheaf.map (homOfLE hrleU).op).hom)
    have hstep := congrArg (fun φ => CommRingCat.Hom.hom φ
      ((chartYSectionsRingEquiv W).symm (sectionUnitElem W)))
      ((projModel W).presheaf.map_comp
        (homOfLE ((projModel W).basicOpen_le
          ((chartYSectionsRingEquiv W).symm (sectionUnitElem W)))).op
        (homOfLE hrleU).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hstep
    have halign := congrArg (fun ψ => (CommRingCat.Hom.hom
      ((projModel W).presheaf.map ψ))
      ((chartYSectionsRingEquiv W).symm (sectionUnitElem W)))
      (Subsingleton.elim ((homOfLE ((projModel W).basicOpen_le
        ((chartYSectionsRingEquiv W).symm (sectionUnitElem W)))).op ≫
        (homOfLE hrleU).op)
        ((homOfLE ((projModel W).basicOpen_le r)).op))
    have hval := (hstep.symm.trans halign)
    exact hval ▸ hpush
  · have hpush := span_pair_map_mem
      (((projModel W).presheaf.map (homOfLE hrle₀).op).hom) hr₀span
    have hσ := pointedIsoChartTransport_res e hr₀ hrle₀
      (AdjoinRoot.root (infChartCubic W'))
    have hτ := pointedIsoChartTransport_res e hr₀ hrle₀ (infChartTElem W')
    rw [hσ, hτ] at hpush
    have hstep := congrArg (fun φ => CommRingCat.Hom.hom φ
      ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W))))
      ((projModel W).presheaf.map_comp
        (homOfLE ((projModel W).basicOpen_le r₀)).op (homOfLE hrle₀).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hstep
    have halign := congrArg (fun ψ => (CommRingCat.Hom.hom
      ((projModel W).presheaf.map ψ))
      ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W))))
      (Subsingleton.elim ((homOfLE ((projModel W).basicOpen_le r₀)).op ≫
        (homOfLE hrle₀).op) ((homOfLE ((projModel W).basicOpen_le r)).op))
    exact mem_of_eq_of_mem (hstep.symm.trans halign).symm hpush

private lemma alpha_unit_aux {C : Type u} [CommRing C] (σ τ sW tW : C)
    (hτσ : τ ∈ Ideal.span {σ}) (htW : tW ∈ Ideal.span {sW})
    (hsp : sW ∈ Ideal.span {σ, τ}) (hσsp : σ ∈ Ideal.span {sW, tW})
    (hnzd : sW ∈ nonZeroDivisors C) :
    ∃ v : Cˣ, σ = ↑v * sW := by
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hτσ
  obtain ⟨v₀, hv₀⟩ := Ideal.mem_span_singleton.mp htW
  obtain ⟨Θ, Ξ, hΘ⟩ := Ideal.mem_span_pair.mp hsp
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hσsp
  have hσs : σ = (a + b * v₀) * sW := by
    rw [← hab, hv₀]
    ring
  have hss : sW = (Θ + Ξ * w) * ((a + b * v₀) * sW) := by
    conv_lhs => rw [← hΘ]
    rw [hw, ← hσs]
    ring
  have hcancel : (1 - (Θ + Ξ * w) * (a + b * v₀)) * sW = 0 := by
    rw [sub_mul, one_mul]
    rw [show (Θ + Ξ * w) * (a + b * v₀) * sW =
      (Θ + Ξ * w) * ((a + b * v₀) * sW) from by ring]
    rw [← hss]
    ring
  have hone : (Θ + Ξ * w) * (a + b * v₀) = 1 := by
    have h2 := (mem_nonZeroDivisors_iff.mp hnzd).2 _ hcancel
    linear_combination -h2
  have hunit : IsUnit (a + b * v₀) :=
    isUnit_iff_exists_inv.mpr ⟨Θ + Ξ * w, by rw [mul_comm]; exact hone⟩
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]
  exact hσs

/-- **The α-unit**: near every prime containing `t`, the transported `s'` is a unit multiple
of `s` — pointed isomorphisms preserve the order of vanishing along the section exactly. -/
lemma exists_basicOpen_transport_root_unit_mul {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (P : Ideal (AdjoinRoot (infChartCubic W))) [P.IsPrime]
    (ht : infChartTElem W ∈ P) :
    ∃ (r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
      (hr : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))),
      chartYSectionsRingEquiv W r ∉ P ∧
      ∃ v : (↑Γ(projModel W, (projModel W).basicOpen r))ˣ,
        pointedIsoChartTransport e hr (AdjoinRoot.root (infChartCubic W')) =
          ↑v * ((((projModel W).presheaf.map
            (homOfLE ((projModel W).basicOpen_le r)).op).hom)
            ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W)))) := by
  obtain ⟨r, hr, hrP, hU', hÛ, hspan⟩ := exists_basicOpen_division_pack e hez P ht
  refine ⟨r, hr, hrP, ?_⟩
  refine alpha_unit_aux
    (pointedIsoChartTransport e hr (AdjoinRoot.root (infChartCubic W')))
    (pointedIsoChartTransport e hr (infChartTElem W'))
    ((((projModel W).presheaf.map
      (homOfLE ((projModel W).basicOpen_le r)).op).hom)
      ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W))))
    ((((projModel W).presheaf.map
      (homOfLE ((projModel W).basicOpen_le r)).op).hom)
      ((chartYSectionsRingEquiv W).symm (infChartTElem W)))
    (tel_image_mem_span_of_isUnit (pointedIsoChartTransport e hr) hU')
    (tel_image_mem_span_of_isUnit
      ((((projModel W).presheaf.map
        (homOfLE ((projModel W).basicOpen_le r)).op).hom).comp
        (chartYSectionsRingEquiv W).symm.toRingHom) hÛ) hspan
    (pointedIsoChartTransport_mem_span_of_aug_eq_zero e hez r hr
      (infChartAug_root W')) ?_
  haveI := (Proj.isAffineOpen_basicOpen (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
    (mk_X_mem_quotientGrading_one W 1) one_pos).isLocalization_basicOpen r
  exact algebraMap_mem_nonZeroDivisors_of_away r
    (RingEquiv_map_mem_nonZeroDivisors (chartYSectionsRingEquiv W).symm
      (infChart_root_mem_nonZeroDivisors W))

private lemma witness_V_le_chartYPreimage {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    {r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))}
    (hr : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) :
    (projModel W).basicOpen r ⊓ (projModel W).basicOpen
      ((chartYSectionsRingEquiv W).symm (infChartTElem W)) ≤
    e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) := inf_le_left.trans hr

private lemma witness_V_le_overlapPreimage {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    {r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))}
    (hr : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) :
    (projModel W).basicOpen r ⊓ (projModel W).basicOpen
      ((chartYSectionsRingEquiv W).symm (infChartTElem W)) ≤
    e.hom ⁻¹ᵁ Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)) := by
  intro x hx
  have h1 : e.hom.base x ∈ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) := (inf_le_left.trans hr) hx
  have h2 : x ∈ Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) :=
    basicOpen_tSection_le_chartZ hx.2
  have h3 : e.hom.base x ∈ Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)) := by
    have := pointedIso_preimage_zChart e hez
    rw [← this] at h2
    exact h2
  show e.hom.base x ∈ Proj.basicOpen (quotientGrading (projIdeal W'))
    ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
      (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
  rw [Proj.basicOpen_mul]
  exact ⟨h1, h3⟩

private lemma witness_V_le_overlapW {W W' : WeierstrassCurve R}
    (_e : projModel W ≅ projModel W')
    {r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))} :
    (projModel W).basicOpen r ⊓ (projModel W).basicOpen
      ((chartYSectionsRingEquiv W).symm (infChartTElem W)) ≤
    Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) := by
  rw [Proj.basicOpen_mul]
  exact le_inf (inf_le_left.trans ((projModel W).basicOpen_le r))
    (inf_le_right.trans basicOpen_tSection_le_chartZ)

private lemma witness_eq_V {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (f' : W'.toAffine.CoordinateRing) (b'' : AdjoinRoot (infChartCubic W')) (n : ℕ)
    (hb'' : algebraMap (AdjoinRoot (infChartCubic W'))
        (Localization.Away (infChartTElem W')) b'' =
      overlapMap W' f' * algebraMap (AdjoinRoot (infChartCubic W'))
        (Localization.Away (infChartTElem W'))
        (AdjoinRoot.root (infChartCubic W')) ^ n)
    {V : (projModel W).Opens}
    (hVE : V ≤ e.hom ⁻¹ᵁ Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)))
    (hVY : V ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))))
    (hVover : V ≤ Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) :
    pointedIsoChartTransport e hVY b'' =
    (((projModel W).presheaf.map (homOfLE hVover).op).hom)
      ((overlapSectionsEquiv W).symm
        (overlapMap W (pointedIsoCoordEquiv e heπ hez f'))) *
    (pointedIsoChartTransport e hVY
      (AdjoinRoot.root (infChartCubic W'))) ^ n := by
  have htr := pointedIso_overlap_sections_equation e heπ hez f' b''
    (AdjoinRoot.root (infChartCubic W')) n hb''
  have hres := congrArg (((projModel W).presheaf.map
    (homOfLE hVE).op).hom) htr
  have hexp := (map_mul (((projModel W).presheaf.map
      (homOfLE hVE).op).hom)
      ((((projModel W).presheaf.map
        (homOfLE (overlapPreimage_le_chartZ e hez)).op).hom)
        ((chartZSectionsRingEquiv W).symm (pointedIsoCoordEquiv e heπ hez f')))
      (((((projModel W).presheaf.map
        (homOfLE (overlapPreimage_le_chartYPreimage e)).op).hom)
        ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom
          ((chartYSectionsRingEquiv W').symm
          (AdjoinRoot.root (infChartCubic W'))))) ^ n)).trans
    (congrArg ((((projModel W).presheaf.map
      (homOfLE hVE).op).hom)
      (((projModel W).presheaf.map
        (homOfLE (overlapPreimage_le_chartZ e hez)).op).hom
        ((chartZSectionsRingEquiv W).symm (pointedIsoCoordEquiv e heπ hez f'))) * ·)
      (map_pow (((projModel W).presheaf.map
        (homOfLE hVE).op).hom)
        ((((projModel W).presheaf.map
          (homOfLE (overlapPreimage_le_chartYPreimage e)).op).hom)
          ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom
          ((chartYSectionsRingEquiv W').symm
            (AdjoinRoot.root (infChartCubic W'))))) n))
  have hY : ∀ b₀ : AdjoinRoot (infChartCubic W'),
      (((projModel W).presheaf.map
        (homOfLE hVE).op).hom)
        ((((projModel W).presheaf.map
          (homOfLE (overlapPreimage_le_chartYPreimage e)).op).hom)
          ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom
          ((chartYSectionsRingEquiv W').symm b₀))) =
      pointedIsoChartTransport e hVY b₀ := by
    intro b₀
    exact pointedIsoChartTransport_res e (overlapPreimage_le_chartYPreimage e)
      hVE b₀
  have hZ : (((projModel W).presheaf.map
      (homOfLE hVE).op).hom)
      ((((projModel W).presheaf.map
        (homOfLE (overlapPreimage_le_chartZ e hez)).op).hom)
        ((chartZSectionsRingEquiv W).symm (pointedIsoCoordEquiv e heπ hez f'))) =
      (((projModel W).presheaf.map (homOfLE hVover).op).hom)
        ((overlapSectionsEquiv W).symm
          (overlapMap W (pointedIsoCoordEquiv e heπ hez f'))) := by
    have hfuse := congrArg (fun φ => CommRingCat.Hom.hom φ
      ((chartZSectionsRingEquiv W).symm (pointedIsoCoordEquiv e heπ hez f')))
      (((projModel W).presheaf.map_comp
        (homOfLE (overlapPreimage_le_chartZ e hez)).op
        (homOfLE hVE).op).symm)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hfuse
    refine hfuse.trans ?_
    have hsplit := congrArg (fun φ => CommRingCat.Hom.hom φ
      ((chartZSectionsRingEquiv W).symm (pointedIsoCoordEquiv e heπ hez f')))
      ((projModel W).presheaf.map_comp
        (homOfLE (Proj.basicOpen_mono _
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
            (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          ⟨_, mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))⟩)).op
        (homOfLE hVover).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hsplit
    have halign := congrArg (fun ψ => (CommRingCat.Hom.hom
      ((projModel W).presheaf.map ψ))
      ((chartZSectionsRingEquiv W).symm (pointedIsoCoordEquiv e heπ hez f')))
      (Subsingleton.elim
        ((homOfLE (overlapPreimage_le_chartZ e hez)).op ≫
          (homOfLE hVE).op)
        ((homOfLE (Proj.basicOpen_mono _
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
            (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          ⟨_, mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))⟩)).op ≫
          (homOfLE hVover).op))
    refine halign.trans ?_
    refine hsplit.trans ?_
    exact congrArg (((projModel W).presheaf.map
      (homOfLE hVover).op).hom)
      (res_chartZSection_eq_symm_overlapMap W (pointedIsoCoordEquiv e heπ hez f'))
  refine ((hY b'').symm.trans (hres.trans (hexp.trans ?_)))
  exact congrArg₂ (· * ·) hZ (congrArg (· ^ n)
    (hY (AdjoinRoot.root (infChartCubic W'))))

/-- Overlap-dictionary values restrict from the overlap to the division open as `Y`-chart
restrictions. -/
private lemma witness_res_dictY {W : WeierstrassCurve R}
    {V : (projModel W).Opens}
    (hVle : V ≤ Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
          (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))
    (hVU : V ≤ (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
    (b : AdjoinRoot (infChartCubic W)) :
    (((projModel W).presheaf.map (homOfLE hVle).op).hom)
      ((overlapSectionsEquiv W).symm (algebraMap (AdjoinRoot (infChartCubic W))
        (Localization.Away (infChartTElem W)) b)) =
    (((projModel W).presheaf.map (homOfLE hVU).op).hom)
      ((chartYSectionsRingEquiv W).symm b) := by
  have hd := res_chartYSection_eq_symm_algebraMap W b
  have hres := congrArg (((projModel W).presheaf.map (homOfLE hVle).op).hom) hd.symm
  refine hres.trans ?_
  have hfuse := congrArg (fun φ => CommRingCat.Hom.hom φ
    ((chartYSectionsRingEquiv W).symm b))
    (((projModel W).presheaf.map_comp
      (homOfLE (Proj.basicOpen_mono _
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
          (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ⟨_, rfl⟩)).op
      (homOfLE hVle).op).symm)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hfuse
  refine hfuse.trans ?_
  exact congrArg (fun ψ => (CommRingCat.Hom.hom ((projModel W).presheaf.map ψ))
    ((chartYSectionsRingEquiv W).symm b)) (Subsingleton.elim _ _)

private lemma psi_clear_generic {L C : Type u} [CommRing L] [CommRing C]
    (ψ : L →+* C) {x tL bL : L} {K : ℕ} (h : x * tL ^ K = bL) :
    ψ x * (ψ tL) ^ K = ψ bL := by
  rw [← map_pow, ← map_mul, h]

private lemma witness_eq_V' {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (f' : W'.toAffine.CoordinateRing) (b'' : AdjoinRoot (infChartCubic W')) (n : ℕ)
    (hb'' : algebraMap (AdjoinRoot (infChartCubic W'))
        (Localization.Away (infChartTElem W')) b'' =
      overlapMap W' f' * algebraMap (AdjoinRoot (infChartCubic W'))
        (Localization.Away (infChartTElem W'))
        (AdjoinRoot.root (infChartCubic W')) ^ n)
    {r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))}
    (hr : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))))
    (bΦ : AdjoinRoot (infChartCubic W)) (K : ℕ)
    (hbΦ : overlapMap W (pointedIsoCoordEquiv e heπ hez f') *
        algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W)) (infChartTElem W) ^ K =
      algebraMap (AdjoinRoot (infChartCubic W))
        (Localization.Away (infChartTElem W)) bΦ) :
    pointedIsoChartTransport e
        ((Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
          (infChartTElem W))).le.trans (witness_V_le_chartYPreimage e hr)) b'' *
      ((((projModel W).presheaf.map (homOfLE ((projModel W).basicOpen_le
        (r * (chartYSectionsRingEquiv W).symm (infChartTElem W)))).op).hom)
        ((chartYSectionsRingEquiv W).symm (infChartTElem W))) ^ K =
    ((((projModel W).presheaf.map (homOfLE ((projModel W).basicOpen_le
        (r * (chartYSectionsRingEquiv W).symm (infChartTElem W)))).op).hom)
        ((chartYSectionsRingEquiv W).symm bΦ)) *
      (pointedIsoChartTransport e
        ((Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
          (infChartTElem W))).le.trans (witness_V_le_chartYPreimage e hr))
        (AdjoinRoot.root (infChartCubic W'))) ^ n := by
  have hVE := (Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
    (infChartTElem W))).le.trans (witness_V_le_overlapPreimage e hez hr)
  have hVover := (Scheme.basicOpen_mul (projModel W) r
    ((chartYSectionsRingEquiv W).symm (infChartTElem W))).le.trans
    (witness_V_le_overlapW e (r := r))
  have h0 := witness_eq_V e heπ hez f' b'' n hb'' hVE
    ((Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
      (infChartTElem W))).le.trans (witness_V_le_chartYPreimage e hr)) hVover
  have h1 := congrArg (· * ((((projModel W).presheaf.map
    (homOfLE hVover).op).hom) ((overlapSectionsEquiv W).symm
      (algebraMap (AdjoinRoot (infChartCubic W))
        (Localization.Away (infChartTElem W)) (infChartTElem W)))) ^ K) h0
  have hclear := psi_clear_generic ((((projModel W).presheaf.map
    (homOfLE hVover).op).hom).comp (overlapSectionsEquiv W).symm.toRingHom) hbΦ
  have hdictT := witness_res_dictY hVover ((projModel W).basicOpen_le
    (r * (chartYSectionsRingEquiv W).symm (infChartTElem W))) (infChartTElem W)
  have hdictB := witness_res_dictY hVover ((projModel W).basicOpen_le
    (r * (chartYSectionsRingEquiv W).symm (infChartTElem W))) bΦ
  have hrearr : ∀ (z t₀ y : ↑Γ(projModel W, (projModel W).basicOpen
      (r * (chartYSectionsRingEquiv W).symm (infChartTElem W)))),
      z * y ^ n * t₀ ^ K = (z * t₀ ^ K) * y ^ n := fun z t₀ y => by ring
  refine (congrArg₂ (· * ·) rfl (congrArg (· ^ K) hdictT.symm)).trans ?_
  refine h1.trans ?_
  refine (hrearr _ _ _).trans ?_
  exact congrArg₂ (· * ·) (hclear.trans hdictB) rfl

private lemma witness_res_unit_root {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    {r : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))}
    (hr : (projModel W).basicOpen r ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))))
    (v : (↑Γ(projModel W, (projModel W).basicOpen r))ˣ)
    (hv : pointedIsoChartTransport e hr (AdjoinRoot.root (infChartCubic W')) =
      ↑v * ((((projModel W).presheaf.map
        (homOfLE ((projModel W).basicOpen_le r)).op).hom)
        ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W))))) :
    pointedIsoChartTransport e
        ((Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
          (infChartTElem W))).le.trans (witness_V_le_chartYPreimage e hr))
        (AdjoinRoot.root (infChartCubic W')) =
    (((projModel W).presheaf.map (homOfLE ((Scheme.basicOpen_mul (projModel W) r
        ((chartYSectionsRingEquiv W).symm (infChartTElem W))).le.trans
        inf_le_left)).op).hom) ↑v *
    (((projModel W).presheaf.map (homOfLE ((projModel W).basicOpen_le
        (r * (chartYSectionsRingEquiv W).symm (infChartTElem W)))).op).hom)
      ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W))) := by
  have hres := pointedIsoChartTransport_res e hr
    ((Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
      (infChartTElem W))).le.trans inf_le_left)
    (AdjoinRoot.root (infChartCubic W'))
  refine hres.symm.trans ?_
  refine (congrArg (((projModel W).presheaf.map (homOfLE
    ((Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
      (infChartTElem W))).le.trans inf_le_left)).op).hom) hv).trans ?_
  refine (map_mul _ _ _).trans ?_
  refine congrArg₂ (· * ·) rfl ?_
  have hfuse := congrArg (fun φ => CommRingCat.Hom.hom φ
    ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W))))
    (((projModel W).presheaf.map_comp
      (homOfLE ((projModel W).basicOpen_le r)).op
      (homOfLE ((Scheme.basicOpen_mul (projModel W) r
        ((chartYSectionsRingEquiv W).symm (infChartTElem W))).le.trans
        inf_le_left)).op).symm)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hfuse
  refine hfuse.trans ?_
  exact congrArg (fun ψ => (CommRingCat.Hom.hom ((projModel W).presheaf.map ψ))
    ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W))))
    (Subsingleton.elim _ _)

private lemma res_numerator_generic {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) {V : X.Opens}
    (hV : V ≤ X.basicOpen f) (hVU : V ≤ U)
    (x : ↑Γ(X, X.basicOpen f)) :
    ∃ (x₀ : ↑Γ(X, U)) (j : ℕ),
      ((X.presheaf.map (homOfLE hV).op).hom) x *
        ((X.presheaf.map (homOfLE hVU).op).hom) (f ^ j) =
      ((X.presheaf.map (homOfLE hVU).op).hom) x₀ := by
  haveI := hU.isLocalization_basicOpen f
  obtain ⟨⟨x₀, u⟩, hx⟩ := IsLocalization.surj (Submonoid.powers f) x
  obtain ⟨j, hj⟩ := u.2
  rw [← hj] at hx
  refine ⟨x₀, j, ?_⟩
  have hres := congrArg ((X.presheaf.map (homOfLE hV).op).hom) hx
  have hexp := (map_mul ((X.presheaf.map (homOfLE hV).op).hom) x
    ((algebraMap (↑Γ(X, U)) (↑Γ(X, X.basicOpen f))) (f ^ j))).symm.trans hres
  have hfuse : ∀ y : ↑Γ(X, U),
      ((X.presheaf.map (homOfLE hV).op).hom)
        ((algebraMap (↑Γ(X, U)) (↑Γ(X, X.basicOpen f))) y) =
      ((X.presheaf.map (homOfLE hVU).op).hom) y := by
    intro y
    have h0 : (algebraMap (↑Γ(X, U)) (↑Γ(X, X.basicOpen f))) y =
        ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom) y := rfl
    rw [h0]
    have hc := congrArg (fun φ => CommRingCat.Hom.hom φ y)
      ((X.presheaf.map_comp (homOfLE (X.basicOpen_le f)).op
        (homOfLE hV).op).symm)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hc
    refine hc.trans ?_
    exact congrArg (fun ψ => (CommRingCat.Hom.hom (X.presheaf.map ψ)) y)
      (Subsingleton.elim _ _)
  exact (congrArg₂ (· * ·) rfl (hfuse (f ^ j))).symm.trans (hexp.trans (hfuse x₀))

private lemma res_eq_pull_generic {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) {y₁ y₂ : ↑Γ(X, U)}
    (h : ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom) y₁ =
      ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom) y₂) :
    ∃ m : ℕ, f ^ m * y₁ = f ^ m * y₂ := by
  haveI := hU.isLocalization_basicOpen f
  have h' : (algebraMap (↑Γ(X, U)) (↑Γ(X, X.basicOpen f))) y₁ =
      (algebraMap (↑Γ(X, U)) (↑Γ(X, X.basicOpen f))) y₂ := h
  obtain ⟨⟨c, hc⟩, hcy⟩ := (IsLocalization.eq_iff_exists
    (Submonoid.powers f) (↑Γ(X, X.basicOpen f))).mp h'
  obtain ⟨m, hm⟩ := hc
  refine ⟨m, ?_⟩
  have hcy' : c * y₁ = c * y₂ := hcy
  rw [← hm] at hcy'
  exact hcy'

private lemma unit_numerator_generic {A S : Type u} [CommRing A] [CommRing S]
    [Algebra A S] (g : A) [IsLocalization.Away g S] (v : Sˣ) :
    ∃ (v₀ : A) (k : ℕ), (↑v : S) * algebraMap A S (g ^ k) = algebraMap A S v₀ ∧
      ∀ (P : Ideal A), P.IsPrime → g ∉ P → v₀ ∉ P := by
  obtain ⟨⟨v₀, u⟩, hv₀⟩ := IsLocalization.surj (Submonoid.powers g) (↑v : S)
  obtain ⟨k, hk⟩ := u.2
  rw [← hk] at hv₀
  obtain ⟨⟨w₀, u'⟩, hw₀⟩ := IsLocalization.surj (Submonoid.powers g) (↑v⁻¹ : S)
  obtain ⟨l, hl⟩ := u'.2
  rw [← hl] at hw₀
  have hprod : algebraMap A S (v₀ * w₀) = algebraMap A S (g ^ k * g ^ l) := by
    rw [map_mul, ← hv₀, ← hw₀, map_mul]
    have hvv : (↑v : S) * ↑v⁻¹ = 1 := v.mul_inv
    calc (↑v : S) * algebraMap A S (g ^ k) * ((↑v⁻¹ : S) * algebraMap A S (g ^ l))
        = ((↑v : S) * ↑v⁻¹) * (algebraMap A S (g ^ k) * algebraMap A S (g ^ l)) := by
          ring
      _ = algebraMap A S (g ^ k) * algebraMap A S (g ^ l) := by rw [hvv, one_mul]
  obtain ⟨⟨c, hc⟩, hcy⟩ := (IsLocalization.eq_iff_exists
    (Submonoid.powers g) S).mp hprod
  obtain ⟨m, hm⟩ := hc
  have hcy' : c * (v₀ * w₀) = c * (g ^ k * g ^ l) := hcy
  rw [← hm] at hcy'
  refine ⟨v₀, k, hv₀, fun P hP hgP hv₀P => ?_⟩
  have hmem : g ^ m * (g ^ k * g ^ l) ∈ P := by
    rw [← hcy']
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hv₀P)
  rcases hP.mem_or_mem hmem with h1 | h2
  · exact hgP (hP.mem_of_pow_mem _ h1)
  · rcases hP.mem_or_mem h2 with h3 | h4
    · exact hgP (hP.mem_of_pow_mem _ h3)
    · exact hgP (hP.mem_of_pow_mem _ h4)

private lemma res_algebraMap_fuse_generic {X : Scheme.{u}} {U : X.Opens}
    (f : Γ(X, U)) {V : X.Opens} (hV : V ≤ X.basicOpen f) (hVU : V ≤ U)
    (y : ↑Γ(X, U)) :
    ((X.presheaf.map (homOfLE hV).op).hom)
      ((algebraMap (↑Γ(X, U)) (↑Γ(X, X.basicOpen f))) y) =
    ((X.presheaf.map (homOfLE hVU).op).hom) y := by
  have h0 : (algebraMap (↑Γ(X, U)) (↑Γ(X, X.basicOpen f))) y =
      ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom) y := rfl
  rw [h0]
  have hc := congrArg (fun φ => CommRingCat.Hom.hom φ y)
    ((X.presheaf.map_comp (homOfLE (X.basicOpen_le f)).op (homOfLE hV).op).symm)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hc
  refine hc.trans ?_
  exact congrArg (fun ψ => (CommRingCat.Hom.hom (X.presheaf.map ψ)) y)
    (Subsingleton.elim _ _)

private lemma witness_combine_generic {A C : Type u} [CommRing A] [CommRing C]
    (φ : A →+* C) (T Troot vC : C) (rtA rA sA bΦA u₀ v₀ : A) (n K j k : ℕ)
    (hEQ : T * (φ rtA) ^ K = φ bΦA * Troot ^ n)
    (hα : Troot = vC * φ sA)
    (hu₀ : T * φ (rA ^ j) = φ u₀)
    (hv₀ : vC * φ (rA ^ k) = φ v₀) :
    φ (u₀ * rtA ^ K * rA ^ (n * k)) = φ (bΦA * sA ^ n * v₀ ^ n * rA ^ j) := by
  have h1 : T * (φ rtA) ^ K * φ (rA ^ j) * φ (rA ^ (n * k)) =
      φ bΦA * (vC * φ sA) ^ n * φ (rA ^ j) * φ (rA ^ (n * k)) := by
    rw [← hα]
    calc T * (φ rtA) ^ K * φ (rA ^ j) * φ (rA ^ (n * k))
        = (T * (φ rtA) ^ K) * φ (rA ^ j) * φ (rA ^ (n * k)) := by ring
      _ = (φ bΦA * Troot ^ n) * φ (rA ^ j) * φ (rA ^ (n * k)) := by rw [hEQ]
      _ = _ := by ring
  have hLHS : T * (φ rtA) ^ K * φ (rA ^ j) * φ (rA ^ (n * k)) =
      φ (u₀ * rtA ^ K * rA ^ (n * k)) := by
    calc T * (φ rtA) ^ K * φ (rA ^ j) * φ (rA ^ (n * k))
        = (T * φ (rA ^ j)) * (φ rtA) ^ K * φ (rA ^ (n * k)) := by ring
      _ = φ u₀ * (φ rtA) ^ K * φ (rA ^ (n * k)) := by rw [hu₀]
      _ = _ := by rw [← map_pow, ← map_mul, ← map_mul]
  have hRHS : φ bΦA * (vC * φ sA) ^ n * φ (rA ^ j) * φ (rA ^ (n * k)) =
      φ (bΦA * sA ^ n * v₀ ^ n * rA ^ j) := by
    have hvn : vC ^ n * φ (rA ^ (n * k)) = φ (v₀ ^ n) := by
      calc vC ^ n * φ (rA ^ (n * k)) = (vC * φ (rA ^ k)) ^ n := by
            rw [mul_pow, ← map_pow, ← pow_mul, Nat.mul_comm k n]
        _ = (φ v₀) ^ n := by rw [hv₀]
        _ = φ (v₀ ^ n) := (map_pow φ v₀ n).symm
    calc φ bΦA * (vC * φ sA) ^ n * φ (rA ^ j) * φ (rA ^ (n * k))
        = φ bΦA * (φ sA) ^ n * (vC ^ n * φ (rA ^ (n * k))) * φ (rA ^ j) := by ring
      _ = φ bΦA * (φ sA) ^ n * φ (v₀ ^ n) * φ (rA ^ j) := by rw [hvn]
      _ = _ := by rw [← map_pow, ← map_mul, ← map_mul, ← map_mul]
  exact hLHS.symm.trans (h1.trans hRHS)

private lemma hom_fold_generic {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (g t bu bv bΦ rt : A) (m K nk j n : ℕ)
    (h : (g * t) ^ m * (bu * t ^ K * g ^ nk) =
      (g * t) ^ m * (bΦ * rt ^ n * bv ^ n * g ^ j)) :
    (φ g * φ t) ^ m * (φ bu * (φ t) ^ K * (φ g) ^ nk) =
    (φ g * φ t) ^ m * (φ bΦ * (φ rt) ^ n * (φ bv) ^ n * (φ g) ^ j) := by
  simpa only [map_mul, map_pow] using congrArg φ h

private lemma equiv_fold_generic {A B : Type u} [CommRing A] [CommRing B]
    (φ : A ≃+* B) (r rt u₀ v₀ bΦs ss : A) (m K nk j n : ℕ)
    (hm : (r * rt) ^ m * (u₀ * rt ^ K * r ^ nk) =
      (r * rt) ^ m * (bΦs * ss ^ n * v₀ ^ n * r ^ j)) :
    (φ r * φ rt) ^ m * (φ u₀ * (φ rt) ^ K * (φ r) ^ nk) =
    (φ r * φ rt) ^ m * (φ bΦs * (φ ss) ^ n * (φ v₀) ^ n * (φ r) ^ j) := by
  simpa only [map_mul, map_pow] using congrArg φ hm

private lemma witness_B_data {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (f' : W'.toAffine.CoordinateRing) (n : ℕ)
    (hf' : overlapMap W' f' * algebraMap (AdjoinRoot (infChartCubic W'))
        (Localization.Away (infChartTElem W'))
        (AdjoinRoot.root (infChartCubic W')) ^ n ∈
      Set.range (algebraMap (AdjoinRoot (infChartCubic W'))
        (Localization.Away (infChartTElem W'))))
    (P : Ideal (AdjoinRoot (infChartCubic W))) [P.IsPrime]
    (ht : infChartTElem W ∈ P) :
    ∃ (g bu bv bΦ : AdjoinRoot (infChartCubic W)) (m K j k : ℕ),
      g ∉ P ∧ bv ∉ P ∧
      (overlapMap W (pointedIsoCoordEquiv e heπ hez f') *
        (algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W))) (infChartTElem W) ^ K = (algebraMap (AdjoinRoot
        (infChartCubic W))
      (Localization.Away (infChartTElem W))) bΦ) ∧
      ((g * infChartTElem W) ^ m *
          (bu * infChartTElem W ^ K * g ^ (n * k)) =
        (g * infChartTElem W) ^ m *
          (bΦ * AdjoinRoot.root (infChartCubic W) ^ n * bv ^ n * g ^ j)) := by
  classical
  obtain ⟨b'', hb''⟩ := hf'
  obtain ⟨⟨bΦ, u⟩, hbΦ0⟩ := IsLocalization.surj (Submonoid.powers (infChartTElem W))
    (overlapMap W (pointedIsoCoordEquiv e heπ hez f'))
  obtain ⟨K, hK⟩ := u.2
  rw [← hK] at hbΦ0
  rw [map_pow] at hbΦ0
  obtain ⟨r, hr, hrP, v, hv⟩ := exists_basicOpen_transport_root_unit_mul e hez P ht
  have hEQ := witness_eq_V' e heπ hez f' b'' n hb'' hr bΦ K hbΦ0
  have hα := witness_res_unit_root e hr v hv
  obtain ⟨u₀, j, hu₀⟩ := res_numerator_generic
    (Proj.isAffineOpen_basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
      (mk_X_mem_quotientGrading_one W 1) one_pos) r
    ((Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
      (infChartTElem W))).le.trans inf_le_left)
    ((projModel W).basicOpen_le
      (r * (chartYSectionsRingEquiv W).symm (infChartTElem W)))
    (pointedIsoChartTransport e hr b'')
  have hu₀' : pointedIsoChartTransport e
      ((Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
        (infChartTElem W))).le.trans (witness_V_le_chartYPreimage e hr)) b'' *
      (((projModel W).presheaf.map (homOfLE ((projModel W).basicOpen_le
        (r * (chartYSectionsRingEquiv W).symm (infChartTElem W)))).op).hom)
        (r ^ j) =
      (((projModel W).presheaf.map (homOfLE ((projModel W).basicOpen_le
        (r * (chartYSectionsRingEquiv W).symm (infChartTElem W)))).op).hom) u₀ := by
    refine (congrArg (· * (((projModel W).presheaf.map (homOfLE
      ((projModel W).basicOpen_le (r * (chartYSectionsRingEquiv W).symm
        (infChartTElem W)))).op).hom) (r ^ j))
      (pointedIsoChartTransport_res e hr ((Scheme.basicOpen_mul (projModel W) r
        ((chartYSectionsRingEquiv W).symm (infChartTElem W))).le.trans
        inf_le_left) b'').symm).trans ?_
    exact hu₀
  haveI := (Proj.isAffineOpen_basicOpen (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
    (mk_X_mem_quotientGrading_one W 1) one_pos).isLocalization_basicOpen r
  obtain ⟨v₀, k, hv₀, hv₀P⟩ := unit_numerator_generic
    (S := ↑Γ(projModel W, (projModel W).basicOpen r)) r v
  have hv₀' : (((projModel W).presheaf.map (homOfLE ((Scheme.basicOpen_mul
      (projModel W) r ((chartYSectionsRingEquiv W).symm
        (infChartTElem W))).le.trans inf_le_left)).op).hom) ↑v *
      (((projModel W).presheaf.map (homOfLE ((projModel W).basicOpen_le
        (r * (chartYSectionsRingEquiv W).symm (infChartTElem W)))).op).hom)
        (r ^ k) =
      (((projModel W).presheaf.map (homOfLE ((projModel W).basicOpen_le
        (r * (chartYSectionsRingEquiv W).symm (infChartTElem W)))).op).hom) v₀ := by
    have hres := congrArg ((((projModel W).presheaf.map (homOfLE
      ((Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
        (infChartTElem W))).le.trans inf_le_left)).op).hom)) hv₀
    have hexp := (map_mul ((((projModel W).presheaf.map (homOfLE
      ((Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
        (infChartTElem W))).le.trans inf_le_left)).op).hom)) (↑v)
      ((algebraMap _ _) (r ^ k))).symm.trans hres
    refine ?_
    have hf1 := res_algebraMap_fuse_generic r
      ((Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
        (infChartTElem W))).le.trans inf_le_left)
      ((projModel W).basicOpen_le
        (r * (chartYSectionsRingEquiv W).symm (infChartTElem W))) (r ^ k)
    have hf2 := res_algebraMap_fuse_generic r
      ((Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
        (infChartTElem W))).le.trans inf_le_left)
      ((projModel W).basicOpen_le
        (r * (chartYSectionsRingEquiv W).symm (infChartTElem W))) v₀
    exact ((congrArg₂ (· * ·) rfl hf1).symm.trans (hexp.trans hf2))
  have hcomb := witness_combine_generic
    (((projModel W).presheaf.map (homOfLE ((projModel W).basicOpen_le
      (r * (chartYSectionsRingEquiv W).symm (infChartTElem W)))).op).hom)
    (pointedIsoChartTransport e
      ((Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
        (infChartTElem W))).le.trans (witness_V_le_chartYPreimage e hr)) b'')
    (pointedIsoChartTransport e
      ((Scheme.basicOpen_mul (projModel W) r ((chartYSectionsRingEquiv W).symm
        (infChartTElem W))).le.trans (witness_V_le_chartYPreimage e hr))
      (AdjoinRoot.root (infChartCubic W')))
    ((((projModel W).presheaf.map (homOfLE ((Scheme.basicOpen_mul (projModel W) r
      ((chartYSectionsRingEquiv W).symm (infChartTElem W))).le.trans
      inf_le_left)).op).hom) ↑v)
    ((chartYSectionsRingEquiv W).symm (infChartTElem W)) r
    ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W)))
    ((chartYSectionsRingEquiv W).symm bΦ) u₀ v₀ n K j k hEQ hα hu₀' hv₀'
  obtain ⟨m, hm⟩ := res_eq_pull_generic
    (Proj.isAffineOpen_basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
      (mk_X_mem_quotientGrading_one W 1) one_pos)
    (r * (chartYSectionsRingEquiv W).symm (infChartTElem W)) hcomb
  have hBfold := equiv_fold_generic (chartYSectionsRingEquiv W) r
    ((chartYSectionsRingEquiv W).symm (infChartTElem W)) u₀ v₀
    ((chartYSectionsRingEquiv W).symm bΦ)
    ((chartYSectionsRingEquiv W).symm (AdjoinRoot.root (infChartCubic W)))
    m K (n * k) j n hm
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
    RingEquiv.apply_symm_apply] at hBfold
  -- bv ∉ P
  have hbvP : chartYSectionsRingEquiv W v₀ ∉ P := by
    intro hbv
    exact (hv₀P (Ideal.comap ((chartYSectionsRingEquiv W) :
        ↑Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))) →+*
        AdjoinRoot (infChartCubic W)) P)
      (Ideal.IsPrime.comap _)
      (fun hr' => hrP (Ideal.mem_comap.mp hr'))) (Ideal.mem_comap.mpr hbv)
  exact ⟨chartYSectionsRingEquiv W r, chartYSectionsRingEquiv W u₀,
    chartYSectionsRingEquiv W v₀, bΦ, m, K, j, k, hrP, hbvP, hbΦ0, hBfold⟩

/-- **The per-prime witness** (b2 endgame): given the transported criterion data on `W'`,
every maximal containing `t` admits a `c ∉ P` making the `W`-criterion element locally
integral. The proof restricts the transported overlap equation to the division-pack basic
open, replaces `σⁿ` by `unitⁿ·sⁿ`, clears `t`-denominators, and pulls back through the two
localizations. -/
lemma pointedIso_exists_witness {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (f' : W'.toAffine.CoordinateRing) (n : ℕ)
    (hf' : overlapMap W' f' * algebraMap (AdjoinRoot (infChartCubic W'))
        (Localization.Away (infChartTElem W'))
        (AdjoinRoot.root (infChartCubic W')) ^ n ∈
      Set.range (algebraMap (AdjoinRoot (infChartCubic W'))
        (Localization.Away (infChartTElem W'))))
    (P : Ideal (AdjoinRoot (infChartCubic W))) (hP : P.IsMaximal)
    (ht : infChartTElem W ∈ P) :
    ∃ c ∉ P, algebraMap (AdjoinRoot (infChartCubic W))
        (Localization.Away (infChartTElem W)) c *
      (overlapMap W (pointedIsoCoordEquiv e heπ hez f') *
        algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W))
          (AdjoinRoot.root (infChartCubic W)) ^ n) ∈
      Set.range (algebraMap (AdjoinRoot (infChartCubic W))
        (Localization.Away (infChartTElem W))) := by
  obtain ⟨g, bu, bv, bΦ, m, K, j, k, hgP, hbvP, hbΦ0, hBfold⟩ :=
    witness_B_data e heπ hez f' n hf' P ht
  refine ⟨g ^ (m + j) * bv ^ n, ?_, ?_⟩
  · intro hc
    rcases (inferInstance : P.IsPrime).mem_or_mem hc with h1 | h2
    · exact hgP ((inferInstance : P.IsPrime).mem_of_pow_mem _ h1)
    · exact hbvP ((inferInstance : P.IsPrime).mem_of_pow_mem _ h2)
  · refine ⟨g ^ (m + n * k) * bu, ?_⟩
    have hLoc0 := hom_fold_generic (algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W))) g (infChartTElem W) bu bv bΦ
      (AdjoinRoot.root (infChartCubic W)) m K (n * k) j n hBfold
    have hUt : IsUnit ((algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W))) (infChartTElem W)) :=
      IsLocalization.map_units (M := Submonoid.powers (infChartTElem W)) _
        ⟨infChartTElem W, 1, pow_one _⟩
    have hDfold : (algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W))) (g ^ (m + n * k) * bu) =
        ((algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W))) g) ^ (m + n * k) * (algebraMap (AdjoinRoot
        (infChartCubic W))
      (Localization.Away (infChartTElem W))) bu := by
      rw [map_mul, map_pow]
    have hcfold : (algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W))) (g ^ (m + j) * bv ^ n) =
        ((algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W))) g) ^ (m + j) * ((algebraMap (AdjoinRoot
        (infChartCubic W))
      (Localization.Away (infChartTElem W))) bv) ^ n := by
      rw [map_mul, map_pow, map_pow]
    refine hDfold.trans ?_
    have hgoal : ((algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W))) g) ^ (m + n * k) * (algebraMap (AdjoinRoot
        (infChartCubic W))
      (Localization.Away (infChartTElem W))) bu =
        ((algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W))) g) ^ (m + j) * ((algebraMap (AdjoinRoot
        (infChartCubic W))
      (Localization.Away (infChartTElem W))) bv) ^ n *
        (overlapMap W (pointedIsoCoordEquiv e heπ hez f') *
          (algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W))) (AdjoinRoot.root (infChartCubic W)) ^ n) := by
      refine ((hUt.pow (m + K)).mul_left_cancel ?_)
      linear_combination -(((algebraMap (AdjoinRoot (infChartCubic W))
        (Localization.Away (infChartTElem W))) (infChartTElem W)) ^ m *
        ((algebraMap (AdjoinRoot (infChartCubic W))
        (Localization.Away (infChartTElem W))) g) ^ (m + j) *
        ((algebraMap (AdjoinRoot (infChartCubic W))
        (Localization.Away (infChartTElem W))) bv) ^ n *
        ((algebraMap (AdjoinRoot (infChartCubic W))
        (Localization.Away (infChartTElem W)))
          (AdjoinRoot.root (infChartCubic W))) ^ n) * hbΦ0 + hLoc0
    refine hgoal.trans ?_
    rw [hcfold]

/-- **(ForMathlib-grade)** Sections round-trip along a split pair through `eqToHom`
transports: if `f ≫ g = 𝟙` then the two conjugated pullbacks compose to the identity. -/
private lemma app_app_eqToHom_of_comp_eq_id {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : f ≫ g = 𝟙 X) {U : X.Opens} {V : Y.Opens}
    (hgU : g ⁻¹ᵁ U = V) (hfV : f ⁻¹ᵁ V = U) (z : ↑Γ(X, U)) :
    ((X.presheaf.map (eqToHom hfV.symm).op).hom)
      ((f.app V).hom (((Y.presheaf.map (eqToHom hgU.symm).op).hom)
        ((g.app U).hom z))) = z := by
  have hUle : U ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U) := by
    rw [hgU, hfV]
  have hnat := congrArg (fun φ => CommRingCat.Hom.hom φ ((g.app U).hom z))
    (Scheme.Hom.naturality f ((eqToHom hgU.symm).op))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
  refine (congrArg ((X.presheaf.map (eqToHom hfV.symm).op).hom) hnat).trans ?_
  have hfuse := congrArg (fun φ => CommRingCat.Hom.hom φ
    ((f.app (g ⁻¹ᵁ U)).hom ((g.app U).hom z)))
    ((X.presheaf.map_comp ((TopologicalSpace.Opens.map f.base).map
      (eqToHom hgU.symm)).op (eqToHom hfV.symm).op).symm)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hfuse
  refine hfuse.trans ?_
  have halign := congrArg (fun ψ => (CommRingCat.Hom.hom (X.presheaf.map ψ))
    ((f.app (g ⁻¹ᵁ U)).hom ((g.app U).hom z)))
    (Subsingleton.elim (((TopologicalSpace.Opens.map f.base).map
      (eqToHom hgU.symm)).op ≫ (eqToHom hfV.symm).op) ((homOfLE hUle).op))
  refine halign.trans ?_
  refine (app_app_res_of_comp_eq_id f g hfg U hUle le_rfl z).trans ?_
  have hone : (homOfLE (le_rfl : U ≤ U)).op = 𝟙 (Opposite.op U) :=
    Subsingleton.elim _ _
  rw [hone, CategoryTheory.Functor.map_id]
  rfl

/-- The chart transport of the inverse composes to the identity. -/
private lemma pointedIsoΓ_symm_apply {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (z : ↑Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) :
    pointedIsoΓ e hez (pointedIsoΓ e.symm (pointedIso_hez_symm e hez) z) = z := by
  have hΓ1 : pointedIsoΓ e.symm (pointedIso_hez_symm e hez) z =
      (((projModel W').presheaf.map (eqToHom
        (pointedIso_preimage_zChart e.symm (pointedIso_hez_symm e hez)).symm).op).hom)
        ((e.symm.hom.app (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).hom z) := by
    refine (congrArg (fun ψ : _ →+* _ => ψ z)
      (Iso.commRingCatIsoToRingEquiv_toRingHom
        ((asIso (e.symm.hom.app (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))).trans
          ((projModel W').presheaf.mapIso (eqToIso
            (pointedIso_preimage_zChart e.symm
              (pointedIso_hez_symm e hez)).symm).op)))).trans ?_
    rw [Iso.trans_hom]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  have hΓ2 : ∀ w : ↑Γ(projModel W', Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))),
      pointedIsoΓ e hez w =
      (((projModel W).presheaf.map (eqToHom
        (pointedIso_preimage_zChart e hez).symm).op).hom)
        ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)))).hom w) := by
    intro w
    refine (congrArg (fun ψ : _ →+* _ => ψ w)
      (Iso.commRingCatIsoToRingEquiv_toRingHom
        ((asIso (e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))))).trans
          ((projModel W).presheaf.mapIso (eqToIso
            (pointedIso_preimage_zChart e hez).symm).op)))).trans ?_
    rw [Iso.trans_hom]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  rw [hΓ1, hΓ2]
  exact app_app_eqToHom_of_comp_eq_id e.hom e.inv e.hom_inv_id
    (pointedIso_preimage_zChart e.symm (pointedIso_hez_symm e hez))
    (pointedIso_preimage_zChart e hez) z

/-- The coordinate transport of the inverse composes to the identity. -/
lemma pointedIsoCoordEquiv_symm_apply {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (a : W.toAffine.CoordinateRing) :
    pointedIsoCoordEquiv e heπ hez (pointedIsoCoordEquiv e.symm
      (pointedIso_heπ_symm e heπ) (pointedIso_hez_symm e hez) a) = a := by
  apply (chartZSectionsRingEquiv W).symm.injective
  refine (pointedIsoCoordEquiv_sections e heπ hez _).trans ?_
  refine (congrArg (pointedIsoΓ e hez)
    (pointedIsoCoordEquiv_sections e.symm (pointedIso_heπ_symm e heπ)
      (pointedIso_hez_symm e hez) a)).trans ?_
  exact pointedIsoΓ_symm_apply e hez _

/-- **Forward inclusion of the filtration transport**: the induced coordinate isomorphism
maps the pole-order filtration into the pole-order filtration. -/
lemma pointedIsoCoordEquiv_filtration_le {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') (n : ℕ) :
    Submodule.map (pointedIsoCoordEquiv e heπ hez).toLinearEquiv.toLinearMap
        (poleOrderFiltration W' n) ≤ poleOrderFiltration W n := by
  rintro _ ⟨f', hf', rfl⟩
  have hf'loc := (mem_poleOrderFiltration_iff W' f' n).mp hf'
  have hgoal : pointedIsoCoordEquiv e heπ hez f' ∈ poleOrderFiltration W n := by
    rw [mem_poleOrderFiltration_iff]
    exact mem_range_algebraMap_of_forall_maximal W _ (fun P hP htP =>
      pointedIso_exists_witness e heπ hez f' n hf'loc P hP htP)
  exact hgoal

/-- **(T-W7.1b-b2 + the INTRINSIC-FILTRATION BRIDGE, coordinator §2)** The induced affine
ring isomorphism preserves the pole-order filtration. NOT free: the landed
`poleOrderFiltration` is a monomial span (coordinate-dependent); this leaf carries the
intrinsic (section-ideal/overlap-order) characterization inside its proof — it GATES all of
1b. DESIGN-DERIVED (audit A1 b2). -/
theorem pointedIsoCoordEquiv_filtration {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') (n : ℕ) :
    Submodule.map (pointedIsoCoordEquiv e heπ hez).toLinearEquiv.toLinearMap
        (poleOrderFiltration W' n) =
      poleOrderFiltration W n := by
  refine le_antisymm (pointedIsoCoordEquiv_filtration_le e heπ hez n) ?_
  intro x hx
  refine Submodule.mem_map.mpr
    ⟨pointedIsoCoordEquiv e.symm (pointedIso_heπ_symm e heπ)
      (pointedIso_hez_symm e hez) x, ?_, ?_⟩
  · exact pointedIsoCoordEquiv_filtration_le e.symm (pointedIso_heπ_symm e heπ)
      (pointedIso_hez_symm e hez) n (Submodule.mem_map_of_mem hx)
  · exact pointedIsoCoordEquiv_symm_apply e heπ hez x

/-! The four T-W7.1b comparison-theorem leaves (`pointedIsoCoordEquiv_coordX`,
`pointedIsoCoordEquiv_coordY`, `pointedIso_exists_variableChange`,
`projModelVCIso_injective`) are proved in `ModularCurves.EllipticCurve.Comparison`,
which sits above the `Comparison{Coefficients,Bridge,Injective}` files (those import this
one, so the leaves cannot be discharged here). Statements are relocated verbatim. -/

end ModularCurves
