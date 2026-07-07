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
  have Cl1 : ((MvPolynomial.C (↑C.u : R)) ^ 6 : MvPolynomial (Fin 3) R) * MvPolynomial.C ((C • W).a₁)
      = (MvPolynomial.C (↑C.u : R)) ^ 5 * (MvPolynomial.C W.a₁ + 2 * MvPolynomial.C C.s) := by
    have inner : (↑C.u : R) ^ 6 * (C • W).a₁ = (↑C.u : R) ^ 5 * (W.a₁ + 2 * C.s) := by
      rw [variableChange_a₁, ← pow_one (↑C.u⁻¹ : R), ← mul_assoc, huinv 6 1 (by norm_num)]
    rw [← map_pow, ← map_mul, inner]; simp only [map_mul, map_pow, map_add, map_ofNat]
  have Cl2 : ((MvPolynomial.C (↑C.u : R)) ^ 6 : MvPolynomial (Fin 3) R) * MvPolynomial.C ((C • W).a₂)
      = (MvPolynomial.C (↑C.u : R)) ^ 4 * (MvPolynomial.C W.a₂ - MvPolynomial.C C.s * MvPolynomial.C W.a₁
        + 3 * MvPolynomial.C C.r - MvPolynomial.C C.s ^ 2) := by
    have inner : (↑C.u : R) ^ 6 * (C • W).a₂
        = (↑C.u : R) ^ 4 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) := by
      rw [variableChange_a₂, ← mul_assoc, huinv 6 2 (by norm_num)]
    rw [← map_pow, ← map_mul, inner]; simp only [map_mul, map_pow, map_add, map_sub, map_ofNat]
  have Cl3 : ((MvPolynomial.C (↑C.u : R)) ^ 6 : MvPolynomial (Fin 3) R) * MvPolynomial.C ((C • W).a₃)
      = (MvPolynomial.C (↑C.u : R)) ^ 3 * (MvPolynomial.C W.a₃ + MvPolynomial.C C.r * MvPolynomial.C W.a₁
        + 2 * MvPolynomial.C C.t) := by
    have inner : (↑C.u : R) ^ 6 * (C • W).a₃ = (↑C.u : R) ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) := by
      rw [variableChange_a₃, ← mul_assoc, huinv 6 3 (by norm_num)]
    rw [← map_pow, ← map_mul, inner]; simp only [map_mul, map_pow, map_add, map_ofNat]
  have Cl4 : ((MvPolynomial.C (↑C.u : R)) ^ 6 : MvPolynomial (Fin 3) R) * MvPolynomial.C ((C • W).a₄)
      = (MvPolynomial.C (↑C.u : R)) ^ 2 * (MvPolynomial.C W.a₄ - MvPolynomial.C C.s * MvPolynomial.C W.a₃
        + 2 * MvPolynomial.C C.r * MvPolynomial.C W.a₂
        - (MvPolynomial.C C.t + MvPolynomial.C C.r * MvPolynomial.C C.s) * MvPolynomial.C W.a₁
        + 3 * MvPolynomial.C C.r ^ 2 - 2 * MvPolynomial.C C.s * MvPolynomial.C C.t) := by
    have inner : (↑C.u : R) ^ 6 * (C • W).a₄
        = (↑C.u : R) ^ 2 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁
          + 3 * C.r ^ 2 - 2 * C.s * C.t) := by
      rw [variableChange_a₄, ← mul_assoc, huinv 6 4 (by norm_num)]
    rw [← map_pow, ← map_mul, inner]; simp only [map_mul, map_pow, map_add, map_sub, map_ofNat]
  have Cl6 : ((MvPolynomial.C (↑C.u : R)) ^ 6 : MvPolynomial (Fin 3) R) * MvPolynomial.C ((C • W).a₆)
      = MvPolynomial.C W.a₆ + MvPolynomial.C C.r * MvPolynomial.C W.a₄
        + MvPolynomial.C C.r ^ 2 * MvPolynomial.C W.a₂ + MvPolynomial.C C.r ^ 3
        - MvPolynomial.C C.t * MvPolynomial.C W.a₃ - MvPolynomial.C C.t ^ 2
        - MvPolynomial.C C.r * MvPolynomial.C C.t * MvPolynomial.C W.a₁ := by
    have inner : (↑C.u : R) ^ 6 * (C • W).a₆
        = W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2 - C.r * C.t * W.a₁ := by
      rw [variableChange_a₆, ← mul_assoc, huinv 6 6 (by norm_num), pow_zero, one_mul]
    rw [← map_pow, ← map_mul, inner]; simp only [map_mul, map_pow, map_add, map_sub, map_ofNat]
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
    simp only [vcMvSubst, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val, MvPolynomial.smul_eq_C_mul]
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
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, map_add, map_sub, map_mul, map_pow,
      map_neg, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.smul_eq_C_mul,
      MvPolynomial.algebraMap_eq]
    linear_combination MvPolynomial.X (0 : Fin 3) * hupow 2
  · show MvPolynomial.aeval (vcMvSubst C) (vcMvSubst C⁻¹ (1 : Fin 3)) = MvPolynomial.X (1 : Fin 3)
    simp only [vcMvSubst, VariableChange.inv_def, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, map_add, map_sub, map_mul, map_pow,
      map_neg, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.smul_eq_C_mul,
      MvPolynomial.algebraMap_eq]
    linear_combination MvPolynomial.X (1 : Fin 3) * hupow 3
  · show MvPolynomial.aeval (vcMvSubst C) (vcMvSubst C⁻¹ (2 : Fin 3)) = MvPolynomial.X (2 : Fin 3)
    simp only [vcMvSubst, VariableChange.inv_def, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, MvPolynomial.aeval_X]

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

/-- **(T-W7.0h-i, pointedness)** `projModelVCIso` carries the point at infinity to the point
at infinity ( `[0:1:0]` is fixed by the projectivised coordinate change). -/
theorem projModelVCIso_zero (C : VariableChange R) (W : WeierstrassCurve R) :
    projModelZero (C • W) ≫ (projModelVCIso C W).hom = projModelZero W := by
  sorry

/-- **Base-change naturality of the substitution**: applying the coefficient map `f` to the
variable-change substitution for `C` gives the substitution for the base-changed `C.map f`. -/
lemma vcMvSubst_map {R' : Type u} [CommRing R'] (f : R →+* R') (C : VariableChange R) (i : Fin 3) :
    MvPolynomial.map f (vcMvSubst C i) = vcMvSubst (C.map f) i := by
  fin_cases i
  · show MvPolynomial.map f (vcMvSubst C (0 : Fin 3)) = vcMvSubst (C.map f) (0 : Fin 3)
    simp only [vcMvSubst, VariableChange.map_u, VariableChange.map_r, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
      MvPolynomial.smul_eq_C_mul, map_add, map_mul, map_pow, MvPolynomial.map_C,
      MvPolynomial.map_X, Units.coe_map, MonoidHom.coe_coe]
  · show MvPolynomial.map f (vcMvSubst C (1 : Fin 3)) = vcMvSubst (C.map f) (1 : Fin 3)
    simp only [vcMvSubst, VariableChange.map_u, VariableChange.map_r, VariableChange.map_s,
      VariableChange.map_t, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val, MvPolynomial.smul_eq_C_mul, map_add, map_mul, map_pow,
      MvPolynomial.map_C, MvPolynomial.map_X, Units.coe_map, MonoidHom.coe_coe]
  · show MvPolynomial.map f (vcMvSubst C (2 : Fin 3)) = vcMvSubst (C.map f) (2 : Fin 3)
    simp only [vcMvSubst, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val, MvPolynomial.map_X]

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

/-- **Substitution cocycle**: the group product of variable changes composes the substitutions. -/
lemma vcMvSubst_mul (C C' : VariableChange R) (i : Fin 3) :
    vcMvSubst (C * C') i = MvPolynomial.aeval (vcMvSubst C) (vcMvSubst C' i) := by
  fin_cases i
  · show vcMvSubst (C * C') (0 : Fin 3) = MvPolynomial.aeval (vcMvSubst C) (vcMvSubst C' (0 : Fin 3))
    simp only [vcMvSubst, VariableChange.mul_def, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, MvPolynomial.smul_eq_C_mul, map_add,
      map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
      Units.val_mul]
    ring
  · show vcMvSubst (C * C') (1 : Fin 3) = MvPolynomial.aeval (vcMvSubst C) (vcMvSubst C' (1 : Fin 3))
    simp only [vcMvSubst, VariableChange.mul_def, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, MvPolynomial.smul_eq_C_mul, map_add,
      map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
      Units.val_mul]
    ring
  · show vcMvSubst (C * C') (2 : Fin 3) = MvPolynomial.aeval (vcMvSubst C) (vcMvSubst C' (2 : Fin 3))
    simp only [vcMvSubst, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
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

/-- **(T-W7.1b-b1, coordinator §2)** A pointed isomorphism of projective models restricts to
the affine parts (it preserves the complement of the zero section) and hence induces an
`R`-algebra isomorphism of the affine coordinate rings. DESIGN-DERIVED (audit A1 b1; no
verbatim source — KM is image-only). -/
noncomputable def pointedIsoCoordEquiv {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    W'.toAffine.CoordinateRing ≃ₐ[R] W.toAffine.CoordinateRing :=
  sorry

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
  sorry

/-- **(T-W7.1b-b3x, coordinator §2)** Coefficient extraction, `x`-side: `Φ(x') = αx + β`
with `α` a unit (from `F₂`-preservation + the freeness of `{1, x}`). Shared-witness
`∃`-bundle (α, β and the unitness travel together into b3y/the relation-matching). -/
theorem pointedIsoCoordEquiv_coordX {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    ∃ α β : R, IsUnit α ∧
      pointedIsoCoordEquiv e heπ hez (coordX W') =
        algebraMap R _ α * coordX W + algebraMap R _ β := by
  sorry

/-- **(T-W7.1b-b3y, coordinator §2)** Coefficient extraction, `y`-side:
`Φ(y') = γy + δx + ε` with `γ` a unit (from `F₃`-preservation). The five variable-change
coefficient equations + `α³ = γ²` (yielding `u := γ/α`) are the body of the main theorem
below, consuming b3x/b3y. -/
theorem pointedIsoCoordEquiv_coordY {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    ∃ γ δ ε : R, IsUnit γ ∧
      pointedIsoCoordEquiv e heπ hez (coordY W') =
        algebraMap R _ γ * coordY W + algebraMap R _ δ * coordX W + algebraMap R _ ε := by
  sorry

/-- **(T-W7.1b, main — the comparison theorem)** Every isomorphism of projective Weierstrass
models over a ring `R` that respects the structure morphisms and the points at infinity is
induced by a variable change: there is a `C : VariableChange R` with `C • W = W'`, and `e` is
the transport of `projModelVCIso` along that equality. The proof route is the pole filtration:
a pointed iso preserves the affine part (`projModel_hom_ext_of_affine` territory) and the
filtration `F_n`, whose low-degree freeness forces `Φ(x') = αx + β`, `Φ(y') = γy + δx + ε`
with `α, γ` units; matching the two Weierstrass relations forces `α³ = γ²`, and
`u := γ/α` yields `C`. Source: audit A1; KM §2.2-style; prior-B2 fix-option (3). -/
theorem pointedIso_exists_variableChange (W W' : WeierstrassCurve R)
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    ∃ C : VariableChange R, ∃ hW : C • W' = W,
      e.hom = eqToHom (by rw [← hW]) ≫ (projModelVCIso C W').hom := by
  sorry

/-- **(T-W7.1b, uniqueness — faithfulness of the model action)** The variable change inducing
a given pointed model isomorphism is unique: distinct variable changes with the same action on
`W` induce distinct model isomorphisms. (Uniqueness is NOT "C with C • W' = W is unique" —
automorphisms exist for special `W`; it is the pinning by the induced isomorphism.) Source:
audit A1 (b5); the filtration argument reads `(u, r, s, t)` off `Φ(x'), Φ(y')`. -/
theorem projModelVCIso_injective (C₁ C₂ : VariableChange R) (W : WeierstrassCurve R)
    (hW : C₁ • W = C₂ • W)
    (h : (projModelVCIso C₁ W).hom = eqToHom (by rw [hW]) ≫ (projModelVCIso C₂ W).hom) :
    C₁ = C₂ := by
  sorry

end ModularCurves
