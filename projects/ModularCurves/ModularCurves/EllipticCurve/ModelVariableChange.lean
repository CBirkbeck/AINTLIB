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
    simp only [allScaleVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val, MvPolynomial.smul_eq_C_mul]
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
    Matrix.head_cons, Matrix.cons_val, MvPolynomial.smul_eq_C_mul]
  ring

lemma allScaleVec_comp_inv (μ : Rˣ) (i : Fin 3) :
    MvPolynomial.aeval (allScaleVec μ) (allScaleVec μ⁻¹ i) = MvPolynomial.X i := by
  fin_cases i
  · show MvPolynomial.aeval (allScaleVec μ) (allScaleVec μ⁻¹ (0 : Fin 3)) = MvPolynomial.X (0 : Fin 3)
    simp [allScaleVec, smul_smul, Units.inv_mul]
  · show MvPolynomial.aeval (allScaleVec μ) (allScaleVec μ⁻¹ (1 : Fin 3)) = MvPolynomial.X (1 : Fin 3)
    simp [allScaleVec, smul_smul, Units.inv_mul]
  · show MvPolynomial.aeval (allScaleVec μ) (allScaleVec μ⁻¹ (2 : Fin 3)) = MvPolynomial.X (2 : Fin 3)
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
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) (e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) le_rfl ≫
      (projModelZero W).appLE (e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) ⊤
        (zero_le_preimage_pointedPreimage e hez) =
    (projModelZero W').appLE (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) ⊤
        (le_of_eq (projModelZero_preimage_yChart W').symm) :=
  appLE_appLE_of_comp_eq (projModelZero W) e.hom (projModelZero W') hez (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))
    (zero_le_preimage_pointedPreimage e hez)
    (le_of_eq (projModelZero_preimage_yChart W').symm)

/-- The `le_rfl`-`appLE` of a morphism agrees with `app`, elementwise. -/
private lemma appLE_le_rfl_apply {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (w' : Γ(projModel W', Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) :
    ((e.hom.appLE (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) (e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))) le_rfl).hom) w' =
    ((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom) w' := by
  have h2 : (homOfLE (le_rfl : e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))) ≤ e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))))).op =
      𝟙 (Opposite.op (e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))))) := Subsingleton.elim _ _
  have h3 := congrArg (fun ψ => (CommRingCat.Hom.hom
    ((projModel W).presheaf.map ψ)) (((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom) w')) h2
  refine h3.trans ?_
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (((e.hom.app (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1)))).hom) w'))
    ((projModel W).presheaf.map_id (Opposite.op (e.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W'))
        ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 1))))))

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
