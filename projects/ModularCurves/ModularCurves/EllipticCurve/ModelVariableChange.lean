import ModularCurves.EllipticCurve.PoleFiltration
import ModularCurves.ForMathlib.AffinePointVariableChange

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

/-- **(T-W7.0h-i)** The isomorphism of projective Weierstrass models induced by a variable
change `C = (u, r, s, t)`: the projectivisation of the affine coordinate change
`(x, y) ↦ (u²x + r, u³y + su²x + t)` (mathlib's `VariableChange` convention), an isomorphism
`projModel (C • W) ≅ projModel W`. Source: Silverman III.3.1(b) (projective form); the graded
ring map mirrors `baseChangeGradedHom`. -/
noncomputable def projModelVCIso (C : VariableChange R) (W : WeierstrassCurve R) :
    projModel (C • W) ≅ projModel W :=
  sorry

/-- **(T-W7.0h-i, π-compatibility)** `projModelVCIso` is a morphism over `Spec R`. -/
theorem projModelVCIso_π (C : VariableChange R) (W : WeierstrassCurve R) :
    (projModelVCIso C W).hom ≫ projModelπ W = projModelπ (C • W) := by
  sorry

/-- **(T-W7.0h-i, pointedness)** `projModelVCIso` carries the point at infinity to the point
at infinity ( `[0:1:0]` is fixed by the projectivised coordinate change). -/
theorem projModelVCIso_zero (C : VariableChange R) (W : WeierstrassCurve R) :
    projModelZero (C • W) ≫ (projModelVCIso C W).hom = projModelZero W := by
  sorry

/-- **(T-W7.0h-i, cocycle)** The model isomorphisms compose according to the
`VariableChange` group law (contravariantly on the acted curve). Source: the affine cocycle
`vcX_comp`/`vcY_comp` (`ForMathlib/AffinePointVariableChange`, DONE), projectivised. -/
theorem projModelVCIso_mul (C C' : VariableChange R) (W : WeierstrassCurve R) :
    (projModelVCIso (C * C') W).hom =
      (eqToHom (by rw [mul_smul])) ≫ (projModelVCIso C (C' • W)).hom ≫
        (projModelVCIso C' W).hom := by
  sorry

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
  sorry

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
