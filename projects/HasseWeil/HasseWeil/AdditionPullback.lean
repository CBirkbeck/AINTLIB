/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.RingTheory.Algebraic.Integral
import HasseWeil.Basic
import HasseWeil.MulByIntPullback
import HasseWeil.OrdAtInftyBridge

/-!
# Addition-Law Pullback on Function Fields

Given an endomorphism `α : Isogeny E E`, we construct the pullback of `id + α`
(the map `P ↦ P + α(P)`) on the function field `K(E)`, using the Weierstrass
addition formulas from mathlib.

## Main results

* `pullback_equation`: The pullback of α preserves the Weierstrass equation.
* `addPullback_equation`: The addition formula outputs satisfy the equation.
* `addPullbackAlgHom`: The F-algebra homomorphism `K(E) →ₐ[F] K(E)` representing
  the pullback of `id + α`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.2.3c (explicit addition
  formulas) + III.3.6 (`+` is a morphism). Round-13 D-R13-A-04 fix: III.3.6 is
  the morphism property; the explicit formula is III.2.3c (referenced inside
  III.3.6's proof at book p. 64).
* Mathlib: `WeierstrassCurve.Affine.equation_add`
-/

open WeierstrassCurve Polynomial

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "R" => W.toAffine.CoordinateRing
local notation "KE" => W.toAffine.FunctionField

noncomputable instance instDecidableEqFunctionField : DecidableEq KE :=
  fun a b ↦ Classical.dec (a = b)

/-- The image of the generic point under a pullback satisfies the Weierstrass equation.
Reference: Silverman III.4. -/
theorem pullback_equation (α : Isogeny W.toAffine W.toAffine) :
    (W_KE W).toAffine.Equation (α.pullback (x_gen W)) (α.pullback (y_gen W)) := by
  have hmapped := Affine.Equation.map α.pullback.toRingHom (generic_equation W)
  rw [show (W_KE W).toAffine.map α.pullback.toRingHom = (W_KE W).toAffine by
    unfold W_KE
    rw [Affine.map, WeierstrassCurve.map_map]
    congr 1
    ext x
    exact α.pullback.commutes x] at hmapped
  exact hmapped

variable (α : Isogeny W.toAffine W.toAffine)

/-- The slope of the line through the generic point and its α-image. -/
noncomputable def addSlope : KE :=
  (W_KE W).toAffine.slope (x_gen W) (α.pullback (x_gen W))
    (y_gen W) (α.pullback (y_gen W))

/-- The x-coordinate of `P + α(P)`. -/
noncomputable def addPullback_x : KE :=
  (W_KE W).toAffine.addX (x_gen W) (α.pullback (x_gen W)) (addSlope W α)

/-- The y-coordinate of `P + α(P)`. -/
noncomputable def addPullback_y : KE :=
  (W_KE W).toAffine.addY (x_gen W) (α.pullback (x_gen W)) (y_gen W) (addSlope W α)

/-- The base ring hom `F[X] →+* K(E)` sending `X ↦ addPullback_x`. -/
noncomputable def addBaseHom : Polynomial F →+* KE :=
  Polynomial.eval₂RingHom (algebraMap F KE) (addPullback_x W α)

/-- The non-inverse hypothesis: the generic point and its α-image are not inverses. -/
abbrev AddNonInverse : Prop :=
  ¬(x_gen W = α.pullback (x_gen W) ∧
    y_gen W = (W_KE W).toAffine.negY (α.pullback (x_gen W)) (α.pullback (y_gen W)))

variable {W α}

/-- The addition formula outputs satisfy the Weierstrass equation.
    Reference: Mathlib `equation_add`. -/
theorem addPullback_equation (hxy : AddNonInverse W α) :
    (W_KE W).toAffine.Equation (addPullback_x W α) (addPullback_y W α) :=
  Affine.equation_add (generic_equation W) (pullback_equation W α) hxy

/-- The Weierstrass polynomial evaluates to zero at the addition coordinates.
    Bridges `Equation`/`evalEval` to the `eval₂` form needed by `AdjoinRoot.lift`. -/
theorem addPullback_poly_eval₂_zero (hxy : AddNonInverse W α) :
    W.toAffine.polynomial.eval₂ (addBaseHom W α) (addPullback_y W α) = 0 := by
  rw [addBaseHom, Polynomial.eval₂_eval₂RingHom_apply, ← Affine.map_polynomial]
  exact addPullback_equation hxy

/-- The ring homomorphism `CoordinateRing → K(E)` sending the coordinate generators
    to the addition formula outputs. Reference: Silverman III.3.6. -/
noncomputable def addCoordRingHom (hxy : AddNonInverse W α) : R →+* KE :=
  AdjoinRoot.lift (addBaseHom W α) (addPullback_y W α) (addPullback_poly_eval₂_zero hxy)

/-- The coordinate ring hom as an F-algebra hom `R →ₐ[F] K(E)`. -/
noncomputable def addCoordAlgHom (hxy : AddNonInverse W α) : R →ₐ[F] KE where
  toRingHom := addCoordRingHom hxy
  commutes' r := by
    change addCoordRingHom hxy (algebraMap (Polynomial F) R (algebraMap F (Polynomial F) r)) = _
    change AdjoinRoot.lift (addBaseHom W α) (addPullback_y W α) _
      (AdjoinRoot.mk _ (Polynomial.C (algebraMap F (Polynomial F) r))) = _
    rw [AdjoinRoot.lift_mk, Polynomial.eval₂_C]
    simp [addBaseHom, Polynomial.eval₂_C]

/-- The addition-pullback as an F-algebra homomorphism `K(E) →ₐ[F] K(E)`, the pullback of
`P ↦ P + α(P)` on the function field. The `hinj` hypothesis (injectivity of the coordinate
ring hom) follows from transcendence of `addPullback_x`. Reference: Silverman III.3.6. -/
noncomputable def addPullbackAlgHom (hxy : AddNonInverse W α)
    (hinj : Function.Injective (addCoordAlgHom hxy)) : KE →ₐ[F] KE :=
  IsFractionRing.liftAlgHom hinj

set_option linter.unusedSectionVars false in
/-- `addBaseHom` coincides with `Polynomial.aeval (addPullback_x W α)` as a ring hom. -/
theorem addBaseHom_eq_aeval :
    (addBaseHom W α : Polynomial F →+* KE) =
      (Polynomial.aeval (addPullback_x W α) : Polynomial F →ₐ[F] KE).toRingHom := by
  ext <;> simp [addBaseHom, Polynomial.aeval_def]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- An element of `FractionRing F[X]` that is algebraic over `F` must be in `F`.
This is the fact that the algebraic closure of `F` in a purely transcendental
extension `F(X)` is `F` itself. -/
theorem algebraic_in_fracRing_eq_const (z : FractionRing (Polynomial F))
    (hz : IsAlgebraic F z) :
    ∃ c : F, z = algebraMap F (FractionRing (Polynomial F)) c := by
  have h_int_poly : IsIntegral (Polynomial F) z := hz.isIntegral.tower_top
  rw [IsIntegrallyClosed.isIntegral_iff] at h_int_poly
  obtain ⟨p, hp⟩ := h_int_poly
  by_cases hdeg : p.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hp
    exact ⟨p.coeff 0, by
      rw [← hp, IsScalarTower.algebraMap_apply F (Polynomial F) (FractionRing (Polynomial F)),
        Polynomial.C_eq_algebraMap]⟩
  · exfalso
    have h_trans : Transcendental F (algebraMap (Polynomial F) (FractionRing (Polynomial F)) p) :=
      (transcendental_algebraMap_iff
        (IsFractionRing.injective (Polynomial F) (FractionRing (Polynomial F)))).mpr
        (Polynomial.transcendental p hdeg
          (mem_nonZeroDivisors_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr
            (Polynomial.ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero hdeg)))))
    rw [← hp] at hz
    exact h_trans hz

/-- If `addPullback_x W α` has a pole at infinity (`ord_∞ < 0`), it cannot equal a
constant from `F`. The pole hypothesis is supplied by the Frobenius pullback formula
`π·x = x^q` for `α = -frobeniusIsog W`, and by Silverman III.3.6 in general. -/
theorem addPullback_x_ne_const_of_pole (hxy : AddNonInverse W α) (c : F)
    (h_pole : (W_smooth W).ordAtInfty (addPullback_x W α) < 0)
    (hc : addPullback_x W α = algebraMap F KE c) : False := by
  by_cases hc_zero : c = 0
  · have h0 : addPullback_x W α = 0 := by rw [hc, hc_zero, map_zero]
    have h_top : (W_smooth W).ordAtInfty (addPullback_x W α) = ⊤ := by
      rw [h0]; exact (W_smooth W).ordAtInfty_zero
    rw [h_top] at h_pole
    exact absurd h_pole (not_lt_of_ge le_top)
  · have h_ord_c : (W_smooth W).ordAtInfty (addPullback_x W α) = 0 := by
      rw [hc]; exact ordAtInfty_algebraMap_F_nonzero W hc_zero
    rw [h_ord_c] at h_pole
    exact absurd h_pole (lt_irrefl _)

-- The four sub-lemmas below decompose the `px ∉ F(x_gen)` case of
-- `addPullback_x_quadratic_over_F`. This is pure field theory (Gauss's lemma plus
-- the algebraic closure of `F` in `F(X)`), not a Silverman result.

omit [DecidableEq F] [W.toAffine.IsElliptic] α in
private lemma minpoly_F_monic_irreducible_in_F_x_gen
    {α : KE} (h_alg : IsAlgebraic F α) :
    Irreducible
      ((minpoly F α).map (algebraMap F (FractionRing (Polynomial F)))) := by
  have h_int : IsIntegral F α := h_alg.isIntegral
  have h_monic : (minpoly F α).Monic := minpoly.monic h_int
  have h_irr : Irreducible (minpoly F α) := minpoly.irreducible h_int
  have h_monic_C : ((minpoly F α).map (algebraMap F (Polynomial F))).Monic :=
    h_monic.map _
  have h_step1 : Irreducible ((minpoly F α).map (algebraMap F (Polynomial F))) := by
    refine ⟨?_, ?_⟩
    · have hnd_pos : 0 < (minpoly F α).natDegree :=
        h_monic.natDegree_pos_of_not_isUnit h_irr.not_isUnit
      have hnd_eq : ((minpoly F α).map (algebraMap F (Polynomial F))).natDegree =
          (minpoly F α).natDegree :=
        h_monic.natDegree_map _
      exact Polynomial.not_isUnit_of_natDegree_pos _ (hnd_eq ▸ hnd_pos)
    · intros a b hfact
      let ev : Polynomial F →+* F := Polynomial.evalRingHom 0
      have h_comp_id : ev.comp (algebraMap F (Polynomial F)) = RingHom.id F := by
        ext c
        change (Polynomial.evalRingHom 0).comp (algebraMap F (Polynomial F)) c = c
        simp
      have h_back : a.map ev * b.map ev = minpoly F α := by
        have h1 : (a * b).map ev =
            (minpoly F α).map (ev.comp (algebraMap F (Polynomial F))) := by
          rw [← hfact, ← Polynomial.map_map]
        rw [Polynomial.map_mul] at h1
        rw [h1, h_comp_id, Polynomial.map_id]
      have h_lc_prod : a.leadingCoeff * b.leadingCoeff = 1 := by
        have h_mul_monic : (a * b).Monic := hfact.symm ▸ h_monic_C
        have h_lc_mul : (a * b).leadingCoeff = a.leadingCoeff * b.leadingCoeff :=
          Polynomial.leadingCoeff_mul a b
        rw [h_mul_monic] at h_lc_mul
        exact h_lc_mul.symm
      have h_lc_a_unit : IsUnit a.leadingCoeff :=
        IsUnit.of_mul_eq_one _ h_lc_prod
      have h_lc_b_unit : IsUnit b.leadingCoeff :=
        IsUnit.of_mul_eq_one_right _ h_lc_prod
      rcases h_irr.isUnit_or_isUnit h_back.symm with hu | hu
      · left
        exact Polynomial.isUnit_of_isUnit_leadingCoeff_of_isUnit_map ev h_lc_a_unit hu
      · right
        exact Polynomial.isUnit_of_isUnit_leadingCoeff_of_isUnit_map ev h_lc_b_unit hu
  have h_step2 :
      Irreducible
        (((minpoly F α).map (algebraMap F (Polynomial F))).map
          (algebraMap (Polynomial F) (FractionRing (Polynomial F)))) :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
      (K := FractionRing (Polynomial F)) h_monic_C).mp h_step1
  have h_tower :
      (algebraMap (Polynomial F) (FractionRing (Polynomial F))).comp
          (algebraMap F (Polynomial F)) =
        algebraMap F (FractionRing (Polynomial F)) := by
    ext c
    exact (IsScalarTower.algebraMap_apply F (Polynomial F) (FractionRing (Polynomial F)) c).symm
  rw [show algebraMap F (FractionRing (Polynomial F)) =
      (algebraMap (Polynomial F) (FractionRing (Polynomial F))).comp
        (algebraMap F (Polynomial F)) from h_tower.symm,
    ← Polynomial.map_map]
  exact h_step2

omit [DecidableEq F] [W.toAffine.IsElliptic] α in
private lemma minpoly_F_x_gen_eq_minpoly_F_map
    {α : KE} (h_alg : IsAlgebraic F α) :
    minpoly (FractionRing (Polynomial F)) α =
      (minpoly F α).map (algebraMap F (FractionRing (Polynomial F))) := by
  have h_int : IsIntegral F α := h_alg.isIntegral
  have h_monic : (minpoly F α).Monic := minpoly.monic h_int
  have h_irr : Irreducible
      ((minpoly F α).map (algebraMap F (FractionRing (Polynomial F)))) :=
    minpoly_F_monic_irreducible_in_F_x_gen h_alg
  have h_monic_map : ((minpoly F α).map (algebraMap F (FractionRing (Polynomial F)))).Monic :=
    h_monic.map _
  have h_aeval :
      Polynomial.aeval α
        ((minpoly F α).map (algebraMap F (FractionRing (Polynomial F)))) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    exact minpoly.aeval F α
  exact (minpoly.eq_of_irreducible_of_monic h_irr h_aeval h_monic_map).symm

omit [DecidableEq F] [W.toAffine.IsElliptic] α in
private lemma minpoly_F_x_gen_natDegree_le_two
    (α : KE) (hfin : Module.finrank (FractionRing (Polynomial F)) KE = 2) :
    (minpoly (FractionRing (Polynomial F)) α).natDegree ≤ 2 := by
  haveI : FiniteDimensional (FractionRing (Polynomial F)) KE :=
    Module.finite_of_finrank_pos (by rw [hfin]; exact (by decide : 0 < 2))
  have h_le := minpoly.natDegree_le (A := FractionRing (Polynomial F)) (B := KE) (x := α)
  rw [hfin] at h_le
  exact h_le

private lemma addPullback_x_quadratic_over_F_case_two
    (h_alg : IsAlgebraic F (addPullback_x W α))
    (hfin : Module.finrank (FractionRing (Polynomial F)) KE = 2)
    (hirr : ¬ ∃ r : FractionRing (Polynomial F),
      addPullback_x W α =
        algebraMap (FractionRing (Polynomial F)) KE r) :
    ∃ c₁ c₀ : F, (addPullback_x W α) ^ 2 -
      algebraMap F KE c₁ * addPullback_x W α + algebraMap F KE c₀ = 0 := by
  set px := addPullback_x W α with hpx_def
  have h_int_F : IsIntegral F px := h_alg.isIntegral
  have h_monic_F : (minpoly F px).Monic := minpoly.monic h_int_F
  have h_int_K : IsIntegral (FractionRing (Polynomial F)) px := (h_alg.tower_top _).isIntegral
  have h_le : (minpoly (FractionRing (Polynomial F)) px).natDegree ≤ 2 :=
    minpoly_F_x_gen_natDegree_le_two px hfin
  have hpx_not_range :
      px ∉ (algebraMap (FractionRing (Polynomial F)) KE).range := by
    rintro ⟨r, hr⟩
    exact hirr ⟨r, hr.symm⟩
  have h_ge : 2 ≤ (minpoly (FractionRing (Polynomial F)) px).natDegree :=
    (minpoly.two_le_natDegree_iff h_int_K).mpr hpx_not_range
  have h_eq_2_K : (minpoly (FractionRing (Polynomial F)) px).natDegree = 2 :=
    le_antisymm h_le h_ge
  have h_map_eq := minpoly_F_x_gen_eq_minpoly_F_map h_alg
  have h_eq_2_F : (minpoly F px).natDegree = 2 := by
    have h1 : ((minpoly F px).map
        (algebraMap F (FractionRing (Polynomial F)))).natDegree = 2 := by
      rw [← h_map_eq]; exact h_eq_2_K
    rwa [h_monic_F.natDegree_map] at h1
  set p := minpoly F px with hp_def
  refine ⟨-(p.coeff 1), p.coeff 0, ?_⟩
  have h_aeval : Polynomial.aeval px p = 0 := minpoly.aeval F px
  have h_lc_2 : p.coeff 2 = 1 := by
    rw [show 2 = p.natDegree from h_eq_2_F.symm]
    exact h_monic_F.coeff_natDegree
  rw [Polynomial.aeval_eq_sum_range, h_eq_2_F] at h_aeval
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, Algebra.smul_def, mul_one] at h_aeval
  rw [h_lc_2, map_one, one_mul] at h_aeval
  rw [map_neg, neg_mul, sub_neg_eq_add]
  linear_combination h_aeval

private lemma addPullback_x_quadratic_over_F (h_alg : IsAlgebraic F (addPullback_x W α))
    (hfin : Module.finrank (FractionRing (Polynomial F)) KE = 2) :
    ∃ c₁ c₀ : F, (addPullback_x W α) ^ 2 -
      algebraMap F KE c₁ * addPullback_x W α + algebraMap F KE c₀ = 0 := by
  set px := addPullback_x W α with hpx_def
  by_cases hmem : ∃ r : FractionRing (Polynomial F),
      px = algebraMap (FractionRing (Polynomial F)) KE r
  · obtain ⟨r, hr⟩ := hmem
    have hr_alg : IsAlgebraic F r := by
      by_contra h_trans
      exact absurd h_alg (hr ▸ (transcendental_algebraMap_iff
        (algebraMap (FractionRing (Polynomial F)) KE).injective).mpr h_trans)
    obtain ⟨c, hc⟩ := algebraic_in_fracRing_eq_const r hr_alg
    have hpx_c : px = algebraMap F KE c := by
      rw [hr, hc, ← IsScalarTower.algebraMap_apply F (FractionRing (Polynomial F)) KE]
    refine ⟨2 * c, c * c, ?_⟩
    rw [hpx_c]
    simp only [map_mul, map_ofNat]
    ring
  · exact addPullback_x_quadratic_over_F_case_two h_alg hfin hmem

private lemma minpoly_not_const_degree_two [NeZero (2 : F)] (c₁ c₀ : F)
    (heval : (addPullback_x W α) ^ 2 -
      algebraMap F KE c₁ * addPullback_x W α + algebraMap F KE c₀ = 0)
    (hirr : ¬ ∃ r : FractionRing (Polynomial F),
      addPullback_x W α = algebraMap (FractionRing (Polynomial F)) KE r) :
    False := by
  let C : HasseWeil.Curves.SmoothPlaneCurve F := W_smooth W
  let px : C.FunctionField := (addPullback_x W α : KE)
  obtain ⟨p, q, hpq⟩ := C.exists_decomp px
  have hq_ne : q ≠ 0 := by
    intro hq
    apply hirr
    refine ⟨p, ?_⟩
    have : px = algebraMap (FractionRing (Polynomial F)) C.FunctionField p := by
      rw [hpq, hq, zero_smul, add_zero, Algebra.smul_def, mul_one]
    exact this
  set α' : FractionRing (Polynomial F) :=
    algebraMap F (FractionRing (Polynomial F)) c₁ with hα'_def
  set γ' : FractionRing (Polynomial F) :=
    algebraMap F (FractionRing (Polynomial F)) c₀ with hγ'_def
  have h_α_img :
      algebraMap (FractionRing (Polynomial F)) C.FunctionField α' =
        algebraMap F C.FunctionField c₁ := by
    change algebraMap (FractionRing (Polynomial F)) C.FunctionField
        (algebraMap F (FractionRing (Polynomial F)) c₁) = _
    rw [← IsScalarTower.algebraMap_apply]
  have h_γ_img :
      algebraMap (FractionRing (Polynomial F)) C.FunctionField γ' =
        algebraMap F C.FunctionField c₀ := by
    change algebraMap (FractionRing (Polynomial F)) C.FunctionField
        (algebraMap F (FractionRing (Polynomial F)) c₀) = _
    rw [← IsScalarTower.algebraMap_apply]
  have hx_quad :
      (p • (1 : C.FunctionField) + q • C.coordYInFunctionField) ^ 2 -
        algebraMap (FractionRing (Polynomial F)) C.FunctionField α' *
          (p • (1 : C.FunctionField) + q • C.coordYInFunctionField) +
        algebraMap (FractionRing (Polynomial F)) C.FunctionField γ' = 0 := by
    rw [h_α_img, h_γ_img, ← hpq]
    exact heval
  obtain ⟨hE1, hE2⟩ := C.decomp_from_quadratic hx_quad
  have hE2' : α' = 2 * p - q * C.bFracPoly := by
    have h_factor : q * (2 * p - q * C.bFracPoly - α') = 0 := by
      linear_combination hE2
    rcases mul_eq_zero.mp h_factor with hq0 | h
    · exact absurd hq0 hq_ne
    · linear_combination -h
  have hγ_form :
      γ' = p ^ 2 - p * q * C.bFracPoly - q ^ 2 * C.cFracPoly := by
    linear_combination hE1 + p * hE2'
  have hDid :=
    C.polynomialDiscriminant_eq_trace_sq_sub_four_norm
      p q α' γ' hE2' hγ_form
  have h_αsq_4γ : α' ^ 2 - 4 * γ' =
      algebraMap (Polynomial F) (FractionRing (Polynomial F))
        (Polynomial.C (c₁ ^ 2 - 4 * c₀)) := by
    have h_alg_F_FX : ∀ x : F,
        algebraMap F (FractionRing (Polynomial F)) x =
        algebraMap (Polynomial F) (FractionRing (Polynomial F)) (Polynomial.C x) := by
      intro x
      rw [IsScalarTower.algebraMap_apply F (Polynomial F) (FractionRing (Polynomial F))]
      rfl
    change (algebraMap F (FractionRing (Polynomial F)) c₁) ^ 2 -
        4 * algebraMap F (FractionRing (Polynomial F)) c₀ = _
    rw [h_alg_F_FX c₁, h_alg_F_FX c₀, ← map_pow, ← Polynomial.C_pow,
      show (4 : FractionRing (Polynomial F)) =
        algebraMap (Polynomial F) (FractionRing (Polynomial F)) (4 : Polynomial F) from
      (map_ofNat _ 4).symm, ← map_mul, ← map_sub]
    congr 1
    change Polynomial.C (c₁ ^ 2) - (4 : Polynomial F) * Polynomial.C c₀ =
      Polynomial.C (c₁ ^ 2 - 4 * c₀)
    rw [show (4 : Polynomial F) = Polynomial.C (4 : F) from
      (map_ofNat Polynomial.C 4).symm, ← Polynomial.C_mul, ← Polynomial.C_sub]
  rw [h_αsq_4γ] at hDid
  obtain ⟨u, v, _hcop, hmk⟩ :=
    IsFractionRing.exists_reduced_fraction (A := Polynomial F)
      (K := FractionRing (Polynomial F)) q
  have hv_ne : (v : Polynomial F) ≠ 0 :=
    nonZeroDivisors.coe_ne_zero v
  have hq_v_eq_u : q * algebraMap (Polynomial F) (FractionRing (Polynomial F))
      ((v : Polynomial F)) =
      algebraMap (Polynomial F) (FractionRing (Polynomial F)) u := by
    rw [show q = IsLocalization.mk' (FractionRing (Polynomial F)) u v from hmk.symm,
      IsLocalization.mk'_spec]
  have h_polyEq : (Polynomial.C (c₁ ^ 2 - 4 * c₀)) * (v : Polynomial F) ^ 2 =
      u ^ 2 * C.polynomialDiscriminant := by
    apply FaithfulSMul.algebraMap_injective (Polynomial F)
      (FractionRing (Polynomial F))
    rw [map_mul, map_mul, map_pow, map_pow]
    have h1 :
        algebraMap (Polynomial F) (FractionRing (Polynomial F))
            (Polynomial.C (c₁ ^ 2 - 4 * c₀)) *
          (algebraMap (Polynomial F) (FractionRing (Polynomial F))
              ((v : Polynomial F))) ^ 2 =
        (q * algebraMap (Polynomial F) (FractionRing (Polynomial F))
            ((v : Polynomial F))) ^ 2 *
          algebraMap (Polynomial F) (FractionRing (Polynomial F))
            C.polynomialDiscriminant := by
      rw [hDid]; ring
    rw [h1, hq_v_eq_u]
  have hav_ne : algebraMap (Polynomial F) (FractionRing (Polynomial F))
      ((v : Polynomial F)) ≠ 0 :=
    fun h ↦ hv_ne (FaithfulSMul.algebraMap_injective _ _
      (h.trans (map_zero _).symm))
  have hu_ne : u ≠ 0 := by
    intro hu0
    rw [hu0, map_zero] at hq_v_eq_u
    rcases mul_eq_zero.mp hq_v_eq_u with h | h
    · exact hq_ne h
    · exact hav_ne h
  by_cases hΔ : c₁ ^ 2 - 4 * c₀ = 0
  · rw [hΔ, Polynomial.C_0, zero_mul] at h_polyEq
    rcases mul_eq_zero.mp h_polyEq.symm with h | h
    · exact hu_ne (pow_eq_zero_iff (n := 2) (by decide : 2 ≠ 0) |>.mp h)
    · exact C.polynomialDiscriminant_ne_zero h
  · have hC_ne : Polynomial.C (c₁ ^ 2 - 4 * c₀) ≠ 0 :=
      Polynomial.C_ne_zero.mpr hΔ
    have hD_natDeg : C.polynomialDiscriminant.natDegree = 3 :=
      C.polynomialDiscriminant_natDegree
    have hLHS_natDeg :
        (Polynomial.C (c₁ ^ 2 - 4 * c₀) * (v : Polynomial F) ^ 2).natDegree =
          2 * (v : Polynomial F).natDegree := by
      rw [Polynomial.natDegree_mul hC_ne (pow_ne_zero 2 hv_ne),
        Polynomial.natDegree_C, Polynomial.natDegree_pow]
      lia
    have hRHS_natDeg :
        (u ^ 2 * C.polynomialDiscriminant).natDegree =
          2 * u.natDegree + 3 := by
      rw [Polynomial.natDegree_mul (pow_ne_zero 2 hu_ne)
          C.polynomialDiscriminant_ne_zero,
        Polynomial.natDegree_pow, hD_natDeg]
    have hdeg_eq : 2 * (v : Polynomial F).natDegree = 2 * u.natDegree + 3 := by
      have := congrArg Polynomial.natDegree h_polyEq
      rw [hLHS_natDeg, hRHS_natDeg] at this
      exact this
    lia

/-- Image of a power-basis element `p • 1 + q • Y` under `addCoordRingHom`: it splits as
`addBaseHom p + addBaseHom q * addPullback_y`, since the lift sends the basis generators
to the addition-formula outputs. -/
private theorem addCoordRingHom_smulBasis (hxy : AddNonInverse W α) (p q : Polynomial F) :
    addCoordRingHom hxy
        (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X) =
      addBaseHom W α p + addBaseHom W α q * addPullback_y W α := by
  simp only [addCoordRingHom, map_add]
  congr 1
  · change AdjoinRoot.lift _ _ _ (p • 1) = _
    rw [Algebra.smul_def, mul_one]
    exact AdjoinRoot.lift_of _
  · change AdjoinRoot.lift _ _ _ (q • AdjoinRoot.root _) = _
    rw [Algebra.smul_def, map_mul]
    congr 1
    · exact AdjoinRoot.lift_of _
    · exact AdjoinRoot.lift_root _

/-- The norm of the power-basis element `p • 1 + q • Y`, pushed into the coordinate ring,
factors as the element times its conjugate `C p + C q * (-Y - C (a₁X + a₃))`. -/
private theorem algebraMap_norm_smulBasis (p q : Polynomial F) :
    algebraMap (Polynomial F) R
        (Algebra.norm (Polynomial F)
          (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X)) =
      (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X) *
        Affine.CoordinateRing.mk W.toAffine
          (Polynomial.C p + Polynomial.C q *
            (-Polynomial.X - Polynomial.C
              (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃))) := by
  change AdjoinRoot.of _ _ = _
  rw [Affine.CoordinateRing.coe_norm_smul_basis, map_mul]
  congr 1
  rw [map_add, map_mul]
  simp [Algebra.smul_def]

/-- The norm of the power-basis element `p • 1 + q • Y` is nonzero whenever `q ≠ 0`:
its degree is `max (2·deg p) (2·deg q + 3)`, and the second term is finite (`≠ ⊥`). -/
private theorem norm_smulBasis_ne_zero_of_snd_ne_zero (p : Polynomial F) {q : Polynomial F}
    (hq : q ≠ 0) :
    Algebra.norm (Polynomial F)
        (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X) ≠ 0 := by
  intro h_norm_eq
  have h_deg := Affine.CoordinateRing.degree_norm_smul_basis (W' := W.toAffine) p q
  rw [h_norm_eq, Polynomial.degree_zero] at h_deg
  have hq_deg : q.degree ≠ ⊥ := Polynomial.degree_ne_bot.mpr hq
  have hqd : 2 • q.degree + 3 ≠ (⊥ : WithBot ℕ) := by
    intro h
    apply hq_deg
    cases hd : q.degree with
    | bot => rfl
    | coe n =>
        rw [hd] at h
        exact absurd h (by
          change ¬ (2 • (↑n : WithBot ℕ) + 3 = ⊥)
          simp [WithBot.mul_ne_bot])
  exact absurd (h_deg ▸ le_max_right _ _ : 2 • q.degree + 3 ≤ ⊥)
    (not_le.mpr (WithBot.bot_lt_iff_ne_bot.mpr hqd))

/-- `addCoordAlgHom hxy` is injective, given injectivity of the base hom `addBaseHom W α`.
This witness-parametric form is consumed by the axiom-clean negFrobenius case
(`addCoordAlgHom_injective_negFrobenius`, in `Frobenius.lean`). -/
theorem addCoordAlgHom_injective_of_baseHom_inj (hxy : AddNonInverse W α)
    (hxinj : Function.Injective (addBaseHom W α)) :
    Function.Injective (addCoordAlgHom hxy) := by
  change Function.Injective (addCoordRingHom hxy)
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨p, q, hpq⟩ := Affine.CoordinateRing.exists_smul_basis_eq r
  -- Decompose `r = p • 1 + q • Y` and compute its image.
  have h_image : addCoordRingHom hxy r =
      addBaseHom W α p + addBaseHom W α q * addPullback_y W α := by
    rw [← hpq]; exact addCoordRingHom_smulBasis hxy p q
  rw [h_image] at hr
  -- It suffices that both coordinates vanish.
  suffices hp : p = 0 ∧ q = 0 by
    obtain ⟨hp1, hp2⟩ := hp
    rw [← hpq, hp1, hp2]
    change (0 : Polynomial F) • (1 : R) + (0 : Polynomial F) •
      Affine.CoordinateRing.mk W.toAffine Polynomial.X = 0
    rw [Algebra.smul_def, Algebra.smul_def, map_zero, zero_mul, zero_mul, add_zero]
  by_cases hq : q = 0
  · -- `q = 0`: vanishing of the image is exactly injectivity of `addBaseHom` on `p`.
    rw [hq, map_zero, zero_mul, add_zero] at hr
    exact ⟨hxinj (hr.trans (map_zero _).symm), hq⟩
  · -- `q ≠ 0`: the norm of `r` is nonzero, yet it maps to `0`, contradicting injectivity.
    refine absurd ?_ (norm_smulBasis_ne_zero_of_snd_ne_zero (W := W) p hq)
    -- The base hom sends the norm to `0` (the hom kills `r`, and the norm factors through `r`).
    have hr_zero :
        addCoordRingHom hxy (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X)
          = 0 := (addCoordRingHom_smulBasis hxy p q).trans hr
    refine hxinj (Eq.trans ?_ (map_zero _).symm)
    have h_alg : addCoordRingHom hxy
        (algebraMap (Polynomial F) R (Algebra.norm (Polynomial F)
          (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X))) =
        addBaseHom W α (Algebra.norm (Polynomial F)
          (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X)) := by
      change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ _) = _
      exact AdjoinRoot.lift_of _
    rw [← h_alg, algebraMap_norm_smulBasis, map_mul, hr_zero, zero_mul]

-- The `_pair` variants below take two isogenies and compute `α₁(P) + α₂(P)` on the
-- generic point, generalising the single-isogeny `id + α` maps (recovered at
-- `α₁ = Isogeny.id W`). The QF degree formula `deg(r·π - s·id) = qr² - tr·rs + s²`
-- needs the addition of two arbitrary endomorphisms.

/-- The slope of the line through `(α₁(P), α₂(P))` images of the generic
point in `K(E)`. -/
noncomputable def addSlopePair (α₁ α₂ : Isogeny W.toAffine W.toAffine) : KE :=
  (W_KE W).toAffine.slope (α₁.pullback (x_gen W)) (α₂.pullback (x_gen W))
    (α₁.pullback (y_gen W)) (α₂.pullback (y_gen W))

/-- The x-coordinate of `α₁(P) + α₂(P)` for the generic point P. -/
noncomputable def addPullback_x_pair (α₁ α₂ : Isogeny W.toAffine W.toAffine) : KE :=
  (W_KE W).toAffine.addX (α₁.pullback (x_gen W)) (α₂.pullback (x_gen W))
    (addSlopePair α₁ α₂)

/-- The y-coordinate of `α₁(P) + α₂(P)` for the generic point P. -/
noncomputable def addPullback_y_pair (α₁ α₂ : Isogeny W.toAffine W.toAffine) : KE :=
  (W_KE W).toAffine.addY (α₁.pullback (x_gen W)) (α₂.pullback (x_gen W))
    (α₁.pullback (y_gen W)) (addSlopePair α₁ α₂)

/-- The non-inverse hypothesis for the (α₁, α₂) pair: the two image points
are not inverses of each other on the curve. -/
abbrev AddNonInversePair (α₁ α₂ : Isogeny W.toAffine W.toAffine) : Prop :=
  ¬(α₁.pullback (x_gen W) = α₂.pullback (x_gen W) ∧
    α₁.pullback (y_gen W) =
      (W_KE W).toAffine.negY (α₂.pullback (x_gen W)) (α₂.pullback (y_gen W)))

/-- The pair addition outputs satisfy the curve equation. Direct from
Mathlib's `Affine.equation_add` applied to the two pullback equations. -/
theorem addPullback_pair_equation {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (hxy : AddNonInversePair α₁ α₂) :
    (W_KE W).toAffine.Equation
      (addPullback_x_pair α₁ α₂) (addPullback_y_pair α₁ α₂) :=
  Affine.equation_add (pullback_equation W α₁) (pullback_equation W α₂) hxy

/-- The base ring hom `F[X] →+* K(E)` sending `X ↦ addPullback_x_pair α₁ α₂`. -/
noncomputable def addBaseHomPair (α₁ α₂ : Isogeny W.toAffine W.toAffine) :
    Polynomial F →+* KE :=
  Polynomial.eval₂RingHom (algebraMap F KE) (addPullback_x_pair α₁ α₂)

/-- The Weierstrass polynomial evaluates to zero at the pair addition coordinates. -/
theorem addPullback_pair_poly_eval₂_zero {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (hxy : AddNonInversePair α₁ α₂) :
    W.toAffine.polynomial.eval₂
      (addBaseHomPair α₁ α₂) (addPullback_y_pair α₁ α₂) = 0 := by
  rw [addBaseHomPair, Polynomial.eval₂_eval₂RingHom_apply, ← Affine.map_polynomial]
  exact addPullback_pair_equation hxy

/-- The coordinate ring homomorphism `R →+* K(E)` for the pair addition. -/
noncomputable def addCoordRingHomPair {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (hxy : AddNonInversePair α₁ α₂) : R →+* KE :=
  AdjoinRoot.lift (addBaseHomPair α₁ α₂) (addPullback_y_pair α₁ α₂)
    (addPullback_pair_poly_eval₂_zero hxy)

/-- The coordinate ring hom as an F-algebra hom for the pair addition. -/
noncomputable def addCoordAlgHomPair {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (hxy : AddNonInversePair α₁ α₂) : R →ₐ[F] KE where
  toRingHom := addCoordRingHomPair hxy
  commutes' r := by
    change addCoordRingHomPair hxy
      (algebraMap (Polynomial F) R (algebraMap F (Polynomial F) r)) = _
    change AdjoinRoot.lift (addBaseHomPair α₁ α₂) (addPullback_y_pair α₁ α₂) _
      (AdjoinRoot.mk _ (Polynomial.C (algebraMap F (Polynomial F) r))) = _
    rw [AdjoinRoot.lift_mk, Polynomial.eval₂_C]
    simp [addBaseHomPair, Polynomial.eval₂_C]

/-- The pair addition pullback as an F-algebra homomorphism `K(E) →ₐ[F] K(E)`.
This is the pullback of `P ↦ α₁(P) + α₂(P)` on the function field, witness-
parametric on injectivity of `addCoordAlgHomPair`. -/
noncomputable def addPullbackAlgHomPair {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (hxy : AddNonInversePair α₁ α₂) (hinj : Function.Injective (addCoordAlgHomPair hxy)) :
    KE →ₐ[F] KE :=
  IsFractionRing.liftAlgHom hinj

/-- Generic `α₁ + α₂` isogeny: combines the algebra-hom pullback (witness-
parametric on `AddNonInversePair` + injectivity) with the additive sum on
rational points. The pullback represents `P ↦ α₁(P) + α₂(P)` on `K(E)`. -/
noncomputable def addIsog {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (hxy : AddNonInversePair α₁ α₂) (hinj : Function.Injective (addCoordAlgHomPair hxy)) :
    Isogeny W.toAffine W.toAffine where
  pullback := addPullbackAlgHomPair hxy hinj
  toAddMonoidHom := α₁.toAddMonoidHom + α₂.toAddMonoidHom

@[simp] theorem addIsog_pullback {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (hxy : AddNonInversePair α₁ α₂) (hinj : Function.Injective (addCoordAlgHomPair hxy)) :
    (addIsog hxy hinj).pullback = addPullbackAlgHomPair hxy hinj := rfl

@[simp] theorem addIsog_toAddMonoidHom {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (hxy : AddNonInversePair α₁ α₂) (hinj : Function.Injective (addCoordAlgHomPair hxy)) :
    (addIsog hxy hinj).toAddMonoidHom =
      α₁.toAddMonoidHom + α₂.toAddMonoidHom := rfl

-- The single-isogeny maps are the `α₁ = Isogeny.id` specialisation of the `_pair`
-- versions; since `Isogeny.id.pullback = AlgHom.id` is `rfl`, each reduction is `rfl`.

/-- `AddNonInversePair (Isogeny.id W) α` is definitionally `AddNonInverse W α`. -/
theorem AddNonInversePair_id (α : Isogeny W.toAffine W.toAffine) :
    AddNonInversePair (Isogeny.id W.toAffine) α ↔ AddNonInverse W α :=
  Iff.rfl

/-- `addSlopePair (id, α) = addSlope α`, definitionally. -/
@[simp] theorem addSlopePair_id (α : Isogeny W.toAffine W.toAffine) :
    addSlopePair (Isogeny.id W.toAffine) α = addSlope W α := rfl

/-- `addPullback_x_pair (id, α) = addPullback_x α`, definitionally. -/
@[simp] theorem addPullback_x_pair_id (α : Isogeny W.toAffine W.toAffine) :
    addPullback_x_pair (Isogeny.id W.toAffine) α = addPullback_x W α := rfl

/-- `addPullback_y_pair (id, α) = addPullback_y α`, definitionally. -/
@[simp] theorem addPullback_y_pair_id (α : Isogeny W.toAffine W.toAffine) :
    addPullback_y_pair (Isogeny.id W.toAffine) α = addPullback_y W α := rfl

/-- `addBaseHomPair (id, α) = addBaseHom α`, definitionally. -/
@[simp] theorem addBaseHomPair_id (α : Isogeny W.toAffine W.toAffine) :
    addBaseHomPair (Isogeny.id W.toAffine) α = addBaseHom W α := rfl

/-- `addCoordRingHomPair (id, α) hxy = addCoordRingHom hxy`, definitionally. -/
@[simp] theorem addCoordRingHomPair_id (α : Isogeny W.toAffine W.toAffine)
    (hxy : AddNonInverse W α) :
    addCoordRingHomPair (α₁ := Isogeny.id W.toAffine) (α₂ := α) hxy =
      addCoordRingHom hxy := rfl

/-- `addCoordAlgHomPair (id, α) hxy = addCoordAlgHom hxy`, definitionally. -/
@[simp] theorem addCoordAlgHomPair_id (α : Isogeny W.toAffine W.toAffine)
    (hxy : AddNonInverse W α) :
    addCoordAlgHomPair (α₁ := Isogeny.id W.toAffine) (α₂ := α) hxy =
      addCoordAlgHom hxy := rfl

/-- `addPullbackAlgHomPair (id, α) hxy hinj = addPullbackAlgHom hxy hinj`,
definitionally — the pair version reduces to the single-α version when `α₁ = Isogeny.id`. -/
@[simp] theorem addPullbackAlgHomPair_id (α : Isogeny W.toAffine W.toAffine)
    (hxy : AddNonInverse W α) (hinj : Function.Injective (addCoordAlgHom hxy)) :
    addPullbackAlgHomPair (α₁ := Isogeny.id W.toAffine) (α₂ := α) hxy hinj =
      addPullbackAlgHom hxy hinj := rfl

/-- Build `AddNonInversePair α₁ α₂` from an x-coordinate mismatch alone:
if `α₁.pullback x_gen ≠ α₂.pullback x_gen`, the pair is non-inverse.
The y-coordinate clause becomes vacuous since the conjunction's first
conjunct already fails. -/
theorem AddNonInversePair_of_x_ne {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (h_x : α₁.pullback (x_gen W) ≠ α₂.pullback (x_gen W)) :
    AddNonInversePair α₁ α₂ :=
  fun ⟨h, _⟩ ↦ h_x h

/-- Build `AddNonInversePair α₁ α₂` from a y-coordinate mismatch (negY-form):
if `α₁.pullback y_gen ≠ negY (α₂.pullback x_gen) (α₂.pullback y_gen)`, the
pair is non-inverse. -/
theorem AddNonInversePair_of_y_ne {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (h_y : α₁.pullback (y_gen W) ≠
      (W_KE W).toAffine.negY (α₂.pullback (x_gen W)) (α₂.pullback (y_gen W))) :
    AddNonInversePair α₁ α₂ :=
  fun ⟨_, h⟩ ↦ h_y h

set_option linter.unusedSectionVars false in
/-- `addBaseHomPair` coincides with `Polynomial.aeval (addPullback_x_pair α₁ α₂)`
as a ring hom. -/
theorem addBaseHomPair_eq_aeval (α₁ α₂ : Isogeny W.toAffine W.toAffine) :
    (addBaseHomPair α₁ α₂ : Polynomial F →+* KE) =
      (Polynomial.aeval (addPullback_x_pair α₁ α₂) :
        Polynomial F →ₐ[F] KE).toRingHom := by
  ext <;> simp [addBaseHomPair, Polynomial.aeval_def]

/-- Image of a coordinate-ring element `p • 1 + q • x` under `addCoordRingHomPair`,
in terms of the base hom and the pulled-back `y`-coordinate. -/
private theorem addCoordRingHomPair_smul_basis_eq
    {α₁ α₂ : Isogeny W.toAffine W.toAffine} (hxy : AddNonInversePair α₁ α₂) (p q : Polynomial F) :
    addCoordRingHomPair hxy
        (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X) =
      addBaseHomPair α₁ α₂ p + addBaseHomPair α₁ α₂ q * addPullback_y_pair α₁ α₂ := by
  simp only [addCoordRingHomPair, map_add]
  congr 1
  · change AdjoinRoot.lift _ _ _ (p • 1) = _
    rw [Algebra.smul_def, mul_one]
    exact AdjoinRoot.lift_of _
  · change AdjoinRoot.lift _ _ _ (q • AdjoinRoot.root _) = _
    rw [Algebra.smul_def, map_mul]
    congr 1
    · exact AdjoinRoot.lift_of _
    · exact AdjoinRoot.lift_root _

/-- If a coordinate-ring element `p • 1 + q • x` with `q ≠ 0` lies in the kernel of
`addCoordRingHomPair`, the norm/degree count is contradictory: the factored norm forces
`Algebra.norm r' = 0` while `degree (norm r') = 2•q.degree + 3 ≠ ⊥`. -/
private theorem addCoordRingHomPair_smul_basis_q_ne_zero
    {α₁ α₂ : Isogeny W.toAffine W.toAffine} (hxy : AddNonInversePair α₁ α₂)
    (hxinj : Function.Injective (addBaseHomPair α₁ α₂)) {p q : Polynomial F} (hq : q ≠ 0)
    (h0 : addCoordRingHomPair hxy
      (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X) = 0) : False := by
  set r' := p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X with hr'_def
  have h_alg : ∀ f : Polynomial F,
      addCoordRingHomPair hxy (algebraMap (Polynomial F) R f) =
        addBaseHomPair α₁ α₂ f := by
    intro f
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ f) = _
    exact AdjoinRoot.lift_of _
  set conj_r := Affine.CoordinateRing.mk W.toAffine
    (Polynomial.C p + Polynomial.C q *
      (-Polynomial.X - Polynomial.C
        (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃))) with hconj_def
  have h_factor : algebraMap (Polynomial F) R (Algebra.norm (Polynomial F) r') =
      r' * conj_r := by
    rw [hr'_def, hconj_def]
    change AdjoinRoot.of _ _ = _
    rw [Affine.CoordinateRing.coe_norm_smul_basis, map_mul]
    congr 1
    rw [map_add, map_mul]
    simp [Algebra.smul_def]
  have hr'_zero : addCoordRingHomPair hxy r' = 0 := h0
  have h_norm_zero : addBaseHomPair α₁ α₂ (Algebra.norm (Polynomial F) r') = 0 := by
    rw [← h_alg, h_factor, map_mul, hr'_zero, zero_mul]
  have h_norm_eq : Algebra.norm (Polynomial F) r' = 0 :=
    hxinj (h_norm_zero.trans (map_zero _).symm)
  rw [hr'_def] at h_norm_eq
  have h_deg := Affine.CoordinateRing.degree_norm_smul_basis (W' := W.toAffine) p q
  rw [h_norm_eq, Polynomial.degree_zero] at h_deg
  have hq_deg : q.degree ≠ ⊥ := Polynomial.degree_ne_bot.mpr hq
  have : 2 • q.degree + 3 ≠ (⊥ : WithBot ℕ) := by
    intro h
    apply hq_deg
    cases hd : q.degree with
    | bot => rfl
    | coe n =>
        rw [hd] at h
        exact absurd h (by
          change ¬ (2 • (↑n : WithBot ℕ) + 3 = ⊥)
          simp [WithBot.mul_ne_bot])
  exact absurd (h_deg ▸ le_max_right _ _ : 2 • q.degree + 3 ≤ ⊥)
    (not_le.mpr (WithBot.bot_lt_iff_ne_bot.mpr this))

/-- `addCoordAlgHomPair hxy` is injective, given injectivity of the base hom
`addBaseHomPair α₁ α₂`. The pair analogue of `addCoordAlgHom_injective_of_baseHom_inj`. -/
theorem addCoordAlgHomPair_injective_of_baseHom_inj {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (hxy : AddNonInversePair α₁ α₂)
    (hxinj : Function.Injective (addBaseHomPair α₁ α₂)) :
    Function.Injective (addCoordAlgHomPair hxy) := by
  change Function.Injective (addCoordRingHomPair hxy)
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨p, q, hpq⟩ := Affine.CoordinateRing.exists_smul_basis_eq r
  have h_image : addCoordRingHomPair hxy r =
      addBaseHomPair α₁ α₂ p +
        addBaseHomPair α₁ α₂ q * addPullback_y_pair α₁ α₂ := by
    rw [← hpq]; exact addCoordRingHomPair_smul_basis_eq hxy p q
  rw [h_image] at hr
  suffices hp : p = 0 ∧ q = 0 by
    obtain ⟨hp1, hp2⟩ := hp
    rw [← hpq, hp1, hp2]
    change (0 : Polynomial F) • (1 : R) + (0 : Polynomial F) •
      Affine.CoordinateRing.mk W.toAffine Polynomial.X = 0
    rw [Algebra.smul_def, Algebra.smul_def, map_zero, zero_mul, zero_mul, add_zero]
  by_cases hq : q = 0
  · rw [hq, map_zero, zero_mul, add_zero] at hr
    exact ⟨hxinj (hr.trans (map_zero _).symm), hq⟩
  · exact (addCoordRingHomPair_smul_basis_q_ne_zero hxy hxinj hq
      (hpq.symm ▸ h_image.trans hr)).elim

-- The σ-invariance lemmas below express that the curve-negation involution
-- `σ = (mulByInt W (-1)).pullback` fixes `addPullback_x_pair α₁ α₂` when both
-- pullbacks satisfy the σ-action symmetry. This is the pullback-level manifestation
-- of `α.comp [-1] = [-1].comp α` (centrality of `[-1]`).

/-- The pair slope formula when `α₁(x_gen) ≠ α₂(x_gen)` (the non-doubling
case): `addSlopePair α₁ α₂ = (α₁(y) - α₂(y)) / (α₁(x) - α₂(x))`. -/
theorem addSlopePair_eq_of_x_ne {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (h_x_ne : α₁.pullback (x_gen W) ≠ α₂.pullback (x_gen W)) :
    addSlopePair α₁ α₂ =
      (α₁.pullback (y_gen W) - α₂.pullback (y_gen W)) /
      (α₁.pullback (x_gen W) - α₂.pullback (x_gen W)) := by
  unfold addSlopePair
  exact Affine.slope_of_X_ne h_x_ne

/-- **σ-action sum identity for the pair slope**: if both pullbacks satisfy
the σ-action symmetry on `x_gen` and `y_gen` and `α₁(x) ≠ α₂(x)`, then
`σ(L_pair) + L_pair = -a₁`. The pair generalisation of
`addSlope_negFrobenius_sigma_sum_eq_neg_a1`. -/
theorem addSlopePair_sigma_sum_eq_neg_a1 {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (h_x_ne : α₁.pullback (x_gen W) ≠ α₂.pullback (x_gen W))
    (h_α₁x : (mulByInt W.toAffine (-1)).pullback (α₁.pullback (x_gen W)) =
              α₁.pullback (x_gen W))
    (h_α₂x : (mulByInt W.toAffine (-1)).pullback (α₂.pullback (x_gen W)) =
              α₂.pullback (x_gen W))
    (h_α₁y : (mulByInt W.toAffine (-1)).pullback (α₁.pullback (y_gen W)) =
              -α₁.pullback (y_gen W) -
              algebraMap F KE W.toAffine.a₁ * α₁.pullback (x_gen W) -
              algebraMap F KE W.toAffine.a₃)
    (h_α₂y : (mulByInt W.toAffine (-1)).pullback (α₂.pullback (y_gen W)) =
              -α₂.pullback (y_gen W) -
              algebraMap F KE W.toAffine.a₁ * α₂.pullback (x_gen W) -
              algebraMap F KE W.toAffine.a₃) :
    (mulByInt W.toAffine (-1)).pullback (addSlopePair α₁ α₂) +
      addSlopePair α₁ α₂ =
      -algebraMap F KE W.toAffine.a₁ := by
  rw [addSlopePair_eq_of_x_ne h_x_ne, map_div₀, map_sub, map_sub,
      h_α₁x, h_α₂x, h_α₁y, h_α₂y]
  have hd : α₁.pullback (x_gen W) - α₂.pullback (x_gen W) ≠ 0 :=
    sub_ne_zero.mpr h_x_ne
  field_simp
  ring

/-- **Generic σ-invariance of pair `addPullback_x`**: if both pullbacks
satisfy the σ-action symmetry on `x_gen` and `y_gen` and `α₁(x) ≠ α₂(x)`,
then σ fixes `addPullback_x_pair α₁ α₂`. The pair generalisation of
`addPullback_x_negFrobenius_sigma_invariant`. -/
theorem addPullback_x_pair_sigma_invariant {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (h_x_ne : α₁.pullback (x_gen W) ≠ α₂.pullback (x_gen W))
    (h_α₁x : (mulByInt W.toAffine (-1)).pullback (α₁.pullback (x_gen W)) =
              α₁.pullback (x_gen W))
    (h_α₂x : (mulByInt W.toAffine (-1)).pullback (α₂.pullback (x_gen W)) =
              α₂.pullback (x_gen W))
    (h_α₁y : (mulByInt W.toAffine (-1)).pullback (α₁.pullback (y_gen W)) =
              -α₁.pullback (y_gen W) -
              algebraMap F KE W.toAffine.a₁ * α₁.pullback (x_gen W) -
              algebraMap F KE W.toAffine.a₃)
    (h_α₂y : (mulByInt W.toAffine (-1)).pullback (α₂.pullback (y_gen W)) =
              -α₂.pullback (y_gen W) -
              algebraMap F KE W.toAffine.a₁ * α₂.pullback (x_gen W) -
              algebraMap F KE W.toAffine.a₃) :
    (mulByInt W.toAffine (-1)).pullback (addPullback_x_pair α₁ α₂) =
      addPullback_x_pair α₁ α₂ := by
  unfold addPullback_x_pair WeierstrassCurve.Affine.addX
  have h_a1 : (W_KE W).toAffine.a₁ = algebraMap F KE W.toAffine.a₁ := rfl
  have h_a2 : (W_KE W).toAffine.a₂ = algebraMap F KE W.toAffine.a₂ := rfl
  rw [h_a1, h_a2]
  simp only [map_sub, map_add, map_mul, map_pow,
    AlgHom.commutes (mulByInt W.toAffine (-1)).pullback,
    h_α₁x, h_α₂x]
  have h := addSlopePair_sigma_sum_eq_neg_a1 h_x_ne h_α₁x h_α₂x h_α₁y h_α₂y
  linear_combination
    ((mulByInt W.toAffine (-1)).pullback (addSlopePair α₁ α₂) -
      addSlopePair α₁ α₂) * h

end HasseWeil
