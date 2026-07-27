/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Isogeny.TwoCurve.FixedField
import HasseWeil.Isogeny.TwoCurve.GroupHom
import HasseWeil.Foundation.Curves.Fiber.LocalizedDictionary
import HasseWeil.Foundation.Curves.Divisor.PushforwardDivisor
import HasseWeil.Foundation.Curves.NormConormIntegralClosure

/-!
# The CoordHom-free norm–conorm: `PlaceRestrictionPreservesPrincipal` (Silverman II.3.6)

This file discharges the single remaining wall of char-0 isogeny symmetry,
`PlaceRestrictionPreservesPrincipal φ` (`TwoCurveGroupHom.lean`): for a separable two-curve
isogeny `φ : Isogeny W₁ W₂` over `[IsAlgClosed F]`, the CoordHom-free place-restriction
pushforward carries principal projective divisors to principal projective divisors — Silverman
II.3.6/II.3.7 (norm–conorm), *without* an affine coordinate-ring comorphism `F[E₂] → F[E₁]`
(which a genuine isogeny lacks, since `φ^*(x_gen₂)` has poles on the affine kernel).

## The integral-closure route (Silverman's actual II.3.6)

The CoordHom-gated `EC.Isogeny.pushforward_preserves_principal` (`PushforwardDivisor.lean`) routes
through `Ideal.relNorm C₂.CoordinateRing (C₁.maximalIdealAt R)`, i.e. the affine coordinate-ring
extension `F[E₂] → F[E₁]` — unavailable here.  Instead we use the **field norm** `N_φ f =
Algebra.norm_{K(E₁)/φ*K(E₂)} f ∈ K(E₂)` and the per-place identity (Silverman II.3.6, every
ramification `e = 1` by III.4.10c over `[IsAlgClosed F]`)

  `ord_Q(N_φ f) = Σ_{P : φ(P) = Q} ord_P(f)`,

which says exactly `div(N_φ f) = placeRestrictionPushforward φ (div f)`. Since
`N_φ f ∈ K(E₂)`, the pushforward of a principal divisor is principal.

The fibre structure (places of `E₁` over a place of `E₂`) is supplied CoordHom-free by the
integral closure `B := integralClosure (localized φ*F[E₂]) K(E₁)` of `HasseWeil/Curves/
LocalizedDictionary.lean`, whose maximal ideals ↔ ALL places of `E₁` (including the
affine-kernel poles of `φ^*x_gen₂`).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.6, II.3.6, II.3.7, III.4.10(c).
-/

open WeierstrassCurve

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.Curves

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : WeierstrassCurve F} [W₁.toAffine.IsElliptic] [W₂.toAffine.IsElliptic]
variable [IsAlgClosed F]

/-- **The conorm** `N_φ : K(E₁) →* K(E₂)`, the field norm of the pullback algebra
structure. -/
noncomputable def conorm (φ : HasseWeil.Isogeny W₁ W₂) :
    W₁.toAffine.FunctionField →* W₂.toAffine.FunctionField :=
  @Algebra.norm W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _ φ.toAlgebra

omit [IsAlgClosed F] in
@[simp] theorem conorm_mul (φ : HasseWeil.Isogeny W₁ W₂) (f g : W₁.toAffine.FunctionField) :
    conorm φ (f * g) = conorm φ f * conorm φ g :=
  (conorm φ).map_mul f g

omit [IsAlgClosed F] in
@[simp] theorem conorm_one (φ : HasseWeil.Isogeny W₁ W₂) :
    conorm φ (1 : W₁.toAffine.FunctionField) = 1 :=
  (conorm φ).map_one

omit [IsAlgClosed F] in
/-- The conorm of a nonzero function is nonzero (a monoid hom sends a unit to a unit). -/
theorem conorm_ne_zero (φ : HasseWeil.Isogeny W₁ W₂) {f : W₁.toAffine.FunctionField}
    (hf : f ≠ 0) : conorm φ f ≠ 0 :=
  (IsUnit.map (conorm φ) (isUnit_iff_ne_zero.mpr hf)).ne_zero

omit [IsAlgClosed F] in
/-- The pullback of a two-curve isogeny makes `K(E₁)` finite-dimensional over `K(E₂)`. -/
theorem isogeny_finiteDimensional_twoCurve (φ : HasseWeil.Isogeny W₁ W₂) :
    @FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra.toModule :=
  HasseWeil.Isogeny.finiteDimensional_toAlgebra_twoCurve φ

private theorem placeRestrictionPushforward_projectiveDivisorOf_eq_sub
    (φ : HasseWeil.Isogeny W₁ W₂) {f av au : W₁.toAffine.FunctionField}
    (hf : f ≠ 0) (hav : av ≠ 0) (hfav : f * av = au) :
    placeRestrictionPushforward φ ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf f) =
      placeRestrictionPushforward φ
          ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf au) -
        placeRestrictionPushforward φ
          ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf av) := by
  rw [← hfav, (⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf_mul hf hav, map_add]
  abel

omit [IsAlgClosed F] in
private theorem projectiveDivisorOf_conorm_eq_sub
    (φ : HasseWeil.Isogeny W₁ W₂) {f av au : W₁.toAffine.FunctionField}
    (hf : conorm φ f ≠ 0) (hav : conorm φ av ≠ 0) (hfav : f * av = au) :
    (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ f) =
      (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ au) -
        (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ av) := by
  rw [← hfav, conorm_mul, (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf_mul hf hav]
  abel

/-- The norm-conorm identity for all functions follows from its coordinate-ring case. -/
theorem placeRestrictionPushforward_projectiveDivisorOf_of_algebraMap
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra.toModule)
    (key : ∀ w : (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing, w ≠ 0 →
      placeRestrictionPushforward φ ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
          (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w)) =
        (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ
          (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
            (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w)))
    (f : W₁.toAffine.FunctionField) :
    placeRestrictionPushforward φ ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf f) =
      (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ f) := by
  classical
  letI : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField := φ.toAlgebra
  haveI := hfin
  by_cases hf : f = 0
  · subst hf
    haveI : Module.Free W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
      Module.Free.of_divisionRing _ _
    rw [(⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf_zero, map_zero,
      show conorm φ (0 : W₁.toAffine.FunctionField) = 0 from Algebra.norm_zero,
      (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf_zero]
  · obtain ⟨u, v, hv_mem, hf_eq⟩ :=
      IsFractionRing.div_surjective (A := (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing) f
    have hv_ne : v ≠ 0 := nonZeroDivisors.ne_zero hv_mem
    set au := algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
      (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField u with hau
    set av := algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
      (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField v with hav
    have hav_ne : av ≠ 0 := by
      rw [hav]
      intro h
      exact hv_ne ((IsFractionRing.injective (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
        (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField) (h.trans (map_zero _).symm))
    have hu_ne : u ≠ 0 := by
      intro hu
      apply hf
      rw [← hf_eq, hau, hu, map_zero, zero_div]
    have hf_av : f * av = au := by rw [← hf_eq, div_mul_cancel₀ _ hav_ne]
    rw [placeRestrictionPushforward_projectiveDivisorOf_eq_sub φ hf hav_ne hf_av,
      projectiveDivisorOf_conorm_eq_sub φ (conorm_ne_zero φ hf) (conorm_ne_zero φ hav_ne) hf_av,
      key u hu_ne, key v hv_ne]

/-- The affine coefficient of a place-restriction pushforward is the corresponding fiber sum. -/
theorem placeRestrictionPushforward_apply_affine
    (φ : HasseWeil.Isogeny W₁ W₂) (D : ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F))
    (Q : (⟨W₂⟩ : SmoothPlaneCurve F).SmoothPoint) :
    placeRestrictionPushforward φ D (ProjectiveSmoothPoint.affine Q) =
      ∑ x ∈ D.support.filter
        (fun x => placeRestrictionPlaceImage φ x = ProjectiveSmoothPoint.affine Q), D x := by
  classical
  rw [placeRestrictionPushforward_apply, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finsupp.single_apply]

omit [DecidableEq F] [IsAlgClosed F] in
private theorem pointValuationSubring_le_valuationSubring_of_center
    (C : SmoothPlaneCurve F) [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing]
    (Q : C.SmoothPoint)
    (w : Valuation C.FunctionField (WithZero (Multiplicative ℤ)))
    (hle : ∀ b : C.CoordinateRing, w (algebraMap C.CoordinateRing C.FunctionField b) ≤ 1)
    (hcenter : ∀ b : C.CoordinateRing,
      w (algebraMap C.CoordinateRing C.FunctionField b) < 1 ↔ b ∈ C.maximalIdealAt Q) :
    (C.pointValuation Q).valuationSubring ≤ w.valuationSubring := by
  classical
  intro f hf
  obtain ⟨x, hx_eq⟩ := (SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one f).mpr
    ((Valuation.mem_valuationSubring_iff _ f).mp hf)
  obtain ⟨a, s, hxas⟩ := IsLocalization.exists_mk'_eq (C.maximalIdealAt Q).primeCompl x
  set sv : C.CoordinateRing := (s : C.CoordinateRing) with hsv
  have hs_notin : sv ∉ C.maximalIdealAt Q := Ideal.mem_primeCompl_iff.mp s.2
  have hs_ne : sv ≠ 0 := fun h => hs_notin (h ▸ Submodule.zero_mem _)
  have hs_map_ne : algebraMap C.CoordinateRing C.FunctionField sv ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective C.CoordinateRing C.FunctionField)).mpr hs_ne
  have hf_eq : f = algebraMap C.CoordinateRing C.FunctionField a /
      algebraMap C.CoordinateRing C.FunctionField sv := by
    rw [eq_div_iff hs_map_ne, ← hx_eq, ← hxas,
      IsScalarTower.algebraMap_apply C.CoordinateRing (C.localRingAt Q) C.FunctionField sv,
      IsScalarTower.algebraMap_apply C.CoordinateRing (C.localRingAt Q) C.FunctionField a,
      ← map_mul]
    congr 1
    exact IsLocalization.mk'_spec (C.localRingAt Q) a s
  have hws : w (algebraMap C.CoordinateRing C.FunctionField sv) = 1 := by
    refine le_antisymm (hle sv) ?_
    by_contra hlt
    rw [not_le] at hlt
    exact hs_notin ((hcenter sv).mp hlt)
  refine (Valuation.mem_valuationSubring_iff _ f).mpr ?_
  rw [hf_eq, map_div₀ w, hws, div_one]
  exact hle a

omit [DecidableEq F] [IsAlgClosed F] in
/-- A surjective valuation on `K(C)` with affine center `m_Q` is `pointValuation Q`. -/
theorem eq_pointValuation_of_center
    (C : SmoothPlaneCurve F) [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing]
    (Q : C.SmoothPoint)
    (w : Valuation C.FunctionField (WithZero (Multiplicative ℤ)))
    (hwsurj : Function.Surjective w)
    (hle : ∀ b : C.CoordinateRing, w (algebraMap C.CoordinateRing C.FunctionField b) ≤ 1)
    (hcenter : ∀ b : C.CoordinateRing,
      w (algebraMap C.CoordinateRing C.FunctionField b) < 1 ↔ b ∈ C.maximalIdealAt Q) :
    w = C.pointValuation Q := by
  classical
  haveI : IsDiscreteValuationRing w.valuationSubring :=
    valuationSubring_isDVR_of_surjective_withZeroInt _ hwsurj
  have hpvsurj : Function.Surjective (C.pointValuation Q) :=
    (IsDiscreteValuationRing.maximalIdeal (C.localRingAt Q)).valuation_surjective C.FunctionField
  set A : ValuationSubring C.FunctionField := w.valuationSubring with hA
  set Bv : ValuationSubring C.FunctionField := (C.pointValuation Q).valuationSubring with hBv
  haveI : IsDiscreteValuationRing Bv :=
    valuationSubring_isDVR_of_surjective_withZeroInt _ hpvsurj
  have hBA : Bv ≤ A := pointValuationSubring_le_valuationSubring_of_center C Q w hle hcenter
  have hAtop : A ≠ ⊤ := valuationSubring_ne_top_of_surjective_withZeroInt w hwsurj
  have hEq : Bv = A := rankOne_valuationSubring_le_eq_of_ne_top Bv A hBA hAtop
  have h_isEquiv : w.IsEquiv (C.pointValuation Q) := by
    rw [Valuation.isEquiv_iff_valuationSubring]
    rw [hA, hBv] at hEq
    exact hEq.symm
  exact Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _ hwsurj hpvsurj h_isEquiv

omit [IsAlgClosed F] in
private theorem pullback_algebraMap_const_le_one
    (φ : HasseWeil.Isogeny W₁ W₂) (P : (W_smooth W₁).SmoothPoint) (d : F) :
    (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
      (φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField (AdjoinRoot.mk W₂.toAffine.polynomial
          (Polynomial.C (Polynomial.C d))))) ≤ 1 := by
  have hdconst : φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField (AdjoinRoot.mk W₂.toAffine.polynomial
        (Polynomial.C (Polynomial.C d)))) =
      algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField
        (algebraMap F (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing d) := by
    rw [show (AdjoinRoot.mk W₂.toAffine.polynomial (Polynomial.C (Polynomial.C d)) :
          (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing) =
        algebraMap F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing d from rfl,
      ← IsScalarTower.algebraMap_apply F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField d, φ.pullback.commutes d,
      ← IsScalarTower.algebraMap_apply F (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
        W₁.toAffine.FunctionField d]
  rw [hdconst]
  exact (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_le_one _ P

omit [IsAlgClosed F] in
private theorem pullback_algebraMap_mk_C_le_one
    (φ : HasseWeil.Isogeny W₁ W₂) (P : (W_smooth W₁).SmoothPoint)
    (hx : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P (φ.pullback (x_gen W₂)) ≤ 1)
    (a : Polynomial F) :
    (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
      (φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField (AdjoinRoot.mk W₂.toAffine.polynomial
          (Polynomial.C a)))) ≤ 1 := by
  set w := (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P with hw
  induction a using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.C_add, map_add, map_add, map_add]
    exact le_trans (w.map_add _ _) (max_le hp hq)
  | monomial m d =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul, Polynomial.C_pow]
    simp only [map_mul, map_pow, w.map_mul]
    have hXgen : φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField (AdjoinRoot.mk W₂.toAffine.polynomial
          (Polynomial.C Polynomial.X))) = φ.pullback (x_gen W₂) := rfl
    exact mul_le_one' (pullback_algebraMap_const_le_one φ P d)
      (by
        rw [hXgen]
        exact pow_le_one₀ zero_le hx)

omit [IsAlgClosed F] in
/-- Pulled-back coordinate-ring elements have valuation at most one at a regular point. -/
theorem pointValuation_le_one_pullback_coordinateRing
    (φ : HasseWeil.Isogeny W₁ W₂) (P : (W_smooth W₁).SmoothPoint)
    (hx : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P (φ.pullback (x_gen W₂)) ≤ 1)
    (hy : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P (φ.pullback (y_gen W₂)) ≤ 1)
    (c : (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing) :
    (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
      (φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField c)) ≤ 1 := by
  classical
  set w := (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P with hw
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective c
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, map_add]
    exact le_trans (w.map_add _ _) (max_le hp hq)
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, w.map_mul]
    have hXeq : φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField (AdjoinRoot.mk W₂.toAffine.polynomial Polynomial.X)) =
        φ.pullback (y_gen W₂) := rfl
    exact mul_le_one' (pullback_algebraMap_mk_C_le_one φ P hx a)
      (by
        rw [hXeq]
        exact pow_le_one₀ zero_le hy)

omit [IsAlgClosed F] in
private theorem pointValuation_le_one_of_mem_B
    (φ : HasseWeil.Isogeny W₁ W₂)
    [algKL : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsScalarTower F W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [algCR1 : Algebra (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField]
    [IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    (halg : ∀ g : W₂.toAffine.FunctionField,
      algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField g = φ.pullback g)
    (P : (W_smooth W₁).SmoothPoint)
    (hxle : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P (φ.pullback (x_gen W₂)) ≤ 1)
    (hyle : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P (φ.pullback (y_gen W₂)) ≤ 1)
    (b : NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :
    (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
      (algebraMap (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
        W₁.toAffine.FunctionField b) ≤ 1 := by
  classical
  set pv := (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P with hpv
  have hImOP : ∀ c : (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing,
      algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField c ∈
        pv.integer := by
    intro c
    rw [Valuation.mem_integer_iff]
    have hceq :
        algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField c =
          φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
            W₂.toAffine.FunctionField c) := by
      rw [← halg, IsScalarTower.algebraMap_apply (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField W₁.toAffine.FunctionField c]
    rw [hceq]
    exact pointValuation_le_one_pullback_coordinateRing φ P hxle hyle c
  letI algCR_int : Algebra (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing pv.integer :=
    (((algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₁.toAffine.FunctionField)).codRestrict pv.integer.toSubsemiring hImOP).toAlgebra
  haveI twCR_int : IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing pv.integer
      W₁.toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hbint : IsIntegral (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (algebraMap (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
        W₁.toAffine.FunctionField b) := b.2
  have hbint_int : IsIntegral pv.integer (algebraMap (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
      W₁.toAffine.FunctionField b) := hbint.tower_top
  exact (Valuation.integer.integers pv).isIntegral_iff_v_le_one.mp hbint_int

omit [IsAlgClosed F] in
omit [DecidableEq F] [W₂.toAffine.IsElliptic] in
private theorem bPrime_valuation_eq_pointValuation_of_center
    [_algKL : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [algCR1 : Algebra (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField]
    [IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsDedekindDomain (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))]
    [IsFractionRing (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
      W₁.toAffine.FunctionField]
    (P : (W_smooth W₁).SmoothPoint)
    (v : IsDedekindDomain.HeightOneSpectrum (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))))
    (hreg : ∀ b : NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)),
      (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
        (algebraMap (NormConormIntegralClosure.B
          (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
          W₁.toAffine.FunctionField b) ≤ 1)
    (hcenter : ∀ b : NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)),
      b ∈ v.asIdeal ↔ (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
        (algebraMap (NormConormIntegralClosure.B
          (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
          W₁.toAffine.FunctionField b) < 1) :
    v.valuation W₁.toAffine.FunctionField =
      (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P := by
  classical
  haveI hDVR : IsDiscreteValuationRing ((⟨W₁⟩ : SmoothPlaneCurve F).localRingAt P) :=
    (⟨W₁⟩ : SmoothPlaneCurve F).localRing_isDVR_of_smooth P
  have hwsurj : Function.Surjective (v.valuation W₁.toAffine.FunctionField) :=
    v.valuation_surjective W₁.toAffine.FunctionField
  have hpvsurj : Function.Surjective ((⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P) :=
    (IsDiscreteValuationRing.maximalIdeal
      ((⟨W₁⟩ : SmoothPlaneCurve F).localRingAt P)).valuation_surjective
      W₁.toAffine.FunctionField
  haveI : IsDiscreteValuationRing (v.valuation W₁.toAffine.FunctionField).valuationSubring :=
    valuationSubring_isDVR_of_surjective_withZeroInt _ hwsurj
  have hsub : (v.valuation W₁.toAffine.FunctionField).valuationSubring ≤
      ((⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P).valuationSubring := by
    intro f hf
    rw [Valuation.mem_valuationSubring_iff] at hf ⊢
    obtain ⟨n, d, hnd⟩ := IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
      v f hf
    have hd_notin :
        (d : NormConormIntegralClosure.B
          (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
          (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) ∉ v.asIdeal :=
      Ideal.mem_primeCompl_iff.mp d.2
    have hd_ge : ¬ (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P (algebraMap _
        W₁.toAffine.FunctionField (d : NormConormIntegralClosure.B
          (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
          (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))) < 1 := by
      rw [← hcenter]
      exact hd_notin
    have hd1 : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P (algebraMap _
        W₁.toAffine.FunctionField (d : NormConormIntegralClosure.B
          (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
          (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))) = 1 :=
      le_antisymm (hreg _) (not_lt.mp hd_ge)
    have hfn : f = algebraMap _ W₁.toAffine.FunctionField n /
        algebraMap _ W₁.toAffine.FunctionField (d : NormConormIntegralClosure.B
          (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
          (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) := by
      have hd_ne : algebraMap _ W₁.toAffine.FunctionField
          (d : NormConormIntegralClosure.B
            (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
            (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) ≠ 0 := by
        rw [Ne, ← ((⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P).zero_iff, hd1]
        exact one_ne_zero
      rw [eq_div_iff hd_ne, hnd]
    rw [hfn, map_div₀ ((⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P), hd1, div_one]
    exact hreg n
  have hAtop : ((⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P).valuationSubring ≠ ⊤ :=
    valuationSubring_ne_top_of_surjective_withZeroInt _ hpvsurj
  have hEq : (v.valuation W₁.toAffine.FunctionField).valuationSubring =
      ((⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P).valuationSubring :=
    rankOne_valuationSubring_le_eq_of_ne_top _ _ hsub hAtop
  have h_isEquiv : (v.valuation W₁.toAffine.FunctionField).IsEquiv
      ((⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P) := by
    rw [Valuation.isEquiv_iff_valuationSubring]
    rw [hEq]
  exact Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _ hwsurj hpvsurj h_isEquiv

omit [IsAlgClosed F] in
/-- A regular point where a nonzero `B`-element vanishes is cut out by a height-one prime of `B`. -/
theorem exists_bPrime_eq_pointValuation_of_notMem_poleLocus
    (φ : HasseWeil.Isogeny W₁ W₂)
    [algKL : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsScalarTower F W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [algCR1 : Algebra (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField]
    [IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsDedekindDomain (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))]
    [IsFractionRing (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
      W₁.toAffine.FunctionField]
    (halg : ∀ g : W₂.toAffine.FunctionField,
      algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField g = φ.pullback g)
    (P : (W_smooth W₁).SmoothPoint) (hP : P ∉ twoCurvePoleLocus φ)
    {z : NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))}
    (hz_ne : z ≠ 0)
    (hzvanish : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
      (algebraMap (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
        W₁.toAffine.FunctionField z) < 1) :
    ∃ v : IsDedekindDomain.HeightOneSpectrum (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))),
      v.valuation W₁.toAffine.FunctionField =
        (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P := by
  classical
  let Bb := NormConormIntegralClosure.B
    (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))
  let pv := (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
  have hxle : pv (φ.pullback (x_gen W₂)) ≤ 1 := by
    by_contra h
    exact hP (Or.inl h)
  have hyle : pv (φ.pullback (y_gen W₂)) ≤ 1 := by
    by_contra h
    exact hP (Or.inr h)
  have hregB : ∀ b : Bb, pv (algebraMap Bb W₁.toAffine.FunctionField b) ≤ 1 :=
    pointValuation_le_one_of_mem_B φ halg P hxle hyle
  set q : Ideal Bb :=
    { carrier := {b : Bb | pv (algebraMap Bb W₁.toAffine.FunctionField b) < 1}
      add_mem' := by
        intro a b ha hb
        change pv (algebraMap Bb W₁.toAffine.FunctionField a) < 1 at ha
        change pv (algebraMap Bb W₁.toAffine.FunctionField b) < 1 at hb
        change pv (algebraMap Bb W₁.toAffine.FunctionField (a + b)) < 1
        rw [RingHom.map_add]
        exact lt_of_le_of_lt (pv.map_add _ _) (max_lt ha hb)
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero, pv.map_zero]
        exact zero_lt_one
      smul_mem' := by
        intro c b hb
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, pv.map_mul] at *
        calc pv (algebraMap Bb W₁.toAffine.FunctionField c) *
              pv (algebraMap Bb W₁.toAffine.FunctionField b)
            ≤ 1 * pv (algebraMap Bb W₁.toAffine.FunctionField b) := by
              gcongr
              exact hregB c
          _ = pv (algebraMap Bb W₁.toAffine.FunctionField b) := one_mul _
          _ < 1 := hb } with hq_def
  have hq_mem_iff : ∀ b : Bb, b ∈ q ↔
      pv (algebraMap Bb W₁.toAffine.FunctionField b) < 1 := fun b => Iff.rfl
  have hq_prime : q.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hq_mem_iff, map_one, pv.map_one]
      exact lt_irrefl 1
    · intro a b hab
      rw [hq_mem_iff, map_mul, pv.map_mul] at hab
      by_contra h
      push Not at h
      obtain ⟨ha, hb⟩ := h
      rw [hq_mem_iff, not_lt] at ha hb
      have ha1 : pv (algebraMap Bb W₁.toAffine.FunctionField a) = 1 := le_antisymm (hregB a) ha
      have hb1 : pv (algebraMap Bb W₁.toAffine.FunctionField b) = 1 := le_antisymm (hregB b) hb
      rw [ha1, hb1, one_mul] at hab
      exact lt_irrefl 1 hab
  have hz_mem : z ∈ q := (hq_mem_iff z).mpr hzvanish
  have hq_ne : q ≠ ⊥ := fun h => hz_ne ((Submodule.mem_bot _).mp (h ▸ hz_mem))
  exact ⟨⟨q, hq_prime, hq_ne⟩,
    bPrime_valuation_eq_pointValuation_of_center P ⟨q, hq_prime, hq_ne⟩ hregB hq_mem_iff⟩

omit [IsAlgClosed F] in
private theorem pullback_algebraMap_coordinateRing_eq_algebraMap_bPrime
    (φ : HasseWeil.Isogeny W₁ W₂)
    [algKL : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsScalarTower F W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [algCR1 : Algebra (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField]
    [IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
      W₁.toAffine.FunctionField]
    (halg : ∀ g : W₂.toAffine.FunctionField,
      algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField g = φ.pullback g)
    (b : (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing) :
    φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField b) =
      algebraMap (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
        W₁.toAffine.FunctionField
        (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          (NormConormIntegralClosure.B
            (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
            (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) b) := by
  rw [← IsScalarTower.algebraMap_apply (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
    (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
    W₁.toAffine.FunctionField b, ← halg,
    IsScalarTower.algebraMap_apply (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField W₁.toAffine.FunctionField b]

omit [IsAlgClosed F] in
omit [DecidableEq F] [W₂.toAffine.IsElliptic] in
private theorem X_sub_x_mem_maximalIdealAt (Q : (W_smooth W₂).SmoothPoint) :
    (algebraMap (Polynomial F) (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Polynomial.X -
        algebraMap F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Q.x) ∈
      (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q := by
  have hx : (⟨W₂⟩ : SmoothPlaneCurve F).evalAt Q
      (algebraMap (Polynomial F) W₂.toAffine.CoordinateRing Polynomial.X) = Q.x := by
    rw [show algebraMap (Polynomial F) W₂.toAffine.CoordinateRing Polynomial.X =
      WeierstrassCurve.Affine.CoordinateRing.mk W₂.toAffine (Polynomial.C Polynomial.X) from rfl]
    exact (⟨W₂⟩ : SmoothPlaneCurve F).evalAt_x Q
  have h0 : (⟨W₂⟩ : SmoothPlaneCurve F).evalAt Q
      (algebraMap (Polynomial F) W₂.toAffine.CoordinateRing Polynomial.X -
        algebraMap F W₂.toAffine.CoordinateRing Q.x) = 0 :=
    (map_sub ((⟨W₂⟩ : SmoothPlaneCurve F).evalAt Q) _ _).trans
      (by
        rw [hx]
        exact sub_eq_zero_of_eq ((⟨W₂⟩ : SmoothPlaneCurve F).evalAt_algebraMap Q Q.x).symm)
  exact (⟨W₂⟩ : SmoothPlaneCurve F).ker_evalAt Q ▸ RingHom.mem_ker.mpr h0

omit [IsAlgClosed F] in
omit [DecidableEq F] [W₂.toAffine.IsElliptic] in
private theorem root_sub_y_mem_maximalIdealAt (Q : (W_smooth W₂).SmoothPoint) :
    (AdjoinRoot.root W₂.toAffine.polynomial -
        algebraMap F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Q.y) ∈
      (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q := by
  have hy :
      (⟨W₂⟩ : SmoothPlaneCurve F).evalAt Q
        (AdjoinRoot.root W₂.toAffine.polynomial) = Q.y :=
    (⟨W₂⟩ : SmoothPlaneCurve F).evalAt_y Q
  have h0 : (⟨W₂⟩ : SmoothPlaneCurve F).evalAt Q
      (AdjoinRoot.root W₂.toAffine.polynomial -
        algebraMap F W₂.toAffine.CoordinateRing Q.y) = 0 :=
    (map_sub ((⟨W₂⟩ : SmoothPlaneCurve F).evalAt Q) _ _).trans
      (by
        rw [hy]
        exact sub_eq_zero_of_eq ((⟨W₂⟩ : SmoothPlaneCurve F).evalAt_algebraMap Q Q.y).symm)
  exact (⟨W₂⟩ : SmoothPlaneCurve F).ker_evalAt Q ▸ RingHom.mem_ker.mpr h0

/-- A `B`-prime over `m_Q` maps its corresponding point to the affine place `Q`. -/
theorem placeRestrictionPlaceImage_affine_eq_of_bPrime
    (φ : HasseWeil.Isogeny W₁ W₂)
    [algKL : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsScalarTower F W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [algCR1 : Algebra (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField]
    [IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsDedekindDomain (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))]
    [IsFractionRing (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
      W₁.toAffine.FunctionField]
    (halg : ∀ g : W₂.toAffine.FunctionField,
      algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField g = φ.pullback g)
    (v : IsDedekindDomain.HeightOneSpectrum (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))))
    (P : (W_smooth W₁).SmoothPoint) (Q : (W_smooth W₂).SmoothPoint)
    (hP : v.valuation W₁.toAffine.FunctionField =
      (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P)
    (hQ : v.asIdeal.under (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing =
      (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q) :
    placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine P) =
      ProjectiveSmoothPoint.affine Q := by
  classical
  haveI tw1B : IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
      W₁.toAffine.FunctionField := inferInstance
  have halgB : ∀ b : (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing,
      φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField b) =
      algebraMap (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
        W₁.toAffine.FunctionField
        (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          (NormConormIntegralClosure.B
            (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
            (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) b) :=
    fun b => pullback_algebraMap_coordinateRing_eq_algebraMap_bPrime φ halg b
  have hkey : ∀ b : (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing,
      b ∈ (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q →
      (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
        (φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField b)) < 1 := by
    intro b hb
    have hmem : algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        (NormConormIntegralClosure.B
          (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
          (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) b ∈ v.asIdeal := by
      have : b ∈ v.asIdeal.under (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing := by
        rw [hQ]
        exact hb
      rwa [Ideal.mem_under] at this
    rw [halgB b, ← hP, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hmem
  have hbx_mem : (algebraMap (Polynomial F) (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        Polynomial.X -
      algebraMap F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Q.x) ∈
      (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q := X_sub_x_mem_maximalIdealAt Q
  have hby_mem : (AdjoinRoot.root W₂.toAffine.polynomial -
      algebraMap F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Q.y) ∈
      (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q := root_sub_y_mem_maximalIdealAt Q
  have hxgen : x_gen W₂ = algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField
      (algebraMap (Polynomial F) (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        Polynomial.X) := rfl
  have hygen : y_gen W₂ = algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField (AdjoinRoot.root W₂.toAffine.polynomial) := rfl
  have hEvX : EvaluatesTo W₁ P (φ.pullback (x_gen W₂)) Q.x := by
    unfold EvaluatesTo
    have hrw : φ.pullback (x_gen W₂) - algebraMap F W₁.toAffine.FunctionField Q.x =
        φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField
          (algebraMap (Polynomial F) (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Polynomial.X -
            algebraMap F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Q.x)) := by
      rw [map_sub, map_sub, hxgen, ← φ.pullback.commutes Q.x,
        ← IsScalarTower.algebraMap_apply F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField Q.x]
    rw [hrw]
    exact hkey _ hbx_mem
  have hEvY : EvaluatesTo W₁ P (φ.pullback (y_gen W₂)) Q.y := by
    unfold EvaluatesTo
    have hrw : φ.pullback (y_gen W₂) - algebraMap F W₁.toAffine.FunctionField Q.y =
        φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField
          (AdjoinRoot.root W₂.toAffine.polynomial -
            algebraMap F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing Q.y)) := by
      rw [map_sub, map_sub, hygen, ← φ.pullback.commutes Q.y,
        ← IsScalarTower.algebraMap_apply F (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField Q.y]
    rw [hrw]
    exact hkey _ hby_mem
  have hregGen : ∀ b : (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing,
      (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
        (φ.pullback (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          W₂.toAffine.FunctionField b)) ≤ 1 := by
    intro b
    rw [halgB b, ← hP]
    exact v.valuation_le_one (K := W₁.toAffine.FunctionField) _
  have hPnotMem : P ∉ twoCurvePoleLocus φ := by
    intro hmem
    rcases hmem with hx | hy
    · exact hx (by
        rw [hxgen]
        exact hregGen _)
    · exact hy (by
        rw [hygen]
        exact hregGen _)
  obtain ⟨h', himg⟩ := placeRestrictionPointMap_residue_agreement φ P hPnotMem hEvX hEvY
  have hgoal : placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine P) =
      (placeRestrictionPointMap φ P.toAffinePoint).toProjectiveSmoothPoint := rfl
  rw [hgoal, himg]
  rfl

private theorem bPrime_exists_point_image_of_mem_primesOver
    (φ : HasseWeil.Isogeny W₁ W₂)
    [algKL : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsScalarTower F W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [algCR1 : Algebra (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField]
    [IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsDedekindDomain (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))]
    [IsFractionRing (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
      W₁.toAffine.FunctionField]
    (halg : ∀ g : W₂.toAffine.FunctionField,
      algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField g = φ.pullback g)
    (hregB : NormConormIntegralClosure.OrdAtInftyReg
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
    (Q : (⟨W₂⟩ : SmoothPlaneCurve F).SmoothPoint)
    (vP : IsDedekindDomain.HeightOneSpectrum (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))))
    (hvP : vP.asIdeal ∈ IsDedekindDomain.primesOverFinset
      ((⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q) (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))) :
    ∃ P : (W_smooth W₁).SmoothPoint,
      vP.valuation W₁.toAffine.FunctionField =
        (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P ∧
      placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine P) =
        ProjectiveSmoothPoint.affine Q := by
  classical
  haveI instFin : Module.Finite (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
    NormConormIntegralClosure.instModuleFiniteB
  haveI instTF : Module.IsTorsionFree (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
    NormConormIntegralClosure.instTorsionFreeB
  haveI instIntClosedB : IsIntegrallyClosed (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
    inferInstance
  haveI instIntegralAB : Algebra.IsIntegral (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
    inferInstance
  haveI hpMax : ((⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q).IsMaximal :=
    (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt_isMaximal Q
  have hp_ne : (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q ≠ ⊥ :=
    (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt_ne_bot Q
  have hcoordLE := NormConormIntegralClosure.bPrimeValuationCoordGenLeOne_of_reg hregB
  obtain ⟨P, hP⟩ :=
    NormConormIntegralClosure.bPrime_valuation_eq_pointValuation_of_coordGen_le_one
      vP (hcoordLE vP).1 (hcoordLE vP).2
  rw [IsDedekindDomain.mem_primesOverFinset_iff (B := NormConormIntegralClosure.B
    (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
    (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) hp_ne] at hvP
  have hunder : vP.asIdeal.under (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing =
      (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q := hvP.2.over.symm
  exact ⟨P, hP, placeRestrictionPlaceImage_affine_eq_of_bPrime φ halg vP P Q hP hunder⟩

omit [DecidableEq F] [W₂.toAffine.IsElliptic] [IsAlgClosed F] in
set_option backward.isDefEq.respectTransparency false in
private theorem bPrime_count_eq_projectiveDivisorOf_of_valuation_eq
    [_algKL : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsScalarTower F W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [algCR1 : Algebra (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing W₁.toAffine.FunctionField]
    [IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    [IsDedekindDomain (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))]
    [IsFractionRing (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
      W₁.toAffine.FunctionField]
    {w : (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing} (hw : w ≠ 0)
    (wB : NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
    (hwB_ne : wB ≠ 0)
    (hwBval : algebraMap (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
        W₁.toAffine.FunctionField wB =
      algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
        (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w)
    (vP : IsDedekindDomain.HeightOneSpectrum (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))))
    (P : (W_smooth W₁).SmoothPoint)
    (hPval : vP.valuation W₁.toAffine.FunctionField =
      (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P) :
    ((Associates.mk vP.asIdeal).count (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ) =
      (⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
          (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w) (ProjectiveSmoothPoint.affine P) := by
  classical
  haveI : IsIntegrallyClosed (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing := inferInstance
  have h1 : vP.valuation W₁.toAffine.FunctionField
        (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
          (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w) =
      WithZero.exp (-((Associates.mk vP.asIdeal).count
        (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ)) := by
    rw [← hwBval, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      vP.intValuation_if_neg hwB_ne]
  have h2 : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P
        (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
          (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w) =
      WithZero.exp (-((Associates.mk ((⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt P)).count
        (Associates.mk (Ideal.span {w})).factors : ℤ)) :=
    (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_eq_exp_count P hw
  have hcounts : ((Associates.mk vP.asIdeal).count
        (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ) =
      ((Associates.mk ((⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt P)).count
        (Associates.mk (Ideal.span {w})).factors : ℤ) := by
    have : WithZero.exp (-((Associates.mk vP.asIdeal).count
          (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ)) =
        WithZero.exp (-((Associates.mk ((⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt P)).count
          (Associates.mk (Ideal.span {w})).factors : ℤ)) := by
      rw [← h1, ← h2, hPval]
    rw [WithZero.exp_inj, neg_inj] at this
    exact this
  rw [hcounts, (⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf_apply_affine,
    (⟨W₁⟩ : SmoothPlaneCurve F).ord_P_algebraMap_eq_count P hw, WithTop.untopD_coe]

set_option backward.isDefEq.respectTransparency false in
/-- The order of a conorm at an affine place equals the sum of orders over its fiber. -/
theorem twoCurve_ord_conorm_eq_sum_fiber
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra.toModule)
    (hsep : @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra)
    (hreg : ∀ f : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.pullback f))
    {w : (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing} (hw : w ≠ 0)
    (Q : (⟨W₂⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (⟨W₂⟩ : SmoothPlaneCurve F).ord_P Q (conorm φ
        (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
          (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w)) =
      (((placeRestrictionPushforward φ
          ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf
            (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
              (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w)))
        (ProjectiveSmoothPoint.affine Q) : ℤ) : WithTop ℤ) := by
  classical
  letI algKL : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField := φ.toAlgebra
  haveI twF : IsScalarTower F W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.pullback.commutes c).symm
  haveI finKL : FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField := hfin
  haveI sepKL : Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField := hsep
  letI algCR1 : Algebra (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₁.toAffine.FunctionField :=
    ((algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField).comp
      (algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        W₂.toAffine.FunctionField)).toAlgebra
  haveI tw1 : IsScalarTower (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI instDed : IsDedekindDomain (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
    NormConormIntegralClosure.instDedekindB
  haveI instFin : Module.Finite (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
    NormConormIntegralClosure.instModuleFiniteB
  haveI instFracB : IsFractionRing (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
      W₁.toAffine.FunctionField :=
    NormConormIntegralClosure.instFractionRingB
  haveI instTF : Module.IsTorsionFree (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
    NormConormIntegralClosure.instTorsionFreeB
  haveI instIntClosedB : IsIntegrallyClosed (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
    inferInstance
  haveI instIntegralAB : Algebra.IsIntegral (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
    inferInstance
  have hregB : NormConormIntegralClosure.OrdAtInftyReg
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
      (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)) := hreg
  set aw := algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
    (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w with haw
  have haw_mem : aw ∈ NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)) :=
    NormConormIntegralClosure.coordRing_mem_B_of_reg hregB w
  set wB : NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)) :=
    ⟨aw, haw_mem⟩ with hwB
  have hwB_ne : wB ≠ 0 := by
    rw [hwB, Ne, Subtype.ext_iff]
    simp only [ZeroMemClass.coe_zero]
    rw [haw]
    intro h
    exact hw ((IsFractionRing.injective (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
      (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField) (h.trans (map_zero _).symm))
  have hconorm_eq : conorm φ aw =
      algebraMap (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField
        (Algebra.intNorm (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          (NormConormIntegralClosure.B
            (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
            (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) wB) := by
    rw [Algebra.algebraMap_intNorm (K := (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField)
      (L := (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField)]
    show conorm φ aw = Algebra.norm (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField
      (algebraMap (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
        (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField wB)
    rfl
  have hintNorm_ne : Algebra.intNorm (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
        (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) wB ≠ 0 := by
    have hconorm_ne : conorm φ aw ≠ 0 := by
      apply conorm_ne_zero φ
      rw [haw]
      intro h
      exact hw ((IsFractionRing.injective (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
        (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField) (h.trans (map_zero _).symm))
    intro hzero
    rw [hconorm_eq, hzero, map_zero] at hconorm_ne
    exact hconorm_ne rfl
  have hLHS : (⟨W₂⟩ : SmoothPlaneCurve F).ord_P Q (conorm φ aw) =
      (((Associates.mk ((⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q)).count
        (Associates.mk (Ideal.span {Algebra.intNorm (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
          (NormConormIntegralClosure.B
            (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
            (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) wB})).factors
          : ℤ) : WithTop ℤ) := by
    rw [hconorm_eq, (⟨W₂⟩ : SmoothPlaneCurve F).ord_P_algebraMap_eq_count Q hintNorm_ne]
  have hrelN : Ideal.span ({Algebra.intNorm (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        (NormConormIntegralClosure.B
          (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
          (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) wB} :
        Set (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing) =
      Ideal.relNorm (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing
        (Ideal.span ({wB} : Set (NormConormIntegralClosure.B
          (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
          (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))))) :=
    (Ideal.relNorm_singleton (R := (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing) wB).symm
  haveI : IsIntegrallyClosed (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing := inferInstance
  set D := (⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf aw with hD_def
  set p : Ideal (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing :=
    (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt Q with hp_def
  have hp_ne : p ≠ ⊥ := (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt_ne_bot Q
  haveI hpMax : p.IsMaximal := (⟨W₂⟩ : SmoothPlaneCurve F).maximalIdealAt_isMaximal Q
  have hpoint : ∀ vP : IsDedekindDomain.HeightOneSpectrum (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))),
      vP.asIdeal ∈ IsDedekindDomain.primesOverFinset p (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) →
      ∃ P : (W_smooth W₁).SmoothPoint,
        vP.valuation W₁.toAffine.FunctionField =
          (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P ∧
        placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine P) =
          ProjectiveSmoothPoint.affine Q :=
    fun vP hvP => bPrime_exists_point_image_of_mem_primesOver φ (fun g => rfl) hregB Q vP hvP
  have hcountMatch : ∀ (vP : IsDedekindDomain.HeightOneSpectrum (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))))
      (P : (W_smooth W₁).SmoothPoint),
      vP.valuation W₁.toAffine.FunctionField =
        (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P →
      ((Associates.mk vP.asIdeal).count (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ) =
        D (ProjectiveSmoothPoint.affine P) :=
    fun vP P hPval =>
      bPrime_count_eq_projectiveDivisorOf_of_valuation_eq hw wB hwB_ne rfl vP P hPval
  rw [hLHS, hrelN, NormConormIntegralClosure.count_relNorm_eq_sum_fiber_B hwB_ne Q]
  set primesB := IsDedekindDomain.primesOverFinset p (NormConormIntegralClosure.B
    (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
    (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) with hprimesB
  have hPrimeData : ∀ P' ∈ primesB, ∃ vP : IsDedekindDomain.HeightOneSpectrum
      (NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))),
      vP.asIdeal = P' ∧ ∃ pt : (W_smooth W₁).SmoothPoint,
        vP.valuation W₁.toAffine.FunctionField =
          (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation pt ∧
        placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine pt) =
          ProjectiveSmoothPoint.affine Q := by
    intro P' hP'
    rw [hprimesB, IsDedekindDomain.mem_primesOverFinset_iff (B := NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
      (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) hp_ne] at hP'
    have hP'_ne : P' ≠ ⊥ := by
      intro h
      apply hp_ne
      have := hP'.2.over
      rw [h, Ideal.under_bot] at this
      exact this
    set vP : IsDedekindDomain.HeightOneSpectrum (NormConormIntegralClosure.B
      (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) :=
      ⟨P', hP'.1, hP'_ne⟩ with hvP_def
    have hmem : vP.asIdeal ∈ primesB := by
      rw [hprimesB, IsDedekindDomain.mem_primesOverFinset_iff (B := NormConormIntegralClosure.B
        (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
        (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) hp_ne]
      exact hP'
    obtain ⟨pt, hpt1, hpt2⟩ := hpoint vP hmem
    exact ⟨vP, rfl, pt, hpt1, hpt2⟩
  let ptF : (P' : Ideal (NormConormIntegralClosure.B
    (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
    (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))) → P' ∈ primesB →
      (W_smooth W₁).SmoothPoint := fun P' hP' => (hPrimeData P' hP').choose_spec.2.choose
  have hptF_val : ∀ P' (hP' : P' ∈ primesB),
      (hPrimeData P' hP').choose.valuation W₁.toAffine.FunctionField =
        (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation (ptF P' hP') := fun P' hP' =>
    (hPrimeData P' hP').choose_spec.2.choose_spec.1
  have hptF_id : ∀ P' (hP' : P' ∈ primesB), (hPrimeData P' hP').choose.asIdeal = P' :=
    fun P' hP' => (hPrimeData P' hP').choose_spec.1
  have hptF_img : ∀ P' (hP' : P' ∈ primesB),
      placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine (ptF P' hP')) =
        ProjectiveSmoothPoint.affine Q := fun P' hP' =>
    (hPrimeData P' hP').choose_spec.2.choose_spec.2
  have hcount_ptF : ∀ P' (hP' : P' ∈ primesB),
      ((Associates.mk P').count (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ) =
        D (ProjectiveSmoothPoint.affine (ptF P' hP')) := by
    intro P' hP'
    have hcm := hcountMatch (hPrimeData P' hP').choose (ptF P' hP') (hptF_val P' hP')
    rw [hptF_id P' hP'] at hcm
    exact hcm
  have hptF_inj : ∀ P₁ (h₁ : P₁ ∈ primesB) P₂ (h₂ : P₂ ∈ primesB),
      ptF P₁ h₁ = ptF P₂ h₂ → P₁ = P₂ := by
    intro P₁ h₁ P₂ h₂ heq
    have hv1 := hptF_val P₁ h₁
    have hv2 := hptF_val P₂ h₂
    rw [heq] at hv1
    have hvaleq : (hPrimeData P₁ h₁).choose.valuation W₁.toAffine.FunctionField =
        (hPrimeData P₂ h₂).choose.valuation W₁.toAffine.FunctionField := by rw [hv1, hv2]
    have hideq : (hPrimeData P₁ h₁).choose.asIdeal = (hPrimeData P₂ h₂).choose.asIdeal := by
      ext a
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
          (K := W₁.toAffine.FunctionField),
        ← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
          (K := W₁.toAffine.FunctionField), hvaleq]
    rw [← hptF_id P₁ h₁, ← hptF_id P₂ h₂, hideq]
  let fibreImg : Finset (ProjectiveSmoothPoint (⟨W₁⟩ : SmoothPlaneCurve F)) :=
    primesB.attach.image (fun P' => ProjectiveSmoothPoint.affine (ptF P'.1 P'.2))
  have hstep1 : (∑ P' ∈ primesB,
      ((Associates.mk P').count (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ)) =
      ∑ x ∈ fibreImg, D x := by
    rw [← Finset.sum_attach primesB (fun P' =>
      ((Associates.mk P').count (Associates.mk (Ideal.span ({wB} : Set _))).factors : ℤ))]
    rw [Finset.sum_image (by
      rintro ⟨a, ha⟩ _ ⟨b, hb⟩ _ hab
      simp only [ProjectiveSmoothPoint.affine.injEq] at hab
      exact Subtype.ext (hptF_inj a ha b hb hab))]
    apply Finset.sum_congr rfl
    rintro ⟨P', hP'⟩ _
    exact hcount_ptF P' hP'
  rw [placeRestrictionPushforward_apply_affine]
  refine congrArg (fun n : ℤ => (n : WithTop ℤ)) ?_
  rw [Nat.cast_sum, hstep1]
  symm
  apply Finset.sum_subset
  · -- `D.support.filter(placeImage = affine Q) ⊆ fibreImg`: surjectivity via `exists_bPrime`.
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hx_supp, hx_img⟩ := hx
    cases x with
    | infinity =>
      refine absurd hx_img ?_
      show (placeRestrictionPointMap φ
        (ProjectiveSmoothPoint.infinity : ProjectiveSmoothPoint
          (⟨W₁⟩ : SmoothPlaneCurve F)).toAffinePoint).toProjectiveSmoothPoint ≠ _
      simp only [Curves.ProjectiveSmoothPoint.toAffinePoint_infinity]
      exact fun h => by cases h
    | affine P' =>
      have hP'_notpole : P' ∉ twoCurvePoleLocus φ := by
        intro hpole
        have himg : placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine P') =
            ProjectiveSmoothPoint.infinity := by
          show (placeRestrictionPointMap φ
            (ProjectiveSmoothPoint.affine P').toAffinePoint).toProjectiveSmoothPoint = _
          rw [Curves.ProjectiveSmoothPoint.toAffinePoint_affine]
          rcases P' with ⟨px, py, ph⟩
          rw [SmoothPlaneCurve.SmoothPoint.toAffinePoint_def,
            placeRestrictionPointMap_some_of_mem φ hpole]
          rfl
        rw [himg] at hx_img
        cases hx_img
      have hP'_vanish : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P'
          (algebraMap (NormConormIntegralClosure.B
            (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F)) (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F)))
            W₁.toAffine.FunctionField wB) < 1 := by
        rw [Finsupp.mem_support_iff, hD_def,
          (⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf_apply_affine] at hx_supp
        have haw_ne : aw ≠ 0 := by
          rw [haw]
          intro h
          exact hw ((IsFractionRing.injective (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
            (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField) (h.trans (map_zero _).symm))
        show (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P' aw < 1
        rw [← (⟨W₁⟩ : SmoothPlaneCurve F).one_le_ord_P_iff_pointValuation_lt_one haw_ne]
        rw [(⟨W₁⟩ : SmoothPlaneCurve F).ord_P_algebraMap_eq_count P' hw] at hx_supp ⊢
        have hcount_ne : (Associates.mk ((⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt P')).count
            (Associates.mk (Ideal.span {w})).factors ≠ 0 := by
          intro h0
          exact hx_supp (by
            rw [h0]
            rfl)
        rw [show (1 : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcount_ne
      obtain ⟨vP, hvP⟩ := exists_bPrime_eq_pointValuation_of_notMem_poleLocus φ
        (fun g => rfl) P' hP'_notpole hwB_ne hP'_vanish
      obtain ⟨Q', hQ'⟩ := NormConormIntegralClosure.exists_smoothPoint_under vP
      have himg' : placeRestrictionPlaceImage φ (ProjectiveSmoothPoint.affine P') =
          ProjectiveSmoothPoint.affine Q' :=
        placeRestrictionPlaceImage_affine_eq_of_bPrime φ (fun g => rfl) vP P' Q' hvP hQ'
      have hQeq : Q' = Q := by
        have h := himg'.symm.trans hx_img
        exact ProjectiveSmoothPoint.affine.inj h
      have hvP_mem : vP.asIdeal ∈ primesB := by
        rw [hprimesB, IsDedekindDomain.mem_primesOverFinset_iff (B :=
          NormConormIntegralClosure.B
            (C₁ := (⟨W₁⟩ : SmoothPlaneCurve F))
            (C₂ := (⟨W₂⟩ : SmoothPlaneCurve F))) hp_ne]
        exact ⟨vP.isPrime, ⟨by
          rw [hp_def, ← hQeq]
          exact hQ'.symm⟩⟩
      simp only [fibreImg, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      refine ⟨vP.asIdeal, hvP_mem, ?_⟩
      congr 1
      have hchoose_eq : (hPrimeData vP.asIdeal hvP_mem).choose = vP :=
        IsDedekindDomain.HeightOneSpectrum.ext (hptF_id vP.asIdeal hvP_mem)
      have hval_eq : (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation (ptF vP.asIdeal hvP_mem) =
          (⟨W₁⟩ : SmoothPlaneCurve F).pointValuation P' := by
        rw [← hptF_val vP.asIdeal hvP_mem, hchoose_eq, hvP]
      have hmIeq : (⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt (ptF vP.asIdeal hvP_mem) =
          (⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt P' := by
        let C := (⟨W₁⟩ : SmoothPlaneCurve F)
        change C.maximalIdealAt (ptF vP.asIdeal hvP_mem) = C.maximalIdealAt P'
        ext a
        rw [← C.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt a,
          ← C.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt a,
          hval_eq]
      exact SmoothPlaneCurve.SmoothPoint.ext
        (congrArg (fun (P : (⟨W₁⟩ : SmoothPlaneCurve F).SmoothPoint) => P.x)
          ((⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt_injective hmIeq))
        (congrArg (fun (P : (⟨W₁⟩ : SmoothPlaneCurve F).SmoothPoint) => P.y)
          ((⟨W₁⟩ : SmoothPlaneCurve F).maximalIdealAt_injective hmIeq))
  · -- the extra `fibreImg` points (not in `support.filter`) have `D = 0`.
    intro x hx_img hx_notin
    simp only [fibreImg, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hx_img
    obtain ⟨P', hP', hxeq⟩ := hx_img
    rw [Finset.mem_filter, not_and] at hx_notin
    by_contra hDx
    exact hx_notin (Finsupp.mem_support_iff.mpr hDx) (by
      rw [← hxeq]
      exact hptF_img P' hP')

private theorem conorm_projectiveDivisorOf_apply_affine_eq
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra.toModule)
    (hsep : @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra)
    (hreg : ∀ f : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.pullback f))
    {w : (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing} (hw : w ≠ 0)
    (Q : (⟨W₂⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ
        (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
          (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w))
        (ProjectiveSmoothPoint.affine Q) =
      placeRestrictionPushforward φ ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
          (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w))
        (ProjectiveSmoothPoint.affine Q) := by
  rw [(⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf_apply_affine,
    twoCurve_ord_conorm_eq_sum_fiber φ hfin hsep hreg hw Q, WithTop.untopD_coe]

/-- The norm-conorm identity holds for nonzero coordinate-ring elements. -/
theorem placeRestrictionPushforward_projectiveDivisorOf_algebraMap
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra.toModule)
    (hsep : @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra)
    (hreg : ∀ f : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.pullback f))
    {w : (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing} (hw : w ≠ 0) :
    placeRestrictionPushforward φ ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
          (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w)) =
      (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ
        (algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
          (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w)) := by
  classical
  set aw := algebraMap (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing
    (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField w with haw
  set LHS := placeRestrictionPushforward φ
    ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf aw) with hLHS_def
  set RHS := (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ aw) with hRHS_def
  have h_aff : ∀ Q : (⟨W₂⟩ : SmoothPlaneCurve F).SmoothPoint,
      LHS (ProjectiveSmoothPoint.affine Q) = RHS (ProjectiveSmoothPoint.affine Q) := fun Q =>
    (conorm_projectiveDivisorOf_apply_affine_eq φ hfin hsep hreg hw Q).symm
  have hLHS_deg : LHS.degree = 0 := by
    rw [hLHS_def, degree_placeRestrictionPushforward]
    exact (⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf_degree_eq_zero _
  have hRHS_deg : RHS.degree = 0 := by
    rw [hRHS_def]
    exact (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf_degree_eq_zero _
  refine Finsupp.ext fun v => ?_
  cases v with
  | affine Q => exact h_aff Q
  | infinity =>
    exact CurveMap.projDivisor_infinity_coeff_eq_of_affine_eq LHS RHS
      (hLHS_deg.trans hRHS_deg.symm) h_aff

/-- The projective divisor of a conorm is the place-restriction pushforward of the
original divisor. -/
theorem placeRestrictionPushforward_projectiveDivisorOf
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra.toModule)
    (hsep : @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra)
    (hreg : ∀ f : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.pullback f))
    (f : W₁.toAffine.FunctionField) :
    placeRestrictionPushforward φ ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf f) =
      (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf (conorm φ f) :=
  placeRestrictionPushforward_projectiveDivisorOf_of_algebraMap φ hfin
    (fun _ hw => placeRestrictionPushforward_projectiveDivisorOf_algebraMap φ hfin hsep hreg hw) f

/-- A finite separable pullback makes place restriction preserve principal divisors. -/
theorem placeRestrictionPreservesPrincipal_of_finite_separable
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra.toModule)
    (hsep : @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra)
    (hreg : ∀ f : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.pullback f)) :
    PlaceRestrictionPreservesPrincipal φ := by
  intro D hD
  obtain ⟨f, hf_ne, hfD⟩ := hD
  refine ⟨conorm φ f, conorm_ne_zero φ hf_ne, ?_⟩
  rw [← hfD]
  exact (placeRestrictionPushforward_projectiveDivisorOf φ hfin hsep hreg f).symm

/-- A separable pullback makes place restriction preserve principal divisors. -/
theorem placeRestrictionPreservesPrincipal_of_separable
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hsep : @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra)
    (hreg : ∀ f : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.pullback f)) :
    PlaceRestrictionPreservesPrincipal φ :=
  placeRestrictionPreservesPrincipal_of_finite_separable φ
    (isogeny_finiteDimensional_twoCurve φ) hsep hreg

/-- In characteristic zero, a separable pullback makes place restriction preserve
principal divisors. -/
theorem placeRestrictionPreservesPrincipal_of_separable_charZero [CharZero F]
    (φ : HasseWeil.Isogeny W₁ W₂)
    (hsep : @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _
      φ.toAlgebra)
    (hreg : ∀ f : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.pullback f)) :
    PlaceRestrictionPreservesPrincipal φ := by
  haveI : CharZero (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing :=
    charZero_of_injective_algebraMap (R := F) (algebraMap F _).injective
  haveI : CharZero (FractionRing (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing) :=
    charZero_of_injective_algebraMap (R := (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing)
      (IsFractionRing.injective (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing _)
  exact placeRestrictionPreservesPrincipal_of_separable φ hsep hreg

end HasseWeil.WeilPairing
