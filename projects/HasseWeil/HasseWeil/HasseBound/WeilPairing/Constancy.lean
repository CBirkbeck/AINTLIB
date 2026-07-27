/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Foundation.Curves.Divisor.ProjectiveDivisor
import HasseWeil.Foundation.Curves.Valuation.NoFinitePolesBridge

/-!
# Constancy of Weil pairing values

This file proves that a nonzero function with trivial projective divisor is a base-field constant.
It then derives constancy and multiplicativity properties used to construct the Weil pairing.

## Main results

* `const_of_projectiveDivisorOf_eq_zero`: a nonzero function with trivial divisor is constant.
* `pairing_const_of_transport`: a translated function is a nonzero scalar multiple of itself.
* `pairing_const_pow_eq_one`: this scalar is a root of unity when the appropriate power is fixed.
* `pairing_const_mul`: the scalars multiply under composition.

## References

* [Joseph H. Silverman, *The Arithmetic of Elliptic Curves*, Chapter II, Proposition 1.2]
-/

open WeierstrassCurve

namespace HasseWeil.WeilPairing

open Curves

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}

/-- A nonzero function with trivial projective divisor is induced by a base-field scalar. -/
theorem const_of_projectiveDivisorOf_eq_zero [IsAlgClosed F] [W.IsElliptic]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hf : f ≠ 0)
    (hdiv : (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf f = 0) :
    ∃ c : F, f = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c := by
  have nonneg_of_untopD_eq_zero {a : WithTop ℤ} (ha : a ≠ ⊤)
      (h : WithTop.untopD 0 a = 0) : 0 ≤ a := by
    obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp ha
    rw [WithTop.untopD_coe] at h
    subst n
    exact le_refl _
  have hord : ∀ P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint,
      0 ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P f := by
    intro P
    apply nonneg_of_untopD_eq_zero
    · exact ((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff f).not.mpr hf
    · simpa only [(⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf_apply_affine,
        Finsupp.coe_zero, Pi.zero_apply] using
        DFunLike.congr_fun hdiv (ProjectiveSmoothPoint.affine P)
  have hinf : (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty f := by
    apply nonneg_of_untopD_eq_zero
    · exact ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_eq_top_iff f).not.mpr hf
    · simpa only [(⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf_apply_infinity,
        Finsupp.coe_zero, Pi.zero_apply] using
        DFunLike.congr_fun hdiv ProjectiveSmoothPoint.infinity
  refine (⟨W⟩ : SmoothPlaneCurve F).const_of_valuation_le_one_of_ordAtInfty_nonneg f ?_ hinf
  intro v
  obtain ⟨P, hP⟩ := smoothPointToHeightOne_surjective W v
  rw [← hP, ← pointValuation_eq_heightOneValuation W P f]
  exact pointValuation_le_one_of_ord_nonneg W hf P (hord P)

/-- A nonzero function with trivial projective divisor is a nonzero base-field scalar. -/
theorem const_unit_of_projectiveDivisorOf_eq_zero [IsAlgClosed F] [W.IsElliptic]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hf : f ≠ 0)
    (hdiv : (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf f = 0) :
    ∃ c : F, c ≠ 0 ∧ f = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c := by
  obtain ⟨c, hc⟩ := const_of_projectiveDivisorOf_eq_zero f hf hdiv
  refine ⟨c, fun h => hf ?_, hc⟩
  simpa [h] using hc

/-- If `τ g / g` has trivial projective divisor, then `τ g` is a nonzero scalar multiple
of `g`. -/
theorem pairing_const_of_transport [IsAlgClosed F] [W.IsElliptic]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (τ : (⟨W⟩ : SmoothPlaneCurve F).FunctionField ≃+*
      (⟨W⟩ : SmoothPlaneCurve F).FunctionField)
    (g : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hg : g ≠ 0)
    (htransport : (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf (τ g / g) = 0) :
    ∃ c : F, c ≠ 0 ∧
      τ g = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c * g := by
  have hτg : τ g ≠ 0 := (map_ne_zero_iff τ τ.injective).mpr hg
  obtain ⟨c, hc0, hc⟩ :=
    const_unit_of_projectiveDivisorOf_eq_zero (τ g / g) (div_ne_zero hτg hg) htransport
  exact ⟨c, hc0, (div_eq_iff hg).mp hc⟩

omit [DecidableEq F] in
/-- A scalar relating `τ g` to `g` is an `ℓ`-th root of unity if `τ` fixes `g ^ ℓ`. -/
theorem pairing_const_pow_eq_one
    (τ : (⟨W⟩ : SmoothPlaneCurve F).FunctionField ≃+*
      (⟨W⟩ : SmoothPlaneCurve F).FunctionField)
    (g : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hg : g ≠ 0) (ℓ : ℕ) {c : F}
    (hc : τ g = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c * g)
    (hfix : τ (g ^ ℓ) = g ^ ℓ) :
    c ^ ℓ = 1 := by
  have h1 : τ (g ^ ℓ) =
      algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField (c ^ ℓ) * g ^ ℓ := by
    rw [map_pow, hc, mul_pow, map_pow]
  rw [hfix] at h1
  have h2 : (1 : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) * g ^ ℓ =
      algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField (c ^ ℓ) * g ^ ℓ := by
    rw [one_mul]
    exact h1
  have h3 := mul_right_cancel₀ (pow_ne_zero ℓ hg) h2
  exact ((algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField).injective
    (by rw [map_one]; exact h3)).symm

omit [DecidableEq F] in
/-- Scalars for two automorphisms multiply when the first fixes the base field. -/
theorem pairing_const_mul
    (τ₁ τ₂ τ₁₂ : (⟨W⟩ : SmoothPlaneCurve F).FunctionField ≃+*
      (⟨W⟩ : SmoothPlaneCurve F).FunctionField)
    (g : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hg : g ≠ 0) {c₁ c₂ c₁₂ : F}
    (hτ₁F : ∀ a : F, τ₁ (algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField a) =
      algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField a)
    (hcomp : ∀ x, τ₁₂ x = τ₁ (τ₂ x))
    (hc₁ : τ₁ g = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c₁ * g)
    (hc₂ : τ₂ g = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c₂ * g)
    (hc₁₂ :
      τ₁₂ g = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c₁₂ * g) :
    c₁₂ = c₁ * c₂ := by
  have hval : τ₁₂ g =
      algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField (c₁ * c₂) * g := by
    rw [hcomp, hc₂, map_mul, hτ₁F, hc₁, map_mul]
    ring
  rw [hc₁₂] at hval
  exact (algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField).injective
    (mul_right_cancel₀ hg hval)

omit [DecidableEq F] in
/-- Pairing scalars multiply across functions related by an invariant factor fixed by `τ`. -/
theorem pairing_const_mul_invariant_factor
    (τ : (⟨W⟩ : SmoothPlaneCurve F).FunctionField ≃+*
      (⟨W⟩ : SmoothPlaneCurve F).FunctionField)
    (g₁ g₂ g₁₂ u : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hg₁₂ : g₁₂ ≠ 0)
    {c c₁ c₂ c₁₂ : F}
    (hτF : ∀ a : F, τ (algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField a) =
      algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField a)
    (hτu : τ u = u)
    (hfact :
      g₁₂ = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c * (g₁ * g₂ * u))
    (hc₁ : τ g₁ = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c₁ * g₁)
    (hc₂ : τ g₂ = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c₂ * g₂)
    (hc₁₂ :
      τ g₁₂ = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c₁₂ * g₁₂) :
    c₁₂ = c₁ * c₂ := by
  have hval : τ g₁₂ =
      algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField (c₁ * c₂) * g₁₂ := by
    conv_lhs => rw [hfact, map_mul, map_mul, map_mul, hτF, hc₁, hc₂, hτu]
    rw [map_mul, hfact]
    ring
  rw [hc₁₂] at hval
  exact (algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField).injective
    (mul_right_cancel₀ hg₁₂ hval)

omit [DecidableEq F] in
/-- A scalar relating a nonzero function to itself is one. -/
theorem pairing_const_refl
    (g : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hg : g ≠ 0) {c : F}
    (hc : g = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c * g) :
    c = 1 := by
  apply (algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField).injective
  apply mul_right_cancel₀ hg
  simpa using hc.symm

end HasseWeil.WeilPairing
