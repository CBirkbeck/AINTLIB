/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.TranslateValuation
import HasseWeil.EC.TranslationOrd
import HasseWeil.Hasse.PoleDivisor2Tor

/-!
# Order-at-infinity transport under translation (Step (C))

This file discharges the deep order-at-infinity transport obligation
`IsTranslateOrdAtInftyCompatible`: for a finite smooth point `P` and a group
element `k` with `P + k = O`, the translation pullback `τ_k` carries the order
at `P` to the order at infinity:
```
  ord_P P (τ_k f) = ordAtInfty f          (when P + k = 0).
```

Geometrically the translation-by-`k` automorphism maps the place `P = -k` to
the place at infinity `O`, preserving order.

## Route

Both `ord_P` (DVR at a finite smooth point) and `ordAtInfty` (norm model at the
unique place at infinity) are normalised discrete valuations on `K(E)`, but they
use *different* local models, so the equality is not formal. We identify them
via the multiplicative `Valuation` packaging:

* `ν₂ := (pointValuation P).comap τ_k` and `ν₁ := ordAtInftyValuation` are two
  surjective `ℤᵐ⁰`-valued valuations on `K(E)`.
* The translation base cases (already shipped:
  `ord_P_translateX_xy_eq_neg_two_*`, `ord_P_translateY_xy_eq_neg_three_*`) give
  `ν₂ x_gen = exp 2 = ν₁ x_gen` and `ν₂ y_gen = exp 3 = ν₁ y_gen`, and `τ_k`
  fixing constants gives `ν₂` trivial on `F^×`.
* A *valuation determined by its values on `x_gen`, `y_gen`* lemma (proved here
  by the basis decomposition `f = r₁ + r₂·y_gen` and strict non-archimedean
  dominance — the cross-term parity makes the `min` unambiguous) forces
  `ν₂ = ν₁ = ordAtInftyValuation`.

Reading off the additive value gives `ord_P P (τ_k f) = ordAtInfty f`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8 (translation), IV.1
  (place at infinity).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-- `pointValuation P f = exp (-n)` from `ord_P P f = n` (for `f ≠ 0`). Curve-side
mirror of `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`, kept local to avoid an
import of `Hasse.L6Witnesses`. -/
theorem pointValuation_eq_exp_neg_of_ord_P_eq {C : Curves.SmoothPlaneCurve F} {P : C.SmoothPoint}
    {f : C.FunctionField} {n : ℤ} (hf : f ≠ 0) (hn : C.ord_P P f = (n : WithTop ℤ)) :
    C.pointValuation P f = WithZero.exp (-n) := by
  have hv : C.pointValuation P f ≠ 0 := (C.pointValuation P).ne_zero_iff.mpr hf
  have hord : C.ord_P P f = ((-(WithZero.unzero hv).toAdd : ℤ) : WithTop ℤ) := by
    unfold Curves.SmoothPlaneCurve.ord_P
    rw [dif_neg hv]
  have hneq : n = -(WithZero.unzero hv).toAdd := by exact_mod_cast (hord.symm.trans hn).symm
  rw [hneq, neg_neg, WithZero.exp, ofAdd_toAdd, WithZero.coe_unzero]

open Polynomial in
/-- **Polynomial valuation via the leading monomial.** If `w u = exp 2` and `w`
is trivial on nonzero constants, then `w (p(u)) = exp (2·natDeg p)` for nonzero `p`. -/
theorem valuation_aeval_eq_exp (w : Valuation KE (WithZero (Multiplicative ℤ))) (u : KE)
    (hu : w u = WithZero.exp 2) (hc : ∀ c : F, c ≠ 0 → w (algebraMap F KE c) = 1)
    {p : Polynomial F} (hp : p ≠ 0) :
    w (Polynomial.aeval u p) = WithZero.exp (2 * (p.natDegree : ℤ)) := by
  classical
  have h_term : ∀ i : ℕ, w (p.coeff i • u ^ i) =
      if p.coeff i = 0 then 0 else WithZero.exp (2 * (i : ℤ)) := by
    intro i
    rw [Algebra.smul_def, map_mul, map_pow, hu, ← WithZero.exp_nsmul]
    by_cases hci : p.coeff i = 0
    · rw [if_pos hci, hci, RingHom.map_zero, map_zero, zero_mul]
    · rw [if_neg hci, hc _ hci, one_mul]
      congr 1
      rw [nsmul_eq_mul]
      ring
  rw [aeval_eq_sum_range]
  set n := p.natDegree with hn
  have h_lead_ne : p.coeff n ≠ 0 := by
    rw [hn, ← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  refine (Valuation.map_sum_eq_of_lt w (Finset.self_mem_range_succ n) ?_).trans ?_
  · intro i hi
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hi
    rw [h_term i, h_term n, if_neg h_lead_ne]
    by_cases hci : p.coeff i = 0
    · rw [if_pos hci]
      exact lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
    · rw [if_neg hci, WithZero.exp_lt_exp]
      omega
  · rw [h_term n, if_neg h_lead_ne]

/-- `algebraMap (Polynomial F) K(E)` is `aeval x_gen` (both are the F-algebra hom
sending `X ↦ x_gen`). -/
theorem aeval_x_gen_eq_algebraMap (p : Polynomial F) :
    Polynomial.aeval (x_gen W) p = algebraMap (Polynomial F) W.toAffine.FunctionField p := by
  have h : (Polynomial.aeval (x_gen W)).toRingHom =
      algebraMap (Polynomial F) W.toAffine.FunctionField := by
    apply Polynomial.ringHom_ext'
    · ext c
      simp [Polynomial.aeval_C,
        IsScalarTower.algebraMap_apply F (Polynomial F) W.toAffine.FunctionField]
    · change Polynomial.aeval (x_gen W) Polynomial.X =
        algebraMap (Polynomial F) W.toAffine.FunctionField Polynomial.X
      rw [Polynomial.aeval_X]
      rfl
  exact DFunLike.congr_fun h p

/-- **Polynomial-image valuation**: for `w` with `w x_gen = exp 2` and `w`
trivial on `F^×`, the value on the image of a nonzero polynomial is
`exp (2·natDeg p)`. Specialisation of `valuation_aeval_eq_exp` at `u = x_gen`. -/
theorem valuation_algebraMap_polynomial_eq_exp (w : Valuation KE (WithZero (Multiplicative ℤ)))
    (hu : w (x_gen W) = WithZero.exp 2) (hc : ∀ c : F, c ≠ 0 → w (algebraMap F KE c) = 1)
    {p : Polynomial F} (hp : p ≠ 0) :
    w (algebraMap (Polynomial F) KE p) = WithZero.exp (2 * (p.natDegree : ℤ)) := by
  rw [← aeval_x_gen_eq_algebraMap W p]
  exact valuation_aeval_eq_exp W w (x_gen W) hu hc hp

private theorem ordAtInftyValuation_algebraMap_polynomial_eq_exp {q : Polynomial F} (hq : q ≠ 0) :
    (W_smooth W).ordAtInftyValuation (algebraMap (Polynomial F) KE q) =
      WithZero.exp (2 * (q.natDegree : ℤ)) := by
  have hq_ne : algebraMap (Polynomial F) KE q ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (Polynomial F) KE)]
    exact fun h ↦ hq (FaithfulSMul.algebraMap_injective (Polynomial F) KE h)
  rw [(W_smooth W).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hq_ne
    ((W_smooth W).ordAtInfty_algebraMap_polynomial_of_ne_zero hq)]
  congr 1
  ring

/-- **Numerator/denominator model in `K(E)`.** Any nonzero `r ∈ F(x) = Frac(F[X])`
is the image of a quotient of nonzero polynomials: there exist `p d : F[X]`, both
nonzero, with `algebraMap r = algebraMap p / algebraMap d` in `K(E)`. Obtained from
`IsLocalization.surj` plus the compatibility `algebraMap r · algebraMap d = algebraMap p`. -/
private theorem exists_polynomial_div_of_fracPolyX_ne_zero {r : FractionRing (Polynomial F)}
    (hr : r ≠ 0) : ∃ p d : Polynomial F, p ≠ 0 ∧ d ≠ 0 ∧
      algebraMap (FractionRing (Polynomial F)) KE r =
        algebraMap (Polynomial F) KE p / algebraMap (Polynomial F) KE d := by
  obtain ⟨⟨p, ⟨d, hd_mem⟩⟩, h_surj⟩ :=
    IsLocalization.surj (nonZeroDivisors (Polynomial F)) r
  have hd_ne : d ≠ 0 := nonZeroDivisors.ne_zero hd_mem
  have hp_ne : p ≠ 0 := by
    intro hp
    apply hr
    have h_zero :
        r * algebraMap (Polynomial F) (FractionRing (Polynomial F)) d = 0 := by
      rw [h_surj, hp, map_zero]
    rcases mul_eq_zero.mp h_zero with h | h
    · exact h
    · exact absurd h fun h' ↦
        hd_ne (FaithfulSMul.algebraMap_injective _ _ (h'.trans (map_zero _).symm))
  have h_KE :
      algebraMap (FractionRing (Polynomial F)) KE r *
        algebraMap (Polynomial F) KE d = algebraMap (Polynomial F) KE p := by
    rw [IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) KE d,
        IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) KE p,
        ← map_mul, h_surj]
  have h_alg_d_ne : algebraMap (Polynomial F) KE d ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (Polynomial F) KE)]
    exact fun h ↦ hd_ne (FaithfulSMul.algebraMap_injective (Polynomial F) KE h)
  refine ⟨p, d, hp_ne, hd_ne, ?_⟩
  rw [eq_div_iff h_alg_d_ne]
  exact h_KE

/-- **Quotient-of-polynomials value via the degree formula.** A `ℤᵐ⁰`-valued
valuation `v` on a field `L` over `F[X]` that takes the value `exp (2·natDeg q)` on
the image of every nonzero polynomial `q` takes the value `exp (2·(natDeg p − natDeg d))`
on `algebraMap p / algebraMap d` (for nonzero `p d`). Shared computation used for both
`w` and `ordAtInftyValuation` (stated over a generic `L` so it applies at either
spelling of the function field). -/
private theorem valuation_polynomial_div_eq_exp_sub {L : Type*} [Field L] [Algebra (Polynomial F) L]
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (hv : ∀ q : Polynomial F, q ≠ 0 →
      v (algebraMap (Polynomial F) L q) = WithZero.exp (2 * (q.natDegree : ℤ)))
    {p d : Polynomial F} (hp : p ≠ 0) (hd : d ≠ 0) :
    v (algebraMap (Polynomial F) L p / algebraMap (Polynomial F) L d) =
      WithZero.exp (2 * ((p.natDegree : ℤ) - (d.natDegree : ℤ))) := by
  rw [map_div₀, hv p hp, hv d hd, ← WithZero.exp_sub]
  congr 1
  ring

/-- **Rational-image valuation agreement.** For `w` with `w x_gen = exp 2` and
`w` trivial on `F^×`, the value on the image of any `r ∈ F(x) = Frac(F[X])`
agrees with `ordAtInftyValuation`. -/
theorem valuation_algebraMap_fracPolyX_eq_ordAtInftyValuation
    (w : Valuation KE (WithZero (Multiplicative ℤ))) (hu : w (x_gen W) = WithZero.exp 2)
    (hc : ∀ c : F, c ≠ 0 → w (algebraMap F KE c) = 1) (r : FractionRing (Polynomial F)) :
    w (algebraMap (FractionRing (Polynomial F)) KE r) =
      (W_smooth W).ordAtInftyValuation
        (algebraMap (FractionRing (Polynomial F)) KE r) := by
  rcases eq_or_ne r 0 with hr | hr
  · subst hr
    rw [map_zero]
    exact (map_zero _).trans (map_zero _).symm
  obtain ⟨p, d, hp_ne, hd_ne, h_r_div⟩ := exists_polynomial_div_of_fracPolyX_ne_zero W hr
  have hL : w (algebraMap (FractionRing (Polynomial F)) KE r) =
      WithZero.exp (2 * ((p.natDegree : ℤ) - (d.natDegree : ℤ))) := by
    rw [h_r_div]
    exact valuation_polynomial_div_eq_exp_sub w
      (fun q hq ↦ valuation_algebraMap_polynomial_eq_exp W w hu hc hq) hp_ne hd_ne
  have hR : (W_smooth W).ordAtInftyValuation (algebraMap (FractionRing (Polynomial F)) KE r) =
      WithZero.exp (2 * ((p.natDegree : ℤ) - (d.natDegree : ℤ))) := by
    rw [h_r_div]
    exact valuation_polynomial_div_eq_exp_sub (W_smooth W).ordAtInftyValuation
      (fun q hq ↦ ordAtInftyValuation_algebraMap_polynomial_eq_exp W hq) hp_ne hd_ne
  rw [hL, hR]

/-- **Parity distinctness.** The two summands of the basis decomposition have
distinct `ordAtInftyValuation`: `ord_∞(algMap r₁)` is even while
`ord_∞(algMap r₂ · coordY)` is odd, so unless the whole element is zero the
multiplicative values differ. -/
theorem ordAtInftyValuation_basis_summands_distinct {r₁ r₂ : FractionRing (Polynomial F)}
    (h_ne : ¬ (r₁ = 0 ∧ r₂ = 0)) :
    (W_smooth W).ordAtInftyValuation
        (algebraMap (FractionRing (Polynomial F)) (W_smooth W).FunctionField r₁) ≠
      (W_smooth W).ordAtInftyValuation
        (algebraMap (FractionRing (Polynomial F)) (W_smooth W).FunctionField r₂ *
          (W_smooth W).coordYInFunctionField) := by
  by_cases hr₁ : r₁ = 0
  · have hβ_ne :
        algebraMap (FractionRing (Polynomial F)) (W_smooth W).FunctionField r₂ ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap (FractionRing (Polynomial F)) (W_smooth W).FunctionField)]
      exact fun h ↦ (fun h' ↦ h_ne ⟨hr₁, h'⟩) (FaithfulSMul.algebraMap_injective _ _ h)
    rw [hr₁, map_zero, map_zero]
    exact Ne.symm ((W_smooth W).ordAtInftyValuation_ne_zero
      (mul_ne_zero hβ_ne (W_smooth W).coordYInFunctionField_ne_zero))
  · have hα_ne :
        algebraMap (FractionRing (Polynomial F)) (W_smooth W).FunctionField r₁ ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap (FractionRing (Polynomial F)) (W_smooth W).FunctionField)]
      exact fun h ↦ hr₁ (FaithfulSMul.algebraMap_injective _ _ h)
    have hα_ord : (W_smooth W).ordAtInfty
        (algebraMap (FractionRing (Polynomial F)) (W_smooth W).FunctionField r₁) =
        ((-2 * RatFunc.intDegree (RatFunc.ofFractionRing r₁) : ℤ) : WithTop ℤ) :=
      (W_smooth W).ordAtInfty_algebraMap_fracPolyX_of_ne_zero hr₁
    by_cases hr₂ : r₂ = 0
    · rw [hr₂, map_zero, zero_mul, map_zero]
      exact (W_smooth W).ordAtInftyValuation_ne_zero hα_ne
    · have hβ_ne :
          algebraMap (FractionRing (Polynomial F)) (W_smooth W).FunctionField r₂ ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap (FractionRing (Polynomial F)) (W_smooth W).FunctionField)]
        exact fun h ↦ hr₂ (FaithfulSMul.algebraMap_injective _ _ h)
      have hβc_ne : algebraMap (FractionRing (Polynomial F)) (W_smooth W).FunctionField r₂ *
          (W_smooth W).coordYInFunctionField ≠ 0 :=
        mul_ne_zero hβ_ne (W_smooth W).coordYInFunctionField_ne_zero
      have hβc_ord : (W_smooth W).ordAtInfty
          (algebraMap (FractionRing (Polynomial F)) (W_smooth W).FunctionField r₂ *
            (W_smooth W).coordYInFunctionField) =
          ((-2 * RatFunc.intDegree (RatFunc.ofFractionRing r₂) + (-3) : ℤ) :
            WithTop ℤ) := by
        rw [(W_smooth W).ordAtInfty_mul hβ_ne (W_smooth W).coordYInFunctionField_ne_zero,
            (W_smooth W).ordAtInfty_coordYInFunctionField,
            (W_smooth W).ordAtInfty_algebraMap_fracPolyX_of_ne_zero hr₂, ← WithTop.coe_add]
      rw [(W_smooth W).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hα_ne hα_ord,
          (W_smooth W).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hβc_ne hβc_ord,
          Ne, WithZero.exp_inj]
      intro h_eq
      omega

/-- **Value on the coordinate function `y`.** A valuation `w` with `w y_gen = exp 3`
agrees with `ordAtInftyValuation` on `coordYInFunctionField` (which is `y_gen`):
both equal `exp (-3)`. -/
private theorem valuation_coordYInFunctionField_eq_ordAtInftyValuation
    (w : Valuation KE (WithZero (Multiplicative ℤ))) (hy : w (y_gen W) = WithZero.exp 3) :
    w (W_smooth W).coordYInFunctionField =
      (W_smooth W).ordAtInftyValuation (W_smooth W).coordYInFunctionField := by
  have h_yeq : (W_smooth W).coordYInFunctionField = y_gen W := by
    rw [← (W_smooth W).coordY_eq_coordYInFunctionField]
    exact coordY_W_smooth_eq_y_gen W
  rw [h_yeq, hy,
    (W_smooth W).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq
      (h_yeq ▸ (W_smooth W).coordYInFunctionField_ne_zero)
      (by rw [← h_yeq]; exact (W_smooth W).ordAtInfty_coordYInFunctionField)]
  norm_num

/-- **Two valuations agreeing on factors agree on the product.** If `w` and `v`
take the same value on `a` and on `b`, they take the same value on `a * b`
(multiplicativity on both sides). -/
private theorem valuation_eq_mul_of_eq_of_eq
    (w v : Valuation KE (WithZero (Multiplicative ℤ))) {a b : KE}
    (ha : w a = v a) (hb : w b = v b) : w (a * b) = v (a * b) := by
  rw [map_mul w, map_mul v, ha, hb]

/-- **Two valuations agreeing on distinctly-valued summands agree on the sum.**
If `w` and `v` agree on `a` and on `b`, and `v` separates them (`v a ≠ v b`),
then both valuations read off `a + b` as the *same* maximum of agreeing
summand-values, so they agree on `a + b` too (strict non-archimedean
dominance via `map_add_of_distinct_val`). -/
private theorem valuation_eq_add_of_eq_of_eq_of_distinct
    (w v : Valuation KE (WithZero (Multiplicative ℤ))) {a b : KE}
    (ha : w a = v a) (hb : w b = v b) (h_dist : v a ≠ v b) :
    w (a + b) = v (a + b) := by
  have h_dist_w : w a ≠ w b := by rw [ha, hb]; exact h_dist
  rw [Valuation.map_add_of_distinct_val w h_dist_w,
    Valuation.map_add_of_distinct_val v h_dist, ha, hb]

/-- **Extension from generators to all of `K(E)`.** A valuation `w` that agrees
with `ordAtInftyValuation` on every `F(x)`-rational image (`h_rat`) and on the
coordinate function `coordYInFunctionField` (`h_coordY`) agrees everywhere. The
decomposition `f = α + β·coordY` (`α, β ∈ F(x)`, via `exists_decomp`) plus the
parity-distinctness of the two summands (`ordAtInftyValuation_basis_summands_distinct`)
lets `map_add_of_distinct_val` read off both valuations as the *same* maximum of
agreeing summand-values. -/
private theorem eq_ordAtInftyValuation_of_agree_fracPolyX_coordY
    (w : Valuation KE (WithZero (Multiplicative ℤ)))
    (h_rat : ∀ r : FractionRing (Polynomial F),
      w (algebraMap (FractionRing (Polynomial F)) KE r) =
        (W_smooth W).ordAtInftyValuation (algebraMap (FractionRing (Polynomial F)) KE r))
    (h_coordY : w (W_smooth W).coordYInFunctionField =
      (W_smooth W).ordAtInftyValuation (W_smooth W).coordYInFunctionField) :
    w = (W_smooth W).ordAtInftyValuation := by
  apply Valuation.ext
  intro f
  obtain ⟨p, q, hf⟩ := (W_smooth W).exists_decomp f
  set α : (W_smooth W).FunctionField :=
    algebraMap (FractionRing (Polynomial F)) (W_smooth W).FunctionField p with hα
  set β : (W_smooth W).FunctionField :=
    algebraMap (FractionRing (Polynomial F)) (W_smooth W).FunctionField q with hβ
  have hf_eq : f = α + β * (W_smooth W).coordYInFunctionField := by
    rw [hf, Algebra.smul_def, mul_one, Algebra.smul_def]
  rw [hf_eq]
  rcases eq_or_ne f 0 with hf0 | hf0
  · rw [hf_eq] at hf0
    rw [hf0]
    exact (map_zero w).trans (map_zero _).symm
  · have h_not_both : ¬ (p = 0 ∧ q = 0) := by
      rintro ⟨hp0, hq0⟩
      apply hf0
      rw [(hf : f = p • (1 : (W_smooth W).FunctionField) +
        q • (W_smooth W).coordYInFunctionField), hp0, hq0, zero_smul, zero_smul, zero_add]
      rfl
    have hβc_agree : w (β * (W_smooth W).coordYInFunctionField) =
        (W_smooth W).ordAtInftyValuation (β * (W_smooth W).coordYInFunctionField) :=
      valuation_eq_mul_of_eq_of_eq W w (W_smooth W).ordAtInftyValuation (h_rat q) h_coordY
    exact valuation_eq_add_of_eq_of_eq_of_distinct W w (W_smooth W).ordAtInftyValuation
      (h_rat p) hβc_agree (ordAtInftyValuation_basis_summands_distinct W h_not_both)

/-- **Valuation determined by `x_gen`, `y_gen`.** A `ℤᵐ⁰`-valued valuation `w` on
`K(E)` with `w x_gen = exp 2`, `w y_gen = exp 3`, and trivial on `F^×` equals
`ordAtInftyValuation`. The decomposition `f = α + β·coordY` (`α, β ∈ F(x)`) plus
the parity-distinctness of the two summands lets `map_add_of_distinct_val` read
off both valuations as the *same* maximum of agreeing summand-values. -/
theorem eq_ordAtInftyValuation_of_x_y (w : Valuation KE (WithZero (Multiplicative ℤ)))
    (hx : w (x_gen W) = WithZero.exp 2) (hy : w (y_gen W) = WithZero.exp 3)
    (hc : ∀ c : F, c ≠ 0 → w (algebraMap F KE c) = 1) :
    w = (W_smooth W).ordAtInftyValuation :=
  eq_ordAtInftyValuation_of_agree_fracPolyX_coordY W w
    (valuation_algebraMap_fracPolyX_eq_ordAtInftyValuation W w hx hc)
    (valuation_coordYInFunctionField_eq_ordAtInftyValuation W w hy)

/-- `ord_P (-T) (τ_T x_gen) = -2`, uniformly across 2-torsion and non-2-torsion
`T = (xk, yk)`. Dispatches to the two shipped cases. -/
theorem ord_P_negSmoothPoint_translateX_xy_eq_neg_two
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (translateX_xy W xk yk) = ((-2 : ℤ) : WithTop ℤ) := by
  by_cases h : yk = W.toAffine.negY xk yk
  · exact ord_P_translateX_xy_eq_neg_two_at_2tor W xk yk h_ns h
  · exact ord_P_translateX_xy_eq_neg_two_of_non_2_tor W xk yk h_ns h

/-- `ord_P (-T) (τ_T y_gen) = -3`, uniformly across 2-torsion and non-2-torsion. -/
theorem ord_P_negSmoothPoint_translateY_xy_eq_neg_three
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (translateY_xy W xk yk) = ((-3 : ℤ) : WithTop ℤ) := by
  by_cases h : yk = W.toAffine.negY xk yk
  · exact ord_P_translateY_xy_eq_neg_three_at_2tor W xk yk h_ns h
  · exact ord_P_translateY_xy_eq_neg_three_of_non_2_tor W xk yk h_ns h

private theorem ne_zero_of_ord_P_eq_coe {P : (W_smooth W).SmoothPoint}
    {g : (W_smooth W).FunctionField} {n : ℤ}
    (h : (W_smooth W).ord_P P g = (n : WithTop ℤ)) : g ≠ 0 := fun h0 ↦
  WithTop.coe_ne_top (h.symm.trans ((Curves.SmoothPlaneCurve.ord_P_eq_top_iff g).mpr h0))

/-- The translation pullback `τ_T` (`T = some xk yk h_ns`) carries `pointValuation`
at `-T = negSmoothPoint` to `ordAtInftyValuation`. -/
theorem pointValuation_comap_translateAlgEquivOfPoint_some_eq_ordAtInftyValuation (xk yk : F)
    (h_ns : W.toAffine.Nonsingular xk yk) :
    ((W_smooth W).pointValuation (negSmoothPoint W xk yk h_ns)).comap
        (translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns)).toAlgHom.toRingHom =
      (W_smooth W).ordAtInftyValuation := by
  set P := negSmoothPoint W xk yk h_ns with hP
  set τ := translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) with hτ
  set w := ((W_smooth W).pointValuation P).comap τ.toAlgHom.toRingHom with hw
  have hw_apply : ∀ g : KE, w g = (W_smooth W).pointValuation P (τ g) := fun g ↦ by
    rw [hw]
    exact Valuation.comap_apply _ _ _
  refine eq_ordAtInftyValuation_of_x_y W w ?_ ?_ ?_
  · rw [hw_apply, show τ (x_gen W) = translateX_xy W xk yk from
      translateAlgEquivOfPoint_apply_x_gen W xk yk h_ns]
    have h_ord : (W_smooth W).ord_P P (translateX_xy W xk yk) = ((-2 : ℤ) : WithTop ℤ) :=
      ord_P_negSmoothPoint_translateX_xy_eq_neg_two W xk yk h_ns
    rw [pointValuation_eq_exp_neg_of_ord_P_eq (C := W_smooth W) (P := P)
      (ne_zero_of_ord_P_eq_coe W h_ord) h_ord]
    norm_num
  · rw [hw_apply, show τ (y_gen W) = translateY_xy W xk yk from
      translateAlgEquivOfPoint_apply_y_gen W xk yk h_ns]
    have h_ord : (W_smooth W).ord_P P (translateY_xy W xk yk) = ((-3 : ℤ) : WithTop ℤ) :=
      ord_P_negSmoothPoint_translateY_xy_eq_neg_three W xk yk h_ns
    rw [pointValuation_eq_exp_neg_of_ord_P_eq (C := W_smooth W) (P := P)
      (ne_zero_of_ord_P_eq_coe W h_ord) h_ord]
    norm_num
  · intro c hc
    rw [hw_apply, show τ (algebraMap F KE c) = algebraMap F KE c from τ.commutes c]
    have h_ord : (W_smooth W).ord_P P (algebraMap F KE c) = ((0 : ℤ) : WithTop ℤ) :=
      Curves.SmoothPlaneCurve.ord_P_algebraMap_F_of_ne_zero (W_smooth W) hc P
    rw [pointValuation_eq_exp_neg_of_ord_P_eq (C := W_smooth W) (P := P)
      (ne_zero_of_ord_P_eq_coe W h_ord) h_ord]
    norm_num

/-- **Pointwise order transport at infinity** (`T = some xk yk h_ns`, the
substantive nonzero-`f` core): `ord_P (-T) (τ_T f) = ordAtInfty f`. -/
theorem ord_P_negSmoothPoint_translateAlgEquivOfPoint_eq_ordAtInfty_some
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) (f : KE) (hf : f ≠ 0) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) f) =
      (W_smooth W).ordAtInfty f := by
  set P := negSmoothPoint W xk yk h_ns with hP
  set τ := translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) with hτ
  have h_at_f : (W_smooth W).pointValuation P (τ f) =
      (W_smooth W).ordAtInftyValuation f := by
    have := DFunLike.congr_fun
      (pointValuation_comap_translateAlgEquivOfPoint_some_eq_ordAtInftyValuation W xk yk h_ns) f
    rwa [Valuation.comap_apply] at this
  have hτf_ne : τ f ≠ 0 := fun h0 ↦ hf (τ.injective (h0.trans (map_zero τ).symm))
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (W_smooth W).ord_P P (τ f) = (m : WithTop ℤ) := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      ((Curves.SmoothPlaneCurve.ord_P_eq_top_iff (τ f)).not.mpr hτf_ne)
    exact ⟨m, hm.symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (W_smooth W).ordAtInfty f = (n : WithTop ℤ) :=
    ⟨_, (W_smooth W).ordAtInfty_of_ne hf⟩
  rw [pointValuation_eq_exp_neg_of_ord_P_eq (C := W_smooth W) (P := P) hτf_ne hm,
    (W_smooth W).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hf hn, WithZero.exp_inj] at h_at_f
  rw [hm, hn]
  exact_mod_cast neg_injective h_at_f

/-- **Unconditional discharge of `IsTranslateOrdAtInftyCompatible`.** For a finite
smooth point `P` and a group element `k` with `P + k = O` (so `P = -k`), the
translation pullback `τ_k` carries the order at `P` to the order at infinity:
`ord_P P (τ_k f) = ordAtInfty f` for all `f`. Gates the Weil-pairing divisor
transport. -/
theorem isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h_zero : P.toAffinePoint + k = Affine.Point.zero) :
    IsTranslateOrdAtInftyCompatible W P k h_zero := by
  have hk_eq : k = -P.toAffinePoint := (neg_eq_of_add_eq_zero_right h_zero).symm
  obtain ⟨xk, yk, h_ns, hk_some⟩ :
      ∃ xk yk, ∃ h_ns : W.toAffine.Nonsingular xk yk,
        k = Affine.Point.some xk yk h_ns ∧
          P = negSmoothPoint W xk yk h_ns := by
    refine ⟨P.x, W.toAffine.negY P.x P.y,
      (Affine.nonsingular_neg P.x P.y).mpr P.nonsingular, ?_, ?_⟩
    · rw [hk_eq, Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def]
      exact neg_some_eq_some W P.x P.y P.nonsingular
    · apply Curves.SmoothPlaneCurve.SmoothPoint.ext
      · rw [negSmoothPoint_x]
      · rw [negSmoothPoint_y, W.toAffine.negY_negY]
  obtain ⟨hk_some, hP_some⟩ := hk_some
  apply isTranslateOrdAtInftyCompatible_of_nonzero_pointwise_eq
  intro f hf
  rw [hk_some, hP_some]
  exact ord_P_negSmoothPoint_translateAlgEquivOfPoint_eq_ordAtInfty_some W xk yk h_ns f hf

end HasseWeil
