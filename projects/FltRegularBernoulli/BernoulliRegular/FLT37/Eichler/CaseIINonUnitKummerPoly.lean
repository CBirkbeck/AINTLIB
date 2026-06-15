import FltRegular.NumberTheory.KummersLemma.Field
import FltRegular.NumberTheory.Unramified
import Mathlib.FieldTheory.KummerExtension

/-!
# [FLT37-CASEII-NONUNIT-POLY] flt-regular's Kummer `poly` for a non-unit primary radical

flt-regular's `KummersLemma.poly` (and the unramifiedness it feeds) is parameterised by a **unit**
`u : (𝓞 K)ˣ`.  The *only* steps that use unit-ness are `roots_poly`'s degenerate `α = 0` branch and
`separable_poly_aux`'s `IsUnit (⟨α,_⟩ : 𝓞 L)` step (which makes the root differences global units).

This file rebuilds the construction for an **integral, primary, non-unit** radical `a : 𝓞 K`
(`a ≠ 0`, `(ζ-1)^p ∣ a - 1`, `X^p - a` having no `p`-th root in `K`).  Everything from the
`(ζ-1)^p`-divisibility of the defining polynomial through the minimal-polynomial identification goes
through verbatim with `(u : 𝓞 K)` replaced by `a` — the unit-ness is *not* used there.  The
separability that *did* use the global unit is replaced, at a single maximal ideal `I`, by the
**local** unit-ness of the radical (the root differences are units modulo `I` exactly when the
radical is an `I`-unit, which at `I = (ζ-1)` follows from primarity since `(ζ-1) ∤ a`).

This is the non-unit generalisation of flt-regular `KummersLemma.separable_poly_aux` /
`KummersLemma.isUnramified` needed by the Case-II ideal-theoretic Lemma 9.1 at the prime over `37`.

## References
* flt-regular, `FltRegular.NumberTheory.KummersLemma.Field`.
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (Lemma 9.1).
-/

@[expose] public section

open scoped NumberField nonZeroDivisors
open Polynomial

namespace BernoulliRegular.FLT37.Eichler.NonUnitKummer

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K] (hp : p ≠ 2)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : 𝓞 K)
  (hcong : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (a : 𝓞 K) - 1)
  (hu : ∀ v : K, v ^ p ≠ algebraMap (𝓞 K) K a)

include hcong hp in
/-- `(ζ-1)^p` divides the defining polynomial `(C(ζ-1)·X - 1)^p + C a` (verbatim flt-regular
`zeta_sub_one_pow_dvd_poly`, with the unit `u` replaced by the element `a`). -/
lemma zeta_sub_one_pow_dvd_poly [IsCyclotomicExtension {p} ℚ K] :
    C ((hζ.toInteger - 1 : 𝓞 K) ^ p) ∣
      (C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (a : 𝓞 K) := by
  rw [← dvd_sub_left (_root_.map_dvd C hcong), add_sub_assoc, C.map_sub (a : 𝓞 K), ← sub_add,
    sub_self, map_one, zero_add]
  refine dvd_C_mul_X_sub_one_pow_add_one hpri.out hp _ _ dvd_rfl ?_
  convert mul_dvd_mul_right (associated_zeta_sub_one_pow_prime hζ).dvd _
  rw [← pow_succ, tsub_add_cancel_of_le (Nat.Prime.one_lt hpri.out).le]

variable [IsCyclotomicExtension {p} ℚ K]

/-- The flt-regular Kummer polynomial for the non-unit radical `a`. -/
noncomputable def poly : (𝓞 K)[X] := (zeta_sub_one_pow_dvd_poly hp hζ a hcong).choose

lemma poly_spec :
    C ((hζ.toInteger - 1 : 𝓞 K) ^ p) * poly hp hζ a hcong =
      (C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (a : 𝓞 K) :=
  (zeta_sub_one_pow_dvd_poly hp hζ a hcong).choose_spec.symm

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
lemma natDegree_poly_aux :
    natDegree ((C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (a : 𝓞 K)) = p := by
  haveI : Fact (Nat.Prime p) := hpri
  rw [natDegree_add_C, natDegree_pow, ← C.map_one, natDegree_sub_C, natDegree_mul_X, natDegree_C,
    zero_add, mul_one]
  exact C_ne_zero.mpr (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
lemma monic_poly_aux :
    leadingCoeff ((C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (a : 𝓞 K)) =
      (hζ.toInteger - 1 : 𝓞 K) ^ p := by
  haveI : Fact (Nat.Prime p) := hpri
  trans leadingCoeff ((C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p)
  · rw [leadingCoeff, leadingCoeff, coeff_add]
    nth_rewrite 1 [natDegree_add_C]
    convert add_zero _ using 2
    rw [natDegree_poly_aux hζ, coeff_C, if_neg (NeZero.pos p).ne.symm]
  · rw [leadingCoeff_pow, ← C.map_one, leadingCoeff, natDegree_sub_C, natDegree_mul_X]
    · simp only [map_one, natDegree_C, zero_add, coeff_sub, coeff_mul_X, coeff_C, coeff_one,
        sub_zero, one_ne_zero, ↓reduceIte]
    · exact C_ne_zero.mpr (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)

lemma monic_poly : Monic (poly hp hζ a hcong) := by
  haveI : Fact (Nat.Prime p) := hpri
  have := congr_arg leadingCoeff (poly_spec hp hζ a hcong)
  simp only [map_pow, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_C,
    monic_poly_aux hζ a] at this
  refine mul_right_injective₀ ?_ (this.trans (mul_one _).symm)
  exact pow_ne_zero _ (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)

lemma natDegree_poly : natDegree (poly hp hζ a hcong) = p := by
  haveI : Fact (Nat.Prime p) := hpri
  have := congr_arg natDegree (poly_spec hp hζ a hcong)
  rwa [natDegree_C_mul, natDegree_poly_aux hζ] at this
  exact pow_ne_zero _ (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)

lemma map_poly : (poly hp hζ a hcong).map (algebraMap (𝓞 K) K) =
    (X - C (1 / (ζ - 1))) ^ p + C (algebraMap (𝓞 K) K a / (ζ - 1) ^ p : K) := by
  ext i
  have := congr_arg (fun P : (𝓞 K)[X] ↦ (↑(coeff P i) : K)) (poly_spec hp hζ a hcong)
  change _ = algebraMap (𝓞 K) K _ at this
  rw [← coeff_map] at this
  replace this : (ζ - 1) ^ p * ↑((poly hp hζ a hcong).coeff i) =
    (((C ζ - 1) * X - 1) ^ p).coeff i +
    (C ((algebraMap ((𝓞 K)) K) a)).coeff i := by
      simp only [map_pow, map_sub, map_one, Polynomial.map_add, Polynomial.map_pow,
        Polynomial.map_sub, Polynomial.map_mul, map_C,
        Polynomial.map_one, map_X, coeff_add] at this
      convert this
      · simp only [← Polynomial.coeff_map]
        simp only [coeff_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_C,
          Polynomial.map_one]
        rw [← Polynomial.coeff_map, mul_comm, ← Polynomial.coeff_mul_C, mul_comm]
        simp
      · rfl
  apply mul_right_injective₀ (pow_ne_zero p (hζ.sub_one_ne_zero hpri.out.one_lt))
  simp only [coeff_map, one_div, coeff_add, this, mul_add]
  simp_rw [← smul_eq_mul (α := K), ← coeff_smul]
  rw [smul_C, smul_eq_mul, ← _root_.smul_pow, ← mul_div_assoc, mul_div_cancel_left₀, smul_sub,
    smul_C, smul_eq_mul, mul_inv_cancel₀, map_one, Algebra.smul_def, ← C_eq_algebraMap, map_sub,
    map_one]
  · exact hζ.sub_one_ne_zero hpri.out.one_lt
  · exact pow_ne_zero _ (hζ.sub_one_ne_zero hpri.out.one_lt)

include hu in
lemma irreducible_map_poly :
    Irreducible ((poly hp hζ a hcong).map (algebraMap (𝓞 K) K)) := by
  rw [map_poly]
  refine Irreducible.of_map (f := algEquivAevalXAddC (1 / (ζ - 1))) ?_
  simp only [one_div, map_add, algEquivAevalXAddC_apply, map_pow, map_sub, aeval_X, aeval_C,
    algebraMap_eq, add_sub_cancel_right]
  rw [← sub_neg_eq_add, ← (C : K →+* _).map_neg]
  apply X_pow_sub_C_irreducible_of_prime hpri.out
  intro b hb
  apply hu (- b * (ζ - 1))
  rw [mul_pow, (hpri.out.odd_of_ne_two hp).neg_pow, hb, neg_neg,
    div_mul_cancel₀ _ (pow_ne_zero _ (hζ.sub_one_ne_zero hpri.out.one_lt))]

theorem aeval_poly {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L (algebraMap (𝓞 K) K a)) (m : ℕ) :
    aeval (((1 : L) - ζ ^ m • α) / (algebraMap K L (ζ - 1))) (poly hp hζ a hcong) = 0 := by
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  rw [map_sub, map_one]
  have := congr_arg (aeval ((1 - ζ ^ m • α) / (algebraMap K L (ζ - 1))))
    (poly_spec hp hζ a hcong)
  have hcoe : (algebraMap (𝓞 K) L) (↑hζ.toInteger) = algebraMap K L ζ := rfl
  have hcoe1 : (algebraMap (𝓞 K) L) a = algebraMap K L (algebraMap (𝓞 K) K a) := rfl
  simp only [map_sub, map_one, map_pow, map_mul, aeval_C, _root_.smul_pow, hcoe, e, hcoe1, map_add,
    aeval_X, ← mul_div_assoc, mul_div_cancel_left₀ _ hζ', sub_sub_cancel_left,
    (hpri.out.odd_of_ne_two hp).neg_pow] at this
  rw [← pow_mul, mul_comm m, pow_mul, hζ.pow_eq_one, one_pow, one_smul, neg_add_cancel,
    mul_eq_zero] at this
  exact this.resolve_left (pow_ne_zero _ hζ')

/-- The flt-regular Kummer root `(1 - ζ^m·α)/(ζ-1) ∈ 𝓞 L` for the non-unit radical. -/
def polyRoot {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L (algebraMap (𝓞 K) K a)) (m : ℕ) : 𝓞 L :=
  ⟨((1 : L) - ζ ^ m • α) / (algebraMap K L (ζ - 1)), isIntegral_trans _
      ⟨poly hp hζ a hcong, monic_poly hp hζ a hcong, aeval_poly hp hζ a hcong α e m⟩⟩

theorem roots_poly {L : Type*} [Field L] [Algebra K L] (ha : a ≠ 0) (α : L)
    (e : α ^ p = algebraMap K L (algebraMap (𝓞 K) K a)) :
    roots ((poly hp hζ a hcong).map (algebraMap (𝓞 K) L)) =
      (Finset.range p).val.map
        (fun i ↦ ((1 : L) - ζ ^ i • α) / (algebraMap K L (ζ - 1))) := by
  by_cases hα : α = 0
  · rw [hα, zero_pow (NeZero.ne p)] at e
    have hne : algebraMap K L (algebraMap (𝓞 K) K a) ≠ 0 := by
      have : algebraMap K L (algebraMap (𝓞 K) K a) = algebraMap (𝓞 K) L a := by
        rw [← (algebraMap K L).comp_apply, ← IsScalarTower.algebraMap_eq]
      rw [this, map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) L)]
      exact ha
    exact absurd e.symm hne
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  classical
  symm; apply Multiset.eq_of_le_of_card_le
  · rw [← Finset.image_val_of_injOn, Finset.val_le_iff_val_subset]
    · intro x hx
      simp only [Finset.image_val, Finset.range_val, Multiset.mem_dedup, Multiset.mem_map,
        Multiset.mem_range] at hx
      obtain ⟨m, _, rfl⟩ := hx
      rw [mem_roots, IsRoot.def, eval_map, ← aeval_def, aeval_poly hp hζ a hcong α e]
      exact ((monic_poly hp hζ a hcong).map (algebraMap (𝓞 K) L)).ne_zero
    · intros i hi j hj e'
      apply (hζ.map_of_injective (algebraMap K L).injective).injOn_pow_mul hα hi hj
      apply_fun (1 - · * (algebraMap K L ζ - 1)) at e'
      dsimp only at e'
      simpa only [Nat.cast_one, map_sub, map_one, Algebra.smul_def, map_pow,
        div_mul_cancel₀ _ hζ', sub_sub_cancel] using e'
  · simp only [Finset.range_val, Multiset.card_map, Multiset.card_range]
    refine (Polynomial.card_roots' _).trans ?_
    rw [(monic_poly hp hζ a hcong).natDegree_map, natDegree_poly hp hζ]

theorem splits_poly {L : Type*} [Field L] [Algebra K L] (ha : a ≠ 0) (α : L)
    (e : α ^ p = algebraMap K L (algebraMap (𝓞 K) K a)) :
    ((poly hp hζ a hcong).map (algebraMap (𝓞 K) L)).Splits := by
  rw [splits_iff_card_roots, roots_poly hp hζ a hcong ha α e,
    (monic_poly hp hζ a hcong).natDegree_map, natDegree_poly hp hζ,
    Finset.range_val, Multiset.card_map, Multiset.card_range]

theorem map_poly_eq_prod {L : Type*} [Field L] [Algebra K L] (ha : a ≠ 0) (α : L)
    (e : α ^ p = algebraMap K L (algebraMap (𝓞 K) K a)) :
    (poly hp hζ a hcong).map (algebraMap (𝓞 K) (𝓞 L)) =
      ∏ i ∈ Finset.range p, (X - C (polyRoot hp hζ a hcong α e i)) := by
  apply map_injective (algebraMap (𝓞 L) L) Subtype.coe_injective
  rw [← coe_mapRingHom, map_prod, coe_mapRingHom, map_map, ← IsScalarTower.algebraMap_eq,
    (splits_poly hp hζ a hcong ha α e).eq_prod_roots_of_monic ((monic_poly hp hζ a hcong).map _),
    roots_poly hp hζ a hcong ha α e, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  simp [polyRoot]

include hu in
lemma minpoly_polyRoot'' {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L (algebraMap (𝓞 K) K a)) (i) :
    minpoly K (polyRoot hp hζ a hcong α e i : L) =
      (poly hp hζ a hcong).map (algebraMap (𝓞 K) K) := by
  have : IsIntegral K (polyRoot hp hζ a hcong α e i : L) :=
    IsIntegral.tower_top (polyRoot hp hζ a hcong α e i).prop
  apply eq_of_monic_of_associated (minpoly.monic this) ((monic_poly hp hζ a hcong).map _)
  refine Irreducible.associated_of_dvd (minpoly.irreducible this)
    (irreducible_map_poly hp hζ a hcong hu) (minpoly.dvd _ _ ?_)
  rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq, ← aeval_def]
  exact aeval_poly hp hζ a hcong α e i

include hu in
lemma minpoly_polyRoot' {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L (algebraMap (𝓞 K) K a)) (i) :
    minpoly (𝓞 K) (polyRoot hp hζ a hcong α e i : L) = (poly hp hζ a hcong) := by
  apply map_injective (algebraMap (𝓞 K) K) Subtype.coe_injective
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' K]
  · exact minpoly_polyRoot'' hp hζ a hcong hu α e i
  · exact IsIntegral.tower_top (polyRoot hp hζ a hcong α e i).prop

/-- **The root-difference is `(unit)·(radical)`** (the unit-free core of `separable_poly_aux`).  For
`m ≠ n`, `polyRoot m - polyRoot n = (algebraMap v)·αO` in `𝓞 L`, where `v` is the unit witnessing
`Associated (ζ-1) (ζ^n - ζ^m)` and `αO ∈ 𝓞 L` is the radical (`αO.val = α`).  No unit-ness of `a` is
used. -/
lemma polyRoot_sub_eq {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L (algebraMap (𝓞 K) K a)) (m n : ℕ)
    (αO : 𝓞 L) (hαO : (αO : L) = α) (v : (𝓞 K)ˣ)
    (hv : (ζ - 1) * ((v : 𝓞 K) : K) = ζ ^ n - ζ ^ m) :
    polyRoot hp hζ a hcong α e m - polyRoot hp hζ a hcong α e n =
      algebraMap (𝓞 K) (𝓞 L) (v : 𝓞 K) * αO := by
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  rw [NumberField.RingOfIntegers.ext_iff]
  simp only [polyRoot, map_sub, map_one, sub_div, one_div, map_sub,
    sub_sub_sub_cancel_left, map_mul, NumberField.RingOfIntegers.map_mk, hαO]
  rw [← sub_div, ← sub_smul, ← hv, Algebra.smul_def, map_mul, map_sub, map_one, mul_assoc,
    mul_div_cancel_left₀ _ hζ']
  rfl

/-! ## The local separability: the unit-hypothesis-free replacement of `separable_poly_aux`

flt-regular's `separable_poly_aux` proves the root differences are **global** units in `𝓞 L` from
`IsUnit u`.  Here the radical `a` need not be a unit, but at a maximal ideal `I` with `a ∉ I`
(`I ∤ (a)`), `a mod I` is a unit in the field `𝓞 K ⧸ I`, hence `(α mod J)^p = i(a mod I)` is a unit
in `𝓞 L ⧸ J` (`J = I·𝓞 L`), so `α mod J` is a unit — exactly what the separability of the reduced
factored polynomial needs. -/

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- The `map_poly_eq_prod` product expansion over `𝓞 L ⧸ J` and the `RingOfIntegers`
-- integral-closure coercions make this elaboration heavier than the default budget.
/-- **Local separability of `poly mod I`** at a maximal ideal `I` with `a ∉ I` (so the radical is a
unit modulo `I`).  This is the non-unit, single-prime replacement of flt-regular's
`KummersLemma.separable_poly`: separability over `𝓞 L ⧸ J` follows from `IsUnit (a mod I)` (which
gives `IsUnit (α mod J)`) rather than from the global unit-ness of the radical.  The field instance
on `𝓞 K ⧸ I` is introduced **locally** (not via `attribute [local instance] Ideal.Quotient.field`,
which would loop trying to prove `J.IsMaximal` while whnf-ing `𝓞 L`'s integral-closure type). -/
lemma separable_poly_local {L : Type*} [Field L] [Algebra K L]
    (ha : a ≠ 0) (α : L) (e : α ^ p = algebraMap K L (algebraMap (𝓞 K) K a))
    (I : Ideal (𝓞 K)) [I.IsMaximal] (haI : a ∉ I) :
    Separable ((poly hp hζ a hcong).map (Ideal.Quotient.mk I)) := by
  haveI : Fact (Nat.Prime p) := hpri
  letI : Field (𝓞 K ⧸ I) := Ideal.Quotient.field I
  -- The radical as an algebraic integer of `L`.
  have hα_int : IsIntegral (𝓞 K) α := by
    apply IsIntegral.of_pow (NeZero.pos p); rw [e]
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) K L]; exact isIntegral_algebraMap
  set αO : 𝓞 L := ⟨α, isIntegral_trans _ hα_int⟩ with hαO
  have hαO_pow : αO ^ p = algebraMap (𝓞 K) (𝓞 L) a := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    have h1 : algebraMap (𝓞 L) L (αO ^ p) = α ^ p := by
      rw [map_pow]; rfl
    have h2 : algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a) =
        algebraMap K L (algebraMap (𝓞 K) K a) := by
      rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        ← IsScalarTower.algebraMap_apply (𝓞 K) K L]
    rw [h1, h2, e]
  let J := I.map (algebraMap (𝓞 K) (𝓞 L))
  let i : 𝓞 K ⧸ I →+* 𝓞 L ⧸ J := Ideal.quotientMap _
    (algebraMap (𝓞 K) (𝓞 L)) Ideal.le_comap_map
  haveI : Nontrivial (𝓞 L ⧸ J) := by
    apply Ideal.Quotient.nontrivial_iff.mpr
    rw [ne_eq, Ideal.map_eq_top_iff]
    · exact Ideal.IsMaximal.ne_top ‹_›
    · intros x y hxy; ext; exact (algebraMap K L).injective (congr_arg Subtype.val hxy)
    · intros x; exact IsIntegral.tower_top (IsIntegralClosure.isIntegral ℤ L x)
  -- Transfer separability along the injection `i : 𝓞 K ⧸ I ↪ 𝓞 L ⧸ J`.
  refine (Polynomial.separable_map i).mp ?_
  have hmap : ((poly hp hζ a hcong).map (Ideal.Quotient.mk I)).map i =
      ∏ k ∈ Finset.range p,
        (X - C (Ideal.Quotient.mk J (polyRoot hp hζ a hcong α e k))) := by
    rw [map_map, Ideal.quotientMap_comp_mk, ← map_map,
      map_poly_eq_prod hp hζ a hcong ha α e, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [hmap]
  set q := Ideal.Quotient.mk J with hq
  -- `a mod I` is a unit in the residue field `𝓞 K ⧸ I` (since `a ∉ I`, `I` maximal).
  have haI_unit : IsUnit (Ideal.Quotient.mk I a) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]; exact haI
  -- `α mod J` is a unit: `(α mod J)^p = i(a mod I)`, a unit.
  have hαJ_unit : IsUnit (q αO) := by
    rw [← isUnit_pow_iff (NeZero.pos p).ne.symm, ← map_pow, hαO_pow]
    have hqi : i (Ideal.Quotient.mk I a) = q (algebraMap (𝓞 K) (𝓞 L) a) := Ideal.quotientMap_mk
    rw [← hqi]; exact haI_unit.map i
  refine separable_prod' ?_ (fun _ _ => separable_X_sub_C)
  intros m hm n hn hmn
  apply isCoprime_X_sub_C_of_isUnit_sub
  -- `polyRoot m - polyRoot n = v · α` with `v` a unit of `𝓞 L`.
  obtain ⟨v, hv⟩ :
      Associated (hζ.toInteger - 1 : 𝓞 K)
        ((hζ.toInteger : 𝓞 K) ^ n - (hζ.toInteger : 𝓞 K) ^ m) := by
    refine hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out ?_ ?_ ?_
    · rw [Finset.mem_coe, mem_nthRootsFinset (NeZero.pos p), ← pow_mul, mul_comm, pow_mul,
        hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    · rw [Finset.mem_coe, mem_nthRootsFinset (NeZero.pos p), ← pow_mul, mul_comm, pow_mul,
        hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    · exact mt (hζ.toInteger_isPrimitiveRoot.injOn_pow hn hm) hmn.symm
  rw [NumberField.RingOfIntegers.ext_iff] at hv
  have hcoe : (algebraMap (𝓞 K) K) (↑hζ.toInteger) = ζ := rfl
  simp only [map_mul, map_sub, map_one, map_pow, hcoe] at hv
  have hv_unit : IsUnit (q (algebraMap (𝓞 K) (𝓞 L) v)) :=
    ((algebraMap (𝓞 K) (𝓞 L)).isUnit_map v.isUnit).map q
  rw [← map_sub, polyRoot_sub_eq hp hζ a hcong α e m n αO rfl v hv, map_mul]
  exact hv_unit.mul hαJ_unit

/-! ## The radical lies in the `K`-adjoin of `polyRoot` (verbatim flt-regular) -/

lemma polyRoot_spec {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L (algebraMap (𝓞 K) K a)) (m) :
    α = (ζ ^ m)⁻¹ • (1 - (ζ - 1) • (polyRoot hp hζ a hcong α e m : L)) := by
  apply smul_right_injective (M := L) (r := ζ ^ m) (pow_ne_zero _ <| hζ.ne_zero
    (NeZero.pos p).ne.symm)
  simp only [polyRoot, map_sub, map_one, NumberField.RingOfIntegers.map_mk,
    Algebra.smul_def (ζ - 1), ← mul_div_assoc,
    mul_div_cancel_left₀ _
      ((hζ.map_of_injective (algebraMap K L).injective).sub_one_ne_zero hpri.out.one_lt),
    sub_sub_cancel, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ <| hζ.ne_zero (NeZero.pos p).ne.symm),
      one_smul]

lemma mem_adjoin_polyRoot {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L (algebraMap (𝓞 K) K a)) (m) :
    α ∈ Algebra.adjoin K {(polyRoot hp hζ a hcong α e m : L)} := by
  conv => enter [2]; rw [polyRoot_spec hp hζ a hcong α e m]
  exact Subalgebra.smul_mem _ (sub_mem (one_mem _)
    (Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton K _) _)) _

/-! ## The single-prime unramifiedness consumer (non-unit form of `KummersLemma.isUnramified`)

For an integral primary radical `a` that is not a `p`-th power and a maximal ideal `I` with `a ∉ I`
(the radical is an `I`-unit), the Kummer extension `L = K(a^{1/p})` is unramified at `I`
(flt-regular's `IsUnramifiedAt (𝓞 L) I`), via `isUnramifiedAt_of_Separable_minpoly` with the
generator `polyRoot 0` and the local separability `separable_poly_local`. -/

set_option backward.isDefEq.respectTransparency false in
include hp hζ hcong hu in
/-- **Single-prime unramifiedness** at `I` (`a ∉ I`) for the non-unit primary radical, where `L`
splits `X^p - a`.  This is the non-unit, single-prime form of flt-regular
`KummersLemma.isUnramified` (which is stated for a global unit radical).

The conclusion is the (now-removed) flt-regular `IsUnramifiedAt (𝓞 L) I` *unfolded* to its meaning:
every prime `P` of `𝓞 L` lying over `I` has ramification index `1`.  This is obtained, per prime,
from mathlib's `Algebra.IsUnramifiedAt (𝓞 K) P` (`isUnramifiedAt_of_Separable_minpoly`, fed the
local separability `separable_poly_local`) via `Algebra.isUnramifiedAt_iff_of_isDedekindDomain`. -/
lemma isUnramifiedAt_local (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [Polynomial.IsSplittingField K L (X ^ p - C (algebraMap (𝓞 K) K a))]
    (ha : a ≠ 0)
    (I : Ideal (𝓞 K)) [I.IsMaximal] (hIbot : I ≠ ⊥) (haI : a ∉ I) :
    ∀ P ∈ I.primesOver (𝓞 L), Ideal.ramificationIdx I P = 1 := by
  haveI : Fact (Nat.Prime p) := hpri
  haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hirr : Irreducible (X ^ p - C (algebraMap (𝓞 K) K a)) := by
    rw [X_pow_sub_C_irreducible_iff_of_prime hpri.out]; exact hu
  haveI := Fact.mk hirr
  haveI := Polynomial.IsSplittingField.finiteDimensional L (X ^ p - C (algebraMap (𝓞 K) K a))
  -- The canonical root and the `0`-th `polyRoot` generator.
  have hβ_pow : (rootOfSplitsXPowSubC (NeZero.pos p) (algebraMap (𝓞 K) K a) L) ^ p =
      algebraMap K L (algebraMap (𝓞 K) K a) :=
    rootOfSplitsXPowSubC_pow (algebraMap (𝓞 K) K a) L
  set α := rootOfSplitsXPowSubC (NeZero.pos p) (algebraMap (𝓞 K) K a) L with hα_def
  set x := polyRoot hp hζ a hcong α hβ_pow 0 with hx_def
  have hx_top : Algebra.adjoin K {(x : L)} = ⊤ := by
    rw [eq_top_iff, ← Algebra.adjoin_root_eq_top_of_isSplittingField
      ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩ hirr hβ_pow,
      Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact mem_adjoin_polyRoot hp hζ a hcong α hβ_pow 0
  -- Per prime `P` of `𝓞 L` over `I`.
  rintro P ⟨hPprime, hPover⟩
  haveI : P.IsPrime := hPprime
  haveI : P.LiesOver I := hPover
  have hIunder : P.under (𝓞 K) = I := (P.over_def I).symm
  have hP_bot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hIbot P
  -- `Algebra.IsUnramifiedAt (𝓞 K) P` from the local separability.
  have hunram : Algebra.IsUnramifiedAt (𝓞 K) P := by
    refine isUnramifiedAt_of_Separable_minpoly (R := 𝓞 K) K (S := 𝓞 L) L P hP_bot (x : L)
      (IsIntegral.tower_top x.prop) hx_top ?_
    rw [minpoly_polyRoot' hp hζ a hcong hu, hIunder]
    exact separable_poly_local hp hζ a hcong ha α hβ_pow I haI
  -- Convert `Algebra.IsUnramifiedAt` to `ramificationIdx = 1`.
  have he : Ideal.ramificationIdx (P.under (𝓞 K)) P = 1 :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP_bot).mp hunram
  rwa [hIunder] at he

end BernoulliRegular.FLT37.Eichler.NonUnitKummer
