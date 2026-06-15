import BernoulliRegular.CyclotomicUnits.KummerLogCoefficient.Evaluator

/-!
# The second-order (mod `p²`) Dwork-coordinate coefficient machinery

This file builds the **second-order** Dwork power-basis coordinate coefficient
`valuedLambdaQuotientDworkCoeffModSq`, the mod-`p²` analog of the proven first-order
`valuedLambdaQuotientDworkCoeffModP`
(`BernoulliRegular/CyclotomicUnits/KummerLogCoefficient/Coordinates.lean`).  It is the genuine
second-order coefficient parallel needed for Washington Proposition 8.12 at the irregular index
`i = 32` (the `p`-adic-`L` core of Corollary 8.23 for `p = 37`).

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The first-order template, and the second order

The first-order coefficient `valuedLambdaQuotientDworkCoeffModP i` takes an element of
`ValuedIntegerRing p K ⧸ (lambdaIdeal p K)^(p-1)` (`= mod (p)`, since `(p) = (λ)^(p-1)`), maps it
into the completed Dwork ring, reads the `i`-th Dwork power-basis coordinate (an element of
`RationalPadicIntegerRing p ≅ ℤ_[p]`), and reduces it modulo `p` via `rationalPadicIntegerToZMod`.
It is well-defined modulo `(λ)^(p-1) = (p)` because changing the representative by `(p)` changes
each Dwork coordinate by `p · (coord)`, which dies mod `p`.

The **second-order** coefficient `valuedLambdaQuotientDworkCoeffModSq i` takes an element of
`ValuedIntegerRing p K ⧸ (lambdaIdeal p K)^(2*(p-1))` (`= mod (p²)`, since `(p²) = (λ)^(2(p-1))`),
maps it into the completed Dwork ring, reads the `i`-th Dwork power-basis coordinate, and reduces
it modulo `p²` via `rationalPadicIntegerToZModSq` (`= PadicInt.toZModPow 2` through the ring
equiv).  It is well-defined modulo `(λ)^(2(p-1)) = (p²)` because changing the representative by
`(p²)` changes each Dwork coordinate by `p² · (coord)`, which dies mod `p²`.  This is the **exact
mod-`p²` analog** of the first-order construction, built in parallel here.

## What is built

* **§0** — `rationalPadicIntegerToZModSq : RationalPadicIntegerRing p →+* ZMod (p^2)`, the mod-`p²`
  residue map, and `rationalPadicIntegerToZModSq_eq_zero_iff_mem_primeIdeal_sq`: its kernel is
  `(rationalPadicPrimeIdeal p)^2 = (p²)`.

* **§1** — the mod-`p²` coordinate congruence: `x - y ∈ (dworkParameterIdeal p K)^(2(p-1))`
  (`= (p²)`) forces every Dwork power-basis coordinate to agree mod `p²`
  (`dworkParameterPowerBasis_coeff_zmodSq_eq_of_sub_mem_parameterIdeal_pow_two_pred`).  This is the
  second-order analog of the proven
  `dworkParameterPowerBasis_coeff_zmod_eq_of_sub_mem_parameterIdeal_pow_pred`.

* **§2** — the second-order coefficient `valuedLambdaQuotientDworkCoeffModSq` and its evaluation API
  (`_mk`, `_evalₐ`, `_evalₐ_powerLinearMap`, `_evalₐ_polynomial_eval₂_of_natDegree_lt`) plus
  additive/scalar linearity (`_add`, `_neg`, `_sub`, `_sum`, `_intCast_mul`), the full parallel of
  the first-order API used by the Kummer-log evaluator.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open BernoulliRegular.Reflection.Local
open scoped BigOperators NumberField

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter
open Furtwaengler.KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

/-! ## 0. The mod-`p²` residue map on the rational completed integer ring

`rationalPadicIntegerToZModSq : RationalPadicIntegerRing p →+* ZMod (p^2)` is the second-order
residue map, transported from mathlib's `PadicInt.toZModPow 2` through the canonical equivalence
`RationalPadicIntegerRing p ≅ ℤ_[p]`.  Its kernel is `(p²) = (rationalPadicPrimeIdeal p)^2`. -/

/-- **The mod-`p²` residue map** on the rational completed integer coefficient ring, transported
from mathlib's `PadicInt.toZModPow 2`.  Second-order analog of `rationalPadicIntegerToZMod`. -/
noncomputable def rationalPadicIntegerToZModSq :
    RationalPadicIntegerRing p →+* ZMod (p ^ 2) :=
  (PadicInt.toZModPow (p := lambdaPadicPrime p) 2).comp
    (padicIntToRationalPadicIntegerRingEquiv (p := p)).symm.toRingHom

@[simp]
theorem rationalPadicIntegerToZModSq_natCast (n : ℕ) :
    rationalPadicIntegerToZModSq p (n : RationalPadicIntegerRing p) =
      (n : ZMod (p ^ 2)) := by
  change PadicInt.toZModPow (p := lambdaPadicPrime p) 2
      ((padicIntToRationalPadicIntegerRingEquiv (p := p)).symm
        (n : RationalPadicIntegerRing p)) = (n : ZMod (p ^ 2))
  have hmap :
      (padicIntToRationalPadicIntegerRingEquiv (p := p))
          (n : ℤ_[lambdaPadicPrime p]) =
        (n : RationalPadicIntegerRing p) := by
    simp [padicIntToRationalPadicIntegerRingEquiv]
  rw [← hmap, RingEquiv.symm_apply_apply, map_natCast]

theorem rationalPadicIntegerToZModSq_eq_zero_iff_mem_primeIdeal_sq
    (x : RationalPadicIntegerRing p) :
    rationalPadicIntegerToZModSq p x = 0 ↔ x ∈ (rationalPadicPrimeIdeal p) ^ 2 := by
  let e := padicIntToRationalPadicIntegerRingEquiv (p := p)
  change PadicInt.toZModPow (p := lambdaPadicPrime p) 2 (e.symm x) = 0 ↔
    x ∈ (rationalPadicPrimeIdeal p) ^ 2
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
  -- `RingHom.ker (toZModPow 2) = span {p^2}`; transport across `e`.
  have hpe : e ((lambdaPadicPrime p : ℕ) : ℤ_[lambdaPadicPrime p]) =
      (p : RationalPadicIntegerRing p) := by
    have hpn : ((lambdaPadicPrime p : ℕ) : ℤ_[lambdaPadicPrime p]) =
        ((p : ℕ) : ℤ_[lambdaPadicPrime p]) := by norm_cast
    rw [hpn]
    simp [e, padicIntToRationalPadicIntegerRingEquiv]
  rw [show ((rationalPadicPrimeIdeal p) ^ 2 :
      Ideal (RationalPadicIntegerRing p)) =
        Ideal.span {(p : RationalPadicIntegerRing p) ^ 2} from by
      rw [rationalPadicPrimeIdeal, Ideal.span_singleton_pow]]
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    -- `e.symm x = (p:ℤ_[p])^2 * c`, so `x = p^2 * e c`.
    refine ⟨e c, ?_⟩
    have hx : x = e (e.symm x) := (e.apply_symm_apply x).symm
    rw [hx, hc, map_mul, map_pow, hpe]
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, ?_⟩
    have hpe' : e.symm (p : RationalPadicIntegerRing p) =
        ((lambdaPadicPrime p : ℕ) : ℤ_[lambdaPadicPrime p]) := by
      rw [← hpe, RingEquiv.symm_apply_apply]
    rw [hc, map_mul, map_pow, hpe']

/-! ## 1. The mod-`p²` Dwork power-basis coordinate congruence

If `x - y ∈ (dworkParameterIdeal p K)^(2(p-1)) = (p²)`, then every Dwork power-basis coordinate
agrees mod `p²`.  This is the second-order analog of the proven
`dworkParameterPowerBasis_coeff_zmod_eq_of_sub_mem_parameterIdeal_pow_pred`.  The proof writes the
difference as `p² · z`, transports to coordinates as `a = p² · b` by injectivity of the Dwork power
linear map, and reads off `a i = p² · b i ∈ (rationalPadicPrimeIdeal)^2`. -/

set_option maxHeartbeats 800000 in
-- The proof compares two full Dwork power-basis expansions through the completed ramification
-- identity `(p²) = (varpi)^(2(p-1))`; elaborating the basis and scalar-action coercions is slower
-- than the default budget (as in the first-order analog).
omit [NumberField.IsCMField K] in
theorem dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_sq_of_mem_parameterIdeal_pow_two_pred
    {x y : DworkCompleteIntegerRing p K}
    (hxy : x - y ∈ (dworkParameterIdeal p K) ^ (2 * (p - 1)))
    (i : Fin (p - 1)) :
    (dworkParameterPowerBasis p K).repr x i -
        (dworkParameterPowerBasis p K).repr y i ∈
      (rationalPadicPrimeIdeal p) ^ 2 := by
  classical
  let R₀ : Type := RationalPadicIntegerRing p
  let S : Type _ := DworkCompleteIntegerRing p K
  -- `(p²) = (varpi)^(2(p-1))`, so `x - y ∈ span {p²}`.
  have hspan : x - y ∈ Ideal.span ({(p : S) ^ 2} : Set S) := by
    rw [← Ideal.span_singleton_pow,
      span_natCast_prime_dworkComplete_eq_parameterIdeal_pow_pred (p := p) (K := K),
      ← pow_mul, Nat.mul_comm]
    exact hxy
  rcases Ideal.mem_span_singleton'.mp hspan with ⟨z, hz⟩
  let a : Fin (p - 1) → R₀ :=
    (dworkParameterPowerBasis p K).repr x -
      (dworkParameterPowerBasis p K).repr y
  let b : Fin (p - 1) → R₀ :=
    (dworkParameterPowerBasis p K).repr z
  have hmap_a :
      dworkParameterPowerLinearMap p K a = x - y := by
    calc
      dworkParameterPowerLinearMap p K a =
          dworkParameterPowerLinearMap p K
            ((dworkParameterPowerBasis p K).repr x -
              (dworkParameterPowerBasis p K).repr y) := by
            rfl
      _ =
          dworkParameterPowerLinearMap p K ((dworkParameterPowerBasis p K).repr x) -
            dworkParameterPowerLinearMap p K ((dworkParameterPowerBasis p K).repr y) :=
            (dworkParameterPowerLinearMap p K).map_sub
              ((dworkParameterPowerBasis p K).repr x)
              ((dworkParameterPowerBasis p K).repr y)
      _ = x - y := by
            rw [KummerLogTrace.dworkParameterPowerLinearMap_repr
                (p := p) (K := K) x,
              KummerLogTrace.dworkParameterPowerLinearMap_repr
                (p := p) (K := K) y]
  have hmap_b :
      dworkParameterPowerLinearMap p K (((p : R₀) ^ 2) • b) = x - y := by
    have hbmap : dworkParameterPowerLinearMap p K b = z := by
      change dworkParameterPowerLinearMap p K
        ((dworkParameterPowerBasis p K).repr z) = z
      exact KummerLogTrace.dworkParameterPowerLinearMap_repr
        (p := p) (K := K) z
    calc
      dworkParameterPowerLinearMap p K (((p : R₀) ^ 2) • b)
          = ((p : R₀) ^ 2) • dworkParameterPowerLinearMap p K b :=
            (dworkParameterPowerLinearMap p K).map_smul ((p : R₀) ^ 2) b
      _ = ((p : R₀) ^ 2) • z := by
            rw [hbmap]
      _ = (p : S) ^ 2 * z := by
            change algebraMap R₀ S ((p : R₀) ^ 2) * z = (p : S) ^ 2 * z
            simp [R₀, S]
      _ = x - y := by
            simpa [S, mul_comm] using hz
  have hcoeff : a = ((p : R₀) ^ 2) • b :=
    dworkParameterPowerLinearMap_injective (p := p) (K := K)
      (hmap_a.trans hmap_b.symm)
  have hi := congrFun hcoeff i
  change a i ∈ (rationalPadicPrimeIdeal p) ^ 2
  rw [hi]
  -- `p² · b i ∈ (rationalPadicPrimeIdeal)^2 = span {p²}`.
  have hp2_mem : (p : R₀) ^ 2 ∈ (rationalPadicPrimeIdeal p) ^ 2 := by
    rw [rationalPadicPrimeIdeal, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self ((p : R₀) ^ 2)
  have hmul_mem : (p : R₀) ^ 2 * b i ∈ (rationalPadicPrimeIdeal p) ^ 2 :=
    ((rationalPadicPrimeIdeal p) ^ 2).mul_mem_right (b i) hp2_mem
  have hi' : (((p : R₀) ^ 2) • b) i = (p : R₀) ^ 2 * b i := by
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hi']
  exact hmul_mem

omit [NumberField.IsCMField K] in
theorem dworkParameterPowerBasis_coeff_zmodSq_eq_of_sub_mem_parameterIdeal_pow_two_pred
    {x y : DworkCompleteIntegerRing p K}
    (hxy : x - y ∈ (dworkParameterIdeal p K) ^ (2 * (p - 1)))
    (i : Fin (p - 1)) :
    rationalPadicIntegerToZModSq p ((dworkParameterPowerBasis p K).repr x i) =
      rationalPadicIntegerToZModSq p ((dworkParameterPowerBasis p K).repr y i) := by
  have hmem :=
    dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_sq_of_mem_parameterIdeal_pow_two_pred
      (p := p) (K := K) hxy i
  have hzero :
      rationalPadicIntegerToZModSq p
        ((dworkParameterPowerBasis p K).repr x i -
          (dworkParameterPowerBasis p K).repr y i) = 0 :=
    (rationalPadicIntegerToZModSq_eq_zero_iff_mem_primeIdeal_sq
      (p := p)
      ((dworkParameterPowerBasis p K).repr x i -
        (dworkParameterPowerBasis p K).repr y i)).mpr hmem
  exact sub_eq_zero.mp (by simpa [map_sub] using hzero)

/-! ## 2. The second-order Dwork-coordinate coefficient

`valuedLambdaQuotientDworkCoeffModSq i` reads the `varpi^i` Dwork coordinate modulo `p²` of a valued
`λ`-quotient at precision `2*(p-1)` (`= mod (p²)`), through the completed Dwork ring.  This is the
full mod-`p²` analog of the proven first-order `valuedLambdaQuotientDworkCoeffModP`.  We mirror its
evaluation API (`_mk`, `_evalₐ`, `_evalₐ_powerLinearMap`, `_evalₐ_polynomial_eval₂`) and
additive/scalar linearity (`_add`, `_neg`, `_sub`, `_sum`, `_intCast_mul`). -/

omit [NumberField.IsCMField K] in
/-- The `varpi^i` coefficient modulo `p²` of a completed Dwork quotient modulo `(varpi)^(2(p-1))`.
Well-defined by the second-order coordinate congruence (§1): changing the representative by
`(varpi)^(2(p-1)) = (p²)` changes every Dwork-basis coefficient by a multiple of `p²`. -/
noncomputable def dworkParameterQuotientCoeffModSq
    (i : Fin (p - 1)) :
    DworkCompleteIntegerRing p K ⧸ (dworkParameterIdeal p K) ^ (2 * (p - 1)) →
      ZMod (p ^ 2) :=
  fun q =>
    Quotient.liftOn' q
      (fun x : DworkCompleteIntegerRing p K =>
        rationalPadicIntegerToZModSq p
          ((dworkParameterPowerBasis p K).repr x i))
      (by
        intro x y hxy
        have hmem : x - y ∈ (dworkParameterIdeal p K) ^ (2 * (p - 1)) := by
          simpa using ((Submodule.quotientRel_def
            (p := (dworkParameterIdeal p K) ^ (2 * (p - 1)))).mp hxy)
        exact dworkParameterPowerBasis_coeff_zmodSq_eq_of_sub_mem_parameterIdeal_pow_two_pred
          (p := p) (K := K) hmem i)

omit [NumberField.IsCMField K] in
@[simp]
theorem dworkParameterQuotientCoeffModSq_mk
    (i : Fin (p - 1)) (x : DworkCompleteIntegerRing p K) :
    dworkParameterQuotientCoeffModSq (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1))) x) =
      rationalPadicIntegerToZModSq p
        ((dworkParameterPowerBasis p K).repr x i) :=
  rfl

omit [NumberField.IsCMField K] in
theorem lambdaIdeal_pow_two_pred_le_comap_dworkParameterIdeal_pow_two_pred :
    (lambdaIdeal p K) ^ (2 * (p - 1)) ≤
      ((dworkParameterIdeal p K) ^ (2 * (p - 1))).comap
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)) := by
  intro x hx
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  have hmap :
      algebraMap R S x ∈
        Ideal.map (algebraMap R S) ((lambdaIdeal p K) ^ (2 * (p - 1))) :=
    Ideal.mem_map_of_mem (algebraMap R S) hx
  simpa [R, S, dworkParameterIdeal_eq_dworkCompleteLambdaIdeal
      (p := p) (K := K), dworkCompleteLambdaIdeal, Ideal.map_pow] using hmap

omit [NumberField.IsCMField K] in
/-- The `varpi^i` coefficient modulo `p²` of a valued `lambda`-quotient at precision `2*(p-1)`, read
after mapping the representative into the completed Dwork ring.  Second-order analog of
`valuedLambdaQuotientDworkCoeffModP`. -/
noncomputable def valuedLambdaQuotientDworkCoeffModSq
    (i : Fin (p - 1)) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1)) → ZMod (p ^ 2) :=
  fun q =>
    dworkParameterQuotientCoeffModSq (p := p) (K := K) i
      (Ideal.quotientMap ((dworkParameterIdeal p K) ^ (2 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K))
        (lambdaIdeal_pow_two_pred_le_comap_dworkParameterIdeal_pow_two_pred
          (p := p) (K := K)) q)

omit [NumberField.IsCMField K] in
@[simp]
theorem valuedLambdaQuotientDworkCoeffModSq_mk
    (i : Fin (p - 1)) (x : ValuedIntegerRing p K) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (2 * (p - 1))) x) =
      rationalPadicIntegerToZModSq p
        ((dworkParameterPowerBasis p K).repr
          (algebraMap (ValuedIntegerRing p K)
            (DworkCompleteIntegerRing p K) x) i) := by
  change
    dworkParameterQuotientCoeffModSq (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1)))
          (algebraMap (ValuedIntegerRing p K)
            (DworkCompleteIntegerRing p K) x)) =
      rationalPadicIntegerToZModSq p
        ((dworkParameterPowerBasis p K).repr
          (algebraMap (ValuedIntegerRing p K)
            (DworkCompleteIntegerRing p K) x) i)
  rw [dworkParameterQuotientCoeffModSq_mk]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModSq_evalₐ
    (i : Fin (p - 1)) (x : DworkCompleteIntegerRing p K) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i
        (AdicCompletion.evalₐ (lambdaIdeal p K) (2 * (p - 1)) x) =
      rationalPadicIntegerToZModSq p
        ((dworkParameterPowerBasis p K).repr x i) := by
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  obtain ⟨r, hr⟩ :=
    Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (2 * (p - 1)) x)
  have hzero :
      AdicCompletion.evalₐ I (2 * (p - 1))
        (x - algebraMap R S r) = 0 := by
    rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    exact sub_eq_zero.mpr hr.symm
  have hmemLam :
      x - algebraMap R S r ∈ (dworkCompleteLambdaIdeal p K) ^ (2 * (p - 1)) :=
    dworkComplete_mem_lambdaIdeal_pow_of_evalₐ_eq_zero
      (p := p) (K := K) hzero
  have hmem :
      x - algebraMap R S r ∈ (dworkParameterIdeal p K) ^ (2 * (p - 1)) := by
    simpa [dworkParameterIdeal_eq_dworkCompleteLambdaIdeal
      (p := p) (K := K)] using hmemLam
  calc
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i
        (AdicCompletion.evalₐ (lambdaIdeal p K) (2 * (p - 1)) x)
        =
      valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (2 * (p - 1))) r) := by
          simpa [I] using congrArg
            (valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i) hr.symm
    _ =
      rationalPadicIntegerToZModSq p
        ((dworkParameterPowerBasis p K).repr (algebraMap R S r) i) := by
          rw [valuedLambdaQuotientDworkCoeffModSq_mk]
    _ =
      rationalPadicIntegerToZModSq p
        ((dworkParameterPowerBasis p K).repr x i) :=
          (dworkParameterPowerBasis_coeff_zmodSq_eq_of_sub_mem_parameterIdeal_pow_two_pred
            (p := p) (K := K) hmem i).symm

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModSq_evalₐ_powerLinearMap
    (i : Fin (p - 1)) (a : Fin (p - 1) → RationalPadicIntegerRing p) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i
        (AdicCompletion.evalₐ (lambdaIdeal p K) (2 * (p - 1))
          (dworkParameterPowerLinearMap p K a)) =
      rationalPadicIntegerToZModSq p (a i) := by
  rw [valuedLambdaQuotientDworkCoeffModSq_evalₐ,
    dworkParameterPowerBasis_repr_powerLinearMap]

/-! ### Additive and scalar linearity of the second-order coefficient -/

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModSq_mk_add
    (i : Fin (p - 1)) (x y : DworkCompleteIntegerRing p K) :
    dworkParameterQuotientCoeffModSq (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1))) (x + y)) =
      dworkParameterQuotientCoeffModSq (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1))) x) +
      dworkParameterQuotientCoeffModSq (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1))) y) := by
  change rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr (x + y) i) =
    rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr x i) +
    rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr y i)
  have hrepr :
      (dworkParameterPowerBasis p K).repr (x + y) i =
        ((dworkParameterPowerBasis p K).repr x +
          (dworkParameterPowerBasis p K).repr y) i :=
    congrArg (fun f => f i) ((dworkParameterPowerBasis p K).repr.map_add x y)
  rw [hrepr]
  change rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr x i +
        (dworkParameterPowerBasis p K).repr y i) =
    rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr x i) +
    rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr y i)
  rw [map_add]

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModSq_mk_neg
    (i : Fin (p - 1)) (x : DworkCompleteIntegerRing p K) :
    dworkParameterQuotientCoeffModSq (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1))) (-x)) =
      -dworkParameterQuotientCoeffModSq (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1))) x) := by
  change rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr (-x) i) =
    -rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr x i)
  have hrepr :
      (dworkParameterPowerBasis p K).repr (-x) i =
        (-(dworkParameterPowerBasis p K).repr x) i :=
    congrArg (fun f => f i) ((dworkParameterPowerBasis p K).repr.map_neg x)
  rw [hrepr]
  change rationalPadicIntegerToZModSq p
      (-(dworkParameterPowerBasis p K).repr x i) =
    -rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr x i)
  rw [map_neg]

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModSq_mk_sub
    (i : Fin (p - 1)) (x y : DworkCompleteIntegerRing p K) :
    dworkParameterQuotientCoeffModSq (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1))) (x - y)) =
      dworkParameterQuotientCoeffModSq (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1))) x) -
      dworkParameterQuotientCoeffModSq (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1))) y) := by
  change rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr (x - y) i) =
    rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr x i) -
    rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr y i)
  have hrepr :
      (dworkParameterPowerBasis p K).repr (x - y) i =
        ((dworkParameterPowerBasis p K).repr x -
          (dworkParameterPowerBasis p K).repr y) i :=
    congrArg (fun f => f i) ((dworkParameterPowerBasis p K).repr.map_sub x y)
  rw [hrepr]
  change rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr x i -
        (dworkParameterPowerBasis p K).repr y i) =
    rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr x i) -
    rationalPadicIntegerToZModSq p
      ((dworkParameterPowerBasis p K).repr y i)
  rw [map_sub]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModSq_add
    (i : Fin (p - 1))
    (x y : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i (x + y) =
      valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i x +
        valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i y := by
  refine Quotient.inductionOn₂' x y ?_
  intro x y
  change dworkParameterQuotientCoeffModSq (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) (x + y))) =
    dworkParameterQuotientCoeffModSq (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) x)) +
    dworkParameterQuotientCoeffModSq (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) y))
  rw [map_add, dworkParameterQuotientCoeffModSq_mk_add]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModSq_neg
    (i : Fin (p - 1))
    (x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i (-x) =
      -valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i x := by
  refine Quotient.inductionOn' x ?_
  intro x
  change dworkParameterQuotientCoeffModSq (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) (-x))) =
    -dworkParameterQuotientCoeffModSq (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) x))
  rw [map_neg, dworkParameterQuotientCoeffModSq_mk_neg]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModSq_sub
    (i : Fin (p - 1))
    (x y : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i (x - y) =
      valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i x -
        valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i y := by
  refine Quotient.inductionOn₂' x y ?_
  intro x y
  change dworkParameterQuotientCoeffModSq (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) (x - y))) =
    dworkParameterQuotientCoeffModSq (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) x)) -
    dworkParameterQuotientCoeffModSq (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (2 * (p - 1)))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) y))
  rw [map_sub, dworkParameterQuotientCoeffModSq_mk_sub]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModSq_sum
    {ι : Type*} (i : Fin (p - 1)) (s : Finset ι)
    (f : ι → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i
        (∑ a ∈ s, f a) =
      ∑ a ∈ s,
        valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i
          (0 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) = 0
      have h := valuedLambdaQuotientDworkCoeffModSq_add
        (p := p) (K := K) i
        (0 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) 0
      simpa using h
  | insert a s has ih =>
      rw [Finset.sum_insert has, valuedLambdaQuotientDworkCoeffModSq_add,
        ih, Finset.sum_insert has]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModSq_natCast_mul
    (i : Fin (p - 1)) (n : ℕ)
    (x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i
        ((n : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) * x) =
      (n : ZMod (p ^ 2)) *
        valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i x := by
  induction n with
  | zero =>
      have hzero := valuedLambdaQuotientDworkCoeffModSq_add
        (p := p) (K := K) i
        (0 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) 0
      simpa using hzero
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, valuedLambdaQuotientDworkCoeffModSq_add, ih]
      simp
      ring

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModSq_intCast_mul
    (i : Fin (p - 1)) (z : ℤ)
    (x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i
        ((z : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) * x) =
      (z : ZMod (p ^ 2)) *
        valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i x := by
  cases z with
  | ofNat n =>
      simpa using
        valuedLambdaQuotientDworkCoeffModSq_natCast_mul
          (p := p) (K := K) i n x
  | negSucc n =>
      have h :=
        valuedLambdaQuotientDworkCoeffModSq_natCast_mul
          (p := p) (K := K) i (n + 1) x
      rw [Int.cast_negSucc, Int.cast_negSucc]
      rw [neg_mul]
      rw [valuedLambdaQuotientDworkCoeffModSq_neg, h]
      ring

omit [NumberField.IsCMField K] in
/-- The second-order coefficient kills `0`. -/
theorem valuedLambdaQuotientDworkCoeffModSq_zero (i : Fin (p - 1)) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i
        (0 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) = 0 := by
  have h := valuedLambdaQuotientDworkCoeffModSq_add (p := p) (K := K) i
    (0 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) 0
  simpa using h

/-! ### Polynomial-evaluation extraction (`< p - 1` degree) -/

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModSq_evalₐ_polynomial_eval₂_of_natDegree_lt
    (i : Fin (p - 1)) (P : Polynomial (RationalPadicIntegerRing p))
    (hdeg : P.natDegree < p - 1) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i
        (AdicCompletion.evalₐ (lambdaIdeal p K) (2 * (p - 1))
          (Polynomial.eval₂
            (algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K))
            (dworkParameter p K) P)) =
      rationalPadicIntegerToZModSq p (P.coeff (i : ℕ)) := by
  rw [dworkParameterPowerLinearMap_of_polynomial_eval₂
    (p := p) (K := K) P hdeg]
  rw [valuedLambdaQuotientDworkCoeffModSq_evalₐ_powerLinearMap]

end CyclotomicUnits
end BernoulliRegular

end
