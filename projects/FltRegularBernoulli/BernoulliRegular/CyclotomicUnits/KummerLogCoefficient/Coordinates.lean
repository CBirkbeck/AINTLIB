import BernoulliRegular.CyclotomicUnits.KummerLogCoefficient.Basic

/-!
# Dwork-coordinate coefficient maps for Kummer logarithms

This file contains the Dwork power-basis and finite quotient coordinate API
used by the Kummer logarithm evaluator.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

set_option maxHeartbeats 800000 in
-- The proof compares two full Dwork power-basis expansions through the
-- completed ramification identity `(p) = (varpi)^(p - 1)`; elaborating the
-- basis and scalar-action coercions is slower than the default budget.
omit [NumberField.IsCMField K] in
theorem dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_of_mem_parameterIdeal_pow_pred
    {x y : DworkCompleteIntegerRing p K}
    (hxy : x - y ∈ (dworkParameterIdeal p K) ^ (p - 1))
    (i : Fin (p - 1)) :
    (dworkParameterPowerBasis p K).repr x i -
        (dworkParameterPowerBasis p K).repr y i ∈
      rationalPadicPrimeIdeal p := by
  classical
  let R₀ : Type := RationalPadicIntegerRing p
  let S : Type _ := DworkCompleteIntegerRing p K
  have hspan : x - y ∈ Ideal.span ({(p : S)} : Set S) := by
    change x - y ∈ Ideal.span
      ({(p : DworkCompleteIntegerRing p K)} :
        Set (DworkCompleteIntegerRing p K))
    rw [span_natCast_prime_dworkComplete_eq_parameterIdeal_pow_pred
      (p := p) (K := K)]
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
      dworkParameterPowerLinearMap p K ((p : R₀) • b) = x - y := by
    have hbmap : dworkParameterPowerLinearMap p K b = z := by
      change dworkParameterPowerLinearMap p K
        ((dworkParameterPowerBasis p K).repr z) = z
      exact KummerLogTrace.dworkParameterPowerLinearMap_repr
        (p := p) (K := K) z
    calc
      dworkParameterPowerLinearMap p K ((p : R₀) • b)
          = (p : R₀) • dworkParameterPowerLinearMap p K b :=
            (dworkParameterPowerLinearMap p K).map_smul (p : R₀) b
      _ = (p : R₀) • z := by
            rw [hbmap]
      _ = (p : S) * z := by
            change algebraMap R₀ S (p : R₀) * z = (p : S) * z
            simp [R₀, S]
      _ = x - y := by
            simpa [S, mul_comm] using hz
  have hcoeff : a = (p : R₀) • b :=
    dworkParameterPowerLinearMap_injective (p := p) (K := K)
      (hmap_a.trans hmap_b.symm)
  have hi := congrFun hcoeff i
  change a i ∈ rationalPadicPrimeIdeal p
  rw [hi]
  have hp_mem' :
      (p : RationalPadicIntegerRing p) ∈ rationalPadicPrimeIdeal p :=
    Ideal.mem_span_singleton_self (p : RationalPadicIntegerRing p)
  have hp_mem : (p : R₀) ∈ rationalPadicPrimeIdeal p := hp_mem'
  have hmul_mem : (p : R₀) * b i ∈ rationalPadicPrimeIdeal p :=
    (rationalPadicPrimeIdeal p).mul_mem_right (b i) hp_mem
  have hi' : a i = (p : R₀) * b i := by
    simpa [Pi.smul_apply, smul_eq_mul] using hi
  simpa [hi'] using hmul_mem

omit [NumberField.IsCMField K] in
theorem dworkParameterPowerBasis_coeff_zmod_eq_of_sub_mem_parameterIdeal_pow_pred
    {x y : DworkCompleteIntegerRing p K}
    (hxy : x - y ∈ (dworkParameterIdeal p K) ^ (p - 1))
    (i : Fin (p - 1)) :
    rationalPadicIntegerToZMod p ((dworkParameterPowerBasis p K).repr x i) =
      rationalPadicIntegerToZMod p ((dworkParameterPowerBasis p K).repr y i) := by
  have hmem :=
    dworkParameterPowerBasis_coeff_sub_mem_primeIdeal_of_mem_parameterIdeal_pow_pred
      (p := p) (K := K) hxy i
  have hzero :
      rationalPadicIntegerToZMod p
        ((dworkParameterPowerBasis p K).repr x i -
          (dworkParameterPowerBasis p K).repr y i) = 0 :=
    (rationalPadicIntegerToZMod_eq_zero_iff_mem_primeIdeal
      (p := p)
      ((dworkParameterPowerBasis p K).repr x i -
        (dworkParameterPowerBasis p K).repr y i)).mpr hmem
  exact sub_eq_zero.mp (by simpa [map_sub] using hzero)

omit [NumberField.IsCMField K] in
theorem dworkFixedEvenPowerBasis_repr_eq_powerBasis_repr
    (hp_two : 2 < p) (x : dworkFixedSubalgebra p K)
    (i : dworkEvenPowerIndex p) :
    (dworkFixedEvenPowerBasis (p := p) (K := K) hp_two).repr x i =
      (dworkParameterPowerBasis p K).repr
        (x : DworkCompleteIntegerRing p K) i.1 := by
  classical
  let a := (dworkFixedEvenPowerBasis (p := p) (K := K) hp_two).repr x
  have h_even :
      dworkEvenPowerLinearMap (p := p) (K := K) hp_two a = x :=
    KummerLogTrace.dworkEvenPowerLinearMap_repr (p := p) (K := K) hp_two x
  have h_even_val :
      dworkParameterPowerLinearMap p K (dworkEvenCoeffExtend p a) =
        (x : DworkCompleteIntegerRing p K) := by
    simpa [dworkEvenPowerLinearMap, a] using congrArg Subtype.val h_even
  have h_full :
      dworkParameterPowerLinearMap p K
          ((dworkParameterPowerBasis p K).repr
            (x : DworkCompleteIntegerRing p K)) =
        (x : DworkCompleteIntegerRing p K) :=
    KummerLogTrace.dworkParameterPowerLinearMap_repr
      (p := p) (K := K) (x : DworkCompleteIntegerRing p K)
  have hcoeff :
      (dworkParameterPowerBasis p K).repr (x : DworkCompleteIntegerRing p K) =
        dworkEvenCoeffExtend p a :=
    dworkParameterPowerLinearMap_injective (p := p) (K := K)
      (h_full.trans h_even_val.symm)
  have hi := congrFun hcoeff i.1
  symm
  simpa [a, dworkEvenCoeffExtend, i.2] using hi

omit [NumberField.IsCMField K] in
theorem dworkFixedEvenPowerBasis_coeff_zmod_eq_of_sub_mem_parameterIdeal_pow_pred
    (hp_two : 2 < p) {x y : dworkFixedSubalgebra p K}
    (hxy :
      (x : DworkCompleteIntegerRing p K) -
          (y : DworkCompleteIntegerRing p K) ∈
        (dworkParameterIdeal p K) ^ (p - 1))
    (i : dworkEvenPowerIndex p) :
    rationalPadicIntegerToZMod p
        ((dworkFixedEvenPowerBasis (p := p) (K := K) hp_two).repr x i) =
      rationalPadicIntegerToZMod p
        ((dworkFixedEvenPowerBasis (p := p) (K := K) hp_two).repr y i) := by
  rw [dworkFixedEvenPowerBasis_repr_eq_powerBasis_repr
      (p := p) (K := K) hp_two x i,
    dworkFixedEvenPowerBasis_repr_eq_powerBasis_repr
      (p := p) (K := K) hp_two y i]
  exact dworkParameterPowerBasis_coeff_zmod_eq_of_sub_mem_parameterIdeal_pow_pred
    (p := p) (K := K) hxy i.1

omit [NumberField.IsCMField K] in
theorem kummerLogEvenPowerIndex_coeff_zmod_eq_of_sub_mem_parameterIdeal_pow_pred
    (hp_five : 5 ≤ p) {x y : dworkFixedSubalgebra p K}
    (hxy :
      (x : DworkCompleteIntegerRing p K) -
          (y : DworkCompleteIntegerRing p K) ∈
        (dworkParameterIdeal p K) ^ (p - 1))
    (j : Fin (kummerLogRank p)) :
    rationalPadicIntegerToZMod p
        ((dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr x
          (kummerLogEvenPowerIndex (p := p) hp_five j)) =
      rationalPadicIntegerToZMod p
        ((dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr y
          (kummerLogEvenPowerIndex (p := p) hp_five j)) :=
  dworkFixedEvenPowerBasis_coeff_zmod_eq_of_sub_mem_parameterIdeal_pow_pred
    (p := p) (K := K) (by omega : 2 < p) hxy
    (kummerLogEvenPowerIndex (p := p) hp_five j)

omit [NumberField.IsCMField K] in
theorem lambdaIdeal_pow_pred_le_comap_dworkParameterIdeal_pow_pred :
    (lambdaIdeal p K) ^ (p - 1) ≤
      ((dworkParameterIdeal p K) ^ (p - 1)).comap
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)) := by
  intro x hx
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  have hmap :
      algebraMap R S x ∈
        Ideal.map (algebraMap R S) ((lambdaIdeal p K) ^ (p - 1)) :=
    Ideal.mem_map_of_mem (algebraMap R S) hx
  simpa [R, S, dworkParameterIdeal_eq_dworkCompleteLambdaIdeal
      (p := p) (K := K), dworkCompleteLambdaIdeal, Ideal.map_pow] using hmap

omit [NumberField.IsCMField K] in
/-- The `varpi^i` coefficient modulo `p` of a completed Dwork quotient modulo
`(varpi)^(p - 1)`.  This is well-defined by CU-11f1: changing the
representative by `(varpi)^(p - 1) = (p)` changes every Dwork-basis
coefficient by a multiple of `p`. -/
noncomputable def dworkParameterQuotientCoeffModP
    (i : Fin (p - 1)) :
    DworkCompleteIntegerRing p K ⧸ (dworkParameterIdeal p K) ^ (p - 1) →
      ZMod p :=
  fun q =>
    Quotient.liftOn' q
      (fun x : DworkCompleteIntegerRing p K =>
        rationalPadicIntegerToZMod p
          ((dworkParameterPowerBasis p K).repr x i))
      (by
        intro x y hxy
        have hmem : x - y ∈ (dworkParameterIdeal p K) ^ (p - 1) := by
          simpa using ((Submodule.quotientRel_def
            (p := (dworkParameterIdeal p K) ^ (p - 1))).mp hxy)
        exact dworkParameterPowerBasis_coeff_zmod_eq_of_sub_mem_parameterIdeal_pow_pred
          (p := p) (K := K) hmem i)

omit [NumberField.IsCMField K] in
@[simp]
theorem dworkParameterQuotientCoeffModP_mk
    (i : Fin (p - 1)) (x : DworkCompleteIntegerRing p K) :
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1)) x) =
      rationalPadicIntegerToZMod p
        ((dworkParameterPowerBasis p K).repr x i) :=
  rfl

omit [NumberField.IsCMField K] in
/-- The `varpi^i` coefficient modulo `p` of a valued `lambda`-quotient, read
after mapping the representative into the completed Dwork ring. -/
noncomputable def valuedLambdaQuotientDworkCoeffModP
    (i : Fin (p - 1)) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1) → ZMod p :=
  fun q =>
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
      (Ideal.quotientMap ((dworkParameterIdeal p K) ^ (p - 1))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K))
        (lambdaIdeal_pow_pred_le_comap_dworkParameterIdeal_pow_pred
          (p := p) (K := K)) q)

omit [NumberField.IsCMField K] in
@[simp]
theorem valuedLambdaQuotientDworkCoeffModP_mk
    (i : Fin (p - 1)) (x : ValuedIntegerRing p K) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1)) x) =
      rationalPadicIntegerToZMod p
        ((dworkParameterPowerBasis p K).repr
          (algebraMap (ValuedIntegerRing p K)
            (DworkCompleteIntegerRing p K) x) i) := by
  change
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
          (algebraMap (ValuedIntegerRing p K)
            (DworkCompleteIntegerRing p K) x)) =
      rationalPadicIntegerToZMod p
        ((dworkParameterPowerBasis p K).repr
          (algebraMap (ValuedIntegerRing p K)
            (DworkCompleteIntegerRing p K) x) i)
  rw [dworkParameterQuotientCoeffModP_mk]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModP_evalₐ
    (i : Fin (p - 1)) (x : DworkCompleteIntegerRing p K) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1) x) =
      rationalPadicIntegerToZMod p
        ((dworkParameterPowerBasis p K).repr x i) := by
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  obtain ⟨r, hr⟩ :=
    Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (p - 1) x)
  have hzero :
      AdicCompletion.evalₐ I (p - 1)
        (x - algebraMap R S r) = 0 := by
    rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    exact sub_eq_zero.mpr hr.symm
  have hmemLam :
      x - algebraMap R S r ∈ (dworkCompleteLambdaIdeal p K) ^ (p - 1) :=
    dworkComplete_mem_lambdaIdeal_pow_of_evalₐ_eq_zero
      (p := p) (K := K) hzero
  have hmem :
      x - algebraMap R S r ∈ (dworkParameterIdeal p K) ^ (p - 1) := by
    simpa [dworkParameterIdeal_eq_dworkCompleteLambdaIdeal
      (p := p) (K := K)] using hmemLam
  calc
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1) x)
        =
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1)) r) :=
          congrArg
            (valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i) hr.symm
    _ =
      rationalPadicIntegerToZMod p
        ((dworkParameterPowerBasis p K).repr (algebraMap R S r) i) := by
          rw [valuedLambdaQuotientDworkCoeffModP_mk]
    _ =
      rationalPadicIntegerToZMod p
        ((dworkParameterPowerBasis p K).repr x i) :=
          (dworkParameterPowerBasis_coeff_zmod_eq_of_sub_mem_parameterIdeal_pow_pred
            (p := p) (K := K) hmem i).symm

omit [NumberField.IsCMField K] in
/-- Dwork power-basis coordinates modulo `p` determine the valued
`lambda^(p - 1)` quotient.

The proof maps a representative difference into the completed Dwork ring,
uses the coefficient congruences to put every Dwork-basis coefficient in the
rational `p`-adic prime ideal, then uses `(p) = (varpi)^(p - 1)` to show the
completed difference vanishes in the `p - 1` quotient. -/
theorem valuedLambdaQuotientDworkCoeffModP_ext
    {x y : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)}
    (h :
      ∀ i : Fin (p - 1),
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i x =
          valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i y) :
    x = y := by
  revert h
  refine Quotient.inductionOn₂' x y ?_
  intro r s hcoeff
  change Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1)) r =
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1)) s
  rw [Ideal.Quotient.eq]
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  let z : S := algebraMap R S (r - s)
  have hcoord_mem :
      ∀ i : Fin (p - 1),
        (dworkParameterPowerBasis p K).repr z i ∈
          (rationalPadicPrimeIdeal p) ^ 1 := by
    intro i
    have hi :
        rationalPadicIntegerToZMod p
            ((dworkParameterPowerBasis p K).repr
              (algebraMap R S r) i) =
          rationalPadicIntegerToZMod p
            ((dworkParameterPowerBasis p K).repr
              (algebraMap R S s) i) := by
      rw [← valuedLambdaQuotientDworkCoeffModP_mk (p := p) (K := K) i r,
        ← valuedLambdaQuotientDworkCoeffModP_mk (p := p) (K := K) i s]
      exact hcoeff i
    have hrepr :
        (dworkParameterPowerBasis p K).repr z i =
          (dworkParameterPowerBasis p K).repr
              (algebraMap R S r) i -
            (dworkParameterPowerBasis p K).repr
              (algebraMap R S s) i := by
      have hmap :=
        congrArg (fun f => f i)
          ((dworkParameterPowerBasis p K).repr.map_sub
            (algebraMap R S r) (algebraMap R S s))
      simp [z, map_sub] at hmap ⊢
    have hzero :
        rationalPadicIntegerToZMod p
          ((dworkParameterPowerBasis p K).repr z i) = 0 := by
      rw [hrepr, map_sub]
      exact sub_eq_zero.mpr hi
    simpa using
      (rationalPadicIntegerToZMod_eq_zero_iff_mem_primeIdeal
        (p := p) ((dworkParameterPowerBasis p K).repr z i)).mp hzero
  have hz_mem_parameter :
      z ∈ (dworkParameterIdeal p K) ^ (p - 1) := by
    have hpow :=
      dworkParameterPowerLinearMap_mem_parameterIdeal_pow_mul_pred_of_forall_mem_primeIdeal_pow
        (p := p) (K := K) (q := 1) hcoord_mem
    have hrepr_map :
        dworkParameterPowerLinearMap p K
            ((dworkParameterPowerBasis p K).repr z) = z :=
      KummerLogTrace.dworkParameterPowerLinearMap_repr
        (p := p) (K := K) z
    simpa [one_mul, hrepr_map] using hpow
  have hz_mem_lambda :
      z ∈ (dworkCompleteLambdaIdeal p K) ^ (p - 1) := by
    simpa [dworkParameterIdeal_eq_dworkCompleteLambdaIdeal
      (p := p) (K := K)] using hz_mem_parameter
  have hzero_eval :
      AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1) z = 0 :=
    dworkComplete_evalₐ_eq_zero_of_mem_lambdaIdeal_pow
      (p := p) (K := K) hz_mem_lambda
  change
    AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
      (algebraMap R S (r - s)) = 0 at hzero_eval
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of] at hzero_eval
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero_eval

omit [NumberField.IsCMField K] in
theorem dworkParameterPowerBasis_repr_powerLinearMap
    (a : Fin (p - 1) → RationalPadicIntegerRing p) :
    (dworkParameterPowerBasis p K).repr
        (dworkParameterPowerLinearMap p K a) = a := by
  apply dworkParameterPowerLinearMap_injective (p := p) (K := K)
  rw [KummerLogTrace.dworkParameterPowerLinearMap_repr]

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModP_mk_powerLinearMap
    (i : Fin (p - 1)) (a : Fin (p - 1) → RationalPadicIntegerRing p) :
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
          (dworkParameterPowerLinearMap p K a)) =
      rationalPadicIntegerToZMod p (a i) := by
  rw [dworkParameterQuotientCoeffModP_mk,
    dworkParameterPowerBasis_repr_powerLinearMap]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModP_evalₐ_powerLinearMap
    (i : Fin (p - 1)) (a : Fin (p - 1) → RationalPadicIntegerRing p) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
          (dworkParameterPowerLinearMap p K a)) =
      rationalPadicIntegerToZMod p (a i) := by
  rw [valuedLambdaQuotientDworkCoeffModP_evalₐ,
    dworkParameterPowerBasis_repr_powerLinearMap]

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModP_mk_add
    (i : Fin (p - 1)) (x y : DworkCompleteIntegerRing p K) :
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1)) (x + y)) =
      dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1)) x) +
      dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1)) y) := by
  change rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr (x + y) i) =
    rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr x i) +
    rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr y i)
  have hrepr :
      (dworkParameterPowerBasis p K).repr (x + y) i =
        ((dworkParameterPowerBasis p K).repr x +
          (dworkParameterPowerBasis p K).repr y) i :=
    congrArg (fun f => f i) ((dworkParameterPowerBasis p K).repr.map_add x y)
  rw [hrepr]
  change rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr x i +
        (dworkParameterPowerBasis p K).repr y i) =
    rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr x i) +
    rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr y i)
  rw [map_add]

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModP_mk_neg
    (i : Fin (p - 1)) (x : DworkCompleteIntegerRing p K) :
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1)) (-x)) =
      -dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1)) x) := by
  change rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr (-x) i) =
    -rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr x i)
  have hrepr :
      (dworkParameterPowerBasis p K).repr (-x) i =
        (-(dworkParameterPowerBasis p K).repr x) i :=
    congrArg (fun f => f i) ((dworkParameterPowerBasis p K).repr.map_neg x)
  rw [hrepr]
  change rationalPadicIntegerToZMod p
      (-(dworkParameterPowerBasis p K).repr x i) =
    -rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr x i)
  rw [map_neg]

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModP_mk_sub
    (i : Fin (p - 1)) (x y : DworkCompleteIntegerRing p K) :
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1)) (x - y)) =
      dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1)) x) -
      dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1)) y) := by
  change rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr (x - y) i) =
    rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr x i) -
    rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr y i)
  have hrepr :
      (dworkParameterPowerBasis p K).repr (x - y) i =
        ((dworkParameterPowerBasis p K).repr x -
          (dworkParameterPowerBasis p K).repr y) i :=
    congrArg (fun f => f i) ((dworkParameterPowerBasis p K).repr.map_sub x y)
  rw [hrepr]
  change rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr x i -
        (dworkParameterPowerBasis p K).repr y i) =
    rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr x i) -
    rationalPadicIntegerToZMod p
      ((dworkParameterPowerBasis p K).repr y i)
  rw [map_sub]

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModP_mk_sum
    {ι : Type*} (i : Fin (p - 1)) (s : Finset ι)
    (f : ι → DworkCompleteIntegerRing p K) :
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
          (∑ a ∈ s, f a)) =
      ∑ a ∈ s,
        dworkParameterQuotientCoeffModP (p := p) (K := K) i
          (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1)) (f a)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change rationalPadicIntegerToZMod p
          ((dworkParameterPowerBasis p K).repr
            (0 : DworkCompleteIntegerRing p K) i) = 0
      simp
  | insert a s has ih =>
      rw [Finset.sum_insert has, dworkParameterQuotientCoeffModP_mk_add,
        ih, Finset.sum_insert has]

set_option maxHeartbeats 800000 in
-- The quotient type in this additive extensionality lemma unfolds the completed
-- Dwork ideal comparison enough that the default heartbeat limit is tight.
omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModP_add
    (i : Fin (p - 1))
    (x y : DworkCompleteIntegerRing p K ⧸
      (dworkParameterIdeal p K) ^ (p - 1)) :
    dworkParameterQuotientCoeffModP (p := p) (K := K) i (x + y) =
      dworkParameterQuotientCoeffModP (p := p) (K := K) i x +
        dworkParameterQuotientCoeffModP (p := p) (K := K) i y := by
  refine Quotient.inductionOn₂' x y ?_
  intro x y
  exact dworkParameterQuotientCoeffModP_mk_add (p := p) (K := K) i x y

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModP_neg
    (i : Fin (p - 1))
    (x : DworkCompleteIntegerRing p K ⧸
      (dworkParameterIdeal p K) ^ (p - 1)) :
    dworkParameterQuotientCoeffModP (p := p) (K := K) i (-x) =
      -dworkParameterQuotientCoeffModP (p := p) (K := K) i x := by
  refine Quotient.inductionOn' x ?_
  intro x
  exact dworkParameterQuotientCoeffModP_mk_neg (p := p) (K := K) i x

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModP_sub
    (i : Fin (p - 1))
    (x y : DworkCompleteIntegerRing p K ⧸
      (dworkParameterIdeal p K) ^ (p - 1)) :
    dworkParameterQuotientCoeffModP (p := p) (K := K) i (x - y) =
      dworkParameterQuotientCoeffModP (p := p) (K := K) i x -
        dworkParameterQuotientCoeffModP (p := p) (K := K) i y := by
  refine Quotient.inductionOn₂' x y ?_
  intro x y
  exact dworkParameterQuotientCoeffModP_mk_sub (p := p) (K := K) i x y

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModP_add
    (i : Fin (p - 1))
    (x y : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i (x + y) =
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i x +
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i y := by
  refine Quotient.inductionOn₂' x y ?_
  intro x y
  change dworkParameterQuotientCoeffModP (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) (x + y))) =
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) x)) +
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) y))
  rw [map_add, dworkParameterQuotientCoeffModP_mk_add]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModP_neg
    (i : Fin (p - 1))
    (x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i (-x) =
      -valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i x := by
  refine Quotient.inductionOn' x ?_
  intro x
  change dworkParameterQuotientCoeffModP (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) (-x))) =
    -dworkParameterQuotientCoeffModP (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) x))
  rw [map_neg, dworkParameterQuotientCoeffModP_mk_neg]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModP_sub
    (i : Fin (p - 1))
    (x y : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i (x - y) =
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i x -
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i y := by
  refine Quotient.inductionOn₂' x y ?_
  intro x y
  change dworkParameterQuotientCoeffModP (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) (x - y))) =
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) x)) -
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
      (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
        (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) y))
  rw [map_sub, dworkParameterQuotientCoeffModP_mk_sub]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModP_sum
    {ι : Type*} (i : Fin (p - 1)) (s : Finset ι)
    (f : ι → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (∑ a ∈ s, f a) =
      ∑ a ∈ s,
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          (0 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) = 0
      have h := valuedLambdaQuotientDworkCoeffModP_add
        (p := p) (K := K) i
        (0 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) 0
      simpa using h
  | insert a s has ih =>
      rw [Finset.sum_insert has, valuedLambdaQuotientDworkCoeffModP_add,
        ih, Finset.sum_insert has]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModP_natCast_mul
    (i : Fin (p - 1)) (n : ℕ)
    (x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        ((n : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) * x) =
      (n : ZMod p) *
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i x := by
  induction n with
  | zero =>
      have hzero := valuedLambdaQuotientDworkCoeffModP_add
        (p := p) (K := K) i
        (0 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) 0
      simpa using hzero
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, valuedLambdaQuotientDworkCoeffModP_add, ih]
      push_cast
      ring

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModP_intCast_mul
    (i : Fin (p - 1)) (z : ℤ)
    (x : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        ((z : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) * x) =
      (z : ZMod p) *
        valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i x := by
  cases z with
  | ofNat n =>
      simpa using
        valuedLambdaQuotientDworkCoeffModP_natCast_mul
          (p := p) (K := K) i n x
  | negSucc n =>
      have h :=
        valuedLambdaQuotientDworkCoeffModP_natCast_mul
          (p := p) (K := K) i (n + 1) x
      rw [Int.cast_negSucc, Int.cast_negSucc, neg_mul,
        valuedLambdaQuotientDworkCoeffModP_neg, h]
      ring

omit [NumberField.IsCMField K] in
theorem den_mul_rIntegralRatToValuedInteger
    (q : Furtwaengler.DieudonneDwork.rIntegralRatSubring p) :
    ((q : ℚ).den : ValuedIntegerRing p K) *
        rIntegralRatToValuedInteger p K q =
      ((q : ℚ).num : ValuedIntegerRing p K) := by
  apply Subtype.ext
  change
    (((q : ℚ).den : ValuedCompletion p K) *
        algebraMap K (ValuedCompletion p K) (algebraMap ℚ K (q : ℚ))) =
      (((q : ℚ).num : ℤ) : ValuedCompletion p K)
  rw [← IsScalarTower.algebraMap_apply ℚ K (ValuedCompletion p K) (q : ℚ)]
  have hrat : ((q : ℚ).den : ℚ) * (q : ℚ) = ((q : ℚ).num : ℚ) := by
    simp
  have hmap := congrArg (algebraMap ℚ (ValuedCompletion p K)) hrat
  rw [map_mul] at hmap
  norm_num at hmap
  simpa [map_ratCast] using hmap

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModP_mk_algebraMap_mul_pow_of_lt
    (i : Fin (p - 1)) (c : RationalPadicIntegerRing p) {n : ℕ}
    (hn : n < p - 1) :
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
          (algebraMap (RationalPadicIntegerRing p)
              (DworkCompleteIntegerRing p K) c *
            dworkParameter p K ^ n)) =
      rationalPadicIntegerToZMod p
        (((Pi.single (⟨n, hn⟩ : Fin (p - 1)) c :
          Fin (p - 1) → RationalPadicIntegerRing p) i)) := by
  rw [← dworkParameterPowerLinearMap_single_coeff
      (p := p) (K := K) (i := (⟨n, hn⟩ : Fin (p - 1))) (c := c),
    dworkParameterQuotientCoeffModP_mk_powerLinearMap]

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModP_mk_pow_of_lt
    (i : Fin (p - 1)) {n : ℕ} (hn : n < p - 1) :
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
          (dworkParameter p K ^ n)) =
      rationalPadicIntegerToZMod p
        (((Pi.single (⟨n, hn⟩ : Fin (p - 1))
          (1 : RationalPadicIntegerRing p) :
            Fin (p - 1) → RationalPadicIntegerRing p) i)) := by
  simpa using
    dworkParameterQuotientCoeffModP_mk_algebraMap_mul_pow_of_lt
      (p := p) (K := K) i (1 : RationalPadicIntegerRing p) hn

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModP_mk_algebraMap_mul_pow_eq_zero_of_pred_le
    (i : Fin (p - 1)) (c : RationalPadicIntegerRing p) {n : ℕ}
    (hn : p - 1 ≤ n) :
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
          (algebraMap (RationalPadicIntegerRing p)
              (DworkCompleteIntegerRing p K) c *
            dworkParameter p K ^ n)) = 0 := by
  let S : Type _ := DworkCompleteIntegerRing p K
  let I : Ideal S := dworkParameterIdeal p K
  have hvarpi : dworkParameter p K ∈ I := by
    change dworkParameter p K ∈
      Ideal.span ({dworkParameter p K} : Set (DworkCompleteIntegerRing p K))
    exact Ideal.mem_span_singleton_self (dworkParameter p K)
  have hpow : dworkParameter p K ^ n ∈ I ^ (p - 1) :=
    Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow hvarpi n)
  have hmem :
      algebraMap (RationalPadicIntegerRing p) S c * dworkParameter p K ^ n - 0 ∈
        (dworkParameterIdeal p K) ^ (p - 1) := by
    rw [sub_zero]
    change algebraMap (RationalPadicIntegerRing p) S c *
        dworkParameter p K ^ n ∈ I ^ (p - 1)
    exact (I ^ (p - 1)).mul_mem_left
      (algebraMap (RationalPadicIntegerRing p) S c) hpow
  have hcoeff :=
    dworkParameterPowerBasis_coeff_zmod_eq_of_sub_mem_parameterIdeal_pow_pred
      (p := p) (K := K) hmem i
  rw [dworkParameterQuotientCoeffModP_mk, hcoeff]
  simp

omit [NumberField.IsCMField K] in
theorem dworkParameterQuotientCoeffModP_mk_pow_eq_zero_of_pred_le
    (i : Fin (p - 1)) {n : ℕ} (hn : p - 1 ≤ n) :
    dworkParameterQuotientCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ (p - 1))
          (dworkParameter p K ^ n)) = 0 := by
  simpa using
    dworkParameterQuotientCoeffModP_mk_algebraMap_mul_pow_eq_zero_of_pred_le
      (p := p) (K := K) i (1 : RationalPadicIntegerRing p) hn

omit [NumberField.IsCMField K] in
/-- Below the Kummer precision, powers of the finite Dwork approximant have
the expected single Dwork power-basis coordinate. -/
theorem valuedLambdaQuotientDworkCoeffModP_mk_dworkParameterApprox_pow_of_lt
    (i : Fin (p - 1)) {n : ℕ} (hn : n < p - 1) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1))
          (dworkParameterApprox p K (p - 1) ^ n)) =
      rationalPadicIntegerToZMod p
        (((Pi.single (⟨n, hn⟩ : Fin (p - 1))
          (1 : RationalPadicIntegerRing p) :
            Fin (p - 1) → RationalPadicIntegerRing p) i)) := by
  have hpow :
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1))
          (dworkParameterApprox p K (p - 1) ^ n) =
        AdicCompletion.evalₐ (lambdaIdeal p K) (p - 1)
          (dworkParameter p K ^ n) := by
    rw [map_pow, map_pow, dworkParameter_evalₐ]
  rw [hpow]
  have hsingle :
      dworkParameter p K ^ n =
        dworkParameterPowerLinearMap p K
          (Pi.single (⟨n, hn⟩ : Fin (p - 1))
            (1 : RationalPadicIntegerRing p)) := by
    rw [dworkParameterPowerLinearMap_single]
  rw [hsingle, valuedLambdaQuotientDworkCoeffModP_evalₐ_powerLinearMap]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModP_mk_intCast_mul_dworkParameterApprox_pow_of_lt
    (i : Fin (p - 1)) (z : ℤ) {n : ℕ} (hn : n < p - 1) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1))
          ((z : ValuedIntegerRing p K) *
            dworkParameterApprox p K (p - 1) ^ n)) =
      (z : ZMod p) *
        rationalPadicIntegerToZMod p
          (((Pi.single (⟨n, hn⟩ : Fin (p - 1))
            (1 : RationalPadicIntegerRing p) :
              Fin (p - 1) → RationalPadicIntegerRing p) i)) := by
  rw [show Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1))
        ((z : ValuedIntegerRing p K) *
          dworkParameterApprox p K (p - 1) ^ n) =
      ((z : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)) *
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1))
          (dworkParameterApprox p K (p - 1) ^ n)) by
        simp]
  rw [valuedLambdaQuotientDworkCoeffModP_intCast_mul,
    valuedLambdaQuotientDworkCoeffModP_mk_dworkParameterApprox_pow_of_lt
      (p := p) (K := K) i hn]

omit [NumberField.IsCMField K] in
theorem valuedLambdaQuotientDworkCoeffModP_mk_rIntegralRat_mul_dworkParameterApprox_pow_of_lt
    (i : Fin (p - 1))
    (q : Furtwaengler.DieudonneDwork.rIntegralRatSubring p)
    {n : ℕ} (hn : n < p - 1) :
    valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1))
          (rIntegralRatToValuedInteger p K q *
            dworkParameterApprox p K (p - 1) ^ n)) =
      (Furtwaengler.DieudonneDwork.rIntegralToZMod p q) *
        rationalPadicIntegerToZMod p
          (((Pi.single (⟨n, hn⟩ : Fin (p - 1))
            (1 : RationalPadicIntegerRing p) :
              Fin (p - 1) → RationalPadicIntegerRing p) i)) := by
  let A : Type _ := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (p - 1)
  let x : A :=
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1))
      (rIntegralRatToValuedInteger p K q *
        dworkParameterApprox p K (p - 1) ^ n)
  let b : ZMod p :=
    rationalPadicIntegerToZMod p
      (((Pi.single (⟨n, hn⟩ : Fin (p - 1))
        (1 : RationalPadicIntegerRing p) :
          Fin (p - 1) → RationalPadicIntegerRing p) i))
  let rhs : ZMod p := (Furtwaengler.DieudonneDwork.rIntegralToZMod p q) * b
  have hcoeff_den :
      ((q : ℚ).den : ZMod p) *
          valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i x =
        ((q : ℚ).num : ZMod p) * b := by
    rw [← valuedLambdaQuotientDworkCoeffModP_natCast_mul
      (p := p) (K := K) i (q : ℚ).den x]
    have hquot :
        (((q : ℚ).den : ValuedIntegerRing p K) : A) * x =
          Ideal.Quotient.mk ((lambdaIdeal p K) ^ (p - 1))
            (((q : ℚ).num : ValuedIntegerRing p K) *
              dworkParameterApprox p K (p - 1) ^ n) := by
      dsimp [x, A]
      rw [← map_mul]
      congr 1
      calc
        ((q : ℚ).den : ValuedIntegerRing p K) *
            (rIntegralRatToValuedInteger p K q *
              dworkParameterApprox p K (p - 1) ^ n)
            =
          (((q : ℚ).den : ValuedIntegerRing p K) *
            rIntegralRatToValuedInteger p K q) *
              dworkParameterApprox p K (p - 1) ^ n := by ring
        _ =
          ((q : ℚ).num : ValuedIntegerRing p K) *
            dworkParameterApprox p K (p - 1) ^ n := by
              rw [den_mul_rIntegralRatToValuedInteger (p := p) (K := K) q]
    change
      valuedLambdaQuotientDworkCoeffModP (p := p) (K := K) i
          ((((q : ℚ).den : ValuedIntegerRing p K) : A) * x) =
        ((q : ℚ).num : ZMod p) * b
    rw [hquot]
    dsimp [b]
    exact
      valuedLambdaQuotientDworkCoeffModP_mk_intCast_mul_dworkParameterApprox_pow_of_lt
        (p := p) (K := K) i (q : ℚ).num hn
  have hrhs_den :
      ((q : ℚ).den : ZMod p) * rhs =
        ((q : ℚ).num : ZMod p) * b := by
    dsimp [rhs]
    have hden :=
      Furtwaengler.DieudonneDwork.IsRIntegralRat.den_mul_toZMod
        (q : ℚ) q.property
    change
      ((q : ℚ).den : ZMod p) *
          ((Furtwaengler.DieudonneDwork.rIntegralToZMod p q) * b) =
        ((q : ℚ).num : ZMod p) * b
    rw [Furtwaengler.DieudonneDwork.rIntegralToZMod_apply]
    calc
      ((q : ℚ).den : ZMod p) *
          (Furtwaengler.DieudonneDwork.IsRIntegralRat.toZMod
            (q : ℚ) q.property * b)
          =
        (((q : ℚ).den : ZMod p) *
          Furtwaengler.DieudonneDwork.IsRIntegralRat.toZMod
            (q : ℚ) q.property) * b := by ring
      _ = ((q : ℚ).num : ZMod p) * b := by rw [hden]
  have hunit :
      IsUnit (((q : ℚ).den : ℕ) : ZMod p) :=
    Furtwaengler.DieudonneDwork.IsRIntegralRat.isUnit_den_zmod
      (q : ℚ) q.property
  exact hunit.mul_left_cancel (by
    rw [hcoeff_den, hrhs_den])

end CyclotomicUnits
end BernoulliRegular

end
