module

public import BernoulliRegular.CyclotomicUnits.Saturation
public import BernoulliRegular.CyclotomicUnits.DworkParameter
public import BernoulliRegular.CyclotomicUnits.KummerLogLinearAlgebra
public import BernoulliRegular.CyclotomicUnits.KummerLogMatrix
public import BernoulliRegular.CyclotomicUnits.KummerLogTrace
public import BernoulliRegular.Reflection.Local.Graded

/-!
# Principal-unit domain lemmas for the saturation logarithm

This file starts the CU-14b logarithm-domain layer.  The first input is the
residue-field fact that the local image of any real unit becomes congruent to
`1` after raising to `p - 1`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup
open PadicLogSetup.DworkParameter

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The valuation-integer local image of a real unit. -/
noncomputable def EPlus_valuedLocalImage (u : (𝓞 K⁺)ˣ) :
    (ValuedIntegerRing p K)ˣ :=
  Units.map (algebraMap (𝓞 K) (ValuedIntegerRing p K)).toMonoidHom
    (Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom u)

omit [NumberField.IsCMField K] in
@[simp]
theorem EPlus_valuedLocalImage_coe (u : (𝓞 K⁺)ˣ) :
    (EPlus_valuedLocalImage (p := p) (K := K) u : ValuedIntegerRing p K) =
      algebraMap (𝓞 K) (ValuedIntegerRing p K)
        (algebraMap (𝓞 K⁺) (𝓞 K) (u : 𝓞 K⁺)) :=
  rfl

/-- The Dwork-completed local image of a real unit. -/
noncomputable def EPlus_localImage (u : (𝓞 K⁺)ˣ) :
    (DworkCompleteIntegerRing p K)ˣ :=
  Units.map
    (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)).toMonoidHom
    (EPlus_valuedLocalImage (p := p) (K := K) u)

omit [NumberField.IsCMField K] in
@[simp]
theorem EPlus_localImage_coe (u : (𝓞 K⁺)ˣ) :
    (EPlus_localImage (p := p) (K := K) u : DworkCompleteIntegerRing p K) =
      algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)
        (EPlus_valuedLocalImage (p := p) (K := K) u : ValuedIntegerRing p K) :=
  rfl

omit [NumberField.IsCMField K] in
/-- Any global integral unit is congruent to a `(p - 1)`-st root of unity modulo
the cyclotomic lambda prime. -/
theorem integralUnit_pow_pred_sub_one_mem_cyclotomicLambda (u : (𝓞 K)ˣ) :
    ((u : 𝓞 K) ^ (p - 1) - 1) ∈ Reflection.Local.cyclotomicLambda p K := by
  let R : Type _ := 𝓞 K
  let I : Ideal R := Reflection.Local.cyclotomicLambda p K
  let F : Type _ := R ⧸ I
  letI : I.IsMaximal := Reflection.Local.cyclotomicLambda_isMaximal (p := p) (K := K)
  letI : Field F := Ideal.Quotient.field I
  haveI : Finite F := Nat.finite_of_card_ne_zero <| by
    rw [show Nat.card F = p from
      Reflection.Local.globalCyclotomicResidueCard (p := p) (K := K)]
    exact (Fact.out : Nat.Prime p).ne_zero
  letI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = p := by
    rw [← Nat.card_eq_fintype_card]
    exact Reflection.Local.globalCyclotomicResidueCard (p := p) (K := K)
  let q : R →+* F := Ideal.Quotient.mk I
  let e : ZMod p ≃+* F :=
    ZMod.ringEquivOfPrime F (Fact.out : Nat.Prime p) hcard
  let a : F := q (u : R)
  have ha_ne : e.symm a ≠ 0 := by
    have ha_unit : IsUnit a := ⟨Units.map q.toMonoidHom u, rfl⟩
    have ha_ne_zero : a ≠ 0 := by
      rcases ha_unit with ⟨v, hv⟩
      rw [← hv]
      exact Units.ne_zero v
    intro hzero
    exact ha_ne_zero (by
      rw [← e.apply_symm_apply a, hzero, map_zero])
  have hpow : a ^ (p - 1) = 1 := by
    calc
      a ^ (p - 1) = e ((e.symm a) ^ (p - 1)) := by
        rw [map_pow, RingEquiv.apply_symm_apply]
      _ = e 1 := by rw [ZMod.pow_card_sub_one_eq_one ha_ne]
      _ = 1 := by simp
  have hzero : q ((u : R) ^ (p - 1) - 1) = 0 := by
    rw [map_sub, map_pow, hpow, map_one, sub_self]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

omit [NumberField.IsCMField K] in
/-- The valuation-ring local image of a real unit is a principal unit after
raising to `p - 1`. -/
theorem EPlus_valuedLocalImage_pow_pred_sub_one_mem_lambdaIdeal
    (u : (𝓞 K⁺)ˣ) :
    ((EPlus_valuedLocalImage (p := p) (K := K) u : ValuedIntegerRing p K) ^
        (p - 1) - 1) ∈
      lambdaIdeal p K := by
  let uK : (𝓞 K)ˣ :=
    Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom u
  have hglobal :
      ((uK : 𝓞 K) ^ (p - 1) - 1) ∈ Reflection.Local.cyclotomicLambda p K :=
    integralUnit_pow_pred_sub_one_mem_cyclotomicLambda (p := p) (K := K) uK
  have hmap :
      algebraMap (𝓞 K) (ValuedIntegerRing p K)
          ((uK : 𝓞 K) ^ (p - 1) - 1) ∈
        Ideal.map (algebraMap (𝓞 K) (ValuedIntegerRing p K))
          (Reflection.Local.cyclotomicLambda p K) :=
    Ideal.mem_map_of_mem (algebraMap (𝓞 K) (ValuedIntegerRing p K)) hglobal
  rw [lambdaIdeal_eq_map_cyclotomicLambda (p := p) (K := K)] at hmap
  simpa [EPlus_valuedLocalImage, uK, map_sub, map_pow] using hmap

omit [NumberField.IsCMField K] in
/-- The Dwork-completed local image of a real unit is congruent to `1` after
raising to `p - 1`. -/
theorem EPlus_localImage_pow_pred_sub_one_mem_logIdeal
    (u : (𝓞 K⁺)ˣ) :
    ((EPlus_localImage (p := p) (K := K) u : DworkCompleteIntegerRing p K) ^
        (p - 1) - 1) ∈
      dworkCompleteLambdaIdeal p K := by
  have hvalued :=
    EPlus_valuedLocalImage_pow_pred_sub_one_mem_lambdaIdeal
      (p := p) (K := K) u
  have hmap :
      algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)
          (((EPlus_valuedLocalImage (p := p) (K := K) u :
            ValuedIntegerRing p K) ^ (p - 1) - 1)) ∈
        Ideal.map (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K))
          (lambdaIdeal p K) :=
    Ideal.mem_map_of_mem
      (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)) hvalued
  simpa [EPlus_localImage, dworkCompleteLambdaIdeal, map_sub, map_pow] using hmap

omit [NumberField.IsCMField K] in
/-- CU-14b1: the arbitrary real-unit witness lies in the completed logarithm
domain after raising to `p - 1`. -/
theorem EPlus_localImage_pow_pred_mem_logDomain (u : (𝓞 K⁺)ˣ) :
    (EPlus_localImage (p := p) (K := K) u) ^ (p - 1) ∈
      Ideal.oneUnitsSubgroup (dworkCompleteLambdaIdeal p K) := by
  rw [Ideal.mem_oneUnitsSubgroup]
  exact EPlus_localImage_pow_pred_sub_one_mem_logIdeal (p := p) (K := K) u

omit [NumberField.IsCMField K] in
/-- The valued principal-unit domain used by the completed same-prime
logarithm. -/
abbrev completedLogDomain : Type _ :=
  Ideal.oneUnitsSubgroup (lambdaIdeal p K)

omit [NumberField.IsCMField K] in
/-- Additive coordinate of a valued principal unit. -/
def completedLogArg (u : completedLogDomain (p := p) (K := K)) :
    ValuedIntegerRing p K :=
  ((u : (ValuedIntegerRing p K)ˣ) : ValuedIntegerRing p K) - 1

omit [NumberField.IsCMField K] in
theorem completedLogArg_mem (u : completedLogDomain (p := p) (K := K)) :
    completedLogArg (p := p) (K := K) u ∈ lambdaIdeal p K :=
  u.2

omit [NumberField.IsCMField K] in
/-- Coordinate of the `n`th power of a principal unit with coordinate `x`. -/
def principalUnitPowCoord (x : ValuedIntegerRing p K) (n : ℕ) :
    ValuedIntegerRing p K :=
  (1 + x) ^ n - 1

omit [NumberField.IsCMField K] in
theorem principalUnitPowCoord_eq_finsetProductCoord
    (x : ValuedIntegerRing p K) (n : ℕ) :
    principalUnitPowCoord (p := p) (K := K) x n =
      Conjugation.samePrimeFiniteLogFinsetProductCoord (p := p) (K := K)
        (Finset.univ : Finset (Fin n)) (fun _ ↦ x) := by
  simp [principalUnitPowCoord, Conjugation.samePrimeFiniteLogFinsetProductCoord]

omit [NumberField.IsCMField K] in
theorem principalUnitPowCoord_mem_lambdaIdeal
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) (n : ℕ) :
    principalUnitPowCoord (p := p) (K := K) x n ∈ lambdaIdeal p K := by
  let f : Fin n → ValuedIntegerRing p K := fun _ ↦ x
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin n)), f i ∈ lambdaIdeal p K := fun i _hi ↦
    hx
  have hmem :=
    Conjugation.samePrimeFiniteLogFinsetProductCoord_mem_lambdaIdeal
      (p := p) (K := K) (s := Finset.univ) (x := f) hf
  simpa [principalUnitPowCoord_eq_finsetProductCoord (p := p) (K := K) x n, f]
    using hmem

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteLog_principalUnitPowCoord_eq_nsmul
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) N
        (principalUnitPowCoord (p := p) (K := K) x p)
        (principalUnitPowCoord_mem_lambdaIdeal (p := p) (K := K) hx p) =
      p • samePrimeFiniteLog (p := p) (K := K) N x hx := by
  let f : Fin p → ValuedIntegerRing p K := fun _ ↦ x
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin p)), f i ∈ lambdaIdeal p K := fun i _hi ↦
    hx
  have hcoord :
      principalUnitPowCoord (p := p) (K := K) x p =
        Conjugation.samePrimeFiniteLogFinsetProductCoord (p := p) (K := K)
          (Finset.univ : Finset (Fin p)) f := by
    simpa [f] using
      principalUnitPowCoord_eq_finsetProductCoord (p := p) (K := K) x p
  have hprod :=
    Conjugation.samePrimeFiniteLog_finsetProductCoord
      (p := p) (K := K) (N := N) (s := Finset.univ) (x := f) hf
  calc
    samePrimeFiniteLog (p := p) (K := K) N
        (principalUnitPowCoord (p := p) (K := K) x p)
        (principalUnitPowCoord_mem_lambdaIdeal (p := p) (K := K) hx p)
        =
      samePrimeFiniteLog (p := p) (K := K) N
        (Conjugation.samePrimeFiniteLogFinsetProductCoord (p := p) (K := K)
          (Finset.univ : Finset (Fin p)) f)
        (Conjugation.samePrimeFiniteLogFinsetProductCoord_mem_lambdaIdeal
          (p := p) (K := K) hf) :=
        samePrimeFiniteLog_eq_of_eq (p := p) (K := K) (N := N)
          hcoord
          (principalUnitPowCoord_mem_lambdaIdeal (p := p) (K := K) hx p)
          (Conjugation.samePrimeFiniteLogFinsetProductCoord_mem_lambdaIdeal
            (p := p) (K := K) hf)
    _ =
      ∑ i ∈ (Finset.univ : Finset (Fin p)).attach,
        samePrimeFiniteLog (p := p) (K := K) N (f i.1) (hf i.1 i.2) := hprod
    _ = p • samePrimeFiniteLog (p := p) (K := K) N x hx := by
      have hsum :
          (∑ i ∈ (Finset.univ : Finset (Fin p)).attach,
              samePrimeFiniteLog (p := p) (K := K) N (f i.1) (hf i.1 i.2)) =
            ∑ _i ∈ (Finset.univ : Finset (Fin p)).attach,
              samePrimeFiniteLog (p := p) (K := K) N x hx := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simp [f]
      rw [hsum]
      simp

omit [NumberField.IsCMField K] in
/-- Quotient coordinate of the completed logarithm. -/
noncomputable def completedLogCoord
    (u : completedLogDomain (p := p) (K := K)) (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N :=
  match N with
  | 0 => 0
  | N + 1 =>
      samePrimeFiniteLog (p := p) (K := K) N
        (completedLogArg (p := p) (K := K) u)
        (completedLogArg_mem (p := p) (K := K) u)

omit [NumberField.IsCMField K] in
@[simp]
theorem completedLogCoord_zero
    (u : completedLogDomain (p := p) (K := K)) :
    completedLogCoord (p := p) (K := K) u 0 = 0 :=
  rfl

omit [NumberField.IsCMField K] in
@[simp]
theorem completedLogCoord_succ
    (u : completedLogDomain (p := p) (K := K)) (N : ℕ) :
    completedLogCoord (p := p) (K := K) u (N + 1) =
      samePrimeFiniteLog (p := p) (K := K) N
        (completedLogArg (p := p) (K := K) u)
        (completedLogArg_mem (p := p) (K := K) u) :=
  rfl

omit [NumberField.IsCMField K] in
theorem completedLogCoord_factorPow
    (u : completedLogDomain (p := p) (K := K)) {M N : ℕ} (hMN : M ≤ N) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
        (completedLogCoord (p := p) (K := K) u N) =
      completedLogCoord (p := p) (K := K) u M := by
  cases M with
  | zero =>
      exact quotient_pow_zero_eq_zero (p := p) (K := K)
        (lambdaIdeal p K)
        (Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
          (completedLogCoord (p := p) (K := K) u N))
  | succ M =>
      cases N with
      | zero =>
          exact False.elim (Nat.not_succ_le_zero M hMN)
      | succ N =>
          have hMN' : M ≤ N := Nat.succ_le_succ_iff.mp hMN
          simpa using
            samePrimeFiniteLog_factorPow
              (p := p) (K := K) hMN'
              (completedLogArg_mem (p := p) (K := K) u)

omit [NumberField.IsCMField K] in
/-- Completed same-prime logarithm on valued principal units. -/
noncomputable def completedLog
    (u : completedLogDomain (p := p) (K := K)) :
    DworkCompleteIntegerRing p K :=
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  ⟨fun N ↦
      (Ideal.quotientEquivAlgOfEq R (by
        ext y
        simp : (I ^ N • ⊤ : Ideal R) = I ^ N)).symm
        (completedLogCoord (p := p) (K := K) u N),
    by
      intro M N hMN
      let hEqM : (I ^ M • ⊤ : Ideal R) = I ^ M := by
        ext y
        simp
      let hEqN : (I ^ N • ⊤ : Ideal R) = I ^ N := by
        ext y
        simp
      apply (Ideal.quotientEquivAlgOfEq R hEqM).injective
      calc
        (Ideal.quotientEquivAlgOfEq R hEqM)
            (AdicCompletion.transitionMap I R hMN
              ((Ideal.quotientEquivAlgOfEq R hEqN).symm
                (completedLogCoord (p := p) (K := K) u N)))
            =
          Ideal.Quotient.factorPow I hMN
            (completedLogCoord (p := p) (K := K) u N) := by
            refine Quotient.inductionOn'
              (completedLogCoord (p := p) (K := K) u N) ?_
            intro r
            rfl
        _ = completedLogCoord (p := p) (K := K) u M :=
            completedLogCoord_factorPow (p := p) (K := K) u hMN
        _ = (Ideal.quotientEquivAlgOfEq R hEqM)
            ((Ideal.quotientEquivAlgOfEq R hEqM).symm
              (completedLogCoord (p := p) (K := K) u M)) := by
            refine Quotient.inductionOn'
              (completedLogCoord (p := p) (K := K) u M) ?_
            intro r
            rfl⟩

omit [NumberField.IsCMField K] in
@[simp]
theorem completedLog_evalₐ
    (u : completedLogDomain (p := p) (K := K)) (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N
        (completedLog (p := p) (K := K) u) =
      completedLogCoord (p := p) (K := K) u N := by
  unfold completedLog
  let hEq :
      ((lambdaIdeal p K) ^ N • ⊤ : Ideal (ValuedIntegerRing p K)) =
        (lambdaIdeal p K) ^ N := by
    ext y
    simp
  change
    (Ideal.quotientEquivAlgOfEq (ValuedIntegerRing p K) hEq)
      ((Ideal.quotientEquivAlgOfEq (ValuedIntegerRing p K) hEq).symm
        (completedLogCoord (p := p) (K := K) u N)) =
      completedLogCoord (p := p) (K := K) u N
  refine Quotient.inductionOn'
    (completedLogCoord (p := p) (K := K) u N) ?_
  intro r
  rfl

omit [NumberField.IsCMField K] in
@[simp]
theorem completedLog_evalₐ_succ
    (u : completedLogDomain (p := p) (K := K)) (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) (N + 1)
        (completedLog (p := p) (K := K) u) =
      samePrimeFiniteLog (p := p) (K := K) N
        (completedLogArg (p := p) (K := K) u)
        (completedLogArg_mem (p := p) (K := K) u) := by
  simp [completedLog_evalₐ]

omit [NumberField.IsCMField K] in
theorem completedLogArg_pow
    (u : completedLogDomain (p := p) (K := K)) (n : ℕ) :
    completedLogArg (p := p) (K := K) (u ^ n) =
      principalUnitPowCoord (p := p) (K := K)
        (completedLogArg (p := p) (K := K) u) n := by
  simp [completedLogArg, principalUnitPowCoord]

omit [NumberField.IsCMField K] in
/-- CU-14b2: the completed same-prime logarithm of a `p`th power is a
`p`-multiple. -/
theorem completedLog_pow_p_eq_p_smul
    (u : completedLogDomain (p := p) (K := K)) :
    completedLog (p := p) (K := K) (u ^ p) =
      p • completedLog (p := p) (K := K) u := by
  apply AdicCompletion.ext_evalₐ
  intro N
  cases N with
  | zero =>
      rw [map_nsmul, completedLog_evalₐ, completedLog_evalₐ]
      simp
  | succ N =>
      rw [map_nsmul, completedLog_evalₐ_succ, completedLog_evalₐ_succ,
        samePrimeFiniteLog_eq_of_eq (p := p) (K := K) (N := N)
        (completedLogArg_pow (p := p) (K := K) u p)
        (completedLogArg_mem (p := p) (K := K) (u ^ p))
        (principalUnitPowCoord_mem_lambdaIdeal
          (p := p) (K := K)
          (completedLogArg_mem (p := p) (K := K) u) p)]
      exact samePrimeFiniteLog_principalUnitPowCoord_eq_nsmul
        (p := p) (K := K) N (completedLogArg_mem (p := p) (K := K) u)

omit [NumberField.IsCMField K] in
/-- The completed logarithm is additive on valued principal units. -/
theorem completedLog_mul
    (u v : completedLogDomain (p := p) (K := K)) :
    completedLog (p := p) (K := K) (u * v) =
      completedLog (p := p) (K := K) u +
        completedLog (p := p) (K := K) v := by
  apply AdicCompletion.ext_evalₐ
  intro N
  cases N with
  | zero =>
      rw [map_add, completedLog_evalₐ, completedLog_evalₐ, completedLog_evalₐ]
      simp
  | succ N =>
      rw [map_add, completedLog_evalₐ_succ, completedLog_evalₐ_succ,
        completedLog_evalₐ_succ]
      let x := completedLogArg (p := p) (K := K) u
      let y := completedLogArg (p := p) (K := K) v
      have hx : x ∈ lambdaIdeal p K :=
        completedLogArg_mem (p := p) (K := K) u
      have hy : y ∈ lambdaIdeal p K :=
        completedLogArg_mem (p := p) (K := K) v
      have harg :
          completedLogArg (p := p) (K := K) (u * v) =
            samePrimeFiniteLogProductCoord (p := p) (K := K) x y := by
        simp [x, y, completedLogArg, samePrimeFiniteLogProductCoord]
        ring
      calc
        samePrimeFiniteLog (p := p) (K := K) N
            (completedLogArg (p := p) (K := K) (u * v))
            (completedLogArg_mem (p := p) (K := K) (u * v))
            =
          samePrimeFiniteLog (p := p) (K := K) N
            (samePrimeFiniteLogProductCoord (p := p) (K := K) x y)
            (samePrimeFiniteLogProductCoord_mem_lambdaIdeal
              (p := p) (K := K) hx hy) :=
            samePrimeFiniteLog_eq_of_eq (p := p) (K := K) (N := N)
              harg
              (completedLogArg_mem (p := p) (K := K) (u * v))
              (samePrimeFiniteLogProductCoord_mem_lambdaIdeal
                (p := p) (K := K) hx hy)
        _ =
          samePrimeFiniteLog (p := p) (K := K) N x hx +
            samePrimeFiniteLog (p := p) (K := K) N y hy :=
            samePrimeFiniteLog_add_add_mul (p := p) (K := K) N hx hy

omit [NumberField.IsCMField K] in
@[simp]
theorem completedLog_one :
    completedLog (p := p) (K := K) (1 : completedLogDomain (p := p) (K := K)) =
      0 := by
  apply AdicCompletion.ext_evalₐ
  intro N
  cases N with
  | zero =>
      rw [completedLog_evalₐ, map_zero]
      simp
  | succ N =>
      rw [completedLog_evalₐ_succ, map_zero]
      have harg :
          completedLogArg (p := p) (K := K)
              (1 : completedLogDomain (p := p) (K := K)) = 0 := by
        simp [completedLogArg]
      calc
        samePrimeFiniteLog (p := p) (K := K) N
            (completedLogArg (p := p) (K := K)
              (1 : completedLogDomain (p := p) (K := K)))
            (completedLogArg_mem (p := p) (K := K)
              (1 : completedLogDomain (p := p) (K := K)))
            =
          samePrimeFiniteLog (p := p) (K := K) N 0 (zero_mem (lambdaIdeal p K)) :=
            samePrimeFiniteLog_eq_of_eq (p := p) (K := K) (N := N)
              harg
              (completedLogArg_mem (p := p) (K := K)
                (1 : completedLogDomain (p := p) (K := K)))
              (zero_mem (lambdaIdeal p K))
        _ = 0 := samePrimeFiniteLog_arg_zero (p := p) (K := K) N

omit [NumberField.IsCMField K] in
/-- The completed logarithm sends an `n`th power to an `n`-multiple. -/
theorem completedLog_pow
    (u : completedLogDomain (p := p) (K := K)) (n : ℕ) :
    completedLog (p := p) (K := K) (u ^ n) =
      n • completedLog (p := p) (K := K) u := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, completedLog_mul, ih]
      ring

omit [NumberField.IsCMField K] in
/-- The completed logarithm sends an inverse to a negation. -/
theorem completedLog_inv
    (u : completedLogDomain (p := p) (K := K)) :
    completedLog (p := p) (K := K) u⁻¹ =
      -completedLog (p := p) (K := K) u := by
  have hmul := completedLog_mul (p := p) (K := K) u⁻¹ u
  exact eq_neg_of_add_eq_zero_left (by simpa using hmul.symm)

omit [NumberField.IsCMField K] in
/-- The completed logarithm sends an integer power to an integer multiple. -/
theorem completedLog_zpow
    (u : completedLogDomain (p := p) (K := K)) (n : ℤ) :
    completedLog (p := p) (K := K) (u ^ n) =
      n • completedLog (p := p) (K := K) u := by
  cases n with
  | ofNat n =>
      simpa using completedLog_pow (p := p) (K := K) u n
  | negSucc n =>
      calc
        completedLog (p := p) (K := K) (u ^ Int.negSucc n) =
            completedLog (p := p) (K := K) ((u ^ (n + 1))⁻¹) := by
              simp
        _ = -completedLog (p := p) (K := K) (u ^ (n + 1)) :=
              completedLog_inv (p := p) (K := K) (u ^ (n + 1))
        _ = -(↑(n + 1) • completedLog (p := p) (K := K) u) := by
              rw [completedLog_pow]
        _ = Int.negSucc n • completedLog (p := p) (K := K) u :=
              (negSucc_zsmul
                (completedLog (p := p) (K := K) u) n).symm

omit [NumberField.IsCMField K] in
/-- The completed logarithm sends a finite product to a finite sum. -/
theorem completedLog_finset_prod {ι : Type*}
    (s : Finset ι) (u : ι → completedLogDomain (p := p) (K := K)) :
    completedLog (p := p) (K := K) (∏ i ∈ s, u i) =
      ∑ i ∈ s, completedLog (p := p) (K := K) (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, completedLog_mul, ih]

omit [NumberField.IsCMField K] in
/-- The valued principal-unit logarithm-domain element attached to a real unit
after raising to `p - 1`. -/
noncomputable def EPlus_completedLogDomainPowPred (u : (𝓞 K⁺)ˣ) :
    completedLogDomain (p := p) (K := K) :=
  ⟨(EPlus_valuedLocalImage (p := p) (K := K) u) ^ (p - 1), by
    simpa using
      EPlus_valuedLocalImage_pow_pred_sub_one_mem_lambdaIdeal
        (p := p) (K := K) u⟩

omit [NumberField.IsCMField K] in
@[simp]
theorem EPlus_completedLogDomainPowPred_coe (u : (𝓞 K⁺)ˣ) :
    ((EPlus_completedLogDomainPowPred (p := p) (K := K) u :
        (ValuedIntegerRing p K)ˣ) : ValuedIntegerRing p K) =
      (EPlus_valuedLocalImage (p := p) (K := K) u : ValuedIntegerRing p K) ^
        (p - 1) :=
  rfl

omit [NumberField.IsCMField K] in
/-- The real-unit `(p - 1)`-power log-domain witness is multiplicative. -/
theorem EPlus_completedLogDomainPowPred_mul (u v : (𝓞 K⁺)ˣ) :
    EPlus_completedLogDomainPowPred (p := p) (K := K) (u * v) =
      EPlus_completedLogDomainPowPred (p := p) (K := K) u *
        EPlus_completedLogDomainPowPred (p := p) (K := K) v := by
  apply Subtype.ext
  apply Units.ext
  simp [EPlus_completedLogDomainPowPred, EPlus_valuedLocalImage, mul_pow]

omit [NumberField.IsCMField K] in
@[simp]
theorem EPlus_completedLogDomainPowPred_one :
    EPlus_completedLogDomainPowPred (p := p) (K := K) (1 : (𝓞 K⁺)ˣ) =
      1 := by
  apply Subtype.ext
  apply Units.ext
  simp [EPlus_completedLogDomainPowPred, EPlus_valuedLocalImage]

omit [NumberField.IsCMField K] in
/-- The real-unit `(p - 1)`-power log-domain witness sends powers to powers. -/
theorem EPlus_completedLogDomainPowPred_pow (u : (𝓞 K⁺)ˣ) (n : ℕ) :
    EPlus_completedLogDomainPowPred (p := p) (K := K) (u ^ n) =
      (EPlus_completedLogDomainPowPred (p := p) (K := K) u) ^ n := by
  apply Subtype.ext
  apply Units.ext
  simp only [EPlus_completedLogDomainPowPred_coe, EPlus_valuedLocalImage_coe,
    Units.val_pow_eq_pow_val, map_pow, SubmonoidClass.coe_pow]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

omit [NumberField.IsCMField K] in
/-- The real-unit `(p - 1)`-power log-domain witness sends inverses to inverses. -/
theorem EPlus_completedLogDomainPowPred_inv (u : (𝓞 K⁺)ˣ) :
    EPlus_completedLogDomainPowPred (p := p) (K := K) u⁻¹ =
      (EPlus_completedLogDomainPowPred (p := p) (K := K) u)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  simp [EPlus_completedLogDomainPowPred, EPlus_valuedLocalImage]

omit [NumberField.IsCMField K] in
/-- The real-unit `(p - 1)`-power log-domain witness sends integer powers to integer powers. -/
theorem EPlus_completedLogDomainPowPred_zpow (u : (𝓞 K⁺)ˣ) (n : ℤ) :
    EPlus_completedLogDomainPowPred (p := p) (K := K) (u ^ n) =
      (EPlus_completedLogDomainPowPred (p := p) (K := K) u) ^ n := by
  cases n with
  | ofNat n =>
      simpa using EPlus_completedLogDomainPowPred_pow (p := p) (K := K) u n
  | negSucc n =>
      simp [zpow_negSucc, EPlus_completedLogDomainPowPred_inv,
        EPlus_completedLogDomainPowPred_pow]

omit [NumberField.IsCMField K] in
/-- The real-unit `(p - 1)`-power log-domain witness sends finite products to finite products. -/
theorem EPlus_completedLogDomainPowPred_finset_prod {ι : Type*}
    (s : Finset ι) (u : ι → (𝓞 K⁺)ˣ) :
    EPlus_completedLogDomainPowPred (p := p) (K := K) (∏ i ∈ s, u i) =
      ∏ i ∈ s, EPlus_completedLogDomainPowPred (p := p) (K := K) (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.prod_empty, EPlus_completedLogDomainPowPred_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        EPlus_completedLogDomainPowPred_mul, ih]

omit [NumberField.IsCMField K] in
/-- For odd `p`, the log-domain witness of any power of `-1` is trivial. -/
theorem EPlus_completedLogDomainPowPred_neg_one_zpow
    (hp_odd : p ≠ 2) (s : ℤ) :
    EPlus_completedLogDomainPowPred (p := p) (K := K)
        ((-1 : (𝓞 K⁺)ˣ) ^ s) =
      1 := by
  apply Subtype.ext
  let y : (ValuedIntegerRing p K)ˣ :=
    EPlus_valuedLocalImage (p := p) (K := K) ((-1 : (𝓞 K⁺)ˣ) ^ s)
  have hy_sq : y ^ 2 = 1 := by
    have hsq_real : (((-1 : (𝓞 K⁺)ˣ) ^ s) ^ 2) = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have heven : Even (s * (2 : ℤ)) := ⟨s, by ring⟩
      exact Even.neg_one_zpow heven
    apply Units.ext
    simpa [y, EPlus_valuedLocalImage] using
      congrArg
        (fun z : (𝓞 K⁺)ˣ ↦
          ((EPlus_valuedLocalImage (p := p) (K := K) z : (ValuedIntegerRing p K)ˣ) :
            ValuedIntegerRing p K))
        hsq_real
  have hp_mod : p % 2 = 1 :=
    Nat.odd_iff.mp ((Fact.out : Nat.Prime p).odd_of_ne_two hp_odd)
  have h_even : Even (p - 1) := by
    rw [Nat.even_iff]
    omega
  rcases h_even with ⟨k, hk⟩
  change y ^ (p - 1) = 1
  rw [hk, show k + k = 2 * k by omega, pow_mul, hy_sq, one_pow]

theorem completedLog_EPlus_CPlusGenerator_powPred
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    completedLog (p := p) (K := K)
        (EPlus_completedLogDomainPowPred (p := p) (K := K)
          (CPlusGenerator (p := p) (K := K) hp_three a)) =
      kummerLogCompletedColumn (p := p) (K := K) hp_three a := by
  apply AdicCompletion.ext_evalₐ
  intro N
  cases N with
  | zero =>
      rw [completedLog_evalₐ, kummerLogCompletedColumn_evalₐ]
      simp
  | succ N =>
      rw [completedLog_evalₐ_succ,
        kummerLogCompletedColumn_evalₐ_succ_eq_samePrimeFiniteLog]
      have harg :
          completedLogArg (p := p) (K := K)
              (EPlus_completedLogDomainPowPred (p := p) (K := K)
                (CPlusGenerator (p := p) (K := K) hp_three a)) =
            kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a := by
        simp [completedLogArg, EPlus_completedLogDomainPowPred,
          EPlus_valuedLocalImage, kummerLogColumnFiniteLogArg,
          kummerLogValuedCyclotomicUnit, kummerLogRealCyclotomicUnit,
          CPlusGenerator]
      exact samePrimeFiniteLog_eq_of_eq (p := p) (K := K) (N := N)
        harg
        (completedLogArg_mem (p := p) (K := K)
          (EPlus_completedLogDomainPowPred (p := p) (K := K)
            (CPlusGenerator (p := p) (K := K) hp_three a)))
        (kummerLogColumnFiniteLogArg_mem_lambdaIdeal
          (p := p) (K := K) hp_three a)

theorem completedLog_EPlus_CPlusExponentProduct_powPred_eq_sum
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (s : ℤ)
    (e : Fin (kummerLogRank p) → ℤ) :
    completedLog (p := p) (K := K)
        (EPlus_completedLogDomainPowPred (p := p) (K := K)
          (CPlusExponentProduct (p := p) (K := K) hp_three s e)) =
      ∑ a : Fin (kummerLogRank p),
        e a • kummerLogCompletedColumn (p := p) (K := K) hp_three a := by
  classical
  unfold CPlusExponentProduct
  rw [EPlus_completedLogDomainPowPred_mul, completedLog_mul,
    EPlus_completedLogDomainPowPred_neg_one_zpow (p := p) (K := K) hp_odd,
    completedLog_one, zero_add]
  rw [EPlus_completedLogDomainPowPred_finset_prod, completedLog_finset_prod]
  refine Finset.sum_congr rfl ?_
  intro a _ha
  rw [EPlus_completedLogDomainPowPred_zpow, completedLog_zpow,
    completedLog_EPlus_CPlusGenerator_powPred]

omit [NumberField.IsCMField K] in
theorem completedLog_EPlus_completedLogDomainPowPred_mem_pPowerSubgroup
    {x : (𝓞 K⁺)ˣ}
    (hpow : x ∈ pPowerSubgroup (EPlus (K := K)) p) :
    ∃ y : DworkCompleteIntegerRing p K,
      p • y =
        completedLog (p := p) (K := K)
          (EPlus_completedLogDomainPowPred (p := p) (K := K) x) := by
  rcases hpow with ⟨u, _hu, hu_pow⟩
  refine ⟨completedLog (p := p) (K := K)
      (EPlus_completedLogDomainPowPred (p := p) (K := K) u), ?_⟩
  calc
    p • completedLog (p := p) (K := K)
        (EPlus_completedLogDomainPowPred (p := p) (K := K) u)
        =
      completedLog (p := p) (K := K)
        ((EPlus_completedLogDomainPowPred (p := p) (K := K) u) ^ p) :=
        (completedLog_pow_p_eq_p_smul
          (p := p) (K := K)
          (EPlus_completedLogDomainPowPred (p := p) (K := K) u)).symm
    _ =
      completedLog (p := p) (K := K)
        (EPlus_completedLogDomainPowPred (p := p) (K := K) (u ^ p)) := by
        rw [EPlus_completedLogDomainPowPred_pow]
    _ =
      completedLog (p := p) (K := K)
        (EPlus_completedLogDomainPowPred (p := p) (K := K) x) := by
        rw [hu_pow]

/-- CU-14b3: a `CPlus` exponent product that is a `p`th power in `EPlus`
gives a `p`-divisible completed logarithm relation in the fixed Dwork
subalgebra. -/
theorem completedLog_relation_of_CPlus_product_mem_powers
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (s : ℤ)
    (e : Fin (kummerLogRank p) → ℤ)
    (hpow :
      CPlusExponentProduct (p := p) (K := K) hp_three s e ∈
        pPowerSubgroup (EPlus (K := K)) p) :
    ∃ y : dworkFixedSubalgebra p K,
      p • y =
        ∑ a : Fin (kummerLogRank p),
          e a • kummerLogFixedColumn (p := p) (K := K) hp_three a := by
  classical
  let S : dworkFixedSubalgebra p K :=
    ∑ a : Fin (kummerLogRank p),
      e a • kummerLogFixedColumn (p := p) (K := K) hp_three a
  rcases completedLog_EPlus_completedLogDomainPowPred_mem_pPowerSubgroup
      (p := p) (K := K) (x :=
        CPlusExponentProduct (p := p) (K := K) hp_three s e) hpow with
    ⟨y, hy⟩
  have hyS : p • y = (S : DworkCompleteIntegerRing p K) := by
    calc
      p • y =
          completedLog (p := p) (K := K)
            (EPlus_completedLogDomainPowPred (p := p) (K := K)
              (CPlusExponentProduct (p := p) (K := K) hp_three s e)) := hy
      _ =
          ∑ a : Fin (kummerLogRank p),
            e a • kummerLogCompletedColumn (p := p) (K := K) hp_three a :=
          completedLog_EPlus_CPlusExponentProduct_powPred_eq_sum
            (p := p) (K := K) hp_odd hp_three s e
      _ = (S : DworkCompleteIntegerRing p K) := by
          simp [S, kummerLogFixedColumn]
  have hfixed_y :
      PadicLogSetup.DworkParameter.Conjugation.dworkCompleteComplexConj
          (p := p) K y = y := by
    have hconjS :
        PadicLogSetup.DworkParameter.Conjugation.dworkCompleteComplexConj
            (p := p) K (S : DworkCompleteIntegerRing p K) =
          (S : DworkCompleteIntegerRing p K) :=
      S.2
    have hconj_y :
        p •
            PadicLogSetup.DworkParameter.Conjugation.dworkCompleteComplexConj
              (p := p) K y =
          (S : DworkCompleteIntegerRing p K) := by
      simpa [map_nsmul, hconjS] using
        congrArg
          (PadicLogSetup.DworkParameter.Conjugation.dworkCompleteComplexConj
            (p := p) K) hyS
    have hzero :
        p •
            (PadicLogSetup.DworkParameter.Conjugation.dworkCompleteComplexConj
                (p := p) K y - y) = 0 := by
      rw [nsmul_sub, hconj_y, hyS, sub_self]
    exact sub_eq_zero.mp
      (dworkComplete_natCast_p_nsmul_eq_zero (p := p) (K := K) hzero)
  refine ⟨⟨y, hfixed_y⟩, ?_⟩
  exact Subtype.ext <| hyS

omit [NumberField.IsCMField K] in
/-- If an element of the fixed Dwork subalgebra is a `p`-multiple, then each
positive Kummer row coordinate vanishes modulo `p`. -/
theorem dworkFixedEvenPowerBasis_coeff_zmod_eq_zero_of_p_smul
    (hp_five : 5 ≤ p) {x y : dworkFixedSubalgebra p K}
    (hy : p • y = x) (j : Fin (kummerLogRank p)) :
    rationalPadicIntegerToZMod p
        ((dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr x
          (kummerLogEvenPowerIndex (p := p) hp_five j)) = 0 := by
  let b := dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)
  let i := kummerLogEvenPowerIndex (p := p) hp_five j
  have hrepr : b.repr (p • y) = p • b.repr y :=
    ((b.repr : dworkFixedSubalgebra p K →ₗ[RationalPadicIntegerRing p]
        dworkEvenPowerIndex p →₀ RationalPadicIntegerRing p).toAddMonoidHom.map_nsmul p y)
  calc
    rationalPadicIntegerToZMod p
        ((dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr x
          (kummerLogEvenPowerIndex (p := p) hp_five j))
        =
      rationalPadicIntegerToZMod p
        ((dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr
          (p • y) (kummerLogEvenPowerIndex (p := p) hp_five j)) := by
        rw [hy]
    _ =
      p • rationalPadicIntegerToZMod p
        ((dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr y
          (kummerLogEvenPowerIndex (p := p) hp_five j)) := by
        change rationalPadicIntegerToZMod p ((b.repr (p • y)) i) =
          p • rationalPadicIntegerToZMod p ((b.repr y) i)
        rw [hrepr]
        simp
    _ = 0 := by
        simp

/-- The `j`th row of the concrete Kummer matrix against integer exponents is
the mod-`p` Kummer coordinate of the corresponding completed-log linear
combination. -/
theorem concreteKummerLogMatrix_mulVec_exponents_eq_coeff
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (e : Fin (kummerLogRank p) → ℤ) (j : Fin (kummerLogRank p)) :
    (Matrix.mulVec (concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five)
        (fun a : Fin (kummerLogRank p) ↦ (e a : ZMod p))) j =
      rationalPadicIntegerToZMod p
        ((dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr
          (∑ a : Fin (kummerLogRank p),
            e a • concreteKummerLogVector (p := p) (K := K) hp_three a)
          (kummerLogEvenPowerIndex (p := p) hp_five j)) := by
  classical
  let b := dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)
  let i := kummerLogEvenPowerIndex (p := p) hp_five j
  let v : Fin (kummerLogRank p) → dworkFixedSubalgebra p K :=
    concreteKummerLogVector (p := p) (K := K) hp_three
  let f : dworkFixedSubalgebra p K →ₗ[RationalPadicIntegerRing p]
      dworkEvenPowerIndex p →₀ RationalPadicIntegerRing p :=
    b.repr
  have hrepr :
      (b.repr (∑ a : Fin (kummerLogRank p), e a • v a)) i =
        ∑ a : Fin (kummerLogRank p), e a • ((b.repr (v a)) i) := by
    have hsum :
        f (∑ a : Fin (kummerLogRank p), e a • v a) =
          ∑ a : Fin (kummerLogRank p), f (e a • v a) :=
      map_sum f (fun a : Fin (kummerLogRank p) ↦ e a • v a) Finset.univ
    have hterm :
        ∀ a : Fin (kummerLogRank p), f (e a • v a) = e a • f (v a) := fun a ↦
      f.toAddMonoidHom.map_zsmul (e a) (v a)
    calc
      (b.repr (∑ a : Fin (kummerLogRank p), e a • v a)) i =
          (f (∑ a : Fin (kummerLogRank p), e a • v a)) i := rfl
      _ = (∑ a : Fin (kummerLogRank p), f (e a • v a)) i := by
          rw [hsum]
      _ = (∑ a : Fin (kummerLogRank p), e a • f (v a)) i := by
          rw [Finset.sum_congr rfl fun a _ha ↦ hterm a]
      _ = ∑ a : Fin (kummerLogRank p), e a • ((b.repr (v a)) i) := by
          simp [f]
  have hright :
      rationalPadicIntegerToZMod p
        ((dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr
          (∑ a : Fin (kummerLogRank p),
            e a • concreteKummerLogVector (p := p) (K := K) hp_three a)
          (kummerLogEvenPowerIndex (p := p) hp_five j)) =
        ∑ a : Fin (kummerLogRank p),
          (e a : ZMod p) *
            rationalPadicIntegerToZMod p ((b.repr (v a)) i) := by
    change rationalPadicIntegerToZMod p
        ((b.repr (∑ a : Fin (kummerLogRank p), e a • v a)) i) =
      ∑ a : Fin (kummerLogRank p),
        (e a : ZMod p) * rationalPadicIntegerToZMod p ((b.repr (v a)) i)
    rw [hrepr, map_sum]
    refine Finset.sum_congr rfl ?_
    intro a _ha
    rw [map_zsmul]
    simp [zsmul_eq_mul]
  have hleft :
      (Matrix.mulVec (concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five)
          (fun a : Fin (kummerLogRank p) ↦ (e a : ZMod p))) j =
        ∑ a : Fin (kummerLogRank p),
          rationalPadicIntegerToZMod p ((b.repr (v a)) i) * (e a : ZMod p) := by
    simp [Matrix.mulVec, dotProduct, concreteKummerLogMatrix_apply,
      concreteKummerLogCoeff_eq, b, i, v]
  rw [hleft, hright]
  exact Finset.sum_congr rfl fun a _ha ↦
    mul_comm (rationalPadicIntegerToZMod p ((b.repr (v a)) i)) (e a : ZMod p)

/-- CU-14c: extracting Kummer coordinates from a `p`-divisible completed-log
relation gives the concrete Kummer matrix kernel equation over `ZMod p`. -/
theorem concreteKummerLogMatrix_mulVec_exponents_eq_zero
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (e : Fin (kummerLogRank p) → ℤ)
    (hlog : ∃ y : dworkFixedSubalgebra p K,
      p • y =
        ∑ a : Fin (kummerLogRank p),
          e a • concreteKummerLogVector (p := p) (K := K) hp_three a) :
    Matrix.mulVec
        (concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five)
        (fun a : Fin (kummerLogRank p) ↦ (e a : ZMod p)) =
      0 := by
  classical
  rcases hlog with ⟨y, hy⟩
  ext j
  rw [Pi.zero_apply]
  rw [concreteKummerLogMatrix_mulVec_exponents_eq_coeff
    (p := p) (K := K) hp_three hp_five e j]
  exact dworkFixedEvenPowerBasis_coeff_zmod_eq_zero_of_p_smul
    (p := p) (K := K) hp_five hy j

/-- CU-14e: determinant nonvanishing forces the generator exponents in a
`p`th-power relation to vanish modulo `p`. -/
theorem CPlusGenerator_exponents_modP_zero_of_kummerLog_det_ne_zero
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (s : ℤ) (e : Fin (kummerLogRank p) → ℤ)
    (hdet : (concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five).det ≠ 0)
    (hpow :
      CPlusExponentProduct (p := p) (K := K) hp_three s e ∈
        pPowerSubgroup (EPlus (K := K)) p) :
    ∀ a : Fin (kummerLogRank p), (e a : ZMod p) = 0 := by
  have hlog :
      ∃ y : dworkFixedSubalgebra p K,
        p • y =
          ∑ a : Fin (kummerLogRank p),
            e a • concreteKummerLogVector (p := p) (K := K) hp_three a := by
    simpa [concreteKummerLogVector] using
      completedLog_relation_of_CPlus_product_mem_powers
        (p := p) (K := K) (by omega : p ≠ 2) hp_three s e hpow
  exact exponents_modP_eq_zero_of_kummerLogMatrix_relation
    (p := p) (K := K) hp_three hp_five e hdet
    (concreteKummerLogMatrix_mulVec_exponents_eq_zero
      (p := p) (K := K) hp_three hp_five e hlog)

/-- CU-14f: Kummer matrix determinant nonvanishing gives exact `p`-saturation
of the real cyclotomic-unit subgroup in the full real-unit group. -/
theorem cyclotomicUnits_pSaturated_of_kummerLog_det_ne_zero
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (hdet : (concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five).det ≠ 0) :
    pSaturated (CPlus (p := p) (K := K) hp_three) (EPlus (K := K)) p := by
  refine CPlus_pSaturated_of_generator_exponents_modP_zero
    (p := p) (K := K) (by omega : p ≠ 2) hp_three ?_
  intro s e hpow
  exact CPlusGenerator_exponents_modP_zero_of_kummerLog_det_ne_zero
    (p := p) (K := K) hp_three hp_five s e hdet hpow

end CyclotomicUnits
end BernoulliRegular

end
