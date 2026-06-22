module

public import BernoulliRegular.CyclotomicUnits.DworkParameter
public import BernoulliRegular.CyclotomicUnits.Vandermonde
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.ConductorFlexiblePhiFacts

/-!
# The Kummer logarithm coefficient matrix

This file packages the coefficient-extraction layer for the logarithmic
matrix in Kummer's cyclotomic-unit criterion.  The analytic construction of
the cyclotomic-unit logarithm vector is deliberately an input here: once a
column has been placed in the conjugation-fixed Dwork subalgebra, its
coordinates in the even-power Dwork basis give the desired matrix entries
modulo `p`.
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

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- A placeholder for the future analytic logarithm columns.  A value of this
type assigns to each Kummer column a conjugation-fixed element of the completed
Dwork integer ring. -/
abbrev KummerLogVector : Type _ :=
  Fin (kummerLogRank p) → dworkFixedSubalgebra p K

/-- The row `j` of Kummer's matrix corresponds to the even Dwork exponent
`2 * (j + 1)`, i.e. to `varpi^(2j)` with mathematical row numbering
`j = 1, ..., (p - 3) / 2`. -/
def kummerLogEvenPowerIndex (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    dworkEvenPowerIndex p :=
  ⟨⟨2 * ((j : ℕ) + 1), by
      have hjle : (j : ℕ) + 1 ≤ kummerLogRank p :=
        Nat.succ_le_of_lt j.isLt
      have hmulrank : 2 * kummerLogRank p ≤ p - 3 := by
        simpa [kummerLogRank, Nat.mul_comm] using
          Nat.div_mul_le_self (p - 3) 2
      have hle : 2 * ((j : ℕ) + 1) ≤ 2 * kummerLogRank p :=
        Nat.mul_le_mul_left 2 hjle
      omega⟩,
    ⟨(j : ℕ) + 1, by
      change 2 * ((j : ℕ) + 1) = (j : ℕ) + 1 + ((j : ℕ) + 1)
      omega⟩⟩

omit [Fact p.Prime] in
@[simp]
theorem kummerLogEvenPowerIndex_val
    (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    ((kummerLogEvenPowerIndex (p := p) hp_five j).1 : ℕ) =
      2 * ((j : ℕ) + 1) :=
  rfl

/-- The coefficient of `varpi^(2 * (j + 1))` in a fixed Dwork logarithm
column, before reduction modulo `p`. -/
def kummerLogCoeffLift
    (hp_five : 5 ≤ p) (logVec : KummerLogVector (p := p) (K := K))
    (j a : Fin (kummerLogRank p)) :
    RationalPadicIntegerRing p :=
  (dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr
    (logVec a) (kummerLogEvenPowerIndex (p := p) hp_five j)

/-- The mod-`p` coefficient of `varpi^(2 * (j + 1))` in a fixed Dwork
logarithm column. -/
def kummerLogCoeff
    (hp_five : 5 ≤ p) (logVec : KummerLogVector (p := p) (K := K))
    (j a : Fin (kummerLogRank p)) : ZMod p :=
  rationalPadicIntegerToZMod p
    (kummerLogCoeffLift (p := p) (K := K) hp_five logVec j a)

/-- The Kummer logarithm coefficient matrix attached to a supplied fixed
logarithm vector. -/
def kummerLogMatrix
    (hp_five : 5 ≤ p) (logVec : KummerLogVector (p := p) (K := K)) :
    Matrix (Fin (kummerLogRank p)) (Fin (kummerLogRank p)) (ZMod p) :=
  fun j a ↦ kummerLogCoeff (p := p) (K := K) hp_five logVec j a

@[simp]
theorem kummerLogMatrix_apply
    (hp_five : 5 ≤ p) (logVec : KummerLogVector (p := p) (K := K))
    (j a : Fin (kummerLogRank p)) :
    kummerLogMatrix (p := p) (K := K) hp_five logVec j a =
      kummerLogCoeff (p := p) (K := K) hp_five logVec j a :=
  rfl

theorem kummerLogCoeffLift_eq_basis_repr
    (hp_five : 5 ≤ p) (logVec : KummerLogVector (p := p) (K := K))
    (j a : Fin (kummerLogRank p)) :
    kummerLogCoeffLift (p := p) (K := K) hp_five logVec j a =
      (dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr
        (logVec a) (kummerLogEvenPowerIndex (p := p) hp_five j) :=
  rfl

theorem kummerLogCoeff_eq_reduction
    (hp_five : 5 ≤ p) (logVec : KummerLogVector (p := p) (K := K))
    (j a : Fin (kummerLogRank p)) :
    kummerLogCoeff (p := p) (K := K) hp_five logVec j a =
      rationalPadicIntegerToZMod p
        (kummerLogCoeffLift (p := p) (K := K) hp_five logVec j a) :=
  rfl

/-- The selected row basis vector is the Dwork monomial
`varpi^(2 * (j + 1))`. -/
theorem dworkFixedEvenPowerBasis_kummerLogEvenPowerIndex
    (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    ((dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)
      (kummerLogEvenPowerIndex (p := p) hp_five j)) :
        DworkCompleteIntegerRing p K) =
      dworkParameter p K ^ (2 * ((j : ℕ) + 1)) := by
  have h :=
    congrArg Subtype.val
      (dworkFixedEvenPowerBasis_apply (p := p) (K := K)
        (by omega : 2 < p) (kummerLogEvenPowerIndex (p := p) hp_five j))
  simpa [kummerLogEvenPowerIndex] using h

/-- Every supplied logarithm column expands in the fixed even-power Dwork
basis; `kummerLogCoeffLift` is the coefficient on the positive even rows
selected above. -/
theorem kummerLogColumn_evenPowerExpansion
    (hp_two : 2 < p) (logVec : KummerLogVector (p := p) (K := K))
    (a : Fin (kummerLogRank p)) :
    (∑ i : dworkEvenPowerIndex p,
        ((dworkFixedEvenPowerBasis (p := p) (K := K)
          hp_two).repr (logVec a) i) •
          dworkFixedEvenPowerBasis (p := p) (K := K)
            hp_two i) =
      logVec a :=
  (dworkFixedEvenPowerBasis (p := p) (K := K) hp_two).sum_repr (logVec a)

section RealCyclotomicColumns

variable [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

omit [Fact p.Prime] in
/-- The Kummer logarithm column uses the same integer index as the
`CPlusGenerator` family. -/
theorem kummerLogColumnIndex_eq_CPlusGeneratorIndex
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogColumnIndex (p := p) hp_three a =
      CPlusGeneratorIndex (p := p) hp_three a :=
  rfl

/-- The Kummer logarithm column index lies in the real cyclotomic-unit range. -/
theorem kummerLogColumnIndex_range
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    2 ≤ kummerLogColumnIndex (p := p) hp_three a ∧
      kummerLogColumnIndex (p := p) hp_three a ≤ (p - 1) / 2 :=
  ⟨kummerLogColumnIndex_two_le (p := p) hp_three a,
    kummerLogColumnIndex_le_half (p := p) hp_three a⟩

/-- The real cyclotomic unit selected by the Kummer logarithm column index. -/
noncomputable def kummerLogRealCyclotomicUnit
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) : (𝓞 K⁺)ˣ :=
  realCyclotomicUnit (p := p) (K := K)
    (kummerLogColumnIndex (p := p) hp_three a)
    (kummerLogColumnIndex_two_le (p := p) hp_three a)
    (kummerLogColumnIndex_le_half (p := p) hp_three a)

@[simp]
theorem kummerLogRealCyclotomicUnit_eq_CPlusGenerator
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogRealCyclotomicUnit (p := p) (K := K) hp_three a =
      CPlusGenerator (p := p) (K := K) hp_three a :=
  rfl

@[simp]
theorem kummerLogRealCyclotomicUnit_val
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogRealCyclotomicUnit (p := p) (K := K) hp_three a : 𝓞 K⁺) =
      FLT37.realCyclotomicUnitPlus p K
        (kummerLogColumnIndex (p := p) hp_three a) := by
  simp [kummerLogRealCyclotomicUnit]

theorem algebraMap_kummerLogRealCyclotomicUnit
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    algebraMap (𝓞 K⁺) (𝓞 K)
        (kummerLogRealCyclotomicUnit (p := p) (K := K) hp_three a : 𝓞 K⁺) =
      FLT37.realCyclotomicUnit p K
        (kummerLogColumnIndex (p := p) hp_three a) :=
  algebraMap_realCyclotomicUnit (p := p) (K := K)
    (kummerLogColumnIndex (p := p) hp_three a)
    (kummerLogColumnIndex_two_le (p := p) hp_three a)
    (kummerLogColumnIndex_le_half (p := p) hp_three a)

/-- The Kummer logarithm column, embedded in the lambda-valued local integer
ring at the Dwork prime. -/
noncomputable def kummerLogValuedCyclotomicUnit
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (ValuedIntegerRing p K)ˣ :=
  Units.map (algebraMap (𝓞 K) (ValuedIntegerRing p K)).toMonoidHom
    (Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom
      (kummerLogRealCyclotomicUnit (p := p) (K := K) hp_three a))

@[simp]
theorem kummerLogValuedCyclotomicUnit_coe
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a :
        ValuedIntegerRing p K) =
      algebraMap (𝓞 K) (ValuedIntegerRing p K)
        (FLT37.realCyclotomicUnit p K
          (kummerLogColumnIndex (p := p) hp_three a)) := by
  change algebraMap (𝓞 K) (ValuedIntegerRing p K)
      (algebraMap (𝓞 K⁺) (𝓞 K)
        (kummerLogRealCyclotomicUnit (p := p) (K := K) hp_three a : 𝓞 K⁺)) =
    algebraMap (𝓞 K) (ValuedIntegerRing p K)
      (FLT37.realCyclotomicUnit p K
        (kummerLogColumnIndex (p := p) hp_three a))
  rw [algebraMap_kummerLogRealCyclotomicUnit]

@[simp]
theorem kummerLogValuedCyclotomicUnit_pow_coe
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (n : ℕ) :
    ((kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a) ^ n :
        (ValuedIntegerRing p K)ˣ) =
      Units.map (algebraMap (𝓞 K) (ValuedIntegerRing p K)).toMonoidHom
        (Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom
          ((kummerLogRealCyclotomicUnit (p := p) (K := K) hp_three a) ^ n)) := by
  simp [kummerLogValuedCyclotomicUnit]

/-- The Kummer logarithm column as a unit in the completed Dwork integer
ring. -/
noncomputable def kummerLogDworkCyclotomicUnit
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (DworkCompleteIntegerRing p K)ˣ :=
  Units.map
    (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)).toMonoidHom
    (kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a)

@[simp]
theorem kummerLogDworkCyclotomicUnit_coe
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogDworkCyclotomicUnit (p := p) (K := K) hp_three a :
        DworkCompleteIntegerRing p K) =
      algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)
        (kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a :
          ValuedIntegerRing p K) :=
  rfl

theorem kummerLogDworkCyclotomicUnit_coe_eq_global
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogDworkCyclotomicUnit (p := p) (K := K) hp_three a :
        DworkCompleteIntegerRing p K) =
      algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)
        (algebraMap (𝓞 K) (ValuedIntegerRing p K)
          (FLT37.realCyclotomicUnit p K
            (kummerLogColumnIndex (p := p) hp_three a))) := by
  simp [kummerLogDworkCyclotomicUnit]

@[simp]
theorem kummerLogDworkCyclotomicUnit_pow_coe
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (n : ℕ) :
    ((kummerLogDworkCyclotomicUnit (p := p) (K := K) hp_three a) ^ n :
        DworkCompleteIntegerRing p K) =
      algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)
        ((kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a :
          ValuedIntegerRing p K) ^ n) := by
  simp [kummerLogDworkCyclotomicUnit]

/-- If two elements are congruent modulo an ideal, then so are their powers. -/
theorem pow_sub_pow_mem_of_sub_mem_ideal
    {R : Type*} [CommRing R] (I : Ideal R) {x y : R}
    (hxy : x - y ∈ I) (n : ℕ) :
    x ^ n - y ^ n ∈ I := by
  rcases sub_dvd_pow_sub_pow x y n with ⟨z, hz⟩
  rw [hz]
  exact I.mul_mem_right z hxy

omit [NumberField.IsCMField K] in
/-- Fermat's theorem, as membership in the Dwork lambda ideal for rational
integer constants. -/
theorem natCast_pow_pred_sub_one_mem_lambdaIdeal_of_coprime
    {m : ℕ} (hm : m.Coprime p) :
    (m : ValuedIntegerRing p K) ^ (p - 1) - 1 ∈ lambdaIdeal p K := by
  have hmod :
      (m : ℤ) ^ (p - 1) ≡ 1 [ZMOD (p : ℤ)] :=
    Int.ModEq.pow_card_sub_one_eq_one (Fact.out : Nat.Prime p) hm.isCoprime
  have hdvd_int : (p : ℤ) ∣ (m : ℤ) ^ (p - 1) - 1 :=
    Int.ModEq.dvd (Int.ModEq.symm hmod)
  have hmem_int :
      algebraMap ℤ (ValuedIntegerRing p K) ((m : ℤ) ^ (p - 1) - 1) ∈
        lambdaIdeal p K := by
    rcases hdvd_int with ⟨q, hq⟩
    rw [hq, map_mul]
    exact (lambdaIdeal p K).mul_mem_right (algebraMap ℤ (ValuedIntegerRing p K) q)
      (by simpa using natCast_prime_mem_lambdaIdeal (p := p) (K := K))
  simpa [map_sub, map_pow] using hmem_int

/-- The local Kummer column is congruent to the rational integer `a^2` modulo
the Dwork lambda ideal. -/
theorem kummerLogValuedCyclotomicUnit_sub_natCast_sq_mem_lambdaIdeal
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a :
        ValuedIntegerRing p K) -
        (kummerLogColumnIndex (p := p) hp_three a :
          ValuedIntegerRing p K) ^ 2 ∈
      lambdaIdeal p K := by
  let k : ℕ := kummerLogColumnIndex (p := p) hp_three a
  have hglobal :
      FLT37.realCyclotomicUnit p K k - (k : 𝓞 K) ^ 2 ∈
        Reflection.Local.cyclotomicLambda p K := by
    rw [Reflection.Local.cyclotomicLambda, zetaPrime, Ideal.mem_span_singleton]
    exact FLT37.zetaSubOne_dvd_realCyclotomicUnit_sub_sq (p := p) (K := K) k
  have hmap :
      algebraMap (𝓞 K) (ValuedIntegerRing p K)
          (FLT37.realCyclotomicUnit p K k - (k : 𝓞 K) ^ 2) ∈
        Ideal.map (algebraMap (𝓞 K) (ValuedIntegerRing p K))
          (Reflection.Local.cyclotomicLambda p K) :=
    Ideal.mem_map_of_mem (algebraMap (𝓞 K) (ValuedIntegerRing p K)) hglobal
  rw [lambdaIdeal_eq_map_cyclotomicLambda (p := p) (K := K)] at hmap
  change (kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a :
        ValuedIntegerRing p K) - (k : ValuedIntegerRing p K) ^ 2 ∈
      lambdaIdeal p K
  simpa [kummerLogValuedCyclotomicUnit_coe, map_sub, map_pow] using hmap

/-- Raising the local Kummer column to `p - 1` gives a principal unit in the
lambda-adic sense used by the Dwork finite logarithms. -/
theorem kummerLogValuedCyclotomicUnit_pow_pred_sub_one_mem_lambdaIdeal
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    ((kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a :
        ValuedIntegerRing p K) ^ (p - 1) - 1) ∈
      lambdaIdeal p K := by
  let k : ℕ := kummerLogColumnIndex (p := p) hp_three a
  let u : ValuedIntegerRing p K :=
    (kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a :
      ValuedIntegerRing p K)
  let c : ValuedIntegerRing p K := (k : ValuedIntegerRing p K) ^ 2
  have huc : u - c ∈ lambdaIdeal p K := by
    simpa [u, c, k] using
      kummerLogValuedCyclotomicUnit_sub_natCast_sq_mem_lambdaIdeal
        (p := p) (K := K) hp_three a
  have hupow : u ^ (p - 1) - c ^ (p - 1) ∈ lambdaIdeal p K :=
    pow_sub_pow_mem_of_sub_mem_ideal (lambdaIdeal p K) huc (p - 1)
  have hk_coprime : k.Coprime p :=
    realCyclotomicUnit_index_coprime (p := p)
      (kummerLogColumnIndex_two_le (p := p) hp_three a)
      (kummerLogColumnIndex_le_half (p := p) hp_three a)
  have hk_pos : 0 < k := by
    have hk_two := kummerLogColumnIndex_two_le (p := p) hp_three a
    omega
  have hk_sq_coprime : (k ^ 2).Coprime p := hk_coprime.pow_left 2
  have hcpow :
      c ^ (p - 1) - 1 ∈ lambdaIdeal p K := by
    have h :=
      natCast_pow_pred_sub_one_mem_lambdaIdeal_of_coprime
        (p := p) (K := K) (m := k ^ 2) hk_sq_coprime
    simpa [c, Nat.cast_pow] using h
  have hsum : (u ^ (p - 1) - c ^ (p - 1)) + (c ^ (p - 1) - 1) ∈
      lambdaIdeal p K :=
    (lambdaIdeal p K).add_mem hupow hcpow
  convert hsum using 1
  ring

/-- The powered local Kummer column belongs to the route-level principal-unit
subgroup `1 + lambdaIdeal`. -/
theorem kummerLogValuedCyclotomicUnit_pow_pred_mem_lambdaPrincipalUnits
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a) ^ (p - 1) ∈
      Ideal.oneUnitsSubgroup (lambdaIdeal p K) := by
  rw [Ideal.mem_oneUnitsSubgroup]
  exact kummerLogValuedCyclotomicUnit_pow_pred_sub_one_mem_lambdaIdeal
    (p := p) (K := K) hp_three a

/-- The powered Kummer column is also a principal unit after passing to the
Dwork completion. -/
theorem kummerLogDworkCyclotomicUnit_pow_pred_sub_one_mem_lambdaIdeal
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    ((kummerLogDworkCyclotomicUnit (p := p) (K := K) hp_three a :
        DworkCompleteIntegerRing p K) ^ (p - 1) - 1) ∈
      dworkCompleteLambdaIdeal p K := by
  have hmap :
      algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)
          (((kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a :
            ValuedIntegerRing p K) ^ (p - 1) - 1)) ∈
        Ideal.map (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K))
          (lambdaIdeal p K) :=
    Ideal.mem_map_of_mem
      (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K))
      (kummerLogValuedCyclotomicUnit_pow_pred_sub_one_mem_lambdaIdeal
        (p := p) (K := K) hp_three a)
  simpa [dworkCompleteLambdaIdeal, map_sub, map_pow] using hmap

/-- Route-level principal-unit subgroup statement in the completed Dwork
integer ring. -/
theorem kummerLogDworkCyclotomicUnit_pow_pred_mem_lambdaPrincipalUnits
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogDworkCyclotomicUnit (p := p) (K := K) hp_three a) ^ (p - 1) ∈
      Ideal.oneUnitsSubgroup (dworkCompleteLambdaIdeal p K) := by
  rw [Ideal.mem_oneUnitsSubgroup]
  exact kummerLogDworkCyclotomicUnit_pow_pred_sub_one_mem_lambdaIdeal
    (p := p) (K := K) hp_three a

/-- The additive argument of the ordinary finite logarithm for the powered
Kummer column: `eps_a^(p - 1) = 1 + x`. -/
noncomputable def kummerLogColumnFiniteLogArg
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    ValuedIntegerRing p K :=
  (kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a :
      ValuedIntegerRing p K) ^ (p - 1) - 1

theorem kummerLogColumnFiniteLogArg_mem_lambdaIdeal
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a ∈
      lambdaIdeal p K :=
  kummerLogValuedCyclotomicUnit_pow_pred_sub_one_mem_lambdaIdeal
    (p := p) (K := K) hp_three a

/-- The finite quotient logarithm of the powered Kummer column. -/
noncomputable def kummerLogColumnFiniteLog
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  samePrimeFiniteLog (p := p) (K := K) N
    (kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a)
    (kummerLogColumnFiniteLogArg_mem_lambdaIdeal (p := p) (K := K) hp_three a)

theorem kummerLogColumnFiniteLog_factorPow
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) {M N : ℕ}
    (hMN : M ≤ N) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (kummerLogColumnFiniteLog (p := p) (K := K) hp_three a N) =
      kummerLogColumnFiniteLog (p := p) (K := K) hp_three a M :=
  samePrimeFiniteLog_factorPow (p := p) (K := K) hMN
    (kummerLogColumnFiniteLogArg_mem_lambdaIdeal (p := p) (K := K) hp_three a)

/-- Quotient coordinates of the completed logarithm column.  The zero-th
coordinate is forced by the quotient modulo the unit ideal. -/
noncomputable def kummerLogColumnCoord
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N :=
  match N with
  | 0 => 0
  | N + 1 => kummerLogColumnFiniteLog (p := p) (K := K) hp_three a N

@[simp]
theorem kummerLogColumnCoord_zero
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogColumnCoord (p := p) (K := K) hp_three a 0 = 0 :=
  rfl

@[simp]
theorem kummerLogColumnCoord_succ
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    kummerLogColumnCoord (p := p) (K := K) hp_three a (N + 1) =
      kummerLogColumnFiniteLog (p := p) (K := K) hp_three a N :=
  rfl

theorem kummerLogColumnCoord_factorPow
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) {M N : ℕ}
    (hMN : M ≤ N) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
        (kummerLogColumnCoord (p := p) (K := K) hp_three a N) =
      kummerLogColumnCoord (p := p) (K := K) hp_three a M := by
  cases M with
  | zero =>
      exact quotient_pow_zero_eq_zero (p := p) (K := K)
        (lambdaIdeal p K)
        (Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
          (kummerLogColumnCoord (p := p) (K := K) hp_three a N))
  | succ M =>
      cases N with
      | zero =>
          exact False.elim (Nat.not_succ_le_zero M hMN)
      | succ N =>
          have hMN' : M ≤ N := Nat.succ_le_succ_iff.mp hMN
          simpa using
            kummerLogColumnFiniteLog_factorPow
              (p := p) (K := K) hp_three a hMN'

/-- The completed local logarithm column attached to the powered real
cyclotomic unit `eps_a^(p - 1)`. -/
noncomputable def kummerLogCompletedColumn
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    DworkCompleteIntegerRing p K :=
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  ⟨fun N ↦
      (Ideal.quotientEquivAlgOfEq R (by
        ext y
        simp : (I ^ N • ⊤ : Ideal R) = I ^ N)).symm
        (kummerLogColumnCoord (p := p) (K := K) hp_three a N),
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
                (kummerLogColumnCoord (p := p) (K := K) hp_three a N)))
            =
          Ideal.Quotient.factorPow I hMN
            (kummerLogColumnCoord (p := p) (K := K) hp_three a N) := by
            refine Quotient.inductionOn'
              (kummerLogColumnCoord (p := p) (K := K) hp_three a N) ?_
            intro r
            rfl
        _ = kummerLogColumnCoord (p := p) (K := K) hp_three a M :=
            kummerLogColumnCoord_factorPow
              (p := p) (K := K) hp_three a hMN
        _ = (Ideal.quotientEquivAlgOfEq R hEqM)
            ((Ideal.quotientEquivAlgOfEq R hEqM).symm
              (kummerLogColumnCoord (p := p) (K := K) hp_three a M)) := by
            refine Quotient.inductionOn'
              (kummerLogColumnCoord (p := p) (K := K) hp_three a M) ?_
            intro r
            rfl
      ⟩

@[simp]
theorem kummerLogCompletedColumn_evalₐ
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N
        (kummerLogCompletedColumn (p := p) (K := K) hp_three a) =
      kummerLogColumnCoord (p := p) (K := K) hp_three a N := by
  unfold kummerLogCompletedColumn
  let hEq :
      ((lambdaIdeal p K) ^ N • ⊤ : Ideal (ValuedIntegerRing p K)) =
        (lambdaIdeal p K) ^ N := by
    ext y
    simp
  change
    (Ideal.quotientEquivAlgOfEq (ValuedIntegerRing p K) hEq)
      ((Ideal.quotientEquivAlgOfEq (ValuedIntegerRing p K) hEq).symm
        (kummerLogColumnCoord (p := p) (K := K) hp_three a N)) =
      kummerLogColumnCoord (p := p) (K := K) hp_three a N
  refine Quotient.inductionOn'
    (kummerLogColumnCoord (p := p) (K := K) hp_three a N) ?_
  intro r
  rfl

@[simp]
theorem kummerLogCompletedColumn_evalₐ_succ
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) (N + 1)
        (kummerLogCompletedColumn (p := p) (K := K) hp_three a) =
      kummerLogColumnFiniteLog (p := p) (K := K) hp_three a N := by
  simp [kummerLogCompletedColumn_evalₐ]

theorem kummerLogCompletedColumn_evalₐ_succ_eq_samePrimeFiniteLog
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) (N + 1)
        (kummerLogCompletedColumn (p := p) (K := K) hp_three a) =
      samePrimeFiniteLog (p := p) (K := K) N
        (kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a)
        (kummerLogColumnFiniteLogArg_mem_lambdaIdeal
          (p := p) (K := K) hp_three a) := by
  simp [kummerLogColumnFiniteLog]

namespace PadicLogSetup.DworkParameter.Conjugation

omit [NumberField.IsCMField K] in
theorem valuedIntegerComplexConj_algebraMap_ringOfIntegers
    (x : 𝓞 K) :
    valuedIntegerComplexConj (p := p) K
        (algebraMap (𝓞 K) (ValuedIntegerRing p K) x) =
      algebraMap (𝓞 K) (ValuedIntegerRing p K)
        (cyclotomicRingOfIntegersEquiv (p := p) K (-1) x) := by
  ext
  change valuedCompletionCyclotomicEquiv (p := p) K (-1)
      (algebraMap (𝓞 K) (ValuedCompletion p K) x) =
    algebraMap (𝓞 K) (ValuedCompletion p K)
      (cyclotomicRingOfIntegersEquiv (p := p) K (-1) x)
  rw [show algebraMap (𝓞 K) (ValuedCompletion p K) x =
      algebraMap K (ValuedCompletion p K) (x : K) from rfl]
  rw [show algebraMap (𝓞 K) (ValuedCompletion p K)
      (cyclotomicRingOfIntegersEquiv (p := p) K (-1) x) =
      algebraMap K (ValuedCompletion p K)
        ((cyclotomicRingOfIntegersEquiv (p := p) K (-1) x : 𝓞 K) : K) from rfl]
  rw [valuedCompletionCyclotomicEquiv_algebraMap,
    map_cyclotomicRingOfIntegersEquiv_coe]

omit [NumberField.IsCMField K] in
theorem valuedIntegerComplexConj_mem_lambdaIdeal_pow {N : ℕ}
    {x : ValuedIntegerRing p K} (hx : x ∈ (lambdaIdeal p K) ^ N) :
    valuedIntegerComplexConj (p := p) K x ∈ (lambdaIdeal p K) ^ N :=
  ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
    (valuedIntegerComplexConj (p := p) K)
    (lambdaIdeal_map_valuedIntegerComplexConj (p := p) (K := K)) N hx

omit [NumberField.IsCMField K] in
theorem valuedIntegerComplexConj_mem_lambdaIdeal
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    valuedIntegerComplexConj (p := p) K x ∈ lambdaIdeal p K := by
  simpa [pow_one] using
    valuedIntegerComplexConj_mem_lambdaIdeal_pow
      (p := p) (K := K) (N := 1) (by simpa [pow_one] using hx)

omit [NumberField.IsCMField K] in
theorem quotientNatCastInv_quotientMap_complexConj
    (N m : ℕ) (hm : Nat.Coprime m p) :
    Ideal.quotientMap ((lambdaIdeal p K) ^ (N + 1))
        (valuedIntegerComplexConj (p := p) K :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (valuedIntegerComplexConj (p := p) K)
          (lambdaIdeal_map_valuedIntegerComplexConj (p := p) (K := K)) (N + 1))
        (quotientNatCastInv (p := p) (K := K) N m hm) =
      quotientNatCastInv (p := p) (K := K) N m hm := by
  let e : ValuedIntegerRing p K ≃+* ValuedIntegerRing p K :=
    valuedIntegerComplexConj (p := p) K
  let φ :
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) →+*
        ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    Ideal.quotientMap ((lambdaIdeal p K) ^ (N + 1))
      (e : ValuedIntegerRing p K →+* ValuedIntegerRing p K)
      (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K) e
        (lambdaIdeal_map_valuedIntegerComplexConj (p := p) (K := K)) (N + 1))
  have hspec :=
    congrArg φ (quotientNatCastInv_spec_right (p := p) (K := K) N m hm)
  symm
  refine quotientNatCastInv_eq_of_mul_right_eq_one
    (p := p) (K := K) (N := N) (m := m) hm ?_
  simpa [φ, e] using hspec

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteLogTermNumerator_complexConj {n : ℕ} (hn : n ≠ 0)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    valuedIntegerComplexConj (p := p) K
        (samePrimeFiniteLogTermNumerator (p := p) (K := K) n x hx) =
      samePrimeFiniteLogTermNumerator (p := p) (K := K) n
        (valuedIntegerComplexConj (p := p) K x)
        (valuedIntegerComplexConj_mem_lambdaIdeal (p := p) (K := K) hx) := by
  let e : ValuedIntegerRing p K ≃+* ValuedIntegerRing p K :=
    valuedIntegerComplexConj (p := p) K
  let hx' : e x ∈ lambdaIdeal p K :=
    valuedIntegerComplexConj_mem_lambdaIdeal (p := p) (K := K) hx
  let y : ValuedIntegerRing p K :=
    samePrimeFiniteLogTermNumerator (p := p) (K := K) n x hx
  let y' : ValuedIntegerRing p K :=
    samePrimeFiniteLogTermNumerator (p := p) (K := K) n (e x) hx'
  have hy : (p : ValuedIntegerRing p K) ^ n.factorization p * y = x ^ n :=
    samePrimeFiniteLogTermNumerator_mul_spec (p := p) (K := K) hn hx
  have hy' : (p : ValuedIntegerRing p K) ^ n.factorization p * y' = (e x) ^ n :=
    samePrimeFiniteLogTermNumerator_mul_spec (p := p) (K := K) hn hx'
  have hspec : (p : ValuedIntegerRing p K) ^ n.factorization p * e y =
      (p : ValuedIntegerRing p K) ^ n.factorization p * y' := by
    calc
      (p : ValuedIntegerRing p K) ^ n.factorization p * e y =
          e ((p : ValuedIntegerRing p K) ^ n.factorization p * y) := by
            rw [map_mul, map_pow]
            simp [e]
      _ = e (x ^ n) := by rw [hy]
      _ = (e x) ^ n := by rw [map_pow]
      _ = (p : ValuedIntegerRing p K) ^ n.factorization p * y' := by rw [hy']
  exact mul_left_cancel₀
    (pow_ne_zero _ (natCast_prime_ne_zero_valuedInteger (p := p) (K := K)))
    hspec

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteLogTermCore_quotientMap_complexConj {N n : ℕ}
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.quotientMap ((lambdaIdeal p K) ^ (N + 1))
        (valuedIntegerComplexConj (p := p) K :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (valuedIntegerComplexConj (p := p) K)
          (lambdaIdeal_map_valuedIntegerComplexConj (p := p) (K := K)) (N + 1))
        (samePrimeFiniteLogTermCore (p := p) (K := K) N n x hx) =
      samePrimeFiniteLogTermCore (p := p) (K := K) N n
        (valuedIntegerComplexConj (p := p) K x)
        (valuedIntegerComplexConj_mem_lambdaIdeal (p := p) (K := K) hx) := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [samePrimeFiniteLogTermCore, samePrimeFiniteLogTermCore, dif_neg hn, dif_neg hn]
  rw [map_mul, quotientNatCastInv_quotientMap_complexConj]
  change Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (valuedIntegerComplexConj (p := p) K
          (samePrimeFiniteLogTermNumerator (p := p) (K := K) n x hx)) *
      quotientNatCastInv (p := p) (K := K) N (ordCompl[p] n)
        (samePrimeFiniteLog_ordCompl_coprime (p := p) hn) =
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (samePrimeFiniteLogTermNumerator (p := p) (K := K) n
          (valuedIntegerComplexConj (p := p) K x)
          (valuedIntegerComplexConj_mem_lambdaIdeal (p := p) (K := K) hx)) *
      quotientNatCastInv (p := p) (K := K) N (ordCompl[p] n)
        (samePrimeFiniteLog_ordCompl_coprime (p := p) hn)
  rw [samePrimeFiniteLogTermNumerator_complexConj (p := p) (K := K) hn hx]

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteLogTerm_quotientMap_complexConj {N n : ℕ}
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.quotientMap ((lambdaIdeal p K) ^ (N + 1))
        (valuedIntegerComplexConj (p := p) K :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (valuedIntegerComplexConj (p := p) K)
          (lambdaIdeal_map_valuedIntegerComplexConj (p := p) (K := K)) (N + 1))
        (samePrimeFiniteLogTerm (p := p) (K := K) N n x hx) =
      samePrimeFiniteLogTerm (p := p) (K := K) N n
        (valuedIntegerComplexConj (p := p) K x)
        (valuedIntegerComplexConj_mem_lambdaIdeal (p := p) (K := K) hx) := by
  rw [samePrimeFiniteLogTerm, samePrimeFiniteLogTerm]
  rw [map_mul, map_pow]
  rw [samePrimeFiniteLogTermCore_quotientMap_complexConj (p := p) (K := K) hx]
  simp

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteLog_quotientMap_complexConj {N : ℕ}
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.quotientMap ((lambdaIdeal p K) ^ (N + 1))
        (valuedIntegerComplexConj (p := p) K :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (valuedIntegerComplexConj (p := p) K)
          (lambdaIdeal_map_valuedIntegerComplexConj (p := p) (K := K)) (N + 1))
        (samePrimeFiniteLog (p := p) (K := K) N x hx) =
      samePrimeFiniteLog (p := p) (K := K) N
        (valuedIntegerComplexConj (p := p) K x)
        (valuedIntegerComplexConj_mem_lambdaIdeal (p := p) (K := K) hx) := by
  classical
  unfold samePrimeFiniteLog
  rw [map_sum]
  exact Finset.sum_congr rfl fun n _hn ↦
    samePrimeFiniteLogTerm_quotientMap_complexConj (p := p) (K := K) hx

end PadicLogSetup.DworkParameter.Conjugation

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteLog_level_zero
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) 0 x hx = 0 := by
  classical
  unfold samePrimeFiniteLog
  refine Finset.sum_eq_zero fun n _hn ↦ ?_
  by_cases hn : n = 0
  · subst n
    simp
  rcases (Ideal.mem_map_iff_of_surjective
      (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (0 + 1)))
      Ideal.Quotient.mk_surjective).1
      (samePrimeFiniteLogTerm_mem_map_lambdaIdeal_pow
        (p := p) (K := K) hn hx) with
    ⟨y, hy, hyq⟩
  rw [← hyq, Ideal.Quotient.eq_zero_iff_mem]
  have horder : 1 ≤ samePrimeFiniteLogTermOrder (p := p) n :=
    one_le_samePrimeFiniteLogTermOrder (p := p) hn
  simpa [pow_one] using Ideal.pow_le_pow_right horder hy

omit [NumberField.IsCMField K] in
/-- The zero even exponent in the fixed Dwork basis. -/
def dworkEvenPowerIndexZero : dworkEvenPowerIndex p :=
  ⟨⟨0, by
      have hp_one : 1 < p := (Fact.out : Nat.Prime p).one_lt
      omega⟩,
    ⟨0, rfl⟩⟩

omit [NumberField.IsCMField K] in
@[simp]
theorem dworkEvenPowerIndexZero_val :
    (((dworkEvenPowerIndexZero (p := p)).1 : Fin (p - 1)) : ℕ) = 0 :=
  rfl

omit [NumberField.IsCMField K] in
theorem dworkEvenPowerIndex_pos_of_ne_zero
    {i : dworkEvenPowerIndex p} (hi : i ≠ dworkEvenPowerIndexZero (p := p)) :
    0 < (((i.1 : Fin (p - 1)) : ℕ)) := by
  by_contra h
  have hnat : (((i.1 : Fin (p - 1)) : ℕ)) = 0 := Nat.eq_zero_of_not_pos h
  apply hi
  apply Subtype.ext
  apply Fin.ext
  simpa [dworkEvenPowerIndexZero] using hnat

set_option synthInstance.maxHeartbeats 80000 in
-- The proof repeatedly forms quotient rings of the completed Dwork ring; the
-- local aliases keep the statement readable but make quotient-ring instance
-- search slightly deeper than the default budget.
set_option maxHeartbeats 400000 in
-- The proof normalizes the basis expansion through quotient maps and ideal
-- membership before applying the existing scalar-prime-ideal criterion.
omit [NumberField.IsCMField K] in
theorem dworkFixedEvenPower_constantCoeff_mem_primeIdeal_of_mem_parameterIdeal
    (hp_two : 2 < p) {x : dworkFixedSubalgebra p K}
    (hx : (x : DworkCompleteIntegerRing p K) ∈ dworkParameterIdeal p K) :
    (dworkFixedEvenPowerBasis (p := p) (K := K) hp_two).repr x
        (dworkEvenPowerIndexZero (p := p)) ∈
      rationalPadicPrimeIdeal p := by
  classical
  let R₀ : Type := RationalPadicIntegerRing p
  let S : Type _ := DworkCompleteIntegerRing p K
  let I : Ideal S := dworkParameterIdeal p K
  let q : S →+* S ⧸ I := Ideal.Quotient.mk I
  let b := dworkFixedEvenPowerBasis (p := p) (K := K) hp_two
  let a : dworkEvenPowerIndex p → R₀ := b.repr x
  have hrepr := congrArg Subtype.val (b.sum_repr x)
  have hrepr' :
      (∑ i : dworkEvenPowerIndex p,
          algebraMap R₀ S (a i) *
            dworkParameter p K ^ (((i.1 : Fin (p - 1)) : ℕ))) =
        (x : S) := by
    rw [← hrepr]
    push_cast [a, b, R₀, S, Algebra.smul_def, dworkFixedEvenPowerBasis_apply]
    rfl
  have hxq : q (x : S) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa [I, S] using hx)
  have hsumq :
      q (∑ i : dworkEvenPowerIndex p,
          algebraMap R₀ S (a i) *
            dworkParameter p K ^ (((i.1 : Fin (p - 1)) : ℕ))) = 0 := by
    rw [hrepr', hxq]
  have hsumq' :
      (∑ i : dworkEvenPowerIndex p,
          q (algebraMap R₀ S (a i) *
            dworkParameter p K ^ (((i.1 : Fin (p - 1)) : ℕ)))) = 0 := by
    simpa [map_sum] using hsumq
  have hsingle :
      (∑ i : dworkEvenPowerIndex p,
          q (algebraMap R₀ S (a i) *
            dworkParameter p K ^ (((i.1 : Fin (p - 1)) : ℕ)))) =
        q (algebraMap R₀ S (a (dworkEvenPowerIndexZero (p := p)))) := by
    rw [Finset.sum_eq_single (dworkEvenPowerIndexZero (p := p))]
    · simp
    · intro i _hi hineq
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have hpos : 1 ≤ (((i.1 : Fin (p - 1)) : ℕ)) :=
        dworkEvenPowerIndex_pos_of_ne_zero (p := p) (i := i) hineq
      have hvarpi : dworkParameter p K ∈ I := by
        dsimp [I, dworkParameterIdeal]
        exact Ideal.mem_span_singleton_self (dworkParameter p K)
      have hpow : dworkParameter p K ^ (((i.1 : Fin (p - 1)) : ℕ)) ∈ I := by
        simpa [pow_one] using
          Ideal.pow_le_pow_right hpos
            (Ideal.pow_mem_pow hvarpi (((i.1 : Fin (p - 1)) : ℕ)))
      exact I.mul_mem_left (algebraMap R₀ S (a i)) hpow
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  have hconstq : q (algebraMap R₀ S (a (dworkEvenPowerIndexZero (p := p)))) = 0 := by
    rw [← hsingle]
    exact hsumq'
  have hconst_mem :
      algebraMap R₀ S (a (dworkEvenPowerIndexZero (p := p))) ∈ I :=
    Ideal.Quotient.eq_zero_iff_mem.mp hconstq
  exact rationalPadicInteger_mem_primeIdeal_of_algebraMap_mem_dworkParameterIdeal
    (p := p) (K := K) (c := a (dworkEvenPowerIndexZero (p := p)))
    (by simpa [R₀, S, I] using hconst_mem)

theorem kummerLogValuedCyclotomicUnit_complexConj
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    Conjugation.valuedIntegerComplexConj (p := p) K
        (kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a :
          ValuedIntegerRing p K) =
      (kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a :
        ValuedIntegerRing p K) := by
  have hp_two : 2 < p := by omega
  have hconj :
      ringOfIntegersComplexConj K
          (FLT37.realCyclotomicUnit p K
            (kummerLogColumnIndex (p := p) hp_three a)) =
        FLT37.realCyclotomicUnit p K
          (kummerLogColumnIndex (p := p) hp_three a) :=
    FLT37.realCyclotomicUnit_complexConj p K
      (kummerLogColumnIndex (p := p) hp_three a)
  rw [kummerLogValuedCyclotomicUnit_coe]
  rw [Conjugation.valuedIntegerComplexConj_algebraMap_ringOfIntegers
    (p := p) (K := K)]
  rw [← Furtwaengler.ringOfIntegersComplexConj_eq_cyclotomicRingOfIntegersEquiv_neg_one
    (p := p) (K := K) hp_two]
  rw [hconj]

theorem kummerLogColumnFiniteLogArg_complexConj
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    Conjugation.valuedIntegerComplexConj (p := p) K
        (kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a) =
      kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a := by
  unfold kummerLogColumnFiniteLogArg
  rw [map_sub, map_pow,
    kummerLogValuedCyclotomicUnit_complexConj (p := p) (K := K) hp_three a,
    map_one]

theorem kummerLogColumnFiniteLog_quotientMap_complexConj
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    Ideal.quotientMap ((lambdaIdeal p K) ^ (N + 1))
        (Conjugation.valuedIntegerComplexConj (p := p) K :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (Conjugation.valuedIntegerComplexConj (p := p) K)
          (Conjugation.lambdaIdeal_map_valuedIntegerComplexConj
            (p := p) (K := K)) (N + 1))
        (kummerLogColumnFiniteLog (p := p) (K := K) hp_three a N) =
      kummerLogColumnFiniteLog (p := p) (K := K) hp_three a N := by
  rw [kummerLogColumnFiniteLog]
  rw [Conjugation.samePrimeFiniteLog_quotientMap_complexConj
    (p := p) (K := K)]
  exact samePrimeFiniteLog_eq_of_eq (p := p) (K := K)
    (N := N)
    (kummerLogColumnFiniteLogArg_complexConj (p := p) (K := K) hp_three a)
    (Conjugation.valuedIntegerComplexConj_mem_lambdaIdeal
      (p := p) (K := K)
      (kummerLogColumnFiniteLogArg_mem_lambdaIdeal
        (p := p) (K := K) hp_three a))
    (kummerLogColumnFiniteLogArg_mem_lambdaIdeal (p := p) (K := K) hp_three a)

theorem kummerLogCompletedColumn_complexConj
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    Conjugation.dworkCompleteComplexConj (p := p) K
        (kummerLogCompletedColumn (p := p) (K := K) hp_three a) =
      kummerLogCompletedColumn (p := p) (K := K) hp_three a := by
  apply AdicCompletion.ext_evalₐ
  intro N
  cases N with
  | zero =>
      trans 0
      · exact quotient_pow_zero_eq_zero (p := p) (K := K)
          (lambdaIdeal p K)
          (AdicCompletion.evalₐ (lambdaIdeal p K) 0
            (Conjugation.dworkCompleteComplexConj (p := p) K
              (kummerLogCompletedColumn (p := p) (K := K) hp_three a)))
      · exact (quotient_pow_zero_eq_zero (p := p) (K := K)
          (lambdaIdeal p K)
          (AdicCompletion.evalₐ (lambdaIdeal p K) 0
            (kummerLogCompletedColumn (p := p) (K := K) hp_three a))).symm
  | succ N =>
      rw [Conjugation.evalₐ_dworkCompleteComplexConj,
        kummerLogCompletedColumn_evalₐ_succ]
      exact kummerLogColumnFiniteLog_quotientMap_complexConj
        (p := p) (K := K) hp_three a N

theorem kummerLogCompletedColumn_mem_fixedSubalgebra
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogCompletedColumn (p := p) (K := K) hp_three a ∈
      dworkFixedSubalgebra p K :=
  kummerLogCompletedColumn_complexConj (p := p) (K := K) hp_three a

/-- The completed logarithm column as an element of the conjugation-fixed
Dwork subalgebra. -/
noncomputable def kummerLogFixedColumn
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    dworkFixedSubalgebra p K :=
  ⟨kummerLogCompletedColumn (p := p) (K := K) hp_three a,
    kummerLogCompletedColumn_mem_fixedSubalgebra (p := p) (K := K) hp_three a⟩

theorem kummerLogCompletedColumn_evalₐ_one_eq_zero
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    AdicCompletion.evalₐ (lambdaIdeal p K) 1
        (kummerLogCompletedColumn (p := p) (K := K) hp_three a) = 0 := by
  rw [show (1 : ℕ) = 0 + 1 by rfl,
    kummerLogCompletedColumn_evalₐ_succ]
  exact samePrimeFiniteLog_level_zero (p := p) (K := K)
    (kummerLogColumnFiniteLogArg_mem_lambdaIdeal (p := p) (K := K) hp_three a)

theorem kummerLogCompletedColumn_mem_dworkParameterIdeal
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogCompletedColumn (p := p) (K := K) hp_three a ∈
      dworkParameterIdeal p K := by
  have hmem :
      kummerLogCompletedColumn (p := p) (K := K) hp_three a ∈
        (dworkCompleteLambdaIdeal p K) ^ 1 :=
    dworkComplete_mem_lambdaIdeal_pow_of_evalₐ_eq_zero (p := p) (K := K)
      (n := 1)
      (kummerLogCompletedColumn_evalₐ_one_eq_zero (p := p) (K := K) hp_three a)
  simpa [pow_one, dworkParameterIdeal_eq_dworkCompleteLambdaIdeal
    (p := p) (K := K)] using hmem

theorem kummerLogFixedColumn_constantCoeff_mem_primeIdeal
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr
        (kummerLogFixedColumn (p := p) (K := K) hp_three a)
        (dworkEvenPowerIndexZero (p := p)) ∈
      rationalPadicPrimeIdeal p :=
  dworkFixedEvenPower_constantCoeff_mem_primeIdeal_of_mem_parameterIdeal
    (p := p) (K := K) (by omega : 2 < p)
    (kummerLogCompletedColumn_mem_dworkParameterIdeal
      (p := p) (K := K) hp_three a)

theorem kummerLogFixedColumn_constantCoeff_mod_p_eq_zero
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    rationalPadicIntegerToZMod p
        ((dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr
          (kummerLogFixedColumn (p := p) (K := K) hp_three a)
          (dworkEvenPowerIndexZero (p := p))) = 0 := by
  rw [rationalPadicIntegerToZMod_eq_zero_iff_mem_primeIdeal]
  exact kummerLogFixedColumn_constantCoeff_mem_primeIdeal
    (p := p) (K := K) hp_three a

end RealCyclotomicColumns

end CyclotomicUnits
end BernoulliRegular

end
