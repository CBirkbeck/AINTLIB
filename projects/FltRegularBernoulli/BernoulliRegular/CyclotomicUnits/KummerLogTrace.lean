module

public import BernoulliRegular.CyclotomicUnits.KummerLogMatrix
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.Part3

/-!
# Trace source for the Kummer logarithm columns

This file proves the honest finite-quotient trace/augmentation input for the
Kummer logarithm columns: the product of all cyclotomic conjugates of the
powered real cyclotomic unit has norm one, hence the finite same-prime
logarithms of those conjugates sum to zero.
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open BernoulliRegular.Reflection.Local
open BernoulliRegular.Furtwaengler.KummerArtinHasse
open scoped BigOperators NumberField

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

namespace KummerLogTrace

variable [NumberField.IsCMField K]

theorem prod_valuedIntegerCyclotomicEquiv_kummerLogValuedCyclotomicUnit
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (∏ σ : CyclotomicUnitDelta p,
        Conjugation.valuedIntegerCyclotomicEquiv (p := p) K σ
          (kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a :
            ValuedIntegerRing p K)) = 1 := by
  classical
  let k : ℕ := kummerLogColumnIndex (p := p) hp_three a
  have hk : k.Coprime p :=
    realCyclotomicUnit_index_coprime (p := p)
      (kummerLogColumnIndex_two_le (p := p) hp_three a)
      (kummerLogColumnIndex_le_half (p := p) hp_three a)
  have hp_odd : p ≠ 2 := by omega
  calc
    (∏ σ : CyclotomicUnitDelta p,
        Conjugation.valuedIntegerCyclotomicEquiv (p := p) K σ
          (kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a :
            ValuedIntegerRing p K))
        =
        ∏ σ : CyclotomicUnitDelta p,
          algebraMap (𝓞 K) (ValuedIntegerRing p K)
            (cyclotomicRingOfIntegersEquiv (p := p) K σ
              (FLT37.realCyclotomicUnit p K k)) := by
          refine Finset.prod_congr rfl ?_
          intro σ _hσ
          simp [k, Conjugation.valuedIntegerCyclotomicEquiv_algebraMap_ringOfIntegers]
    _ =
        algebraMap (𝓞 K) (ValuedIntegerRing p K)
          (∏ σ : CyclotomicUnitDelta p,
            cyclotomicRingOfIntegersEquiv (p := p) K σ
              (FLT37.realCyclotomicUnit p K k)) :=
          (map_prod (algebraMap (𝓞 K) (ValuedIntegerRing p K))
            (fun σ : CyclotomicUnitDelta p ↦
              cyclotomicRingOfIntegersEquiv (p := p) K σ
                (FLT37.realCyclotomicUnit p K k))
            Finset.univ).symm
    _ =
        algebraMap (𝓞 K) (ValuedIntegerRing p K)
          (((Algebra.norm ℤ (FLT37.realCyclotomicUnit p K k) : ℤ) : 𝓞 K)) := by
          rw [Furtwaengler.prod_cyclotomicRingOfIntegersEquiv_eq_intNorm]
    _ = 1 := by
          rw [FLT37.realCyclotomicUnit_norm_int (p := p) (K := K) k hk hp_odd]
          simp

theorem prod_one_add_cyclotomic_kummerLogColumnFiniteLogArg
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (∏ σ : CyclotomicUnitDelta p,
        (1 +
          Conjugation.valuedIntegerCyclotomicEquiv (p := p) K σ
            (kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a))) = 1 := by
  classical
  let u : CyclotomicUnitDelta p → ValuedIntegerRing p K := fun σ ↦
    Conjugation.valuedIntegerCyclotomicEquiv (p := p) K σ
      (kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a :
        ValuedIntegerRing p K)
  have hprod :
      (∏ σ : CyclotomicUnitDelta p, u σ) = 1 :=
    prod_valuedIntegerCyclotomicEquiv_kummerLogValuedCyclotomicUnit
      (p := p) (K := K) hp_three a
  calc
    (∏ σ : CyclotomicUnitDelta p,
        (1 +
          Conjugation.valuedIntegerCyclotomicEquiv (p := p) K σ
            (kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a)))
        =
        ∏ σ : CyclotomicUnitDelta p, (u σ) ^ (p - 1) := by
          refine Finset.prod_congr rfl ?_
          intro σ _hσ
          simp [u, kummerLogColumnFiniteLogArg, map_sub, map_pow]
    _ = (∏ σ : CyclotomicUnitDelta p, u σ) ^ (p - 1) :=
          Finset.prod_pow Finset.univ (p - 1) u
    _ = 1 := by
          rw [hprod, one_pow]

theorem samePrimeFiniteLogFinsetProductCoord_cyclotomic_kummerLogColumn_eq_zero
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    Conjugation.samePrimeFiniteLogFinsetProductCoord (p := p) (K := K)
        (Finset.univ : Finset (CyclotomicUnitDelta p))
        (fun σ ↦
          Conjugation.valuedIntegerCyclotomicEquiv (p := p) K σ
            (kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a)) = 0 := by
  unfold Conjugation.samePrimeFiniteLogFinsetProductCoord
  rw [prod_one_add_cyclotomic_kummerLogColumnFiniteLogArg
    (p := p) (K := K) hp_three a]
  simp

theorem sum_samePrimeFiniteLog_cyclotomic_kummerLogColumn_eq_zero
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    (∑ σ ∈ (Finset.univ : Finset (CyclotomicUnitDelta p)).attach,
        samePrimeFiniteLog (p := p) (K := K) N
          (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K σ.1
            (kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a))
          (Conjugation.valuedIntegerCyclotomicEquiv_mem_lambdaIdeal
            (p := p) (K := K) σ.1
            (kummerLogColumnFiniteLogArg_mem_lambdaIdeal
              (p := p) (K := K) hp_three a))) = 0 := by
  classical
  let x : CyclotomicUnitDelta p → ValuedIntegerRing p K := fun σ ↦
    Conjugation.valuedIntegerCyclotomicEquiv (p := p) K σ
      (kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a)
  have hx : ∀ σ ∈ (Finset.univ : Finset (CyclotomicUnitDelta p)),
      x σ ∈ lambdaIdeal p K := fun σ _hσ ↦
    Conjugation.valuedIntegerCyclotomicEquiv_mem_lambdaIdeal
      (p := p) (K := K) σ
      (kummerLogColumnFiniteLogArg_mem_lambdaIdeal (p := p) (K := K) hp_three a)
  have hlog :=
    Conjugation.samePrimeFiniteLog_finsetProductCoord
      (p := p) (K := K) (ι := CyclotomicUnitDelta p) N
      (s := Finset.univ) (x := x) hx
  have hcoord :
      Conjugation.samePrimeFiniteLogFinsetProductCoord (p := p) (K := K)
          (Finset.univ : Finset (CyclotomicUnitDelta p)) x = 0 :=
    samePrimeFiniteLogFinsetProductCoord_cyclotomic_kummerLogColumn_eq_zero
      (p := p) (K := K) hp_three a
  have hleft :
      samePrimeFiniteLog (p := p) (K := K) N
          (Conjugation.samePrimeFiniteLogFinsetProductCoord (p := p) (K := K)
            (Finset.univ : Finset (CyclotomicUnitDelta p)) x)
          (Conjugation.samePrimeFiniteLogFinsetProductCoord_mem_lambdaIdeal
            (p := p) (K := K) hx) =
        samePrimeFiniteLog (p := p) (K := K) N 0 ((lambdaIdeal p K).zero_mem) :=
    samePrimeFiniteLog_eq_of_eq (p := p) (K := K) (N := N) hcoord
      (Conjugation.samePrimeFiniteLogFinsetProductCoord_mem_lambdaIdeal
        (p := p) (K := K) hx)
      ((lambdaIdeal p K).zero_mem)
  rw [hleft] at hlog
  simpa [x, samePrimeFiniteLog_arg_zero] using hlog.symm

theorem sum_samePrimeFiniteLog_cyclotomic_kummerLogColumn_univ_eq_zero
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    (∑ σ : CyclotomicUnitDelta p,
        samePrimeFiniteLog (p := p) (K := K) N
          (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K σ
            (kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a))
          (Conjugation.valuedIntegerCyclotomicEquiv_mem_lambdaIdeal
            (p := p) (K := K) σ
            (kummerLogColumnFiniteLogArg_mem_lambdaIdeal
              (p := p) (K := K) hp_three a))) = 0 := by
  have h :=
    sum_samePrimeFiniteLog_cyclotomic_kummerLogColumn_eq_zero
      (p := p) (K := K) hp_three a N
  simpa [Finset.sum_attach] using h

theorem sum_dworkCompleteCyclotomicEquiv_kummerLogCompletedColumn_eq_zero
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (∑ σ : CyclotomicUnitDelta p,
        Conjugation.dworkCompleteCyclotomicEquiv (p := p) K σ
          (kummerLogCompletedColumn (p := p) (K := K) hp_three a)) = 0 := by
  classical
  apply AdicCompletion.ext_evalₐ
  intro N
  cases N with
  | zero =>
      trans 0
      · exact quotient_pow_zero_eq_zero (p := p) (K := K) (lambdaIdeal p K)
          (AdicCompletion.evalₐ (lambdaIdeal p K) 0
            (∑ σ : CyclotomicUnitDelta p,
              Conjugation.dworkCompleteCyclotomicEquiv (p := p) K σ
                (kummerLogCompletedColumn (p := p) (K := K) hp_three a)))
      · symm
        exact quotient_pow_zero_eq_zero (p := p) (K := K) (lambdaIdeal p K)
          (AdicCompletion.evalₐ (lambdaIdeal p K) 0
            (0 : DworkCompleteIntegerRing p K))
  | succ N =>
      rw [map_sum]
      trans
        (∑ σ : CyclotomicUnitDelta p,
          samePrimeFiniteLog (p := p) (K := K) N
            (Conjugation.valuedIntegerCyclotomicEquiv (p := p) K σ
              (kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a))
            (Conjugation.valuedIntegerCyclotomicEquiv_mem_lambdaIdeal
              (p := p) (K := K) σ
              (kummerLogColumnFiniteLogArg_mem_lambdaIdeal
                (p := p) (K := K) hp_three a)))
      · refine Finset.sum_congr rfl ?_
        intro σ _hσ
        rw [Conjugation.evalₐ_dworkCompleteCyclotomicEquiv,
          kummerLogCompletedColumn_evalₐ_succ]
        exact Conjugation.samePrimeFiniteLog_quotientMap_cyclotomic
          (p := p) (K := K) σ
          (kummerLogColumnFiniteLogArg_mem_lambdaIdeal
            (p := p) (K := K) hp_three a)
      · exact sum_samePrimeFiniteLog_cyclotomic_kummerLogColumn_univ_eq_zero
          (p := p) (K := K) hp_three a N

omit [NumberField.IsCMField K] in
theorem dworkParameterPowerLinearMap_repr
    (x : DworkCompleteIntegerRing p K) :
    dworkParameterPowerLinearMap p K ((dworkParameterPowerBasis p K).repr x) = x := by
  rw [dworkParameterPowerLinearMap_apply]
  conv_rhs => rw [← (dworkParameterPowerBasis p K).sum_repr x]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dworkParameterPowerBasis_apply]
  exact (Algebra.smul_def _ _).symm

omit [NumberField.IsCMField K] in
theorem dworkEvenPowerLinearMap_repr
    (hp_two : 2 < p) (x : dworkFixedSubalgebra p K) :
    dworkEvenPowerLinearMap (p := p) (K := K) hp_two
        ((dworkFixedEvenPowerBasis (p := p) (K := K) hp_two).repr x) = x := by
  rw [dworkFixedEvenPowerBasis]
  exact LinearEquiv.apply_symm_apply
    (LinearEquiv.ofBijective
      (dworkEvenPowerLinearMap (p := p) (K := K) hp_two)
      (dworkEvenPowerLinearMap_bijective (p := p) (K := K) hp_two)) x

omit [NumberField.IsCMField K] in
theorem dworkFixedEvenPowerBasis_repr_zero_eq_powerBasis_repr
    (hp_two : 2 < p) (x : dworkFixedSubalgebra p K) :
    (dworkFixedEvenPowerBasis (p := p) (K := K) hp_two).repr x
        (dworkEvenPowerIndexZero (p := p)) =
      (dworkParameterPowerBasis p K).repr
        (x : DworkCompleteIntegerRing p K) (dworkEvenPowerIndexZero (p := p)).1 := by
  classical
  let a := (dworkFixedEvenPowerBasis (p := p) (K := K) hp_two).repr x
  have h_even :
      dworkEvenPowerLinearMap (p := p) (K := K) hp_two a = x :=
    dworkEvenPowerLinearMap_repr (p := p) (K := K) hp_two x
  have h_even_val :
      dworkParameterPowerLinearMap p K (dworkEvenCoeffExtend p a) =
        (x : DworkCompleteIntegerRing p K) := by
    simpa [dworkEvenPowerLinearMap, a] using congrArg Subtype.val h_even
  have h_full :
      dworkParameterPowerLinearMap p K
          ((dworkParameterPowerBasis p K).repr
            (x : DworkCompleteIntegerRing p K)) =
        (x : DworkCompleteIntegerRing p K) :=
    dworkParameterPowerLinearMap_repr (p := p) (K := K) (x : DworkCompleteIntegerRing p K)
  have hcoeff :
      (dworkParameterPowerBasis p K).repr (x : DworkCompleteIntegerRing p K) =
        dworkEvenCoeffExtend p a :=
    dworkParameterPowerLinearMap_injective (p := p) (K := K)
      (h_full.trans h_even_val.symm)
  have hzero := congrFun hcoeff (dworkEvenPowerIndexZero (p := p)).1
  symm
  simpa [a, dworkEvenCoeffExtend, dworkEvenPowerIndexZero] using hzero

omit [NumberField.IsCMField K] in
theorem dworkParameterPowerBasis_repr_cyclotomic_zero
    (σ : CyclotomicUnitDelta p) (x : DworkCompleteIntegerRing p K) :
    (dworkParameterPowerBasis p K).repr
        (Conjugation.dworkCompleteCyclotomicEquiv (p := p) K σ x)
        (dworkEvenPowerIndexZero (p := p)).1 =
      (dworkParameterPowerBasis p K).repr x (dworkEvenPowerIndexZero (p := p)).1 := by
  classical
  let c : Fin (p - 1) → RationalPadicIntegerRing p :=
    fun i ↦ (dworkParameterPowerBasis p K).repr x i
  have hx : dworkParameterPowerLinearMap p K c = x :=
    by simpa [c] using dworkParameterPowerLinearMap_repr (p := p) (K := K) x
  have haction :
      Conjugation.dworkCompleteCyclotomicEquiv (p := p) K σ x =
        dworkParameterPowerLinearMap p K
          (fun i ↦ rationalPadicTeichmuller p (σ : ZMod p) ^ (i : ℕ) * c i) := by
    rw [← hx]
    exact Conjugation.dworkCompleteCyclotomicEquiv_powerLinearMap
      (p := p) (K := K) σ c
  have hcoeff :
      (fun i : Fin (p - 1) ↦
        (dworkParameterPowerBasis p K).repr
          (Conjugation.dworkCompleteCyclotomicEquiv (p := p) K σ x) i) =
        (fun i : Fin (p - 1) ↦
          rationalPadicTeichmuller p (σ : ZMod p) ^ (i : ℕ) * c i) := by
    apply dworkParameterPowerLinearMap_injective (p := p) (K := K)
    rw [show dworkParameterPowerLinearMap p K
          (fun i : Fin (p - 1) ↦
            (dworkParameterPowerBasis p K).repr
              (Conjugation.dworkCompleteCyclotomicEquiv (p := p) K σ x) i) =
        Conjugation.dworkCompleteCyclotomicEquiv (p := p) K σ x by
          simpa using dworkParameterPowerLinearMap_repr (p := p) (K := K)
            (Conjugation.dworkCompleteCyclotomicEquiv (p := p) K σ x),
      haction]
  have hzero := congrFun hcoeff (dworkEvenPowerIndexZero (p := p)).1
  simpa [c, dworkEvenPowerIndexZero] using hzero

omit [NumberField.IsCMField K] in
theorem dworkParameterPowerBasis_repr_sum_cyclotomic_zero
    (x : DworkCompleteIntegerRing p K) :
    (dworkParameterPowerBasis p K).repr
        (∑ σ : CyclotomicUnitDelta p,
          Conjugation.dworkCompleteCyclotomicEquiv (p := p) K σ x)
        (dworkEvenPowerIndexZero (p := p)).1 =
      (Fintype.card (CyclotomicUnitDelta p) : RationalPadicIntegerRing p) *
        (dworkParameterPowerBasis p K).repr x
          (dworkEvenPowerIndexZero (p := p)).1 := by
  classical
  rw [map_sum]
  simp [dworkParameterPowerBasis_repr_cyclotomic_zero (p := p) (K := K),
    nsmul_eq_mul]

theorem kummerLogFixedColumn_constantCoeff_eq_zero
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr
        (kummerLogFixedColumn (p := p) (K := K) hp_three a)
        (dworkEvenPowerIndexZero (p := p)) = 0 := by
  classical
  let x : DworkCompleteIntegerRing p K :=
    kummerLogCompletedColumn (p := p) (K := K) hp_three a
  let c0 : RationalPadicIntegerRing p :=
    (dworkParameterPowerBasis p K).repr x (dworkEvenPowerIndexZero (p := p)).1
  have htrace :
      (∑ σ : CyclotomicUnitDelta p,
          Conjugation.dworkCompleteCyclotomicEquiv (p := p) K σ x) = 0 := by
    simpa [x] using
      sum_dworkCompleteCyclotomicEquiv_kummerLogCompletedColumn_eq_zero
        (p := p) (K := K) hp_three a
  have hcard_mul :
      (Fintype.card (CyclotomicUnitDelta p) : RationalPadicIntegerRing p) * c0 = 0 := by
    have hcoord := congrArg
      (fun y : DworkCompleteIntegerRing p K ↦
        (dworkParameterPowerBasis p K).repr y (dworkEvenPowerIndexZero (p := p)).1)
      htrace
    change (dworkParameterPowerBasis p K).repr
        (∑ σ : CyclotomicUnitDelta p,
          Conjugation.dworkCompleteCyclotomicEquiv (p := p) K σ x)
        (dworkEvenPowerIndexZero (p := p)).1 =
      (dworkParameterPowerBasis p K).repr
        (0 : DworkCompleteIntegerRing p K) (dworkEvenPowerIndexZero (p := p)).1 at hcoord
    rw [dworkParameterPowerBasis_repr_sum_cyclotomic_zero] at hcoord
    simpa [c0] using hcoord
  have hcard_pos : 0 < Fintype.card (CyclotomicUnitDelta p) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  have hcard_ne :
      (Fintype.card (CyclotomicUnitDelta p) : RationalPadicIntegerRing p) ≠ 0 := by
    intro h
    have hval :
        (Fintype.card (CyclotomicUnitDelta p) :
          (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) = 0 := by
      simpa using congrArg Subtype.val h
    letI : CharZero ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) :=
      algebraRat.charZero ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
    exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hcard_pos)) hval
  have hc0 : c0 = 0 :=
    (mul_eq_zero.mp hcard_mul).resolve_left hcard_ne
  have hbridge :=
    dworkFixedEvenPowerBasis_repr_zero_eq_powerBasis_repr
      (p := p) (K := K) (by omega : 2 < p)
      (kummerLogFixedColumn (p := p) (K := K) hp_three a)
  rw [hbridge]
  simpa [c0, x, kummerLogFixedColumn] using hc0

end KummerLogTrace

theorem kummerLogFixedColumn_constantCoeff_eq_zero
    [NumberField.IsCMField K] (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr
        (kummerLogFixedColumn (p := p) (K := K) hp_three a)
        (dworkEvenPowerIndexZero (p := p)) = 0 :=
  KummerLogTrace.kummerLogFixedColumn_constantCoeff_eq_zero
    (p := p) (K := K) hp_three a

/-- The concrete logarithm vector produced from the selected real cyclotomic
units by the same-prime finite logarithm construction in the Dwork completion. -/
noncomputable def concreteKummerLogVector
    [NumberField.IsCMField K] (hp_three : 3 ≤ p) :
    KummerLogVector (p := p) (K := K) :=
  fun a ↦ kummerLogFixedColumn (p := p) (K := K) hp_three a

@[simp]
theorem concreteKummerLogVector_apply
    [NumberField.IsCMField K] (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    concreteKummerLogVector (p := p) (K := K) hp_three a =
      kummerLogFixedColumn (p := p) (K := K) hp_three a :=
  rfl

/-- The unreduced Kummer coefficient of the concrete logarithm vector is the
corresponding even-power Dwork coordinate of the completed logarithm column. -/
theorem concreteKummerLogCoeffLift_eq
    [NumberField.IsCMField K] (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    kummerLogCoeffLift (p := p) (K := K) hp_five
        (concreteKummerLogVector (p := p) (K := K) hp_three) j a =
      (dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr
        (kummerLogFixedColumn (p := p) (K := K) hp_three a)
        (kummerLogEvenPowerIndex (p := p) hp_five j) :=
  rfl

/-- The reduced Kummer coefficient of the concrete logarithm vector is the
mod-`p` reduction of the matching even-power Dwork coordinate. -/
theorem concreteKummerLogCoeff_eq
    [NumberField.IsCMField K] (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    kummerLogCoeff (p := p) (K := K) hp_five
        (concreteKummerLogVector (p := p) (K := K) hp_three) j a =
      rationalPadicIntegerToZMod p
        ((dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr
          (kummerLogFixedColumn (p := p) (K := K) hp_three a)
          (kummerLogEvenPowerIndex (p := p) hp_five j)) :=
  rfl

/-- The concrete coefficient matrix obtained from the completed logarithm
columns. -/
noncomputable def concreteKummerLogMatrix
    [NumberField.IsCMField K] (hp_three : 3 ≤ p) (hp_five : 5 ≤ p) :
    Matrix (Fin (kummerLogRank p)) (Fin (kummerLogRank p)) (ZMod p) :=
  kummerLogMatrix (p := p) (K := K) hp_five
    (concreteKummerLogVector (p := p) (K := K) hp_three)

@[simp]
theorem concreteKummerLogMatrix_apply
    [NumberField.IsCMField K] (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    concreteKummerLogMatrix (p := p) (K := K) hp_three hp_five j a =
      kummerLogCoeff (p := p) (K := K) hp_five
        (concreteKummerLogVector (p := p) (K := K) hp_three) j a :=
  rfl

/-- The constant even-power coordinate of every concrete logarithm vector
column vanishes exactly. -/
theorem concreteKummerLogVector_constantCoeff_eq_zero
    [NumberField.IsCMField K] (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (dworkFixedEvenPowerBasis (p := p) (K := K) (by omega : 2 < p)).repr
        (concreteKummerLogVector (p := p) (K := K) hp_three a)
        (dworkEvenPowerIndexZero (p := p)) = 0 := by
  simpa using
    kummerLogFixedColumn_constantCoeff_eq_zero (p := p) (K := K) hp_three a

end CyclotomicUnits
end BernoulliRegular

end
