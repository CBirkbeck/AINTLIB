module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Part17

/-!
# Full cyclotomic action on the Dwork completion

This file extends the complex-conjugation lift from `Part8Conjugation` to the
full cyclotomic Galois group.  The trace/augmentation argument for the exact
Kummer-log constant term needs this genuine completion automorphism rather than
only the involution at `-1`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

namespace Conjugation

open BernoulliRegular.Reflection.Local
open Furtwaengler.KummerArtinHasse

theorem valuedIntegerCyclotomicEquiv_algebraMap_ringOfIntegers
    (a : CyclotomicUnitDelta p) (x : 𝓞 K) :
    valuedIntegerCyclotomicEquiv (p := p) K a
        (algebraMap (𝓞 K) (ValuedIntegerRing p K) x) =
      algebraMap (𝓞 K) (ValuedIntegerRing p K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a x) := by
  ext
  change valuedCompletionCyclotomicEquiv (p := p) K a
      (algebraMap (𝓞 K) (ValuedCompletion p K) x) =
    algebraMap (𝓞 K) (ValuedCompletion p K)
      (cyclotomicRingOfIntegersEquiv (p := p) K a x)
  rw [show algebraMap (𝓞 K) (ValuedCompletion p K) x =
      algebraMap K (ValuedCompletion p K) (x : K) from rfl]
  rw [valuedCompletionCyclotomicEquiv_algebraMap]
  change algebraMap K (ValuedCompletion p K)
      (cyclotomicSigmaOfUnit (p := p) K a (x : K)) =
    algebraMap K (ValuedCompletion p K)
      ((cyclotomicRingOfIntegersEquiv (p := p) K a x : 𝓞 K) : K)
  rw [map_cyclotomicRingOfIntegersEquiv_coe]

theorem valuedIntegerCyclotomicEquiv_valuedCyclotomicLambdaInteger
    (a : CyclotomicUnitDelta p) :
    valuedIntegerCyclotomicEquiv (p := p) K a
        (valuedCyclotomicLambdaInteger p K) =
      algebraMap (𝓞 K) (ValuedIntegerRing p K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a
          ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1)) := by
  change valuedIntegerCyclotomicEquiv (p := p) K a
      (algebraMap (𝓞 K) (ValuedIntegerRing p K)
        ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1)) =
    algebraMap (𝓞 K) (ValuedIntegerRing p K)
      (cyclotomicRingOfIntegersEquiv (p := p) K a
        ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1))
  rw [valuedIntegerCyclotomicEquiv_algebraMap_ringOfIntegers]

theorem valuedIntegerCyclotomicEquiv_valuedCyclotomicLambdaInteger_eq_zeta_pow_sub_one
    (a : CyclotomicUnitDelta p) :
    valuedIntegerCyclotomicEquiv (p := p) K a
        (valuedCyclotomicLambdaInteger p K) =
      valuedCyclotomicZetaInteger p K ^ (a : ZMod p).val - 1 := by
  rw [valuedIntegerCyclotomicEquiv_valuedCyclotomicLambdaInteger]
  calc
    algebraMap (𝓞 K) (ValuedIntegerRing p K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a
          ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1))
        =
        algebraMap (𝓞 K) (ValuedIntegerRing p K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a
            (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1) := by
          rw [map_sub, map_one]
    _ =
        algebraMap (𝓞 K) (ValuedIntegerRing p K)
          (cyclotomicSigmaOfUnit (p := p) K a •
            (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1) := by
          rfl
    _ = valuedCyclotomicZetaInteger p K ^ (a : ZMod p).val - 1 := by
          rw [map_sub, map_one, cyclotomicSigmaOfUnit_smul_zetaInteger]
          simp [valuedCyclotomicZetaInteger,
            Furtwaengler.KummerArtinHasse.lambdaValuedZetaInteger, map_pow]

theorem valuedIntegerCyclotomicEquiv_valuedCyclotomicLambdaInteger_mem
    (a : CyclotomicUnitDelta p) :
      valuedIntegerCyclotomicEquiv (p := p) K a
        (valuedCyclotomicLambdaInteger p K) ∈ lambdaIdeal p K := by
  rw [valuedIntegerCyclotomicEquiv_valuedCyclotomicLambdaInteger]
  rw [← lambdaIdeal_eq_map_cyclotomicLambda (p := p) (K := K)]
  exact Ideal.mem_map_of_mem (algebraMap (𝓞 K) (ValuedIntegerRing p K))
    (cyclotomicRingOfIntegersEquiv_zeta_sub_one_mem_lambda (p := p) (K := K) a)

theorem lambdaIdeal_map_valuedIntegerCyclotomicEquiv_le
    (a : CyclotomicUnitDelta p) :
    (lambdaIdeal p K).map
        (valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K) ≤
      lambdaIdeal p K := by
  rw [lambdaIdeal, Ideal.map_span, Ideal.span_le]
  rintro x ⟨y, hy, rfl⟩
  simp only [Set.mem_singleton_iff] at hy
  subst y
  exact valuedIntegerCyclotomicEquiv_valuedCyclotomicLambdaInteger_mem
    (p := p) (K := K) a

theorem lambdaIdeal_map_valuedIntegerCyclotomicEquiv
    (a : CyclotomicUnitDelta p) :
    (lambdaIdeal p K).map
        (valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K) =
      lambdaIdeal p K := by
  apply le_antisymm
  · exact lambdaIdeal_map_valuedIntegerCyclotomicEquiv_le
      (p := p) (K := K) a
  · rw [lambdaIdeal, Ideal.span_le]
    rintro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    let e := valuedIntegerCyclotomicEquiv (p := p) K a
    let lamK : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1
    let y : ValuedIntegerRing p K :=
      algebraMap (𝓞 K) (ValuedIntegerRing p K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ lamK)
    have hy : y ∈ lambdaIdeal p K := by
      rw [← lambdaIdeal_eq_map_cyclotomicLambda (p := p) (K := K)]
      exact Ideal.mem_map_of_mem (algebraMap (𝓞 K) (ValuedIntegerRing p K))
        (cyclotomicRingOfIntegersEquiv_zeta_sub_one_mem_lambda
          (p := p) (K := K) a⁻¹)
    have hey : e y = valuedCyclotomicLambdaInteger p K := by
      change valuedIntegerCyclotomicEquiv (p := p) K a
          (algebraMap (𝓞 K) (ValuedIntegerRing p K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ lamK)) =
        valuedCyclotomicLambdaInteger p K
      rw [valuedIntegerCyclotomicEquiv_algebraMap_ringOfIntegers]
      rw [← cyclotomicRingOfIntegersEquiv_mul_apply]
      simp [lamK, valuedCyclotomicLambdaInteger,
        Furtwaengler.KummerArtinHasse.lambdaValuedPiInteger]
    have himage :
        e y ∈ (lambdaIdeal p K).map
            (e : ValuedIntegerRing p K →+* ValuedIntegerRing p K) :=
      Ideal.mem_map_of_mem
      (e : ValuedIntegerRing p K →+* ValuedIntegerRing p K) hy
    simpa [hey] using himage

theorem valuedIntegerCyclotomicEquiv_mem_lambdaIdeal_pow
    (a : CyclotomicUnitDelta p) {N : ℕ} {x : ValuedIntegerRing p K}
    (hx : x ∈ (lambdaIdeal p K) ^ N) :
    valuedIntegerCyclotomicEquiv (p := p) K a x ∈ (lambdaIdeal p K) ^ N := by
  let e := valuedIntegerCyclotomicEquiv (p := p) K a
  have hmap : ((lambdaIdeal p K) ^ N).map (e : ValuedIntegerRing p K →+*
      ValuedIntegerRing p K) = (lambdaIdeal p K) ^ N := by
    rw [Ideal.map_pow, lambdaIdeal_map_valuedIntegerCyclotomicEquiv
      (p := p) (K := K) a]
  rw [← hmap]
  exact Ideal.mem_map_of_mem (e : ValuedIntegerRing p K →+* ValuedIntegerRing p K) hx

theorem valuedIntegerCyclotomicEquiv_mem_lambdaIdeal
    (a : CyclotomicUnitDelta p) {x : ValuedIntegerRing p K}
    (hx : x ∈ lambdaIdeal p K) :
    valuedIntegerCyclotomicEquiv (p := p) K a x ∈ lambdaIdeal p K := by
  simpa [pow_one] using
    valuedIntegerCyclotomicEquiv_mem_lambdaIdeal_pow
      (p := p) (K := K) a (N := 1) (by simpa [pow_one] using hx)

theorem quotientNatCastInv_quotientMap_cyclotomic
    (a : CyclotomicUnitDelta p) (N m : ℕ) (hm : Nat.Coprime m p) :
    Ideal.quotientMap ((lambdaIdeal p K) ^ (N + 1))
        (valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (valuedIntegerCyclotomicEquiv (p := p) K a)
          (lambdaIdeal_map_valuedIntegerCyclotomicEquiv
            (p := p) (K := K) a) (N + 1))
        (quotientNatCastInv (p := p) (K := K) N m hm) =
      quotientNatCastInv (p := p) (K := K) N m hm := by
  let e : ValuedIntegerRing p K ≃+* ValuedIntegerRing p K :=
    valuedIntegerCyclotomicEquiv (p := p) K a
  let φ :
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) →+*
        ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    Ideal.quotientMap ((lambdaIdeal p K) ^ (N + 1))
      (e : ValuedIntegerRing p K →+* ValuedIntegerRing p K)
      (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K) e
        (lambdaIdeal_map_valuedIntegerCyclotomicEquiv (p := p) (K := K) a) (N + 1))
  have hspec :=
    congrArg φ (quotientNatCastInv_spec_right (p := p) (K := K) N m hm)
  symm
  refine quotientNatCastInv_eq_of_mul_right_eq_one
    (p := p) (K := K) (N := N) (m := m) hm ?_
  simpa [φ, e] using hspec

theorem samePrimeFiniteLogTermNumerator_cyclotomic {n : ℕ} (hn : n ≠ 0)
    (a : CyclotomicUnitDelta p)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    valuedIntegerCyclotomicEquiv (p := p) K a
        (samePrimeFiniteLogTermNumerator (p := p) (K := K) n x hx) =
      samePrimeFiniteLogTermNumerator (p := p) (K := K) n
        (valuedIntegerCyclotomicEquiv (p := p) K a x)
        (valuedIntegerCyclotomicEquiv_mem_lambdaIdeal (p := p) (K := K) a hx) := by
  let e : ValuedIntegerRing p K ≃+* ValuedIntegerRing p K :=
    valuedIntegerCyclotomicEquiv (p := p) K a
  let hx' : e x ∈ lambdaIdeal p K :=
    valuedIntegerCyclotomicEquiv_mem_lambdaIdeal (p := p) (K := K) a hx
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

theorem samePrimeFiniteLogTermCore_quotientMap_cyclotomic {N n : ℕ}
    (a : CyclotomicUnitDelta p)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.quotientMap ((lambdaIdeal p K) ^ (N + 1))
        (valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (valuedIntegerCyclotomicEquiv (p := p) K a)
          (lambdaIdeal_map_valuedIntegerCyclotomicEquiv
            (p := p) (K := K) a) (N + 1))
        (samePrimeFiniteLogTermCore (p := p) (K := K) N n x hx) =
      samePrimeFiniteLogTermCore (p := p) (K := K) N n
        (valuedIntegerCyclotomicEquiv (p := p) K a x)
        (valuedIntegerCyclotomicEquiv_mem_lambdaIdeal (p := p) (K := K) a hx) := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [samePrimeFiniteLogTermCore, samePrimeFiniteLogTermCore, dif_neg hn, dif_neg hn]
  rw [map_mul, quotientNatCastInv_quotientMap_cyclotomic]
  change Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (valuedIntegerCyclotomicEquiv (p := p) K a
          (samePrimeFiniteLogTermNumerator (p := p) (K := K) n x hx)) *
      quotientNatCastInv (p := p) (K := K) N (ordCompl[p] n)
        (samePrimeFiniteLog_ordCompl_coprime (p := p) hn) =
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (samePrimeFiniteLogTermNumerator (p := p) (K := K) n
          (valuedIntegerCyclotomicEquiv (p := p) K a x)
          (valuedIntegerCyclotomicEquiv_mem_lambdaIdeal (p := p) (K := K) a hx)) *
      quotientNatCastInv (p := p) (K := K) N (ordCompl[p] n)
        (samePrimeFiniteLog_ordCompl_coprime (p := p) hn)
  rw [samePrimeFiniteLogTermNumerator_cyclotomic (p := p) (K := K) hn a hx]

theorem samePrimeFiniteLogTerm_quotientMap_cyclotomic {N n : ℕ}
    (a : CyclotomicUnitDelta p)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.quotientMap ((lambdaIdeal p K) ^ (N + 1))
        (valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (valuedIntegerCyclotomicEquiv (p := p) K a)
          (lambdaIdeal_map_valuedIntegerCyclotomicEquiv
            (p := p) (K := K) a) (N + 1))
        (samePrimeFiniteLogTerm (p := p) (K := K) N n x hx) =
      samePrimeFiniteLogTerm (p := p) (K := K) N n
        (valuedIntegerCyclotomicEquiv (p := p) K a x)
        (valuedIntegerCyclotomicEquiv_mem_lambdaIdeal (p := p) (K := K) a hx) := by
  rw [samePrimeFiniteLogTerm, samePrimeFiniteLogTerm]
  rw [map_mul, map_pow]
  rw [samePrimeFiniteLogTermCore_quotientMap_cyclotomic (p := p) (K := K) a hx]
  simp

theorem samePrimeFiniteLog_quotientMap_cyclotomic {N : ℕ}
    (a : CyclotomicUnitDelta p)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.quotientMap ((lambdaIdeal p K) ^ (N + 1))
        (valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (valuedIntegerCyclotomicEquiv (p := p) K a)
          (lambdaIdeal_map_valuedIntegerCyclotomicEquiv
            (p := p) (K := K) a) (N + 1))
        (samePrimeFiniteLog (p := p) (K := K) N x hx) =
      samePrimeFiniteLog (p := p) (K := K) N
        (valuedIntegerCyclotomicEquiv (p := p) K a x)
        (valuedIntegerCyclotomicEquiv_mem_lambdaIdeal (p := p) (K := K) a hx) := by
  classical
  unfold samePrimeFiniteLog
  rw [map_sum]
  exact Finset.sum_congr rfl fun n _hn =>
    samePrimeFiniteLogTerm_quotientMap_cyclotomic (p := p) (K := K) a hx

section FinsetProducts

variable {ι : Type*}

/-- Principal-unit product coordinate for a finite family:
`1 + coord = ∏ i, (1 + x i)`. -/
def samePrimeFiniteLogFinsetProductCoord
    (s : Finset ι) (x : ι → ValuedIntegerRing p K) :
    ValuedIntegerRing p K :=
  (∏ i ∈ s, (1 + x i)) - 1

@[simp]
theorem samePrimeFiniteLogFinsetProductCoord_empty
    (x : ι → ValuedIntegerRing p K) :
    samePrimeFiniteLogFinsetProductCoord (p := p) (K := K)
        (∅ : Finset ι) x = 0 := by
  simp [samePrimeFiniteLogFinsetProductCoord]

theorem samePrimeFiniteLogProductCoord_finsetProductCoord_insert
    [DecidableEq ι]
    {s : Finset ι} {a : ι} (ha : a ∉ s)
    (x : ι → ValuedIntegerRing p K) :
    samePrimeFiniteLogProductCoord (p := p) (K := K)
        (samePrimeFiniteLogFinsetProductCoord (p := p) (K := K) s x) (x a) =
      samePrimeFiniteLogFinsetProductCoord (p := p) (K := K) (insert a s) x := by
  classical
  simp [samePrimeFiniteLogProductCoord, samePrimeFiniteLogFinsetProductCoord,
    Finset.prod_insert, ha]
  ring

theorem samePrimeFiniteLogFinsetProductCoord_mem_lambdaIdeal
    {s : Finset ι} {x : ι → ValuedIntegerRing p K}
    (hx : ∀ i ∈ s, x i ∈ lambdaIdeal p K) :
    samePrimeFiniteLogFinsetProductCoord (p := p) (K := K) s x ∈
      lambdaIdeal p K := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      have hs : samePrimeFiniteLogFinsetProductCoord (p := p) (K := K) s x ∈
          lambdaIdeal p K := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
      have haI : x a ∈ lambdaIdeal p K := hx a (Finset.mem_insert_self a s)
      have hprod :
          samePrimeFiniteLogProductCoord (p := p) (K := K)
              (samePrimeFiniteLogFinsetProductCoord (p := p) (K := K) s x) (x a) ∈
            lambdaIdeal p K :=
        samePrimeFiniteLogProductCoord_mem_lambdaIdeal (p := p) (K := K) hs haI
      simpa [samePrimeFiniteLogProductCoord_finsetProductCoord_insert
        (p := p) (K := K) ha x] using hprod

theorem samePrimeFiniteLog_finsetProductCoord
    (N : ℕ) {s : Finset ι} {x : ι → ValuedIntegerRing p K}
    (hx : ∀ i ∈ s, x i ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteLogFinsetProductCoord (p := p) (K := K) s x)
        (samePrimeFiniteLogFinsetProductCoord_mem_lambdaIdeal
          (p := p) (K := K) hx) =
      ∑ i ∈ s.attach,
        samePrimeFiniteLog (p := p) (K := K) N (x i.1) (hx i.1 i.2) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [samePrimeFiniteLog_arg_zero]
  | insert a s ha ih =>
      have hs : ∀ i ∈ s, x i ∈ lambdaIdeal p K :=
        fun i hi => hx i (Finset.mem_insert_of_mem hi)
      have hcoord_mem :
          samePrimeFiniteLogFinsetProductCoord (p := p) (K := K) s x ∈
            lambdaIdeal p K :=
        samePrimeFiniteLogFinsetProductCoord_mem_lambdaIdeal (p := p) (K := K) hs
      have ha_mem : x a ∈ lambdaIdeal p K :=
        hx a (Finset.mem_insert_self a s)
      have hprod_mem :
          samePrimeFiniteLogProductCoord (p := p) (K := K)
              (samePrimeFiniteLogFinsetProductCoord (p := p) (K := K) s x) (x a) ∈
            lambdaIdeal p K :=
        samePrimeFiniteLogProductCoord_mem_lambdaIdeal
          (p := p) (K := K) hcoord_mem ha_mem
      calc
        samePrimeFiniteLog (p := p) (K := K) N
            (samePrimeFiniteLogFinsetProductCoord (p := p) (K := K) (insert a s) x)
            (samePrimeFiniteLogFinsetProductCoord_mem_lambdaIdeal
              (p := p) (K := K) hx)
            =
          samePrimeFiniteLog (p := p) (K := K) N
            (samePrimeFiniteLogProductCoord (p := p) (K := K)
              (samePrimeFiniteLogFinsetProductCoord (p := p) (K := K) s x) (x a))
            hprod_mem :=
              samePrimeFiniteLog_eq_of_eq (p := p) (K := K)
                (N := N)
                (samePrimeFiniteLogProductCoord_finsetProductCoord_insert
                  (p := p) (K := K) ha x).symm
                (samePrimeFiniteLogFinsetProductCoord_mem_lambdaIdeal
                  (p := p) (K := K) hx)
                hprod_mem
        _ =
          samePrimeFiniteLog (p := p) (K := K) N
              (samePrimeFiniteLogFinsetProductCoord (p := p) (K := K) s x) hcoord_mem +
            samePrimeFiniteLog (p := p) (K := K) N (x a) ha_mem :=
              samePrimeFiniteLog_add_add_mul
                (p := p) (K := K) N hcoord_mem ha_mem
        _ =
          (∑ i ∈ s.attach,
              samePrimeFiniteLog (p := p) (K := K) N (x i.1) (hs i.1 i.2)) +
            samePrimeFiniteLog (p := p) (K := K) N (x a) ha_mem := by
              rw [ih hs]
        _ = ∑ i ∈ (insert a s).attach,
              samePrimeFiniteLog (p := p) (K := K) N (x i.1) (hx i.1 i.2) := by
              symm
              rw [Finset.attach_insert, Finset.sum_insert]
              · rw [Finset.sum_image]
                · simp [add_comm]
                · intro b _hb c _hc hbc
                  have hval : b.1 = c.1 :=
                    congrArg (fun z : {i // i ∈ insert a s} => z.1) hbc
                  exact Subtype.ext hval
              · simp [ha]

end FinsetProducts

/-- The full cyclotomic automorphism lifted to the `lambda`-adic Dwork
completion. -/
noncomputable def dworkCompleteCyclotomicEquiv
    (a : CyclotomicUnitDelta p) :
    DworkCompleteIntegerRing p K ≃+* DworkCompleteIntegerRing p K :=
  adicCompletionRingEquivOfIdealMapEq (I := lambdaIdeal p K)
    (valuedIntegerCyclotomicEquiv (p := p) K a)
    (lambdaIdeal_map_valuedIntegerCyclotomicEquiv (p := p) (K := K) a)

@[simp]
theorem evalₐ_dworkCompleteCyclotomicEquiv
    (a : CyclotomicUnitDelta p) (N : ℕ) (x : DworkCompleteIntegerRing p K) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N
        (dworkCompleteCyclotomicEquiv (p := p) K a x) =
      Ideal.quotientMap ((lambdaIdeal p K) ^ N)
        (valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (valuedIntegerCyclotomicEquiv (p := p) K a)
          (lambdaIdeal_map_valuedIntegerCyclotomicEquiv
            (p := p) (K := K) a) N)
        (AdicCompletion.evalₐ (lambdaIdeal p K) N x) :=
  evalₐ_adicCompletionRingEquivOfIdealMapEq (I := lambdaIdeal p K)
    (valuedIntegerCyclotomicEquiv (p := p) K a)
    (lambdaIdeal_map_valuedIntegerCyclotomicEquiv (p := p) (K := K) a) N x

/-- The image of the completed lambda coordinate under the cyclotomic action. -/
@[simp]
theorem dworkCompleteCyclotomicEquiv_dworkCompleteLambda
    (a : CyclotomicUnitDelta p) :
    dworkCompleteCyclotomicEquiv (p := p) K a (dworkCompleteLambda p K) =
      AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
        (valuedCyclotomicZetaInteger p K ^ (a : ZMod p).val - 1) := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [evalₐ_dworkCompleteCyclotomicEquiv]
  simp [dworkCompleteLambda,
    valuedIntegerCyclotomicEquiv_valuedCyclotomicLambdaInteger_eq_zeta_pow_sub_one]

@[simp]
theorem valuedIntegerCyclotomicEquiv_rIntegralRatToValuedInteger
    (a : CyclotomicUnitDelta p)
    (q : Furtwaengler.DieudonneDwork.rIntegralRatSubring p) :
    valuedIntegerCyclotomicEquiv (p := p) K a
        (rIntegralRatToValuedInteger p K q) =
      rIntegralRatToValuedInteger p K q := by
  ext
  change valuedCompletionCyclotomicEquiv (p := p) K a
      (algebraMap K (ValuedCompletion p K) (algebraMap ℚ K (q : ℚ))) =
    algebraMap K (ValuedCompletion p K) (algebraMap ℚ K (q : ℚ))
  rw [valuedCompletionCyclotomicEquiv_algebraMap]
  simp

@[simp]
theorem integralInverseSeries_map_valuedIntegerCyclotomicEquiv
    (a : CyclotomicUnitDelta p) :
    PowerSeries.map
        (valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (integralInverseSeries p K) =
      integralInverseSeries p K := by
  ext n
  simp [integralInverseSeries, Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]

theorem quotientMap_evalIntegralPowerSeriesMod_cyclotomic
    (a : CyclotomicUnitDelta p)
    (F : PowerSeries (ValuedIntegerRing p K))
    (hF : PowerSeries.map
      (valuedIntegerCyclotomicEquiv (p := p) K a :
        ValuedIntegerRing p K →+* ValuedIntegerRing p K) F = F)
    (x : DworkCompleteIntegerRing p K) (N : ℕ) :
    Ideal.quotientMap ((lambdaIdeal p K) ^ N)
        (valuedIntegerCyclotomicEquiv (p := p) K a :
          ValuedIntegerRing p K →+* ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (valuedIntegerCyclotomicEquiv (p := p) K a)
          (lambdaIdeal_map_valuedIntegerCyclotomicEquiv (p := p) (K := K) a) N)
        (evalIntegralPowerSeriesMod p K F x N) =
      evalIntegralPowerSeriesMod p K F
        (dworkCompleteCyclotomicEquiv (p := p) K a x) N := by
  classical
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let A : Type _ := R ⧸ I ^ N
  let q : R →+* A := Ideal.Quotient.mk (I ^ N)
  let e : R ≃+* R := valuedIntegerCyclotomicEquiv (p := p) K a
  let he : I.map (e : R →+* R) = I :=
    lambdaIdeal_map_valuedIntegerCyclotomicEquiv (p := p) (K := K) a
  let φ : A →+* A :=
    Ideal.quotientMap (I ^ N) (e : R →+* R)
      (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he N)
  let P : Polynomial A := PowerSeries.trunc N (PowerSeries.map q F)
  have hφq : φ.comp q = q.comp (e : R →+* R) := by
    ext r
    rfl
  have hPSmap :
      PowerSeries.map φ (PowerSeries.map q F) = PowerSeries.map q F := by
    ext n
    have hn : e (PowerSeries.coeff n F) = PowerSeries.coeff n F := by
      have h := congrArg (fun G : PowerSeries R => PowerSeries.coeff n G) hF
      simpa [PowerSeries.coeff_map] using h
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    change φ (q (PowerSeries.coeff n F)) = q (PowerSeries.coeff n F)
    change (φ.comp q) (PowerSeries.coeff n F) = q (PowerSeries.coeff n F)
    rw [hφq]
    simp [hn]
  have hPmap : P.map φ = P := by
    change (PowerSeries.trunc N (PowerSeries.map q F)).map φ =
      PowerSeries.trunc N (PowerSeries.map q F)
    rw [← PowerSeries.trunc_map, hPSmap]
  rw [evalIntegralPowerSeriesMod, evalIntegralPowerSeriesMod]
  change φ (P.eval₂ (RingHom.id A) (AdicCompletion.evalₐ I N x)) =
    P.eval₂ (RingHom.id A)
      (AdicCompletion.evalₐ I N (dworkCompleteCyclotomicEquiv (p := p) K a x))
  rw [evalₐ_dworkCompleteCyclotomicEquiv]
  change φ (P.eval₂ (RingHom.id A) (AdicCompletion.evalₐ I N x)) =
    P.eval₂ (RingHom.id A) (φ (AdicCompletion.evalₐ I N x))
  calc
    φ (P.eval₂ (RingHom.id A) (AdicCompletion.evalₐ I N x)) =
        P.eval₂ φ (φ (AdicCompletion.evalₐ I N x)) :=
          Polynomial.hom_eval₂ P (RingHom.id A) φ (AdicCompletion.evalₐ I N x)
    _ = P.eval₂ (RingHom.id A) (φ (AdicCompletion.evalₐ I N x)) := by
          rw [← Polynomial.eval_map, hPmap]
          rfl

theorem dworkCompleteCyclotomicEquiv_evalIntegralPowerSeries_inverse
    (a : CyclotomicUnitDelta p)
    (x : DworkCompleteIntegerRing p K)
    (hx : AdicCompletion.evalₐ (lambdaIdeal p K) 1 x = 0) :
    dworkCompleteCyclotomicEquiv (p := p) K a
        (evalIntegralPowerSeries p K (integralInverseSeries p K) x hx) =
      evalIntegralPowerSeries p K (integralInverseSeries p K)
        (dworkCompleteCyclotomicEquiv (p := p) K a x)
        (by
          rw [evalₐ_dworkCompleteCyclotomicEquiv, hx, map_zero]) := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [evalₐ_dworkCompleteCyclotomicEquiv, evalIntegralPowerSeries_evalₐ,
    evalIntegralPowerSeries_evalₐ]
  exact quotientMap_evalIntegralPowerSeriesMod_cyclotomic (p := p) (K := K) a
    (integralInverseSeries p K)
    (integralInverseSeries_map_valuedIntegerCyclotomicEquiv (p := p) (K := K) a)
    x N

theorem dworkCompleteCyclotomicEquiv_dworkParameter_as_inverse
    (a : CyclotomicUnitDelta p) :
    dworkCompleteCyclotomicEquiv (p := p) K a (dworkParameter p K) =
      evalIntegralPowerSeries p K (integralInverseSeries p K)
        (AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
          (valuedCyclotomicZetaInteger p K ^ (a : ZMod p).val - 1))
        (by
          rw [AdicCompletion.evalₐ_of]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr
            (by
              simpa [pow_one] using
                zetaPowSubOne_mem_lambdaIdeal (p := p) (K := K) (a : ZMod p))) := by
  rw [dworkParameter_eq_evalIntegralPowerSeries_lambda (p := p) (K := K)]
  rw [dworkCompleteCyclotomicEquiv_evalIntegralPowerSeries_inverse]
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [evalIntegralPowerSeries_evalₐ, evalIntegralPowerSeries_evalₐ,
    dworkCompleteCyclotomicEquiv_dworkCompleteLambda]

theorem evalIntegralPowerSeriesMod_expMinusOne_eq_exp_sub_one
    (x : DworkCompleteIntegerRing p K) (N : ℕ) :
    evalIntegralPowerSeriesMod p K (integralExpMinusOneSeries p K) x N =
      evalIntegralPowerSeriesMod p K (integralExpSeries p K) x N - 1 := by
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let A : Type _ := R ⧸ I ^ N
  let q : R →+* A := Ideal.Quotient.mk (I ^ N)
  let xN : A := AdicCompletion.evalₐ I N x
  change
    (PowerSeries.trunc N (PowerSeries.map q (integralExpMinusOneSeries p K))).eval₂
        (RingHom.id A) xN =
      (PowerSeries.trunc N (PowerSeries.map q (integralExpSeries p K))).eval₂
        (RingHom.id A) xN - 1
  rw [integralExpMinusOneSeries_eq]
  rw [map_sub]
  change
    (PowerSeries.trunc N
        (PowerSeries.map q (integralExpSeries p K) - PowerSeries.map q 1)).eval₂
        (RingHom.id A) xN =
      (PowerSeries.trunc N (PowerSeries.map q (integralExpSeries p K))).eval₂
        (RingHom.id A) xN - 1
  rw [LinearMap.map_sub]
  simp only [map_one, Polynomial.eval₂_sub, Polynomial.eval₂_id, sub_right_inj]
  cases N with
  | zero =>
      simpa using (quotient_pow_zero_eq_zero (p := p) (K := K) I
        (1 : ValuedIntegerRing p K ⧸ I ^ 0)).symm
  | succ N =>
      simp

theorem evalIntegralPowerSeries_expMinusOne_scaledDworkParameter_eq_zetaPowSubOne
    (a : ZMod p) :
    evalIntegralPowerSeries p K (integralExpMinusOneSeries p K)
        (scaledDworkParameter p K a)
        (scaledDworkParameter_evalₐ_one (p := p) (K := K) a) =
      AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
        (valuedCyclotomicZetaInteger p K ^ a.val - 1) := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [evalIntegralPowerSeries_evalₐ,
    evalIntegralPowerSeriesMod_expMinusOne_eq_exp_sub_one]
  rw [← artinHasseExp_eval_scaledDworkParameter_evalₐ]
  rw [artinHasseExp_eval_scaledDworkParameter_eq_zeta_pow]
  rw [AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of]
  simp [map_sub]

set_option maxHeartbeats 800000 in
-- The proof compares inverse formal series quotient-by-quotient through
-- truncated substitutions, which pushes simplification and instance search past
-- the default heartbeat budget.
theorem evalIntegralPowerSeries_inverse_zetaPowSubOne_eq_scaledDworkParameter
    (a : ZMod p) :
    evalIntegralPowerSeries p K (integralInverseSeries p K)
        (AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
          (valuedCyclotomicZetaInteger p K ^ a.val - 1))
        (by
          rw [AdicCompletion.evalₐ_of]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr
            (by
              simpa [pow_one] using
                zetaPowSubOne_mem_lambdaIdeal (p := p) (K := K) a)) =
      scaledDworkParameter p K a := by
  classical
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let y : DworkCompleteIntegerRing p K :=
    AdicCompletion.of I R (valuedCyclotomicZetaInteger p K ^ a.val - 1)
  have hy_one : AdicCompletion.evalₐ I 1 y = 0 := by
    dsimp [y, I]
    rw [AdicCompletion.evalₐ_of]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (by
        simpa [pow_one] using
          zetaPowSubOne_mem_lambdaIdeal (p := p) (K := K) a)
  apply AdicCompletion.ext_evalₐ
  intro N
  cases N with
  | zero =>
      trans 0
      · exact quotient_pow_zero_eq_zero (p := p) (K := K) I
          (AdicCompletion.evalₐ I 0
            (evalIntegralPowerSeries p K (integralInverseSeries p K) y hy_one))
      · symm
        exact quotient_pow_zero_eq_zero (p := p) (K := K) I
          (AdicCompletion.evalₐ I 0 (scaledDworkParameter p K a))
  | succ M =>
      let A : Type _ := R ⧸ I ^ (M + 1)
      let q : R →+* A := Ideal.Quotient.mk (I ^ (M + 1))
      let G : PowerSeries A := PowerSeries.map q (integralInverseSeries p K)
      let H : PowerSeries A := PowerSeries.map q (integralExpMinusOneSeries p K)
      let xbar : A := AdicCompletion.evalₐ I (M + 1) (scaledDworkParameter p K a)
      let ybar : A := AdicCompletion.evalₐ I (M + 1) y
      have hxNil : xbar ^ (M + 1) = 0 :=
        evalₐ_pow_eq_zero_of_evalₐ_one_eq_zero
          (p := p) (K := K)
          (scaledDworkParameter_evalₐ_one (p := p) (K := K) a) (M + 1)
      have hyEval :
          (PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A) xbar = ybar := by
        have h := congrArg (AdicCompletion.evalₐ I (M + 1))
          (evalIntegralPowerSeries_expMinusOne_scaledDworkParameter_eq_zetaPowSubOne
            (p := p) (K := K) a)
        rw [evalIntegralPowerSeries_evalₐ] at h
        change evalIntegralPowerSeriesMod p K (integralExpMinusOneSeries p K)
            (scaledDworkParameter p K a) (M + 1) =
          AdicCompletion.evalₐ I (M + 1) y at h
        simpa [evalIntegralPowerSeriesMod, H, xbar, ybar, q, A, I, R] using h
      have hyNil : ybar ^ (M + 1) = 0 := by
        dsimp [ybar]
        exact evalₐ_pow_eq_zero_of_evalₐ_one_eq_zero
          (p := p) (K := K) hy_one (M + 1)
      have hG0 : PowerSeries.constantCoeff G = 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        rw [PowerSeries.coeff_map]
        have hcoeff :
            (PowerSeries.coeff (R := R) 0) (integralInverseSeries p K) = 0 := by
          rw [integralInverseSeries]
          rw [Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]
          have hcoeff0 :
              (PowerSeries.coeff (R := ℚ) 0) (FormalDwork.inverseSeries p) = 0 := by
            rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
            exact FormalDwork.inverseSeries_constantCoeff p
          have hsubzero :
              (⟨(PowerSeries.coeff (R := ℚ) 0) (FormalDwork.inverseSeries p),
                  FormalDwork.inverseSeries_isPIntegral p 0⟩ :
                Furtwaengler.DieudonneDwork.rIntegralRatSubring p) = 0 := by
            ext
            exact hcoeff0
          rw [hsubzero]
          exact map_zero (rIntegralRatToValuedInteger p K)
        rw [hcoeff]
        exact map_zero q
      have hH0 : PowerSeries.constantCoeff H = 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        rw [PowerSeries.coeff_map]
        have hcoeff :
            (PowerSeries.coeff (R := R) 0) (integralExpMinusOneSeries p K) = 0 := by
          rw [integralExpMinusOneSeries]
          rw [Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]
          have hcoeff0 :
              (PowerSeries.coeff (R := ℚ) 0) (FormalDwork.expMinusOneSeries p) = 0 := by
            rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
            exact FormalDwork.expMinusOneSeries_constantCoeff p
          have hsubzero :
              (⟨(PowerSeries.coeff (R := ℚ) 0) (FormalDwork.expMinusOneSeries p),
                  FormalDwork.expMinusOneSeries_isPIntegral p 0⟩ :
                Furtwaengler.DieudonneDwork.rIntegralRatSubring p) = 0 := by
            ext
            exact hcoeff0
          rw [hsubzero]
          exact map_zero (rIntegralRatToValuedInteger p K)
        rw [hcoeff]
        exact map_zero q
      have hseries : PowerSeries.subst H G = (PowerSeries.X : PowerSeries A) := by
        have h := congrArg (PowerSeries.map q)
          (integralInverseSeries_subst_integralExpMinusOneSeries (p := p) (K := K))
        have hH0R : PowerSeries.constantCoeff (integralExpMinusOneSeries p K) = 0 := by
          rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
          exact
            show (PowerSeries.coeff (R := R) 0) (integralExpMinusOneSeries p K) = 0 from by
              rw [integralExpMinusOneSeries]
              rw [Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]
              have hcoeff0 :
                  (PowerSeries.coeff (R := ℚ) 0) (FormalDwork.expMinusOneSeries p) = 0 := by
                rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
                exact FormalDwork.expMinusOneSeries_constantCoeff p
              have hsubzero :
                  (⟨(PowerSeries.coeff (R := ℚ) 0) (FormalDwork.expMinusOneSeries p),
                      FormalDwork.expMinusOneSeries_isPIntegral p 0⟩ :
                    Furtwaengler.DieudonneDwork.rIntegralRatSubring p) = 0 := by
                ext
                exact hcoeff0
              rw [hsubzero]
              exact map_zero (rIntegralRatToValuedInteger p K)
        have hsubst :
            PowerSeries.HasSubst (integralExpMinusOneSeries p K) :=
          PowerSeries.HasSubst.of_constantCoeff_zero' hH0R
        have hmap_subst :
            PowerSeries.map q
                (PowerSeries.subst (integralExpMinusOneSeries p K)
                  (integralInverseSeries p K)) =
              PowerSeries.subst H G :=
          PowerSeries.map_subst (h := q) hsubst (integralInverseSeries p K)
        rw [hmap_subst] at h
        simpa [G, H] using h
      have hEvalNil :
          ((PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A) xbar) ^ (M + 1) = 0 := by
        rw [hyEval]
        exact hyNil
      have hcomp :
          (PowerSeries.trunc (M + 1) (PowerSeries.subst H G)).eval₂
              (RingHom.id A) xbar =
            (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) ybar := by
        have hsubst := powerSeries_trunc_eval₂_subst_of_pow_succ_eq_zero
          (a := xbar) (N := M) hxNil
          (G := H) hH0 hEvalNil G
        calc
          (PowerSeries.trunc (M + 1) (PowerSeries.subst H G)).eval₂
              (RingHom.id A) xbar =
            (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A)
              ((PowerSeries.trunc (M + 1) H).eval₂ (RingHom.id A) xbar) := hsubst
          _ = (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) ybar := by
            rw [hyEval]
      have hXeval :
          (PowerSeries.trunc (M + 1) (PowerSeries.X : PowerSeries A)).eval₂
              (RingHom.id A) xbar = xbar := by
        cases M with
        | zero =>
            have hxbar_zero : xbar = 0 := by
              dsimp [xbar, A, I]
              exact scaledDworkParameter_evalₐ_one (p := p) (K := K) a
            rw [hxbar_zero]
            simp
        | succ M =>
            rw [PowerSeries.trunc_X M]
            simp
      calc
        AdicCompletion.evalₐ I (M + 1)
            (evalIntegralPowerSeries p K (integralInverseSeries p K) y hy_one)
            =
          (PowerSeries.trunc (M + 1) G).eval₂ (RingHom.id A) ybar := by
            rw [evalIntegralPowerSeries_evalₐ]
            rfl
        _ =
          (PowerSeries.trunc (M + 1) (PowerSeries.subst H G)).eval₂
              (RingHom.id A) xbar := hcomp.symm
        _ =
          (PowerSeries.trunc (M + 1) (PowerSeries.X : PowerSeries A)).eval₂
              (RingHom.id A) xbar := by rw [hseries]
        _ = xbar := hXeval
        _ = AdicCompletion.evalₐ I (M + 1) (scaledDworkParameter p K a) := rfl

theorem dworkCompleteCyclotomicEquiv_dworkParameter
    (a : CyclotomicUnitDelta p) :
    dworkCompleteCyclotomicEquiv (p := p) K a (dworkParameter p K) =
      scaledDworkParameter p K (a : ZMod p) := by
  rw [dworkCompleteCyclotomicEquiv_dworkParameter_as_inverse]
  exact evalIntegralPowerSeries_inverse_zetaPowSubOne_eq_scaledDworkParameter
    (p := p) (K := K) (a : ZMod p)

@[simp]
theorem valuedIntegerCyclotomicEquiv_rationalPadicIntegerToValuedInteger
    (a : CyclotomicUnitDelta p) (x : RationalPadicIntegerRing p) :
    valuedIntegerCyclotomicEquiv (p := p) K a
        (rationalPadicIntegerToValuedInteger (p := p) (K := K) x) =
      rationalPadicIntegerToValuedInteger (p := p) (K := K) x := by
  ext
  change valuedCompletionCyclotomicEquiv (p := p) K a
      (rationalToLambdaCompletionRingHom (p := p) (K := K)
        (x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)) =
    rationalToLambdaCompletionRingHom (p := p) (K := K)
      (x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
  exact valuedCompletionCyclotomicEquiv_rationalToLambdaCompletionRingHom
    (p := p) (K := K) a x

@[simp]
theorem dworkCompleteCyclotomicEquiv_algebraMap_rationalPadicInteger
    (a : CyclotomicUnitDelta p) (x : RationalPadicIntegerRing p) :
    dworkCompleteCyclotomicEquiv (p := p) K a
        (algebraMap (RationalPadicIntegerRing p)
          (DworkCompleteIntegerRing p K) x) =
      algebraMap (RationalPadicIntegerRing p)
        (DworkCompleteIntegerRing p K) x := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [evalₐ_dworkCompleteCyclotomicEquiv]
  simp [algebraMap_rationalPadicInteger_dworkComplete_apply]

/-- The full cyclotomic action scales the `i`-th Dwork-parameter power by the
Teichmuller lift of the acting unit to the `i`-th power. -/
theorem dworkCompleteCyclotomicEquiv_dworkParameter_pow
    (a : CyclotomicUnitDelta p) (i : Fin (p - 1)) :
    dworkCompleteCyclotomicEquiv (p := p) K a
        (dworkParameter p K ^ (i : ℕ)) =
      algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K)
          (rationalPadicTeichmuller p (a : ZMod p) ^ (i : ℕ)) *
        dworkParameter p K ^ (i : ℕ) := by
  rw [map_pow, dworkCompleteCyclotomicEquiv_dworkParameter]
  simp [scaledDworkParameter, map_pow, mul_pow]

/-- Coefficient action on the finite Dwork power expansion. -/
theorem dworkCompleteCyclotomicEquiv_powerLinearMap
    (a : CyclotomicUnitDelta p)
    (c : Fin (p - 1) → RationalPadicIntegerRing p) :
    dworkCompleteCyclotomicEquiv (p := p) K a
        (dworkParameterPowerLinearMap p K c) =
      dworkParameterPowerLinearMap p K
        (fun i => rationalPadicTeichmuller p (a : ZMod p) ^ (i : ℕ) * c i) := by
  classical
  rw [dworkParameterPowerLinearMap_apply, dworkParameterPowerLinearMap_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [map_mul, dworkCompleteCyclotomicEquiv_algebraMap_rationalPadicInteger,
    dworkCompleteCyclotomicEquiv_dworkParameter_pow]
  simp [map_mul, map_pow]
  ring

end Conjugation

end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end
