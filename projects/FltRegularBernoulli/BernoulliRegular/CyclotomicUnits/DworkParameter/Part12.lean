module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Part11
public import BernoulliRegular.Reflection.Local.Graded
public import Mathlib.LinearAlgebra.StdBasis

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

open Furtwaengler.KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance : CharZero (ValuedCompletion p K) :=
  algebraRat.charZero (ValuedCompletion p K)

theorem rationalToLambdaWithValRingHom_le_one_iff
    (x : WithVal ((lambdaRationalHeightOneSpectrum p).valuation ℚ)) :
    Valued.v (rationalToLambdaWithValRingHom (p := p) (K := K) x) ≤ 1 ↔
      Valued.v x ≤ 1 := by
  let vQ := (lambdaRationalHeightOneSpectrum p).valuation ℚ
  let vK := (lambdaHeightOneSpectrum p K).valuation K
  change vK (algebraMap ℚ K ((WithVal.equiv vQ) x)) ≤ 1 ↔ vQ ((WithVal.equiv vQ) x) ≤ 1
  rw [← Valuation.comap_apply]
  exact (lambdaValuation_comap_rat_isEquiv (p := p) (K := K)).le_one_iff_le_one.symm

theorem rationalToLambdaCompletionRingHom_le_one_iff
    (x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) :
    Valued.v (rationalToLambdaCompletionRingHom (p := p) (K := K) x) ≤ 1 ↔
      Valued.v x ≤ 1 := by
  classical
  let f : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ →
      LambdaValuedCompletion p K :=
    rationalToLambdaCompletionRingHom (p := p) (K := K)
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      let A : Set ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) :=
        {x | Valued.v x ≤ 1}
      let B : Set ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) :=
        {x | Valued.v (f x) ≤ 1}
      have hA' :
          IsClopen {x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ |
            Valued.v.restrict x ≤ 1} :=
        Valued.isClopen_closedBall
          (R := (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
          (r := 1) one_ne_zero
      have hA : IsClopen A := by
        convert hA' using 1
        ext x
        simp [A, Valuation.restrict_le_one_iff]
      have hB' :
          IsClopen {x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ |
            Valued.v.restrict (f x) ≤ 1} :=
        (Valued.isClopen_closedBall
          (R := LambdaValuedCompletion p K) (r := 1)
          one_ne_zero).preimage
          (continuous_algebraMap_rationalCompletionToLambdaAlgebra (p := p) (K := K))
      have hB : IsClopen B := by
        convert hB' using 1
        ext x
        simp [B, Valuation.restrict_le_one_iff]
      have hset :
          {x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ |
              Valued.v (f x) ≤ 1 ↔ Valued.v x ≤ 1} =
            (B ∩ A) ∪ (Bᶜ ∩ Aᶜ) := by
        ext x
        simp [A, B, iff_iff_and_or_not_and_not, and_comm]
      rw [hset]
      exact (hB.inter hA).1.union ((hB.compl.inter hA.compl).1)
  | ih x =>
      rw [rationalToLambdaCompletionRingHom_coe]
      simpa [Valued.valuedCompletion_apply] using
        rationalToLambdaWithValRingHom_le_one_iff (p := p) (K := K) x

/-- The rational `p`-adic integer ring, expressed as the integer subring of the
rational adic completion.  This is canonically equivalent to `ℤ_[p]`, but it
avoids bundled-prime transport noise in the Dwork-local algebra API. -/
abbrev RationalPadicIntegerRing : Type :=
  (lambdaRationalHeightOneSpectrum p).adicCompletionIntegers ℚ

theorem rationalToLambdaCompletionRingHom_mem_integers
    (x : RationalPadicIntegerRing p) :
    rationalToLambdaCompletionRingHom (p := p) (K := K)
        (x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) ∈
      (lambdaHeightOneSpectrum p K).adicCompletionIntegers K := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  apply (rationalToLambdaCompletionRingHom_le_one_iff (p := p) (K := K)
    (x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)).mpr
  rw [← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  exact x.property

/-- Integral rational-completion coefficients as elements of the lambda-valued
integer ring. -/
def rationalPadicIntegerToValuedInteger :
    RationalPadicIntegerRing p →+* ValuedIntegerRing p K where
  toFun x :=
    ⟨rationalToLambdaCompletionRingHom (p := p) (K := K)
        (x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ),
      rationalToLambdaCompletionRingHom_mem_integers (p := p) (K := K) x⟩
  map_zero' := by
    ext
    exact map_zero (rationalToLambdaCompletionRingHom (p := p) (K := K))
  map_one' := by
    ext
    exact map_one (rationalToLambdaCompletionRingHom (p := p) (K := K))
  map_add' x y := by
    ext
    exact map_add (rationalToLambdaCompletionRingHom (p := p) (K := K))
      (x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) y
  map_mul' x y := by
    ext
    exact map_mul (rationalToLambdaCompletionRingHom (p := p) (K := K))
      (x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) y

instance instAlgebraRationalPadicIntegerValuedInteger :
    Algebra (RationalPadicIntegerRing p) (ValuedIntegerRing p K) :=
  (rationalPadicIntegerToValuedInteger (p := p) (K := K)).toAlgebra

instance instAlgebraRationalPadicIntegerDworkComplete :
    Algebra (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K) :=
  ((algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)).comp
    (rationalPadicIntegerToValuedInteger (p := p) (K := K))).toAlgebra

/-- The formal `Z_p[varpi]` object for CU-09e2, using the rational-completion
integer model of `Z_p`. -/
abbrev dworkParameterAdjoin :
    Subalgebra (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K) :=
  Algebra.adjoin (RationalPadicIntegerRing p)
    ({dworkParameter p K} : Set (DworkCompleteIntegerRing p K))

@[simp]
theorem algebraMap_rationalPadicInteger_dworkComplete_apply
    (x : RationalPadicIntegerRing p) :
    algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K) x =
      algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)
        (rationalPadicIntegerToValuedInteger (p := p) (K := K) x) :=
  rfl

theorem dworkParameter_mem_adjoin :
    dworkParameter p K ∈ dworkParameterAdjoin p K :=
  Algebra.subset_adjoin (Set.mem_singleton (dworkParameter p K))

theorem dworkParameter_pow_mem_adjoin (n : ℕ) :
    dworkParameter p K ^ n ∈ dworkParameterAdjoin p K :=
  (dworkParameterAdjoin p K).pow_mem
    (dworkParameter_mem_adjoin (p := p) (K := K)) n

theorem algebraMap_mem_dworkParameterAdjoin
    (x : RationalPadicIntegerRing p) :
    algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K) x ∈
      dworkParameterAdjoin p K :=
  (dworkParameterAdjoin p K).algebraMap_mem x

/-- The finite power expansion map for the candidate `Z_p`-basis
`1, varpi, ..., varpi^(p - 2)`. -/
def dworkParameterPowerLinearMap :
    (Fin (p - 1) → RationalPadicIntegerRing p) →ₗ[RationalPadicIntegerRing p]
      DworkCompleteIntegerRing p K where
  toFun a :=
    ∑ i : Fin (p - 1),
      algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K) (a i) *
        dworkParameter p K ^ (i : ℕ)
  map_add' a b := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    change
      ∑ x : Fin (p - 1),
        algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K) c *
            algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K) (a x) *
          dworkParameter p K ^ (x : ℕ) =
        algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K) c *
          ∑ i : Fin (p - 1),
            algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K) (a i) *
              dworkParameter p K ^ (i : ℕ)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    simp [mul_assoc]

theorem dworkParameterPowerLinearMap_apply
    (a : Fin (p - 1) → RationalPadicIntegerRing p) :
    dworkParameterPowerLinearMap p K a =
      ∑ i : Fin (p - 1),
        algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K) (a i) *
          dworkParameter p K ^ (i : ℕ) :=
  rfl

@[simp]
theorem dworkParameterPowerLinearMap_single (i : Fin (p - 1)) :
    dworkParameterPowerLinearMap p K
        (Pi.single i (1 : RationalPadicIntegerRing p)) =
      dworkParameter p K ^ (i : ℕ) := by
  classical
  rw [dworkParameterPowerLinearMap_apply, Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [Pi.single_eq_of_ne hji]
  · intro hi
    simp at hi

@[simp]
theorem dworkParameterPowerLinearMap_single_coeff
    (i : Fin (p - 1)) (c : RationalPadicIntegerRing p) :
    dworkParameterPowerLinearMap p K (Pi.single i c) =
      algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K) c *
        dworkParameter p K ^ (i : ℕ) := by
  classical
  rw [dworkParameterPowerLinearMap_apply, Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [Pi.single_eq_of_ne hji]
  · intro hi
    simp at hi

theorem dworkParameterPowerLinearMap_mem_adjoin
    (a : Fin (p - 1) → RationalPadicIntegerRing p) :
    dworkParameterPowerLinearMap p K a ∈ dworkParameterAdjoin p K := by
  classical
  rw [dworkParameterPowerLinearMap_apply]
  exact Subalgebra.sum_mem _ (fun i _hi =>
    (dworkParameterAdjoin p K).mul_mem
      (algebraMap_mem_dworkParameterAdjoin (p := p) (K := K) (a i))
      (dworkParameter_pow_mem_adjoin (p := p) (K := K) (i : ℕ)))

theorem dworkParameterAdjoin_eq_top_of_powerLinearMap_surjective
    (hsurj : Function.Surjective (dworkParameterPowerLinearMap p K)) :
    dworkParameterAdjoin p K = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro x _hx
    rcases hsurj x with ⟨a, rfl⟩
    exact dworkParameterPowerLinearMap_mem_adjoin (p := p) (K := K) a

/-- Once the finite power expansion map is bijective, its image of the standard
function basis is the desired basis of the Dwork completion. -/
noncomputable def dworkParameterPowerBasisOfBijective
    (hbij : Function.Bijective (dworkParameterPowerLinearMap p K)) :
    Module.Basis (Fin (p - 1)) (RationalPadicIntegerRing p)
      (DworkCompleteIntegerRing p K) :=
  (Pi.basisFun (RationalPadicIntegerRing p) (Fin (p - 1))).map
    (LinearEquiv.ofBijective (dworkParameterPowerLinearMap p K) hbij)

theorem dworkParameterPowerBasisOfBijective_apply
    (hbij : Function.Bijective (dworkParameterPowerLinearMap p K))
    (i : Fin (p - 1)) :
    dworkParameterPowerBasisOfBijective p K hbij i =
      dworkParameter p K ^ (i : ℕ) := by
  classical
  rw [dworkParameterPowerBasisOfBijective, Module.Basis.map_apply, Pi.basisFun_apply]
  exact dworkParameterPowerLinearMap_single (p := p) (K := K) i

theorem pow_sub_pow_mem_dworkParameterIdeal_pow_add {N n : ℕ} (hn : n ≠ 0)
    {x y : DworkCompleteIntegerRing p K} (hx : x ∈ dworkParameterIdeal p K)
    (hy : y ∈ dworkParameterIdeal p K)
    (hxy : x - y ∈ (dworkParameterIdeal p K) ^ (N + 1)) :
    x ^ n - y ^ n ∈ (dworkParameterIdeal p K) ^ (N + n) := by
  classical
  let I : Ideal (DworkCompleteIntegerRing p K) := dworkParameterIdeal p K
  let g : DworkCompleteIntegerRing p K :=
    ∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)
  have hg : g ∈ I ^ (n - 1) := by
    refine Ideal.sum_mem _ ?_
    intro i hi
    have hix : x ^ i ∈ I ^ i := Ideal.pow_mem_pow hx i
    have hiy : y ^ (n - 1 - i) ∈ I ^ (n - 1 - i) :=
      Ideal.pow_mem_pow hy (n - 1 - i)
    have hmul : x ^ i * y ^ (n - 1 - i) ∈ I ^ i * I ^ (n - 1 - i) :=
      Ideal.mul_mem_mul hix hiy
    rw [← pow_add] at hmul
    have hidx : i + (n - 1 - i) = n - 1 := by
      have hi_lt : i < n := Finset.mem_range.mp hi
      omega
    simpa [hidx] using hmul
  have hprod : (x - y) * g ∈ I ^ (N + n) := by
    have hmul : (x - y) * g ∈ I ^ (N + 1) * I ^ (n - 1) :=
      Ideal.mul_mem_mul hxy hg
    rw [← pow_add] at hmul
    have hidx : (N + 1) + (n - 1) = N + n := by omega
    simpa [I, hidx] using hmul
  have hgeom : (x - y) * g = x ^ n - y ^ n := by
    change (x - y) *
        (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n
    rw [mul_comm]
    exact geom_sum₂_mul x y n
  simpa [I, g, hgeom] using hprod

theorem dworkCompleteLambda_pow_sub_dworkParameter_pow_mem_parameterIdeal_pow_succ
    (n : ℕ) :
    dworkCompleteLambda p K ^ n - dworkParameter p K ^ n ∈
      (dworkParameterIdeal p K) ^ (n + 1) := by
  cases n with
  | zero =>
      simp
  | succ n =>
      have hLam : dworkCompleteLambda p K ∈ dworkParameterIdeal p K :=
        dworkCompleteLambda_mem_dworkParameterIdeal (p := p) (K := K)
      have hVarpi : dworkParameter p K ∈ dworkParameterIdeal p K := by
        rw [dworkParameterIdeal]
        exact Ideal.mem_span_singleton_self (dworkParameter p K)
      have hsub : dworkCompleteLambda p K - dworkParameter p K ∈
          (dworkParameterIdeal p K) ^ (1 + 1) := by
        simpa [one_add_one_eq_two] using
          dworkCompleteLambda_sub_dworkParameter_mem_parameterIdeal_sq
            (p := p) (K := K)
      have h := pow_sub_pow_mem_dworkParameterIdeal_pow_add
        (p := p) (K := K) (N := 1) (n := n + 1)
        (by omega) hLam hVarpi hsub
      rwa [Nat.add_comm 1 (n + 1)] at h

theorem dworkParameter_pow_sub_dworkCompleteLambda_pow_mem_parameterIdeal_pow_succ
    (n : ℕ) :
    dworkParameter p K ^ n - dworkCompleteLambda p K ^ n ∈
      (dworkParameterIdeal p K) ^ (n + 1) := by
  have h :=
    ((dworkParameterIdeal p K) ^ (n + 1)).neg_mem
      (dworkCompleteLambda_pow_sub_dworkParameter_pow_mem_parameterIdeal_pow_succ
        (p := p) (K := K) n)
  simpa [neg_sub] using h

/-- Dwork-side parameter-ideal denominator bookkeeping:
`(varpi)^(m(p-1)+s) = (p^m) (varpi)^s`. -/
theorem dworkParameterIdeal_pow_mul_pred_add_eq_span_natCast_prime_pow_mul
    (m s : ℕ) :
    (dworkParameterIdeal p K) ^ (m * (p - 1) + s) =
      Ideal.span ({((p : DworkCompleteIntegerRing p K) ^ m)} :
          Set (DworkCompleteIntegerRing p K)) *
        (dworkParameterIdeal p K) ^ s := by
  let I : Ideal (DworkCompleteIntegerRing p K) := dworkParameterIdeal p K
  calc
    I ^ (m * (p - 1) + s) = I ^ (m * (p - 1)) * I ^ s := by
      rw [pow_add]
    _ = (I ^ (p - 1)) ^ m * I ^ s := by
      rw [Nat.mul_comm m (p - 1), ← pow_mul]
    _ = (Ideal.span ({(p : DworkCompleteIntegerRing p K)} :
          Set (DworkCompleteIntegerRing p K))) ^ m * I ^ s := by
      rw [← span_natCast_prime_dworkComplete_eq_parameterIdeal_pow_pred
        (p := p) (K := K)]
    _ = Ideal.span ({((p : DworkCompleteIntegerRing p K) ^ m)} :
          Set (DworkCompleteIntegerRing p K)) * I ^ s := by
      rw [Ideal.span_singleton_pow]

/-- If a completed Dwork element has parameter-adic order at least
`m * (p - 1) + s`, one can factor out `p^m` and keep residual order at least
`s`. -/
theorem exists_natCast_prime_pow_mul_eq_of_mem_dworkParameterIdeal_pow_mul_pred_add
    (m s : ℕ) {x : DworkCompleteIntegerRing p K}
    (hx : x ∈ (dworkParameterIdeal p K) ^ (m * (p - 1) + s)) :
    ∃ y : DworkCompleteIntegerRing p K, y ∈ (dworkParameterIdeal p K) ^ s ∧
      (p : DworkCompleteIntegerRing p K) ^ m * y = x := by
  rw [dworkParameterIdeal_pow_mul_pred_add_eq_span_natCast_prime_pow_mul
    (p := p) (K := K) m s] at hx
  exact Ideal.mem_span_singleton_mul.mp hx

theorem natCast_prime_pow_mem_dworkParameterIdeal_pow_mul_pred (m : ℕ) :
    (p : DworkCompleteIntegerRing p K) ^ m ∈
      (dworkParameterIdeal p K) ^ (m * (p - 1)) := by
  rw [show m * (p - 1) = m * (p - 1) + 0 by omega]
  rw [dworkParameterIdeal_pow_mul_pred_add_eq_span_natCast_prime_pow_mul
    (p := p) (K := K) m 0]
  have hmul := Ideal.mul_mem_mul
    (Ideal.mem_span_singleton_self ((p : DworkCompleteIntegerRing p K) ^ m))
    (show (1 : DworkCompleteIntegerRing p K) ∈
      (dworkParameterIdeal p K) ^ 0 by simp)
  rwa [mul_one] at hmul

theorem natCast_prime_pow_mem_dworkParameterIdeal_pow {M N : ℕ}
    (hNM : N ≤ M * (p - 1)) :
    (p : DworkCompleteIntegerRing p K) ^ M ∈ (dworkParameterIdeal p K) ^ N :=
  Ideal.pow_le_pow_right hNM
    (natCast_prime_pow_mem_dworkParameterIdeal_pow_mul_pred (p := p) (K := K) M)

theorem mem_lambdaIdeal_iff_valuation_le_lambda
    (x : ValuedIntegerRing p K) :
    x ∈ lambdaIdeal p K ↔
      Valued.v (x : ValuedCompletion p K) ≤
        Valued.v (valuedCyclotomicLambdaInteger p K : ValuedCompletion p K) := by
  let hv :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (K := K) (v := Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum p K)
  have hset :=
    Valuation.Integers.coe_span_singleton_eq_setOf_le_v_algebraMap
      (F := ValuedCompletion p K) hv (valuedCyclotomicLambdaInteger p K)
  change x ∈ ((Ideal.span ({valuedCyclotomicLambdaInteger p K} :
      Set (ValuedIntegerRing p K)) : Ideal (ValuedIntegerRing p K)) :
        Set (ValuedIntegerRing p K)) ↔
    Valued.v (x : ValuedCompletion p K) ≤
      Valued.v (valuedCyclotomicLambdaInteger p K : ValuedCompletion p K)
  rw [show ((Ideal.span ({valuedCyclotomicLambdaInteger p K} :
      Set (ValuedIntegerRing p K)) : Ideal (ValuedIntegerRing p K)) :
        Set (ValuedIntegerRing p K)) =
      {y : ValuedIntegerRing p K |
        Valued.v (y : ValuedCompletion p K) ≤
          Valued.v (valuedCyclotomicLambdaInteger p K : ValuedCompletion p K)} by
    simpa using hset]
  rfl

theorem mem_lambdaIdeal_iff_valuation_le_exp_neg_one
    (x : ValuedIntegerRing p K) :
    x ∈ lambdaIdeal p K ↔
      Valued.v (x : ValuedCompletion p K) ≤ WithZero.exp (-1 : ℤ) := by
  rw [mem_lambdaIdeal_iff_valuation_le_lambda (p := p) (K := K)]
  have hlam :
      Valued.v (valuedCyclotomicLambdaInteger p K : ValuedCompletion p K) =
        WithZero.exp (-1 : ℤ) :=
    valuedCyclotomicLambda_valuation (p := p) (K := K)
  rw [hlam]

/-- The global lambda residue field is represented by the rational classes
`0, ..., p - 1`. -/
theorem globalCyclotomicResidue_natCast_fin_surjective :
    Function.Surjective
      (fun i : Fin p =>
        Ideal.Quotient.mk (Reflection.Local.cyclotomicLambda p K)
          (algebraMap ℤ (𝓞 K) (i : ℤ))) := by
  classical
  let Q : Type _ := 𝓞 K ⧸ Reflection.Local.cyclotomicLambda p K
  let f : Fin p → Q := fun i =>
    Ideal.Quotient.mk (Reflection.Local.cyclotomicLambda p K)
      (algebraMap ℤ (𝓞 K) (i : ℤ))
  have hcardQ : Nat.card Q = p :=
    Reflection.Local.globalCyclotomicResidueCard (p := p) (K := K)
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by
    rw [hcardQ]
    exact (Fact.out : Nat.Prime p).ne_zero)
  have hinj : Function.Injective f := by
    intro i j hij
    have hmem :
        algebraMap ℤ (𝓞 K) ((i : ℤ) - (j : ℤ)) ∈
          Reflection.Local.cyclotomicLambda p K := by
      have hsub := (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := Reflection.Local.cyclotomicLambda p K)
        (algebraMap ℤ (𝓞 K) (i : ℤ))
        (algebraMap ℤ (𝓞 K) (j : ℤ))).mp hij
      simpa [map_sub] using hsub
    have hlie :
        (Reflection.Local.cyclotomicLambda p K).LiesOver
          (Furtwaengler.KummerArtinHasse.lambdaRationalPrimeIdeal p) := by
      simpa [Reflection.Local.cyclotomicLambda] using
        Furtwaengler.KummerArtinHasse.zetaPrime_liesOver_lambdaRationalPrimeIdeal
          (p := p) (K := K)
    have hmemZ :
        ((i : ℤ) - (j : ℤ)) ∈
          Furtwaengler.KummerArtinHasse.lambdaRationalPrimeIdeal p := by
      letI := hlie
      exact (Ideal.mem_of_liesOver
        (P := Reflection.Local.cyclotomicLambda p K)
        (p := Furtwaengler.KummerArtinHasse.lambdaRationalPrimeIdeal p)
        ((i : ℤ) - (j : ℤ))).mpr hmem
    rw [Furtwaengler.KummerArtinHasse.lambdaRationalPrimeIdeal,
      Ideal.mem_span_singleton] at hmemZ
    have hi_lt : (i : ℤ) < p := by exact_mod_cast i.isLt
    have hj_lt : (j : ℤ) < p := by exact_mod_cast j.isLt
    have hp_pos : (0 : ℤ) < p := by
      exact_mod_cast (Fact.out : Nat.Prime p).pos
    have hdiff_zero : (i : ℤ) - (j : ℤ) = 0 :=
      Int.eq_zero_of_abs_lt_dvd hmemZ (by rw [abs_lt]; omega)
    apply Fin.ext
    omega
  have hcard : Nat.card (Fin p) = Nat.card Q := by
    simp [hcardQ]
  obtain ⟨e : Fin p ≃ Q⟩ := Finite.card_eq.mp hcard
  exact (Finite.injective_iff_surjective_of_equiv e).mp hinj

theorem exists_global_fin_valuation_sub_le_exp_neg_one_of_valuation_le_one
    (x : K)
    (hx :
      (Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum p K).valuation K x ≤ 1) :
    ∃ i : Fin p,
      (Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum p K).valuation K
          (x - (i : ℤ)) ≤ WithZero.exp (-1 : ℤ) := by
  classical
  let v := Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum p K
  let I : Ideal (𝓞 K) := Reflection.Local.cyclotomicLambda p K
  have hImax : I.IsMaximal :=
    Reflection.Local.cyclotomicLambda_isMaximal (p := p) (K := K)
  letI : I.IsMaximal := hImax
  letI : Field (𝓞 K ⧸ I) := Ideal.Quotient.field I
  rcases v.exists_primeCompl_mul_eq_of_integer (K := K) x hx with ⟨n, d, hxd⟩
  let q : 𝓞 K →+* 𝓞 K ⧸ I := Ideal.Quotient.mk I
  have hd_not_mem : (d : 𝓞 K) ∉ I := d.property
  have hqd_ne : q d ≠ 0 := by
    change Ideal.Quotient.mk I (d : 𝓞 K) ≠ 0
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hd_not_mem
  rcases globalCyclotomicResidue_natCast_fin_surjective (p := p) (K := K)
      (q n * (q d)⁻¹) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  have hq_n_eq :
      q n = q (algebraMap ℤ (𝓞 K) (i : ℤ)) * q d := by
    calc
      q n = (q n * (q d)⁻¹) * q d := by
        rw [mul_assoc, inv_mul_cancel₀ hqd_ne, mul_one]
      _ = q (algebraMap ℤ (𝓞 K) (i : ℤ)) * q d := by
        rw [← hi]
  have hmem :
      n - algebraMap ℤ (𝓞 K) (i : ℤ) * d ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q (n - algebraMap ℤ (𝓞 K) (i : ℤ) * d) = 0
    rw [map_sub, map_mul, hq_n_eq, sub_self]
  have hval_mem :
      v.valuation K
          (algebraMap (𝓞 K) K
            (n - algebraMap ℤ (𝓞 K) (i : ℤ) * d)) ≤
        WithZero.exp (-1 : ℤ) := by
    rw [v.valuation_of_algebraMap]
    have hpow : n - algebraMap ℤ (𝓞 K) (i : ℤ) * d ∈ v.asIdeal ^ 1 := by
      simpa [v, I, Reflection.Local.cyclotomicLambda] using hmem
    exact (v.intValuation_le_pow_iff_mem
      (n - algebraMap ℤ (𝓞 K) (i : ℤ) * d) 1).mpr hpow
  have hdval :
      v.valuation K (algebraMap (𝓞 K) K (d : 𝓞 K)) = 1 := by
    rw [v.valuation_of_algebraMap, v.intValuation_eq_one_iff_mem_primeCompl]
    exact d.property
  have hmul :
      (x - (i : ℤ)) * algebraMap (𝓞 K) K (d : 𝓞 K) =
        algebraMap (𝓞 K) K
          (n - algebraMap ℤ (𝓞 K) (i : ℤ) * d) := by
    rw [map_sub, map_mul, sub_mul, hxd]
    simp [sub_eq_add_neg]
  have hmulval :
      v.valuation K ((x - (i : ℤ)) * algebraMap (𝓞 K) K (d : 𝓞 K)) ≤
        WithZero.exp (-1 : ℤ) := by
    rw [hmul]
    exact hval_mem
  rw [map_mul, hdval, mul_one] at hmulval
  exact hmulval

theorem exists_completion_fin_valuation_sub_le_exp_neg_one_of_valuation_le_one
    (x : ValuedCompletion p K) (hx : Valued.v x ≤ 1) :
    ∃ i : Fin p, Valued.v (x - (i : ℤ)) ≤ WithZero.exp (-1 : ℤ) := by
  classical
  let v := Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum p K
  let A : Set (ValuedCompletion p K) := {x | Valued.v x ≤ 1}
  let B : Set (ValuedCompletion p K) :=
    ⋃ i : Fin p, {x | Valued.v (x - (i : ℤ)) ≤ WithZero.exp (-1 : ℤ)}
  have hlam :
      Valued.v (valuedCyclotomicLambdaInteger p K : ValuedCompletion p K) =
        WithZero.exp (-1 : ℤ) :=
    valuedCyclotomicLambda_valuation (p := p) (K := K)
  have hA' : IsClopen {x : ValuedCompletion p K | Valued.v.restrict x ≤ 1} :=
    Valued.isClopen_closedBall
      (R := ValuedCompletion p K) (r := 1) one_ne_zero
  have hA : IsClopen A := by
    convert hA' using 1
    ext x
    simp [A, Valuation.restrict_le_one_iff]
  have hB_i :
      ∀ i : Fin p,
        IsClopen
          {x : ValuedCompletion p K |
            Valued.v (x - (i : ℤ)) ≤ WithZero.exp (-1 : ℤ)} := by
    intro i
    have hlam_ne :
        Valued.v.restrict
            (valuedCyclotomicLambdaInteger p K : ValuedCompletion p K) ≠ 0 := by
      have hval_ne :
          Valued.v (valuedCyclotomicLambdaInteger p K : ValuedCompletion p K) ≠ 0 := by
        rw [hlam]
        exact WithZero.exp_ne_zero
      have hne :
          (valuedCyclotomicLambdaInteger p K : ValuedCompletion p K) ≠ 0 :=
        (Valuation.ne_zero_iff
          (Valued.v : Valuation (ValuedCompletion p K) (WithZero (Multiplicative ℤ)))).mp
            hval_ne
      exact (Valuation.ne_zero_iff Valued.v.restrict).mpr hne
    have hclosed :
        IsClopen
          {x : ValuedCompletion p K |
            Valued.v.restrict (x - (i : ℤ)) ≤
              Valued.v.restrict
                (valuedCyclotomicLambdaInteger p K : ValuedCompletion p K)} :=
      (Valued.isClopen_closedBall
          (R := ValuedCompletion p K)
          (r := Valued.v.restrict
            (valuedCyclotomicLambdaInteger p K : ValuedCompletion p K))
          hlam_ne).preimage (continuous_id.sub continuous_const)
    convert hclosed using 1
    ext x
    simp [hlam]
  have hB : IsClopen B := by
    dsimp [B]
    exact isClopen_iUnion_of_finite hB_i
  have hcover_all :
      ∀ x : ValuedCompletion p K, x ∈ Aᶜ ∪ B := by
    intro x
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
        exact (hA.compl.union hB).1
    | ih y =>
        by_cases hy : Valued.v (y : ValuedCompletion p K) ≤ 1
        · right
          have hyK : v.valuation K (WithVal.ofVal y) ≤ 1 := by
            simpa [v, Valued.valuedCompletion_apply, WithVal.apply_ofVal] using hy
          rcases exists_global_fin_valuation_sub_le_exp_neg_one_of_valuation_le_one
              (p := p) (K := K) (WithVal.ofVal y) hyK with
            ⟨i, hi⟩
          refine Set.mem_iUnion.mpr ⟨i, ?_⟩
          have hconst :
              ((i : ℕ) : ValuedCompletion p K) =
                (((i : ℕ) : WithVal (v.valuation K)) :
                  ValuedCompletion p K) :=
            (map_natCast
                (UniformSpace.Completion.coeRingHom :
                  WithVal (v.valuation K) →+*
                      ValuedCompletion p K) (i : ℕ)).symm
          have htarget :
              Valued.v
                  (((y -
                    ((i : ℕ) : WithVal (v.valuation K))) :
                    WithVal (v.valuation K)) :
                    ValuedCompletion p K) ≤ WithZero.exp (-1 : ℤ) := by
            rw [Valued.valuedCompletion_apply, ← WithVal.apply_ofVal]
            convert hi using 2
            simp [WithVal.ofVal_sub, WithVal.ofVal_natCast]
          change
            Valued.v
                ((y : ValuedCompletion p K) - ((i : ℕ) : ValuedCompletion p K)) ≤
              WithZero.exp (-1 : ℤ)
          rw [hconst]
          simpa [UniformSpace.Completion.coe_sub] using htarget
        · left
          exact hy
  have hcover : x ∈ Aᶜ ∪ B := hcover_all x
  have hxA : x ∈ A := hx
  have hxB : x ∈ B := by
    rcases hcover with hxnotA | hxB
    · exact (hxnotA hxA).elim
    · exact hxB
  simpa [B] using hxB

@[simp]
theorem rationalPadicIntegerToValuedInteger_algebraMap_int_coe (z : ℤ) :
    ((rationalPadicIntegerToValuedInteger (p := p) (K := K)
      (algebraMap ℤ (RationalPadicIntegerRing p) z) : ValuedIntegerRing p K) :
        ValuedCompletion p K) =
      (z : ValuedCompletion p K) := by
  change
    rationalToLambdaCompletionRingHom (p := p) (K := K)
        ((algebraMap ℤ (RationalPadicIntegerRing p) z :
          RationalPadicIntegerRing p) :
          (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) =
      (z : ValuedCompletion p K)
  rw [show
      ((algebraMap ℤ (RationalPadicIntegerRing p) z :
          RationalPadicIntegerRing p) :
          (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) =
        algebraMap ℚ ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
          (z : ℚ) from rfl,
    rationalToLambdaCompletionRingHom_algebraMap]
  simp

theorem valuedInteger_residue_lift_rationalPadicInteger
    (x : ValuedIntegerRing p K) :
    ∃ a : RationalPadicIntegerRing p,
      x - rationalPadicIntegerToValuedInteger (p := p) (K := K) a ∈
        lambdaIdeal p K := by
  classical
  have hx : Valued.v (x : ValuedCompletion p K) ≤ 1 := x.property
  rcases exists_completion_fin_valuation_sub_le_exp_neg_one_of_valuation_le_one
      (p := p) (K := K) (x : ValuedCompletion p K) hx with
    ⟨i, hi⟩
  refine ⟨algebraMap ℤ (RationalPadicIntegerRing p) (i : ℤ), ?_⟩
  rw [mem_lambdaIdeal_iff_valuation_le_exp_neg_one]
  simpa using hi

theorem dworkComplete_residue_lift_of_valuedInteger_residue_lift
    (hres :
      ∀ x : ValuedIntegerRing p K,
        ∃ a : RationalPadicIntegerRing p,
          x - rationalPadicIntegerToValuedInteger (p := p) (K := K) a ∈
            lambdaIdeal p K) :
    ∀ x : DworkCompleteIntegerRing p K,
      ∃ a : RationalPadicIntegerRing p,
        x - algebraMap (RationalPadicIntegerRing p)
            (DworkCompleteIntegerRing p K) a ∈ dworkParameterIdeal p K := by
  intro x
  let I₀ : Ideal (ValuedIntegerRing p K) := lambdaIdeal p K
  let S : Type _ := DworkCompleteIntegerRing p K
  rcases Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ I₀ 1 x) with ⟨r, hr⟩
  rcases hres r with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have ha' :
      r - rationalPadicIntegerToValuedInteger (p := p) (K := K) a ∈ I₀ ^ 1 := by
    simpa [I₀, pow_one] using ha
  have heval :
      AdicCompletion.evalₐ I₀ 1
          (x - algebraMap (RationalPadicIntegerRing p) S a) = 0 := by
    calc
      AdicCompletion.evalₐ I₀ 1
          (x - algebraMap (RationalPadicIntegerRing p) S a)
          = Ideal.Quotient.mk (I₀ ^ 1) r -
              Ideal.Quotient.mk (I₀ ^ 1)
                (rationalPadicIntegerToValuedInteger (p := p) (K := K) a) := by
            rw [map_sub, ← hr, algebraMap_rationalPadicInteger_dworkComplete_apply,
              AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
            simp
      _ = Ideal.Quotient.mk (I₀ ^ 1)
            (r - rationalPadicIntegerToValuedInteger (p := p) (K := K) a) :=
            (map_sub (Ideal.Quotient.mk (I₀ ^ 1)) r
              (rationalPadicIntegerToValuedInteger (p := p) (K := K) a)).symm
      _ = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr ha'
  have hmem :
      x - algebraMap (RationalPadicIntegerRing p) S a ∈
        (dworkCompleteLambdaIdeal p K) ^ 1 :=
    dworkComplete_mem_lambdaIdeal_pow_of_evalₐ_eq_zero
      (p := p) (K := K) heval
  simpa [S, pow_one, dworkCompleteLambdaIdeal_eq_dworkParameterIdeal
    (p := p) (K := K)] using hmem

set_option maxHeartbeats 800000 in
/-- This induction repeatedly rewrites through the completed Dwork algebra
structure and the coefficient algebra map; the higher heartbeat limit keeps
the final normalization steps stable. -/
theorem dworkParameterPowerLinearMap_approx_of_residue_lift
    (hres :
      ∀ x : DworkCompleteIntegerRing p K,
        ∃ a : RationalPadicIntegerRing p,
          x - algebraMap (RationalPadicIntegerRing p)
              (DworkCompleteIntegerRing p K) a ∈ dworkParameterIdeal p K) :
    ∀ N : ℕ, ∀ x : DworkCompleteIntegerRing p K,
      ∃ a : Fin (p - 1) → RationalPadicIntegerRing p,
        x - dworkParameterPowerLinearMap p K a ∈
          (dworkParameterIdeal p K) ^ N := by
  classical
  intro N
  induction N with
  | zero =>
      intro x
      refine ⟨0, ?_⟩
      simp
  | succ N ih =>
      intro x
      rcases ih x with ⟨a, ha⟩
      let S : Type _ := DworkCompleteIntegerRing p K
      let R₀ : Type := RationalPadicIntegerRing p
      let I : Ideal S := dworkParameterIdeal p K
      let varpi : S := dworkParameter p K
      let m : ℕ := N / (p - 1)
      let s : ℕ := N % (p - 1)
      have hp_pred_pos : 0 < p - 1 :=
        Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
      have hs_lt : s < p - 1 := Nat.mod_lt N hp_pred_pos
      let i : Fin (p - 1) := ⟨s, hs_lt⟩
      have hN : N = m * (p - 1) + s := by
        dsimp [m, s]
        calc
          N = (p - 1) * (N / (p - 1)) + N % (p - 1) :=
            (Nat.div_add_mod N (p - 1)).symm
          _ = N / (p - 1) * (p - 1) + N % (p - 1) := by
            rw [Nat.mul_comm]
      have ha' : x - dworkParameterPowerLinearMap p K a ∈
          I ^ (m * (p - 1) + s) := by
        simpa [I, hN] using ha
      rcases exists_natCast_prime_pow_mul_eq_of_mem_dworkParameterIdeal_pow_mul_pred_add
          (p := p) (K := K) m s ha' with
        ⟨z, hz, hz_eq⟩
      have hz_span : z ∈ Ideal.span ({varpi ^ s} : Set S) := by
        simpa [I, varpi, dworkParameterIdeal, Ideal.span_singleton_pow] using hz
      rcases Ideal.mem_span_singleton'.mp hz_span with ⟨y, hyz⟩
      rcases hres y with ⟨b, hb⟩
      have hvarpi_pow : varpi ^ s ∈ I ^ s :=
        Ideal.pow_mem_pow
          (by
            dsimp [I, varpi, dworkParameterIdeal]
            exact Ideal.mem_span_singleton_self (dworkParameter p K)) s
      have hdiff_mul : (y - algebraMap R₀ S b) * varpi ^ s ∈ I ^ (s + 1) := by
        rw [pow_succ']
        exact Ideal.mul_mem_mul hb hvarpi_pow
      have hz_sub : z - algebraMap R₀ S b * varpi ^ s ∈ I ^ (s + 1) := by
        have hcalc : z - algebraMap R₀ S b * varpi ^ s =
            (y - algebraMap R₀ S b) * varpi ^ s := by
          rw [← hyz]
          ring
        simpa [hcalc] using hdiff_mul
      have hmul_mem :
          (p : S) ^ m * (z - algebraMap R₀ S b * varpi ^ s) ∈
            I ^ (m * (p - 1) + (s + 1)) := by
        have hmul : (p : S) ^ m * (z - algebraMap R₀ S b * varpi ^ s) ∈
            Ideal.span ({((p : S) ^ m)} : Set S) * I ^ (s + 1) :=
          Ideal.mul_mem_mul
            (Ideal.mem_span_singleton_self ((p : S) ^ m)) hz_sub
        rw [← dworkParameterIdeal_pow_mul_pred_add_eq_span_natCast_prime_pow_mul
          (p := p) (K := K) m (s + 1)] at hmul
        simpa [S, I] using hmul
      let corr : Fin (p - 1) → R₀ :=
        Pi.single i ((p : R₀) ^ m * b)
      refine ⟨a + corr, ?_⟩
      have hcorr :
          dworkParameterPowerLinearMap p K corr =
            (p : S) ^ m * algebraMap R₀ S b * varpi ^ s := by
        dsimp [corr, i, R₀, S, varpi]
        rw [dworkParameterPowerLinearMap_single_coeff]
        simp [mul_assoc]
      have hresid :
          x - dworkParameterPowerLinearMap p K (a + corr) =
            (p : S) ^ m * (z - algebraMap R₀ S b * varpi ^ s) := by
        have hz_eq' : (p : S) ^ m * z =
            x - dworkParameterPowerLinearMap p K a :=
          hz_eq
        calc
          x - dworkParameterPowerLinearMap p K (a + corr) =
              (x - dworkParameterPowerLinearMap p K a) -
                dworkParameterPowerLinearMap p K corr := by
            rw [map_add]
            abel
          _ = (p : S) ^ m * z - (p : S) ^ m * algebraMap R₀ S b * varpi ^ s := by
            rw [hz_eq', hcorr]
          _ = (p : S) ^ m * (z - algebraMap R₀ S b * varpi ^ s) := by
            ring
      have hidx : m * (p - 1) + (s + 1) = N + 1 := by
        omega
      rw [hresid]
      change (p : S) ^ m * (z - algebraMap R₀ S b * varpi ^ s) ∈ I ^ (N + 1)
      rw [← hidx]
      exact hmul_mem

theorem dworkParameterPowerLinearMap_approx_of_valuedInteger_residue_lift
    (hres :
      ∀ x : ValuedIntegerRing p K,
        ∃ a : RationalPadicIntegerRing p,
          x - rationalPadicIntegerToValuedInteger (p := p) (K := K) a ∈
            lambdaIdeal p K) :
    ∀ N : ℕ, ∀ x : DworkCompleteIntegerRing p K,
      ∃ a : Fin (p - 1) → RationalPadicIntegerRing p,
        x - dworkParameterPowerLinearMap p K a ∈
          (dworkParameterIdeal p K) ^ N :=
  dworkParameterPowerLinearMap_approx_of_residue_lift (p := p) (K := K)
    (dworkComplete_residue_lift_of_valuedInteger_residue_lift
      (p := p) (K := K) hres)

theorem dworkParameterPowerLinearMap_approx :
    ∀ N : ℕ, ∀ x : DworkCompleteIntegerRing p K,
      ∃ a : Fin (p - 1) → RationalPadicIntegerRing p,
        x - dworkParameterPowerLinearMap p K a ∈
          (dworkParameterIdeal p K) ^ N :=
  dworkParameterPowerLinearMap_approx_of_valuedInteger_residue_lift
    (p := p) (K := K)
    (valuedInteger_residue_lift_rationalPadicInteger (p := p) (K := K))

theorem dworkParameterPowerLinearMap_quotient_surjective (N : ℕ) :
    Function.Surjective
      (fun a : Fin (p - 1) → RationalPadicIntegerRing p =>
        Ideal.Quotient.mk ((dworkParameterIdeal p K) ^ N)
          (dworkParameterPowerLinearMap p K a)) := by
  intro x
  rcases Ideal.Quotient.mk_surjective x with ⟨y, rfl⟩
  rcases dworkParameterPowerLinearMap_approx (p := p) (K := K) N y with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [Ideal.Quotient.eq]
  have hneg :
      -(y - dworkParameterPowerLinearMap p K a) ∈
        (dworkParameterIdeal p K) ^ N :=
    neg_mem ha
  simpa [neg_sub] using hneg

end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end
