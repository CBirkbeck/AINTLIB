module

public import BernoulliRegular.CyclotomicUnits.PadicLogSetup
public import BernoulliRegular.Reflection.Local.PowerMap
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteArtinHasseFormal
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteLogBounds
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteLogFormal
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Basic.Part1
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The corrected Dwork parameter

This file starts CU-09b.  The first layer is the coefficient map sending
`p`-integral rational Artin-Hasse coefficients into the valuation-completion
integer ring at `lambda = zeta_p - 1`.

The actual completed element `G_p(lambda)` is not constructed here yet.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open PowerSeries

namespace BernoulliRegular
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance valuedCompletion_charZero : CharZero (ValuedCompletion p K) :=
  algebraRat.charZero (ValuedCompletion p K)

/-- A `p`-integral rational has denominator outside the rational prime `(p)`. -/
theorem rIntegralRat_den_not_mem_lambdaRationalPrimeIdeal
    (q : Furtwaengler.DieudonneDwork.rIntegralRatSubring p) :
    ((q : ℚ).den : ℤ) ∉
      Furtwaengler.KummerArtinHasse.lambdaRationalPrimeIdeal p := by
  have hnot_dvd_nat : ¬ p ∣ (q : ℚ).den :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mp
      (show Nat.Coprime p (q : ℚ).den from q.property.symm)
  intro hmem
  have hnot_dvd_int : ¬ (p : ℤ) ∣ ((q : ℚ).den : ℤ) := fun h =>
    hnot_dvd_nat (Int.natCast_dvd_natCast.mp h)
  exact hnot_dvd_int (by
    simpa [Furtwaengler.KummerArtinHasse.lambdaRationalPrimeIdeal,
      Ideal.mem_span_singleton] using hmem)

/-- The lambda valuation of a `p`-integral rational coefficient is at most one
after embedding into the cyclotomic lambda completion. -/
theorem rIntegralRat_lambdaValuation_le_one
    (q : Furtwaengler.DieudonneDwork.rIntegralRatSubring p) :
    (Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum p K).valuation K
        (algebraMap ℚ K (q : ℚ)) ≤ 1 :=
  (Furtwaengler.KummerArtinHasse.lambdaValuation_algebraMap_rat_le_one_iff_den
      (p := p) (K := K) (q : ℚ)).mpr
    (rIntegralRat_den_not_mem_lambdaRationalPrimeIdeal (p := p) q)

/-- The field-valued coefficient map from `p`-integral rational coefficients
to the lambda-adic completion. -/
def rIntegralRatToValuedCompletion :
    Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+*
      ValuedCompletion p K :=
  (algebraMap K (ValuedCompletion p K)).comp
    ((algebraMap ℚ K).comp
      (Furtwaengler.DieudonneDwork.rIntegralRatSubring p).subtype)

@[simp]
theorem rIntegralRatToValuedCompletion_apply
    (q : Furtwaengler.DieudonneDwork.rIntegralRatSubring p) :
    rIntegralRatToValuedCompletion p K q =
      algebraMap K (ValuedCompletion p K) (algebraMap ℚ K (q : ℚ)) :=
  rfl

/-- The field-valued coefficient map lands in the completed integer ring. -/
theorem rIntegralRatToValuedCompletion_mem_integers
    (q : Furtwaengler.DieudonneDwork.rIntegralRatSubring p) :
    rIntegralRatToValuedCompletion p K q ∈
      (Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum p K).adicCompletionIntegers K := by
  rw [rIntegralRatToValuedCompletion_apply,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v
      (algebraMap K
        ((Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum p K).adicCompletion K)
        (algebraMap ℚ K (q : ℚ))) ≤ 1
  rw [show algebraMap K
        ((Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum p K).adicCompletion K)
        (algebraMap ℚ K (q : ℚ)) =
      ((algebraMap ℚ K (q : ℚ) : K) :
        (Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum p K).adicCompletion K) from rfl]
  rw [Valued.valuedCompletion_apply]
  exact rIntegralRat_lambdaValuation_le_one (p := p) (K := K) q

/-- The CU-09b coefficient map from `p`-integral rational coefficients into
the valuation-completion integer ring. -/
def rIntegralRatToValuedInteger :
    Furtwaengler.DieudonneDwork.rIntegralRatSubring p →+*
      ValuedIntegerRing p K where
  toFun q :=
    ⟨rIntegralRatToValuedCompletion p K q,
      rIntegralRatToValuedCompletion_mem_integers (p := p) (K := K) q⟩
  map_zero' := by
    ext
    exact map_zero (rIntegralRatToValuedCompletion p K)
  map_one' := by
    ext
    exact map_one (rIntegralRatToValuedCompletion p K)
  map_add' q₁ q₂ := by
    ext
    exact map_add (rIntegralRatToValuedCompletion p K) q₁ q₂
  map_mul' q₁ q₂ := by
    ext
    exact map_mul (rIntegralRatToValuedCompletion p K) q₁ q₂

@[simp]
theorem rIntegralRatToValuedInteger_coe
    (q : Furtwaengler.DieudonneDwork.rIntegralRatSubring p) :
    ((rIntegralRatToValuedInteger p K q : ValuedIntegerRing p K) :
        ValuedCompletion p K) =
      algebraMap K (ValuedCompletion p K) (algebraMap ℚ K (q : ℚ)) :=
  rfl

/-- The Artin-Hasse exponential as a power series over the chosen completed
integer ring. -/
def integralExpSeries : PowerSeries (ValuedIntegerRing p K) :=
  (show Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (FormalDwork.expSeries p) from
    fun n => Furtwaengler.artinHasseExpSeries_coeff_isRIntegral p n).mapTo
      (rIntegralRatToValuedInteger p K)

/-- The inverse series `G_p = (E_p - 1)^(-1)` as a power series over the chosen
completed integer ring. -/
def integralInverseSeries : PowerSeries (ValuedIntegerRing p K) :=
  (FormalDwork.inverseSeries_isPIntegral p).mapTo
    (rIntegralRatToValuedInteger p K)

/-- The series `E_p(T)-1` over the chosen completed integer ring. -/
def integralExpMinusOneSeries : PowerSeries (ValuedIntegerRing p K) :=
  (FormalDwork.expMinusOneSeries_isPIntegral p).mapTo
    (rIntegralRatToValuedInteger p K)

theorem integralExpMinusOneSeries_eq :
    integralExpMinusOneSeries p K = integralExpSeries p K - 1 := by
  let φ := rIntegralRatToValuedInteger p K
  let hE : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (FormalDwork.expSeries p) :=
    fun n => Furtwaengler.artinHasseExpSeries_coeff_isRIntegral p n
  let hOne : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (1 : PowerSeries ℚ) :=
    Furtwaengler.DieudonneDwork.IsRIntegralPS.one p
  let hM : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (FormalDwork.expMinusOneSeries p) :=
    FormalDwork.expMinusOneSeries_isPIntegral p
  calc
    integralExpMinusOneSeries p K = hM.mapTo φ := by
        rfl
    _ = (hE.sub hOne).mapTo φ :=
        Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_eq_of_eq
          φ hM (hE.sub hOne) (by
            simp [FormalDwork.expMinusOneSeries, FormalDwork.expSeries,
              Furtwaengler.artinHasseExpMinusOneSeries])
    _ = hE.mapTo φ - hOne.mapTo φ :=
        Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_sub φ hE hOne
    _ = integralExpSeries p K - 1 := by
        simp [integralExpSeries, φ]

/-- Integral-coefficient specialization of `E_p(G_p(T)) = 1 + T` in the
chosen completed local integer ring. -/
theorem integralExpSeries_subst_integralInverseSeries :
    PowerSeries.subst (integralInverseSeries p K) (integralExpSeries p K) =
      1 + (PowerSeries.X : PowerSeries (ValuedIntegerRing p K)) := by
  simpa [integralExpSeries, integralInverseSeries, FormalDwork.expSeries] using
    FormalDwork.expSeries_mapTo_subst_inverse (p := p)
      (rIntegralRatToValuedInteger p K)

theorem formal_inverseSeries_subst_expMinusOneSeries :
    PowerSeries.subst (FormalDwork.expMinusOneSeries p)
        (FormalDwork.inverseSeries p) =
      (PowerSeries.X : PowerSeries ℚ) := by
  let P : PowerSeries ℚ := FormalDwork.expMinusOneSeries p
  have hcoeff : (PowerSeries.coeff (R := ℚ) 1) P = 1 := by
    simp [P, FormalDwork.expMinusOneSeries]
  letI : Invertible ((PowerSeries.coeff (R := ℚ) 1) P) := by
    rw [hcoeff]
    exact invertibleOfNonzero (by norm_num : (1 : ℚ) ≠ 0)
  simpa [P, FormalDwork.inverseSeries, FormalDwork.expMinusOneSeries,
    Furtwaengler.artinHasseExpInverseSeries] using
    PowerSeries.subst_substInv_left P (by simp [P, FormalDwork.expMinusOneSeries])

/-- Integral-coefficient specialization of `G_p(E_p(T)-1) = T`. -/
theorem integralInverseSeries_subst_integralExpMinusOneSeries :
    PowerSeries.subst (integralExpMinusOneSeries p K)
        (integralInverseSeries p K) =
      (PowerSeries.X : PowerSeries (ValuedIntegerRing p K)) := by
  let φ := rIntegralRatToValuedInteger p K
  let hInv : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (FormalDwork.inverseSeries p) :=
    FormalDwork.inverseSeries_isPIntegral p
  let hM : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (FormalDwork.expMinusOneSeries p) :=
    FormalDwork.expMinusOneSeries_isPIntegral p
  have hM0 : PowerSeries.constantCoeff (FormalDwork.expMinusOneSeries p) = 0 :=
    FormalDwork.expMinusOneSeries_constantCoeff p
  calc
    PowerSeries.subst (integralExpMinusOneSeries p K)
        (integralInverseSeries p K)
        = (hInv.subst hM hM0).mapTo φ := by
            rw [Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_subst φ hInv hM hM0]
            rfl
    _ = (Furtwaengler.DieudonneDwork.IsRIntegralPS.X p).mapTo φ :=
            Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_eq_of_eq
              φ _ _ (formal_inverseSeries_subst_expMinusOneSeries (p := p))
    _ = (PowerSeries.X : PowerSeries (ValuedIntegerRing p K)) := by
            simp [φ]

/-- Integral-coefficient specialization of the formal conjugation identity
`G_p(H_p(-G_p(T))) = -G_p(T)`, where `H_p(T) = E_p(T)-1`. -/
theorem integralInverseSeries_subst_integralExpMinusOneSeries_subst_neg_inverse :
    PowerSeries.subst
        (PowerSeries.subst (-(integralInverseSeries p K))
          (integralExpMinusOneSeries p K))
        (integralInverseSeries p K) =
      -(integralInverseSeries p K) := by
  let φ := rIntegralRatToValuedInteger p K
  let hInv : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (FormalDwork.inverseSeries p) :=
    FormalDwork.inverseSeries_isPIntegral p
  let hM : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (FormalDwork.expMinusOneSeries p) :=
    FormalDwork.expMinusOneSeries_isPIntegral p
  let hNegInv : Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (-(FormalDwork.inverseSeries p)) :=
    hInv.neg
  have hNegInv0 :
      PowerSeries.constantCoeff (-(FormalDwork.inverseSeries p)) = 0 := by
    simp
  let inner : PowerSeries ℚ :=
    PowerSeries.subst (-(FormalDwork.inverseSeries p))
      (FormalDwork.expMinusOneSeries p)
  let hInner : Furtwaengler.DieudonneDwork.IsRIntegralPS p inner :=
    hM.subst hNegInv hNegInv0
  have hInner0 : PowerSeries.constantCoeff inner = 0 := by
    show PowerSeries.constantCoeff
        (PowerSeries.subst (-(FormalDwork.inverseSeries p))
          (FormalDwork.expMinusOneSeries p)) = 0
    exact PowerSeries.constantCoeff_subst_eq_zero
      (by simp : PowerSeries.constantCoeff (-(FormalDwork.inverseSeries p)) = 0)
      (FormalDwork.expMinusOneSeries p)
      (FormalDwork.expMinusOneSeries_constantCoeff p)
  have hInnerMap :
      hInner.mapTo φ =
        PowerSeries.subst (-(integralInverseSeries p K))
          (integralExpMinusOneSeries p K) := by
    calc
      hInner.mapTo φ =
          PowerSeries.subst (hNegInv.mapTo φ) (hM.mapTo φ) :=
            Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_subst
              φ hM hNegInv hNegInv0
      _ = PowerSeries.subst (-(integralInverseSeries p K))
          (integralExpMinusOneSeries p K) := by
            rw [show hNegInv.mapTo φ = -(integralInverseSeries p K) by
              simpa [hNegInv, hInv, integralInverseSeries, φ] using
                Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_neg φ hInv]
            rfl
  calc
    PowerSeries.subst
        (PowerSeries.subst (-(integralInverseSeries p K))
          (integralExpMinusOneSeries p K))
        (integralInverseSeries p K) =
        PowerSeries.subst (hInner.mapTo φ) (hInv.mapTo φ) := by
          rw [hInnerMap]
          rfl
    _ = (hInv.subst hInner hInner0).mapTo φ :=
          (Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_subst
            φ hInv hInner hInner0).symm
    _ = hInv.neg.mapTo φ :=
          Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_eq_of_eq
            φ (hInv.subst hInner hInner0) hInv.neg
            (by
              simpa [inner] using
                FormalDwork.inverseSeries_subst_expMinusOneSeries_subst_neg_inverse
                  (p := p))
    _ = -(integralInverseSeries p K) := by
          simpa [hInv, integralInverseSeries, φ] using
            Furtwaengler.DieudonneDwork.IsRIntegralPS.mapTo_neg φ hInv

/-- The inverse series over the completed local integer ring starts with `T`.
This is the finite-polynomial form needed for the eventual congruence
`G_p(lambda) == lambda mod lambda^2`. -/
theorem integralInverseSeries_trunc_two :
    PowerSeries.trunc 2 (integralInverseSeries p K) =
      PowerSeries.trunc 2
        (PowerSeries.X : PowerSeries (ValuedIntegerRing p K)) := by
  ext n
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  by_cases hn : n < 2
  · interval_cases n <;> simp [integralInverseSeries]
  · simp [hn]

/-- The Artin-Hasse exponential over the completed local integer ring starts
with `1 + T`. -/
theorem integralExpSeries_trunc_two :
    PowerSeries.trunc 2 (integralExpSeries p K) =
      PowerSeries.trunc 2
        (1 + PowerSeries.X : PowerSeries (ValuedIntegerRing p K)) := by
  ext n
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  by_cases hn : n < 2
  · interval_cases n
    · simp [integralExpSeries]
    · have hp_one : 1 < p := (Fact.out : Nat.Prime p).one_lt
      have hcoeff :
          (PowerSeries.coeff (R := ℚ) 1) (FormalDwork.expSeries p) = 1 := by
        simpa [FormalDwork.expSeries] using
          Furtwaengler.artinHasseExpSeries_coeff_eq_inv_factorial_of_lt p hp_one
      simp [integralExpSeries, hcoeff]
  · simp [hn]

/-- Finite truncation approximations to the corrected Dwork parameter
`G_p(lambda)`.  CU-09b's remaining analytic step is to prove that these
approximations converge in the completed local ring. -/
def dworkParameterApprox (N : ℕ) : ValuedIntegerRing p K :=
  (PowerSeries.trunc N (integralInverseSeries p K)).eval₂
    (RingHom.id (ValuedIntegerRing p K)) (valuedCyclotomicLambdaInteger p K)

@[simp]
theorem dworkParameterApprox_two :
    dworkParameterApprox p K 2 = valuedCyclotomicLambdaInteger p K := by
  unfold dworkParameterApprox
  rw [integralInverseSeries_trunc_two]
  simp

/-- Field-valued evaluation of an integral power series.  The definition is
available before CU-09b proves the convergence and quotient-compatibility
theorems needed to make it the final completed-local evaluation API. -/
def evalIntegralPowerSeriesField
    (F : PowerSeries (ValuedIntegerRing p K)) (x : ValuedCompletion p K) :
    ValuedCompletion p K :=
  PowerSeries.eval₂ (algebraMap (ValuedIntegerRing p K) (ValuedCompletion p K)) x F

/-- The field-valued candidate for the corrected Dwork parameter.  This is not
yet the final CU-09b integer-ring element: the remaining work is proving
convergence/integrality and the identity `E_p(G_p(lambda)) = zeta_p`. -/
def dworkParameterFieldCandidate : ValuedCompletion p K :=
  evalIntegralPowerSeriesField p K (integralInverseSeries p K)
    (valuedCyclotomicLambda p K)

/-- The principal `lambda`-adic ideal in the valuation integer ring.  This is
the ideal used for the honest inverse-limit construction below; it avoids
assuming an adic-completeness instance for `ValuedIntegerRing p K`. -/
abbrev lambdaIdeal : Ideal (ValuedIntegerRing p K) :=
  Ideal.span ({valuedCyclotomicLambdaInteger p K} : Set (ValuedIntegerRing p K))

/-- The `lambda`-adic completion of the valuation integer ring. -/
abbrev DworkCompleteIntegerRing : Type _ :=
  AdicCompletion (lambdaIdeal p K) (ValuedIntegerRing p K)

/-- The completed image of the cyclotomic lambda parameter. -/
def dworkCompleteLambda : DworkCompleteIntegerRing p K :=
  AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
    (valuedCyclotomicLambdaInteger p K)

/-- The lambda ideal is finitely generated, since it is principal. -/
theorem lambdaIdeal_fg : (lambdaIdeal p K).FG := by
  rw [lambdaIdeal]
  exact Submodule.fg_span_singleton (valuedCyclotomicLambdaInteger p K)

/-- The constructed Dwork integer ring is complete for the lambda-adic
filtration. -/
instance instIsAdicCompleteDworkCompleteIntegerRing :
    IsAdicComplete (lambdaIdeal p K) (DworkCompleteIntegerRing p K) :=
  AdicCompletion.isAdicComplete (I := lambdaIdeal p K)
    (M := ValuedIntegerRing p K) (lambdaIdeal_fg (p := p) (K := K))

/-- The Dwork completion is flat over the valuation integer ring. -/
instance instFlatDworkCompleteIntegerRing :
    Module.Flat (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K) := by
  dsimp [DworkCompleteIntegerRing]
  infer_instance

/-- The Dwork completion is torsion-free over the valuation integer ring. -/
instance instIsTorsionFreeDworkCompleteIntegerRing :
    Module.IsTorsionFree (ValuedIntegerRing p K)
      (DworkCompleteIntegerRing p K) := by
  infer_instance

/-- Scalar multiplication by a nonzero element of the valuation integer ring
is injective on the Dwork completion. -/
theorem dworkComplete_smul_eq_zero_of_ne_zero
    {a : ValuedIntegerRing p K} (ha : a ≠ 0)
    {x : DworkCompleteIntegerRing p K} (hx : a • x = 0) :
    x = 0 :=
  (smul_eq_zero_iff_right (M := DworkCompleteIntegerRing p K) ha).mp hx

theorem natCast_prime_ne_zero_valuedInteger :
    (p : ValuedIntegerRing p K) ≠ 0 := by
  intro hp_zero
  have hp_val_ne :
      Valued.v (((p : ValuedIntegerRing p K) : ValuedCompletion p K)) ≠ 0 := by
    rw [show (((p : ValuedIntegerRing p K) : ValuedCompletion p K)) =
        (p : ValuedCompletion p K) from rfl]
    rw [show (p : ValuedCompletion p K) =
        algebraMap K (ValuedCompletion p K) (p : K) by
          exact (map_natCast (algebraMap K (ValuedCompletion p K)) p).symm]
    rw [show algebraMap K (ValuedCompletion p K) (p : K) =
        ((p : K) : ValuedCompletion p K) from rfl]
    rw [Valued.valuedCompletion_apply]
    have hpK : (p : K) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    let vK := (Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum p K).valuation K
    have hpWithVal : (WithVal.equiv vK).symm (p : K) ≠ 0 := fun h =>
      hpK (by simpa [vK] using congrArg (WithVal.equiv vK) h)
    exact (Valuation.ne_zero_iff _).2 hpWithVal
  have hp_val_zero :
      Valued.v (((p : ValuedIntegerRing p K) : ValuedCompletion p K)) = 0 := by
    simp [hp_zero]
  exact hp_val_ne hp_val_zero

/-- The Dwork completion has no additive `p`-torsion. -/
theorem dworkComplete_natCast_p_nsmul_eq_zero
    {x : DworkCompleteIntegerRing p K} (hx : p • x = 0) :
    x = 0 := by
  have hp_ne : (p : ValuedIntegerRing p K) ≠ 0 :=
    natCast_prime_ne_zero_valuedInteger (p := p) (K := K)
  exact dworkComplete_smul_eq_zero_of_ne_zero (p := p) (K := K)
    hp_ne (by simpa [Nat.cast_smul_eq_nsmul] using hx)

/-- If every finite quotient coordinate of a completed element is killed by
`p`, then the completed element itself is zero. -/
theorem dworkComplete_eq_zero_of_evalₐ_natCast_p_nsmul_eq_zero
    {x : DworkCompleteIntegerRing p K}
    (hx : ∀ N : ℕ,
      p • AdicCompletion.evalₐ (lambdaIdeal p K) N x = 0) :
    x = 0 := by
  apply dworkComplete_natCast_p_nsmul_eq_zero (p := p) (K := K)
  apply AdicCompletion.ext_evalₐ
  intro N
  change AdicCompletion.evalₐ (lambdaIdeal p K) N (p • x) = 0
  rw [map_nsmul]
  exact hx N

/-- The completed lambda ideal on the constructed Dwork integer ring. -/
abbrev dworkCompleteLambdaIdeal : Ideal (DworkCompleteIntegerRing p K) :=
  (lambdaIdeal p K).map
    (algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K))

/-- The Dwork completion carries its lambda-adic topology by default. -/
instance instWithIdealDworkCompleteIntegerRing :
    WithIdeal (DworkCompleteIntegerRing p K) where
  i := dworkCompleteLambdaIdeal p K

/-- The constructed Dwork integer ring is complete for its completed
lambda-adic ideal. -/
theorem dworkComplete_isAdicComplete :
    IsAdicComplete (dworkCompleteLambdaIdeal p K)
      (DworkCompleteIntegerRing p K) := by
  rw [dworkCompleteLambdaIdeal]
  exact (IsAdicComplete.map_algebraMap_iff
    (I := lambdaIdeal p K)
    (S := DworkCompleteIntegerRing p K)
    (M := DworkCompleteIntegerRing p K)).mpr
      (instIsAdicCompleteDworkCompleteIntegerRing (p := p) (K := K))

theorem dworkCompleteLambdaIdeal_eq_span :
    dworkCompleteLambdaIdeal p K =
      Ideal.span ({dworkCompleteLambda p K} :
        Set (DworkCompleteIntegerRing p K)) := by
  rw [dworkCompleteLambdaIdeal]
  change (Ideal.span ({valuedCyclotomicLambdaInteger p K} :
      Set (ValuedIntegerRing p K))).map
        (algebraMap (ValuedIntegerRing p K)
          (DworkCompleteIntegerRing p K)) =
    Ideal.span ({dworkCompleteLambda p K} :
      Set (DworkCompleteIntegerRing p K))
  rw [Ideal.map_span]
  simp [dworkCompleteLambda, AdicCompletion.algebraMap_apply]

/-- In the explicit Dwork completion, vanishing in the `n`th quotient means
membership in the `n`th power of the completed lambda ideal. -/
theorem dworkComplete_mem_lambdaIdeal_pow_of_evalₐ_eq_zero
    {n : ℕ} {x : DworkCompleteIntegerRing p K}
    (hx : AdicCompletion.evalₐ (lambdaIdeal p K) n x = 0) :
    x ∈ (dworkCompleteLambdaIdeal p K) ^ n := by
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let S : Type _ := DworkCompleteIntegerRing p K
  have hle₁ : I ^ n ≤ I ^ n • (⊤ : Ideal R) :=
    le_of_eq (Ideal.mul_top (I ^ n)).symm
  have heval : AdicCompletion.eval I R n x = 0 := by
    rw [← AdicCompletion.factor_evalₐ_eq_eval (I := I) (R := R)
      (n := n) (x := x) hle₁]
    rw [hx, map_zero]
  have hxker : x ∈ LinearMap.ker (AdicCompletion.eval I R n) :=
    LinearMap.mem_ker.mpr heval
  have hxsmul : x ∈ I ^ n • (⊤ : Submodule R S) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval
      (I := I) (M := R) (lambdaIdeal_fg (p := p) (K := K)) (n := n)]
    exact hxker
  simpa [S, I, dworkCompleteLambdaIdeal, Ideal.map_pow] using hxsmul

/-- The Dwork completion is Henselian for its completed lambda ideal. -/
instance dworkComplete_henselianRing :
    HenselianRing (DworkCompleteIntegerRing p K)
      (dworkCompleteLambdaIdeal p K) :=
  @IsAdicComplete.henselianRing (DworkCompleteIntegerRing p K) _
    (dworkCompleteLambdaIdeal p K)
    (dworkComplete_isAdicComplete (p := p) (K := K))

theorem isUnit_one_add_of_mem_dworkCompleteLambdaIdeal
    {x : DworkCompleteIntegerRing p K}
    (hx : x ∈ dworkCompleteLambdaIdeal p K) : IsUnit (1 + x) := by
  have hH : HenselianRing (DworkCompleteIntegerRing p K)
      (dworkCompleteLambdaIdeal p K) :=
    dworkComplete_henselianRing (p := p) (K := K)
  have hxjac : x ∈ Ideal.jacobson (⊥ : Ideal (DworkCompleteIntegerRing p K)) :=
    hH.jac hx
  simpa [mul_comm, add_comm] using (Ideal.mem_jacobson_bot.mp hxjac 1)

/-- The lambda-adic topology on the Dwork completion is Hausdorff. -/
instance instT2SpaceDworkCompleteIntegerRing :
    T2Space (DworkCompleteIntegerRing p K) := by
  have hAdic :
      IsAdic (dworkCompleteLambdaIdeal p K :
        Ideal (DworkCompleteIntegerRing p K)) := rfl
  exact ((hAdic.isAdicComplete_iff).mp
    (dworkComplete_isAdicComplete (p := p) (K := K))).2

/-- The lambda-adic topology on the Dwork completion is complete. -/
instance instCompleteSpaceDworkCompleteIntegerRing :
    CompleteSpace (DworkCompleteIntegerRing p K) := by
  have hAdic :
      IsAdic (dworkCompleteLambdaIdeal p K :
        Ideal (DworkCompleteIntegerRing p K)) := rfl
  exact ((hAdic.isAdicComplete_iff).mp
    (dworkComplete_isAdicComplete (p := p) (K := K))).1

theorem valuedCyclotomicLambdaInteger_mem_lambdaIdeal :
    valuedCyclotomicLambdaInteger p K ∈ lambdaIdeal p K :=
  Ideal.subset_span (by simp)

theorem valuedCyclotomicLambdaInteger_pow_mem_lambdaIdeal_pow (n : ℕ) :
    valuedCyclotomicLambdaInteger p K ^ n ∈ (lambdaIdeal p K) ^ n :=
  Ideal.pow_mem_pow (valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K)) n

theorem valuedCyclotomicLambdaInteger_ne_zero :
    valuedCyclotomicLambdaInteger p K ≠ 0 := by
  intro hzero
  have hv_zero :
      Valued.v (valuedCyclotomicLambdaInteger p K : ValuedCompletion p K) = 0 := by
    simp [hzero]
  have hv_lam :
      Valued.v (valuedCyclotomicLambdaInteger p K : ValuedCompletion p K) =
        WithZero.exp (-1 : ℤ) :=
    valuedCyclotomicLambda_valuation (p := p) (K := K)
  rw [hv_lam] at hv_zero
  norm_num at hv_zero

/-- The lambda generator is not a unit in the valuation integer ring. -/
theorem valuedCyclotomicLambdaInteger_not_isUnit :
    ¬ IsUnit (valuedCyclotomicLambdaInteger p K) := by
  intro h
  have hv :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (K := K) (v := Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum p K)).mp h
  have hvlam :
      Valued.v (valuedCyclotomicLambdaInteger p K : ValuedCompletion p K) =
        WithZero.exp (-1 : ℤ) :=
    valuedCyclotomicLambda_valuation (p := p) (K := K)
  rw [hvlam] at hv
  norm_num at hv

theorem lambdaIdeal_ne_top : lambdaIdeal p K ≠ ⊤ := by
  intro htop
  have hunit : IsUnit (valuedCyclotomicLambdaInteger p K) := by
    rwa [lambdaIdeal, Ideal.span_singleton_eq_top] at htop
  exact valuedCyclotomicLambdaInteger_not_isUnit (p := p) (K := K) hunit

/-- The valuation-completion lambda ideal is the image of the global
cyclotomic lambda ideal. -/
theorem lambdaIdeal_eq_map_cyclotomicLambda :
    Ideal.map (algebraMap (𝓞 K) (ValuedIntegerRing p K))
        (Reflection.Local.cyclotomicLambda p K) =
      lambdaIdeal p K := by
  rw [Reflection.Local.cyclotomicLambda, zetaPrime, lambdaIdeal,
    valuedCyclotomicLambdaInteger, Furtwaengler.KummerArtinHasse.lambdaValuedPiInteger]
  rw [Ideal.map_span]
  simp [Set.image_singleton]

/-- Exact same-prime ramification in the valuation integer ring:
`(p) = lambda^(p-1)`. -/
theorem span_natCast_prime_eq_lambdaIdeal_pow_pred :
    Ideal.span ({(p : ValuedIntegerRing p K)} : Set (ValuedIntegerRing p K)) =
      (lambdaIdeal p K) ^ (p - 1) := by
  let R : Type _ := ValuedIntegerRing p K
  haveI : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) (p ^ (0 + 1)) := by
    simp
  have hfin : Module.finrank ℚ K = p - 1 := by
    rw [IsCyclotomicExtension.finrank (K := ℚ) (L := K)
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos p)),
      Nat.totient_prime (Fact.out : Nat.Prime p)]
  have hglobal :
      Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span ({(p : ℤ)} : Set ℤ)) =
        Reflection.Local.cyclotomicLambda p K ^ (p - 1) := by
    simpa [Reflection.Local.cyclotomicLambda, zetaPrime, hfin] using
      (IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow p 0 hζ)
  have hmap := congrArg (Ideal.map (algebraMap (𝓞 K) R)) hglobal
  rw [Ideal.map_map, Ideal.map_pow,
    lambdaIdeal_eq_map_cyclotomicLambda (p := p) (K := K)] at hmap
  simpa [R, Ideal.map_span] using hmap

theorem natCast_prime_mem_lambdaIdeal :
    (p : ValuedIntegerRing p K) ∈ lambdaIdeal p K := by
  have hp_pow :
      (p : ValuedIntegerRing p K) ∈ (lambdaIdeal p K) ^ (p - 1) := by
    rw [← span_natCast_prime_eq_lambdaIdeal_pow_pred (p := p) (K := K)]
    exact Ideal.mem_span_singleton_self (p : ValuedIntegerRing p K)
  exact Ideal.pow_le_self
    (Nat.sub_ne_zero_of_lt (Fact.out : Nat.Prime p).one_lt) hp_pow

/-- Natural numbers prime to `p` are units modulo the lambda ideal. -/
theorem natCast_not_mem_lambdaIdeal_of_coprime {m : ℕ} (hm : Nat.Coprime m p) :
    (m : ValuedIntegerRing p K) ∉ lambdaIdeal p K := by
  intro hmI
  rcases (Nat.Coprime.cast (R := ValuedIntegerRing p K) hm) with ⟨a, b, hbez⟩
  have h1 : (1 : ValuedIntegerRing p K) ∈ lambdaIdeal p K := by
    rw [← hbez]
    exact (lambdaIdeal p K).add_mem ((lambdaIdeal p K).mul_mem_left a hmI)
      ((lambdaIdeal p K).mul_mem_left b (natCast_prime_mem_lambdaIdeal (p := p) (K := K)))
  have htop : lambdaIdeal p K = ⊤ := (Ideal.eq_top_iff_one (lambdaIdeal p K)).mpr h1
  exact lambdaIdeal_ne_top (p := p) (K := K) htop

/-- Cancelling `p^m` against lambda-adic order leaves the predicted residual
lambda-adic order. -/
theorem lambdaIdeal_pow_mul_pred_add_eq_span_natCast_prime_pow_mul
    (m s : ℕ) :
    (lambdaIdeal p K) ^ (m * (p - 1) + s) =
      Ideal.span ({((p : ValuedIntegerRing p K) ^ m)} :
          Set (ValuedIntegerRing p K)) *
        (lambdaIdeal p K) ^ s := by
  let I : Ideal (ValuedIntegerRing p K) := lambdaIdeal p K
  calc
    I ^ (m * (p - 1) + s) = I ^ (m * (p - 1)) * I ^ s := by
      rw [pow_add]
    _ = (I ^ (p - 1)) ^ m * I ^ s := by
      rw [Nat.mul_comm m (p - 1), ← pow_mul]
    _ = (Ideal.span ({(p : ValuedIntegerRing p K)} :
          Set (ValuedIntegerRing p K))) ^ m * I ^ s := by
      rw [← span_natCast_prime_eq_lambdaIdeal_pow_pred (p := p) (K := K)]
    _ = Ideal.span ({((p : ValuedIntegerRing p K) ^ m)} :
          Set (ValuedIntegerRing p K)) * I ^ s := by
      rw [Ideal.span_singleton_pow]

/-- Lift-level same-prime denominator cancellation.  If an element has
lambda-adic order at least `m * (p - 1) + s`, then it is divisible by `p^m`
with quotient of lambda-adic order at least `s`. -/
theorem exists_natCast_prime_pow_mul_eq_of_mem_lambdaIdeal_pow_mul_pred_add
    (m s : ℕ) {x : ValuedIntegerRing p K}
    (hx : x ∈ (lambdaIdeal p K) ^ (m * (p - 1) + s)) :
    ∃ y : ValuedIntegerRing p K, y ∈ (lambdaIdeal p K) ^ s ∧
      (p : ValuedIntegerRing p K) ^ m * y = x := by
  rw [lambdaIdeal_pow_mul_pred_add_eq_span_natCast_prime_pow_mul
    (p := p) (K := K) m s] at hx
  exact Ideal.mem_span_singleton_mul.mp hx

theorem natCast_prime_pow_mem_lambdaIdeal_pow_mul_pred (m : ℕ) :
    (p : ValuedIntegerRing p K) ^ m ∈ (lambdaIdeal p K) ^ (m * (p - 1)) := by
  rw [show m * (p - 1) = m * (p - 1) + 0 by omega]
  rw [lambdaIdeal_pow_mul_pred_add_eq_span_natCast_prime_pow_mul
    (p := p) (K := K) m 0]
  have hmul := Ideal.mul_mem_mul
    (Ideal.mem_span_singleton_self ((p : ValuedIntegerRing p K) ^ m))
    (show (1 : ValuedIntegerRing p K) ∈ (lambdaIdeal p K) ^ 0 by simp)
  rwa [mul_one] at hmul

theorem natCast_prime_pow_mem_lambdaIdeal_pow {M N : ℕ}
    (hNM : N ≤ M * (p - 1)) :
    (p : ValuedIntegerRing p K) ^ M ∈ (lambdaIdeal p K) ^ N :=
  Ideal.pow_le_pow_right hNM
    (natCast_prime_pow_mem_lambdaIdeal_pow_mul_pred (p := p) (K := K) M)

theorem natCast_mem_lambdaIdeal_pow_factorization_mul_pred (c : ℕ) :
    (c : ValuedIntegerRing p K) ∈
      (lambdaIdeal p K) ^ (c.factorization p * (p - 1)) := by
  by_cases hc : c = 0
  · subst c
    simp
  · have hp : Nat.Prime p := Fact.out
    have hdvd : p ^ c.factorization p ∣ c :=
      (hp.pow_dvd_iff_le_factorization hc).2 le_rfl
    rcases hdvd with ⟨q, hq⟩
    have hmem :
        ((p ^ c.factorization p * q : ℕ) : ValuedIntegerRing p K) ∈
          (lambdaIdeal p K) ^ (c.factorization p * (p - 1)) := by
      rw [Nat.cast_mul, Nat.cast_pow]
      exact
        ((lambdaIdeal p K) ^ (c.factorization p * (p - 1))).mul_mem_right
          (q : ValuedIntegerRing p K)
          (natCast_prime_pow_mem_lambdaIdeal_pow_mul_pred
            (p := p) (K := K) (c.factorization p))
    have hcast :
        (c : ValuedIntegerRing p K) =
          ((p ^ c.factorization p * q : ℕ) : ValuedIntegerRing p K) :=
      congrArg (fun n : ℕ => (n : ValuedIntegerRing p K)) hq
    rw [hcast]
    exact hmem

theorem natCast_mul_mem_lambdaIdeal_pow_factorization_mul_pred_add
    {c e : ℕ} {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ e) :
    (c : ValuedIntegerRing p K) * z ∈
      (lambdaIdeal p K) ^ (c.factorization p * (p - 1) + e) := by
  have hc := natCast_mem_lambdaIdeal_pow_factorization_mul_pred
    (p := p) (K := K) c
  simpa [pow_add] using Ideal.mul_mem_mul hc hz

/-- Natural numbers prime to `p` are invertible in every finite
lambda-adic quotient. -/
theorem quotient_mk_natCast_isUnit_of_coprime
    (N m : ℕ) (hm : Nat.Coprime m p) :
    IsUnit
      (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (m : ValuedIntegerRing p K)) := by
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let q : R →+* R ⧸ I ^ (N + 1) := Ideal.Quotient.mk (I ^ (N + 1))
  have hcop : Nat.Coprime m (p ^ (N + 1)) := hm.pow_right (N + 1)
  rcases (Nat.Coprime.cast (R := R) hcop) with ⟨a, b, hbez⟩
  have hp_mem : ((p : R) ^ (N + 1)) ∈ I ^ (N + 1) := by
    have hp_pred : 1 ≤ p - 1 := by
      have hp_one : 1 < p := (Fact.out : Nat.Prime p).one_lt
      omega
    have hle : N + 1 ≤ (N + 1) * (p - 1) := by
      simpa [one_mul] using Nat.mul_le_mul_left (N + 1) hp_pred
    exact natCast_prime_pow_mem_lambdaIdeal_pow (p := p) (K := K) hle
  have hp_zero : q ((p : R) ^ (N + 1)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hp_mem
  have hp_zero_nat : q ((p ^ (N + 1) : ℕ) : R) = 0 := by
    rw [Nat.cast_pow]
    exact hp_zero
  have hq0 : q (a * (m : R) + b * ((p ^ (N + 1) : ℕ) : R)) = 1 := by
    rw [hbez]
    exact map_one q
  have hq : q a * q (m : R) = 1 := by
    rw [map_add, map_mul, map_mul, hp_zero_nat, mul_zero, add_zero] at hq0
    exact hq0
  refine isUnit_iff_exists.mpr ⟨q a, ?_, ?_⟩
  · rwa [mul_comm] at hq
  · exact hq

/-- A chosen inverse of the image of a natural number prime to `p` in a finite
lambda-adic quotient. -/
noncomputable def quotientNatCastInv (N m : ℕ) (hm : Nat.Coprime m p) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  Classical.choose
    (isUnit_iff_exists.mp
      (quotient_mk_natCast_isUnit_of_coprime (p := p) (K := K) N m hm))

theorem quotientNatCastInv_spec_right (N m : ℕ) (hm : Nat.Coprime m p) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (m : ValuedIntegerRing p K) *
      quotientNatCastInv (p := p) (K := K) N m hm = 1 :=
  (Classical.choose_spec
    (isUnit_iff_exists.mp
      (quotient_mk_natCast_isUnit_of_coprime (p := p) (K := K) N m hm))).1

theorem quotientNatCastInv_spec_left (N m : ℕ) (hm : Nat.Coprime m p) :
    quotientNatCastInv (p := p) (K := K) N m hm *
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (m : ValuedIntegerRing p K) = 1 :=
  (Classical.choose_spec
    (isUnit_iff_exists.mp
      (quotient_mk_natCast_isUnit_of_coprime (p := p) (K := K) N m hm))).2

theorem quotientNatCastInv_eq_of_mul_right_eq_one {N m : ℕ}
    (hm : Nat.Coprime m p)
    {u : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)}
    (hu : Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (m : ValuedIntegerRing p K) * u = 1) :
    quotientNatCastInv (p := p) (K := K) N m hm = u :=
  (quotient_mk_natCast_isUnit_of_coprime (p := p) (K := K) N m hm).mul_left_inj.mp
      (by
        rw [quotientNatCastInv_spec_left (p := p) (K := K) N m hm]
        rw [mul_comm u (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (m : ValuedIntegerRing p K)), hu])

theorem quotientNatCastInv_mul (N m n : ℕ)
    (hm : Nat.Coprime m p) (hn : Nat.Coprime n p) :
    quotientNatCastInv (p := p) (K := K) N (m * n) (hm.mul_left hn) =
      quotientNatCastInv (p := p) (K := K) N n hn *
        quotientNatCastInv (p := p) (K := K) N m hm := by
  refine quotientNatCastInv_eq_of_mul_right_eq_one
    (p := p) (K := K) (N := N) (m := m * n) (hm.mul_left hn) ?_
  rw [Nat.cast_mul, map_mul]
  calc
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (m : ValuedIntegerRing p K) *
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (n : ValuedIntegerRing p K) *
        (quotientNatCastInv (p := p) (K := K) N n hn *
          quotientNatCastInv (p := p) (K := K) N m hm)
        =
      (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (n : ValuedIntegerRing p K) *
        quotientNatCastInv (p := p) (K := K) N n hn) *
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (m : ValuedIntegerRing p K) *
        quotientNatCastInv (p := p) (K := K) N m hm) := by
          ring
    _ = 1 := by
          rw [quotientNatCastInv_spec_right (p := p) (K := K) N n hn,
            quotientNatCastInv_spec_right (p := p) (K := K) N m hm]
          simp

/-- Number of terms in the ordinary finite logarithm, with a dummy zero-th
term for range sums. -/
def samePrimeFiniteLogCutoff (N : ℕ) : ℕ :=
  p * (N + 1)

/-- Forced lambda-adic order of the ordinary logarithm term `x^n / n` when
`x` lies in the lambda ideal. -/
def samePrimeFiniteLogTermOrder (n : ℕ) : ℕ :=
  n - (p - 1) * n.factorization p

theorem one_le_samePrimeFiniteLogTermOrder {n : ℕ} (hn : n ≠ 0) :
    1 ≤ samePrimeFiniteLogTermOrder (p := p) n := by
  simpa [samePrimeFiniteLogTermOrder] using
    Nat.one_le_sub_pred_mul_factorization (ell := p) (n := n)
      (Fact.out : Nat.Prime p) hn

theorem succ_le_samePrimeFiniteLogTermOrder_of_cutoff_le {N n : ℕ}
    (hn : samePrimeFiniteLogCutoff (p := p) N ≤ n) :
    N + 1 ≤ samePrimeFiniteLogTermOrder (p := p) n := by
  simpa [samePrimeFiniteLogCutoff, samePrimeFiniteLogTermOrder] using
    Nat.succ_le_sub_pred_mul_factorization_of_mul_succ_le
      (ell := p) (N := N) (n := n) (Fact.out : Nat.Prime p) hn

theorem factorization_mul_pred_add_samePrimeFiniteLogTermOrder {n : ℕ}
    (hn : n ≠ 0) :
    n.factorization p * (p - 1) + samePrimeFiniteLogTermOrder (p := p) n = n := by
  have hle : n.factorization p * (p - 1) ≤ n := by
    have h := Nat.factorization_mul_pred_le_pred (ell := p) (n := n)
      (Fact.out : Nat.Prime p) hn
    omega
  simp [samePrimeFiniteLogTermOrder, Nat.mul_comm (p - 1) (n.factorization p),
    Nat.add_sub_cancel' hle]

theorem samePrimeFiniteLogTermData_exists {n : ℕ} (hn : n ≠ 0)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    ∃ y : ValuedIntegerRing p K,
      y ∈ (lambdaIdeal p K) ^ samePrimeFiniteLogTermOrder (p := p) n ∧
        (p : ValuedIntegerRing p K) ^ n.factorization p * y = x ^ n := by
  have hxpow : x ^ n ∈
      (lambdaIdeal p K) ^
        (n.factorization p * (p - 1) + samePrimeFiniteLogTermOrder (p := p) n) := by
    simpa [factorization_mul_pred_add_samePrimeFiniteLogTermOrder
        (p := p) hn] using
      Ideal.pow_mem_pow hx n
  exact exists_natCast_prime_pow_mul_eq_of_mem_lambdaIdeal_pow_mul_pred_add
    (p := p) (K := K) (n.factorization p)
    (samePrimeFiniteLogTermOrder (p := p) n) hxpow

/-- Chosen numerator representing `x^n / p^v_p(n)` in the same-prime local
ring. -/
noncomputable def samePrimeFiniteLogTermNumerator (n : ℕ)
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K :=
  if hn : n = 0 then 0 else
    Classical.choose
      (samePrimeFiniteLogTermData_exists (p := p) (K := K) hn hx)

theorem samePrimeFiniteLogTermNumerator_spec {n : ℕ} (hn : n ≠ 0)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTermNumerator (p := p) (K := K) n x hx ∈
        (lambdaIdeal p K) ^ samePrimeFiniteLogTermOrder (p := p) n ∧
      (p : ValuedIntegerRing p K) ^ n.factorization p *
          samePrimeFiniteLogTermNumerator (p := p) (K := K) n x hx =
        x ^ n := by
  rw [samePrimeFiniteLogTermNumerator, dif_neg hn]
  exact Classical.choose_spec
    (samePrimeFiniteLogTermData_exists (p := p) (K := K) hn hx)

theorem samePrimeFiniteLogTermNumerator_mem_lambdaIdeal_pow {n : ℕ} (hn : n ≠ 0)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTermNumerator (p := p) (K := K) n x hx ∈
      (lambdaIdeal p K) ^ samePrimeFiniteLogTermOrder (p := p) n :=
  (samePrimeFiniteLogTermNumerator_spec (p := p) (K := K) hn hx).1

theorem samePrimeFiniteLogTermNumerator_mul_spec {n : ℕ} (hn : n ≠ 0)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    (p : ValuedIntegerRing p K) ^ n.factorization p *
        samePrimeFiniteLogTermNumerator (p := p) (K := K) n x hx =
      x ^ n :=
  (samePrimeFiniteLogTermNumerator_spec (p := p) (K := K) hn hx).2

theorem samePrimeFiniteLog_ordCompl_coprime {n : ℕ} (hn : n ≠ 0) :
    Nat.Coprime (ordCompl[p] n) p :=
  ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mpr
    (Nat.not_dvd_ordCompl (Fact.out : Nat.Prime p) hn)).symm

/-- Chosen numerator representing `z / p^v_p(n)` when `z` has enough
lambda-adic order to cancel the `p`-power part of `n`. -/
noncomputable def samePrimeNatDivNumerator (n s : ℕ)
    (z : ValuedIntegerRing p K)
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    ValuedIntegerRing p K :=
  Classical.choose
    (exists_natCast_prime_pow_mul_eq_of_mem_lambdaIdeal_pow_mul_pred_add
      (p := p) (K := K) (n.factorization p) s hz)

theorem samePrimeNatDivNumerator_spec {n s : ℕ}
    {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    samePrimeNatDivNumerator (p := p) (K := K) n s z hz ∈
        (lambdaIdeal p K) ^ s ∧
      (p : ValuedIntegerRing p K) ^ n.factorization p *
          samePrimeNatDivNumerator (p := p) (K := K) n s z hz = z :=
  Classical.choose_spec
    (exists_natCast_prime_pow_mul_eq_of_mem_lambdaIdeal_pow_mul_pred_add
      (p := p) (K := K) (n.factorization p) s hz)

theorem samePrimeNatDivNumerator_mem_lambdaIdeal_pow {n s : ℕ}
    {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    samePrimeNatDivNumerator (p := p) (K := K) n s z hz ∈
      (lambdaIdeal p K) ^ s :=
  (samePrimeNatDivNumerator_spec (p := p) (K := K) hz).1

theorem samePrimeNatDivNumerator_mul_spec {n s : ℕ}
    {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    (p : ValuedIntegerRing p K) ^ n.factorization p *
        samePrimeNatDivNumerator (p := p) (K := K) n s z hz = z :=
  (samePrimeNatDivNumerator_spec (p := p) (K := K) hz).2


end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end
