module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FullTeich
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.WittCarry.AdjustedProductRecursion

/-!
# Witt carry comparison for Dwork factorization

Split from `DworkFactorization.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (F : FullTeichStickelbergerSetup ℓ p k K R')

/-- Non-existential parameter-general adjusted product recursion using the
fixed Witt carry `traceCarry`. -/
theorem adjusted_product_pow_prime_eq_trace_recursion_traceCarry_of_parameter
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * θ (F.traceCarry y))) ^ ℓ =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hc :=
    F.traceCarry_correction_eq_pow_wittTheta_of_parameter N y ε hε
  have hrec :=
    F.artinHasseExp_product_pow_prime_mul_trace_carry_eq_trace_recursion_of_parameter
      N y ε hε
  calc
    ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * θ (F.traceCarry y))) ^ ℓ
        =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε * θ (F.traceCarry y))) ^ ℓ := by
          rw [mul_pow]
    _ =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε * ((t : A) -
                ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) := by
          rw [← hc]
    _ =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          rw [hrec]

/-- Fixed-carry finite-coordinate form of the adjusted product recursion.  This
is the non-existential analogue of the older adjusted-product expansion: the
ordinary correction factor is replaced by the explicit product attached to
`traceCarry y`. -/
theorem adjusted_product_teichmuller_series_pow_prime_eq_trace_recursion_traceCarry_of_parameter
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
      ∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                ((F.traceCarry y).coeff r))))) ^ (ℓ ^ r)) ^ ℓ =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hcorr :=
    F.traceCarry_wittTheta_correction_eq_teichmuller_series_product_powers_of_parameter
      N y ε hε
  have hrec :=
    F.adjusted_product_pow_prime_eq_trace_recursion_traceCarry_of_parameter
      N y ε hε
  calc
    ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
      ∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                ((F.traceCarry y).coeff r))))) ^ (ℓ ^ r)) ^ ℓ
        =
          ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε * θ (F.traceCarry y))) ^ ℓ := by
          rw [← hcorr]
    _ =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
        simpa [A, θ, Eps, Rps, zbar, t] using hrec

/-- Prime-field-coordinate form of
`adjusted_product_teichmuller_series_pow_prime_eq_trace_recursion_traceCarry_of_parameter`. -/
theorem adjusted_product_zmod_series_pow_prime_eq_trace_recursion_of_parameter
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
      ∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r))))) ^
          (ℓ ^ r)) ^ ℓ =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hcorr :=
    F.traceCarry_wittTheta_correction_eq_zmod_product_powers_of_parameter
      N y ε hε
  have hrec :=
    F.adjusted_product_pow_prime_eq_trace_recursion_traceCarry_of_parameter
      N y ε hε
  calc
    ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
      ∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r))))) ^
          (ℓ ^ r)) ^ ℓ
        =
          ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε * θ (F.traceCarry y))) ^ ℓ := by
          rw [← hcorr]
    _ =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
        simpa [A, θ, Eps, Rps, zbar, t] using hrec

/-- Power-normalized prime-field-coordinate form of the adjusted product
recursion.  This exposes the carry-coordinate exponents as `ℓ^(r+1)`, which
is the shape needed by the subsequent root-of-unity cancellation step. -/
theorem adjusted_product_pow_prime_mul_zmod_product_eq_trace_recursion_of_parameter
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
      (∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r))))) ^
          (ℓ ^ (r + 1))) =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hrec :=
    F.adjusted_product_zmod_series_pow_prime_eq_trace_recursion_of_parameter
      N y ε hε
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
      (∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r))))) ^
          (ℓ ^ (r + 1)))
        =
          ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
            ∏ r ∈ Finset.Iic N,
              ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (ε *
                  θ (WittVector.teichmuller ℓ
                    (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r))))) ^
                (ℓ ^ r)) ^ ℓ := by
          rw [mul_pow]
          congr 1
          rw [← Finset.prod_pow]
          refine Finset.prod_congr rfl ?_
          intro r _hr
          rw [← pow_mul, Nat.pow_succ]
    _ =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
        simpa [A, θ, Eps, Rps, zbar, t] using hrec

/-- Parameter-general finite Teichmüller-coordinate expansion of the
trace-carry correction. -/
theorem exists_traceCarry_correction_eq_teichmuller_series_product_of_parameter
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : WittVector ℓ k,
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε * ((t : A) -
            ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) =
        ∏ j ∈ Finset.Iic N,
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε * ((ℓ : A) ^ (j + 1) *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))))) := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  obtain ⟨c, hc⟩ :=
    F.exists_traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta_series N y
  let u : ℕ → A := fun j =>
    (ℓ : A) ^ (j + 1) *
      θ (WittVector.teichmuller ℓ
        (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j)))
  have hsum :
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) =
        ∑ j ∈ Finset.Iic N, u j := by
    calc
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))
          =
            (ℓ : A) *
              ∑ j ∈ Finset.Iic N,
                (ℓ : A) ^ j *
                  θ (WittVector.teichmuller ℓ
                    (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))) := hc
      _ =
            ∑ j ∈ Finset.Iic N, u j := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j _hj
              simp [u, pow_succ]
              ring
  have hprod :=
    rescale_exp_trunc_eval₂_finset_prod_eq_sum
      (r := ℓ)
      (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      (N := N)
      (δ := ε)
      hε
      (s := Finset.Iic N)
      (u := u)
  refine ⟨c, ?_⟩
  rw [hsum]
  simpa [A, θ, Rps, zbar, t, u] using hprod.symm

/-- Parameter-general power-normalized finite Teichmüller-coordinate
expansion of the trace-carry correction. -/
theorem exists_traceCarry_correction_eq_teichmuller_series_product_powers_of_parameter
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : WittVector ℓ k,
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε * ((t : A) -
            ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) =
        ∏ j ∈ Finset.Iic N,
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))))) ^
            (ℓ ^ (j + 1)) := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  obtain ⟨c, hc⟩ :=
    F.exists_traceCarry_correction_eq_teichmuller_series_product_of_parameter
      N y ε hε
  refine ⟨c, ?_⟩
  calc
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))))
        =
          ∏ j ∈ Finset.Iic N,
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε * ((ℓ : A) ^ (j + 1) *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))))) := hc
    _ =
          ∏ j ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))))) ^
              (ℓ ^ (j + 1)) := by
          refine Finset.prod_congr rfl ?_
          intro j _hj
          simpa [A, θ, Rps, zbar, t, mul_assoc, mul_left_comm, mul_comm] using
            (rescale_exp_trunc_eval₂_mul_natCast_mul_eq_pow
              (r := ℓ)
              (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
              (N := N)
              (δ := ε)
              hε
              (x := θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j))))
              (t := ℓ ^ (j + 1)))

/-- Parameter-general fully expanded adjusted-product recursion. -/
theorem exists_adjusted_product_teichmuller_series_pow_prime_eq_trace_recursion_of_parameter
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : WittVector ℓ k,
      ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
        ∏ j ∈ Finset.Iic N,
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε * ((ℓ : A) ^ j *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j)))))) ^ ℓ =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  obtain ⟨c, hc⟩ :=
    F.exists_traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta_series N y
  let coord : ℕ → A := fun j =>
    θ (WittVector.teichmuller ℓ
      (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j)))
  let carryBase : A := ∑ j ∈ Finset.Iic N, (ℓ : A) ^ j * coord j
  let correction : A :=
    ∏ j ∈ Finset.Iic N,
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ((ℓ : A) ^ j * coord j))
  have hcarry :
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) =
        (ℓ : A) * carryBase := by
    simpa [A, θ, zbar, t, coord, carryBase] using hc
  have hcorrection :
      correction =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε * carryBase) := by
    have hprod :=
      rescale_exp_trunc_eval₂_finset_prod_eq_sum
        (r := ℓ)
        (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
        (N := N)
        (δ := ε)
        hε
        (s := Finset.Iic N)
        (u := fun j => (ℓ : A) ^ j * coord j)
    simpa [A, θ, Rps, coord, carryBase, correction] using hprod
  have hcorrection_pow :
      correction ^ ℓ =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε * ((t : A) -
            ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) := by
    calc
      correction ^ ℓ =
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε * carryBase)) ^ ℓ := by
          rw [hcorrection]
      _ =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε * ((ℓ : A) * carryBase)) := by
          rw [rescale_exp_trunc_eval₂_mul_natCast_mul_eq_pow
            (r := ℓ)
            (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
            (N := N)
            (δ := ε)
            hε
            (x := carryBase)
            (t := ℓ)]
      _ =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε * ((t : A) -
              ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) := by
          rw [hcarry]
  have hrec :=
    F.artinHasseExp_product_pow_prime_mul_trace_carry_eq_trace_recursion_of_parameter
      N y ε hε
  refine ⟨c, ?_⟩
  calc
    ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
      ∏ j ∈ Finset.Iic N,
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε * ((ℓ : A) ^ j *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j)))))) ^ ℓ
      =
        (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ * correction ^ ℓ := by
        simp [correction, coord, mul_pow]
    _ =
        (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε * ((t : A) -
              ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) := by
        rw [hcorrection_pow]
    _ =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
        simpa [A, Eps, Rps, zbar, t] using hrec

/-- Cancellation-free comparison between the product recursion and the base
recursion at an arbitrary nilpotent quotient parameter. The trace-carry
factor is kept explicitly on the product side, so no unit or division
assumption is needed. -/
theorem artinHasseExp_product_carry_mul_base_next_eq_base_pow_mul_product_next_of_parameter
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))))) *
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε ^ ℓ)) ^ t =
      (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^ ℓ *
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hprod :=
    F.artinHasseExp_product_pow_prime_mul_trace_carry_eq_trace_recursion_of_parameter
      N y ε hε
  have hbase :=
    F.artinHasseExp_base_trace_pow_prime_eq_trace_nat_correction_mul_parameter_pow_of_parameter
      N y ε hε
  calc
    ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))))) *
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε ^ ℓ)) ^ t
        =
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ)))) *
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε ^ ℓ)) ^ t := by
          rw [hprod]
    _ =
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε ^ ℓ)) ^ t) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          ring
    _ =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^ ℓ *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          rw [← hbase]

/-- Cancellation-free comparison in adjusted-product form. After absorbing
the carry as a Witt correction, the adjusted product at `ε` and the base
value at `ε` have matching `ℓ`-power recursions against the next parameter
`ε^ℓ`. -/
theorem exists_adjusted_product_pow_prime_mul_base_next_eq_base_pow_mul_product_next_of_parameter
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : WittVector ℓ k,
      ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * θ c)) ^ ℓ *
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε ^ ℓ)) ^ t =
      (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^ ℓ *
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  obtain ⟨c, hadj⟩ :=
    F.exists_adjusted_product_pow_prime_eq_trace_recursion_of_parameter N y ε hε
  have hbase :=
    F.artinHasseExp_base_trace_pow_prime_eq_trace_nat_correction_mul_parameter_pow_of_parameter
      N y ε hε
  refine ⟨c, ?_⟩
  calc
    ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * θ c)) ^ ℓ *
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε ^ ℓ)) ^ t
        =
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ)))) *
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε ^ ℓ)) ^ t := by
          rw [hadj]
    _ =
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε ^ ℓ)) ^ t) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          ring
    _ =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^ ℓ *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          rw [← hbase]


end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
