module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FullTeich
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.WittCarry.Part2

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

/-- Fully expanded adjusted-product recursion: the correction multiplying
the Frobenius theta product is the finite product over Teichmüller
coordinates of the Witt carry. -/
theorem exists_adjusted_product_teichmuller_series_pow_prime_eq_trace_recursion
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : WittVector ℓ k,
      ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ * zbar ^ (ℓ ^ (i : ℕ)))) *
        ∏ j ∈ Finset.Iic N,
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (δ * ((ℓ : A) ^ j *
              θ (WittVector.teichmuller ℓ
                (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j)))))) ^ ℓ =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (t : A)) *
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (δ ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
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
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
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
        (δ * ((ℓ : A) ^ j * coord j))
  have hcarry :
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) =
        (ℓ : A) * carryBase := by
    simpa [A, θ, zbar, t, coord, carryBase] using hc
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  have hcorrection :
      correction =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (δ * carryBase) := by
    have hprod :=
      rescale_exp_trunc_eval₂_finset_prod_eq_sum
        (r := ℓ)
        (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
        (N := N)
        (δ := δ)
        hδ
        (s := Finset.Iic N)
        (u := fun j => (ℓ : A) ^ j * coord j)
    simpa [A, Ips, Rps, πbar, δ, coord, carryBase, correction] using hprod
  have hcorrection_pow :
      correction ^ ℓ =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (δ * ((t : A) -
            ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) := by
    calc
      correction ^ ℓ =
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (δ * carryBase)) ^ ℓ := by
          rw [hcorrection]
      _ =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (δ * ((ℓ : A) * carryBase)) := by
          rw [rescale_exp_trunc_eval₂_mul_natCast_mul_eq_pow
            (r := ℓ)
            (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
            (N := N)
            (δ := δ)
            hδ
            (x := carryBase)
            (t := ℓ)]
      _ =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (δ * ((t : A) -
              ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) := by
          rw [hcarry]
  have hrec := F.artinHasseExp_product_pow_prime_mul_trace_carry_eq_trace_recursion N y
  refine ⟨c, ?_⟩
  calc
    ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) *
      ∏ j ∈ Finset.Iic N,
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (δ * ((ℓ : A) ^ j *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ j) (c.coeff j)))))) ^ ℓ
      =
        (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ * correction ^ ℓ := by
        simp [correction, coord, mul_pow]
    _ =
        (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (δ * ((t : A) -
              ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) := by
        rw [hcorrection_pow]
    _ =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (t : A)) *
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (δ ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
        simpa [A, Eps, Ips, Rps, πbar, δ, zbar, t] using hrec

/-- The ordinary correction factor at the explicit trace carry is an
`ℓ`-th power of a correction factor attached to a Witt carry. -/
theorem exists_traceCarry_correction_eq_pow_wittTheta
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : WittVector ℓ k,
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (δ * ((t : A) -
            ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) =
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * θ c)) ^ ℓ := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  obtain ⟨c, hc⟩ :=
    F.exists_traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta N y
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  refine ⟨c, ?_⟩
  calc
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (δ * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))))
        =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (δ * ((ℓ : A) * θ c)) := by
          rw [hc]
    _ =
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * θ c)) ^ ℓ := by
          simpa [A, θ, Ips, Rps, πbar, δ, zbar, t] using
            rescale_exp_trunc_eval₂_mul_natCast_mul_eq_pow
              (r := ℓ)
              (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
              (N := N)
              (δ := δ)
              hδ
              (x := θ c)
              (t := ℓ)

/-- After multiplying the Frobenius theta product by the Witt-carry
correction, the product recursion has the same correction factor as the base
trace recursion. -/
theorem exists_adjusted_product_pow_prime_eq_trace_recursion
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : WittVector ℓ k,
      ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ * zbar ^ (ℓ ^ (i : ℕ)))) *
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * θ c)) ^ ℓ =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (t : A)) *
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (δ ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  obtain ⟨c, hc⟩ := F.exists_traceCarry_correction_eq_pow_wittTheta N y
  have hrec := F.artinHasseExp_product_pow_prime_mul_trace_carry_eq_trace_recursion N y
  refine ⟨c, ?_⟩
  calc
    ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) *
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * θ c)) ^ ℓ
        =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * θ c)) ^ ℓ := by
          rw [mul_pow]
    _ =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (δ * ((t : A) -
                ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) := by
          rw [← hc]
    _ =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (t : A)) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          rw [hrec]

/-- Parameter-general version of `exists_traceCarry_correction_eq_pow_wittTheta`:
the trace-carry correction at any nilpotent quotient parameter is an
`ℓ`-th power of a correction factor attached to a Witt carry. -/
theorem exists_traceCarry_correction_eq_pow_wittTheta_of_parameter
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
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * θ c)) ^ ℓ := by
  classical
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
    F.exists_traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta N y
  refine ⟨c, ?_⟩
  calc
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))))
        =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε * ((ℓ : A) * θ c)) := by
          rw [hc]
    _ =
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * θ c)) ^ ℓ := by
          simpa [A, θ, Rps, zbar, t] using
            rescale_exp_trunc_eval₂_mul_natCast_mul_eq_pow
              (r := ℓ)
              (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
              (N := N)
              (δ := ε)
              hε
              (x := θ c)
              (t := ℓ)

/-- Parameter-general adjusted product recursion: after multiplying the
Frobenius theta product at `ε` by the Witt-carry correction, its `ℓ`-th
power has the same trace correction as the base recursion and advances the
parameter to `ε^ℓ`. -/
theorem exists_adjusted_product_pow_prime_eq_trace_recursion_of_parameter
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
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * θ c)) ^ ℓ =
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
  obtain ⟨c, hc⟩ :=
    F.exists_traceCarry_correction_eq_pow_wittTheta_of_parameter N y ε hε
  have hrec :=
    F.artinHasseExp_product_pow_prime_mul_trace_carry_eq_trace_recursion_of_parameter
      N y ε hε
  refine ⟨c, ?_⟩
  calc
    ((∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * θ c)) ^ ℓ
        =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * θ c)) ^ ℓ := by
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

/-- Non-existential version of
`exists_traceCarry_correction_eq_pow_wittTheta_of_parameter`: the fixed
Witt carry `traceCarry` supplies the correction root at every nilpotent
parameter. -/
theorem traceCarry_correction_eq_pow_wittTheta_of_parameter
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
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) =
      ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * θ (F.traceCarry y))) ^ ℓ := by
  classical
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
  have hcarry :=
    F.traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta_traceCarry
      N y
  calc
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))))
        =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε * ((ℓ : A) * θ (F.traceCarry y))) := by
          rw [hcarry]
    _ =
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε * θ (F.traceCarry y))) ^ ℓ := by
          simpa [A, θ, Rps, zbar, t] using
            rescale_exp_trunc_eval₂_mul_natCast_mul_eq_pow
              (r := ℓ)
              (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
              (N := N)
              (δ := ε)
              hε
              (x := θ (F.traceCarry y))
              (t := ℓ)

/-- Parameter-general finite Teichmüller-coordinate factor-power expansion of
the fixed trace-carry correction.  Unlike the existential coordinate expansion,
this uses the actual carry vector `traceCarry y`, so the downstream
prime-field coordinate rewrites apply deterministically. -/
theorem traceCarry_correction_eq_teichmuller_series_product_powers_traceCarry_of_parameter
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
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) =
      ∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                ((F.traceCarry y).coeff r))))) ^ (ℓ ^ (r + 1)) := by
  classical
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
  let coord : ℕ → A := fun r =>
    θ (WittVector.teichmuller ℓ
      (((_root_.frobeniusEquiv k ℓ).symm ^ r) ((F.traceCarry y).coeff r)))
  let u : ℕ → A := fun r => (ℓ : A) ^ (r + 1) * coord r
  have hseries :
      θ (F.traceCarry y) =
        ∑ r ∈ Finset.Iic N, (ℓ : A) ^ r * coord r := by
    simpa [A, θ, coord] using
      F.toConcreteStickelbergerSetup.wittThetaModQPow_eq_sum_teichmuller_series
        N (F.traceCarry y)
  have hdiff :
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) =
        (ℓ : A) * θ (F.traceCarry y) := by
    simpa [A, θ, zbar, t] using
      F.traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul_wittTheta_traceCarry
        N y
  have hsum :
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))) =
        ∑ r ∈ Finset.Iic N, u r := by
    calc
      (t : A) -
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))
          = (ℓ : A) * θ (F.traceCarry y) := hdiff
      _ =
          (ℓ : A) *
            ∑ r ∈ Finset.Iic N, (ℓ : A) ^ r * coord r := by
          rw [hseries]
      _ = ∑ r ∈ Finset.Iic N, u r := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro r _hr
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
  calc
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))))
        =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε * ∑ r ∈ Finset.Iic N, u r) := by
          rw [hsum]
    _ =
          ∏ r ∈ Finset.Iic N,
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε * u r) := by
          simpa [A, Rps] using hprod.symm
    _ =
          ∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε * coord r)) ^ (ℓ ^ (r + 1)) := by
          refine Finset.prod_congr rfl ?_
          intro r _hr
          simpa [A, θ, Rps, zbar, t, coord, u, mul_assoc, mul_left_comm,
            mul_comm] using
            (rescale_exp_trunc_eval₂_mul_natCast_mul_eq_pow
              (r := ℓ)
              (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
              (N := N)
              (δ := ε)
              hε
              (x := coord r)
              (t := ℓ ^ (r + 1)))

/-- Prime-field-coordinate form of
`traceCarry_correction_eq_teichmuller_series_product_powers_traceCarry_of_parameter`.
Each trace-carry coordinate is rewritten using the chosen `ZMod ℓ`
representative. -/
theorem traceCarry_correction_eq_zmod_product_powers_of_parameter
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
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) =
      ∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r))))) ^
          (ℓ ^ (r + 1)) := by
  classical
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
  calc
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))))
        =
          ∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                    ((F.traceCarry y).coeff r))))) ^ (ℓ ^ (r + 1)) := by
          simpa [A, θ, Rps, zbar, t] using
            F.traceCarry_correction_eq_teichmuller_series_product_powers_traceCarry_of_parameter
              N y ε hε
    _ =
          ∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε *
                θ (WittVector.teichmuller ℓ
                  (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r))))) ^
              (ℓ ^ (r + 1)) := by
          simpa [A, θ, Rps, zbar, t] using
            F.rescaleExp_traceCarry_coord_product_eq_zmod
              N N ε y (fun r => ℓ ^ (r + 1))

/-- Parameter-general finite Teichmüller-coordinate factor-power expansion of
the ordinary correction at the fixed trace carry itself. -/
theorem traceCarry_wittTheta_correction_eq_teichmuller_series_product_powers_of_parameter
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * θ (F.traceCarry y)) =
      ∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                ((F.traceCarry y).coeff r))))) ^ (ℓ ^ r) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let coord : ℕ → A := fun r =>
    θ (WittVector.teichmuller ℓ
      (((_root_.frobeniusEquiv k ℓ).symm ^ r) ((F.traceCarry y).coeff r)))
  let u : ℕ → A := fun r => (ℓ : A) ^ r * coord r
  have hseries :
      θ (F.traceCarry y) = ∑ r ∈ Finset.Iic N, u r := by
    simpa [A, θ, coord, u] using
      F.toConcreteStickelbergerSetup.wittThetaModQPow_eq_sum_teichmuller_series
        N (F.traceCarry y)
  have hprod :=
    rescale_exp_trunc_eval₂_finset_prod_eq_sum
      (r := ℓ)
      (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      (N := N)
      (δ := ε)
      hε
      (s := Finset.Iic N)
      (u := u)
  calc
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * θ (F.traceCarry y))
        =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε * ∑ r ∈ Finset.Iic N, u r) := by
          rw [hseries]
    _ =
          ∏ r ∈ Finset.Iic N,
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε * u r) := by
          simpa [A, Rps] using hprod.symm
    _ =
          ∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε * coord r)) ^ (ℓ ^ r) := by
          refine Finset.prod_congr rfl ?_
          intro r _hr
          simpa [A, θ, Rps, coord, u, mul_assoc, mul_left_comm, mul_comm] using
            (rescale_exp_trunc_eval₂_mul_natCast_mul_eq_pow
              (r := ℓ)
              (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
              (N := N)
              (δ := ε)
              hε
              (x := coord r)
              (t := ℓ ^ r))

/-- Prime-field-coordinate form of
`traceCarry_wittTheta_correction_eq_teichmuller_series_product_powers_of_parameter`. -/
theorem traceCarry_wittTheta_correction_eq_zmod_product_powers_of_parameter
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * θ (F.traceCarry y)) =
      ∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r))))) ^
          (ℓ ^ r) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  calc
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * θ (F.traceCarry y))
        =
          ∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε *
                θ (WittVector.teichmuller ℓ
                  (((_root_.frobeniusEquiv k ℓ).symm ^ r)
                    ((F.traceCarry y).coeff r))))) ^ (ℓ ^ r) := by
          simpa [A, θ, Rps] using
            F.traceCarry_wittTheta_correction_eq_teichmuller_series_product_powers_of_parameter
              N y ε hε
    _ =
          ∏ r ∈ Finset.Iic N,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε *
                θ (WittVector.teichmuller ℓ
                  (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r))))) ^
              (ℓ ^ r) := by
          simpa [A, θ, Rps] using
            F.rescaleExp_traceCarry_coord_product_eq_zmod
              N N ε y (fun r => ℓ ^ r)

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
