module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Concrete
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FullTeich.Part2

/-!
# Full Teichmuller Dwork product setup

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

/-- The product-side correction at the Teichmüller Frobenius trace sum and
the correction at the remaining trace carry multiply to the base-side
ordinary trace-lift correction. -/
theorem artinHasseExp_trace_sum_correction_mul_trace_carry_eq_trace_nat_correction
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
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
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (δ * ∑ i : Fin F.toConcreteStickelbergerSetup.f,
          zbar ^ (ℓ ^ (i : ℕ))) *
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (δ * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (t : A)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
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
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  simpa [A, Ips, Rps, πbar, δ, zbar, t] using
    rescale_exp_trunc_eval₂_mul_sub
      (r := ℓ)
      (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      (N := N)
      (δ := δ)
      (x := ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))
      (y := (t : A))
      hδ

/-- Parameter-general trace-carry correction identity: the product-side
trace-sum correction and the carry correction multiply to the ordinary
trace-lift correction at any nilpotent quotient parameter `ε`. -/
theorem artinHasseExp_trace_sum_correction_mul_trace_carry_eq_trace_nat_correction_of_parameter
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ∑ i : Fin F.toConcreteStickelbergerSetup.f,
          zbar ^ (ℓ ^ (i : ℕ))) *
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  simpa [A, Rps, zbar, t] using
    rescale_exp_trunc_eval₂_mul_sub
      (r := ℓ)
      (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      (N := N)
      (δ := ε)
      (x := ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))
      (y := (t : A))
      hε

/-- Product recursion with the trace carry correction moved explicitly onto
the left side. This is the exact obstruction form of the remaining
Witt/Artin-Hasse trace comparison. -/
theorem artinHasseExp_product_pow_prime_mul_trace_carry_eq_trace_recursion
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
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
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (δ * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (t : A)) *
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
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
  have hprod :=
    F.artinHasseExp_frobenius_product_pow_prime_eq_trace_sum_mul_parameter_pow N y
  have hcarry :=
    F.artinHasseExp_trace_sum_correction_mul_trace_carry_eq_trace_nat_correction N y
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (δ * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))))
        =
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (δ * ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                zbar ^ (ℓ ^ (i : ℕ))) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ ^ ℓ * zbar ^ (ℓ ^ (i : ℕ)))) *
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (δ * ((t : A) -
                ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) := by
          rw [hprod]
    _ =
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (δ * ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                zbar ^ (ℓ ^ (i : ℕ))) *
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (δ * ((t : A) -
                ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))))) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          ring
    _ =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (t : A)) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          rw [hcarry]

/-- Parameter-general product recursion with the trace-carry correction moved
onto the left side. This is the uniform recursion needed for iteration along
`ε`, `ε^ℓ`, `ε^(ℓ^2)`, ... . -/
theorem artinHasseExp_product_pow_prime_mul_trace_carry_eq_trace_recursion_of_parameter
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
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
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
    F.artinHasseExp_frobenius_product_pow_prime_eq_trace_sum_mul_parameter_pow_of_parameter
      N y ε hε
  have hcarry :=
    F.artinHasseExp_trace_sum_correction_mul_trace_carry_eq_trace_nat_correction_of_parameter
      N y ε hε
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ((t : A) -
          ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))))
        =
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε * ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                zbar ^ (ℓ ^ (i : ℕ))) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ)))) *
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε * ((t : A) -
                ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ)))) := by
          rw [hprod]
    _ =
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε * ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                zbar ^ (ℓ ^ (i : ℕ))) *
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε * ((t : A) -
                ∑ i : Fin F.toConcreteStickelbergerSetup.f, zbar ^ (ℓ ^ (i : ℕ))))) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          ring
    _ =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          rw [hcarry]

/-- The second-order Teichmüller-side expansion obtained from the
precision-2 Artin-Hasse theta product.  This is the expression that must be
compared with `psiTraceBinomialApprox F 2 y` to finish the `N = 2` Dwork
splitting check. -/
noncomputable def artinHasseSecondOrderTeichExpansion (γ : 𝓞 R') (y : kˣ) :
    𝓞 R' :=
  let u : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
    (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  let a : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i => F.π * u i
  let b : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
    (γ - F.π) * u i + dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup γ 2 2 *
      u i ^ 2
  1 + (∑ i : Fin F.toConcreteStickelbergerSetup.f, a i) +
    (∑ i : Fin F.toConcreteStickelbergerSetup.f, b i) +
    ∑ i : Fin F.toConcreteStickelbergerSetup.f,
      a i * ∑ j ∈ Finset.univ.filter (fun j => j < i), a j

/-- The second-order Teichmüller-side expansion in collected linear,
quadratic, and pair-sum form. -/
theorem artinHasseSecondOrderTeichExpansion_eq_collected
    (γ : 𝓞 R') (y : kˣ) :
    let u : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
      (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
    let c₂ : 𝓞 R' :=
      dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup γ 2 2
    artinHasseSecondOrderTeichExpansion F γ y =
      1 + F.π * (∑ i : Fin F.toConcreteStickelbergerSetup.f, u i) +
        ((γ - F.π) * (∑ i : Fin F.toConcreteStickelbergerSetup.f, u i) +
          c₂ * (∑ i : Fin F.toConcreteStickelbergerSetup.f, u i ^ 2)) +
        F.π ^ 2 *
          ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            u i * ∑ j ∈ Finset.univ.filter (fun j => j < i), u j := by
  classical
  let u : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
    (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  let c₂ : 𝓞 R' :=
    dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup γ 2 2
  change artinHasseSecondOrderTeichExpansion F γ y =
    1 + F.π * (∑ i : Fin F.toConcreteStickelbergerSetup.f, u i) +
      ((γ - F.π) * (∑ i : Fin F.toConcreteStickelbergerSetup.f, u i) +
        c₂ * (∑ i : Fin F.toConcreteStickelbergerSetup.f, u i ^ 2)) +
      F.π ^ 2 *
        ∑ i : Fin F.toConcreteStickelbergerSetup.f,
          u i * ∑ j ∈ Finset.univ.filter (fun j => j < i), u j
  have hquad :
      (∑ i : Fin F.toConcreteStickelbergerSetup.f,
          ((γ - F.π) * u i + c₂ * u i ^ 2)) =
        (γ - F.π) * (∑ i : Fin F.toConcreteStickelbergerSetup.f, u i) +
          c₂ * (∑ i : Fin F.toConcreteStickelbergerSetup.f, u i ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hlinear :
      (∑ i : Fin F.toConcreteStickelbergerSetup.f, F.π * u i) =
        F.π * (∑ i : Fin F.toConcreteStickelbergerSetup.f, u i) := by
    rw [Finset.mul_sum]
  have hpair :
      (∑ i : Fin F.toConcreteStickelbergerSetup.f,
          (F.π * u i) *
            ∑ j ∈ Finset.univ.filter (fun j : Fin F.toConcreteStickelbergerSetup.f => j < i),
              F.π * u j) =
        F.π ^ 2 *
          ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            u i *
              ∑ j ∈ Finset.univ.filter
                (fun j : Fin F.toConcreteStickelbergerSetup.f => j < i), u j := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  dsimp [artinHasseSecondOrderTeichExpansion]
  rw [hlinear, hquad, hpair]

/-- The finite Artin-Hasse theta product equals the expected `multiIndexLE`
sum modulo `Q^(N+1)`. -/
theorem artinHasseThetaTruncProduct_sub_multiIndexSum_mem_Q_pow_succ
    (N : ℕ) (y : kˣ) :
    artinHasseThetaTruncProduct F N y -
        (∑ m ∈ Furtwaengler.multiIndexLE F.toConcreteStickelbergerSetup.f N,
          dworkMultiIndexTerm ℓ
            (dworkCoeffArtinHasse F.toConcreteStickelbergerSetup)
            (F.teichUnitFullVal (F.traceScale * y)) m) ∈ F.Q ^ (N + 1) := by
  simpa [artinHasseThetaTruncProduct, artinHasseDworkMultiIndexSum,
    dworkMultiIndexTerm] using
    dworkThetaFrobeniusProduct_sub_multiIndexLESum_mem_I_pow_succ
      (I := F.Q) ℓ F.toConcreteStickelbergerSetup.f N
      (dworkCoeffArtinHasse F.toConcreteStickelbergerSetup)
      (F.teichUnitFullVal (F.traceScale * y))
      (fun n => dworkCoeffArtinHasse_mem_Q_pow F.toConcreteStickelbergerSetup n)

/-- The finite parameterized Artin-Hasse theta product equals the expected
`multiIndexLE` sum modulo `Q^(N+1)` when `γ ∈ Q`. -/
theorem artinHasseThetaTruncProductAt_sub_multiIndexSumAt_mem_Q_pow_succ
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (N : ℕ) (y : kˣ) :
    artinHasseThetaTruncProductAt F γ N y -
        (∑ m ∈ Furtwaengler.multiIndexLE F.toConcreteStickelbergerSetup.f N,
          dworkMultiIndexTerm ℓ
            (dworkCoeffArtinHasseAt F.toConcreteStickelbergerSetup γ)
            (F.teichUnitFullVal (F.traceScale * y)) m) ∈ F.Q ^ (N + 1) := by
  simpa [artinHasseThetaTruncProductAt, artinHasseDworkMultiIndexSumAt,
    dworkMultiIndexTerm] using
    dworkThetaFrobeniusProduct_sub_multiIndexLESum_mem_I_pow_succ
      (I := F.Q) ℓ F.toConcreteStickelbergerSetup.f N
      (dworkCoeffArtinHasseAt F.toConcreteStickelbergerSetup γ)
      (F.teichUnitFullVal (F.traceScale * y))
      (fun n => dworkCoeffArtinHasseAt_mem_Q_pow F.toConcreteStickelbergerSetup hγ n)

/-- The precision-indexed finite Artin-Hasse theta product equals the
corresponding `multiIndexLE` sum modulo `Q^(N+1)` when `γ ∈ Q`. -/
theorem artinHasseThetaTruncProductAtTo_sub_multiIndexSumAtTo_mem_Q_pow_succ
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (N : ℕ) (y : kˣ) :
    artinHasseThetaTruncProductAtTo F γ N y -
        (∑ m ∈ Furtwaengler.multiIndexLE F.toConcreteStickelbergerSetup.f N,
          dworkMultiIndexTerm ℓ
            (dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup γ N)
            (F.teichUnitFullVal (F.traceScale * y)) m) ∈ F.Q ^ (N + 1) := by
  simpa [artinHasseThetaTruncProductAtTo, artinHasseDworkMultiIndexSumAtTo,
    dworkMultiIndexTerm] using
    dworkThetaFrobeniusProduct_sub_multiIndexLESum_mem_I_pow_succ
      (I := F.Q) ℓ F.toConcreteStickelbergerSetup.f N
      (dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup γ N)
      (F.teichUnitFullVal (F.traceScale * y))
      (fun n => dworkCoeffArtinHasseAtTo_mem_Q_pow F.toConcreteStickelbergerSetup hγ N n)

/-- Final algebraic bridge: a theta-product splitting congruence implies the
same congruence for the `multiIndexLE` sum used by `FullTeichDworkSetup`. -/
theorem psiInt_sub_artinHasseDworkMultiIndexSum_mem_Q_pow_succ_of_theta
    (N : ℕ) (y : kˣ)
    (htheta :
      F.psiInt (y : k) - artinHasseThetaTruncProduct F N y ∈ F.Q ^ (N + 1)) :
    F.psiInt (y : k) - artinHasseDworkMultiIndexSum F N y ∈ F.Q ^ (N + 1) :=
  sub_mem_trans (F.Q ^ (N + 1)) htheta
    (by
      simpa [artinHasseDworkMultiIndexSum] using
        F.artinHasseThetaTruncProduct_sub_multiIndexSum_mem_Q_pow_succ N y)

/-- Parameterized final algebraic bridge: a theta-product splitting congruence
for `E_ℓ(γT)` implies the corresponding `multiIndexLE` congruence. -/
theorem psiInt_sub_artinHasseDworkMultiIndexSumAt_mem_Q_pow_succ_of_theta
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (N : ℕ) (y : kˣ)
    (htheta :
      F.psiInt (y : k) - artinHasseThetaTruncProductAt F γ N y ∈ F.Q ^ (N + 1)) :
    F.psiInt (y : k) - artinHasseDworkMultiIndexSumAt F γ N y ∈ F.Q ^ (N + 1) :=
  sub_mem_trans (F.Q ^ (N + 1)) htheta
    (by
      simpa [artinHasseDworkMultiIndexSumAt] using
        F.artinHasseThetaTruncProductAt_sub_multiIndexSumAt_mem_Q_pow_succ hγ N y)

/-- Precision-indexed final algebraic bridge: a theta-product splitting
congruence for the `N`-precision coefficient representatives implies the
corresponding `multiIndexLE` congruence. -/
theorem psiInt_sub_artinHasseDworkMultiIndexSumAtTo_mem_Q_pow_succ_of_theta
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (N : ℕ) (y : kˣ)
    (htheta :
      F.psiInt (y : k) - artinHasseThetaTruncProductAtTo F γ N y ∈ F.Q ^ (N + 1)) :
    F.psiInt (y : k) - artinHasseDworkMultiIndexSumAtTo F γ N y ∈
      F.Q ^ (N + 1) :=
  sub_mem_trans (F.Q ^ (N + 1)) htheta
    (by
      simpa [artinHasseDworkMultiIndexSumAtTo] using
        F.artinHasseThetaTruncProductAtTo_sub_multiIndexSumAtTo_mem_Q_pow_succ hγ N y)

/-- Construct `FullTeichDworkSetup` from the unparameterized Artin-Hasse
coefficient sequence once the Dwork factorization congruence has been
supplied. The two coefficient hypotheses are discharged by `ArtinHasse.lean`;
the caller supplies the genuine factorization theorem from REF-18tf3c. -/
noncomputable def toFullTeichDworkArtinHasse
    (hpsi : ∀ (N : ℕ) (y : kˣ),
      F.psiInt (y : k) - artinHasseDworkMultiIndexSum F N y ∈ F.Q ^ (N + 1)) :
    FullTeichDworkSetup ℓ p k K R' where
  toFullTeichStickelbergerSetup := F
  dworkCoeff := fun _N n => dworkCoeffArtinHasse F.toConcreteStickelbergerSetup n
  dworkCoeff_mem_Q_pow :=
    fun _N n => dworkCoeffArtinHasse_mem_Q_pow F.toConcreteStickelbergerSetup n
  dworkCoeff_lt_ell_leading :=
    fun _N n _hnN hn =>
      dworkCoeffArtinHasse_lt_ell_leading F.toConcreteStickelbergerSetup n hn
  psi_dwork_factorization := by
    intro N y
    simpa [artinHasseDworkMultiIndexSum, dworkMultiIndexTerm, teichUnitFullVal] using hpsi N y

/-- Constructor variant where the remaining unparameterized splitting input
is stated at the theta-product level rather than the expanded multi-index
level. -/
noncomputable def toFullTeichDworkArtinHasseOfTheta
    (htheta : ∀ (N : ℕ) (y : kˣ),
      F.psiInt (y : k) - artinHasseThetaTruncProduct F N y ∈ F.Q ^ (N + 1)) :
    FullTeichDworkSetup ℓ p k K R' :=
  F.toFullTeichDworkArtinHasse
    (fun N y =>
      F.psiInt_sub_artinHasseDworkMultiIndexSum_mem_Q_pow_succ_of_theta
        N y (htheta N y))

/-- Construct `FullTeichDworkSetup` from the corrected parameterized
Artin-Hasse coefficients once the parameter `γ` and the all-order Dwork
splitting congruence have been supplied.  The valuation and leading-term
fields are discharged by `ArtinHasse.lean`; only the genuine splitting theorem
remains as input. -/
noncomputable def toFullTeichDworkSetupArtinHasseAt
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (hγπ : γ - F.π ∈ F.Q ^ 2)
    (hpsi : ∀ (N : ℕ) (y : kˣ),
      F.psiInt (y : k) - artinHasseDworkMultiIndexSumAt F γ N y ∈ F.Q ^ (N + 1)) :
    FullTeichDworkSetup ℓ p k K R' where
  toFullTeichStickelbergerSetup := F
  dworkCoeff := fun _N n => dworkCoeffArtinHasseAt F.toConcreteStickelbergerSetup γ n
  dworkCoeff_mem_Q_pow :=
    fun _N n => dworkCoeffArtinHasseAt_mem_Q_pow F.toConcreteStickelbergerSetup hγ n
  dworkCoeff_lt_ell_leading :=
    fun _N n _hnN hn =>
      dworkCoeffArtinHasseAt_lt_ell_leading F.toConcreteStickelbergerSetup hγ hγπ n hn
  psi_dwork_factorization := by
    intro N y
    simpa [artinHasseDworkMultiIndexSumAt, dworkMultiIndexTerm, teichUnitFullVal] using hpsi N y

/-- Constructor variant where the remaining splitting input is stated at the
theta-product level rather than the expanded multi-index level. -/
noncomputable def toFullTeichDworkSetupArtinHasseAtOfTheta
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (hγπ : γ - F.π ∈ F.Q ^ 2)
    (htheta : ∀ (N : ℕ) (y : kˣ),
      F.psiInt (y : k) - artinHasseThetaTruncProductAt F γ N y ∈ F.Q ^ (N + 1)) :
    FullTeichDworkSetup ℓ p k K R' :=
  F.toFullTeichDworkSetupArtinHasseAt hγ hγπ
    (fun N y => F.psiInt_sub_artinHasseDworkMultiIndexSumAt_mem_Q_pow_succ_of_theta
      hγ N y (htheta N y))

/-- Construct `FullTeichDworkSetup` from a precision-indexed family of
Artin-Hasse parameters `γ_N`.  This is the shape needed for the finite
inverse-series construction: the parameter and coefficient representatives
are both allowed to depend on the target precision `N`. -/
noncomputable def toFullTeichDworkSetupArtinHasseAtTo
    (γ : ℕ → 𝓞 R') (hγ : ∀ N : ℕ, γ N ∈ F.Q)
    (hγπ : ∀ N : ℕ, 0 < N → γ N - F.π ∈ F.Q ^ 2)
    (hpsi : ∀ (N : ℕ) (y : kˣ),
      F.psiInt (y : k) - artinHasseDworkMultiIndexSumAtTo F (γ N) N y ∈
        F.Q ^ (N + 1)) :
    FullTeichDworkSetup ℓ p k K R' where
  toFullTeichStickelbergerSetup := F
  dworkCoeff := fun N n =>
    dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup (γ N) N n
  dworkCoeff_mem_Q_pow := fun N n =>
    dworkCoeffArtinHasseAtTo_mem_Q_pow F.toConcreteStickelbergerSetup (hγ N) N n
  dworkCoeff_lt_ell_leading := by
    intro N n hnN hn
    by_cases hN : N = 0
    · subst N
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hnN
      subst n
      simp [dworkCoeffArtinHasseAtTo]
    · exact
        dworkCoeffArtinHasseAtTo_lt_ell_leading F.toConcreteStickelbergerSetup
          (hγ N) (hγπ N (Nat.pos_of_ne_zero hN)) N n hnN hn
  psi_dwork_factorization := by
    intro N y
    simpa [artinHasseDworkMultiIndexSumAtTo, dworkMultiIndexTerm, teichUnitFullVal] using hpsi N y

/-- Constructor variant where the precision-indexed splitting input is stated
at the theta-product level. -/
noncomputable def toFullTeichDworkSetupArtinHasseAtToOfTheta
    (γ : ℕ → 𝓞 R') (hγ : ∀ N : ℕ, γ N ∈ F.Q)
    (hγπ : ∀ N : ℕ, 0 < N → γ N - F.π ∈ F.Q ^ 2)
    (htheta : ∀ (N : ℕ) (y : kˣ),
      F.psiInt (y : k) - artinHasseThetaTruncProductAtTo F (γ N) N y ∈
        F.Q ^ (N + 1)) :
    FullTeichDworkSetup ℓ p k K R' :=
  F.toFullTeichDworkSetupArtinHasseAtTo γ hγ hγπ
    (fun N y =>
      F.psiInt_sub_artinHasseDworkMultiIndexSumAtTo_mem_Q_pow_succ_of_theta
        (hγ N) N y (htheta N y))

/-- The concrete precision-indexed Artin-Hasse setup constructor.  The only
remaining input is the all-order Dwork splitting congruence for the finite
inverse-series parameter
`artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N`. -/
noncomputable def toFullTeichDworkSetupArtinHasseApproxTo
    (hpsi : ∀ (N : ℕ) (y : kˣ),
      F.psiInt (y : k) -
          artinHasseDworkMultiIndexSumAtTo F
            (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y ∈
        F.Q ^ (N + 1)) :
    FullTeichDworkSetup ℓ p k K R' :=
  F.toFullTeichDworkSetupArtinHasseAtTo
    (fun N => artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
    (fun N => artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N)
    (fun _N hN =>
      artinHasseDworkParameterApproxTo_sub_pi_mem_Q_sq_of_pos
        F.toConcreteStickelbergerSetup hN)
    hpsi

/-- Concrete constructor variant where the remaining all-order splitting input
is stated at the theta-product level. -/
noncomputable def toFullTeichDworkSetupArtinHasseApproxToOfTheta
    (htheta : ∀ (N : ℕ) (y : kˣ),
      F.psiInt (y : k) -
          artinHasseThetaTruncProductAtTo F
            (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y ∈
        F.Q ^ (N + 1)) :
    FullTeichDworkSetup ℓ p k K R' :=
  F.toFullTeichDworkSetupArtinHasseAtToOfTheta
    (fun N => artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
    (fun N => artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N)
    (fun _N hN =>
      artinHasseDworkParameterApproxTo_sub_pi_mem_Q_sq_of_pos
        F.toConcreteStickelbergerSetup hN)
    htheta

/-- Algebraic reduction of the Dwork splitting congruence to one-variable
factor congruences. The remaining hard input is to provide the target factors
and prove the two hypotheses in the concrete Artin-Hasse situation. -/
theorem psiInt_sub_artinHasseThetaTruncProduct_mem_Q_pow_succ_of_factor_congruence
    (N : ℕ) (y : kˣ)
    (target : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R')
    (hpsi :
      F.psiInt (y : k) - (∏ i : Fin F.toConcreteStickelbergerSetup.f, target i) ∈
        F.Q ^ (N + 1))
    (hfactor :
      ∀ i : Fin F.toConcreteStickelbergerSetup.f,
        target i - artinHasseThetaFactor F N y i ∈ F.Q ^ (N + 1)) :
    F.psiInt (y : k) - artinHasseThetaTruncProduct F N y ∈ F.Q ^ (N + 1) := by
  have hprod :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f, target i) -
          artinHasseThetaTruncProduct F N y ∈ F.Q ^ (N + 1) := by
    rw [artinHasseThetaTruncProduct_eq_prod_factor]
    exact fin_prod_sub_prod_mem_pow (I := F.Q)
      target (fun i => artinHasseThetaFactor F N y i) (N + 1) hfactor
  exact sub_mem_trans (F.Q ^ (N + 1)) hpsi hprod

/-- Precision-indexed algebraic reduction of the Dwork splitting congruence to
one-variable factor congruences. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_mem_Q_pow_succ_of_factor_congruence
    {γ : 𝓞 R'} (N : ℕ) (y : kˣ)
    (target : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R')
    (hpsi :
      F.psiInt (y : k) - (∏ i : Fin F.toConcreteStickelbergerSetup.f, target i) ∈
        F.Q ^ (N + 1))
    (hfactor :
      ∀ i : Fin F.toConcreteStickelbergerSetup.f,
        target i - artinHasseThetaFactorAtTo F γ N y i ∈ F.Q ^ (N + 1)) :
    F.psiInt (y : k) - artinHasseThetaTruncProductAtTo F γ N y ∈ F.Q ^ (N + 1) := by
  have hprod :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f, target i) -
          artinHasseThetaTruncProductAtTo F γ N y ∈ F.Q ^ (N + 1) := by
    simpa [artinHasseThetaTruncProductAtTo, artinHasseThetaFactorAtTo,
      dworkThetaFrobeniusProduct] using
      fin_prod_sub_prod_mem_pow (I := F.Q)
        target (fun i => artinHasseThetaFactorAtTo F γ N y i) (N + 1) hfactor
  exact sub_mem_trans (F.Q ^ (N + 1)) hpsi hprod

/-- The first theta product is linear modulo `Q^2`: the only surviving
degree-one contribution is `π` times the sum of Teichmüller Frobenius
conjugates. -/
theorem artinHasseThetaTruncProduct_one_sub_linearTeichSum_mem_Q_sq (y : kˣ) :
    artinHasseThetaTruncProduct F 1 y -
        (1 + F.π *
          ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈
      F.Q ^ 2 := by
  rw [artinHasseThetaTruncProduct_eq_prod_factor]
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' :=
    F.toConcreteStickelbergerSetup
  let u : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
    (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hfactor :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f, artinHasseThetaFactor F 1 y i) -
          (∏ i : Fin F.toConcreteStickelbergerSetup.f, (1 + F.π * u i)) ∈
        F.Q ^ 2 :=
    fin_prod_sub_prod_mem_pow (I := F.Q)
      (fun i : Fin F.toConcreteStickelbergerSetup.f => artinHasseThetaFactor F 1 y i)
      (fun i : Fin F.toConcreteStickelbergerSetup.f => (1 + F.π * u i)) 2
      (fun i =>
        by
          have hi :=
            S0.dworkThetaTrunc_artinHasse_one_sub_one_add_pi_mul_mem_Q_sq (u i)
          simpa [artinHasseThetaFactor, u, S0] using
            hi)
  have hlinear :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f, (1 + F.π * u i)) -
          (1 + F.π * ∑ i : Fin F.toConcreteStickelbergerSetup.f, u i) ∈ F.Q ^ 2 :=
    fin_prod_one_add_mul_sub_one_add_mul_sum_mem_pow_two
      (I := F.Q) F.π_mem_Q u
  simpa [u] using sub_mem_trans (F.Q ^ 2) hfactor hlinear

/-- Parameterized first theta product linearization modulo `Q^2`. -/
theorem artinHasseThetaTruncProductAt_one_sub_linearTeichSum_mem_Q_sq
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (hγπ : γ - F.π ∈ F.Q ^ 2) (y : kˣ) :
    artinHasseThetaTruncProductAt F γ 1 y -
        (1 + F.π *
          ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈
      F.Q ^ 2 := by
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' :=
    F.toConcreteStickelbergerSetup
  let u : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
    (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hfactor :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f, artinHasseThetaFactorAt F γ 1 y i) -
          (∏ i : Fin F.toConcreteStickelbergerSetup.f, (1 + F.π * u i)) ∈
        F.Q ^ 2 :=
    fin_prod_sub_prod_mem_pow (I := F.Q)
      (fun i : Fin F.toConcreteStickelbergerSetup.f => artinHasseThetaFactorAt F γ 1 y i)
      (fun i : Fin F.toConcreteStickelbergerSetup.f => (1 + F.π * u i)) 2
      (fun i =>
        by
          have hi :=
            S0.dworkThetaTrunc_artinHasseAt_one_sub_one_add_pi_mul_mem_Q_sq
              hγ hγπ (u i)
          simpa [artinHasseThetaFactorAt, u, S0] using hi)
  have hlinear :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f, (1 + F.π * u i)) -
          (1 + F.π * ∑ i : Fin F.toConcreteStickelbergerSetup.f, u i) ∈ F.Q ^ 2 :=
    fin_prod_one_add_mul_sub_one_add_mul_sum_mem_pow_two
      (I := F.Q) F.π_mem_Q u
  simpa [artinHasseThetaTruncProductAt, artinHasseThetaFactorAt,
    dworkThetaFrobeniusProduct, u] using
    sub_mem_trans (F.Q ^ 2) hfactor hlinear

/-- Precision-indexed parameterized first theta product linearization modulo
`Q^2`. -/
theorem artinHasseThetaTruncProductAtTo_one_sub_linearTeichSum_mem_Q_sq
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (hγπ : γ - F.π ∈ F.Q ^ 2) (y : kˣ) :
    artinHasseThetaTruncProductAtTo F γ 1 y -
        (1 + F.π *
          ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈
      F.Q ^ 2 := by
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' :=
    F.toConcreteStickelbergerSetup
  let u : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
    (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hfactor :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f, artinHasseThetaFactorAtTo F γ 1 y i) -
          (∏ i : Fin F.toConcreteStickelbergerSetup.f, (1 + F.π * u i)) ∈
        F.Q ^ 2 :=
    fin_prod_sub_prod_mem_pow (I := F.Q)
      (fun i : Fin F.toConcreteStickelbergerSetup.f => artinHasseThetaFactorAtTo F γ 1 y i)
      (fun i : Fin F.toConcreteStickelbergerSetup.f => (1 + F.π * u i)) 2
      (fun i =>
        by
          have hi :=
            S0.dworkThetaTrunc_artinHasseAtTo_one_sub_one_add_pi_mul_mem_Q_sq
              hγ hγπ (u i)
          simpa [artinHasseThetaFactorAtTo, u, S0] using hi)
  have hlinear :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f, (1 + F.π * u i)) -
          (1 + F.π * ∑ i : Fin F.toConcreteStickelbergerSetup.f, u i) ∈ F.Q ^ 2 :=
    fin_prod_one_add_mul_sub_one_add_mul_sum_mem_pow_two
      (I := F.Q) F.π_mem_Q u
  simpa [artinHasseThetaTruncProductAtTo, artinHasseThetaFactorAtTo,
    dworkThetaFrobeniusProduct, u] using
    sub_mem_trans (F.Q ^ 2) hfactor hlinear

/-- Any positive precision-indexed parameterized theta product has the same
first-order reduction modulo `Q^2`. -/
theorem artinHasseThetaTruncProductAtTo_sub_linearTeichSum_mem_Q_sq_of_one_le
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (hγπ : γ - F.π ∈ F.Q ^ 2)
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    artinHasseThetaTruncProductAtTo F γ N y -
        (1 + F.π *
          ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))) ∈
      F.Q ^ 2 := by
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' :=
    F.toConcreteStickelbergerSetup
  let u : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
    (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hfactor :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f, artinHasseThetaFactorAtTo F γ N y i) -
          (∏ i : Fin F.toConcreteStickelbergerSetup.f, (1 + F.π * u i)) ∈
        F.Q ^ 2 :=
    fin_prod_sub_prod_mem_pow (I := F.Q)
      (fun i : Fin F.toConcreteStickelbergerSetup.f => artinHasseThetaFactorAtTo F γ N y i)
      (fun i : Fin F.toConcreteStickelbergerSetup.f => (1 + F.π * u i)) 2
      (fun i =>
        by
          have hi :=
            S0.dworkThetaTrunc_artinHasseAtTo_sub_one_add_pi_mul_mem_Q_sq_of_one_le
              hγ hγπ hN (u i)
          simpa [artinHasseThetaFactorAtTo, u, S0] using hi)
  have hlinear :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f, (1 + F.π * u i)) -
          (1 + F.π * ∑ i : Fin F.toConcreteStickelbergerSetup.f, u i) ∈ F.Q ^ 2 :=
    fin_prod_one_add_mul_sub_one_add_mul_sum_mem_pow_two
      (I := F.Q) F.π_mem_Q u
  simpa [artinHasseThetaTruncProductAtTo, artinHasseThetaFactorAtTo,
    dworkThetaFrobeniusProduct, u] using
    sub_mem_trans (F.Q ^ 2) hfactor hlinear

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
