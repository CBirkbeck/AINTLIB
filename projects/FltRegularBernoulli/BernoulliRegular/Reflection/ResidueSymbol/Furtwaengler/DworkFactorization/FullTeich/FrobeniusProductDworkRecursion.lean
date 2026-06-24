module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Concrete
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FullTeich.FullTeichDworkSetup

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

/-- Dwork recursion after collapsing the ordinary-exponential correction
product to the single trace-sum correction factor. -/
theorem artinHasseExp_frobenius_product_pow_prime_eq_trace_sum_mul_parameter_pow
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
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (δ * ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            zbar ^ (ℓ ^ (i : ℕ))) *
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
  have hrec :=
    F.artinHasseExp_trunc_eval_frobenius_product_pow_prime_eq_correction_mul_parameter_pow N y
  have hcorr :=
    F.artinHasseExp_trunc_eval_frobenius_correction_product_eq_trace_sum N y
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ
        =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (δ * zbar ^ (ℓ ^ (i : ℕ)))) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          simpa [A, Eps, Ips, Rps, πbar, δ, zbar] using hrec
    _ =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (δ * ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                zbar ^ (ℓ ^ (i : ℕ))) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          rw [hcorr]

/-- Parameter-general Frobenius-shift reindexing. This is the same orbit
calculation as `artinHasseExp_trunc_eval_frobenius_shift_product`, but with
an arbitrary quotient parameter `ε`; it is needed to iterate the Dwork
recursion at `δ^ℓ`, `δ^(ℓ^2)`, and later powers. -/
theorem artinHasseExp_trunc_eval_frobenius_shift_product_of_parameter
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε * zbar ^ (ℓ ^ (i : ℕ))) ^ ℓ)) =
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
  let z : 𝓞 R' := F.teichUnitFullVal (F.traceScale * y)
  let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) z
  let f : ℕ := F.toConcreteStickelbergerSetup.f
  let g : ℕ → A := fun i =>
    (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
      (ε ^ ℓ * zbar ^ (ℓ ^ i))
  have hzperiod : zbar ^ (ℓ ^ f) = zbar := by
    have hcard : z ^ Fintype.card k = z := by
      have hcard_pos : 0 < Fintype.card k := Fintype.card_pos
      rw [show Fintype.card k = (Fintype.card k - 1) + 1 by
        exact (Nat.sub_add_cancel (Nat.succ_le_of_lt hcard_pos)).symm]
      rw [pow_succ]
      have hunit := F.teichUnitFullVal_pow_card_sub_one (F.traceScale * y)
      simpa [z] using congrArg (fun a : 𝓞 R' => a * z) hunit
    have hz : z ^ (ℓ ^ f) = z := by
      rw [← F.toConcreteStickelbergerSetup.card_k_eq]
      exact hcard
    simpa [zbar, map_pow] using congrArg (Ideal.Quotient.mk (F.Q ^ (N + 1))) hz
  have hgperiod : g f = g 0 := by
    simp [g, hzperiod]
  have hleft :
      (∏ i : Fin f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε * zbar ^ (ℓ ^ (i : ℕ))) ^ ℓ)) =
        ∏ i ∈ Finset.range f, g (i + 1) := by
    calc
      (∏ i : Fin f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε * zbar ^ (ℓ ^ (i : ℕ))) ^ ℓ))
          = ∏ i ∈ Finset.range f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                ((ε * zbar ^ (ℓ ^ i)) ^ ℓ) :=
              (Finset.prod_range
                (f := fun i : ℕ =>
                  (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                    ((ε * zbar ^ (ℓ ^ i)) ^ ℓ))).symm
      _ = ∏ i ∈ Finset.range f, g (i + 1) := by
              refine Finset.prod_congr rfl ?_
              intro i _hi
              have hpow : (zbar ^ (ℓ ^ i)) ^ ℓ = zbar ^ (ℓ ^ (i + 1)) := by
                rw [← pow_mul, ← pow_succ]
              rw [mul_pow, hpow]
  have hright :
      (∏ i : Fin f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ)))) =
        ∏ i ∈ Finset.range f, g i :=
    (Finset.prod_range (f := g)).symm
  rw [show F.toConcreteStickelbergerSetup.f = f from rfl]
  rw [hleft, hright]
  exact prod_range_shift_eq_of_last_eq_first g f hgperiod

/-- Iterated Frobenius-shift reindexing. After `m` Dwork-recursion steps,
the shifted Frobenius orbit can still be reindexed back to the original
orbit, with the parameter changed from `ε` to `ε^(ℓ^m)`. -/
theorem artinHasseExp_trunc_eval_frobenius_shift_product_iterate_of_parameter
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((ε * zbar ^ (ℓ ^ (i : ℕ))) ^ (ℓ ^ m))) =
      ∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let z : 𝓞 R' := F.teichUnitFullVal (F.traceScale * y)
  let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) z
  let f : ℕ := F.toConcreteStickelbergerSetup.f
  let g : ℕ → A := fun n =>
    (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
      (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ n))
  have hzperiod : zbar ^ (ℓ ^ f) = zbar := by
    have hcard : z ^ Fintype.card k = z := by
      have hcard_pos : 0 < Fintype.card k := Fintype.card_pos
      rw [show Fintype.card k = (Fintype.card k - 1) + 1 by
        exact (Nat.sub_add_cancel (Nat.succ_le_of_lt hcard_pos)).symm]
      rw [pow_succ]
      have hunit := F.teichUnitFullVal_pow_card_sub_one (F.traceScale * y)
      simpa [z] using congrArg (fun a : 𝓞 R' => a * z) hunit
    have hz : z ^ (ℓ ^ f) = z := by
      rw [← F.toConcreteStickelbergerSetup.card_k_eq]
      exact hcard
    simpa [zbar, map_pow] using congrArg (Ideal.Quotient.mk (F.Q ^ (N + 1))) hz
  have hzperiod_iter : ∀ n : ℕ, zbar ^ (ℓ ^ (n + f)) = zbar ^ (ℓ ^ n) := by
    intro n
    rw [show ℓ ^ (n + f) = ℓ ^ f * ℓ ^ n by rw [pow_add, Nat.mul_comm], pow_mul,
      hzperiod]
  have hgperiod : ∀ n : ℕ, g (n + f) = g n := by
    intro n
    simp [g, hzperiod_iter n]
  have hleft :
      (∏ i : Fin f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε * zbar ^ (ℓ ^ (i : ℕ))) ^ (ℓ ^ m))) =
        ∏ i ∈ Finset.range f, g (i + m) := by
    calc
      (∏ i : Fin f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((ε * zbar ^ (ℓ ^ (i : ℕ))) ^ (ℓ ^ m)))
          = ∏ i ∈ Finset.range f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                ((ε * zbar ^ (ℓ ^ i)) ^ (ℓ ^ m)) :=
              (Finset.prod_range
                (f := fun i : ℕ =>
                  (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                    ((ε * zbar ^ (ℓ ^ i)) ^ (ℓ ^ m)))).symm
      _ = ∏ i ∈ Finset.range f, g (i + m) := by
              refine Finset.prod_congr rfl ?_
              intro i _hi
              have hpow :
                  (zbar ^ (ℓ ^ i)) ^ (ℓ ^ m) = zbar ^ (ℓ ^ (i + m)) := by
                rw [← pow_mul, ← pow_add]
              rw [mul_pow, hpow]
  have hright :
      (∏ i : Fin f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ (i : ℕ)))) =
        ∏ i ∈ Finset.range f, g i :=
    (Finset.prod_range (f := g)).symm
  rw [show F.toConcreteStickelbergerSetup.f = f from rfl]
  rw [hleft, hright]
  exact prod_range_shift_iterate_eq_of_period g f m hgperiod

/-- The finite correction accumulated by iterating the Dwork recursion for
the whole Frobenius theta product. -/
noncomputable def artinHasseExpFrobeniusProductIterCorrection
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (m : ℕ) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  ∏ i : Fin F.toConcreteStickelbergerSetup.f,
    F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N
      (ε * zbar ^ (ℓ ^ (i : ℕ))) m

/-- Iterated finite Dwork recursion for the complete Frobenius theta product:
after `m` recursion steps, the product at `ε` is related to the product at
`ε^(ℓ^m)` by an explicit accumulated correction. -/
theorem artinHasseExp_frobenius_product_pow_prime_iterate_eq_iterCorrection_mul
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) =
      F.artinHasseExpFrobeniusProductIterCorrection N y ε m *
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' :=
    F.toConcreteStickelbergerSetup
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  have hshift :=
    F.artinHasseExp_trunc_eval_frobenius_shift_product_iterate_of_parameter
      N m y ε
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m)
        =
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) := by
          rw [Finset.prod_pow]
    _ =
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (S0.artinHasseExpIterCorrection N
                (ε * zbar ^ (ℓ ^ (i : ℕ))) m *
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                ((ε * zbar ^ (ℓ ^ (i : ℕ))) ^ (ℓ ^ m))) := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          have hzi :
              (ε * zbar ^ (ℓ ^ (i : ℕ))) ^ (N + 1) = 0 := by
            rw [mul_pow, hε, zero_mul]
          simpa [S0, A, Eps] using
            S0.artinHasseExp_trunc_eval_pow_prime_iterate_eq_iterCorrection_mul
              (N := N) (m := m) (z := ε * zbar ^ (ℓ ^ (i : ℕ))) hzi
    _ =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
            S0.artinHasseExpIterCorrection N
              (ε * zbar ^ (ℓ ^ (i : ℕ))) m) *
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              ((ε * zbar ^ (ℓ ^ (i : ℕ))) ^ (ℓ ^ m)) := by
          rw [Finset.prod_mul_distrib]
    _ =
          F.artinHasseExpFrobeniusProductIterCorrection N y ε m *
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ (i : ℕ))) := by
          rw [hshift]
          rfl

/-- Parameter-general clean Dwork recursion for the Frobenius theta product:
`P(ε)^ℓ = C(ε) * P(ε^ℓ)` for any nilpotent quotient parameter `ε`. -/
theorem artinHasseExp_frobenius_product_pow_prime_eq_correction_mul_of_parameter
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
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ =
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' :=
    F.toConcreteStickelbergerSetup
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
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ
        =
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ := by rw [Finset.prod_pow]
    _ =
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (ε * zbar ^ (ℓ ^ (i : ℕ))) *
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                ((ε * zbar ^ (ℓ ^ (i : ℕ))) ^ ℓ)) := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          have hz :
              (ε * zbar ^ (ℓ ^ (i : ℕ))) ^ (N + 1) = 0 := by
            rw [mul_pow, hε, zero_mul]
          simpa [A, Eps, Rps] using
            S0.artinHasseExp_trunc_eval_pow_prime_eq_rescale_exp_trunc_eval_mul_frob
              (N := N) (z := ε * zbar ^ (ℓ ^ (i : ℕ))) hz
    _ =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                ((ε * zbar ^ (ℓ ^ (i : ℕ))) ^ ℓ) := by
          rw [Finset.prod_mul_distrib]
    _ =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          rw [F.artinHasseExp_trunc_eval_frobenius_shift_product_of_parameter N y ε]

/-- Parameter-general collapse of the ordinary-exponential correction product
to the correction at the finite Frobenius trace sum. -/
theorem artinHasseExp_trunc_eval_frobenius_correction_product_eq_trace_sum_of_parameter
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (ε * ∑ i : Fin F.toConcreteStickelbergerSetup.f,
          zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  have hprod :=
    rescale_exp_trunc_eval₂_finset_prod_eq_sum
      (r := ℓ)
      (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      (N := N)
      (δ := ε)
      hε
      (s := (Finset.univ : Finset (Fin F.toConcreteStickelbergerSetup.f)))
      (u := fun i : Fin F.toConcreteStickelbergerSetup.f => zbar ^ (ℓ ^ (i : ℕ)))
  simpa [A, Rps, zbar] using hprod

/-- Parameter-general Dwork recursion after collapsing the correction product
to the trace-sum correction factor. -/
theorem artinHasseExp_frobenius_product_pow_prime_eq_trace_sum_mul_parameter_pow_of_parameter
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
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (ε * ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            zbar ^ (ℓ ^ (i : ℕ))) *
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
  have hrec :=
    F.artinHasseExp_frobenius_product_pow_prime_eq_correction_mul_of_parameter
      N y ε hε
  have hcorr :=
    F.artinHasseExp_trunc_eval_frobenius_correction_product_eq_trace_sum_of_parameter
      N y ε hε
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ
        =
          (∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (ε * zbar ^ (ℓ ^ (i : ℕ)))) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          simpa [A, Eps, Rps, zbar] using hrec
    _ =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (ε * ∑ i : Fin F.toConcreteStickelbergerSetup.f,
                zbar ^ (ℓ ^ (i : ℕ))) *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          rw [hcorr]

/-- The ordinary trace-lift correction factor is the corresponding power of
the base correction factor. -/
theorem artinHasseExp_trace_nat_correction_eq_base_correction_pow
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
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (t : A)) =
      ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) δ) ^ t := by
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
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  simpa [A, Ips, Rps, πbar, δ, t] using
    rescale_exp_trunc_eval₂_natCast_mul_eq_pow
      (r := ℓ)
      (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      (N := N)
      (δ := δ)
      hδ
      t

/-- The normalized base value `E(δ)^trace` satisfies the same formal Dwork
recursion, with the correction factor at the ordinary trace lift. -/
theorem artinHasseExp_base_trace_pow_prime_eq_trace_nat_correction_mul_parameter_pow
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
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) δ) ^ t) ^ ℓ =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (t : A)) *
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (δ ^ ℓ)) ^ t := by
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
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hbase :
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) δ) ^ ℓ =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) δ *
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (δ ^ ℓ) := by
    have h :=
      ConcreteStickelbergerSetup.artinHasseExp_trunc_eval_inverse_mul_pow_prime_eq_rescale_exp_mul_frob
        (S := F.toConcreteStickelbergerSetup)
        (N := N)
        (u := (1 : A))
    simpa [A, Eps, Ips, Rps, πbar, δ] using h
  have hcorr :=
    F.artinHasseExp_trace_nat_correction_eq_base_correction_pow N y
  calc
    (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) δ) ^ t) ^ ℓ
        = (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) δ) ^ ℓ) ^ t := by
          rw [pow_right_comm]
    _ =
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) δ *
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (δ ^ ℓ)) ^ t := by
          rw [hbase]
    _ =
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) δ) ^ t *
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (δ ^ ℓ)) ^ t := by
          rw [mul_pow]
    _ =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (t : A)) *
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (δ ^ ℓ)) ^ t := by
          rw [hcorr]

/-- Parameter-general ordinary trace-lift correction: the correction at
`ε * t` is the `t`-th power of the correction at `ε`. -/
theorem artinHasseExp_trace_nat_correction_eq_base_correction_pow_of_parameter
    (N : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) =
      ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) ε) ^ t := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  simpa [A, Rps, t] using
    rescale_exp_trunc_eval₂_natCast_mul_eq_pow
      (r := ℓ)
      (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      (N := N)
      (δ := ε)
      hε
      t

/-- Parameter-general base recursion: the normalized base value satisfies the
same formal Dwork recursion at any nilpotent quotient parameter `ε`. -/
theorem artinHasseExp_base_trace_pow_prime_eq_trace_nat_correction_mul_parameter_pow_of_parameter
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
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^ ℓ =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε ^ ℓ)) ^ t := by
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
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' := F.toConcreteStickelbergerSetup
  have hbase :
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ ℓ =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) ε *
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε ^ ℓ) := by
    simpa [A, Eps, Rps] using
      S0.artinHasseExp_trunc_eval_pow_prime_eq_rescale_exp_trunc_eval_mul_frob
          (N := N) (z := ε) hε
  have hcorr :=
    F.artinHasseExp_trace_nat_correction_eq_base_correction_pow_of_parameter
      N y ε hε
  calc
    (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^ ℓ
        = (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ ℓ) ^ t := by
          rw [pow_right_comm]
    _ =
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) ε *
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε ^ ℓ)) ^ t := by
          rw [hbase]
    _ =
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) ε) ^ t *
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε ^ ℓ)) ^ t := by
          rw [mul_pow]
    _ =
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (ε * (t : A)) *
          ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε ^ ℓ)) ^ t := by
          rw [hcorr]

/-- Iterated finite Dwork recursion for the normalized base side
`E(ε)^trace`. -/
theorem artinHasseExp_base_trace_pow_prime_iterate_eq_iterCorrection_mul
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^ (ℓ ^ m) =
      (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^ t *
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε ^ (ℓ ^ m))) ^ t := by
  classical
  dsimp only
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' := F.toConcreteStickelbergerSetup
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hiter :=
    S0.artinHasseExp_trunc_eval_pow_prime_iterate_eq_iterCorrection_mul
      (N := N) (m := m) (z := ε) hε
  calc
    (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^ (ℓ ^ m)
        =
          (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^
            (ℓ ^ m)) ^ t := by
          rw [pow_right_comm]
    _ =
          (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m *
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m))) ^ t := by
          rw [hiter]
    _ =
          (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^ t *
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m))) ^ t := by
          rw [mul_pow]

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
