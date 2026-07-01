module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Concrete

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

/-- The binomial truncation of the additive character
`ψ(y) = (1 + π) ^ Tr(traceScale * y)`, through `Q`-adic order `N`. -/
noncomputable def psiTraceBinomialApprox (N : ℕ) (y : kˣ) : 𝓞 R' :=
  ∑ n ∈ Finset.range (N + 1),
    F.π ^ n *
      (Nat.choose
        (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val n : 𝓞 R')

/-- Exact quotient normal form for the trace-form additive character. -/
theorem quotient_mk_psiInt_eq_one_add_pi_pow_trace (N : ℕ) (y : kˣ) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.psiInt (y : k)) =
      (1 + Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π) ^
        (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val := by
  let t : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hpsi :
      F.psiInt (y : k) = F.zeta_ell_int ^ t := by
    simpa [t] using
      F.toTraceFormStickelbergerSetup.psiInt_eq_zeta_ell_int_pow_trace (y : k)
  have hzeta : F.zeta_ell_int = 1 + F.π := by
    rw [F.hπ]
    ring
  calc
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.psiInt (y : k))
        = Ideal.Quotient.mk (F.Q ^ (N + 1)) ((1 + F.π) ^ t) := by
            rw [hpsi, hzeta]
    _ = (1 + Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π) ^ t := by
            simp

/-- All-order additive-character expansion: modulo `Q^(N+1)`, `ψ(y)` is the
binomial truncation of `(1 + π)^Tr(traceScale*y)`. -/
theorem psiInt_sub_traceBinomialApprox_mem_Q_pow_succ (N : ℕ) (y : kˣ) :
    F.psiInt (y : k) - psiTraceBinomialApprox F N y ∈ F.Q ^ (N + 1) := by
  let t : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hpsi :
      F.psiInt (y : k) = F.zeta_ell_int ^ t := by
    simpa [t] using
      F.toTraceFormStickelbergerSetup.psiInt_eq_zeta_ell_int_pow_trace (y : k)
  have hzeta : F.zeta_ell_int = 1 + F.π := by
    rw [F.hπ]
    ring
  have htrunc := one_add_pow_sub_choose_sum_mem_pow (I := F.Q) F.π_mem_Q t N
  simpa [psiTraceBinomialApprox, hpsi, hzeta, t] using htrunc

/-- The `i`-th truncated Artin-Hasse theta factor at the Teichmüller
Frobenius power attached to `traceScale * y`. -/
noncomputable def artinHasseThetaFactor (N : ℕ) (y : kˣ)
    (i : Fin F.toConcreteStickelbergerSetup.f) : 𝓞 R' :=
  dworkThetaTrunc
    (dworkCoeffArtinHasse F.toConcreteStickelbergerSetup) N
    ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))

/-- The finite product of Artin-Hasse theta truncations at the Teichmüller
Frobenius powers attached to `traceScale * y`. -/
noncomputable def artinHasseThetaTruncProduct (N : ℕ) (y : kˣ) : 𝓞 R' :=
  dworkThetaFrobeniusProduct ℓ F.toConcreteStickelbergerSetup.f N
    (dworkCoeffArtinHasse F.toConcreteStickelbergerSetup)
    (F.teichUnitFullVal (F.traceScale * y))

/-- The finite theta product is the product of its one-variable factors. -/
theorem artinHasseThetaTruncProduct_eq_prod_factor (N : ℕ) (y : kˣ) :
    artinHasseThetaTruncProduct F N y =
      ∏ i : Fin F.toConcreteStickelbergerSetup.f,
        artinHasseThetaFactor F N y i := rfl

/-- The finite multi-index sum appearing in
`FullTeichDworkSetup.psi_dwork_factorization`, specialized to the
Artin-Hasse Dwork coefficients. -/
noncomputable def artinHasseDworkMultiIndexSum (N : ℕ) (y : kˣ) : 𝓞 R' :=
  ∑ m ∈ Furtwaengler.multiIndexLE F.toConcreteStickelbergerSetup.f N,
    dworkMultiIndexTerm ℓ
      (dworkCoeffArtinHasse F.toConcreteStickelbergerSetup)
      (F.teichUnitFullVal (F.traceScale * y)) m

/-- The `i`-th truncated Artin-Hasse theta factor with an explicit Dwork
parameter `γ`. -/
noncomputable def artinHasseThetaFactorAt (γ : 𝓞 R') (N : ℕ) (y : kˣ)
    (i : Fin F.toConcreteStickelbergerSetup.f) : 𝓞 R' :=
  dworkThetaTrunc
    (dworkCoeffArtinHasseAt F.toConcreteStickelbergerSetup γ) N
    ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))

/-- The `i`-th truncated Artin-Hasse theta factor with an explicit parameter
and precision-indexed coefficient representatives. -/
noncomputable def artinHasseThetaFactorAtTo (γ : 𝓞 R') (N : ℕ) (y : kˣ)
    (i : Fin F.toConcreteStickelbergerSetup.f) : 𝓞 R' :=
  dworkThetaTrunc
    (dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup γ N) N
    ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))

/-- The finite product of Artin-Hasse theta truncations with an explicit
Dwork parameter `γ`. -/
noncomputable def artinHasseThetaTruncProductAt (γ : 𝓞 R') (N : ℕ) (y : kˣ) :
    𝓞 R' :=
  dworkThetaFrobeniusProduct ℓ F.toConcreteStickelbergerSetup.f N
    (dworkCoeffArtinHasseAt F.toConcreteStickelbergerSetup γ)
    (F.teichUnitFullVal (F.traceScale * y))

/-- The finite product of Artin-Hasse theta truncations with precision-indexed
coefficient representatives. -/
noncomputable def artinHasseThetaTruncProductAtTo (γ : 𝓞 R') (N : ℕ) (y : kˣ) :
    𝓞 R' :=
  dworkThetaFrobeniusProduct ℓ F.toConcreteStickelbergerSetup.f N
    (dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup γ N)
    (F.teichUnitFullVal (F.traceScale * y))

/-- The finite multi-index sum for the parameterized Artin-Hasse Dwork
coefficients. -/
noncomputable def artinHasseDworkMultiIndexSumAt (γ : 𝓞 R') (N : ℕ) (y : kˣ) :
    𝓞 R' :=
  ∑ m ∈ Furtwaengler.multiIndexLE F.toConcreteStickelbergerSetup.f N,
    dworkMultiIndexTerm ℓ
      (dworkCoeffArtinHasseAt F.toConcreteStickelbergerSetup γ)
      (F.teichUnitFullVal (F.traceScale * y)) m

/-- The finite multi-index sum for precision-indexed Artin-Hasse coefficient
representatives. -/
noncomputable def artinHasseDworkMultiIndexSumAtTo (γ : 𝓞 R') (N : ℕ) (y : kˣ) :
    𝓞 R' :=
  ∑ m ∈ Furtwaengler.multiIndexLE F.toConcreteStickelbergerSetup.f N,
    dworkMultiIndexTerm ℓ
      (dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup γ N)
      (F.teichUnitFullVal (F.traceScale * y)) m

/-- Quotient normal form for the precision-indexed Artin-Hasse theta product:
it is a finite product of polynomial evaluations of the mapped Artin-Hasse
exponential. -/
theorem quotient_mk_artinHasseThetaTruncProductAtTo_eq_prod_trunc_eval
    (γ : 𝓞 R') (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (artinHasseThetaTruncProductAtTo F γ N y) =
      ∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂
          (RingHom.id A)
          (Ideal.Quotient.mk (F.Q ^ (N + 1))
            (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) := by
  classical
  dsimp only
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' :=
    F.toConcreteStickelbergerSetup
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let Eps : PowerSeries A := hE.mapTo (S0.rIntegralRatToQuotient N)
  let u : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
    (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  calc
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (artinHasseThetaTruncProductAtTo F γ N y)
        = ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            Ideal.Quotient.mk (F.Q ^ (N + 1))
              (dworkThetaTrunc (dworkCoeffArtinHasseAtTo S0 γ N) N (u i)) := by
            simp [artinHasseThetaTruncProductAtTo, dworkThetaFrobeniusProduct,
              S0, u, map_prod]
    _ = ∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂
          (RingHom.id A)
          (Ideal.Quotient.mk (F.Q ^ (N + 1)) (γ * u i)) := by
            refine Finset.prod_congr rfl ?_
            intro i _hi
            simpa [Eps, hE, S0, A] using
              ConcreteStickelbergerSetup.quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_trunc_eval
                S0 γ (u i) N
    _ = ∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂
          (RingHom.id A)
          (Ideal.Quotient.mk (F.Q ^ (N + 1))
            (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) := by
            rfl

/-- Quotient normal form for the corrected theta product, with the
precision-indexed parameter replaced everywhere by the finite inverse-series
evaluation at `π`. -/
theorem quotient_mk_artinHasseThetaTruncProductAtTo_approx_eq_prod_inverse_trunc_eval
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y) =
      ∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂
          (RingHom.id A)
          ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
            Ideal.Quotient.mk (F.Q ^ (N + 1))
              ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) := by
  classical
  dsimp only
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' :=
    F.toConcreteStickelbergerSetup
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let Eps : PowerSeries A := hE.mapTo (S0.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (S0.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let γ : 𝓞 R' := artinHasseDworkParameterApproxTo S0 N
  let u : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
    (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hγ :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) γ =
        (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar := by
    simpa [γ, Ips, πbar, S0, A] using
      quotient_mk_artinHasseDworkParameterApproxTo_eq_trunc_eval S0 N
  calc
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (artinHasseThetaTruncProductAtTo F γ N y)
        = ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂
              (RingHom.id A)
              (Ideal.Quotient.mk (F.Q ^ (N + 1)) (γ * u i)) := by
            simpa [Eps, hE, S0, γ, u, A] using
              quotient_mk_artinHasseThetaTruncProductAtTo_eq_prod_trunc_eval
                F γ N y
    _ = ∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂
          (RingHom.id A)
          ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
            Ideal.Quotient.mk (F.Q ^ (N + 1)) (u i)) := by
            refine Finset.prod_congr rfl ?_
            intro i _hi
            have harg :
                Ideal.Quotient.mk (F.Q ^ (N + 1)) (γ * u i) =
                  (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
                    Ideal.Quotient.mk (F.Q ^ (N + 1)) (u i) := by
              rw [map_mul, hγ]
            rw [harg]

/-- Single-polynomial quotient normal form for the corrected theta product:
the finite product of inverse-series Artin-Hasse evaluations is the evaluation
at `E_ℓ^{-1}(π)` of the product of the rescaled Artin-Hasse truncations. -/
theorem quotient_mk_artinHasseThetaTruncProductAtTo_approx_eq_rescaled_inverse_eval
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y) =
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        PowerSeries.trunc (N + 1)
          (PowerSeries.rescale
            (Ideal.Quotient.mk (F.Q ^ (N + 1))
              ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) Eps)
        ).eval₂ (RingHom.id A) δ := by
  classical
  dsimp only
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' :=
    F.toConcreteStickelbergerSetup
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let Eps : PowerSeries A := hE.mapTo (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let u : Fin F.toConcreteStickelbergerSetup.f → A := fun i =>
    Ideal.Quotient.mk (F.Q ^ (N + 1))
      ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))
  calc
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y)
        = ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂
              (RingHom.id A) (δ * u i) := by
            simpa [Eps, Ips, πbar, δ, u, hE, A] using
              F.quotient_mk_artinHasseThetaTruncProductAtTo_approx_eq_prod_inverse_trunc_eval
                N y
    _ = ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) (PowerSeries.rescale (u i) Eps)).eval₂
            (RingHom.id A) δ := by
            refine Finset.prod_congr rfl ?_
            intro i _hi
            rw [powerSeries_trunc_rescale_eval₂_eq_trunc_eval₂_mul]
    _ = (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        PowerSeries.trunc (N + 1) (PowerSeries.rescale (u i) Eps)
        ).eval₂ (RingHom.id A) δ := by
            simpa using
              (Polynomial.eval₂_finsetProd
                (s := (Finset.univ : Finset (Fin F.toConcreteStickelbergerSetup.f)))
                (g := fun i : Fin F.toConcreteStickelbergerSetup.f =>
                  PowerSeries.trunc (N + 1) (PowerSeries.rescale (u i) Eps))
                (f := RingHom.id A) (x := δ)).symm

/-- Exact quotient target for the remaining all-order Artin-Hasse splitting:
the theta-product congruence is equivalent to the finite inverse-series
Artin-Hasse product being `(1 + π)^Tr`. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_iff
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    F.psiInt (y : k) -
        artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y ∈
      F.Q ^ (N + 1) ↔
      (1 + πbar) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val =
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂
            (RingHom.id A)
            ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
              Ideal.Quotient.mk (F.Q ^ (N + 1))
                ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let Eps : PowerSeries A := hE.mapTo (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let theta : 𝓞 R' :=
    artinHasseThetaTruncProductAtTo F
      (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y
  let target : A :=
    ∏ i : Fin F.toConcreteStickelbergerSetup.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id A)
        ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))))
  have hpsi :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.psiInt (y : k)) =
        (1 + πbar) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val := by
    simpa [πbar, A] using F.quotient_mk_psiInt_eq_one_add_pi_pow_trace N y
  have htheta :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) theta = target := by
    simpa [theta, target, Eps, Ips, πbar, hE, A] using
      F.quotient_mk_artinHasseThetaTruncProductAtTo_approx_eq_prod_inverse_trunc_eval
        N y
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.psiInt (y : k) - theta) = 0 ↔
      (1 + πbar) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val =
        target
  rw [map_sub]
  constructor
  · intro h
    have heq :
        Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.psiInt (y : k)) =
          Ideal.Quotient.mk (F.Q ^ (N + 1)) theta := sub_eq_zero.mp h
    simpa [hpsi, htheta] using heq
  · intro h
    rw [hpsi, htheta, h]
    simp

/-- Equivalent multiplicative-character target for the remaining all-order
splitting: the product of the corrected Artin-Hasse values over the
Frobenius orbit must equal the normalized base value `θ(1)` raised to the
trace exponent. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_iff_base_pow
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    F.psiInt (y : k) -
        artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y ∈
      F.Q ^ (N + 1) ↔
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) δ) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val =
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂
            (RingHom.id A)
            (δ *
              Ideal.Quotient.mk (F.Q ^ (N + 1))
                ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) := by
  classical
  dsimp only
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' :=
    F.toConcreteStickelbergerSetup
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let Eps : PowerSeries A := hE.mapTo (S0.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (S0.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hnorm :
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) δ = 1 + πbar := by
    simpa [S0, Eps, Ips, πbar, δ, hE, A] using
      ConcreteStickelbergerSetup.artinHasseExp_trunc_eval_inverse_trunc_eval_eq_one_add_pi
        S0 N
  rw [hnorm]
  simpa [S0, Eps, Ips, πbar, δ, hE, A] using
    F.psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_iff N y

/-! ### Named exact quotient target for the all-order Dwork endpoint -/

/-- The normalized quotient product identity for the corrected Artin-Hasse
Dwork approximation.  This is the statement supplied by the finite-log proof:
the Frobenius-orbit product of the truncated Artin-Hasse evaluations equals
`(1 + π)^Tr`. -/
def artinHasseApproxDworkOneAddPiProductIdentity (N : ℕ) (y : kˣ) : Prop :=
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  (1 + πbar) ^
      (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val =
    ∏ i : Fin F.toConcreteStickelbergerSetup.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id A)
        (δ *
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))))

/-- The base-value quotient product identity for the corrected Artin-Hasse
Dwork approximation.  This is the equivalent endpoint obtained by rewriting
the normalized base `1 + π` as the truncated Artin-Hasse value at the
inverse-series parameter. -/
def artinHasseApproxDworkBaseProductIdentity (N : ℕ) (y : kˣ) : Prop :=
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) δ) ^
      (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val =
    ∏ i : Fin F.toConcreteStickelbergerSetup.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id A)
        (δ *
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))))

/-- Named quotient target for the all-order Dwork endpoint, in normalized
`(1 + π)^Tr` form. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_iff_oneAddPiProductIdentity
    (N : ℕ) (y : kˣ) :
    F.psiInt (y : k) -
        artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y ∈
      F.Q ^ (N + 1) ↔
      F.artinHasseApproxDworkOneAddPiProductIdentity N y := by
  simpa [artinHasseApproxDworkOneAddPiProductIdentity] using
    F.psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_iff N y

/-- Named quotient target for the all-order Dwork endpoint, in base-value
`E_N(δ_N)^Tr` form. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_iff_baseProductIdentity
    (N : ℕ) (y : kˣ) :
    F.psiInt (y : k) -
        artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y ∈
      F.Q ^ (N + 1) ↔
      F.artinHasseApproxDworkBaseProductIdentity N y := by
  simpa [artinHasseApproxDworkBaseProductIdentity] using
    F.psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_iff_base_pow N y

/-- Forward wrapper: proving the normalized quotient product identity is enough
to close the required all-order Dwork membership theorem. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_of_oneAddPiProductIdentity
    {N : ℕ} {y : kˣ}
    (h : F.artinHasseApproxDworkOneAddPiProductIdentity N y) :
    F.psiInt (y : k) -
        artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y ∈
      F.Q ^ (N + 1) :=
  (F.psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_iff_oneAddPiProductIdentity
    N y).2 h

/-- Forward wrapper: proving the base-value quotient product identity is enough
to close the required all-order Dwork membership theorem. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_of_baseProductIdentity
    {N : ℕ} {y : kˣ}
    (h : F.artinHasseApproxDworkBaseProductIdentity N y) :
    F.psiInt (y : k) -
        artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y ∈
      F.Q ^ (N + 1) :=
  (F.psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_iff_baseProductIdentity
    N y).2 h

/-! ### Finite Artin-Hasse-Witt Teichmüller surface -/

/-- Quotient-level Artin-Hasse factor attached to one Witt-Teichmüller
representative. This is the presentation-level surface for the finite
Artin-Hasse-Witt character; proving that it descends/adds on arbitrary Witt
vectors is the separate carry-cancellation step. -/
noncomputable def artinHasseWittTeichFactor
    (N : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (x : k) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
    (ε * θ (WittVector.teichmuller ℓ x))

/-- Finite product of the quotient-level Artin-Hasse factors attached to a
chosen family of Teichmüller representatives. -/
noncomputable def artinHasseWittTeichProduct
    (N : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) {ι : Type*}
    (s : Finset ι) (x : ι → k) : 𝓞 R' ⧸ F.Q ^ (N + 1) :=
  ∏ i ∈ s, F.artinHasseWittTeichFactor N ε (x i)

/-- On a single Teichmüller unit, the presentation-level AH-Witt factor is
the existing one-variable truncated Artin-Hasse factor at the selected
integral Teichmüller lift. -/
theorem artinHasseWittTeichFactor_unit_eq_trunc_eval
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (x : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal x)
    F.artinHasseWittTeichFactor N ε (x : k) =
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (ε * zbar) := by
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal x)
  rw [artinHasseWittTeichFactor]
  rw [F.wittThetaModQPow_teichmuller_unit N x]

/-- The AH-Witt Teichmüller product attached to the Frobenius-Teichmüller
presentation of `wittFrobeniusTrace [x]` is exactly the finite product of
one-variable Artin-Hasse factors over the Frobenius orbit. -/
theorem artinHasseWittTeichProduct_frobeniusTrace_teichmuller_unit
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N f : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (x : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal x)
    F.artinHasseWittTeichProduct N ε (Finset.univ : Finset (Fin f))
        (fun i : Fin f => (x : k) ^ (ℓ ^ (i : ℕ))) =
      ∏ i : Fin f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal x)
  rw [artinHasseWittTeichProduct]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  have hfactor :=
    F.artinHasseWittTeichFactor_unit_eq_trunc_eval N ε (x ^ (ℓ ^ (i : ℕ)))
  have hz :
      (Ideal.Quotient.mk (F.Q ^ (N + 1))
          (F.teichUnitFullVal (x ^ (ℓ ^ (i : ℕ)))) : A) =
        zbar ^ (ℓ ^ (i : ℕ)) := by
    simp [zbar, map_pow]
  simpa [A, Eps, zbar, hz] using hfactor

/-- The concrete Frobenius-orbit product used in the final quotient target,
rewritten as the presentation-level AH-Witt product for the Witt Frobenius
trace of the Teichmüller representative of `traceScale * y`. -/
theorem artinHasseWittTeichProduct_traceScale_eq_frobenius_product
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1)) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    F.artinHasseWittTeichProduct N ε
        (Finset.univ : Finset (Fin F.toConcreteStickelbergerSetup.f))
        (fun i : Fin F.toConcreteStickelbergerSetup.f =>
          ((F.traceScale * y : kˣ) : k) ^ (ℓ ^ (i : ℕ))) =
      ∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ))) := by
  simpa using
    F.artinHasseWittTeichProduct_frobeniusTrace_teichmuller_unit
      N F.toConcreteStickelbergerSetup.f ε (F.traceScale * y)

/-- The Frobenius-shifted Artin-Hasse product produced by the product
recursion can be reindexed back to the same finite Frobenius orbit, with the
parameter changed from `δ` to `δ^ℓ`. -/
theorem artinHasseExp_trunc_eval_frobenius_shift_product
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((δ * zbar ^ (ℓ ^ (i : ℕ))) ^ ℓ)) =
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
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let z : 𝓞 R' := F.teichUnitFullVal (F.traceScale * y)
  let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) z
  let f : ℕ := F.toConcreteStickelbergerSetup.f
  let g : ℕ → A := fun i =>
    (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
      (δ ^ ℓ * zbar ^ (ℓ ^ i))
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
            ((δ * zbar ^ (ℓ ^ (i : ℕ))) ^ ℓ)) =
        ∏ i ∈ Finset.range f, g (i + 1) := by
    calc
      (∏ i : Fin f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            ((δ * zbar ^ (ℓ ^ (i : ℕ))) ^ ℓ))
          = ∏ i ∈ Finset.range f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                ((δ * zbar ^ (ℓ ^ i)) ^ ℓ) :=
              (Finset.prod_range
                (f := fun i : ℕ =>
                  (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                    ((δ * zbar ^ (ℓ ^ i)) ^ ℓ))).symm
      _ = ∏ i ∈ Finset.range f, g (i + 1) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              have hpow : (zbar ^ (ℓ ^ i)) ^ ℓ = zbar ^ (ℓ ^ (i + 1)) := by
                rw [← pow_mul]
                exact congrArg (fun n : ℕ => zbar ^ n) (by rw [pow_succ] : ℓ ^ i * ℓ = ℓ ^ (i + 1))
              rw [mul_pow, hpow]
  have hright :
      (∏ i : Fin f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ ℓ * zbar ^ (ℓ ^ (i : ℕ)))) =
        ∏ i ∈ Finset.range f, g i := by
    calc
      (∏ i : Fin f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))))
          = ∏ i ∈ Finset.range f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (δ ^ ℓ * zbar ^ (ℓ ^ i)) :=
              (Finset.prod_range
                (f := fun i : ℕ =>
                  (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                    (δ ^ ℓ * zbar ^ (ℓ ^ i))).symm)
      _ = ∏ i ∈ Finset.range f, g i := rfl
  rw [show F.toConcreteStickelbergerSetup.f = f from rfl]
  rw [hleft, hright]
  exact prod_range_shift_eq_of_last_eq_first g f hgperiod

/-- Clean recursive form for the corrected Frobenius theta product:
`P(δ)^ℓ = C(δ) * P(δ^ℓ)`, where `C(δ)` is the finite product of the
ordinary-exponential correction factors. -/
theorem artinHasseExp_trunc_eval_frobenius_product_pow_prime_eq_correction_mul_parameter_pow
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
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (δ * zbar ^ (ℓ ^ (i : ℕ)))) *
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
    ConcreteStickelbergerSetup.artinHasseExp_trunc_eval_inverse_mul_finset_prod_pow_prime_eq
      (S := F.toConcreteStickelbergerSetup)
      (N := N)
      (s := (Finset.univ : Finset (Fin F.toConcreteStickelbergerSetup.f)))
      (u := fun i : Fin F.toConcreteStickelbergerSetup.f => zbar ^ (ℓ ^ (i : ℕ)))
  have hshift :=
    F.artinHasseExp_trunc_eval_frobenius_shift_product N y
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ
        = (∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (δ * zbar ^ (ℓ ^ (i : ℕ)))) *
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              ((δ * zbar ^ (ℓ ^ (i : ℕ))) ^ ℓ) := by
          simpa [A, Eps, Ips, Rps, πbar, δ, zbar] using hrec
    _ = (∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
              (δ * zbar ^ (ℓ ^ (i : ℕ)))) *
          ∏ i : Fin F.toConcreteStickelbergerSetup.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (δ ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
          rw [hshift]

/-- The ordinary-exponential correction product in the Dwork recursion
collapses to one correction factor at the finite Frobenius trace sum. -/
theorem artinHasseExp_trunc_eval_frobenius_correction_product_eq_trace_sum
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
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (δ * ∑ i : Fin F.toConcreteStickelbergerSetup.f,
          zbar ^ (ℓ ^ (i : ℕ))) := by
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
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  have hprod :=
    rescale_exp_trunc_eval₂_finset_prod_eq_sum
      (r := ℓ)
      (φ := F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
      (N := N)
      (δ := δ)
      hδ
      (s := (Finset.univ : Finset (Fin F.toConcreteStickelbergerSetup.f)))
      (u := fun i : Fin F.toConcreteStickelbergerSetup.f => zbar ^ (ℓ ^ (i : ℕ)))
  simpa [A, Ips, Rps, πbar, δ, zbar] using hprod

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
