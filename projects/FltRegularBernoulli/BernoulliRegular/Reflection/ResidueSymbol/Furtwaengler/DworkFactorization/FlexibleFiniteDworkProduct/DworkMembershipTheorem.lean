module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleFiniteDworkProduct.FiniteLogDworkProduct

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConductorFlexibleFullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')

/-- Positive-precision quotient identity for the corrected Dwork product:
`P_N(a)` equals the trace-form target root modulo `Q^(N+1)`. -/
theorem quotient_mk_dworkProductApprox_eq_one_add_pi_pow_traceNatCast_of_one_le
    {N : ℕ} (hN : 1 ≤ N) (y : kˣ) :
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y) =
      Ideal.Quotient.mk (F.Q ^ (N + 1))
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val) := by
  let P : 𝓞 R' :=
    F.artinHasseThetaTruncProductAtTo
      (F.concrete.artinHasseDworkParameterApproxTo N) N y
  let R : 𝓞 R' :=
    (1 + F.π) ^
      (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let invCoord : 𝓞 R' := F.traceRootInverseCoord y
  have hratio :
      P * (1 + invCoord) - 1 ∈ F.Q ^ (N + 1) := by
    simpa [P, invCoord] using
      F.dworkProductApprox_mul_traceRootInverse_sub_one_mem_Q_pow_succ_of_one_le hN y
  have hRinv : R * (1 + invCoord) = 1 := by
    simpa [R, invCoord] using
      F.one_add_pi_pow_traceNatCast_mul_one_add_traceRootInverseCoord_eq_one y
  have hdiff : P - R ∈ F.Q ^ (N + 1) := by
    have hmul : R * (P * (1 + invCoord) - 1) ∈ F.Q ^ (N + 1) :=
      (F.Q ^ (N + 1)).mul_mem_left R hratio
    have heq : P - R = R * (P * (1 + invCoord) - 1) := by
      calc
        P - R = P * (R * (1 + invCoord)) - R := by
          rw [hRinv]
          ring
        _ = R * (P * (1 + invCoord) - 1) := by
          ring
    simpa [heq] using hmul
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  simpa [P, R] using hdiff

/-- Quotient identity for the corrected Dwork product at every precision. -/
theorem quotient_mk_dworkProductApprox_eq_one_add_pi_pow_traceNatCast
    (N : ℕ) (y : kˣ) :
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y) =
      Ideal.Quotient.mk (F.Q ^ (N + 1))
        ((1 + F.π) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val) := by
  by_cases hN : 1 ≤ N
  · exact F.quotient_mk_dworkProductApprox_eq_one_add_pi_pow_traceNatCast_of_one_le hN y
  · have hN0 : N = 0 := by omega
    subst N
    let P : 𝓞 R' :=
      F.artinHasseThetaTruncProductAtTo
        (F.concrete.artinHasseDworkParameterApproxTo 0) 0 y
    let R : 𝓞 R' :=
      (1 + F.π) ^
        (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    have hP : P - 1 ∈ F.Q := by
      simpa [P] using F.artinHasseThetaTruncProductAtTo_approx_sub_one_mem_Q 0 y
    have hR : R - 1 ∈ F.Q := by
      simpa [R] using F.one_add_pi_pow_traceNatCast_sub_one_mem_Q y
    have hdiffQ : P - R ∈ F.Q := by
      have hsub : (P - 1) - (R - 1) ∈ F.Q := F.Q.sub_mem hP hR
      have heq : P - R = (P - 1) - (R - 1) := by
        ring
      rw [heq]
      exact hsub
    have hdiff : P - R ∈ F.Q ^ (0 + 1) := by
      simpa using hdiffQ
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    simpa [P, R] using hdiff

/-- Quotient identity packaged in the named product-identity form used by the
final quotient-to-membership reduction. -/
theorem artinHasseApproxDworkOneAddPiProductIdentity_of_finiteLog
    (N : ℕ) (y : kˣ) :
    F.artinHasseApproxDworkOneAddPiProductIdentity N y := by
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.concrete.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.concrete.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  let P : 𝓞 R' :=
    F.artinHasseThetaTruncProductAtTo
      (F.concrete.artinHasseDworkParameterApproxTo N) N y
  let R : 𝓞 R' := (1 + F.π) ^ t
  let target : A :=
    ∏ i : Fin F.concrete.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id A)
        ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))))
  have hquot :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) P =
        Ideal.Quotient.mk (F.Q ^ (N + 1)) R := by
    simpa [P, R, t] using
      F.quotient_mk_dworkProductApprox_eq_one_add_pi_pow_traceNatCast N y
  have hprod :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) P = target := by
    simpa [P, target, Eps, Ips, πbar, A] using
      F.quotient_mk_artinHasseThetaTruncProductAtTo_approx_eq_prod_inverse_trunc_eval
        N y
  have hroot :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) R = (1 + πbar) ^ t := by
    simp [R, πbar, t]
  have hidentity : (1 + πbar) ^ t = target := by
    calc
      (1 + πbar) ^ t = Ideal.Quotient.mk (F.Q ^ (N + 1)) R := hroot.symm
      _ = Ideal.Quotient.mk (F.Q ^ (N + 1)) P := hquot.symm
      _ = target := hprod
  simpa [artinHasseApproxDworkOneAddPiProductIdentity, A, Eps, Ips, πbar, t,
    target] using hidentity

/-- The finite-log quotient identity closes the all-order flexible Dwork
membership theorem for the Artin-Hasse theta approximation. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ
    (N : ℕ) (y : kˣ) :
    F.psiInt (y : k) -
        F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y ∈
      F.Q ^ (N + 1) :=
  F.psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_of_oneAddPiProductIdentity
    (F.artinHasseApproxDworkOneAddPiProductIdentity_of_finiteLog N y)

/-- The precision-indexed flexible Artin-Hasse theta product equals the
corresponding `multiIndexLE` sum modulo `Q^(N+1)` when `γ ∈ Q`. -/
theorem artinHasseThetaTruncProductAtTo_sub_multiIndexSumAtTo_mem_Q_pow_succ
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (N : ℕ) (y : kˣ) :
    F.artinHasseThetaTruncProductAtTo γ N y -
        (∑ m ∈ Furtwaengler.multiIndexLE F.concrete.f N,
          dworkMultiIndexTerm ℓ
            (F.concrete.dworkCoeffArtinHasseAtTo γ N)
            (F.teichUnitFullVal (F.traceScale * y)) m) ∈ F.Q ^ (N + 1) := by
  simpa [artinHasseThetaTruncProductAtTo, artinHasseDworkMultiIndexSumAtTo,
    dworkMultiIndexTerm] using
    dworkThetaFrobeniusProduct_sub_multiIndexLESum_mem_I_pow_succ
      (I := F.Q) ℓ F.concrete.f N
      (F.concrete.dworkCoeffArtinHasseAtTo γ N)
      (F.teichUnitFullVal (F.traceScale * y))
      (fun n => F.concrete.dworkCoeffArtinHasseAtTo_mem_Q_pow hγ N n)

/-- Precision-indexed final algebraic bridge: a theta-product splitting
congruence for the `N`-precision coefficient representatives implies the
corresponding `multiIndexLE` congruence. -/
theorem psiInt_sub_artinHasseDworkMultiIndexSumAtTo_mem_Q_pow_succ_of_theta
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (N : ℕ) (y : kˣ)
    (htheta :
      F.psiInt (y : k) - F.artinHasseThetaTruncProductAtTo γ N y ∈ F.Q ^ (N + 1)) :
    F.psiInt (y : k) - F.artinHasseDworkMultiIndexSumAtTo γ N y ∈
      F.Q ^ (N + 1) :=
  sub_mem_trans (F.Q ^ (N + 1)) htheta
    (by
      simpa [artinHasseDworkMultiIndexSumAtTo] using
        F.artinHasseThetaTruncProductAtTo_sub_multiIndexSumAtTo_mem_Q_pow_succ hγ N y)

/-- Construct a conductor-flexible Dwork setup from a precision-indexed family
of Artin-Hasse parameters `γ_N`.  The parameter and coefficient
representatives may depend on the target precision `N`. -/
noncomputable def toConductorFlexibleFullTeichDworkSetupArtinHasseAtTo
    (γ : ℕ → 𝓞 R') (hγ : ∀ N : ℕ, γ N ∈ F.Q)
    (hγπ : ∀ N : ℕ, 0 < N → γ N - F.π ∈ F.Q ^ 2)
    (hpsi : ∀ (N : ℕ) (y : kˣ),
      F.psiInt (y : k) - F.artinHasseDworkMultiIndexSumAtTo (γ N) N y ∈
        F.Q ^ (N + 1)) :
    ConductorFlexibleFullTeichDworkSetup ℓ p k K R' where
  toConductorFlexibleFullTeichStickelbergerSetup := F
  dworkCoeff := fun N n =>
    F.concrete.dworkCoeffArtinHasseAtTo (γ N) N n
  dworkCoeff_mem_Q_pow := fun N n =>
    F.concrete.dworkCoeffArtinHasseAtTo_mem_Q_pow (hγ N) N n
  dworkCoeff_lt_ell_leading := by
    intro N n hnN hn
    by_cases hN : N = 0
    · subst N
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hnN
      subst n
      simp [ConductorFlexibleConcreteStickelbergerSetup.dworkCoeffArtinHasseAtTo]
    · exact
        F.concrete.dworkCoeffArtinHasseAtTo_lt_ell_leading
          (hγ N) (hγπ N (Nat.pos_of_ne_zero hN)) N n hnN hn
  psi_dwork_factorization := by
    intro N y
    simpa [artinHasseDworkMultiIndexSumAtTo, dworkMultiIndexTerm, teichUnitFullVal,
      ConductorFlexibleFullTeichStickelbergerSetup.concrete,
      ConductorFlexibleTraceFormStickelbergerSetup.concrete] using hpsi N y

/-- Constructor variant where the precision-indexed splitting input is stated
at the theta-product level. -/
noncomputable def toConductorFlexibleFullTeichDworkSetupArtinHasseAtToOfTheta
    (γ : ℕ → 𝓞 R') (hγ : ∀ N : ℕ, γ N ∈ F.Q)
    (hγπ : ∀ N : ℕ, 0 < N → γ N - F.π ∈ F.Q ^ 2)
    (htheta : ∀ (N : ℕ) (y : kˣ),
      F.psiInt (y : k) - F.artinHasseThetaTruncProductAtTo (γ N) N y ∈
        F.Q ^ (N + 1)) :
    ConductorFlexibleFullTeichDworkSetup ℓ p k K R' :=
  F.toConductorFlexibleFullTeichDworkSetupArtinHasseAtTo γ hγ hγπ
    (fun N y =>
      F.psiInt_sub_artinHasseDworkMultiIndexSumAtTo_mem_Q_pow_succ_of_theta
        (hγ N) N y (htheta N y))

/-- The concrete precision-indexed Artin-Hasse flexible setup constructor. -/
noncomputable def toConductorFlexibleFullTeichDworkSetupArtinHasseApproxTo
    (hpsi : ∀ (N : ℕ) (y : kˣ),
      F.psiInt (y : k) -
          F.artinHasseDworkMultiIndexSumAtTo
            (F.concrete.artinHasseDworkParameterApproxTo N) N y ∈
        F.Q ^ (N + 1)) :
    ConductorFlexibleFullTeichDworkSetup ℓ p k K R' :=
  F.toConductorFlexibleFullTeichDworkSetupArtinHasseAtTo
    (fun N => F.concrete.artinHasseDworkParameterApproxTo N)
    (fun N => F.concrete.artinHasseDworkParameterApproxTo_mem_Q N)
    (fun _N hN =>
      F.concrete.artinHasseDworkParameterApproxTo_sub_pi_mem_Q_sq_of_pos hN)
    hpsi

/-- Concrete constructor variant where the all-order splitting input is stated
at the theta-product level. -/
noncomputable def toConductorFlexibleFullTeichDworkSetupArtinHasseApproxToOfTheta
    (htheta : ∀ (N : ℕ) (y : kˣ),
      F.psiInt (y : k) -
          F.artinHasseThetaTruncProductAtTo
            (F.concrete.artinHasseDworkParameterApproxTo N) N y ∈
        F.Q ^ (N + 1)) :
    ConductorFlexibleFullTeichDworkSetup ℓ p k K R' :=
  F.toConductorFlexibleFullTeichDworkSetupArtinHasseAtToOfTheta
    (fun N => F.concrete.artinHasseDworkParameterApproxTo N)
    (fun N => F.concrete.artinHasseDworkParameterApproxTo_mem_Q N)
    (fun _N hN =>
      F.concrete.artinHasseDworkParameterApproxTo_sub_pi_mem_Q_sq_of_pos hN)
    htheta

/-- Flexible full-Teich Dwork setup from the Artin-Hasse inverse parameter,
with no remaining Dwork splitting premise. -/
noncomputable def toConductorFlexibleFullTeichDworkSetupArtinHasseApproxToOfFiniteLog :
    ConductorFlexibleFullTeichDworkSetup ℓ p k K R' :=
  F.toConductorFlexibleFullTeichDworkSetupArtinHasseApproxToOfTheta
    (fun N y => F.psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ N y)

end ConductorFlexibleFullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
