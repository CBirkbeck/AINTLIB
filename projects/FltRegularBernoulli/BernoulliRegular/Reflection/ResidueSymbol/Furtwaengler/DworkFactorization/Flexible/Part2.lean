module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Flexible.Part1

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConductorFlexibleConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R')

theorem quotient_mk_dworkCoeffArtinHasseAtTo_den_mul_eq_num_gamma_pow
    (γ : 𝓞 R') (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
    Ideal.Quotient.mk (S.Q ^ (N + 1))
        ((c.den : 𝓞 R') * S.dworkCoeffArtinHasseAtTo γ N n) =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) ((c.num : 𝓞 R') * γ ^ n) := by
  dsimp only
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact S.dworkCoeffArtinHasseAtTo_den_mul_sub_num_gamma_pow_mem_Q_pow_succ γ N n

/-- The precision-indexed Artin-Hasse coefficient representative is the
quotient value of the rational coefficient times `γ^n`. -/
theorem quotient_mk_dworkCoeffArtinHasseAtTo_eq_rIntegralRatToQuotient_mul_gamma_pow
    (γ : 𝓞 R') (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
    let q : DieudonneDwork.rIntegralRatSubring ℓ :=
      ⟨c, artinHasseExpSeries_coeff_isRIntegral ℓ n⟩
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (S.dworkCoeffArtinHasseAtTo γ N n) =
      S.rIntegralRatToQuotient N q *
        Ideal.Quotient.mk (S.Q ^ (N + 1)) (γ ^ n) := by
  dsimp only
  let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
  let q : DieudonneDwork.rIntegralRatSubring ℓ :=
    ⟨c, artinHasseExpSeries_coeff_isRIntegral ℓ n⟩
  let QN : Ideal (𝓞 R') := S.Q ^ (N + 1)
  let d : 𝓞 R' ⧸ QN :=
    Ideal.Quotient.mk QN (((c.den : ℕ) : 𝓞 R'))
  have hdunit : IsUnit d := by
    simpa [d, q, c, QN] using S.rIntegralRat_den_isUnit_mod_Q_pow N q
  exact hdunit.mul_left_cancel <| by
    calc
      d * Ideal.Quotient.mk QN (S.dworkCoeffArtinHasseAtTo γ N n)
          = Ideal.Quotient.mk QN
              ((c.den : 𝓞 R') * S.dworkCoeffArtinHasseAtTo γ N n) := by
            simp [d, QN]
      _ = Ideal.Quotient.mk QN ((c.num : 𝓞 R') * γ ^ n) := by
            simpa [c, QN] using
              S.quotient_mk_dworkCoeffArtinHasseAtTo_den_mul_eq_num_gamma_pow γ N n
      _ = Ideal.Quotient.mk QN (((q : ℚ).num : ℤ) : 𝓞 R') *
            Ideal.Quotient.mk QN (γ ^ n) := by
            simp [q, c, QN]
      _ = (d * S.rIntegralRatToQuotient N q) *
            Ideal.Quotient.mk QN (γ ^ n) := by
            rw [show d * S.rIntegralRatToQuotient N q =
                Ideal.Quotient.mk QN (((q : ℚ).num : ℤ) : 𝓞 R') by
              simpa [d, q, c, QN] using S.rIntegralRatToQuotient_den_mul N q]
      _ = d * (S.rIntegralRatToQuotient N q *
            Ideal.Quotient.mk QN (γ ^ n)) := by ring

/-- If two elements are congruent modulo `I^2` and both lie in `I`, then their
`n`-th powers are congruent modulo `I^(n+1)`. -/
theorem pow_sub_pow_mem_pow_succ_of_sub_mem_sq
    {A : Type*} [CommRing A] (I : Ideal A) {γ π : A}
    (hγ : γ ∈ I) (hπ : π ∈ I) (hγπ : γ - π ∈ I ^ 2) (n : ℕ) :
    γ ^ n - π ^ n ∈ I ^ (n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hγn : γ ^ n ∈ I ^ n :=
        Ideal.pow_mem_pow hγ n
      have hleft : γ ^ n * (γ - π) ∈ I ^ (n + 2) := by
        have hmul : γ ^ n * (γ - π) ∈ I ^ n * I ^ 2 :=
          Ideal.mul_mem_mul hγn hγπ
        simpa [pow_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmul
      have hright : (γ ^ n - π ^ n) * π ∈ I ^ (n + 2) := by
        have hmul : (γ ^ n - π ^ n) * π ∈ I ^ (n + 1) * I ^ 1 :=
          Ideal.mul_mem_mul ih (by simpa using hπ)
        change (γ ^ n - π ^ n) * π ∈ I ^ ((n + 1) + 1)
        simpa [Ideal.IsTwoSided.pow_add] using hmul
      rw [show γ ^ (n + 1) - π ^ (n + 1) =
          γ ^ n * (γ - π) + (γ ^ n - π ^ n) * π by ring]
      exact (I ^ (n + 2)).add_mem hleft hright

/-- Precision-indexed leading-term congruence for `n < ℓ`. -/
theorem dworkCoeffArtinHasseAtTo_lt_ell_leading
    {γ : 𝓞 R'} (hγ : γ ∈ S.Q) (hγπ : γ - S.π ∈ S.Q ^ 2)
    (N n : ℕ) (hnN : n ≤ N) (hn : n < ℓ) :
    ((Nat.factorial n : ℕ) : 𝓞 R') * S.dworkCoeffArtinHasseAtTo γ N n - S.π ^ n
      ∈ S.Q ^ (n + 1) := by
  cases n with
  | zero =>
      simp [dworkCoeffArtinHasseAtTo]
  | succ n =>
      let m : ℕ := Nat.succ n
      let c : ℚ := (PowerSeries.coeff (R := ℚ) m) (artinHasseExpSeries ℓ)
      have hc : c = (1 : ℚ) / (Nat.factorial m : ℚ) := by
        simpa [c, m] using artinHasseExpSeries_coeff_eq_inv_factorial_of_lt ℓ hn
      have hnum : c.num = 1 := by
        rw [hc]
        norm_num [Nat.factorial_pos]
      have hden : c.den = Nat.factorial m := by
        rw [hc]
        norm_num [Nat.factorial_pos, Nat.factorial_ne_zero]
      have hdenInvN :
          ((Nat.factorial m : ℕ) : 𝓞 R') * S.dworkCoeffArtinHasseDenInvTo m N - 1 ∈
            S.Q ^ (N + 1) := by
        simpa [c, hden] using S.dworkCoeffArtinHasseDenInvTo_spec m N
      have hdenInv :
          ((Nat.factorial m : ℕ) : 𝓞 R') * S.dworkCoeffArtinHasseDenInvTo m N - 1 ∈
            S.Q ^ (m + 1) :=
        Ideal.pow_le_pow_right (Nat.succ_le_succ hnN) hdenInvN
      have hcoeff_gamma :
          ((Nat.factorial m : ℕ) : 𝓞 R') * S.dworkCoeffArtinHasseAtTo γ N m -
              γ ^ m ∈ S.Q ^ (m + 1) := by
        have hmul :
            γ ^ m *
                (((Nat.factorial m : ℕ) : 𝓞 R') *
                    S.dworkCoeffArtinHasseDenInvTo m N - 1) ∈
              S.Q ^ (m + 1) :=
          Ideal.mul_mem_left _ _ hdenInv
        convert hmul using 1
        simp [dworkCoeffArtinHasseAtTo, dworkCoeffArtinHasseAtRawTo, c, m, hnum]
        ring
      have hpow : γ ^ m - S.π ^ m ∈ S.Q ^ (m + 1) :=
        pow_sub_pow_mem_pow_succ_of_sub_mem_sq (I := S.Q)
          hγ S.π_mem_Q hγπ m
      rw [show ((Nat.factorial m : ℕ) : 𝓞 R') * S.dworkCoeffArtinHasseAtTo γ N m -
          S.π ^ m =
            (((Nat.factorial m : ℕ) : 𝓞 R') * S.dworkCoeffArtinHasseAtTo γ N m -
              γ ^ m) + (γ ^ m - S.π ^ m) by ring]
      exact (S.Q ^ (m + 1)).add_mem hcoeff_gamma hpow

/-- Quotient sum form of a precision-indexed one-variable Artin-Hasse theta
truncation. -/
theorem quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_sum_rIntegralRatToQuotient
    (γ u : 𝓞 R') (N : ℕ) :
    Ideal.Quotient.mk (S.Q ^ (N + 1))
        (dworkThetaTrunc (S.dworkCoeffArtinHasseAtTo γ N) N u) =
      ∑ n ∈ Finset.range (N + 1),
        S.rIntegralRatToQuotient N
          (⟨(PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ),
            artinHasseExpSeries_coeff_isRIntegral ℓ n⟩ :
              DieudonneDwork.rIntegralRatSubring ℓ) *
          Ideal.Quotient.mk (S.Q ^ (N + 1)) (γ ^ n) *
          Ideal.Quotient.mk (S.Q ^ (N + 1)) (u ^ n) := by
  classical
  rw [dworkThetaTrunc, map_sum]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  calc
    Ideal.Quotient.mk (S.Q ^ (N + 1))
        (S.dworkCoeffArtinHasseAtTo γ N n * u ^ n)
        = Ideal.Quotient.mk (S.Q ^ (N + 1))
            (S.dworkCoeffArtinHasseAtTo γ N n) *
          Ideal.Quotient.mk (S.Q ^ (N + 1)) (u ^ n) := by
            simp
    _ =
        (S.rIntegralRatToQuotient N
          (⟨(PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ),
            artinHasseExpSeries_coeff_isRIntegral ℓ n⟩ :
              DieudonneDwork.rIntegralRatSubring ℓ) *
          Ideal.Quotient.mk (S.Q ^ (N + 1)) (γ ^ n)) *
          Ideal.Quotient.mk (S.Q ^ (N + 1)) (u ^ n) := by
            rw [S.quotient_mk_dworkCoeffArtinHasseAtTo_eq_rIntegralRatToQuotient_mul_gamma_pow]
    _ =
        S.rIntegralRatToQuotient N
          (⟨(PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ),
            artinHasseExpSeries_coeff_isRIntegral ℓ n⟩ :
              DieudonneDwork.rIntegralRatSubring ℓ) *
        Ideal.Quotient.mk (S.Q ^ (N + 1)) (γ ^ n) *
        Ideal.Quotient.mk (S.Q ^ (N + 1)) (u ^ n) := by
            ring

/-- Polynomial-evaluation form of the quotient Artin-Hasse theta truncation. -/
theorem quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_trunc_eval
    (γ u : 𝓞 R') (N : ℕ) :
    Ideal.Quotient.mk (S.Q ^ (N + 1))
        (dworkThetaTrunc (S.dworkCoeffArtinHasseAtTo γ N) N u) =
      (PowerSeries.trunc (N + 1)
        ((show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (S.rIntegralRatToQuotient N))).eval₂
        (RingHom.id (𝓞 R' ⧸ S.Q ^ (N + 1)))
        (Ideal.Quotient.mk (S.Q ^ (N + 1)) (γ * u)) := by
  classical
  rw [S.quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_sum_rIntegralRatToQuotient]
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp [map_pow, mul_pow, mul_assoc]

/-- The finite Artin-Hasse exponential at the inverse-series Dwork parameter
is `1 + π` modulo `Q^(N+1)`. -/
theorem quotient_mk_dworkThetaTrunc_artinHasseAtTo_approx_one_eq_one_add_pi
    (N : ℕ) :
    Ideal.Quotient.mk (S.Q ^ (N + 1))
        (dworkThetaTrunc
          (S.dworkCoeffArtinHasseAtTo (S.artinHasseDworkParameterApproxTo N) N) N 1) =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) (1 + S.π) := by
  let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
  let φ : DieudonneDwork.rIntegralRatSubring ℓ →+* A :=
    S.rIntegralRatToQuotient N
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let hInv : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpInverseSeries ℓ) :=
    artinHasseExpInverseSeries_isRIntegral ℓ
  let Eps : PowerSeries A := hE.mapTo φ
  let Ips : PowerSeries A := hInv.mapTo φ
  let πbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π
  let γ : 𝓞 R' := S.artinHasseDworkParameterApproxTo N
  let γbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) γ
  have hπnil : πbar ^ (N + 1) = 0 := by
    simpa [πbar] using quotient_mk_mem_pow_succ_eq_zero S.Q S.π_mem_Q N
  have hγmem : γ ∈ S.Q := by
    simpa [γ] using S.artinHasseDworkParameterApproxTo_mem_Q N
  have hγnil : γbar ^ (N + 1) = 0 := by
    simpa [γbar] using quotient_mk_mem_pow_succ_eq_zero S.Q hγmem N
  have hInvEval :
      γbar = (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar := by
    simpa [γbar, πbar, Ips, hInv, φ] using
      S.quotient_mk_artinHasseDworkParameterApproxTo_eq_trunc_eval N
  have hSubInv :
      PowerSeries.subst (PowerSeries.C πbar) Ips = PowerSeries.C γbar := by
    rw [powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero
      πbar N hπnil Ips]
    rw [← hInvEval]
  have hInv0 : PowerSeries.constantCoeff Ips = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [DieudonneDwork.IsRIntegralPS.coeff_mapTo]
    have hcoeff0 :
        (PowerSeries.coeff (R := ℚ) 0) (artinHasseExpInverseSeries ℓ) = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact artinHasseExpInverseSeries_constantCoeff ℓ
    have hsubzero :
        (⟨(PowerSeries.coeff (R := ℚ) 0) (artinHasseExpInverseSeries ℓ), hInv 0⟩ :
            DieudonneDwork.rIntegralRatSubring ℓ) = 0 := by
      ext
      exact hcoeff0
    rw [hsubzero]
    exact map_zero φ
  have hIpsSubst : PowerSeries.HasSubst Ips :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hInv0
  have hCπSubst : PowerSeries.HasSubst (PowerSeries.C πbar : PowerSeries A) := by
    change IsNilpotent
      (PowerSeries.constantCoeff (PowerSeries.C πbar : PowerSeries A))
    exact ⟨N + 1, by simpa using hπnil⟩
  have hseries :
      PowerSeries.subst Ips Eps = 1 + (PowerSeries.X : PowerSeries A) := by
    simpa [Eps, Ips, hE, hInv, φ] using
      artinHasseExpSeries_mapTo_subst_inverse ℓ φ
  have hcomp :
      PowerSeries.subst (PowerSeries.C γbar) Eps =
        PowerSeries.C (1 + πbar) := by
    calc
      PowerSeries.subst (PowerSeries.C γbar) Eps
          = PowerSeries.subst (PowerSeries.subst (PowerSeries.C πbar) Ips) Eps := by
              rw [hSubInv]
      _ = PowerSeries.subst (PowerSeries.C πbar) (PowerSeries.subst Ips Eps) := by
              rw [← PowerSeries.subst_comp_subst_apply hIpsSubst hCπSubst Eps]
      _ = PowerSeries.subst (PowerSeries.C πbar) (1 + (PowerSeries.X : PowerSeries A)) := by
              rw [hseries]
      _ = PowerSeries.C (1 + πbar) := by
              have hone :
                  PowerSeries.subst (PowerSeries.C πbar) (1 : PowerSeries A) = 1 := by
                simpa using
                  (PowerSeries.subst_C
                    (a := (PowerSeries.C πbar : PowerSeries A)) (r := (1 : A)))
              rw [PowerSeries.subst_add hCπSubst,
                PowerSeries.subst_X hCπSubst, hone]
              simp
  have hthetaEval :
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) γbar = 1 + πbar := by
    have hsubst :=
      powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero
        γbar N hγnil Eps
    apply PowerSeries.C_injective
    rw [← hsubst, hcomp]
  calc
    Ideal.Quotient.mk (S.Q ^ (N + 1))
        (dworkThetaTrunc
          (S.dworkCoeffArtinHasseAtTo (S.artinHasseDworkParameterApproxTo N) N) N 1)
        = (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) γbar := by
            simpa [Eps, hE, φ, γ, γbar, A] using
              S.quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_trunc_eval γ 1 N
    _ = 1 + πbar := hthetaEval
    _ = Ideal.Quotient.mk (S.Q ^ (N + 1)) (1 + S.π) := by
            simp [πbar]

/-- Inverse-series normalization in quotient-series form:
`E_N(E_N^{-1}(π)) = 1 + π`. -/
theorem artinHasseExp_trunc_eval_inverse_trunc_eval_eq_one_add_pi
    (N : ℕ) :
    let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (S.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (S.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π
    (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar) =
      1 + πbar := by
  let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let Eps : PowerSeries A := hE.mapTo (S.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (S.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π
  let γ : 𝓞 R' := S.artinHasseDworkParameterApproxTo N
  have hγ :
      (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar =
        Ideal.Quotient.mk (S.Q ^ (N + 1)) γ := by
    simpa [γ, Ips, πbar, A] using
      (S.quotient_mk_artinHasseDworkParameterApproxTo_eq_trunc_eval N).symm
  calc
    (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar)
        =
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (Ideal.Quotient.mk (S.Q ^ (N + 1)) γ) := by
          rw [hγ]
    _ =
      Ideal.Quotient.mk (S.Q ^ (N + 1))
        (dworkThetaTrunc
          (S.dworkCoeffArtinHasseAtTo (S.artinHasseDworkParameterApproxTo N) N) N 1) := by
          symm
          simpa [Eps, hE, γ, A] using
            S.quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_trunc_eval γ 1 N
    _ = 1 + πbar := by
          simpa [γ, πbar, map_add] using
            S.quotient_mk_dworkThetaTrunc_artinHasseAtTo_approx_one_eq_one_add_pi N

end ConductorFlexibleConcreteStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
