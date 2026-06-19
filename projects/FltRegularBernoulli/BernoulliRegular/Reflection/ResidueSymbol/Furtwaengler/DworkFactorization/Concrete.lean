module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Basic

/-!
# Concrete Artin-Hasse quotient facts

Split from `DworkFactorization.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

/-- The Artin-Hasse Dwork constant coefficient is congruent to `1` modulo
`Q`. -/
theorem dworkCoeffArtinHasse_zero_sub_one_mem_Q :
    dworkCoeffArtinHasse S 0 - 1 ∈ S.Q := by
  simp

/-- The zero-th theta truncation is congruent to `1` modulo `Q`. -/
theorem dworkThetaTrunc_artinHasse_zero_sub_one_mem_Q (u : 𝓞 R') :
    dworkThetaTrunc (dworkCoeffArtinHasse S) 0 u - 1 ∈ S.Q := by
  simp [dworkThetaTrunc]

/-- The linear Artin-Hasse coefficient is congruent to `π` modulo `Q^2`. -/
theorem dworkCoeffArtinHasse_one_sub_pi_mem_Q_sq :
    dworkCoeffArtinHasse S 1 - S.π ∈ S.Q ^ 2 := by
  have hℓ : 1 < ℓ := (Fact.out : Nat.Prime ℓ).one_lt
  simpa using dworkCoeffArtinHasse_lt_ell_leading S 1 hℓ

/-- The linear parameterized Artin-Hasse coefficient is congruent to `π`
modulo `Q^2` as soon as `γ ≡ π mod Q^2`. -/
theorem dworkCoeffArtinHasseAt_one_sub_pi_mem_Q_sq
    {γ : 𝓞 R'} (hγ : γ ∈ S.Q) (hγπ : γ - S.π ∈ S.Q ^ 2) :
    dworkCoeffArtinHasseAt S γ 1 - S.π ∈ S.Q ^ 2 := by
  have hℓ : 1 < ℓ := (Fact.out : Nat.Prime ℓ).one_lt
  simpa using dworkCoeffArtinHasseAt_lt_ell_leading S hγ hγπ 1 hℓ

/-- The precision-indexed linear parameterized Artin-Hasse coefficient is
congruent to `π` modulo `Q^2` as soon as `γ ≡ π mod Q^2`. -/
theorem dworkCoeffArtinHasseAtTo_one_sub_pi_mem_Q_sq
    {γ : 𝓞 R'} (hγ : γ ∈ S.Q) (hγπ : γ - S.π ∈ S.Q ^ 2)
    {N : ℕ} (hN : 1 ≤ N) :
    dworkCoeffArtinHasseAtTo S γ N 1 - S.π ∈ S.Q ^ 2 := by
  have hℓ : 1 < ℓ := (Fact.out : Nat.Prime ℓ).one_lt
  simpa using dworkCoeffArtinHasseAtTo_lt_ell_leading S hγ hγπ N 1 hN hℓ

/-- The current `E_ℓ(πT)` coefficient source is even more rigid in degree
one: its linear coefficient is `π` modulo `Q^3`.  This is useful diagnostic
information for the all-order splitting step, where the genuine Dwork
parameter must carry higher-order corrections. -/
theorem dworkCoeffArtinHasse_one_sub_pi_mem_Q_cubed :
    dworkCoeffArtinHasse S 1 - S.π ∈ S.Q ^ 3 := by
  have hcoeff :
      (PowerSeries.coeff (R := ℚ) 1) (artinHasseExpSeries ℓ) = 1 := by
    have hℓ : 1 < ℓ := (Fact.out : Nat.Prime ℓ).one_lt
    simpa using artinHasseExpSeries_coeff_eq_inv_factorial_of_lt ℓ hℓ
  have hden :
      dworkCoeffArtinHasseDenInv S 1 - 1 ∈ S.Q ^ 2 := by
    simpa [hcoeff] using dworkCoeffArtinHasseDenInv_spec S 1
  have hπ : S.π ∈ S.Q ^ 1 := by
    simpa using S.π_mem_Q
  have hmul : S.π * (dworkCoeffArtinHasseDenInv S 1 - 1) ∈ S.Q ^ (1 + 2) := by
    have hmul' :
        S.π * (dworkCoeffArtinHasseDenInv S 1 - 1) ∈ S.Q ^ 1 * S.Q ^ 2 :=
      Ideal.mul_mem_mul hπ hden
    rw [← pow_add] at hmul'
    exact hmul'
  convert hmul using 1
  simp [dworkCoeffArtinHasse, dworkCoeffArtinHasseRaw, hcoeff]
  ring

/-- The first Artin-Hasse theta truncation is congruent to `1 + πu` modulo
`Q^2`. -/
theorem dworkThetaTrunc_artinHasse_one_sub_one_add_pi_mul_mem_Q_sq (u : 𝓞 R') :
    dworkThetaTrunc (dworkCoeffArtinHasse S) 1 u - (1 + S.π * u) ∈ S.Q ^ 2 := by
  have hcoeff : dworkCoeffArtinHasse S 1 - S.π ∈ S.Q ^ 2 :=
    S.dworkCoeffArtinHasse_one_sub_pi_mem_Q_sq
  have hmul : (dworkCoeffArtinHasse S 1 - S.π) * u ∈ S.Q ^ 2 :=
    Ideal.mul_mem_right _ _ hcoeff
  convert hmul using 1
  simp [dworkThetaTrunc, Finset.sum_range_succ]
  ring

/-- The first parameterized Artin-Hasse theta truncation is congruent to
`1 + πu` modulo `Q^2`. -/
theorem dworkThetaTrunc_artinHasseAt_one_sub_one_add_pi_mul_mem_Q_sq
    {γ : 𝓞 R'} (hγ : γ ∈ S.Q) (hγπ : γ - S.π ∈ S.Q ^ 2) (u : 𝓞 R') :
    dworkThetaTrunc (dworkCoeffArtinHasseAt S γ) 1 u - (1 + S.π * u) ∈ S.Q ^ 2 := by
  have hcoeff : dworkCoeffArtinHasseAt S γ 1 - S.π ∈ S.Q ^ 2 :=
    S.dworkCoeffArtinHasseAt_one_sub_pi_mem_Q_sq hγ hγπ
  have hmul : (dworkCoeffArtinHasseAt S γ 1 - S.π) * u ∈ S.Q ^ 2 :=
    Ideal.mul_mem_right _ _ hcoeff
  convert hmul using 1
  simp [dworkThetaTrunc, Finset.sum_range_succ]
  ring

/-- The first precision-indexed parameterized Artin-Hasse theta truncation is
congruent to `1 + πu` modulo `Q^2`. -/
theorem dworkThetaTrunc_artinHasseAtTo_one_sub_one_add_pi_mul_mem_Q_sq
    {γ : 𝓞 R'} (hγ : γ ∈ S.Q) (hγπ : γ - S.π ∈ S.Q ^ 2) (u : 𝓞 R') :
    dworkThetaTrunc (dworkCoeffArtinHasseAtTo S γ 1) 1 u - (1 + S.π * u) ∈
      S.Q ^ 2 := by
  have hcoeff : dworkCoeffArtinHasseAtTo S γ 1 1 - S.π ∈ S.Q ^ 2 :=
    S.dworkCoeffArtinHasseAtTo_one_sub_pi_mem_Q_sq hγ hγπ le_rfl
  have hmul : (dworkCoeffArtinHasseAtTo S γ 1 1 - S.π) * u ∈ S.Q ^ 2 :=
    Ideal.mul_mem_right _ _ hcoeff
  convert hmul using 1
  simp [dworkThetaTrunc, Finset.sum_range_succ]
  ring

/-- Any positive precision-indexed parameterized Artin-Hasse theta
truncation has the same first-order reduction modulo `Q^2`. -/
theorem quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_one_add_pi_mul_mod_sq_of_one_le
    {γ : 𝓞 R'} (hγ : γ ∈ S.Q) (hγπ : γ - S.π ∈ S.Q ^ 2)
    {N : ℕ} (hN : 1 ≤ N) (u : 𝓞 R') :
    Ideal.Quotient.mk (S.Q ^ 2)
        (dworkThetaTrunc (dworkCoeffArtinHasseAtTo S γ N) N u) =
      Ideal.Quotient.mk (S.Q ^ 2) (1 + S.π * u) := by
  classical
  let coeff : ℕ → 𝓞 R' := dworkCoeffArtinHasseAtTo S γ N
  have h0mem : 0 ∈ Finset.range (N + 1) := by simp
  have h1lt : 1 < N + 1 := Nat.lt_succ_of_le hN
  have h1mem : 1 ∈ Finset.range (N + 1) \ {0} := by
    simp [h1lt]
  have hcoeff₁ : coeff 1 - S.π ∈ S.Q ^ 2 :=
    S.dworkCoeffArtinHasseAtTo_one_sub_pi_mem_Q_sq hγ hγπ hN
  have hlinear :
      Ideal.Quotient.mk (S.Q ^ 2) (coeff 1 * u) =
        Ideal.Quotient.mk (S.Q ^ 2) (S.π * u) := by
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    have hmul : (coeff 1 - S.π) * u ∈ S.Q ^ 2 :=
      Ideal.mul_mem_right _ _ hcoeff₁
    convert hmul using 1
    ring
  have htail :
      (∑ n ∈ (Finset.range (N + 1) \ {0}) \ {1},
          Ideal.Quotient.mk (S.Q ^ 2) (coeff n * u ^ n)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn_ne1 : n ≠ 1 := by
      have hnot := (Finset.mem_sdiff.mp hn).2
      simpa using hnot
    have hn_mem0 : n ∈ Finset.range (N + 1) \ {0} :=
      (Finset.mem_sdiff.mp hn).1
    have hn_ne0 : n ≠ 0 := by
      have hnot := (Finset.mem_sdiff.mp hn_mem0).2
      simpa using hnot
    have hn2 : 2 ≤ n := by omega
    have hcoeff₂ : coeff n ∈ S.Q ^ 2 :=
      Ideal.pow_le_pow_right hn2
        (dworkCoeffArtinHasseAtTo_mem_Q_pow S hγ N n)
    have hterm : coeff n * u ^ n ∈ S.Q ^ 2 :=
      Ideal.mul_mem_right _ _ hcoeff₂
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hterm
  calc
    Ideal.Quotient.mk (S.Q ^ 2)
        (dworkThetaTrunc (dworkCoeffArtinHasseAtTo S γ N) N u)
        = ∑ n ∈ Finset.range (N + 1),
            Ideal.Quotient.mk (S.Q ^ 2) (coeff n * u ^ n) := by
            simp [dworkThetaTrunc, coeff, map_sum]
    _ =
        Ideal.Quotient.mk (S.Q ^ 2) (coeff 0 * u ^ 0) +
          (Ideal.Quotient.mk (S.Q ^ 2) (coeff 1 * u ^ 1) +
            ∑ n ∈ (Finset.range (N + 1) \ {0}) \ {1},
              Ideal.Quotient.mk (S.Q ^ 2) (coeff n * u ^ n)) := by
            simp only [Finset.sdiff_singleton_eq_erase] at h0mem h1mem ⊢
            rw [← Finset.add_sum_erase _ _ h0mem, ← Finset.add_sum_erase _ _ h1mem]
    _ = Ideal.Quotient.mk (S.Q ^ 2) (1 + S.π * u) := by
            rw [htail]
            simp only [pow_zero, pow_one, mul_one, add_zero]
            rw [hlinear]
            simp [coeff]

/-- Subtraction-form first-order reduction of every positive
precision-indexed parameterized Artin-Hasse theta truncation. -/
theorem dworkThetaTrunc_artinHasseAtTo_sub_one_add_pi_mul_mem_Q_sq_of_one_le
    {γ : 𝓞 R'} (hγ : γ ∈ S.Q) (hγπ : γ - S.π ∈ S.Q ^ 2)
    {N : ℕ} (hN : 1 ≤ N) (u : 𝓞 R') :
    dworkThetaTrunc (dworkCoeffArtinHasseAtTo S γ N) N u - (1 + S.π * u) ∈
      S.Q ^ 2 := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change Ideal.Quotient.mk (S.Q ^ 2)
      (dworkThetaTrunc (dworkCoeffArtinHasseAtTo S γ N) N u - (1 + S.π * u)) = 0
  rw [map_sub,
    quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_one_add_pi_mul_mod_sq_of_one_le
      S hγ hγπ hN u]
  simp

/-- The second precision-indexed parameterized theta truncation, separated
into its linear and quadratic parts modulo `Q^3`. -/
theorem dworkThetaTrunc_artinHasseAtTo_two_sub_one_add_linear_quadratic_mem_Q_cubed
    (γ : 𝓞 R') (u : 𝓞 R') :
    dworkThetaTrunc (dworkCoeffArtinHasseAtTo S γ 2) 2 u -
        (1 + S.π * u +
          ((γ - S.π) * u + dworkCoeffArtinHasseAtTo S γ 2 2 * u ^ 2)) ∈
      S.Q ^ 3 := by
  have hcoeff : dworkCoeffArtinHasseAtTo S γ 2 1 - γ ∈ S.Q ^ 3 :=
    dworkCoeffArtinHasseAtTo_one_sub_gamma_mem_Q_cubed S γ
  have hmul : (dworkCoeffArtinHasseAtTo S γ 2 1 - γ) * u ∈ S.Q ^ 3 :=
    Ideal.mul_mem_right _ _ hcoeff
  convert hmul using 1
  simp [dworkThetaTrunc, Finset.sum_range_succ]
  ring

/-- Quotient form of a precision-indexed one-variable Artin-Hasse theta
truncation. This rewrites the integral coefficient representatives as the
canonical quotient values of the `ℓ`-integral rational Artin-Hasse
coefficients. -/
theorem quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_sum_rIntegralRatToQuotient
    (γ u : 𝓞 R') (N : ℕ) :
    Ideal.Quotient.mk (S.Q ^ (N + 1))
        (dworkThetaTrunc (dworkCoeffArtinHasseAtTo S γ N) N u) =
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
        (dworkCoeffArtinHasseAtTo S γ N n * u ^ n)
        = Ideal.Quotient.mk (S.Q ^ (N + 1))
            (dworkCoeffArtinHasseAtTo S γ N n) *
          Ideal.Quotient.mk (S.Q ^ (N + 1)) (u ^ n) := by
            simp
    _ =
        (S.rIntegralRatToQuotient N
          (⟨(PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ),
            artinHasseExpSeries_coeff_isRIntegral ℓ n⟩ :
              DieudonneDwork.rIntegralRatSubring ℓ) *
          Ideal.Quotient.mk (S.Q ^ (N + 1)) (γ ^ n)) *
          Ideal.Quotient.mk (S.Q ^ (N + 1)) (u ^ n) := by
            rw [quotient_mk_dworkCoeffArtinHasseAtTo_eq_rIntegralRatToQuotient_mul_gamma_pow]
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
        (dworkThetaTrunc (dworkCoeffArtinHasseAtTo S γ N) N u) =
      (PowerSeries.trunc (N + 1)
        ((show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
          fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
            (S.rIntegralRatToQuotient N))).eval₂
        (RingHom.id (𝓞 R' ⧸ S.Q ^ (N + 1)))
        (Ideal.Quotient.mk (S.Q ^ (N + 1)) (γ * u)) := by
  classical
  rw [quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_sum_rIntegralRatToQuotient]
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp [map_pow, mul_pow, mul_assoc]

/-- All-order one-variable normalization for the precision-indexed Dwork
parameter: evaluating the truncated theta series at `u = 1` gives `1 + π`
modulo `Q^(N+1)`. -/
theorem quotient_mk_dworkThetaTrunc_artinHasseAtTo_approx_one_eq_one_add_pi
    (N : ℕ) :
    Ideal.Quotient.mk (S.Q ^ (N + 1))
        (dworkThetaTrunc
          (dworkCoeffArtinHasseAtTo S (artinHasseDworkParameterApproxTo S N) N) N 1) =
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
  let γ : 𝓞 R' := artinHasseDworkParameterApproxTo S N
  let γbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) γ
  have hπnil : πbar ^ (N + 1) = 0 := by
    simpa [πbar] using quotient_mk_mem_pow_succ_eq_zero S.Q S.π_mem_Q N
  have hγmem : γ ∈ S.Q := by
    simpa [γ] using artinHasseDworkParameterApproxTo_mem_Q S N
  have hγnil : γbar ^ (N + 1) = 0 := by
    simpa [γbar] using quotient_mk_mem_pow_succ_eq_zero S.Q hγmem N
  have hInvEval :
      γbar = (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar := by
    simpa [γbar, πbar, Ips, hInv, φ] using
      quotient_mk_artinHasseDworkParameterApproxTo_eq_trunc_eval S N
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
          (dworkCoeffArtinHasseAtTo S (artinHasseDworkParameterApproxTo S N) N) N 1)
        = (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) γbar := by
            simpa [Eps, hE, φ, γ, γbar, A] using
              quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_trunc_eval
                S γ 1 N
    _ = 1 + πbar := hthetaEval
    _ = Ideal.Quotient.mk (S.Q ^ (N + 1)) (1 + S.π) := by
            simp [πbar]

/-- Subtraction-form version of
`quotient_mk_dworkThetaTrunc_artinHasseAtTo_approx_one_eq_one_add_pi`. -/
theorem dworkThetaTrunc_artinHasseAtTo_approx_one_sub_one_add_pi_mem_Q_pow_succ
    (N : ℕ) :
    dworkThetaTrunc
        (dworkCoeffArtinHasseAtTo S (artinHasseDworkParameterApproxTo S N) N) N 1 -
        (1 + S.π) ∈ S.Q ^ (N + 1) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change Ideal.Quotient.mk (S.Q ^ (N + 1))
      (dworkThetaTrunc
        (dworkCoeffArtinHasseAtTo S (artinHasseDworkParameterApproxTo S N) N) N 1 -
        (1 + S.π)) = 0
  rw [map_sub, quotient_mk_dworkThetaTrunc_artinHasseAtTo_approx_one_eq_one_add_pi S N]
  simp

/-- Finite-evaluation form of the Artin-Hasse Dwork recursion in
`𝓞 R' / Q^(N+1)`: evaluating `E_ℓ(T)^ℓ = exp(ℓT) E_ℓ(T^ℓ)` at a nilpotent
element gives the corresponding identity for the finite truncation
evaluations. -/
theorem artinHasseExp_trunc_eval_pow_prime_eq_rescale_exp_trunc_eval_mul_frob
    (N : ℕ) {z : 𝓞 R' ⧸ S.Q ^ (N + 1)} (hz : z ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (S.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo (S.rIntegralRatToQuotient N)
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) z) ^ ℓ =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) z *
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (z ^ ℓ) := by
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (S.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo (S.rIntegralRatToQuotient N)
  have hzpow : (z ^ ℓ) ^ (N + 1) = 0 := by
    rw [← pow_mul]
    have hle : N + 1 ≤ ℓ * (N + 1) :=
      Nat.le_mul_of_pos_left (N + 1) (Fact.out : Nat.Prime ℓ).pos
    exact pow_eq_zero_of_le (a := z) (m := N + 1) (n := ℓ * (N + 1)) hle hz
  have hseries :
      Eps ^ ℓ =
        Rps * PowerSeries.subst ((PowerSeries.X : PowerSeries A) ^ ℓ) Eps := by
    simpa [Eps, Rps, A] using
      artinHasseExpSeries_pow_mapTo_eq_rescale_exp_mul_subst_X_pow_mapTo
        (r := ℓ) (A := A) (S.rIntegralRatToQuotient N)
  calc
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) z) ^ ℓ
        = (PowerSeries.trunc (N + 1) (Eps ^ ℓ)).eval₂ (RingHom.id A) z := by
          rw [powerSeries_trunc_eval₂_pow_of_pow_succ_eq_zero z N hz Eps ℓ]
    _ = (PowerSeries.trunc (N + 1)
          (Rps * PowerSeries.subst ((PowerSeries.X : PowerSeries A) ^ ℓ) Eps)).eval₂
          (RingHom.id A) z := by
          rw [hseries]
    _ = (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) z *
          (PowerSeries.trunc (N + 1)
            (PowerSeries.subst ((PowerSeries.X : PowerSeries A) ^ ℓ) Eps)).eval₂
            (RingHom.id A) z := by
          rw [powerSeries_trunc_eval₂_mul_of_pow_succ_eq_zero z N hz]
    _ = (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) z *
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (z ^ ℓ) := by
          rw [powerSeries_trunc_eval₂_subst_X_pow_of_pow_succ_eq_zero z N ℓ
            (Fact.out : Nat.Prime ℓ).ne_zero hz hzpow Eps]

/-- Ratio-free powered form of the one-step Dwork recursion.  A powered
ordinary correction factor can be absorbed into the corresponding powered
next Artin-Hasse factor, producing the next power of the current
Artin-Hasse factor. -/
theorem rescale_exp_trunc_eval_pow_prime_iterate_mul_frob_eq_eval_pow_succ
    (N q : ℕ) {z : 𝓞 R' ⧸ S.Q ^ (N + 1)} (hz : z ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (S.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo (S.rIntegralRatToQuotient N)
    ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) z) ^ (ℓ ^ q) *
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (z ^ ℓ)) ^ (ℓ ^ q) =
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) z) ^ (ℓ ^ (q + 1)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (S.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo (S.rIntegralRatToQuotient N)
  let e : A := (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) z
  let r : A := (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) z
  let eNext : A := (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (z ^ ℓ)
  have hrec : e ^ ℓ = r * eNext := by
    simpa [A, Eps, Rps, e, r, eNext] using
      S.artinHasseExp_trunc_eval_pow_prime_eq_rescale_exp_trunc_eval_mul_frob
        (N := N) (z := z) hz
  calc
    r ^ (ℓ ^ q) * eNext ^ (ℓ ^ q)
        = (r * eNext) ^ (ℓ ^ q) := by
          rw [mul_pow]
    _ = (e ^ ℓ) ^ (ℓ ^ q) := by
          rw [← hrec]
    _ = e ^ (ℓ ^ (q + 1)) := by
          have hexp : ℓ * ℓ ^ q = ℓ ^ (q + 1) := by
            rw [pow_succ, Nat.mul_comm]
          rw [← pow_mul, hexp]

/-- The finite correction accumulated by iterating the Dwork recursion
`m` times from a quotient parameter `z`. -/
noncomputable def artinHasseExpIterCorrection
    (N : ℕ) (z : 𝓞 R' ⧸ S.Q ^ (N + 1)) : ℕ → 𝓞 R' ⧸ S.Q ^ (N + 1)
  | 0 => 1
  | m + 1 =>
      (artinHasseExpIterCorrection N z m) ^ ℓ *
        (PowerSeries.trunc (N + 1)
          ((rescale_exp_isRIntegral ℓ).mapTo (S.rIntegralRatToQuotient N))).eval₂
            (RingHom.id (𝓞 R' ⧸ S.Q ^ (N + 1))) (z ^ (ℓ ^ m))

/-- Closed product form for the finite correction accumulated by iterating
the one-factor Dwork recursion. -/
theorem artinHasseExpIterCorrection_eq_prod
    (N m : ℕ) (z : 𝓞 R' ⧸ S.Q ^ (N + 1)) :
    let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo (S.rIntegralRatToQuotient N)
    S.artinHasseExpIterCorrection N z m =
      ∏ j ∈ Finset.range m,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (z ^ (ℓ ^ j))) ^ (ℓ ^ (m - 1 - j)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo (S.rIntegralRatToQuotient N)
  let a : ℕ → A := fun j =>
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (z ^ (ℓ ^ j))
  change S.artinHasseExpIterCorrection N z m =
    ∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - 1 - j))
  induction m with
  | zero =>
      simp [artinHasseExpIterCorrection]
  | succ m ih =>
      have hpowprod :
          (∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - 1 - j))) ^ ℓ =
            ∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - j)) := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl ?_
        intro j hj
        have hjlt : j < m := Finset.mem_range.mp hj
        have hexp : ℓ ^ (m - 1 - j) * ℓ = ℓ ^ (m - j) := by
          rw [← pow_succ]
          congr 1
          omega
        rw [← pow_mul, hexp]
      calc
        S.artinHasseExpIterCorrection N z (m + 1)
            = (S.artinHasseExpIterCorrection N z m) ^ ℓ * a m := by
              rfl
        _ =
            (∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - 1 - j))) ^ ℓ * a m := by
              rw [ih]
        _ =
            (∏ j ∈ Finset.range m, a j ^ (ℓ ^ (m - j))) * a m := by
              rw [hpowprod]
        _ =
            ∏ j ∈ Finset.range (m + 1), a j ^ (ℓ ^ (m - j)) := by
              rw [Finset.prod_range_succ]
              simp

/-- Iterated finite Dwork recursion:
`E(z)^(ℓ^m)` equals the accumulated ordinary-exponential correction times
`E(z^(ℓ^m))`. -/
theorem artinHasseExp_trunc_eval_pow_prime_iterate_eq_iterCorrection_mul
    (N m : ℕ) {z : 𝓞 R' ⧸ S.Q ^ (N + 1)} (hz : z ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (S.rIntegralRatToQuotient N)
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) z) ^ (ℓ ^ m) =
      S.artinHasseExpIterCorrection N z m *
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (z ^ (ℓ ^ m)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (S.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo (S.rIntegralRatToQuotient N)
  induction m with
  | zero =>
      simp [artinHasseExpIterCorrection]
  | succ m ih =>
      have hz_iter :
          (z ^ (ℓ ^ m)) ^ (N + 1) = 0 := by
        rw [← pow_mul]
        exact pow_eq_zero_of_le (a := z)
          (m := N + 1)
          (n := ℓ ^ m * (N + 1))
          (Nat.le_mul_of_pos_left _ (Nat.pow_pos (Fact.out : Nat.Prime ℓ).pos))
          hz
      have hrec :=
        S.artinHasseExp_trunc_eval_pow_prime_eq_rescale_exp_trunc_eval_mul_frob
          (N := N) (z := z ^ (ℓ ^ m)) hz_iter
      have hpow :
          (z ^ (ℓ ^ m)) ^ ℓ = z ^ (ℓ ^ (m + 1)) := by
        rw [← pow_mul]
        exact congrArg (fun n : ℕ => z ^ n)
          (by rw [pow_succ] : ℓ ^ m * ℓ = ℓ ^ (m + 1))
      calc
        ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) z) ^ (ℓ ^ (m + 1))
            =
              (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) z) ^
                (ℓ ^ m)) ^ ℓ := by
              rw [← pow_mul]
              exact congrArg
                (fun n : ℕ =>
                  ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) z) ^ n)
                (by rw [pow_succ] : ℓ ^ m * ℓ = ℓ ^ (m + 1))
        _ =
              (S.artinHasseExpIterCorrection N z m *
                (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                  (z ^ (ℓ ^ m))) ^ ℓ := by
              rw [ih]
        _ =
              (S.artinHasseExpIterCorrection N z m) ^ ℓ *
                ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                  (z ^ (ℓ ^ m))) ^ ℓ := by
              rw [mul_pow]
        _ =
              (S.artinHasseExpIterCorrection N z m) ^ ℓ *
                ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                    (z ^ (ℓ ^ m)) *
                  (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                    ((z ^ (ℓ ^ m)) ^ ℓ)) := by
              simpa [A, Eps, Rps] using congrArg
                (fun a : A =>
                  (S.artinHasseExpIterCorrection N z m) ^ ℓ * a)
                hrec
        _ =
              S.artinHasseExpIterCorrection N z (m + 1) *
                (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                  (z ^ (ℓ ^ (m + 1))) := by
              rw [hpow]
              simp [artinHasseExpIterCorrection, Rps, A]
              ring

/-- The finite inverse-series Dwork parameter is nilpotent in
`𝓞 R' / Q^(N+1)`. -/
theorem artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero
    (N : ℕ) :
    let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (S.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π
    ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar) ^ (N + 1) = 0 := by
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (S.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π
  let γ : 𝓞 R' := artinHasseDworkParameterApproxTo S N
  have hγmem : γ ∈ S.Q := by
    simpa [γ] using artinHasseDworkParameterApproxTo_mem_Q S N
  have hγnil :
      (Ideal.Quotient.mk (S.Q ^ (N + 1)) γ : A) ^ (N + 1) = 0 := by
    simpa [A] using quotient_mk_mem_pow_succ_eq_zero S.Q hγmem N
  have hγ :
      (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar =
        Ideal.Quotient.mk (S.Q ^ (N + 1)) γ := by
    simpa [γ, Ips, πbar, A] using
      (quotient_mk_artinHasseDworkParameterApproxTo_eq_trunc_eval S N).symm
  rw [hγ]
  exact hγnil

/-- Multiplying the finite inverse-series Dwork parameter by any quotient
element preserves nilpotence at precision `N+1`. -/
theorem artinHasseExp_inverse_trunc_eval_mul_pow_succ_eq_zero
    (N : ℕ) (u : 𝓞 R' ⧸ S.Q ^ (N + 1)) :
    let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (S.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π
    (((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar) * u) ^
        (N + 1) = 0 := by
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (S.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π
  have hδ :
      ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar) ^
        (N + 1) = 0 := by
    simpa [A, Ips, πbar] using S.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  rw [mul_pow, hδ, zero_mul]

/-- Dwork recursion applied to the actual theta-factor argument
`E_ℓ^{-1}(π) * u`. -/
theorem artinHasseExp_trunc_eval_inverse_mul_pow_prime_eq_rescale_exp_mul_frob
    (N : ℕ) (u : 𝓞 R' ⧸ S.Q ^ (N + 1)) :
    let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (S.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (S.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo (S.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (δ * u)) ^ ℓ =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * u) *
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ((δ * u) ^ ℓ) := by
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (S.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hz : (δ * u) ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      S.artinHasseExp_inverse_trunc_eval_mul_pow_succ_eq_zero N u
  simpa [A, Ips, πbar, δ] using
    S.artinHasseExp_trunc_eval_pow_prime_eq_rescale_exp_trunc_eval_mul_frob
      (N := N) (z := δ * u) hz

/-- Product-level Dwork recursion for a finite family of theta-factor
arguments. -/
theorem artinHasseExp_trunc_eval_inverse_mul_finset_prod_pow_prime_eq
    (N : ℕ) {ι : Type*} (s : Finset ι)
    (u : ι → 𝓞 R' ⧸ S.Q ^ (N + 1)) :
    let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (S.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (S.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo (S.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    (∏ i ∈ s,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (δ * u i)) ^ ℓ =
      (∏ i ∈ s,
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * u i)) *
        ∏ i ∈ s,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ((δ * u i) ^ ℓ) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (S.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (S.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo (S.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  calc
    (∏ i ∈ s,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (δ * u i)) ^ ℓ
        = ∏ i ∈ s,
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) (δ * u i)) ^ ℓ := by
          rw [← Finset.prod_pow]
    _ = ∏ i ∈ s,
          ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * u i) *
            (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ((δ * u i) ^ ℓ)) := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          simpa [A, Eps, Ips, Rps, πbar, δ] using
            S.artinHasseExp_trunc_eval_inverse_mul_pow_prime_eq_rescale_exp_mul_frob
              (N := N) (u := u i)
    _ = (∏ i ∈ s,
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * u i)) *
        ∏ i ∈ s,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ((δ * u i) ^ ℓ) := by
          rw [Finset.prod_mul_distrib]

/-- Quotient form of a corrected Artin-Hasse theta factor with the Dwork
parameter replaced by the finite inverse-series evaluation at `π`. -/
theorem quotient_mk_dworkThetaTrunc_artinHasseAtTo_approx_eq_inverse_trunc_eval
    (N : ℕ) (u : 𝓞 R') :
    let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (S.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (S.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π
    Ideal.Quotient.mk (S.Q ^ (N + 1))
        (dworkThetaTrunc
          (dworkCoeffArtinHasseAtTo S (artinHasseDworkParameterApproxTo S N) N) N u) =
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
          Ideal.Quotient.mk (S.Q ^ (N + 1)) u) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let Eps : PowerSeries A := hE.mapTo (S.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (S.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π
  let γ : 𝓞 R' := artinHasseDworkParameterApproxTo S N
  have hγ :
      Ideal.Quotient.mk (S.Q ^ (N + 1)) γ =
        (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar := by
    simpa [γ, Ips, πbar, A] using
      quotient_mk_artinHasseDworkParameterApproxTo_eq_trunc_eval S N
  have harg :
      Ideal.Quotient.mk (S.Q ^ (N + 1)) (γ * u) =
        (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
          Ideal.Quotient.mk (S.Q ^ (N + 1)) u := by
    rw [map_mul, hγ]
  calc
    Ideal.Quotient.mk (S.Q ^ (N + 1))
        (dworkThetaTrunc
          (dworkCoeffArtinHasseAtTo S (artinHasseDworkParameterApproxTo S N) N) N u)
        = (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (Ideal.Quotient.mk (S.Q ^ (N + 1)) (γ * u)) := by
            simpa [Eps, hE, γ, A] using
              quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_trunc_eval
                S γ u N
    _ = (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
          Ideal.Quotient.mk (S.Q ^ (N + 1)) u) := by
            rw [harg]

/-- Standalone inverse-series normalization in the quotient:
`E_ℓ(E_ℓ^{-1}(π)) = 1 + π` modulo `Q^(N+1)`. -/
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
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let Eps : PowerSeries A := hE.mapTo (S.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (S.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π
  have htheta :
      Ideal.Quotient.mk (S.Q ^ (N + 1))
          (dworkThetaTrunc
            (dworkCoeffArtinHasseAtTo S (artinHasseDworkParameterApproxTo S N) N) N 1) =
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar) := by
    simpa [Eps, Ips, πbar, hE, A] using
      quotient_mk_dworkThetaTrunc_artinHasseAtTo_approx_eq_inverse_trunc_eval
        S N 1
  have hone :
      Ideal.Quotient.mk (S.Q ^ (N + 1))
          (dworkThetaTrunc
            (dworkCoeffArtinHasseAtTo S (artinHasseDworkParameterApproxTo S N) N) N 1) =
        1 + πbar := by
    simpa [πbar, A] using
      quotient_mk_dworkThetaTrunc_artinHasseAtTo_approx_one_eq_one_add_pi S N
  exact htheta.symm.trans hone

end ConcreteStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
