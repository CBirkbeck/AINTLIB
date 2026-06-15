module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ConcreteSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DieudonneDwork
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ArtinHasse.Part2

/-!
# Artin-Hasse exponential power series

This file defines the Artin-Hasse log and exponential power series over `ℚ`,
indexed by a prime `r`:

* `artinHasseLogSeries r : PowerSeries ℚ` is `L_r(T) = ∑_{i ≥ 0} T^{r^i} / r^i`.
* `artinHasseExpSeries r : PowerSeries ℚ` is `E_r(T) = exp(L_r(T))`.

The "is a power of `r`" predicate is decidable via `Nat.log`: for `r ≥ 2`,
`n = r^i` for some `i ≥ 0` iff `r ^ Nat.log r n = n ∧ n ≠ 0`. (For `n = 0`,
`r ^ Nat.log r 0 = r ^ 0 = 1 ≠ 0`, so the predicate fails as expected.)

These are the building blocks of the Dwork coefficient sequence used by the
`FullTeichDworkSetup` interface in REF-18 (the project's Φ/Kelly/Furtwängler
route). p-integrality of the Artin-Hasse exponential coefficients (the
substantive Dieudonné-Dwork content) is proved separately.

## References

* Alain M. Robert, *A Course in p-adic Analysis* (GTM 198, Springer 2000),
  §7.1 Definition 1, p. 187.
* Neal Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*
  (GTM 58, Springer 1984), §IV.2 Definition, p. 93.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- The precision-indexed inverse-series coefficient lift is the quotient
value of the corresponding `ℓ`-integral rational coefficient times `π^n`. -/
theorem quotient_mk_artinHasseInverseCoeffLiftTo_eq_rIntegralRatToQuotient_mul_pi_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)
    let q : DieudonneDwork.rIntegralRatSubring ℓ :=
      ⟨c, artinHasseExpInverseSeries_coeff_isRIntegral ℓ n⟩
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (artinHasseInverseCoeffLiftTo S N n) =
      S.rIntegralRatToQuotient N q *
        Ideal.Quotient.mk (S.Q ^ (N + 1)) (S.π ^ n) := by
  dsimp only
  let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)
  let q : DieudonneDwork.rIntegralRatSubring ℓ :=
    ⟨c, artinHasseExpInverseSeries_coeff_isRIntegral ℓ n⟩
  let QN : Ideal (𝓞 R') := S.Q ^ (N + 1)
  let d : 𝓞 R' ⧸ QN :=
    Ideal.Quotient.mk QN (((c.den : ℕ) : 𝓞 R'))
  have hdunit : IsUnit d := by
    simpa [d, q, c, QN] using S.rIntegralRat_den_isUnit_mod_Q_pow N q
  exact hdunit.mul_left_cancel <| by
    calc
      d * Ideal.Quotient.mk QN (artinHasseInverseCoeffLiftTo S N n)
          = Ideal.Quotient.mk QN
              ((c.den : 𝓞 R') * artinHasseInverseCoeffLiftTo S N n) := by
            simp [d, QN]
      _ = Ideal.Quotient.mk QN ((c.num : 𝓞 R') * S.π ^ n) := by
            simpa [c, QN] using
              quotient_mk_artinHasseInverseCoeffLiftTo_den_mul_eq_num_pi_pow S N n
      _ = Ideal.Quotient.mk QN (((q : ℚ).num : ℤ) : 𝓞 R') *
            Ideal.Quotient.mk QN (S.π ^ n) := by
            simp [q, c, QN]
      _ = (d * S.rIntegralRatToQuotient N q) *
            Ideal.Quotient.mk QN (S.π ^ n) := by
            rw [show d * S.rIntegralRatToQuotient N q =
                Ideal.Quotient.mk QN (((q : ℚ).num : ℤ) : 𝓞 R') by
              simpa [d, q, c, QN] using S.rIntegralRatToQuotient_den_mul N q]
      _ = d * (S.rIntegralRatToQuotient N q *
            Ideal.Quotient.mk QN (S.π ^ n)) := by ring

/-- Denominator-cleared congruence for the lifted inverse-series coefficient
evaluated at `π`. -/
theorem artinHasseInverseCoeffLift_den_mul_sub_num_pi_pow_mem_Q_pow_succ
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)
    (c.den : 𝓞 R') * artinHasseInverseCoeffLift S n - (c.num : 𝓞 R') * S.π ^ n ∈
      S.Q ^ (n + 1) := by
  dsimp only
  let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)
  have hden :
      (c.den : 𝓞 R') * artinHasseInverseCoeffDenInv S n - 1 ∈
        S.Q ^ (n + 1) := by
    simpa [c] using artinHasseInverseCoeffDenInv_spec S n
  have hmul :
      ((c.num : 𝓞 R') * S.π ^ n) *
          ((c.den : 𝓞 R') * artinHasseInverseCoeffDenInv S n - 1) ∈
        S.Q ^ (n + 1) :=
    Ideal.mul_mem_left _ _ hden
  convert hmul using 1
  simp [artinHasseInverseCoeffLift, c]
  ring

theorem artinHasseInverseCoeffLift_one_sub_pi_mem_Q_sq
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') :
    artinHasseInverseCoeffLift S 1 - S.π ∈ S.Q ^ 2 := by
  have h :=
    artinHasseInverseCoeffLift_den_mul_sub_num_pi_pow_mem_Q_pow_succ S 1
  simpa using h

/-- Second correction term for the formal Dwork parameter: below the
Artin-Hasse prime degree, the inverse contributes `-π^2/2` modulo `Q^3`. -/
theorem two_mul_artinHasseInverseCoeffLift_two_add_pi_sq_mem_Q_cubed
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (hℓ : 2 < ℓ) :
    (2 : 𝓞 R') * artinHasseInverseCoeffLift S 2 + S.π ^ 2 ∈ S.Q ^ 3 := by
  have hcoeff :
      (PowerSeries.coeff (R := ℚ) 2) (artinHasseExpInverseSeries ℓ) =
        -(1 / 2 : ℚ) :=
    artinHasseExpInverseSeries_coeff_two_of_two_lt ℓ hℓ
  have h :=
    artinHasseInverseCoeffLift_den_mul_sub_num_pi_pow_mem_Q_pow_succ S 2
  have h' :
      (2 : 𝓞 R') * artinHasseInverseCoeffLift S 2 +
          ((Int.sign 2 : ℤ) : 𝓞 R') * S.π ^ 2 ∈ S.Q ^ 3 := by
    simpa [hcoeff] using h
  have hsign : ((Int.sign 2 : ℤ) : 𝓞 R') = 1 := by
    norm_num
  simpa [hsign] using h'

theorem artinHasseInverseCoeffLiftTo_one_sub_pi_mem_Q_cubed
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') :
    artinHasseInverseCoeffLiftTo S 2 1 - S.π ∈ S.Q ^ 3 := by
  have hcoeff :
      (PowerSeries.coeff (R := ℚ) 1) (artinHasseExpInverseSeries ℓ) = 1 :=
    artinHasseExpInverseSeries_coeff_one ℓ
  have h :=
    artinHasseInverseCoeffLiftTo_den_mul_sub_num_pi_pow_mem_Q_pow_succ S 2 1
  simpa [hcoeff] using h

theorem two_mul_artinHasseInverseCoeffLiftTo_two_add_pi_sq_mem_Q_cubed
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (hℓ : 2 < ℓ) :
    (2 : 𝓞 R') * artinHasseInverseCoeffLiftTo S 2 2 + S.π ^ 2 ∈ S.Q ^ 3 := by
  have hcoeff :
      (PowerSeries.coeff (R := ℚ) 2) (artinHasseExpInverseSeries ℓ) =
        -(1 / 2 : ℚ) :=
    artinHasseExpInverseSeries_coeff_two_of_two_lt ℓ hℓ
  have h :=
    artinHasseInverseCoeffLiftTo_den_mul_sub_num_pi_pow_mem_Q_pow_succ S 2 2
  have h' :
      (2 : 𝓞 R') * artinHasseInverseCoeffLiftTo S 2 2 +
          ((Int.sign 2 : ℤ) : 𝓞 R') * S.π ^ 2 ∈ S.Q ^ 3 := by
    simpa [hcoeff] using h
  have hsign : ((Int.sign 2 : ℤ) : 𝓞 R') = 1 := by
    norm_num
  simpa [hsign] using h'

/-- Finite `Q`-adic truncation of the formal Dwork parameter
`(E_ℓ(T)-1)^{-1}(π)`.  This is deliberately finite: the analytic/completion
step is separate from these coefficient-level congruences. -/
noncomputable def artinHasseDworkParameterApprox
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N : ℕ) : 𝓞 R' :=
  ∑ n ∈ Finset.range (N + 1), artinHasseInverseCoeffLift S n

/-- Precision-consistent `N`-th truncation of the formal Dwork parameter:
every coefficient denominator is inverted modulo `Q^(N+1)`. -/
noncomputable def artinHasseDworkParameterApproxTo
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N : ℕ) : 𝓞 R' :=
  ∑ n ∈ Finset.range (N + 1), artinHasseInverseCoeffLiftTo S N n

/-- Quotient form of the finite inverse-series Dwork parameter approximation:
it is the finite evaluation of the formal inverse coefficients at `π`. -/
theorem quotient_mk_artinHasseDworkParameterApproxTo_eq_sum_rIntegralRatToQuotient
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N : ℕ) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (artinHasseDworkParameterApproxTo S N) =
      ∑ n ∈ Finset.range (N + 1),
        S.rIntegralRatToQuotient N
          (⟨(PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ),
            artinHasseExpInverseSeries_coeff_isRIntegral ℓ n⟩ :
              DieudonneDwork.rIntegralRatSubring ℓ) *
          Ideal.Quotient.mk (S.Q ^ (N + 1)) (S.π ^ n) := by
  classical
  rw [artinHasseDworkParameterApproxTo, map_sum]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simpa using
    quotient_mk_artinHasseInverseCoeffLiftTo_eq_rIntegralRatToQuotient_mul_pi_pow
      S N n

/-- Polynomial-evaluation form of
`quotient_mk_artinHasseDworkParameterApproxTo_eq_sum_rIntegralRatToQuotient`. -/
theorem quotient_mk_artinHasseDworkParameterApproxTo_eq_trunc_eval
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N : ℕ) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (artinHasseDworkParameterApproxTo S N) =
      (PowerSeries.trunc (N + 1)
        ((artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
          (S.rIntegralRatToQuotient N))).eval₂
        (RingHom.id (𝓞 R' ⧸ S.Q ^ (N + 1)))
        (Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π) := by
  classical
  rw [quotient_mk_artinHasseDworkParameterApproxTo_eq_sum_rIntegralRatToQuotient]
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp [map_pow]

/-- The finite inverse-series Dwork parameter is compatible under precision
reduction. -/
theorem quotient_mk_artinHasseDworkParameterApproxTo_factor_eq
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') {M N : ℕ} (hMN : M ≤ N) :
    let φ : 𝓞 R' ⧸ S.Q ^ (N + 1) →+* 𝓞 R' ⧸ S.Q ^ (M + 1) :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
    φ (Ideal.Quotient.mk (S.Q ^ (N + 1))
        (artinHasseDworkParameterApproxTo S N)) =
      Ideal.Quotient.mk (S.Q ^ (M + 1))
        (artinHasseDworkParameterApproxTo S M) := by
  classical
  dsimp only
  let φ : 𝓞 R' ⧸ S.Q ^ (N + 1) →+* 𝓞 R' ⧸ S.Q ^ (M + 1) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
  let term : ℕ → 𝓞 R' ⧸ S.Q ^ (M + 1) := fun n =>
    S.rIntegralRatToQuotient M
      (⟨(PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ),
        artinHasseExpInverseSeries_coeff_isRIntegral ℓ n⟩ :
          DieudonneDwork.rIntegralRatSubring ℓ) *
      Ideal.Quotient.mk (S.Q ^ (M + 1)) (S.π ^ n)
  have hcoeff :
      ∀ q : DieudonneDwork.rIntegralRatSubring ℓ,
        φ (S.rIntegralRatToQuotient N q) = S.rIntegralRatToQuotient M q := by
    intro q
    simpa [φ, RingHom.comp_apply] using
      congrArg (fun ψ : DieudonneDwork.rIntegralRatSubring ℓ →+*
          𝓞 R' ⧸ S.Q ^ (M + 1) => ψ q)
        (S.rIntegralRatToQuotient_factor_comp hMN)
  have hN :
      φ (Ideal.Quotient.mk (S.Q ^ (N + 1))
          (artinHasseDworkParameterApproxTo S N)) =
        ∑ n ∈ Finset.range (N + 1), term n := by
    rw [quotient_mk_artinHasseDworkParameterApproxTo_eq_sum_rIntegralRatToQuotient]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    let q : DieudonneDwork.rIntegralRatSubring ℓ :=
      ⟨(PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ),
        artinHasseExpInverseSeries_coeff_isRIntegral ℓ n⟩
    calc
      φ (S.rIntegralRatToQuotient N q *
          Ideal.Quotient.mk (S.Q ^ (N + 1)) (S.π ^ n))
          =
            φ (S.rIntegralRatToQuotient N q) *
              φ (Ideal.Quotient.mk (S.Q ^ (N + 1)) (S.π ^ n)) := by
            rw [map_mul]
      _ =
            S.rIntegralRatToQuotient M q *
              Ideal.Quotient.mk (S.Q ^ (M + 1)) (S.π ^ n) := by
            rw [hcoeff q]
            simp [φ]
      _ = term n := rfl
  have hM :
      Ideal.Quotient.mk (S.Q ^ (M + 1))
          (artinHasseDworkParameterApproxTo S M) =
        ∑ n ∈ Finset.range (M + 1), term n := by
    simpa [term] using
      quotient_mk_artinHasseDworkParameterApproxTo_eq_sum_rIntegralRatToQuotient S M
  have htail :
      ∀ n ∈ Finset.range (N + 1), n ∉ Finset.range (M + 1) → term n = 0 := by
    intro n _hnN hnM
    have hMn : M + 1 ≤ n := Nat.le_of_not_gt (by simpa using hnM)
    have hπ :
        Ideal.Quotient.mk (S.Q ^ (M + 1)) (S.π ^ n) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_le_pow_right hMn (Ideal.pow_mem_pow S.π_mem_Q n)
    change
      S.rIntegralRatToQuotient M
        (⟨(PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ),
          artinHasseExpInverseSeries_coeff_isRIntegral ℓ n⟩ :
            DieudonneDwork.rIntegralRatSubring ℓ) *
        Ideal.Quotient.mk (S.Q ^ (M + 1)) (S.π ^ n) = 0
    rw [hπ, mul_zero]
  have hsum :
      ∑ n ∈ Finset.range (N + 1), term n =
        ∑ n ∈ Finset.range (M + 1), term n :=
    (Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hMN)) htail).symm
  rw [hN, hM, hsum]

theorem artinHasseDworkParameterApprox_mem_Q
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N : ℕ) :
    artinHasseDworkParameterApprox S N ∈ S.Q := by
  classical
  unfold artinHasseDworkParameterApprox
  apply Ideal.sum_mem
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  · exact Ideal.pow_le_self hn0 (artinHasseInverseCoeffLift_mem_Q_pow S n)

theorem artinHasseDworkParameterApproxTo_mem_Q
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N : ℕ) :
    artinHasseDworkParameterApproxTo S N ∈ S.Q := by
  classical
  unfold artinHasseDworkParameterApproxTo
  apply Ideal.sum_mem
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  · exact Ideal.pow_le_self hn0 (artinHasseInverseCoeffLiftTo_mem_Q_pow S N n)

theorem artinHasseDworkParameterApprox_one_sub_pi_mem_Q_sq
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') :
    artinHasseDworkParameterApprox S 1 - S.π ∈ S.Q ^ 2 := by
  have hsum : artinHasseDworkParameterApprox S 1 = artinHasseInverseCoeffLift S 1 := by
    simp [artinHasseDworkParameterApprox, Finset.sum_range_succ]
  simpa [hsum] using artinHasseInverseCoeffLift_one_sub_pi_mem_Q_sq S

theorem artinHasseDworkParameterApproxTo_one_sub_pi_mem_Q_sq
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') :
    artinHasseDworkParameterApproxTo S 1 - S.π ∈ S.Q ^ 2 := by
  have hsum :
      artinHasseDworkParameterApproxTo S 1 = artinHasseInverseCoeffLiftTo S 1 1 := by
    simp [artinHasseDworkParameterApproxTo, Finset.sum_range_succ]
  have hcoeff :
      (PowerSeries.coeff (R := ℚ) 1) (artinHasseExpInverseSeries ℓ) = 1 :=
    artinHasseExpInverseSeries_coeff_one ℓ
  have h :=
    artinHasseInverseCoeffLiftTo_den_mul_sub_num_pi_pow_mem_Q_pow_succ S 1 1
  simpa [hsum, hcoeff] using h

theorem artinHasseInverseCoeffLiftTo_one_sub_pi_mem_Q_sq_of_one_le
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') {N : ℕ} (hN : 1 ≤ N) :
    artinHasseInverseCoeffLiftTo S N 1 - S.π ∈ S.Q ^ 2 := by
  have hcoeff :
      (PowerSeries.coeff (R := ℚ) 1) (artinHasseExpInverseSeries ℓ) = 1 :=
    artinHasseExpInverseSeries_coeff_one ℓ
  have hNprec :
      artinHasseInverseCoeffLiftTo S N 1 - S.π ∈ S.Q ^ (N + 1) := by
    have h :=
      artinHasseInverseCoeffLiftTo_den_mul_sub_num_pi_pow_mem_Q_pow_succ S N 1
    simpa [hcoeff] using h
  exact Ideal.pow_le_pow_right (Nat.succ_le_succ hN) hNprec

theorem artinHasseDworkParameterApproxTo_sub_pi_mem_Q_sq_of_pos
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') {N : ℕ} (hN : 0 < N) :
    artinHasseDworkParameterApproxTo S N - S.π ∈ S.Q ^ 2 := by
  classical
  let f : ℕ → 𝓞 R' := fun n => artinHasseInverseCoeffLiftTo S N n
  have h1N : 1 ≤ N := Nat.succ_le_of_lt hN
  have hmem_one :
      1 ∈ Finset.range (N + 1) := by
    simp only [Finset.mem_range]; omega
  have hsum_indicator :
      (∑ n ∈ Finset.range (N + 1), if n = 1 then S.π else 0) = S.π := by
    rw [Finset.sum_ite_eq']
    simp [hmem_one]
  have hrewrite :
      artinHasseDworkParameterApproxTo S N - S.π =
        ∑ n ∈ Finset.range (N + 1),
          (if n = 1 then f n - S.π else f n) := by
    calc
      artinHasseDworkParameterApproxTo S N - S.π
          = (∑ n ∈ Finset.range (N + 1), f n) -
              ∑ n ∈ Finset.range (N + 1), (if n = 1 then S.π else 0) := by
                simp [artinHasseDworkParameterApproxTo, f, hsum_indicator]
      _ = ∑ n ∈ Finset.range (N + 1),
            (f n - (if n = 1 then S.π else 0)) := by
              rw [Finset.sum_sub_distrib]
      _ = ∑ n ∈ Finset.range (N + 1),
            (if n = 1 then f n - S.π else f n) := by
              refine Finset.sum_congr rfl ?_
              intro n _hn
              by_cases hn1 : n = 1 <;> simp [hn1]
  rw [hrewrite]
  refine Ideal.sum_mem _ ?_
  intro n hn
  by_cases hn1 : n = 1
  · simpa [f, hn1] using
      artinHasseInverseCoeffLiftTo_one_sub_pi_mem_Q_sq_of_one_le S h1N
  · by_cases hn0 : n = 0
    · simp [f, hn0]
    · have hn2 : 2 ≤ n := by omega
      have hfmem : f n ∈ S.Q ^ n := by
        simpa [f] using artinHasseInverseCoeffLiftTo_mem_Q_pow S N n
      simpa [hn1] using Ideal.pow_le_pow_right hn2 hfmem

/-- Second-order expansion of the precision-consistent formal Dwork parameter:
`γ₂ = π - π²/2` modulo `Q^3`, stated without division. -/
theorem two_mul_artinHasseDworkParameterApproxTo_two_sub_pi_add_pi_sq_mem_Q_cubed
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (hℓ : 2 < ℓ) :
    (2 : 𝓞 R') * (artinHasseDworkParameterApproxTo S 2 - S.π) + S.π ^ 2 ∈
      S.Q ^ 3 := by
  have hsum :
      artinHasseDworkParameterApproxTo S 2 =
        artinHasseInverseCoeffLiftTo S 2 1 +
          artinHasseInverseCoeffLiftTo S 2 2 := by
    simp [artinHasseDworkParameterApproxTo, Finset.sum_range_succ]
  have h1 :
      (2 : 𝓞 R') * (artinHasseInverseCoeffLiftTo S 2 1 - S.π) ∈ S.Q ^ 3 :=
    Ideal.mul_mem_left _ _ (artinHasseInverseCoeffLiftTo_one_sub_pi_mem_Q_cubed S)
  have h2 :
      (2 : 𝓞 R') * artinHasseInverseCoeffLiftTo S 2 2 + S.π ^ 2 ∈ S.Q ^ 3 :=
    two_mul_artinHasseInverseCoeffLiftTo_two_add_pi_sq_mem_Q_cubed S hℓ
  rw [hsum]
  rw [show (2 : 𝓞 R') *
        (artinHasseInverseCoeffLiftTo S 2 1 + artinHasseInverseCoeffLiftTo S 2 2 - S.π) +
          S.π ^ 2 =
        (2 : 𝓞 R') * (artinHasseInverseCoeffLiftTo S 2 1 - S.π) +
          ((2 : 𝓞 R') * artinHasseInverseCoeffLiftTo S 2 2 + S.π ^ 2) by ring]
  exact (S.Q ^ 3).add_mem h1 h2

/-- Raw denominator-inverse lift of the coefficient of `E_ℓ(πT)`.  The public
coefficient sequence below pins the constant term exactly and uses this raw
lift from degree `1` onward. -/
noncomputable def dworkCoeffArtinHasseRaw
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) : 𝓞 R' :=
  (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).num : 𝓞 R') *
    S.π ^ n * dworkCoeffArtinHasseDenInv S n

/-- The `Q`-adic Dwork coefficient obtained by substituting `T ↦ πT` in the
Artin-Hasse exponential.  The constant term is fixed exactly as `1`; in degree
at least one, if `c_n = [T^n] E_ℓ(T)`, this is the integral representative of
`c_n · π^n` modulo `Q^(n+1)`, formed by choosing an inverse to `c_n.den`
modulo `Q^(n+1)`. -/
noncomputable def dworkCoeffArtinHasse
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) : 𝓞 R' :=
  match n with
  | 0 => 1
  | Nat.succ n => dworkCoeffArtinHasseRaw S (Nat.succ n)

/-- Raw denominator-inverse lift of the coefficient of `E_ℓ(γT)` for an
arbitrary local Dwork parameter `γ`.  The existing `dworkCoeffArtinHasseRaw`
is the specialization `γ = π`; the parameterized version is needed because
the genuine Dwork splitting parameter has higher `Q`-adic corrections beyond
`π`. -/
noncomputable def dworkCoeffArtinHasseAtRaw
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (n : ℕ) : 𝓞 R' :=
  (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).num : 𝓞 R') *
    γ ^ n * dworkCoeffArtinHasseDenInv S n

/-- Precision-indexed raw lift of the coefficient of `E_ℓ(γT)`.  The
denominator inverse is chosen modulo `Q^(N+1)`, which is the precision needed
by an `N`-th Dwork splitting congruence. -/
noncomputable def dworkCoeffArtinHasseAtRawTo
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (N n : ℕ) : 𝓞 R' :=
  (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).num : 𝓞 R') *
    γ ^ n * dworkCoeffArtinHasseDenInvTo S n N

/-- The denominator-inverse integral representative of the coefficients of
`E_ℓ(γT)`, with constant term fixed exactly as `1`. -/
noncomputable def dworkCoeffArtinHasseAt
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (n : ℕ) : 𝓞 R' :=
  match n with
  | 0 => 1
  | Nat.succ n => dworkCoeffArtinHasseAtRaw S γ (Nat.succ n)

/-- Precision-indexed integral representative of the coefficients of
`E_ℓ(γT)`, with constant term fixed exactly as `1`.  The argument `N` is the
target truncation precision. -/
noncomputable def dworkCoeffArtinHasseAtTo
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (N n : ℕ) : 𝓞 R' :=
  match n with
  | 0 => 1
  | Nat.succ n => dworkCoeffArtinHasseAtRawTo S γ N (Nat.succ n)

@[simp] theorem dworkCoeffArtinHasse_zero
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') :
    dworkCoeffArtinHasse S 0 = 1 := rfl

@[simp] theorem dworkCoeffArtinHasseAt_zero
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') :
    dworkCoeffArtinHasseAt S γ 0 = 1 := rfl

@[simp] theorem dworkCoeffArtinHasseAtTo_zero
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (N : ℕ) :
    dworkCoeffArtinHasseAtTo S γ N 0 = 1 := rfl

/-- The lifted Artin-Hasse Dwork coefficient has `Q`-adic order at least
`n`. -/
theorem dworkCoeffArtinHasse_mem_Q_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) :
    dworkCoeffArtinHasse S n ∈ S.Q ^ n := by
  cases n with
  | zero =>
      simp
  | succ n =>
      let m : ℕ := Nat.succ n
      have hπ : S.π ^ m ∈ S.Q ^ m :=
        Ideal.pow_mem_pow S.π_mem_Q m
      have hnum :
          (((PowerSeries.coeff (R := ℚ) m) (artinHasseExpSeries ℓ)).num :
                𝓞 R') * S.π ^ m ∈ S.Q ^ m :=
        Ideal.mul_mem_left _ _ hπ
      simpa [dworkCoeffArtinHasse, dworkCoeffArtinHasseRaw, m] using
        Ideal.mul_mem_right (dworkCoeffArtinHasseDenInv S m) (S.Q ^ m) hnum

/-- If the parameter `γ` lies in `Q`, the lifted coefficient of `E_ℓ(γT)` has
`Q`-adic order at least `n`. -/
theorem dworkCoeffArtinHasseAt_mem_Q_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') {γ : 𝓞 R'} (hγ : γ ∈ S.Q) (n : ℕ) :
    dworkCoeffArtinHasseAt S γ n ∈ S.Q ^ n := by
  cases n with
  | zero =>
      simp
  | succ n =>
      let m : ℕ := Nat.succ n
      have hγpow : γ ^ m ∈ S.Q ^ m :=
        Ideal.pow_mem_pow hγ m
      have hnum :
          (((PowerSeries.coeff (R := ℚ) m) (artinHasseExpSeries ℓ)).num :
                𝓞 R') * γ ^ m ∈ S.Q ^ m :=
        Ideal.mul_mem_left _ _ hγpow
      simpa [dworkCoeffArtinHasseAt, dworkCoeffArtinHasseAtRaw, m] using
        Ideal.mul_mem_right (dworkCoeffArtinHasseDenInv S m) (S.Q ^ m) hnum

/-- Precision-indexed coefficients of `E_ℓ(γT)` still have `Q`-adic order at
least their degree. -/
theorem dworkCoeffArtinHasseAtTo_mem_Q_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') {γ : 𝓞 R'} (hγ : γ ∈ S.Q)
    (N n : ℕ) :
    dworkCoeffArtinHasseAtTo S γ N n ∈ S.Q ^ n := by
  cases n with
  | zero =>
      simp
  | succ n =>
      let m : ℕ := Nat.succ n
      have hγpow : γ ^ m ∈ S.Q ^ m :=
        Ideal.pow_mem_pow hγ m
      have hnum :
          (((PowerSeries.coeff (R := ℚ) m) (artinHasseExpSeries ℓ)).num :
                𝓞 R') * γ ^ m ∈ S.Q ^ m :=
        Ideal.mul_mem_left _ _ hγpow
      simpa [dworkCoeffArtinHasseAtTo, dworkCoeffArtinHasseAtRawTo, m] using
        Ideal.mul_mem_right (dworkCoeffArtinHasseDenInvTo S m N) (S.Q ^ m) hnum

/-- Denominator-cleared congruence expressing that `dworkCoeffArtinHasse S n`
lifts the coefficient of `E_ℓ(πT)` modulo `Q^(n+1)`. -/
theorem dworkCoeffArtinHasse_den_mul_sub_num_pi_pow_mem_Q_pow_succ
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
    (c.den : 𝓞 R') * dworkCoeffArtinHasse S n - (c.num : 𝓞 R') * S.π ^ n ∈
      S.Q ^ (n + 1) := by
  cases n with
  | zero =>
      dsimp only
      have hc :
          (PowerSeries.coeff (R := ℚ) 0) (artinHasseExpSeries ℓ) = 1 := by
        have hℓ : 0 < ℓ := (Fact.out : Nat.Prime ℓ).pos
        simp [artinHasseExpSeries_coeff_eq_inv_factorial_of_lt ℓ hℓ]
      simp [dworkCoeffArtinHasse, hc]
  | succ n =>
      dsimp only
      let m : ℕ := Nat.succ n
      let c : ℚ := (PowerSeries.coeff (R := ℚ) m) (artinHasseExpSeries ℓ)
      have hden :
          (c.den : 𝓞 R') * dworkCoeffArtinHasseDenInv S m - 1 ∈
            S.Q ^ (m + 1) := by
        simpa [c] using dworkCoeffArtinHasseDenInv_spec S m
      have hmul :
          ((c.num : 𝓞 R') * S.π ^ m) *
              ((c.den : 𝓞 R') * dworkCoeffArtinHasseDenInv S m - 1) ∈
            S.Q ^ (m + 1) :=
        Ideal.mul_mem_left _ _ hden
      convert hmul using 1
      simp [dworkCoeffArtinHasse, dworkCoeffArtinHasseRaw, c, m]
      ring

/-- Denominator-cleared congruence expressing that `dworkCoeffArtinHasseAt S γ n`
lifts the coefficient of `E_ℓ(γT)` modulo `Q^(n+1)`. -/
theorem dworkCoeffArtinHasseAt_den_mul_sub_num_gamma_pow_mem_Q_pow_succ
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
    (c.den : 𝓞 R') * dworkCoeffArtinHasseAt S γ n - (c.num : 𝓞 R') * γ ^ n ∈
      S.Q ^ (n + 1) := by
  cases n with
  | zero =>
      dsimp only
      have hc :
          (PowerSeries.coeff (R := ℚ) 0) (artinHasseExpSeries ℓ) = 1 := by
        have hℓ : 0 < ℓ := (Fact.out : Nat.Prime ℓ).pos
        simp [artinHasseExpSeries_coeff_eq_inv_factorial_of_lt ℓ hℓ]
      simp [dworkCoeffArtinHasseAt, hc]
  | succ n =>
      dsimp only
      let m : ℕ := Nat.succ n
      let c : ℚ := (PowerSeries.coeff (R := ℚ) m) (artinHasseExpSeries ℓ)
      have hden :
          (c.den : 𝓞 R') * dworkCoeffArtinHasseDenInv S m - 1 ∈
            S.Q ^ (m + 1) := by
        simpa [c] using dworkCoeffArtinHasseDenInv_spec S m
      have hmul :
          ((c.num : 𝓞 R') * γ ^ m) *
              ((c.den : 𝓞 R') * dworkCoeffArtinHasseDenInv S m - 1) ∈
            S.Q ^ (m + 1) :=
        Ideal.mul_mem_left _ _ hden
      convert hmul using 1
      simp [dworkCoeffArtinHasseAt, dworkCoeffArtinHasseAtRaw, c, m]
      ring

/-- Denominator-cleared congruence for the precision-indexed coefficients of
`E_ℓ(γT)`, valid at the target precision `Q^(N+1)`. -/
theorem dworkCoeffArtinHasseAtTo_den_mul_sub_num_gamma_pow_mem_Q_pow_succ
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
    (c.den : 𝓞 R') * dworkCoeffArtinHasseAtTo S γ N n - (c.num : 𝓞 R') * γ ^ n ∈
      S.Q ^ (N + 1) := by
  cases n with
  | zero =>
      dsimp only
      have hc :
          (PowerSeries.coeff (R := ℚ) 0) (artinHasseExpSeries ℓ) = 1 := by
        have hℓ : 0 < ℓ := (Fact.out : Nat.Prime ℓ).pos
        simp [artinHasseExpSeries_coeff_eq_inv_factorial_of_lt ℓ hℓ]
      simp [dworkCoeffArtinHasseAtTo, hc]
  | succ n =>
      dsimp only
      let m : ℕ := Nat.succ n
      let c : ℚ := (PowerSeries.coeff (R := ℚ) m) (artinHasseExpSeries ℓ)
      have hden :
          (c.den : 𝓞 R') * dworkCoeffArtinHasseDenInvTo S m N - 1 ∈
            S.Q ^ (N + 1) := by
        simpa [c] using dworkCoeffArtinHasseDenInvTo_spec S m N
      have hmul :
          ((c.num : 𝓞 R') * γ ^ m) *
              ((c.den : 𝓞 R') * dworkCoeffArtinHasseDenInvTo S m N - 1) ∈
            S.Q ^ (N + 1) :=
        Ideal.mul_mem_left _ _ hden
      convert hmul using 1
      simp [dworkCoeffArtinHasseAtTo, dworkCoeffArtinHasseAtRawTo, c, m]
      ring

/-- Stronger precision form of
`dworkCoeffArtinHasseAtTo_den_mul_sub_num_gamma_pow_mem_Q_pow_succ`: if the
parameter lies in `Q`, the factor `γ^n` in the coefficient error supplies
`n` additional `Q`-adic orders. -/
theorem dworkCoeffArtinHasseAtTo_den_mul_sub_num_gamma_pow_mem_Q_pow_succ_add
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') {γ : 𝓞 R'} (hγ : γ ∈ S.Q)
    (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
    (c.den : 𝓞 R') * dworkCoeffArtinHasseAtTo S γ N n - (c.num : 𝓞 R') * γ ^ n ∈
      S.Q ^ (N + 1 + n) := by
  cases n with
  | zero =>
      dsimp only
      have hc :
          (PowerSeries.coeff (R := ℚ) 0) (artinHasseExpSeries ℓ) = 1 := by
        have hℓ : 0 < ℓ := (Fact.out : Nat.Prime ℓ).pos
        simp [artinHasseExpSeries_coeff_eq_inv_factorial_of_lt ℓ hℓ]
      simp [dworkCoeffArtinHasseAtTo, hc]
  | succ n =>
      dsimp only
      let m : ℕ := Nat.succ n
      let c : ℚ := (PowerSeries.coeff (R := ℚ) m) (artinHasseExpSeries ℓ)
      have hden :
          (c.den : 𝓞 R') * dworkCoeffArtinHasseDenInvTo S m N - 1 ∈
            S.Q ^ (N + 1) := by
        simpa [c] using dworkCoeffArtinHasseDenInvTo_spec S m N
      have hγpow : γ ^ m ∈ S.Q ^ m := Ideal.pow_mem_pow hγ m
      have hmul :
          ((c.num : 𝓞 R') * γ ^ m) *
              ((c.den : 𝓞 R') * dworkCoeffArtinHasseDenInvTo S m N - 1) ∈
            S.Q ^ (m + (N + 1)) := by
        have hnumγ : (c.num : 𝓞 R') * γ ^ m ∈ S.Q ^ m :=
          Ideal.mul_mem_left _ _ hγpow
        simpa [pow_add] using Ideal.mul_mem_mul hnumγ hden
      have hmul' :
          ((c.num : 𝓞 R') * γ ^ m) *
              ((c.den : 𝓞 R') * dworkCoeffArtinHasseDenInvTo S m N - 1) ∈
            S.Q ^ (N + 1 + m) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmul
      convert hmul' using 1
      simp [dworkCoeffArtinHasseAtTo, dworkCoeffArtinHasseAtRawTo, c, m]
      ring

/-- Quotient form of
`dworkCoeffArtinHasseAtTo_den_mul_sub_num_gamma_pow_mem_Q_pow_succ`. -/
theorem quotient_mk_dworkCoeffArtinHasseAtTo_den_mul_eq_num_gamma_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
    Ideal.Quotient.mk (S.Q ^ (N + 1))
        ((c.den : 𝓞 R') * dworkCoeffArtinHasseAtTo S γ N n) =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) ((c.num : 𝓞 R') * γ ^ n) := by
  dsimp only
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact dworkCoeffArtinHasseAtTo_den_mul_sub_num_gamma_pow_mem_Q_pow_succ S γ N n

end Furtwaengler

end BernoulliRegular

end
