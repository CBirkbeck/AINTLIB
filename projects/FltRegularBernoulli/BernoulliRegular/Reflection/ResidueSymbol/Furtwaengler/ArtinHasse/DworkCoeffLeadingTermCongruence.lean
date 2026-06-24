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
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ArtinHasse.DworkParameterApproxCompatibility

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

/-- The precision-indexed Artin-Hasse coefficient representative is the
quotient value of the `ℓ`-integral rational coefficient times `γ^n`. -/
theorem quotient_mk_dworkCoeffArtinHasseAtTo_eq_rIntegralRatToQuotient_mul_gamma_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
    let q : DieudonneDwork.rIntegralRatSubring ℓ :=
      ⟨c, artinHasseExpSeries_coeff_isRIntegral ℓ n⟩
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (dworkCoeffArtinHasseAtTo S γ N n) =
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
      d * Ideal.Quotient.mk QN (dworkCoeffArtinHasseAtTo S γ N n)
          = Ideal.Quotient.mk QN
              ((c.den : 𝓞 R') * dworkCoeffArtinHasseAtTo S γ N n) := by
            simp [d, QN]
      _ = Ideal.Quotient.mk QN ((c.num : 𝓞 R') * γ ^ n) := by
            simpa [c, QN] using
              quotient_mk_dworkCoeffArtinHasseAtTo_den_mul_eq_num_gamma_pow
                S γ N n
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

theorem dworkCoeffArtinHasseAtTo_one_sub_gamma_mem_Q_cubed
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') :
    dworkCoeffArtinHasseAtTo S γ 2 1 - γ ∈ S.Q ^ 3 := by
  have hcoeff :
      (PowerSeries.coeff (R := ℚ) 1) (artinHasseExpSeries ℓ) = 1 := by
    have hℓ : 1 < ℓ := (Fact.out : Nat.Prime ℓ).one_lt
    simpa using artinHasseExpSeries_coeff_eq_inv_factorial_of_lt ℓ hℓ
  have h :=
    dworkCoeffArtinHasseAtTo_den_mul_sub_num_gamma_pow_mem_Q_pow_succ S γ 2 1
  simpa [hcoeff] using h

theorem two_mul_dworkCoeffArtinHasseAtTo_two_sub_gamma_sq_mem_Q_cubed
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (γ : 𝓞 R') (hℓ : 2 < ℓ) :
    (2 : 𝓞 R') * dworkCoeffArtinHasseAtTo S γ 2 2 - γ ^ 2 ∈ S.Q ^ 3 := by
  let c : ℚ := (PowerSeries.coeff (R := ℚ) 2) (artinHasseExpSeries ℓ)
  have hc : c = (1 : ℚ) / (Nat.factorial 2 : ℚ) := by
    simpa [c] using artinHasseExpSeries_coeff_eq_inv_factorial_of_lt ℓ hℓ
  have hnum : c.num = 1 := by rw [hc]; norm_num
  have hden : c.den = 2 := by rw [hc]; norm_num
  have h :=
    dworkCoeffArtinHasseAtTo_den_mul_sub_num_gamma_pow_mem_Q_pow_succ S γ 2 2
  simpa [c, hnum, hden] using h

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
        simpa [Ideal.IsTwoSided.pow_add] using hmul
      have hright : (γ ^ n - π ^ n) * π ∈ I ^ (n + 2) := by
        have hmul : (γ ^ n - π ^ n) * π ∈ I ^ (n + 1) * I ^ 1 :=
          Ideal.mul_mem_mul ih (by simpa using hπ)
        change (γ ^ n - π ^ n) * π ∈ I ^ ((n + 1) + 1)
        simpa [Ideal.IsTwoSided.pow_add] using hmul
      rw [show γ ^ (n + 1) - π ^ (n + 1) =
          γ ^ n * (γ - π) + (γ ^ n - π ^ n) * π by ring]
      exact (I ^ (n + 2)).add_mem hleft hright

/-- For `n < ℓ`, the chosen Dwork coefficient has leading term `π^n / n!`
modulo `Q^(n+1)`. -/
theorem dworkCoeffArtinHasse_lt_ell_leading
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) (hn : n < ℓ) :
    ((Nat.factorial n : ℕ) : 𝓞 R') * dworkCoeffArtinHasse S n - S.π ^ n
      ∈ S.Q ^ (n + 1) := by
  cases n with
  | zero =>
      simp [dworkCoeffArtinHasse]
  | succ n =>
      let m : ℕ := Nat.succ n
      let c : ℚ := (PowerSeries.coeff (R := ℚ) m) (artinHasseExpSeries ℓ)
      have hc : c = (1 : ℚ) / (Nat.factorial m : ℚ) := by
        simpa [c, m] using artinHasseExpSeries_coeff_eq_inv_factorial_of_lt ℓ hn
      have hnum : c.num = 1 := by rw [hc]; norm_num [Nat.factorial_pos]
      have hden : c.den = Nat.factorial m := by
        rw [hc]; norm_num [Nat.factorial_pos, Nat.factorial_ne_zero]
      have hdenInv :
          ((Nat.factorial m : ℕ) : 𝓞 R') * dworkCoeffArtinHasseDenInv S m - 1 ∈
            S.Q ^ (m + 1) := by
        simpa [c, hden] using dworkCoeffArtinHasseDenInv_spec S m
      have hmul :
          S.π ^ m *
              (((Nat.factorial m : ℕ) : 𝓞 R') *
                  dworkCoeffArtinHasseDenInv S m - 1) ∈
            S.Q ^ (m + 1) :=
        Ideal.mul_mem_left _ _ hdenInv
      convert hmul using 1
      simp [dworkCoeffArtinHasse, dworkCoeffArtinHasseRaw, c, m, hnum]
      ring

/-- For `n < ℓ`, if `γ = π` modulo `Q^2`, the parameterized Dwork coefficient
has the same leading term `π^n / n!` modulo `Q^(n+1)`.  This is the coefficient
API needed for the genuine Dwork splitting parameter. -/
theorem dworkCoeffArtinHasseAt_lt_ell_leading
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') {γ : 𝓞 R'}
    (hγ : γ ∈ S.Q) (hγπ : γ - S.π ∈ S.Q ^ 2) (n : ℕ) (hn : n < ℓ) :
    ((Nat.factorial n : ℕ) : 𝓞 R') * dworkCoeffArtinHasseAt S γ n - S.π ^ n
      ∈ S.Q ^ (n + 1) := by
  cases n with
  | zero =>
      simp [dworkCoeffArtinHasseAt]
  | succ n =>
      let m : ℕ := Nat.succ n
      let c : ℚ := (PowerSeries.coeff (R := ℚ) m) (artinHasseExpSeries ℓ)
      have hc : c = (1 : ℚ) / (Nat.factorial m : ℚ) := by
        simpa [c, m] using artinHasseExpSeries_coeff_eq_inv_factorial_of_lt ℓ hn
      have hnum : c.num = 1 := by rw [hc]; norm_num [Nat.factorial_pos]
      have hden : c.den = Nat.factorial m := by
        rw [hc]; norm_num [Nat.factorial_pos, Nat.factorial_ne_zero]
      have hdenInv :
          ((Nat.factorial m : ℕ) : 𝓞 R') * dworkCoeffArtinHasseDenInv S m - 1 ∈
            S.Q ^ (m + 1) := by
        simpa [c, hden] using dworkCoeffArtinHasseDenInv_spec S m
      have hcoeff_gamma :
          ((Nat.factorial m : ℕ) : 𝓞 R') * dworkCoeffArtinHasseAt S γ m - γ ^ m ∈
            S.Q ^ (m + 1) := by
        have hmul :
            γ ^ m *
                (((Nat.factorial m : ℕ) : 𝓞 R') *
                    dworkCoeffArtinHasseDenInv S m - 1) ∈
              S.Q ^ (m + 1) :=
          Ideal.mul_mem_left _ _ hdenInv
        convert hmul using 1
        simp [dworkCoeffArtinHasseAt, dworkCoeffArtinHasseAtRaw, c, m, hnum]
        ring
      have hpow : γ ^ m - S.π ^ m ∈ S.Q ^ (m + 1) :=
        pow_sub_pow_mem_pow_succ_of_sub_mem_sq (I := S.Q)
          hγ S.π_mem_Q hγπ m
      rw [show ((Nat.factorial m : ℕ) : 𝓞 R') * dworkCoeffArtinHasseAt S γ m -
          S.π ^ m =
            (((Nat.factorial m : ℕ) : 𝓞 R') * dworkCoeffArtinHasseAt S γ m -
              γ ^ m) + (γ ^ m - S.π ^ m) by ring]
      exact (S.Q ^ (m + 1)).add_mem hcoeff_gamma hpow

/-- Precision-indexed leading-term congruence.  The extra hypothesis `n ≤ N`
lets the denominator inverse chosen modulo `Q^(N+1)` be degraded to the
coefficient-level precision `Q^(n+1)`. -/
theorem dworkCoeffArtinHasseAtTo_lt_ell_leading
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') {γ : 𝓞 R'}
    (hγ : γ ∈ S.Q) (hγπ : γ - S.π ∈ S.Q ^ 2)
    (N n : ℕ) (hnN : n ≤ N) (hn : n < ℓ) :
    ((Nat.factorial n : ℕ) : 𝓞 R') * dworkCoeffArtinHasseAtTo S γ N n - S.π ^ n
      ∈ S.Q ^ (n + 1) := by
  cases n with
  | zero =>
      simp [dworkCoeffArtinHasseAtTo]
  | succ n =>
      let m : ℕ := Nat.succ n
      let c : ℚ := (PowerSeries.coeff (R := ℚ) m) (artinHasseExpSeries ℓ)
      have hc : c = (1 : ℚ) / (Nat.factorial m : ℚ) := by
        simpa [c, m] using artinHasseExpSeries_coeff_eq_inv_factorial_of_lt ℓ hn
      have hnum : c.num = 1 := by rw [hc]; norm_num [Nat.factorial_pos]
      have hden : c.den = Nat.factorial m := by
        rw [hc]; norm_num [Nat.factorial_pos, Nat.factorial_ne_zero]
      have hdenInvN :
          ((Nat.factorial m : ℕ) : 𝓞 R') * dworkCoeffArtinHasseDenInvTo S m N - 1 ∈
            S.Q ^ (N + 1) := by
        simpa [c, hden] using dworkCoeffArtinHasseDenInvTo_spec S m N
      have hdenInv :
          ((Nat.factorial m : ℕ) : 𝓞 R') * dworkCoeffArtinHasseDenInvTo S m N - 1 ∈
            S.Q ^ (m + 1) :=
        Ideal.pow_le_pow_right (Nat.succ_le_succ hnN) hdenInvN
      have hcoeff_gamma :
          ((Nat.factorial m : ℕ) : 𝓞 R') * dworkCoeffArtinHasseAtTo S γ N m -
              γ ^ m ∈ S.Q ^ (m + 1) := by
        have hmul :
            γ ^ m *
                (((Nat.factorial m : ℕ) : 𝓞 R') *
                    dworkCoeffArtinHasseDenInvTo S m N - 1) ∈
              S.Q ^ (m + 1) :=
          Ideal.mul_mem_left _ _ hdenInv
        convert hmul using 1
        simp [dworkCoeffArtinHasseAtTo, dworkCoeffArtinHasseAtRawTo, c, m, hnum]
        ring
      have hpow : γ ^ m - S.π ^ m ∈ S.Q ^ (m + 1) :=
        pow_sub_pow_mem_pow_succ_of_sub_mem_sq (I := S.Q)
          hγ S.π_mem_Q hγπ m
      rw [show ((Nat.factorial m : ℕ) : 𝓞 R') * dworkCoeffArtinHasseAtTo S γ N m -
          S.π ^ m =
            (((Nat.factorial m : ℕ) : 𝓞 R') * dworkCoeffArtinHasseAtTo S γ N m -
              γ ^ m) + (γ ^ m - S.π ^ m) by ring]
      exact (S.Q ^ (m + 1)).add_mem hcoeff_gamma hpow

end Furtwaengler

end BernoulliRegular

end
