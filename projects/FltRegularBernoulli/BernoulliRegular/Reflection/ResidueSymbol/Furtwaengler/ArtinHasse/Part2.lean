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
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ArtinHasse.Part1

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

/-- The multiplication form of the Dwork quotient identity transported through
any localized coefficient map. -/
theorem artinHasseExpSeries_pow_mapTo_eq_rescale_exp_mul_subst_X_pow_mapTo
    (r : ℕ) [Fact (Nat.Prime r)] {A : Type*} [CommRing A]
    (φ : DieudonneDwork.rIntegralRatSubring r →+* A) :
    let hE : DieudonneDwork.IsRIntegralPS r (artinHasseExpSeries r) :=
      fun n ↦ artinHasseExpSeries_coeff_isRIntegral r n
    let hRes : DieudonneDwork.IsRIntegralPS r
        (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ)) :=
      rescale_exp_isRIntegral r
    hE.mapTo φ ^ r =
      hRes.mapTo φ *
        PowerSeries.subst ((PowerSeries.X : PowerSeries A) ^ r) (hE.mapTo φ) := by
  classical
  dsimp only
  let hE : DieudonneDwork.IsRIntegralPS r (artinHasseExpSeries r) :=
    fun n ↦ artinHasseExpSeries_coeff_isRIntegral r n
  let hRes : DieudonneDwork.IsRIntegralPS r
      (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ)) :=
    rescale_exp_isRIntegral r
  let hSub : DieudonneDwork.IsRIntegralPS r
      (PowerSeries.subst ((PowerSeries.X : PowerSeries ℚ) ^ r) (artinHasseExpSeries r)) :=
    hE.subst_X_pow (Fact.out : Nat.Prime r).ne_zero
  let hX : DieudonneDwork.IsRIntegralPS r ((PowerSeries.X : PowerSeries ℚ) ^ r) :=
    (DieudonneDwork.IsRIntegralPS.X r).pow r
  have hX0 :
      PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries ℚ) ^ r) = 0 := by
    simp [(Fact.out : Nat.Prime r).ne_zero]
  have hSub_map :
      hSub.mapTo φ =
        PowerSeries.subst ((PowerSeries.X : PowerSeries A) ^ r) (hE.mapTo φ) := by
    calc
      hSub.mapTo φ = (hE.subst hX hX0).mapTo φ :=
        DieudonneDwork.IsRIntegralPS.mapTo_congr_proof φ hSub (hE.subst hX hX0)
      _ = PowerSeries.subst (hX.mapTo φ) (hE.mapTo φ) :=
        DieudonneDwork.IsRIntegralPS.mapTo_subst φ hE hX hX0
      _ = PowerSeries.subst ((PowerSeries.X : PowerSeries A) ^ r) (hE.mapTo φ) := by
        have hXmap :
            hX.mapTo φ = (PowerSeries.X : PowerSeries A) ^ r := by
          calc
            hX.mapTo φ = (DieudonneDwork.IsRIntegralPS.X r).mapTo φ ^ r :=
              DieudonneDwork.IsRIntegralPS.mapTo_pow φ
                (DieudonneDwork.IsRIntegralPS.X r) r
            _ = (PowerSeries.X : PowerSeries A) ^ r := by
              rw [DieudonneDwork.IsRIntegralPS.mapTo_X]
        rw [hXmap]
  have hmap :
      (hE.pow r).mapTo φ = (hRes.mul hSub).mapTo φ :=
    DieudonneDwork.IsRIntegralPS.mapTo_eq_of_eq φ _ _
      (artinHasseExpSeries_pow_eq_rescale_exp_mul_subst_X_pow r)
  calc
    hE.mapTo φ ^ r = (hE.pow r).mapTo φ := by
      rw [DieudonneDwork.IsRIntegralPS.mapTo_pow]
    _ = (hRes.mul hSub).mapTo φ := hmap
    _ = hRes.mapTo φ * hSub.mapTo φ := by
      rw [DieudonneDwork.IsRIntegralPS.mapTo_mul]
    _ = hRes.mapTo φ *
        PowerSeries.subst ((PowerSeries.X : PowerSeries A) ^ r) (hE.mapTo φ) := by
      rw [hSub_map]

theorem artinHasseExpMinusOneSeries_isRIntegral
    (r : ℕ) [Fact (Nat.Prime r)] :
    DieudonneDwork.IsRIntegralPS r (artinHasseExpMinusOneSeries r) := by
  have hE : DieudonneDwork.IsRIntegralPS r (artinHasseExpSeries r) :=
    fun n ↦ artinHasseExpSeries_coeff_isRIntegral r n
  exact hE.sub (DieudonneDwork.IsRIntegralPS.one r)

theorem artinHasseExpSeries_coeff_den_coprime
    (r : ℕ) [Fact (Nat.Prime r)] (n : ℕ) :
    ((PowerSeries.coeff (R := ℚ) n (artinHasseExpSeries r)).den : ℕ).Coprime r :=
  artinHasseExpSeries_coeff_isRIntegral r n

theorem artinHasseExpInverseSeries_isRIntegral
    (r : ℕ) [Fact (Nat.Prime r)] :
    DieudonneDwork.IsRIntegralPS r (artinHasseExpInverseSeries r) := by
  let P : PowerSeries ℚ := artinHasseExpMinusOneSeries r
  have hcoeff : (PowerSeries.coeff (R := ℚ) 1) P = 1 := by
    simp [P]
  letI : Invertible ((PowerSeries.coeff (R := ℚ) 1) P) := by
    rw [hcoeff]
    exact invertibleOfNonzero (by norm_num : (1 : ℚ) ≠ 0)
  have hP : DieudonneDwork.IsRIntegralPS r P := by
    simpa [P] using artinHasseExpMinusOneSeries_isRIntegral r
  have hP0 : PowerSeries.constantCoeff P = 0 := by
    simp [P]
  have hinv :=
    DieudonneDwork.IsRIntegralPS.substInv_of_constantCoeff_zero_coeff_one
      (P := P) hP hP0 hcoeff
  simpa [artinHasseExpInverseSeries, P] using hinv

theorem artinHasseExpInverseSeries_coeff_isRIntegral
    (r : ℕ) [Fact (Nat.Prime r)] (n : ℕ) :
    DieudonneDwork.IsRIntegralRat r
      ((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries r)) :=
  artinHasseExpInverseSeries_isRIntegral r n

theorem artinHasseExpInverseSeries_coeff_den_coprime
    (r : ℕ) [Fact (Nat.Prime r)] (n : ℕ) :
    ((PowerSeries.coeff (R := ℚ) n (artinHasseExpInverseSeries r)).den : ℕ).Coprime r :=
  artinHasseExpInverseSeries_coeff_isRIntegral r n

/-- The formal inverse identity transported through any coefficient map out
of the localized Artin-Hasse coefficient ring. -/
theorem artinHasseExpSeries_mapTo_subst_inverse
    (r : ℕ) [Fact (Nat.Prime r)] {A : Type*} [CommRing A]
    (φ : DieudonneDwork.rIntegralRatSubring r →+* A) :
    PowerSeries.subst
        ((artinHasseExpInverseSeries_isRIntegral r).mapTo φ)
        ((show DieudonneDwork.IsRIntegralPS r (artinHasseExpSeries r) from
          fun n ↦ artinHasseExpSeries_coeff_isRIntegral r n).mapTo φ) =
      1 + (PowerSeries.X : PowerSeries A) := by
  let hE : DieudonneDwork.IsRIntegralPS r (artinHasseExpSeries r) :=
    fun n ↦ artinHasseExpSeries_coeff_isRIntegral r n
  let hInv : DieudonneDwork.IsRIntegralPS r (artinHasseExpInverseSeries r) :=
    artinHasseExpInverseSeries_isRIntegral r
  have hInv0 : PowerSeries.constantCoeff (artinHasseExpInverseSeries r) = 0 :=
    artinHasseExpInverseSeries_constantCoeff r
  calc
    PowerSeries.subst (hInv.mapTo φ) (hE.mapTo φ)
        = (hE.subst hInv hInv0).mapTo φ := by
          rw [hE.mapTo_subst φ hInv hInv0]
    _ =
        ((DieudonneDwork.IsRIntegralPS.one r).add (DieudonneDwork.IsRIntegralPS.X r)).mapTo φ :=
          DieudonneDwork.IsRIntegralPS.mapTo_eq_of_eq φ _ _
            (artinHasseExpSeries_subst_inverse r)
    _ = (DieudonneDwork.IsRIntegralPS.one r).mapTo φ +
          (DieudonneDwork.IsRIntegralPS.X r).mapTo φ := by
          rw [DieudonneDwork.IsRIntegralPS.mapTo_add]
    _ = 1 + (PowerSeries.X : PowerSeries A) := by
          simp

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

omit [Algebra (ZMod ℓ) k] in
/-- The selected prime `Q` is maximal: it is a nonzero prime ideal in the
ring of integers of a number field. -/
theorem Q_isMaximal : S.Q.IsMaximal := by
  haveI : S.Q.IsPrime := S.hQ_prime
  refine Ideal.IsPrime.isMaximal inferInstance ?_
  intro hQ_bot
  have hℓ_zero : (ℓ : 𝓞 R') = 0 := by
    rw [← Ideal.mem_bot, ← hQ_bot]
    exact S.hQ
  have hℓ_ne_zero : (ℓ : 𝓞 R') ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime ℓ).ne_zero
  exact hℓ_ne_zero hℓ_zero

/-- A natural number coprime to `ℓ` is not in the selected prime `Q` above
`ℓ`. -/
theorem natCast_not_mem_Q_of_coprime_ell {m : ℕ} (hm : m.Coprime ℓ) :
    (m : 𝓞 R') ∉ S.Q := by
  classical
  intro hmem
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  have hres : S.residueMap (m : 𝓞 R') = 0 :=
    (S.mem_Q_iff_residueMap_eq_zero (m : 𝓞 R')).1 hmem
  rw [map_natCast] at hres
  have hnot_dvd : ¬ ℓ ∣ m :=
    ((Fact.out : Nat.Prime ℓ).coprime_iff_not_dvd).1 hm.symm
  exact hnot_dvd ((CharP.cast_eq_zero_iff k ℓ m).1 hres)

end ConcreteStickelbergerSetup

private theorem exists_inverse_mod_pow_of_not_mem_maximal
    {A : Type*} [CommRing A] {I : Ideal A} [I.IsMaximal] {x : A} {e : ℕ}
    (he : e ≠ 0) (hx : x ∉ I) :
    ∃ y : A, x * y - 1 ∈ I ^ e := by
  have hunit : IsUnit (Ideal.Quotient.mk (I ^ e) x) :=
    (Ideal.Quotient.isUnit_mk_pow_iff_notMem (I := I) (n := e) he).2 hx
  rcases isUnit_iff_exists.mp hunit with ⟨u, hxu, _hux⟩
  rcases Ideal.Quotient.mk_surjective u with ⟨y, rfl⟩
  refine ⟨y, ?_⟩
  have hzero : Ideal.Quotient.mk (I ^ e) (x * y - 1) = 0 := by
    rw [map_sub, map_mul, hxu, map_one, sub_self]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

/-- The denominator of an `ℓ`-integral rational is a unit modulo every power
of the selected prime `Q`. -/
theorem rIntegralRat_den_isUnit_mod_Q_pow
    (N : ℕ) (q : DieudonneDwork.rIntegralRatSubring ℓ) :
    IsUnit
      (Ideal.Quotient.mk (S.Q ^ (N + 1))
        ((((q : ℚ).den : ℕ) : 𝓞 R'))) := by
  letI : S.Q.IsMaximal := S.Q_isMaximal
  exact
    (Ideal.Quotient.isUnit_mk_pow_iff_notMem (I := S.Q) (n := N + 1)
      (Nat.succ_ne_zero N)).2
      (S.natCast_not_mem_Q_of_coprime_ell
        (show (((q : ℚ).den : ℕ).Coprime ℓ) from q.property))

/-- Value of an `ℓ`-integral rational in `𝓞 R' / Q^(N+1)`, written as
`num * den⁻¹`. -/
noncomputable def rIntegralRatToQuotientVal
    (N : ℕ) (q : DieudonneDwork.rIntegralRatSubring ℓ) :
    𝓞 R' ⧸ S.Q ^ (N + 1) :=
  Ideal.Quotient.mk (S.Q ^ (N + 1)) (((q : ℚ).num : ℤ) : 𝓞 R') *
    ↑(S.rIntegralRat_den_isUnit_mod_Q_pow N q).unit⁻¹

theorem rIntegralRatToQuotientVal_den_mul
    (N : ℕ) (q : DieudonneDwork.rIntegralRatSubring ℓ) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) ((((q : ℚ).den : ℕ) : 𝓞 R')) *
        S.rIntegralRatToQuotientVal N q =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) (((q : ℚ).num : ℤ) : 𝓞 R') := by
  unfold rIntegralRatToQuotientVal
  calc
    Ideal.Quotient.mk (S.Q ^ (N + 1)) ((((q : ℚ).den : ℕ) : 𝓞 R')) *
        (Ideal.Quotient.mk (S.Q ^ (N + 1)) (((q : ℚ).num : ℤ) : 𝓞 R') *
          ↑(S.rIntegralRat_den_isUnit_mod_Q_pow N q).unit⁻¹)
        = Ideal.Quotient.mk (S.Q ^ (N + 1)) (((q : ℚ).num : ℤ) : 𝓞 R') *
          (Ideal.Quotient.mk (S.Q ^ (N + 1)) ((((q : ℚ).den : ℕ) : 𝓞 R')) *
            ↑(S.rIntegralRat_den_isUnit_mod_Q_pow N q).unit⁻¹) := by ring
    _ = Ideal.Quotient.mk (S.Q ^ (N + 1)) (((q : ℚ).num : ℤ) : 𝓞 R') := by
      rw [(S.rIntegralRat_den_isUnit_mod_Q_pow N q).mul_val_inv, mul_one]

/-- The canonical map from `ℓ`-integral rationals to the finite quotient
`𝓞 R' / Q^(N+1)`, obtained by inverting denominators in the quotient. -/
noncomputable def rIntegralRatToQuotient (N : ℕ) :
    DieudonneDwork.rIntegralRatSubring ℓ →+* (𝓞 R' ⧸ S.Q ^ (N + 1)) where
  toFun q := S.rIntegralRatToQuotientVal N q
  map_zero' := by
    simp [rIntegralRatToQuotientVal]
  map_one' := by
    simp [rIntegralRatToQuotientVal]
  map_add' q₁ q₂ := by
    let QN : Ideal (𝓞 R') := S.Q ^ (N + 1)
    let val : DieudonneDwork.rIntegralRatSubring ℓ → 𝓞 R' ⧸ QN :=
      fun q ↦ S.rIntegralRatToQuotientVal N q
    let d₁ : 𝓞 R' ⧸ QN :=
      Ideal.Quotient.mk QN ((((q₁ : ℚ).den : ℕ) : 𝓞 R'))
    let d₂ : 𝓞 R' ⧸ QN :=
      Ideal.Quotient.mk QN ((((q₂ : ℚ).den : ℕ) : 𝓞 R'))
    let D : 𝓞 R' ⧸ QN :=
      Ideal.Quotient.mk QN (((((q₁ + q₂ : DieudonneDwork.rIntegralRatSubring ℓ) :
        ℚ).den : ℕ) : 𝓞 R'))
    let n₁ : 𝓞 R' ⧸ QN :=
      Ideal.Quotient.mk QN ((((q₁ : ℚ).num : ℤ) : 𝓞 R'))
    let n₂ : 𝓞 R' ⧸ QN :=
      Ideal.Quotient.mk QN ((((q₂ : ℚ).num : ℤ) : 𝓞 R'))
    let Num : 𝓞 R' ⧸ QN :=
      Ideal.Quotient.mk QN (((((q₁ + q₂ : DieudonneDwork.rIntegralRatSubring ℓ) :
        ℚ).num : ℤ) : 𝓞 R'))
    have hden₁ : d₁ * val q₁ = n₁ := by
      simpa [QN, val, d₁, n₁] using S.rIntegralRatToQuotientVal_den_mul N q₁
    have hden₂ : d₂ * val q₂ = n₂ := by
      simpa [QN, val, d₂, n₂] using S.rIntegralRatToQuotientVal_den_mul N q₂
    have hden_sum : D * val (q₁ + q₂) = Num := by
      simpa [QN, val, D, Num] using
        S.rIntegralRatToQuotientVal_den_mul N (q₁ + q₂)
    have hcross : Num * d₁ * d₂ = (n₁ * d₂ + n₂ * d₁) * D := by
      simpa [QN, d₁, d₂, D, n₁, n₂, Num, map_mul, map_add, Int.cast_natCast,
        mul_assoc] using
        congrArg
          (fun z : ℤ ↦ Ideal.Quotient.mk QN ((z : ℤ) : 𝓞 R'))
          (Rat.add_num_den' (q₁ : ℚ) (q₂ : ℚ))
    have hunit : IsUnit (d₁ * d₂) :=
      (S.rIntegralRat_den_isUnit_mod_Q_pow N q₁).mul
        (S.rIntegralRat_den_isUnit_mod_Q_pow N q₂)
    change val (q₁ + q₂) = val q₁ + val q₂
    symm
    exact (S.rIntegralRat_den_isUnit_mod_Q_pow N (q₁ + q₂)).mul_left_cancel <| by
      rw [hden_sum]
      exact hunit.mul_left_cancel <| by
        calc
          (d₁ * d₂) * (D * (val q₁ + val q₂))
              = ((d₁ * val q₁) * d₂ + (d₂ * val q₂) * d₁) * D := by ring
          _ = (n₁ * d₂ + n₂ * d₁) * D := by rw [hden₁, hden₂]
          _ = Num * (d₁ * d₂) := by rw [← hcross]; ring
          _ = (d₁ * d₂) * Num := by ring
  map_mul' q₁ q₂ := by
    let QN : Ideal (𝓞 R') := S.Q ^ (N + 1)
    let val : DieudonneDwork.rIntegralRatSubring ℓ → 𝓞 R' ⧸ QN :=
      fun q ↦ S.rIntegralRatToQuotientVal N q
    let d₁ : 𝓞 R' ⧸ QN :=
      Ideal.Quotient.mk QN ((((q₁ : ℚ).den : ℕ) : 𝓞 R'))
    let d₂ : 𝓞 R' ⧸ QN :=
      Ideal.Quotient.mk QN ((((q₂ : ℚ).den : ℕ) : 𝓞 R'))
    let D : 𝓞 R' ⧸ QN :=
      Ideal.Quotient.mk QN (((((q₁ * q₂ : DieudonneDwork.rIntegralRatSubring ℓ) :
        ℚ).den : ℕ) : 𝓞 R'))
    let n₁ : 𝓞 R' ⧸ QN :=
      Ideal.Quotient.mk QN ((((q₁ : ℚ).num : ℤ) : 𝓞 R'))
    let n₂ : 𝓞 R' ⧸ QN :=
      Ideal.Quotient.mk QN ((((q₂ : ℚ).num : ℤ) : 𝓞 R'))
    let Num : 𝓞 R' ⧸ QN :=
      Ideal.Quotient.mk QN (((((q₁ * q₂ : DieudonneDwork.rIntegralRatSubring ℓ) :
        ℚ).num : ℤ) : 𝓞 R'))
    have hden₁ : d₁ * val q₁ = n₁ := by
      simpa [QN, val, d₁, n₁] using S.rIntegralRatToQuotientVal_den_mul N q₁
    have hden₂ : d₂ * val q₂ = n₂ := by
      simpa [QN, val, d₂, n₂] using S.rIntegralRatToQuotientVal_den_mul N q₂
    have hden_mul : D * val (q₁ * q₂) = Num := by
      simpa [QN, val, D, Num] using
        S.rIntegralRatToQuotientVal_den_mul N (q₁ * q₂)
    have hcross : Num * d₁ * d₂ = (n₁ * n₂) * D := by
      simpa [QN, d₁, d₂, D, n₁, n₂, Num, map_mul, Int.cast_natCast,
        mul_assoc] using
        congrArg
          (fun z : ℤ ↦ Ideal.Quotient.mk QN ((z : ℤ) : 𝓞 R'))
          (Rat.mul_num_den' (q₁ : ℚ) (q₂ : ℚ))
    have hunit : IsUnit (d₁ * d₂) :=
      (S.rIntegralRat_den_isUnit_mod_Q_pow N q₁).mul
        (S.rIntegralRat_den_isUnit_mod_Q_pow N q₂)
    change val (q₁ * q₂) = val q₁ * val q₂
    symm
    exact (S.rIntegralRat_den_isUnit_mod_Q_pow N (q₁ * q₂)).mul_left_cancel <| by
      rw [hden_mul]
      exact hunit.mul_left_cancel <| by
        calc
          (d₁ * d₂) * (D * (val q₁ * val q₂))
              = ((d₁ * val q₁) * (d₂ * val q₂)) * D := by ring
          _ = (n₁ * n₂) * D := by rw [hden₁, hden₂]
          _ = Num * (d₁ * d₂) := by rw [← hcross]; ring
          _ = (d₁ * d₂) * Num := by ring

@[simp]
theorem rIntegralRatToQuotient_apply (N : ℕ)
    (q : DieudonneDwork.rIntegralRatSubring ℓ) :
    S.rIntegralRatToQuotient N q = S.rIntegralRatToQuotientVal N q :=
  rfl

theorem rIntegralRatToQuotient_den_mul
    (N : ℕ) (q : DieudonneDwork.rIntegralRatSubring ℓ) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) ((((q : ℚ).den : ℕ) : 𝓞 R')) *
        S.rIntegralRatToQuotient N q =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) (((q : ℚ).num : ℤ) : 𝓞 R') := by
  simpa [rIntegralRatToQuotient_apply] using S.rIntegralRatToQuotientVal_den_mul N q

/-- The finite quotient maps from `ℓ`-integral rationals are compatible under
precision reduction. -/
theorem rIntegralRatToQuotient_factor_comp
    {M N : ℕ} (hMN : M ≤ N) :
    (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))).comp
      (S.rIntegralRatToQuotient N) =
    S.rIntegralRatToQuotient M := by
  ext q
  let φ : 𝓞 R' ⧸ S.Q ^ (N + 1) →+* 𝓞 R' ⧸ S.Q ^ (M + 1) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
  have hN := congrArg φ (S.rIntegralRatToQuotient_den_mul N q)
  have hM := S.rIntegralRatToQuotient_den_mul M q
  apply (S.rIntegralRat_den_isUnit_mod_Q_pow M q).mul_left_cancel
  calc
    Ideal.Quotient.mk (S.Q ^ (M + 1)) ((((q : ℚ).den : ℕ) : 𝓞 R')) *
        φ (S.rIntegralRatToQuotient N q)
        =
          Ideal.Quotient.mk (S.Q ^ (M + 1)) (((q : ℚ).num : ℤ) : 𝓞 R') := by
          simpa [φ, map_mul] using hN
    _ =
        Ideal.Quotient.mk (S.Q ^ (M + 1)) ((((q : ℚ).den : ℕ) : 𝓞 R')) *
          S.rIntegralRatToQuotient M q := hM.symm

/-- Coefficientwise `ℓ`-integral power-series maps are compatible under
precision reduction. -/
theorem isRIntegralPS_mapTo_factor_eq
    {F : PowerSeries ℚ} (hF : DieudonneDwork.IsRIntegralPS ℓ F)
    {M N : ℕ} (hMN : M ≤ N) :
    let φ : 𝓞 R' ⧸ S.Q ^ (N + 1) →+* 𝓞 R' ⧸ S.Q ^ (M + 1) :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
    PowerSeries.map φ (hF.mapTo (S.rIntegralRatToQuotient N)) =
      hF.mapTo (S.rIntegralRatToQuotient M) := by
  dsimp only
  let φ : 𝓞 R' ⧸ S.Q ^ (N + 1) →+* 𝓞 R' ⧸ S.Q ^ (M + 1) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
  calc
    PowerSeries.map φ (hF.mapTo (S.rIntegralRatToQuotient N))
        = hF.mapTo (φ.comp (S.rIntegralRatToQuotient N)) := by
          rw [DieudonneDwork.IsRIntegralPS.map_mapTo]
    _ = hF.mapTo (S.rIntegralRatToQuotient M) := by
          rw [S.rIntegralRatToQuotient_factor_comp hMN]

/-- Finite evaluations of mapped `ℓ`-integral power series are compatible
under precision reduction at nilpotent parameters. -/
theorem isRIntegralPS_trunc_eval₂_factor_eq
    {F : PowerSeries ℚ} (hF : DieudonneDwork.IsRIntegralPS ℓ F)
    {M N : ℕ} (hMN : M ≤ N)
    (zN : 𝓞 R' ⧸ S.Q ^ (N + 1)) (zM : 𝓞 R' ⧸ S.Q ^ (M + 1))
    (hz : (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))) zN = zM)
    (hzM : zM ^ (M + 1) = 0) :
    let φ : 𝓞 R' ⧸ S.Q ^ (N + 1) →+* 𝓞 R' ⧸ S.Q ^ (M + 1) :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
    let FN : PowerSeries (𝓞 R' ⧸ S.Q ^ (N + 1)) :=
      hF.mapTo (S.rIntegralRatToQuotient N)
    let FM : PowerSeries (𝓞 R' ⧸ S.Q ^ (M + 1)) :=
      hF.mapTo (S.rIntegralRatToQuotient M)
    φ ((PowerSeries.trunc (N + 1) FN).eval₂
        (RingHom.id (𝓞 R' ⧸ S.Q ^ (N + 1))) zN) =
      (PowerSeries.trunc (M + 1) FM).eval₂
        (RingHom.id (𝓞 R' ⧸ S.Q ^ (M + 1))) zM := by
  classical
  dsimp only
  let φ : 𝓞 R' ⧸ S.Q ^ (N + 1) →+* 𝓞 R' ⧸ S.Q ^ (M + 1) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
  let FN : PowerSeries (𝓞 R' ⧸ S.Q ^ (N + 1)) :=
    hF.mapTo (S.rIntegralRatToQuotient N)
  let FM : PowerSeries (𝓞 R' ⧸ S.Q ^ (M + 1)) :=
    hF.mapTo (S.rIntegralRatToQuotient M)
  have hmap : PowerSeries.map φ FN = FM := by
    simpa [φ, FN, FM] using S.isRIntegralPS_mapTo_factor_eq hF hMN
  have hcoeff :
      ∀ n : ℕ, φ ((PowerSeries.coeff (R := 𝓞 R' ⧸ S.Q ^ (N + 1)) n) FN) =
        (PowerSeries.coeff (R := 𝓞 R' ⧸ S.Q ^ (M + 1)) n) FM := by
    intro n
    have h := congrArg (fun G : PowerSeries (𝓞 R' ⧸ S.Q ^ (M + 1)) ↦
        (PowerSeries.coeff (R := 𝓞 R' ⧸ S.Q ^ (M + 1)) n) G) hmap
    simpa using h
  have hleft :
      φ ((PowerSeries.trunc (N + 1) FN).eval₂
          (RingHom.id (𝓞 R' ⧸ S.Q ^ (N + 1))) zN) =
        ∑ n ∈ Finset.range (N + 1),
          (PowerSeries.coeff (R := 𝓞 R' ⧸ S.Q ^ (M + 1)) n) FM * zM ^ n := by
    rw [PowerSeries.eval₂_trunc_eq_sum_range]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    calc
      φ ((PowerSeries.coeff (R := 𝓞 R' ⧸ S.Q ^ (N + 1)) n) FN * zN ^ n)
          =
            φ ((PowerSeries.coeff (R := 𝓞 R' ⧸ S.Q ^ (N + 1)) n) FN) *
              φ (zN ^ n) := by
            rw [map_mul]
      _ =
            (PowerSeries.coeff (R := 𝓞 R' ⧸ S.Q ^ (M + 1)) n) FM * zM ^ n := by
            rw [hcoeff n, map_pow, hz]
  have htail :
      ∀ n ∈ Finset.range (N + 1), n ∉ Finset.range (M + 1) →
        (PowerSeries.coeff (R := 𝓞 R' ⧸ S.Q ^ (M + 1)) n) FM * zM ^ n = 0 := by
    intro n _hnN hnM
    have hMn : M + 1 ≤ n := Nat.le_of_not_gt (by simpa using hnM)
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMn
    have hpow : zM ^ (M + 1 + d) = 0 := by
      calc
        zM ^ (M + 1 + d) = zM ^ (M + 1) * zM ^ d :=
          pow_add zM (M + 1) d
        _ = 0 := by
          rw [hzM, zero_mul]
    rw [hpow, mul_zero]
  have hsum :
      ∑ n ∈ Finset.range (N + 1),
          (PowerSeries.coeff (R := 𝓞 R' ⧸ S.Q ^ (M + 1)) n) FM * zM ^ n =
        ∑ n ∈ Finset.range (M + 1),
          (PowerSeries.coeff (R := 𝓞 R' ⧸ S.Q ^ (M + 1)) n) FM * zM ^ n :=
    (Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hMN)) htail).symm
  rw [hleft, hsum, PowerSeries.eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp [FM]

end ConcreteStickelbergerSetup

private theorem artinHasseCoeff_den_not_mem_Q
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) :
    (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).den : 𝓞 R') ∉ S.Q :=
  S.natCast_not_mem_Q_of_coprime_ell
    (artinHasseExpSeries_coeff_den_coprime ℓ n)

private theorem artinHasseInverseCoeff_den_not_mem_Q
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) :
    (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).den : 𝓞 R') ∉
      S.Q :=
  S.natCast_not_mem_Q_of_coprime_ell
    (artinHasseExpInverseSeries_coeff_den_coprime ℓ n)

/-- Existence of an inverse modulo `Q^(n+1)` for the denominator of the
`n`-th Artin-Hasse coefficient. -/
theorem dworkCoeffArtinHasseDenInv_exists
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) :
    ∃ e : 𝓞 R',
      (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).den : 𝓞 R') * e - 1 ∈
        S.Q ^ (n + 1) := by
  letI : S.Q.IsMaximal := S.Q_isMaximal
  exact exists_inverse_mod_pow_of_not_mem_maximal
    (I := S.Q)
    (x := (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).den : 𝓞 R'))
    (e := n + 1) (Nat.succ_ne_zero n) (artinHasseCoeff_den_not_mem_Q S n)

/-- A chosen inverse modulo `Q^(n+1)` of the denominator of the `n`-th
Artin-Hasse coefficient. -/
noncomputable def dworkCoeffArtinHasseDenInv
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) : 𝓞 R' :=
  Classical.choose (dworkCoeffArtinHasseDenInv_exists S n)

/-- The chosen denominator inverse is inverse to the Artin-Hasse coefficient
denominator modulo `Q^(n+1)`. -/
theorem dworkCoeffArtinHasseDenInv_spec
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) :
    (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).den : 𝓞 R') *
        dworkCoeffArtinHasseDenInv S n - 1 ∈ S.Q ^ (n + 1) :=
  by
    simpa [dworkCoeffArtinHasseDenInv] using
      Classical.choose_spec (dworkCoeffArtinHasseDenInv_exists S n)

/-- Precision-indexed inverse modulo `Q^(N+1)` for denominators of the
Artin-Hasse exponential coefficients. -/
theorem dworkCoeffArtinHasseDenInvTo_exists
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n N : ℕ) :
    ∃ e : 𝓞 R',
      (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).den : 𝓞 R') *
          e - 1 ∈ S.Q ^ (N + 1) := by
  letI : S.Q.IsMaximal := S.Q_isMaximal
  exact exists_inverse_mod_pow_of_not_mem_maximal
    (I := S.Q)
    (x := (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).den : 𝓞 R'))
    (e := N + 1) (Nat.succ_ne_zero N) (artinHasseCoeff_den_not_mem_Q S n)

/-- Chosen denominator inverse for the `n`-th Artin-Hasse coefficient, valid
modulo `Q^(N+1)`. -/
noncomputable def dworkCoeffArtinHasseDenInvTo
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n N : ℕ) : 𝓞 R' :=
  Classical.choose (dworkCoeffArtinHasseDenInvTo_exists S n N)

theorem dworkCoeffArtinHasseDenInvTo_spec
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n N : ℕ) :
    (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).den : 𝓞 R') *
        dworkCoeffArtinHasseDenInvTo S n N - 1 ∈ S.Q ^ (N + 1) :=
  by
    simpa [dworkCoeffArtinHasseDenInvTo] using
      Classical.choose_spec (dworkCoeffArtinHasseDenInvTo_exists S n N)

/-- Existence of an inverse modulo `Q^(n+1)` for the denominator of the
`n`-th coefficient of the formal inverse of `E_ℓ(T)-1`. -/
theorem artinHasseInverseCoeffDenInv_exists
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) :
    ∃ e : 𝓞 R',
      (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).den : 𝓞 R') *
          e - 1 ∈ S.Q ^ (n + 1) := by
  letI : S.Q.IsMaximal := S.Q_isMaximal
  exact exists_inverse_mod_pow_of_not_mem_maximal
    (I := S.Q)
    (x := (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).den :
      𝓞 R'))
    (e := n + 1) (Nat.succ_ne_zero n) (artinHasseInverseCoeff_den_not_mem_Q S n)

/-- A chosen inverse modulo `Q^(n+1)` of the denominator of the `n`-th
coefficient of the formal inverse of `E_ℓ(T)-1`. -/
noncomputable def artinHasseInverseCoeffDenInv
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) : 𝓞 R' :=
  Classical.choose (artinHasseInverseCoeffDenInv_exists S n)

/-- The chosen denominator inverse for inverse-series coefficients is inverse
modulo `Q^(n+1)`. -/
theorem artinHasseInverseCoeffDenInv_spec
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) :
    (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).den : 𝓞 R') *
        artinHasseInverseCoeffDenInv S n - 1 ∈ S.Q ^ (n + 1) :=
  by
    simpa [artinHasseInverseCoeffDenInv] using
      Classical.choose_spec (artinHasseInverseCoeffDenInv_exists S n)

/-- Precision-indexed denominator inverse for inverse-series coefficients:
for an `N`-th truncation we need each rational coefficient lifted modulo
`Q^(N+1)`, not merely modulo its own natural order. -/
theorem artinHasseInverseCoeffDenInvTo_exists
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n N : ℕ) :
    ∃ e : 𝓞 R',
      (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).den : 𝓞 R') *
          e - 1 ∈ S.Q ^ (N + 1) := by
  letI : S.Q.IsMaximal := S.Q_isMaximal
  exact exists_inverse_mod_pow_of_not_mem_maximal
    (I := S.Q)
    (x := (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).den :
      𝓞 R'))
    (e := N + 1) (Nat.succ_ne_zero N) (artinHasseInverseCoeff_den_not_mem_Q S n)

/-- Chosen denominator inverse for the `n`-th inverse-series coefficient,
valid modulo `Q^(N+1)`. -/
noncomputable def artinHasseInverseCoeffDenInvTo
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n N : ℕ) : 𝓞 R' :=
  Classical.choose (artinHasseInverseCoeffDenInvTo_exists S n N)

theorem artinHasseInverseCoeffDenInvTo_spec
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n N : ℕ) :
    (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).den : 𝓞 R') *
        artinHasseInverseCoeffDenInvTo S n N - 1 ∈ S.Q ^ (N + 1) :=
  by
    simpa [artinHasseInverseCoeffDenInvTo] using
      Classical.choose_spec (artinHasseInverseCoeffDenInvTo_exists S n N)

/-- Integral `Q`-adic lift of the `n`-th term of
`artinHasseExpInverseSeries ℓ` evaluated at `π = ζ_ℓ - 1`. -/
noncomputable def artinHasseInverseCoeffLift
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) : 𝓞 R' :=
  (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).num : 𝓞 R') *
    S.π ^ n * artinHasseInverseCoeffDenInv S n

theorem artinHasseInverseCoeffLift_mem_Q_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (n : ℕ) :
    artinHasseInverseCoeffLift S n ∈ S.Q ^ n := by
  have hπ : S.π ^ n ∈ S.Q ^ n :=
    Ideal.pow_mem_pow S.π_mem_Q n
  have hnum :
      (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).num :
            𝓞 R') * S.π ^ n ∈ S.Q ^ n :=
    Ideal.mul_mem_left _ _ hπ
  simpa [artinHasseInverseCoeffLift] using
    Ideal.mul_mem_right (artinHasseInverseCoeffDenInv S n) (S.Q ^ n) hnum

@[simp] theorem artinHasseInverseCoeffLift_zero
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') :
    artinHasseInverseCoeffLift S 0 = 0 := by
  simp [artinHasseInverseCoeffLift]

/-- Precision-indexed integral lift of the `n`-th term of
`artinHasseExpInverseSeries ℓ` evaluated at `π`.  The final argument `N`
means the denominator inverse is chosen modulo `Q^(N+1)`. -/
noncomputable def artinHasseInverseCoeffLiftTo
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N n : ℕ) : 𝓞 R' :=
  (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).num : 𝓞 R') *
    S.π ^ n * artinHasseInverseCoeffDenInvTo S n N

theorem artinHasseInverseCoeffLiftTo_mem_Q_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N n : ℕ) :
    artinHasseInverseCoeffLiftTo S N n ∈ S.Q ^ n := by
  have hπ : S.π ^ n ∈ S.Q ^ n :=
    Ideal.pow_mem_pow S.π_mem_Q n
  have hnum :
      (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).num :
            𝓞 R') * S.π ^ n ∈ S.Q ^ n :=
    Ideal.mul_mem_left _ _ hπ
  simpa [artinHasseInverseCoeffLiftTo] using
    Ideal.mul_mem_right (artinHasseInverseCoeffDenInvTo S n N) (S.Q ^ n) hnum

@[simp] theorem artinHasseInverseCoeffLiftTo_zero
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N : ℕ) :
    artinHasseInverseCoeffLiftTo S N 0 = 0 := by
  simp [artinHasseInverseCoeffLiftTo]

/-- Denominator-cleared congruence for the precision-indexed inverse-series
coefficient lift. -/
theorem artinHasseInverseCoeffLiftTo_den_mul_sub_num_pi_pow_mem_Q_pow_succ
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)
    (c.den : 𝓞 R') * artinHasseInverseCoeffLiftTo S N n -
        (c.num : 𝓞 R') * S.π ^ n ∈ S.Q ^ (N + 1) := by
  dsimp only
  let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)
  have hden :
      (c.den : 𝓞 R') * artinHasseInverseCoeffDenInvTo S n N - 1 ∈
        S.Q ^ (N + 1) := by
    simpa [c] using artinHasseInverseCoeffDenInvTo_spec S n N
  have hmul :
      ((c.num : 𝓞 R') * S.π ^ n) *
          ((c.den : 𝓞 R') * artinHasseInverseCoeffDenInvTo S n N - 1) ∈
        S.Q ^ (N + 1) :=
    Ideal.mul_mem_left _ _ hden
  convert hmul using 1
  simp [artinHasseInverseCoeffLiftTo, c]
  ring

/-- Quotient form of
`artinHasseInverseCoeffLiftTo_den_mul_sub_num_pi_pow_mem_Q_pow_succ`. -/
theorem quotient_mk_artinHasseInverseCoeffLiftTo_den_mul_eq_num_pi_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)
    Ideal.Quotient.mk (S.Q ^ (N + 1))
        ((c.den : 𝓞 R') * artinHasseInverseCoeffLiftTo S N n) =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) ((c.num : 𝓞 R') * S.π ^ n) := by
  dsimp only
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact artinHasseInverseCoeffLiftTo_den_mul_sub_num_pi_pow_mem_Q_pow_succ S N n

end Furtwaengler

end BernoulliRegular

end
