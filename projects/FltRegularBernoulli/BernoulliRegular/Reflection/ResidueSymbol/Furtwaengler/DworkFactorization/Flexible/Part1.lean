module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Concrete

/-!
# Conductor-flexible Artin-Hasse quotient API

This module mirrors the coefficient and finite-quotient API used by the exact
`ConcreteStickelbergerSetup`, but for the conductor-flexible setup structures.
The point is to keep the Artin-Hasse/Dwork finite-product statements available
without reintroducing a pair-cyclotomic typeclass assumption on the target
field.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

private theorem exists_inverse_mod_pow_of_not_mem_maximal_flexible
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

namespace ConductorFlexibleConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R')

omit [Algebra (ZMod ℓ) k] in
/-- The selected prime `Q` is maximal. -/
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

/-- A natural number coprime to `ℓ` is not in the selected prime `Q`. -/
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

omit [Algebra (ZMod ℓ) k] in
/-- The rational prime `ℓ` lies in the selected prime ideal. -/
theorem ell_mem_Q : (ℓ : 𝓞 R') ∈ S.Q :=
  S.hQ

omit [Algebra (ZMod ℓ) k] in
/-- Powers of `ℓ` land in the corresponding powers of `Q`. -/
theorem natCast_ell_pow_mem_Q_pow (N : ℕ) :
    (ℓ : 𝓞 R') ^ N ∈ S.Q ^ N :=
  Ideal.pow_mem_pow S.hQ N

omit [Algebra (ZMod ℓ) k] in
/-- Elements outside `Q` become units modulo every positive power of `Q`. -/
theorem quotient_mk_isUnit_of_not_mem_Q (N : ℕ) {s : 𝓞 R'} (hs : s ∉ S.Q) :
    IsUnit (Ideal.Quotient.mk (S.Q ^ (N + 1)) s) := by
  haveI : S.Q.IsMaximal := S.Q_isMaximal
  exact (Ideal.Quotient.isUnit_mk_pow_iff_notMem (I := S.Q)
    (n := N + 1) (Nat.succ_ne_zero N)).2 hs

/-- The canonical unit in `𝓞 R' / Q^(N+1)` attached to an element outside
`Q`. -/
noncomputable def quotientUnitOfNotMemQ
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) : (𝓞 R' ⧸ S.Q ^ (N + 1))ˣ :=
  (S.quotient_mk_isUnit_of_not_mem_Q N hs).unit

omit [Algebra (ZMod ℓ) k] in
@[simp]
theorem quotientUnitOfNotMemQ_coe (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) :
    (S.quotientUnitOfNotMemQ N s hs : 𝓞 R' ⧸ S.Q ^ (N + 1)) =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) s :=
  (S.quotient_mk_isUnit_of_not_mem_Q N hs).unit_spec

/-- The chosen inverse of an element outside `Q` in the quotient by
`Q^(N+1)`. -/
noncomputable def quotientInvOfNotMemQ
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) : 𝓞 R' ⧸ S.Q ^ (N + 1) :=
  ((S.quotientUnitOfNotMemQ N s hs)⁻¹ : (𝓞 R' ⧸ S.Q ^ (N + 1))ˣ)

omit [Algebra (ZMod ℓ) k] in
@[simp]
theorem quotient_mk_mul_quotientInvOfNotMemQ
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) s *
        S.quotientInvOfNotMemQ N s hs = 1 := by
  simp [quotientInvOfNotMemQ]

omit [Algebra (ZMod ℓ) k] in
@[simp]
theorem quotientInvOfNotMemQ_mul_quotient_mk
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) :
    S.quotientInvOfNotMemQ N s hs *
        Ideal.Quotient.mk (S.Q ^ (N + 1)) s = 1 := by
  simp [quotientInvOfNotMemQ]

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

/-- The canonical map from `ℓ`-integral rationals to the finite quotient. -/
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
      fun q => S.rIntegralRatToQuotientVal N q
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
          (fun z : ℤ => Ideal.Quotient.mk QN ((z : ℤ) : 𝓞 R'))
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
      fun q => S.rIntegralRatToQuotientVal N q
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
          (fun z : ℤ => Ideal.Quotient.mk QN ((z : ℤ) : 𝓞 R'))
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

/-- Precision-reduction compatibility for the quotient coefficient maps. -/
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

private theorem artinHasseCoeff_den_not_mem_Q (n : ℕ) :
    (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).den : 𝓞 R') ∉ S.Q :=
  S.natCast_not_mem_Q_of_coprime_ell
    (artinHasseExpSeries_coeff_den_coprime ℓ n)

private theorem artinHasseInverseCoeff_den_not_mem_Q (n : ℕ) :
    (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).den : 𝓞 R') ∉
      S.Q :=
  S.natCast_not_mem_Q_of_coprime_ell
    (artinHasseExpInverseSeries_coeff_den_coprime ℓ n)

/-- Precision-indexed inverse modulo `Q^(N+1)` for Artin-Hasse denominators. -/
theorem dworkCoeffArtinHasseDenInvTo_exists (n N : ℕ) :
    ∃ e : 𝓞 R',
      (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).den : 𝓞 R') *
          e - 1 ∈ S.Q ^ (N + 1) := by
  letI : S.Q.IsMaximal := S.Q_isMaximal
  exact exists_inverse_mod_pow_of_not_mem_maximal_flexible
    (I := S.Q)
    (x := (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).den : 𝓞 R'))
    (e := N + 1) (Nat.succ_ne_zero N) (S.artinHasseCoeff_den_not_mem_Q n)

/-- Chosen denominator inverse for the `n`-th Artin-Hasse coefficient,
valid modulo `Q^(N+1)`. -/
noncomputable def dworkCoeffArtinHasseDenInvTo (n N : ℕ) : 𝓞 R' :=
  Classical.choose (S.dworkCoeffArtinHasseDenInvTo_exists n N)

theorem dworkCoeffArtinHasseDenInvTo_spec (n N : ℕ) :
    (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).den : 𝓞 R') *
        S.dworkCoeffArtinHasseDenInvTo n N - 1 ∈ S.Q ^ (N + 1) :=
  by
    simpa [dworkCoeffArtinHasseDenInvTo] using
      Classical.choose_spec (S.dworkCoeffArtinHasseDenInvTo_exists n N)

/-- Precision-indexed denominator inverse for inverse-series coefficients. -/
theorem artinHasseInverseCoeffDenInvTo_exists (n N : ℕ) :
    ∃ e : 𝓞 R',
      (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).den : 𝓞 R') *
          e - 1 ∈ S.Q ^ (N + 1) := by
  letI : S.Q.IsMaximal := S.Q_isMaximal
  exact exists_inverse_mod_pow_of_not_mem_maximal_flexible
    (I := S.Q)
    (x := (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).den :
      𝓞 R'))
    (e := N + 1) (Nat.succ_ne_zero N) (S.artinHasseInverseCoeff_den_not_mem_Q n)

/-- Chosen denominator inverse for the `n`-th inverse-series coefficient,
valid modulo `Q^(N+1)`. -/
noncomputable def artinHasseInverseCoeffDenInvTo (n N : ℕ) : 𝓞 R' :=
  Classical.choose (S.artinHasseInverseCoeffDenInvTo_exists n N)

theorem artinHasseInverseCoeffDenInvTo_spec (n N : ℕ) :
    (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).den : 𝓞 R') *
        S.artinHasseInverseCoeffDenInvTo n N - 1 ∈ S.Q ^ (N + 1) :=
  by
    simpa [artinHasseInverseCoeffDenInvTo] using
      Classical.choose_spec (S.artinHasseInverseCoeffDenInvTo_exists n N)

/-- Precision-indexed lift of the inverse-series coefficient evaluated at
`π`. -/
noncomputable def artinHasseInverseCoeffLiftTo (N n : ℕ) : 𝓞 R' :=
  (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).num : 𝓞 R') *
    S.π ^ n * S.artinHasseInverseCoeffDenInvTo n N

theorem artinHasseInverseCoeffLiftTo_mem_Q_pow (N n : ℕ) :
    S.artinHasseInverseCoeffLiftTo N n ∈ S.Q ^ n := by
  have hπ : S.π ^ n ∈ S.Q ^ n :=
    Ideal.pow_mem_pow S.π_mem_Q n
  have hnum :
      (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)).num :
            𝓞 R') * S.π ^ n ∈ S.Q ^ n :=
    Ideal.mul_mem_left _ _ hπ
  simpa [artinHasseInverseCoeffLiftTo] using
    Ideal.mul_mem_right (S.artinHasseInverseCoeffDenInvTo n N) (S.Q ^ n) hnum

@[simp] theorem artinHasseInverseCoeffLiftTo_zero (N : ℕ) :
    S.artinHasseInverseCoeffLiftTo N 0 = 0 := by
  simp [artinHasseInverseCoeffLiftTo]

/-- Denominator-cleared congruence for the precision-indexed inverse-series
coefficient lift. -/
theorem artinHasseInverseCoeffLiftTo_den_mul_sub_num_pi_pow_mem_Q_pow_succ
    (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)
    (c.den : 𝓞 R') * S.artinHasseInverseCoeffLiftTo N n -
        (c.num : 𝓞 R') * S.π ^ n ∈ S.Q ^ (N + 1) := by
  dsimp only
  let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)
  have hden :
      (c.den : 𝓞 R') * S.artinHasseInverseCoeffDenInvTo n N - 1 ∈
        S.Q ^ (N + 1) := by
    simpa [c] using S.artinHasseInverseCoeffDenInvTo_spec n N
  have hmul :
      ((c.num : 𝓞 R') * S.π ^ n) *
          ((c.den : 𝓞 R') * S.artinHasseInverseCoeffDenInvTo n N - 1) ∈
        S.Q ^ (N + 1) :=
    Ideal.mul_mem_left _ _ hden
  convert hmul using 1
  simp [artinHasseInverseCoeffLiftTo, c]
  ring

/-- Quotient form of the inverse-series coefficient lift. -/
theorem quotient_mk_artinHasseInverseCoeffLiftTo_den_mul_eq_num_pi_pow
    (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)
    Ideal.Quotient.mk (S.Q ^ (N + 1))
        ((c.den : 𝓞 R') * S.artinHasseInverseCoeffLiftTo N n) =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) ((c.num : 𝓞 R') * S.π ^ n) := by
  dsimp only
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact S.artinHasseInverseCoeffLiftTo_den_mul_sub_num_pi_pow_mem_Q_pow_succ N n

/-- The precision-indexed inverse-series coefficient lift is the quotient
value of the corresponding rational coefficient times `π^n`. -/
theorem quotient_mk_artinHasseInverseCoeffLiftTo_eq_rIntegralRatToQuotient_mul_pi_pow
    (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpInverseSeries ℓ)
    let q : DieudonneDwork.rIntegralRatSubring ℓ :=
      ⟨c, artinHasseExpInverseSeries_coeff_isRIntegral ℓ n⟩
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (S.artinHasseInverseCoeffLiftTo N n) =
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
      d * Ideal.Quotient.mk QN (S.artinHasseInverseCoeffLiftTo N n)
          = Ideal.Quotient.mk QN
              ((c.den : 𝓞 R') * S.artinHasseInverseCoeffLiftTo N n) := by
            simp [d, QN]
      _ = Ideal.Quotient.mk QN ((c.num : 𝓞 R') * S.π ^ n) := by
            simpa [c, QN] using
              S.quotient_mk_artinHasseInverseCoeffLiftTo_den_mul_eq_num_pi_pow N n
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

/-- Finite `Q`-adic truncation of the formal Dwork inverse parameter. -/
noncomputable def artinHasseDworkParameterApproxTo (N : ℕ) : 𝓞 R' :=
  ∑ n ∈ Finset.range (N + 1), S.artinHasseInverseCoeffLiftTo N n

/-- Quotient sum form of the finite inverse-series Dwork parameter. -/
theorem quotient_mk_artinHasseDworkParameterApproxTo_eq_sum_rIntegralRatToQuotient
    (N : ℕ) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (S.artinHasseDworkParameterApproxTo N) =
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
    S.quotient_mk_artinHasseInverseCoeffLiftTo_eq_rIntegralRatToQuotient_mul_pi_pow
      N n

/-- Polynomial-evaluation form of the finite inverse-series Dwork parameter. -/
theorem quotient_mk_artinHasseDworkParameterApproxTo_eq_trunc_eval
    (N : ℕ) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (S.artinHasseDworkParameterApproxTo N) =
      (PowerSeries.trunc (N + 1)
        ((artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
          (S.rIntegralRatToQuotient N))).eval₂
        (RingHom.id (𝓞 R' ⧸ S.Q ^ (N + 1)))
        (Ideal.Quotient.mk (S.Q ^ (N + 1)) S.π) := by
  classical
  rw [S.quotient_mk_artinHasseDworkParameterApproxTo_eq_sum_rIntegralRatToQuotient]
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp [map_pow]

/-- The finite inverse-series Dwork parameter is compatible under precision
reduction. -/
theorem quotient_mk_artinHasseDworkParameterApproxTo_factor_eq
    {M N : ℕ} (hMN : M ≤ N) :
    let φ : 𝓞 R' ⧸ S.Q ^ (N + 1) →+* 𝓞 R' ⧸ S.Q ^ (M + 1) :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))
    φ (Ideal.Quotient.mk (S.Q ^ (N + 1))
        (S.artinHasseDworkParameterApproxTo N)) =
      Ideal.Quotient.mk (S.Q ^ (M + 1))
        (S.artinHasseDworkParameterApproxTo M) := by
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
          (S.artinHasseDworkParameterApproxTo N)) =
        ∑ n ∈ Finset.range (N + 1), term n := by
    rw [S.quotient_mk_artinHasseDworkParameterApproxTo_eq_sum_rIntegralRatToQuotient]
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
          (S.artinHasseDworkParameterApproxTo M) =
        ∑ n ∈ Finset.range (M + 1), term n := by
    simpa [term] using
      S.quotient_mk_artinHasseDworkParameterApproxTo_eq_sum_rIntegralRatToQuotient M
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

theorem artinHasseDworkParameterApproxTo_mem_Q (N : ℕ) :
    S.artinHasseDworkParameterApproxTo N ∈ S.Q := by
  classical
  unfold artinHasseDworkParameterApproxTo
  apply Ideal.sum_mem
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  · exact Ideal.pow_le_self hn0 (S.artinHasseInverseCoeffLiftTo_mem_Q_pow N n)

theorem artinHasseInverseCoeffLiftTo_one_sub_pi_mem_Q_sq_of_one_le
    {N : ℕ} (hN : 1 ≤ N) :
    S.artinHasseInverseCoeffLiftTo N 1 - S.π ∈ S.Q ^ 2 := by
  have hcoeff :
      (PowerSeries.coeff (R := ℚ) 1) (artinHasseExpInverseSeries ℓ) = 1 :=
    artinHasseExpInverseSeries_coeff_one ℓ
  have hNprec :
      S.artinHasseInverseCoeffLiftTo N 1 - S.π ∈ S.Q ^ (N + 1) := by
    have h :=
      S.artinHasseInverseCoeffLiftTo_den_mul_sub_num_pi_pow_mem_Q_pow_succ N 1
    simpa [hcoeff] using h
  exact Ideal.pow_le_pow_right (Nat.succ_le_succ hN) hNprec

theorem artinHasseDworkParameterApproxTo_sub_pi_mem_Q_sq_of_pos
    {N : ℕ} (hN : 0 < N) :
    S.artinHasseDworkParameterApproxTo N - S.π ∈ S.Q ^ 2 := by
  classical
  let f : ℕ → 𝓞 R' := fun n => S.artinHasseInverseCoeffLiftTo N n
  have h1N : 1 ≤ N := Nat.succ_le_of_lt hN
  have hmem_one :
      1 ∈ Finset.range (N + 1) := by
    simpa using hN
  have hsum_indicator :
      (∑ n ∈ Finset.range (N + 1), if n = 1 then S.π else 0) = S.π := by
    rw [Finset.sum_ite_eq']
    simp [hmem_one]
  have hrewrite :
      S.artinHasseDworkParameterApproxTo N - S.π =
        ∑ n ∈ Finset.range (N + 1),
          (if n = 1 then f n - S.π else f n) := by
    calc
      S.artinHasseDworkParameterApproxTo N - S.π
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
      S.artinHasseInverseCoeffLiftTo_one_sub_pi_mem_Q_sq_of_one_le h1N
  · by_cases hn0 : n = 0
    · simp [f, hn0]
    · have hn2 : 2 ≤ n := by omega
      have hfmem : f n ∈ S.Q ^ n := by
        simpa [f] using S.artinHasseInverseCoeffLiftTo_mem_Q_pow N n
      simpa [hn1] using Ideal.pow_le_pow_right hn2 hfmem

/-- Precision-indexed raw lift of the coefficient of `E_ℓ(γT)`. -/
noncomputable def dworkCoeffArtinHasseAtRawTo
    (γ : 𝓞 R') (N n : ℕ) : 𝓞 R' :=
  (((PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)).num : 𝓞 R') *
    γ ^ n * S.dworkCoeffArtinHasseDenInvTo n N

/-- Precision-indexed integral representative of the coefficients of
`E_ℓ(γT)`, with constant term fixed exactly as `1`. -/
noncomputable def dworkCoeffArtinHasseAtTo
    (γ : 𝓞 R') (N n : ℕ) : 𝓞 R' :=
  match n with
  | 0 => 1
  | Nat.succ n => S.dworkCoeffArtinHasseAtRawTo γ N (Nat.succ n)

@[simp] theorem dworkCoeffArtinHasseAtTo_zero
    (γ : 𝓞 R') (N : ℕ) :
    S.dworkCoeffArtinHasseAtTo γ N 0 = 1 := rfl

/-- Precision-indexed coefficients of `E_ℓ(γT)` have `Q`-adic order at least
their degree when `γ ∈ Q`. -/
theorem dworkCoeffArtinHasseAtTo_mem_Q_pow
    {γ : 𝓞 R'} (hγ : γ ∈ S.Q) (N n : ℕ) :
    S.dworkCoeffArtinHasseAtTo γ N n ∈ S.Q ^ n := by
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
        Ideal.mul_mem_right (S.dworkCoeffArtinHasseDenInvTo m N) (S.Q ^ m) hnum

/-- Denominator-cleared congruence for precision-indexed coefficients of
`E_ℓ(γT)`. -/
theorem dworkCoeffArtinHasseAtTo_den_mul_sub_num_gamma_pow_mem_Q_pow_succ
    (γ : 𝓞 R') (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
    (c.den : 𝓞 R') * S.dworkCoeffArtinHasseAtTo γ N n - (c.num : 𝓞 R') * γ ^ n ∈
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
          (c.den : 𝓞 R') * S.dworkCoeffArtinHasseDenInvTo m N - 1 ∈
            S.Q ^ (N + 1) := by
        simpa [c] using S.dworkCoeffArtinHasseDenInvTo_spec m N
      have hmul :
          ((c.num : 𝓞 R') * γ ^ m) *
              ((c.den : 𝓞 R') * S.dworkCoeffArtinHasseDenInvTo m N - 1) ∈
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
    {γ : 𝓞 R'} (hγ : γ ∈ S.Q) (N n : ℕ) :
    let c : ℚ := (PowerSeries.coeff (R := ℚ) n) (artinHasseExpSeries ℓ)
    (c.den : 𝓞 R') * S.dworkCoeffArtinHasseAtTo γ N n - (c.num : 𝓞 R') * γ ^ n ∈
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
          (c.den : 𝓞 R') * S.dworkCoeffArtinHasseDenInvTo m N - 1 ∈
            S.Q ^ (N + 1) := by
        simpa [c] using S.dworkCoeffArtinHasseDenInvTo_spec m N
      have hγpow : γ ^ m ∈ S.Q ^ m := Ideal.pow_mem_pow hγ m
      have hmul :
          ((c.num : 𝓞 R') * γ ^ m) *
              ((c.den : 𝓞 R') * S.dworkCoeffArtinHasseDenInvTo m N - 1) ∈
            S.Q ^ (m + (N + 1)) := by
        have hnumγ : (c.num : 𝓞 R') * γ ^ m ∈ S.Q ^ m :=
          Ideal.mul_mem_left _ _ hγpow
        simpa [pow_add] using Ideal.mul_mem_mul hnumγ hden
      have hmul' :
          ((c.num : 𝓞 R') * γ ^ m) *
              ((c.den : 𝓞 R') * S.dworkCoeffArtinHasseDenInvTo m N - 1) ∈
            S.Q ^ (N + 1 + m) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmul
      convert hmul' using 1
      simp [dworkCoeffArtinHasseAtTo, dworkCoeffArtinHasseAtRawTo, c, m]
      ring

end ConductorFlexibleConcreteStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
