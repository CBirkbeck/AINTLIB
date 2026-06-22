module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge.Part1.Part1

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-- In residue degree one, the ordinary-convention Dwork order at index
`p - a.val` is the raw integer `a.val * stickD`. -/
theorem stickOrdOrd_sub_val_eq_val_mul_stickD_of_f_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (hf : S.f = 1) (a : CyclotomicUnitDelta p) :
    S.stickOrdOrd (p - (a : ZMod p).val) =
      (a : ZMod p).val * S.stickD := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hℓ_two : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  have h_card : Fintype.card k = ℓ := by
    rw [S.toConcreteStickelbergerSetup.card_k_eq, hf, pow_one]
  have hpd : p * S.stickD = ℓ - 1 := by
    rw [S.toTraceFormStickelbergerSetup.p_mul_stickD_eq_card_sub_one, h_card]
  have hD_pos : 0 < S.stickD := by
    by_contra hpos
    have hD_zero : S.stickD = 0 := Nat.eq_zero_of_not_pos hpos
    have hℓ_sub_zero : ℓ - 1 = 0 := by
      rw [← hpd, hD_zero, mul_zero]
    omega
  have ha_lt : (a : ZMod p).val < p := ZMod.val_lt (a : ZMod p)
  have harg_lt : (a : ZMod p).val * S.stickD < ℓ := by
    have hmul_lt :
        (a : ZMod p).val * S.stickD < p * S.stickD :=
      Nat.mul_lt_mul_of_pos_right ha_lt hD_pos
    rw [hpd] at hmul_lt
    omega
  unfold TraceFormStickelbergerSetup.stickOrdOrd
    TraceFormStickelbergerSetup.stickOrd
  rw [show p - (p - (a : ZMod p).val) = (a : ZMod p).val by omega]
  exact digitSum_eq_self_of_lt hℓ_two harg_lt

/-- The Dwork exponent `p * stickOrdOrd (p - a.val)` is divisible by the
relative ramification index in the residue-degree-one split case. -/
theorem descentRamificationIdx_dvd_p_mul_stickOrdOrd_sub_val_of_f_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (hf : S.f = 1)
    (he : S.toConcreteStickelbergerSetup.descentRamificationIdx = ℓ - 1)
    (a : CyclotomicUnitDelta p) :
    S.toConcreteStickelbergerSetup.descentRamificationIdx ∣
      p * S.stickOrdOrd (p - (a : ZMod p).val) := by
  have h_card : Fintype.card k = ℓ := by
    rw [S.toConcreteStickelbergerSetup.card_k_eq, hf, pow_one]
  have hpd : p * S.stickD = ℓ - 1 := by
    rw [S.toTraceFormStickelbergerSetup.p_mul_stickD_eq_card_sub_one, h_card]
  have hord :=
    stickOrdOrd_sub_val_eq_val_mul_stickD_of_f_eq_one S hf a
  rw [he, hord]
  refine ⟨(a : ZMod p).val, ?_⟩
  nlinarith

/-- The exact Dwork exponent normalizes to `a.val` after division by the
relative ramification index in the residue-degree-one split case. -/
theorem dworkExponent_sub_val_div_descentRamificationIdx_eq_val_of_f_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (hf : S.f = 1)
    (he : S.toConcreteStickelbergerSetup.descentRamificationIdx = ℓ - 1)
    (a : CyclotomicUnitDelta p) :
    (p * S.stickOrdOrd (p - (a : ZMod p).val)) /
        S.toConcreteStickelbergerSetup.descentRamificationIdx =
      (a : ZMod p).val := by
  have hℓ_sub_pos : 0 < ℓ - 1 := by
    have hℓ_two : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
    omega
  have h_card : Fintype.card k = ℓ := by
    rw [S.toConcreteStickelbergerSetup.card_k_eq, hf, pow_one]
  have hpd : p * S.stickD = ℓ - 1 := by
    rw [S.toTraceFormStickelbergerSetup.p_mul_stickD_eq_card_sub_one, h_card]
  have hord :=
    stickOrdOrd_sub_val_eq_val_mul_stickD_of_f_eq_one S hf a
  have hnum :
      p * S.stickOrdOrd (p - (a : ZMod p).val) =
        (ℓ - 1) * (a : ZMod p).val := by
    rw [hord]
    nlinarith
  rw [he, hnum, Nat.mul_comm (ℓ - 1) ((a : ZMod p).val),
    Nat.mul_div_left _ hℓ_sub_pos]

/-- Divisibility form of the split exponent normalization, using only the
unramifiedness of the chosen prime of `K` over `(ℓ)`. -/
theorem descentRamificationIdx_dvd_p_mul_stickOrdOrd_sub_val_of_f_eq_one_of_unramified_base
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
      [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    (hf : S.f = 1)
    (he : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn
        (𝓞 K) = 1)
    (a : CyclotomicUnitDelta p) :
    S.toConcreteStickelbergerSetup.descentRamificationIdx ∣
      p * S.stickOrdOrd (p - (a : ZMod p).val) :=
  descentRamificationIdx_dvd_p_mul_stickOrdOrd_sub_val_of_f_eq_one S hf
    (S.toConcreteStickelbergerSetup
      |>.descentRamificationIdx_eq_ell_sub_one_of_unramified_base he)
    a

/-- Quotient form of the split exponent normalization, using only the
unramifiedness of the chosen prime of `K` over `(ℓ)`. -/
theorem dworkExponent_sub_val_div_descentRamificationIdx_eq_val_of_f_eq_one_of_unramified_base
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
      [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    (hf : S.f = 1)
    (he : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn
        (𝓞 K) = 1)
    (a : CyclotomicUnitDelta p) :
    (p * S.stickOrdOrd (p - (a : ZMod p).val)) /
        S.toConcreteStickelbergerSetup.descentRamificationIdx =
      (a : ZMod p).val :=
  dworkExponent_sub_val_div_descentRamificationIdx_eq_val_of_f_eq_one S hf
    (S.toConcreteStickelbergerSetup
      |>.descentRamificationIdx_eq_ell_sub_one_of_unramified_base he)
    a

/-! ### Conductor-flexible reciprocal exponent normalization -/

namespace ConductorFlexibleFullTeichDworkSetup

/-- Flexible residue-degree-one form of the ordinary-convention Dwork order at
index `p - a.val`. -/
theorem stickOrdOrd_sub_val_eq_val_mul_stickD_of_f_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (hf : S.f = 1) (a : CyclotomicUnitDelta p) :
    S.stickOrdOrd (p - (a : ZMod p).val) =
      (a : ZMod p).val * S.stickD := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hℓ_two : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  have h_card : Fintype.card k = ℓ := by
    rw [S.card_k, hf, pow_one]
  have hpd : p * S.stickD = ℓ - 1 := by
    rw [S.toConductorFlexibleTraceFormStickelbergerSetup.p_mul_stickD_eq_card_sub_one,
      h_card]
  have hD_pos : 0 < S.stickD := by
    by_contra hpos
    have hD_zero : S.stickD = 0 := Nat.eq_zero_of_not_pos hpos
    have hℓ_sub_zero : ℓ - 1 = 0 := by
      rw [← hpd, hD_zero, mul_zero]
    omega
  have ha_lt : (a : ZMod p).val < p := ZMod.val_lt (a : ZMod p)
  have harg_lt : (a : ZMod p).val * S.stickD < ℓ := by
    have hmul_lt :
        (a : ZMod p).val * S.stickD < p * S.stickD :=
      Nat.mul_lt_mul_of_pos_right ha_lt hD_pos
    rw [hpd] at hmul_lt
    omega
  unfold ConductorFlexibleTraceFormStickelbergerSetup.stickOrdOrd
    ConductorFlexibleTraceFormStickelbergerSetup.stickOrd
  rw [show p - (p - (a : ZMod p).val) = (a : ZMod p).val by omega]
  exact digitSum_eq_self_of_lt hℓ_two harg_lt

/-- Flexible divisibility form of the split reciprocal Dwork exponent
normalization. -/
theorem descentRamificationIdx_dvd_p_mul_stickOrdOrd_sub_val_of_f_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (hf : S.f = 1)
    (he : S.concrete.descentRamificationIdx = ℓ - 1)
    (a : CyclotomicUnitDelta p) :
    S.concrete.descentRamificationIdx ∣
      p * S.stickOrdOrd (p - (a : ZMod p).val) := by
  have h_card : Fintype.card k = ℓ := by
    rw [S.card_k, hf, pow_one]
  have hpd : p * S.stickD = ℓ - 1 := by
    rw [S.toConductorFlexibleTraceFormStickelbergerSetup.p_mul_stickD_eq_card_sub_one,
      h_card]
  have hord :=
    S.stickOrdOrd_sub_val_eq_val_mul_stickD_of_f_eq_one hf a
  rw [he, hord]
  refine ⟨(a : ZMod p).val, ?_⟩
  nlinarith

/-- Flexible quotient form of the split reciprocal Dwork exponent
normalization. -/
theorem dworkExponent_sub_val_div_descentRamificationIdx_eq_val_of_f_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (hf : S.f = 1)
    (he : S.concrete.descentRamificationIdx = ℓ - 1)
    (a : CyclotomicUnitDelta p) :
    (p * S.stickOrdOrd (p - (a : ZMod p).val)) /
        S.concrete.descentRamificationIdx =
      (a : ZMod p).val := by
  have hℓ_sub_pos : 0 < ℓ - 1 := by
    have hℓ_two : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
    omega
  have h_card : Fintype.card k = ℓ := by
    rw [S.card_k, hf, pow_one]
  have hpd : p * S.stickD = ℓ - 1 := by
    rw [S.toConductorFlexibleTraceFormStickelbergerSetup.p_mul_stickD_eq_card_sub_one,
      h_card]
  have hord :=
    S.stickOrdOrd_sub_val_eq_val_mul_stickD_of_f_eq_one hf a
  have hnum :
      p * S.stickOrdOrd (p - (a : ZMod p).val) =
        (ℓ - 1) * (a : ZMod p).val := by
    rw [hord]
    nlinarith
  rw [he, hnum, Nat.mul_comm (ℓ - 1) ((a : ZMod p).val),
    Nat.mul_div_left _ hℓ_sub_pos]

/-- Arbitrary-residue-degree Dwork exponent formula before dividing by the
descent ramification index.

This replaces the residue-degree-one digit argument by the cyclic carry
calculation over the Frobenius orbit of `ℓ mod p`. -/
theorem p_mul_stickOrdOrd_sub_val_eq_ell_sub_one_mul_residueOrbitSum_of_f_eq_orderOf
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (hℓp : ℓ.Coprime p)
    (hf : S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (a : CyclotomicUnitDelta p) :
    p * S.stickOrdOrd (p - (a : ZMod p).val) =
      (ℓ - 1) *
        ∑ i ∈ Finset.range
          (orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p)),
          residueOrbit ℓ p (a : ZMod p).val i := by
  classical
  let u : CyclotomicUnitDelta p := ZMod.unitOfCoprime ℓ hℓp
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hℓ_pos : 0 < ℓ := (Fact.out : Nat.Prime ℓ).pos
  have hℓ_one : 1 < ℓ := (Fact.out : Nat.Prime ℓ).one_lt
  have ha_lt : (a : ZMod p).val < p := ZMod.val_lt (a : ZMod p)
  have hpow_zmod : ((ℓ ^ orderOf u : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    have hval : ((u ^ orderOf u : CyclotomicUnitDelta p) : ZMod p) = (1 : ZMod p) :=
      congrArg (fun x : CyclotomicUnitDelta p ↦ (x : ZMod p))
        (pow_orderOf_eq_one u)
    have hleft : ((u ^ orderOf u : CyclotomicUnitDelta p) : ZMod p) =
        ((ℓ ^ orderOf u : ℕ) : ZMod p) := by
      rw [Units.val_pow_eq_pow_val]
      have hu : (u : ZMod p) = (ℓ : ZMod p) := by
        simp [u, ZMod.coe_unitOfCoprime]
      rw [hu]
      simp
    rw [← hleft, hval]
    simp
  have hpow : ℓ ^ orderOf u ≡ 1 [MOD p] :=
    (ZMod.natCast_eq_natCast_iff (ℓ ^ orderOf u) 1 p).mp hpow_zmod
  have hdiv : p ∣ ℓ ^ orderOf u - 1 := by
    have hle : 1 ≤ ℓ ^ orderOf u := Nat.one_le_pow (orderOf u) ℓ hℓ_pos
    exact (Nat.modEq_iff_dvd' hle).mp hpow.symm
  have hstick :
      S.stickOrdOrd (p - (a : ZMod p).val) =
        digitSum ℓ ((a : ZMod p).val * ((ℓ ^ orderOf u - 1) / p)) := by
    unfold ConductorFlexibleTraceFormStickelbergerSetup.stickOrdOrd
      ConductorFlexibleTraceFormStickelbergerSetup.stickOrd
      ConductorFlexibleTraceFormStickelbergerSetup.stickD
    rw [show p - (p - (a : ZMod p).val) = (a : ZMod p).val by omega]
    rw [S.card_k, hf]
  rw [hstick]
  simpa [u] using
    (p_mul_digitSum_mul_div_eq_ell_sub_one_mul_residueOrbitSum
      (ℓ := ℓ) (p := p) (A := (a : ZMod p).val) (f := orderOf u)
      hℓ_one hp_pos ha_lt hpow hdiv)

/-- Arbitrary-residue-degree Dwork exponent formula collected over the
collapsed Frobenius coset, hence expressed as the repeated Stickelberger
multiplicity of the actual conjugate prime. -/
theorem p_mul_stickOrdOrd_sub_val_eq_descentRamificationIdx_mul_repeatedMultiplicity_of_f_eq_orderOf
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (hℓp : ℓ.Coprime p)
    (hf : S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (he : S.concrete.descentRamificationIdx = ℓ - 1)
    (a : CyclotomicUnitDelta p) :
    p * S.stickOrdOrd (p - (a : ZMod p).val) =
      S.concrete.descentRamificationIdx *
        S.StickelbergerRepeatedMultiplicity
          (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            S.concrete.descentPrime) := by
  classical
  rw [he]
  calc
    p * S.stickOrdOrd (p - (a : ZMod p).val) =
        (ℓ - 1) *
          ∑ i ∈ Finset.range
            (orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p)),
            residueOrbit ℓ p (a : ZMod p).val i :=
      S.p_mul_stickOrdOrd_sub_val_eq_ell_sub_one_mul_residueOrbitSum_of_f_eq_orderOf
        hℓp hf a
    _ = (ℓ - 1) *
        S.StickelbergerRepeatedMultiplicity
          (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            S.concrete.descentPrime) := by
      rw [S.StickelbergerRepeatedMultiplicity_conjugate_eq_frobeniusCosetSum hℓp a,
        frobeniusCosetWeightSum_eq_residueOrbitSum hℓp a]

/-- Arbitrary-degree divisibility input for
`repeatedExactExponentsOnOrbit_phiPrimeGenDescent_sub_one_sourceConductorSigma`. -/
theorem descentRamificationIdx_dvd_p_mul_stickOrdOrd_sub_val_of_f_eq_orderOf
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (hℓp : ℓ.Coprime p)
    (hf : S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (he : S.concrete.descentRamificationIdx = ℓ - 1)
    (a : CyclotomicUnitDelta p) :
    S.concrete.descentRamificationIdx ∣
      p * S.stickOrdOrd (p - (a : ZMod p).val) := by
  rw [S.p_mul_stickOrdOrd_sub_val_eq_descentRamificationIdx_mul_repeatedMultiplicity_of_f_eq_orderOf
    hℓp hf he a]
  exact dvd_mul_right S.concrete.descentRamificationIdx _

/-- Arbitrary-degree quotient input for
`repeatedExactExponentsOnOrbit_phiPrimeGenDescent_sub_one_sourceConductorSigma`. -/
theorem dworkExponent_sub_val_div_descentRamificationIdx_eq_repeatedMultiplicity_of_f_eq_orderOf
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (hℓp : ℓ.Coprime p)
    (hf : S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (he : S.concrete.descentRamificationIdx = ℓ - 1)
    (a : CyclotomicUnitDelta p) :
    (p * S.stickOrdOrd (p - (a : ZMod p).val)) /
        S.concrete.descentRamificationIdx =
      S.StickelbergerRepeatedMultiplicity
        (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
          S.concrete.descentPrime) := by
  have hℓ_sub_pos : 0 < ℓ - 1 := by
    have hℓ_two : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
    omega
  rw [S.p_mul_stickOrdOrd_sub_val_eq_descentRamificationIdx_mul_repeatedMultiplicity_of_f_eq_orderOf
    hℓp hf he a]
  rw [he, Nat.mul_div_right _ hℓ_sub_pos]

end ConductorFlexibleFullTeichDworkSetup

/-- REF-18 exact conjugate exponents for `phiPrimeGenDescent S 1` in the
split, unramified-base case. The only remaining substantive input is the
Galois covariance of the descended element. -/
theorem StickelbergerExactConjugateExponents_phiPrimeGenDescent_one_of_sub_val_conjugates_split
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    (hf : S.f = 1)
    (he : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn
        (𝓞 K) = 1)
    (h_ne_zero : S.gaussSumInt 1 ^ p ≠ 0)
    (h_conj :
      ∀ a : CyclotomicUnitDelta p,
        algebraMap (𝓞 K) (𝓞 R')
          (cyclotomicRingOfIntegersEquiv (p := p) K a
            (phiPrimeGenDescent S
              (le_refl 1)
              (by
                have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
                omega)
              h_ne_zero)) =
          S.gaussSumInt (p - (a : ZMod p).val) ^ p) :
    S.StickelbergerExactConjugateExponents
      (phiPrimeGenDescent S
        (le_refl 1)
        (by
          have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
          omega)
        h_ne_zero) :=
  StickelbergerExactConjugateExponents_phiPrimeGenDescent_one_of_sub_val_conjugates
    S h_ne_zero h_conj
    (fun a ↦
      descentRamificationIdx_dvd_p_mul_stickOrdOrd_sub_val_of_f_eq_one_of_unramified_base
        S hf he a)
    (fun a ↦
      dworkExponent_sub_val_div_descentRamificationIdx_eq_val_of_f_eq_one_of_unramified_base
        S hf he a)

/-- Applying a target ring hom to the field-valued integral Gauss sum changes
the character and additive character by post-composition. This is the direct
form needed for the non-`K` cyclotomic automorphisms in the conjugate
covariance proof. -/
theorem ConcreteStickelbergerSetup.ringHom_gaussSumInt_eq_of_residueChar_psi
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R')
    (τ : R' →+* R') {a b : ℕ}
    (hχ : (S.residueChar ^ a).ringHomComp τ = S.residueChar ^ b)
    (hψ : τ.toMonoidHom.compAddChar S.psi = S.psi) :
    τ (algebraMap (𝓞 R') R' (S.gaussSumInt a)) =
      algebraMap (𝓞 R') R' (S.gaussSumInt b) := by
  rw [S.algebraMap_gaussSumInt a, S.algebraMap_gaussSumInt b,
    gaussSum_ringHomComp, hχ, hψ]

/-- One-index specialization of `ringHom_gaussSumInt_eq_of_residueChar_psi`. -/
theorem ConcreteStickelbergerSetup.ringHom_gaussSumInt_one_eq_of_residueChar_psi
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R')
    (τ : R' →+* R') {b : ℕ}
    (hχ : S.residueChar.ringHomComp τ = S.residueChar ^ b)
    (hψ : τ.toMonoidHom.compAddChar S.psi = S.psi) :
    τ (algebraMap (𝓞 R') R' (S.gaussSumInt 1)) =
      algebraMap (𝓞 R') R' (S.gaussSumInt b) := by
  apply S.ringHom_gaussSumInt_eq_of_residueChar_psi τ (a := 1) (b := b)
  · simpa using hχ
  · exact hψ

end Furtwaengler

end BernoulliRegular

end

end
