import BernoulliRegular.CyclotomicUnits.Basic
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.KummerLift.CharacterIdentification
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.SigmaPreservation
import Mathlib.Data.ZMod.Units

/-!
# Normalized cyclotomic units

This file starts the CU-06b replacement of the squared real cyclotomic-unit
family by the normalized units

`ζ ^ e * (1 - ζ ^ a) / (1 - ζ)`, with `2 * e = 1 - a mod p`.

The definitions here live first in `(𝓞 K)ˣ`.  Later files descend the
complex-conjugation fixed units to `(𝓞 K⁺)ˣ` and compare the generated
subgroup with the existing squared-family subgroup.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension

namespace BernoulliRegular

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The canonical exponent used in
`ζ ^ e * (1 - ζ ^ a) / (1 - ζ)`: it is the residue of
`2⁻¹ * (1 - a)` modulo `p`. -/
noncomputable def normalizedCyclotomicUnitExponent (p a : ℕ) : ℕ :=
  ((2 : ZMod p)⁻¹ * (1 - (a : ZMod p))).val

theorem normalizedCyclotomicUnitExponent_spec (hp_odd : p ≠ 2) (a : ℕ) :
    ((2 * normalizedCyclotomicUnitExponent p a : ℕ) : ZMod p) =
      1 - (a : ZMod p) := by
  have hcop : Nat.Coprime 2 p := by
    simpa using ((Fact.out : Nat.Prime p).odd_of_ne_two hp_odd).coprime_two_left
  have hunit : IsUnit (2 : ZMod p) := (ZMod.isUnit_iff_coprime 2 p).2 hcop
  unfold normalizedCyclotomicUnitExponent
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  change (2 : ZMod p) * ((2 : ZMod p)⁻¹ * (1 - (a : ZMod p))) = 1 - (a : ZMod p)
  rw [← mul_assoc, ZMod.mul_inv_of_unit (2 : ZMod p) hunit, one_mul]

omit [IsCMField K] in
theorem zetaUnit_pow_eq_of_zmod_eq {m n : ℕ}
    (h : (m : ZMod p) = (n : ZMod p)) :
    ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ m =
      ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ n := by
  let ζu : (𝓞 K)ˣ := ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
  change ζu ^ m = ζu ^ n
  have hord : orderOf ζu = p := by
    rw [← orderOf_units]
    show orderOf (ζu : 𝓞 K) = p
    rw [show (ζu : 𝓞 K) = (zeta_spec p ℚ K).toInteger from IsUnit.unit_spec _]
    exact ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.eq_orderOf).symm
  rw [pow_eq_pow_iff_modEq, hord]
  exact (ZMod.natCast_eq_natCast_iff m n p).mp h

omit [IsCMField K] in
theorem zeta_pow_eq_of_zmod_eq {m n : ℕ}
    (h : (m : ZMod p) = (n : ZMod p)) :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ m =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ n := by
  have h_unit := congrArg (fun u : (𝓞 K)ˣ => (u : 𝓞 K))
    (zetaUnit_pow_eq_of_zmod_eq (p := p) (K := K) h)
  simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec] using h_unit

/-- The normalized cyclotomic unit in `𝓞 K`, with an explicit exponent.

The TeX exponent condition is `2 * e = 1 - a mod p`; the definition is kept
separate from that condition so algebraic identities can be reused with any
chosen representative. -/
noncomputable def normalizedCyclotomicUnitKWithExponent (a e : ℕ)
    (ha : a.Coprime p) (hp_two : 2 ≤ p) : (𝓞 K)ˣ :=
  ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ e *
    FLT37.cyclotomicUnitUnit p K a ha hp_two

omit [IsCMField K] in
@[simp]
theorem normalizedCyclotomicUnitKWithExponent_val (a e : ℕ)
    (ha : a.Coprime p) (hp_two : 2 ≤ p) :
    (normalizedCyclotomicUnitKWithExponent (p := p) (K := K) a e ha hp_two : 𝓞 K) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ e * FLT37.cyclotomicUnit p K a := by
  simp [normalizedCyclotomicUnitKWithExponent, FLT37.cyclotomicUnitUnit_val]

/-- The canonical normalized cyclotomic unit in `𝓞 K`. -/
noncomputable def normalizedCyclotomicUnitK (a : ℕ)
    (ha : a.Coprime p) : (𝓞 K)ˣ :=
  normalizedCyclotomicUnitKWithExponent (p := p) (K := K) a
    (normalizedCyclotomicUnitExponent p a) ha (Fact.out : Nat.Prime p).two_le

omit [IsCMField K] in
@[simp]
theorem normalizedCyclotomicUnitK_val (a : ℕ)
    (ha : a.Coprime p) :
    (normalizedCyclotomicUnitK (p := p) (K := K) a ha : 𝓞 K) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^
          normalizedCyclotomicUnitExponent p a * FLT37.cyclotomicUnit p K a := by
  simp [normalizedCyclotomicUnitK]

omit [IsCMField K] in
theorem normalizedCyclotomicUnitKWithExponent_sq_val (a e : ℕ)
    (ha : a.Coprime p) (hp_two : 2 ≤ p) :
    (normalizedCyclotomicUnitKWithExponent (p := p) (K := K) a e ha hp_two ^ 2 : 𝓞 K) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (2 * e) *
        (FLT37.cyclotomicUnit p K a) ^ 2 := by
  let ζ : 𝓞 K := ((zeta_spec p ℚ K).toInteger : 𝓞 K)
  let c : 𝓞 K := FLT37.cyclotomicUnit p K a
  change (ζ ^ e * c) ^ 2 = ζ ^ (2 * e) * c ^ 2
  rw [pow_two, pow_two]
  calc
    (ζ ^ e * c) * (ζ ^ e * c) = (ζ ^ e * ζ ^ e) * (c * c) := by ring
    _ = ζ ^ (e + e) * (c * c) := by rw [← pow_add]
    _ = ζ ^ (2 * e) * (c * c) := by rw [two_mul]

/-- Conjugating the quotient unit contributes the expected zeta factor:
`σ((1 - ζ^a) / (1 - ζ)) = ζ^(1-a) * (1 - ζ^a) / (1 - ζ)`.

The exponent is represented as `p + 1 - a`, which is congruent to `1 - a`
modulo `p` in the range `1 ≤ a ≤ p`. -/
theorem ringOfIntegersComplexConj_cyclotomicUnit_eq_zeta_pow_mul_self
    (a : ℕ) (_ha_pos : 1 ≤ a) (ha_le : a ≤ p) :
    ringOfIntegersComplexConj K (FLT37.cyclotomicUnit p K a) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p + 1 - a) *
        FLT37.cyclotomicUnit p K a := by
  let ζ : 𝓞 K := ((zeta_spec p ℚ K).toInteger : 𝓞 K)
  let c : ℕ → 𝓞 K := FLT37.cyclotomicUnit p K
  have hζp : ζ ^ p = 1 :=
    (zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_eq_one
  have hσ := FLT37.Sinnott.cyclotomicUnit_pred_mul_complexConj_cyclotomicUnit_eq
    (p := p) (K := K) a ha_le
  change c (p - 1) * ringOfIntegersComplexConj K (c a) = c (p - a) at hσ
  have hpred : c (p - 1) = -ζ ^ (p - 1) := by
    simpa [c, ζ] using FLT37.cyclotomicUnit_p_sub_one (p := p) (K := K)
  rw [hpred] at hσ
  have hσ' : ζ ^ (p - 1) * ringOfIntegersComplexConj K (c a) = -c (p - a) := by
    linear_combination -hσ
  have hconj : ringOfIntegersComplexConj K (c a) = -ζ * c (p - a) := by
    calc
      ringOfIntegersComplexConj K (c a)
          = ζ ^ p * ringOfIntegersComplexConj K (c a) := by rw [hζp, one_mul]
      _ = ζ * (ζ ^ (p - 1) * ringOfIntegersComplexConj K (c a)) := by
        rw [← mul_assoc, mul_comm ζ (ζ ^ (p - 1)), ← pow_succ,
          Nat.sub_one_add_one (Fact.out : Nat.Prime p).ne_zero]
      _ = -ζ * c (p - a) := by rw [hσ']; ring
  have hpair : c a = -ζ ^ a * c (p - a) := by
    simpa [c, ζ] using
      FLT37.cyclotomicUnit_eq_neg_zeta_pow_mul_cyclotomicUnit_p_sub
        (p := p) (K := K) a ha_le
  rw [hconj]
  change -ζ * c (p - a) = ζ ^ (p + 1 - a) * c a
  rw [hpair]
  have ha_le_succ : a ≤ p + 1 := le_trans ha_le (Nat.le_succ p)
  calc
    -ζ * c (p - a)
        = ζ ^ (p + 1 - a) * (-ζ ^ a * c (p - a)) := by
          rw [show ζ ^ (p + 1 - a) * (-ζ ^ a * c (p - a)) =
              -(ζ ^ (p + 1 - a) * ζ ^ a) * c (p - a) by ring,
            ← pow_add, Nat.sub_add_cancel ha_le_succ]
          rw [show p + 1 = p.succ by rfl, pow_succ, hζp]
          ring
    _ = ζ ^ (p + 1 - a) * (-ζ ^ a * c (p - a)) := rfl

/-- The normalized K-side unit is fixed by complex conjugation when the
exponent satisfies the TeX congruence `2 * e = 1 - a mod p`. -/
theorem unitsComplexConj_normalizedCyclotomicUnitKWithExponent
    (a e : ℕ) (ha : a.Coprime p) (ha_pos : 1 ≤ a) (ha_le : a ≤ p)
    (hp_two : 2 ≤ p)
    (he : ((2 * e : ℕ) : ZMod p) = 1 - (a : ZMod p)) :
    unitsComplexConj K
        (normalizedCyclotomicUnitKWithExponent (p := p) (K := K) a e ha hp_two) =
      normalizedCyclotomicUnitKWithExponent (p := p) (K := K) a e ha hp_two := by
  let ζ : 𝓞 K := ((zeta_spec p ℚ K).toInteger : 𝓞 K)
  let c : 𝓞 K := FLT37.cyclotomicUnit p K a
  apply Units.ext
  change ringOfIntegersComplexConj K
      (ζ ^ e * c) = ζ ^ e * c
  rw [map_mul, map_pow]
  have hconjζ : ringOfIntegersComplexConj K ζ = ζ ^ (p - 1) := by
    change ringOfIntegersComplexConj K (zeta_spec p ℚ K).toInteger =
      (zeta_spec p ℚ K).toInteger ^ (p - 1)
    exact complexConj_apply_zeta (p := p) (K := K)
  rw [hconjζ]
  have hc : ringOfIntegersComplexConj K c = ζ ^ (p + 1 - a) * c := by
    simpa [c, ζ] using
      ringOfIntegersComplexConj_cyclotomicUnit_eq_zeta_pow_mul_self
        (p := p) (K := K) a ha_pos ha_le
  rw [hc]
  have ha_le_succ : a ≤ p + 1 := le_trans ha_le (Nat.le_succ p)
  have hp_one : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  have hpred : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp_one, Nat.cast_one]
    simp
  have hsub : ((p + 1 - a : ℕ) : ZMod p) = 1 - (a : ZMod p) := by
    rw [Nat.cast_sub ha_le_succ, Nat.cast_add, Nat.cast_one]
    simp
  have hmod :
      (((p - 1) * e + (p + 1 - a) : ℕ) : ZMod p) = (e : ZMod p) := by
    rw [Nat.cast_add, Nat.cast_mul, hpred, hsub, ← he]
    rw [Nat.cast_mul]
    ring
  have hpow : ζ ^ ((p - 1) * e + (p + 1 - a)) = ζ ^ e := by
    simpa [ζ] using zeta_pow_eq_of_zmod_eq (p := p) (K := K) hmod
  calc
    (ζ ^ (p - 1)) ^ e * (ζ ^ (p + 1 - a) * c)
        = ζ ^ ((p - 1) * e + (p + 1 - a)) * c := by
          rw [← pow_mul, ← mul_assoc, ← pow_add]
    _ = ζ ^ e * c := by rw [hpow]

theorem unitsComplexConj_normalizedCyclotomicUnitK
    (hp_odd : p ≠ 2) (a : ℕ) (ha : a.Coprime p) (ha_pos : 1 ≤ a) (ha_le : a ≤ p) :
    unitsComplexConj K (normalizedCyclotomicUnitK (p := p) (K := K) a ha) =
      normalizedCyclotomicUnitK (p := p) (K := K) a ha :=
  unitsComplexConj_normalizedCyclotomicUnitKWithExponent
    (p := p) (K := K) a (normalizedCyclotomicUnitExponent p a) ha ha_pos ha_le
    (Fact.out : Nat.Prime p).two_le
    (normalizedCyclotomicUnitExponent_spec (p := p) hp_odd a)

omit [IsCMField K] in
/-- The normalized K-side unit for the standard real-cyclotomic range
`2 ≤ a ≤ (p - 1) / 2`. -/
noncomputable def normalizedCyclotomicUnitKOfRange (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) : (𝓞 K)ˣ :=
  normalizedCyclotomicUnitK (p := p) (K := K) a
    (realCyclotomicUnit_index_coprime (p := p) ha_two ha_le)

omit [IsCMField K] in
@[simp]
theorem normalizedCyclotomicUnitKOfRange_val (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    (normalizedCyclotomicUnitKOfRange (p := p) (K := K) a ha_two ha_le : 𝓞 K) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^
          normalizedCyclotomicUnitExponent p a * FLT37.cyclotomicUnit p K a := by
  simp [normalizedCyclotomicUnitKOfRange]

theorem unitsComplexConj_normalizedCyclotomicUnitKOfRange
    (hp_odd : p ≠ 2) (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    unitsComplexConj K
        (normalizedCyclotomicUnitKOfRange (p := p) (K := K) a ha_two ha_le) =
      normalizedCyclotomicUnitKOfRange (p := p) (K := K) a ha_two ha_le := by
  apply unitsComplexConj_normalizedCyclotomicUnitK (p := p) (K := K) hp_odd
  · omega
  · have hhalf : (p - 1) / 2 ≤ p := by omega
    omega

/-- The normalized K-side unit descends to the maximal real subfield. -/
theorem exists_normalizedCyclotomicUnitPlus
    (hp_odd : p ≠ 2) (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    ∃ y : 𝓞 K⁺,
      algebraMap (𝓞 K⁺) (𝓞 K) y =
        (normalizedCyclotomicUnitKOfRange (p := p) (K := K) a ha_two ha_le : 𝓞 K) := by
  let u : (𝓞 K)ˣ := normalizedCyclotomicUnitKOfRange (p := p) (K := K) a ha_two ha_le
  have hunit := unitsComplexConj_normalizedCyclotomicUnitKOfRange
    (p := p) (K := K) hp_odd a ha_two ha_le
  have hfixed : ringOfIntegersComplexConj K (u : 𝓞 K) = (u : 𝓞 K) := by
    have hval := congrArg (fun v : (𝓞 K)ˣ => (v : 𝓞 K)) hunit
    change ringOfIntegersComplexConj K (u : 𝓞 K) = (u : 𝓞 K) at hval
    exact hval
  exact (ringOfIntegersComplexConj_eq_self_iff K (u : 𝓞 K)).mp hfixed

/-- The normalized real cyclotomic unit as an element of `𝓞 K⁺`. -/
noncomputable def normalizedCyclotomicUnitPlus
    (hp_odd : p ≠ 2) (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) : 𝓞 K⁺ :=
  (exists_normalizedCyclotomicUnitPlus (p := p) (K := K) hp_odd a ha_two ha_le).choose

@[simp]
theorem algebraMap_normalizedCyclotomicUnitPlus
    (hp_odd : p ≠ 2) (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    algebraMap (𝓞 K⁺) (𝓞 K)
        (normalizedCyclotomicUnitPlus (p := p) (K := K) hp_odd a ha_two ha_le) =
      (normalizedCyclotomicUnitKOfRange (p := p) (K := K) a ha_two ha_le : 𝓞 K) :=
  (exists_normalizedCyclotomicUnitPlus (p := p) (K := K) hp_odd a ha_two ha_le).choose_spec

/-- The descended normalized element is a unit of `𝓞 K⁺`. -/
theorem isUnit_normalizedCyclotomicUnitPlus
    (hp_odd : p ≠ 2) (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    IsUnit (normalizedCyclotomicUnitPlus (p := p) (K := K) hp_odd a ha_two ha_le) := by
  have h_unit : IsUnit (algebraMap (𝓞 K⁺) (𝓞 K)
      (normalizedCyclotomicUnitPlus (p := p) (K := K) hp_odd a ha_two ha_le)) := by
    rw [algebraMap_normalizedCyclotomicUnitPlus]
    exact (normalizedCyclotomicUnitKOfRange (p := p) (K := K) a ha_two ha_le).isUnit
  have h_norm_unit : IsUnit (RingOfIntegers.norm K⁺
      (algebraMap (𝓞 K⁺) (𝓞 K)
        (normalizedCyclotomicUnitPlus (p := p) (K := K) hp_odd a ha_two ha_le))) :=
    h_unit.map _
  rw [RingOfIntegers.norm_algebraMap] at h_norm_unit
  have hfin_ne : Module.finrank K⁺ K ≠ 0 := by
    rw [finrank_K_over_Kplus]
    decide
  exact (isUnit_pow_iff hfin_ne).mp h_norm_unit

/-- The normalized real cyclotomic unit packaged as a unit of `𝓞 K⁺`. -/
noncomputable def normalizedCyclotomicUnitPlusUnit
    (hp_odd : p ≠ 2) (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) : (𝓞 K⁺)ˣ :=
  (isUnit_normalizedCyclotomicUnitPlus (p := p) (K := K) hp_odd a ha_two ha_le).unit

@[simp]
theorem normalizedCyclotomicUnitPlusUnit_val
    (hp_odd : p ≠ 2) (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    (normalizedCyclotomicUnitPlusUnit (p := p) (K := K) hp_odd a ha_two ha_le : 𝓞 K⁺) =
      normalizedCyclotomicUnitPlus (p := p) (K := K) hp_odd a ha_two ha_le :=
  IsUnit.unit_spec _

@[simp]
theorem algebraMap_normalizedCyclotomicUnitPlusUnit
    (hp_odd : p ≠ 2) (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    algebraMap (𝓞 K⁺) (𝓞 K)
        (normalizedCyclotomicUnitPlusUnit (p := p) (K := K) hp_odd a ha_two ha_le) =
      (normalizedCyclotomicUnitKOfRange (p := p) (K := K) a ha_two ha_le : 𝓞 K) := by
  rw [normalizedCyclotomicUnitPlusUnit_val, algebraMap_normalizedCyclotomicUnitPlus]

/-- K-side square identity: the square of the normalized unit is the existing
squared-family real cyclotomic unit. -/
theorem normalizedCyclotomicUnitKOfRange_sq_val_eq_realCyclotomicUnit
    (hp_odd : p ≠ 2) (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    (normalizedCyclotomicUnitKOfRange (p := p) (K := K) a ha_two ha_le ^ 2 : 𝓞 K) =
      FLT37.realCyclotomicUnit p K a := by
  let e := normalizedCyclotomicUnitExponent p a
  let ζ : 𝓞 K := ((zeta_spec p ℚ K).toInteger : 𝓞 K)
  let c : 𝓞 K := FLT37.cyclotomicUnit p K a
  have ha_le_p : a ≤ p := by
    have hhalf : (p - 1) / 2 ≤ p := by omega
    omega
  have ha_le_succ : a ≤ p + 1 := le_trans ha_le_p (Nat.le_succ p)
  have hsub : ((p + 1 - a : ℕ) : ZMod p) = 1 - (a : ZMod p) := by
    rw [Nat.cast_sub ha_le_succ, Nat.cast_add, Nat.cast_one]
    simp
  have hmod : ((2 * e : ℕ) : ZMod p) = ((p + 1 - a : ℕ) : ZMod p) := by
    rw [hsub]
    exact normalizedCyclotomicUnitExponent_spec (p := p) hp_odd a
  have hpow : ζ ^ (2 * e) = ζ ^ (p + 1 - a) := by
    simpa [ζ] using zeta_pow_eq_of_zmod_eq (p := p) (K := K) hmod
  unfold normalizedCyclotomicUnitKOfRange normalizedCyclotomicUnitK
  rw [normalizedCyclotomicUnitKWithExponent_sq_val]
  unfold FLT37.realCyclotomicUnit
  change ζ ^ (2 * e) * c ^ 2 = c * ringOfIntegersComplexConj K c
  rw [ringOfIntegersComplexConj_cyclotomicUnit_eq_zeta_pow_mul_self
    (p := p) (K := K) a (by omega) ha_le_p]
  change ζ ^ (2 * e) * c ^ 2 = c * (ζ ^ (p + 1 - a) * c)
  rw [hpow]
  ring

/-- Plus-side square identity: the square of the normalized descended unit is
the older squared-family generator. -/
theorem normalizedCyclotomicUnitPlusUnit_sq_eq_realCyclotomicUnit
    (hp_odd : p ≠ 2) (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    normalizedCyclotomicUnitPlusUnit (p := p) (K := K) hp_odd a ha_two ha_le ^ 2 =
      realCyclotomicUnit (p := p) (K := K) a ha_two ha_le := by
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective (𝓞 K⁺) (𝓞 K)
  simp only [Units.val_pow_eq_pow_val, map_pow]
  rw [algebraMap_normalizedCyclotomicUnitPlusUnit
      (p := p) (K := K) hp_odd a ha_two ha_le,
    normalizedCyclotomicUnitKOfRange_sq_val_eq_realCyclotomicUnit
      (p := p) (K := K) hp_odd a ha_two ha_le,
    algebraMap_realCyclotomicUnit (p := p) (K := K) a ha_two ha_le]

end BernoulliRegular

end
