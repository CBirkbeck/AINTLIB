import BernoulliRegular.CyclotomicUnits.KummerLogTrace
import BernoulliRegular.CyclotomicUnits.DworkParameter
import BernoulliRegular.CyclotomicUnits.NormalizedUnits

/-!
# Normalization of the Kummer logarithm columns

The logarithm columns constructed in `KummerLogMatrix` use the squared real
cyclotomic-unit family.  This file connects those columns with the normalized
cyclotomic units `epsilon_a`: locally, the selected real cyclotomic unit is
`epsilon_a ^ 2`, so its finite logarithm is twice the normalized finite
logarithm.
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open IsCyclotomicExtension
open BernoulliRegular.Reflection.Local
open scoped BigOperators NumberField

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
theorem kummerLogColumnIndex_coprime
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogColumnIndex (p := p) hp_three a).Coprime p :=
  realCyclotomicUnit_index_coprime (p := p)
    (kummerLogColumnIndex_two_le (p := p) hp_three a)
    (kummerLogColumnIndex_le_half (p := p) hp_three a)

/-- The normalized K-side cyclotomic unit, mapped into the lambda-valued local
integer ring at the Dwork prime. -/
noncomputable def kummerLogValuedNormalizedUnit
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (ValuedIntegerRing p K)ˣ :=
  Units.map (algebraMap (𝓞 K) (ValuedIntegerRing p K)).toMonoidHom
    (normalizedCyclotomicUnitKOfRange (p := p) (K := K)
      (kummerLogColumnIndex (p := p) hp_three a)
      (kummerLogColumnIndex_two_le (p := p) hp_three a)
      (kummerLogColumnIndex_le_half (p := p) hp_three a))

omit [NumberField.IsCMField K] in
@[simp]
theorem kummerLogValuedNormalizedUnit_coe
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogValuedNormalizedUnit (p := p) (K := K) hp_three a :
        ValuedIntegerRing p K) =
      algebraMap (𝓞 K) (ValuedIntegerRing p K)
        (normalizedCyclotomicUnitKOfRange (p := p) (K := K)
          (kummerLogColumnIndex (p := p) hp_three a)
          (kummerLogColumnIndex_two_le (p := p) hp_three a)
          (kummerLogColumnIndex_le_half (p := p) hp_three a) : 𝓞 K) :=
  rfl

/-- The already-used real cyclotomic-unit column is the square of the
normalized local unit. -/
theorem kummerLogValuedNormalizedUnit_sq_eq_kummerLogValuedCyclotomicUnit
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogValuedNormalizedUnit (p := p) (K := K) hp_three a ^ 2 =
      kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a := by
  ext
  have hsq :=
    normalizedCyclotomicUnitKOfRange_sq_val_eq_realCyclotomicUnit
    (p := p) (K := K) (by omega : p ≠ 2)
    (kummerLogColumnIndex (p := p) hp_three a)
    (kummerLogColumnIndex_two_le (p := p) hp_three a)
    (kummerLogColumnIndex_le_half (p := p) hp_three a)
  rw [Units.val_pow_eq_pow_val, kummerLogValuedNormalizedUnit_coe,
    kummerLogValuedCyclotomicUnit_coe, ← map_pow, hsq]

/-- The denominator `(1 - zeta^a) / (1 - zeta)` of the normalized quotient,
as a local unit at the Dwork prime. -/
noncomputable def kummerLogValuedCyclotomicQuotientDenUnit
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (ValuedIntegerRing p K)ˣ :=
  Units.map (algebraMap (𝓞 K) (ValuedIntegerRing p K)).toMonoidHom
    (FLT37.cyclotomicUnitUnit p K
      (kummerLogColumnIndex (p := p) hp_three a)
      (kummerLogColumnIndex_coprime (p := p) hp_three a)
      (Fact.out : Nat.Prime p).two_le)

omit [NumberField.IsCMField K] in
@[simp]
theorem kummerLogValuedCyclotomicQuotientDenUnit_coe
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogValuedCyclotomicQuotientDenUnit (p := p) (K := K) hp_three a :
        ValuedIntegerRing p K) =
      algebraMap (𝓞 K) (ValuedIntegerRing p K)
        (FLT37.cyclotomicUnit p K (kummerLogColumnIndex (p := p) hp_three a)) := by
  simp [kummerLogValuedCyclotomicQuotientDenUnit, FLT37.cyclotomicUnitUnit_val]

omit [NumberField.IsCMField K] in
theorem kummerLogValuedCyclotomicQuotientDenUnit_sub_natCast_mem_lambdaIdeal
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogValuedCyclotomicQuotientDenUnit (p := p) (K := K) hp_three a :
        ValuedIntegerRing p K) -
        (kummerLogColumnIndex (p := p) hp_three a : ValuedIntegerRing p K) ∈
      lambdaIdeal p K := by
  let k : ℕ := kummerLogColumnIndex (p := p) hp_three a
  have hglobal :
      FLT37.cyclotomicUnit p K k - (k : 𝓞 K) ∈
        Reflection.Local.cyclotomicLambda p K := by
    rw [Reflection.Local.cyclotomicLambda, zetaPrime, Ideal.mem_span_singleton]
    exact FLT37.zetaSubOne_dvd_cyclotomicUnit_sub_natCast (p := p) (K := K) k
  have hmap :
      algebraMap (𝓞 K) (ValuedIntegerRing p K)
          (FLT37.cyclotomicUnit p K k - (k : 𝓞 K)) ∈
        Ideal.map (algebraMap (𝓞 K) (ValuedIntegerRing p K))
          (Reflection.Local.cyclotomicLambda p K) :=
    Ideal.mem_map_of_mem (algebraMap (𝓞 K) (ValuedIntegerRing p K)) hglobal
  rw [lambdaIdeal_eq_map_cyclotomicLambda (p := p) (K := K)] at hmap
  rw [map_sub] at hmap
  have hnat :
      algebraMap (𝓞 K) (ValuedIntegerRing p K) (k : 𝓞 K) =
        (k : ValuedIntegerRing p K) :=
    map_natCast (algebraMap (𝓞 K) (ValuedIntegerRing p K)) k
  rw [hnat] at hmap
  simpa [k] using hmap

/-- Additive argument for the normalized quotient
`a * (1 - zeta) / (1 - zeta^a)`, represented as
`a * ((1 - zeta^a) / (1 - zeta))^{-1} - 1`. -/
noncomputable def kummerLogNormalizedQuotientFiniteLogArg
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    ValuedIntegerRing p K :=
  (kummerLogColumnIndex (p := p) hp_three a : ValuedIntegerRing p K) *
      (kummerLogValuedCyclotomicQuotientDenUnit
        (p := p) (K := K) hp_three a)⁻¹ - 1

omit [NumberField.IsCMField K] in
theorem kummerLogNormalizedQuotientFiniteLogArg_mem_lambdaIdeal
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogNormalizedQuotientFiniteLogArg (p := p) (K := K) hp_three a ∈
      lambdaIdeal p K := by
  let cU : (ValuedIntegerRing p K)ˣ :=
    kummerLogValuedCyclotomicQuotientDenUnit (p := p) (K := K) hp_three a
  let c : ValuedIntegerRing p K := (cU : ValuedIntegerRing p K)
  let k : ValuedIntegerRing p K :=
    (kummerLogColumnIndex (p := p) hp_three a : ValuedIntegerRing p K)
  let cinv : ValuedIntegerRing p K := (cU⁻¹ : (ValuedIntegerRing p K)ˣ)
  have hc : c - k ∈ lambdaIdeal p K := by
    simpa [cU, c, k] using
      kummerLogValuedCyclotomicQuotientDenUnit_sub_natCast_mem_lambdaIdeal
        (p := p) (K := K) hp_three a
  have hmul : (c - k) * cinv ∈ lambdaIdeal p K :=
    (lambdaIdeal p K).mul_mem_right cinv hc
  have harg : k * cinv - 1 = -((c - k) * cinv) := by
    have hc_inv : c * cinv = 1 := by
      simp [c, cinv]
    calc
      k * cinv - 1 = k * cinv - c * cinv := by rw [hc_inv]
      _ = -((c - k) * cinv) := by ring
  rw [kummerLogNormalizedQuotientFiniteLogArg, harg]
  exact (lambdaIdeal p K).neg_mem hmul

/-- Finite quotient logarithm of the normalized quotient
`a * (1 - zeta) / (1 - zeta^a)`. -/
noncomputable def kummerLogNormalizedQuotientFiniteLog
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  samePrimeFiniteLog (p := p) (K := K) N
    (kummerLogNormalizedQuotientFiniteLogArg (p := p) (K := K) hp_three a)
    (kummerLogNormalizedQuotientFiniteLogArg_mem_lambdaIdeal
      (p := p) (K := K) hp_three a)

/-- The additive finite-log argument for the normalized cyclotomic unit:
`epsilon_a^(p - 1) = 1 + x`. -/
noncomputable def kummerLogNormalizedUnitFiniteLogArg
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    ValuedIntegerRing p K :=
  (kummerLogValuedNormalizedUnit (p := p) (K := K) hp_three a :
      ValuedIntegerRing p K) ^ (p - 1) - 1

omit [NumberField.IsCMField K] in
theorem kummerLogNormalizedUnitFiniteLogArg_mem_lambdaIdeal
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogNormalizedUnitFiniteLogArg (p := p) (K := K) hp_three a ∈
      lambdaIdeal p K := by
  let u : ValuedIntegerRing p K :=
    (kummerLogValuedNormalizedUnit (p := p) (K := K) hp_three a :
      ValuedIntegerRing p K)
  let k : ℕ := kummerLogColumnIndex (p := p) hp_three a
  have huk : u - (k : ValuedIntegerRing p K) ∈ lambdaIdeal p K := by
    have hglobal :
        ((normalizedCyclotomicUnitKOfRange (p := p) (K := K) k
          (kummerLogColumnIndex_two_le (p := p) hp_three a)
          (kummerLogColumnIndex_le_half (p := p) hp_three a) : 𝓞 K) -
            (k : 𝓞 K)) ∈ Reflection.Local.cyclotomicLambda p K := by
      rw [Reflection.Local.cyclotomicLambda, zetaPrime, Ideal.mem_span_singleton]
      rw [normalizedCyclotomicUnitKOfRange_val]
      let e := normalizedCyclotomicUnitExponent p k
      let ζ : 𝓞 K := ((zeta_spec p ℚ K).toInteger : 𝓞 K)
      let c : 𝓞 K := FLT37.cyclotomicUnit p K k
      have hc : ζ - 1 ∣ c - (k : 𝓞 K) :=
        by simpa [ζ, c] using
          FLT37.zetaSubOne_dvd_cyclotomicUnit_sub_natCast (p := p) (K := K) k
      have hz : ζ - 1 ∣ ζ ^ e - 1 :=
        by simpa [ζ] using
          FLT37.zetaSubOne_dvd_zeta_pow_sub_one (p := p) (K := K) e
      have hsplit : ζ ^ e * c - (k : 𝓞 K) =
          (ζ ^ e - 1) * c + (c - (k : 𝓞 K)) := by ring
      change ζ - 1 ∣ ζ ^ e * c - (k : 𝓞 K)
      rw [hsplit]
      exact dvd_add (hz.mul_right c) hc
    have hmap :
        algebraMap (𝓞 K) (ValuedIntegerRing p K)
            (((normalizedCyclotomicUnitKOfRange (p := p) (K := K) k
              (kummerLogColumnIndex_two_le (p := p) hp_three a)
              (kummerLogColumnIndex_le_half (p := p) hp_three a) : 𝓞 K) -
                (k : 𝓞 K))) ∈
          Ideal.map (algebraMap (𝓞 K) (ValuedIntegerRing p K))
            (Reflection.Local.cyclotomicLambda p K) :=
      Ideal.mem_map_of_mem (algebraMap (𝓞 K) (ValuedIntegerRing p K)) hglobal
    rw [lambdaIdeal_eq_map_cyclotomicLambda (p := p) (K := K)] at hmap
    rw [map_sub] at hmap
    have hnat :
        algebraMap (𝓞 K) (ValuedIntegerRing p K) (k : 𝓞 K) =
          (k : ValuedIntegerRing p K) :=
      map_natCast (algebraMap (𝓞 K) (ValuedIntegerRing p K)) k
    rw [hnat] at hmap
    simpa [u, k] using hmap
  have hpow :
      u ^ (p - 1) - (k : ValuedIntegerRing p K) ^ (p - 1) ∈
        lambdaIdeal p K :=
    pow_sub_pow_mem_of_sub_mem_ideal (lambdaIdeal p K) huk (p - 1)
  have hkpow :
      (k : ValuedIntegerRing p K) ^ (p - 1) - 1 ∈ lambdaIdeal p K :=
    natCast_pow_pred_sub_one_mem_lambdaIdeal_of_coprime
      (p := p) (K := K)
      (kummerLogColumnIndex_coprime (p := p) hp_three a)
  have hsum :
      (u ^ (p - 1) - (k : ValuedIntegerRing p K) ^ (p - 1)) +
          ((k : ValuedIntegerRing p K) ^ (p - 1) - 1) ∈ lambdaIdeal p K :=
    (lambdaIdeal p K).add_mem hpow hkpow
  change u ^ (p - 1) - 1 ∈ lambdaIdeal p K
  convert hsum using 1
  ring

/-- Finite quotient logarithm of the normalized cyclotomic unit. -/
noncomputable def kummerLogNormalizedUnitFiniteLog
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  samePrimeFiniteLog (p := p) (K := K) N
    (kummerLogNormalizedUnitFiniteLogArg (p := p) (K := K) hp_three a)
    (kummerLogNormalizedUnitFiniteLogArg_mem_lambdaIdeal
      (p := p) (K := K) hp_three a)

/-- The powered real-unit logarithm is the finite logarithm of
`(epsilon_a^(p - 1))^2`. -/
theorem kummerLogColumnFiniteLog_eq_normalizedUnit_square
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    kummerLogColumnFiniteLog (p := p) (K := K) hp_three a N =
      samePrimeFiniteLog (p := p) (K := K) N
        (((kummerLogValuedNormalizedUnit (p := p) (K := K) hp_three a :
            ValuedIntegerRing p K) ^ (p - 1)) ^ 2 - 1)
        (by
          have hx :=
            samePrimeFiniteLogProductCoord_mem_lambdaIdeal
              (p := p) (K := K)
              (kummerLogNormalizedUnitFiniteLogArg_mem_lambdaIdeal
                (p := p) (K := K) hp_three a)
              (kummerLogNormalizedUnitFiniteLogArg_mem_lambdaIdeal
                (p := p) (K := K) hp_three a)
          convert hx using 1
          simp [samePrimeFiniteLogProductCoord, kummerLogNormalizedUnitFiniteLogArg]
          ring) := by
  let u : (ValuedIntegerRing p K)ˣ :=
    kummerLogValuedNormalizedUnit (p := p) (K := K) hp_three a
  let v : (ValuedIntegerRing p K)ˣ :=
    kummerLogValuedCyclotomicUnit (p := p) (K := K) hp_three a
  have huv : u ^ 2 = v :=
    kummerLogValuedNormalizedUnit_sq_eq_kummerLogValuedCyclotomicUnit
      (p := p) (K := K) hp_three a
  have harg :
      kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a =
        (((u : ValuedIntegerRing p K) ^ (p - 1)) ^ 2 - 1) := by
    have hval := congrArg (fun w : (ValuedIntegerRing p K)ˣ => (w : ValuedIntegerRing p K)) huv
    simp only [Units.val_pow_eq_pow_val] at hval
    calc
      kummerLogColumnFiniteLogArg (p := p) (K := K) hp_three a =
          (v : ValuedIntegerRing p K) ^ (p - 1) - 1 := rfl
      _ = ((u : ValuedIntegerRing p K) ^ 2) ^ (p - 1) - 1 := by rw [← hval]
      _ = (((u : ValuedIntegerRing p K) ^ (p - 1)) ^ 2 - 1) := by
            rw [← pow_mul, ← pow_mul]
            congr 2
            omega
  exact samePrimeFiniteLog_eq_of_eq (p := p) (K := K) (N := N) harg
    (kummerLogColumnFiniteLogArg_mem_lambdaIdeal (p := p) (K := K) hp_three a)
    (by
      have hx :=
        samePrimeFiniteLogProductCoord_mem_lambdaIdeal
          (p := p) (K := K)
          (kummerLogNormalizedUnitFiniteLogArg_mem_lambdaIdeal
            (p := p) (K := K) hp_three a)
          (kummerLogNormalizedUnitFiniteLogArg_mem_lambdaIdeal
            (p := p) (K := K) hp_three a)
      convert hx using 1
      simp [samePrimeFiniteLogProductCoord, kummerLogNormalizedUnitFiniteLogArg, u]
      ring)

set_option maxHeartbeats 800000 in
-- The final rewrite unfolds the finite-log additivity proof and the
-- normalized-unit argument proof; the larger heartbeat budget keeps this
-- wrapper theorem deterministic without changing the proof source.
/-- Since the implemented columns use the squared real family, the finite
logarithm of a Kummer column is twice the finite logarithm of the normalized
cyclotomic unit. -/
theorem kummerLogColumnFiniteLog_eq_two_nsmul_normalizedUnitFiniteLog
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    kummerLogColumnFiniteLog (p := p) (K := K) hp_three a N =
      2 • kummerLogNormalizedUnitFiniteLog (p := p) (K := K) hp_three a N := by
  rw [kummerLogColumnFiniteLog_eq_normalizedUnit_square
    (p := p) (K := K) hp_three a N]
  let x : ValuedIntegerRing p K :=
    kummerLogNormalizedUnitFiniteLogArg (p := p) (K := K) hp_three a
  have hx : x ∈ lambdaIdeal p K :=
    kummerLogNormalizedUnitFiniteLogArg_mem_lambdaIdeal
      (p := p) (K := K) hp_three a
  have hadd := samePrimeFiniteLog_add_add_mul
    (p := p) (K := K) N hx hx
  have hcoord :
      samePrimeFiniteLogProductCoord (p := p) (K := K) x x =
        (((kummerLogValuedNormalizedUnit (p := p) (K := K) hp_three a :
            ValuedIntegerRing p K) ^ (p - 1)) ^ 2 - 1) := by
    simp [samePrimeFiniteLogProductCoord, x, kummerLogNormalizedUnitFiniteLogArg]
    ring
  rw [← samePrimeFiniteLog_eq_of_eq (p := p) (K := K) (N := N) hcoord
    (samePrimeFiniteLogProductCoord_mem_lambdaIdeal (p := p) (K := K) hx hx)
    (by
      convert samePrimeFiniteLogProductCoord_mem_lambdaIdeal (p := p) (K := K) hx hx using 1
      exact hcoord.symm)]
  rw [hadd]
  simp [kummerLogNormalizedUnitFiniteLog, x, two_mul]

omit [NumberField.IsCMField K] in
theorem valuedCyclotomicZetaInteger_pow_eq_of_zmod_eq {m n : ℕ}
    (h : (m : ZMod p) = (n : ZMod p)) :
    valuedCyclotomicZetaInteger p K ^ m =
      valuedCyclotomicZetaInteger p K ^ n := by
  have hmod : m ≡ n [MOD p] :=
    (ZMod.natCast_eq_natCast_iff m n p).mp h
  exact pow_eq_pow_of_modEq hmod
    (valuedCyclotomicZetaInteger_pow_eq_one (p := p) (K := K))

omit [NumberField.IsCMField K] in
theorem zetaNatPowSubOne_mem_lambdaIdeal (m : ℕ) :
    valuedCyclotomicZetaInteger p K ^ m - 1 ∈ lambdaIdeal p K := by
  let a : ZMod p := (m : ZMod p)
  have hpow :
      valuedCyclotomicZetaInteger p K ^ m =
        valuedCyclotomicZetaInteger p K ^ a.val :=
    valuedCyclotomicZetaInteger_pow_eq_of_zmod_eq (p := p) (K := K) (by simp [a])
  rw [hpow]
  exact zetaPowSubOne_mem_lambdaIdeal (p := p) (K := K) a

omit [NumberField.IsCMField K] in
theorem samePrimeFiniteLog_zetaNatPowSubOne_eq_zero
    (m N : ℕ) :
    samePrimeFiniteLog (p := p) (K := K) N
        (valuedCyclotomicZetaInteger p K ^ m - 1)
        (zetaNatPowSubOne_mem_lambdaIdeal (p := p) (K := K) m) = 0 := by
  let a : ZMod p := (m : ZMod p)
  have hpow :
      valuedCyclotomicZetaInteger p K ^ m =
        valuedCyclotomicZetaInteger p K ^ a.val :=
    valuedCyclotomicZetaInteger_pow_eq_of_zmod_eq (p := p) (K := K) (by simp [a])
  have harg :
      valuedCyclotomicZetaInteger p K ^ m - 1 =
        valuedCyclotomicZetaInteger p K ^ a.val - 1 := by
    rw [hpow]
  calc
    samePrimeFiniteLog (p := p) (K := K) N
        (valuedCyclotomicZetaInteger p K ^ m - 1)
        (zetaNatPowSubOne_mem_lambdaIdeal (p := p) (K := K) m)
        =
      samePrimeFiniteLog (p := p) (K := K) N
        (valuedCyclotomicZetaInteger p K ^ a.val - 1)
        (zetaPowSubOne_mem_lambdaIdeal (p := p) (K := K) a) :=
        samePrimeFiniteLog_eq_of_eq (p := p) (K := K) (N := N) harg
          (zetaNatPowSubOne_mem_lambdaIdeal (p := p) (K := K) m)
          (zetaPowSubOne_mem_lambdaIdeal (p := p) (K := K) a)
    _ = 0 := samePrimeFiniteLog_zetaPowSubOne_eq_zero (p := p) (K := K) a N

omit [NumberField.IsCMField K] in
theorem kummerLogValuedCyclotomicQuotientDenUnit_pow_pred_sub_one_mem_lambdaIdeal
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    ((kummerLogValuedCyclotomicQuotientDenUnit
        (p := p) (K := K) hp_three a : ValuedIntegerRing p K) ^ (p - 1) - 1) ∈
      lambdaIdeal p K := by
  let k : ℕ := kummerLogColumnIndex (p := p) hp_three a
  let c : ValuedIntegerRing p K :=
    (kummerLogValuedCyclotomicQuotientDenUnit
      (p := p) (K := K) hp_three a : ValuedIntegerRing p K)
  have hck : c - (k : ValuedIntegerRing p K) ∈ lambdaIdeal p K := by
    simpa [c, k] using
      kummerLogValuedCyclotomicQuotientDenUnit_sub_natCast_mem_lambdaIdeal
        (p := p) (K := K) hp_three a
  have hpow :
      c ^ (p - 1) - (k : ValuedIntegerRing p K) ^ (p - 1) ∈
        lambdaIdeal p K :=
    pow_sub_pow_mem_of_sub_mem_ideal (lambdaIdeal p K) hck (p - 1)
  have hkpow :
      (k : ValuedIntegerRing p K) ^ (p - 1) - 1 ∈ lambdaIdeal p K :=
    natCast_pow_pred_sub_one_mem_lambdaIdeal_of_coprime
      (p := p) (K := K)
      (kummerLogColumnIndex_coprime (p := p) hp_three a)
  have hsum :
      (c ^ (p - 1) - (k : ValuedIntegerRing p K) ^ (p - 1)) +
          ((k : ValuedIntegerRing p K) ^ (p - 1) - 1) ∈ lambdaIdeal p K :=
    (lambdaIdeal p K).add_mem hpow hkpow
  change c ^ (p - 1) - 1 ∈ lambdaIdeal p K
  convert hsum using 1
  ring

omit [NumberField.IsCMField K] in
theorem kummerLogNormalizedUnitFiniteLog_eq_denUnitPowPredFiniteLog
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) (N : ℕ) :
    kummerLogNormalizedUnitFiniteLog (p := p) (K := K) hp_three a N =
      samePrimeFiniteLog (p := p) (K := K) N
        ((kummerLogValuedCyclotomicQuotientDenUnit
          (p := p) (K := K) hp_three a : ValuedIntegerRing p K) ^ (p - 1) - 1)
        (kummerLogValuedCyclotomicQuotientDenUnit_pow_pred_sub_one_mem_lambdaIdeal
          (p := p) (K := K) hp_three a) := by
  let e : ℕ :=
    normalizedCyclotomicUnitExponent p
      (kummerLogColumnIndex (p := p) hp_three a)
  let ζ : ValuedIntegerRing p K := valuedCyclotomicZetaInteger p K
  let c : ValuedIntegerRing p K :=
    (kummerLogValuedCyclotomicQuotientDenUnit
      (p := p) (K := K) hp_three a : ValuedIntegerRing p K)
  let zarg : ValuedIntegerRing p K := ζ ^ (e * (p - 1)) - 1
  let carg : ValuedIntegerRing p K := c ^ (p - 1) - 1
  have hz : zarg ∈ lambdaIdeal p K := by
    simpa [zarg, ζ] using zetaNatPowSubOne_mem_lambdaIdeal
      (p := p) (K := K) (e * (p - 1))
  have hc : carg ∈ lambdaIdeal p K := by
    simpa [carg, c] using
      kummerLogValuedCyclotomicQuotientDenUnit_pow_pred_sub_one_mem_lambdaIdeal
        (p := p) (K := K) hp_three a
  have hprod_mem :
      samePrimeFiniteLogProductCoord (p := p) (K := K) zarg carg ∈
        lambdaIdeal p K :=
    samePrimeFiniteLogProductCoord_mem_lambdaIdeal (p := p) (K := K) hz hc
  have harg :
      samePrimeFiniteLogProductCoord (p := p) (K := K) zarg carg =
        kummerLogNormalizedUnitFiniteLogArg (p := p) (K := K) hp_three a := by
    have hu :
        (kummerLogValuedNormalizedUnit (p := p) (K := K) hp_three a :
            ValuedIntegerRing p K) =
          ζ ^ e * c := by
      have hzeta :
          algebraMap (𝓞 K) (ValuedIntegerRing p K)
              ((zeta_spec p ℚ K).toInteger : 𝓞 K) = ζ := by
        rfl
      have hcmap :
          algebraMap (𝓞 K) (ValuedIntegerRing p K)
              (FLT37.cyclotomicUnit p K
                (kummerLogColumnIndex (p := p) hp_three a)) = c := by
        simp [c]
      calc
        (kummerLogValuedNormalizedUnit (p := p) (K := K) hp_three a :
            ValuedIntegerRing p K)
            =
          algebraMap (𝓞 K) (ValuedIntegerRing p K)
            (normalizedCyclotomicUnitKOfRange (p := p) (K := K)
              (kummerLogColumnIndex (p := p) hp_three a)
              (kummerLogColumnIndex_two_le (p := p) hp_three a)
              (kummerLogColumnIndex_le_half (p := p) hp_three a) : 𝓞 K) := rfl
        _ =
          algebraMap (𝓞 K) (ValuedIntegerRing p K)
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ e *
              FLT37.cyclotomicUnit p K
                (kummerLogColumnIndex (p := p) hp_three a)) := by
            simp [normalizedCyclotomicUnitKOfRange_val, e]
        _ = ζ ^ e * c := by
            rw [map_mul, map_pow, hzeta, hcmap]
    change zarg + carg + zarg * carg =
      (kummerLogValuedNormalizedUnit (p := p) (K := K) hp_three a :
        ValuedIntegerRing p K) ^ (p - 1) - 1
    dsimp [zarg, carg]
    rw [← kummerLogValuedNormalizedUnit_coe (p := p) (K := K) hp_three a]
    rw [hu, mul_pow, pow_mul]
    ring_nf
  calc
    kummerLogNormalizedUnitFiniteLog (p := p) (K := K) hp_three a N =
      samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteLogProductCoord (p := p) (K := K) zarg carg) hprod_mem :=
        samePrimeFiniteLog_eq_of_eq (p := p) (K := K) (N := N) harg.symm
          (kummerLogNormalizedUnitFiniteLogArg_mem_lambdaIdeal
            (p := p) (K := K) hp_three a)
          hprod_mem
    _ =
      samePrimeFiniteLog (p := p) (K := K) N zarg hz +
        samePrimeFiniteLog (p := p) (K := K) N carg hc :=
        samePrimeFiniteLog_add_add_mul (p := p) (K := K) N hz hc
    _ =
      samePrimeFiniteLog (p := p) (K := K) N carg hc := by
        rw [samePrimeFiniteLog_zetaNatPowSubOne_eq_zero
          (p := p) (K := K) (e * (p - 1)) N, zero_add]
    _ =
      samePrimeFiniteLog (p := p) (K := K) N
        ((kummerLogValuedCyclotomicQuotientDenUnit
          (p := p) (K := K) hp_three a : ValuedIntegerRing p K) ^ (p - 1) - 1)
        (kummerLogValuedCyclotomicQuotientDenUnit_pow_pred_sub_one_mem_lambdaIdeal
          (p := p) (K := K) hp_three a) := by
        rfl

omit [NumberField.IsCMField K] in
theorem pow_prime_sub_natCast_pow_mem_lambdaIdeal_pow_pred_of_sub_mem
    {x : ValuedIntegerRing p K} {k : ℕ}
    (hx : x - (k : ValuedIntegerRing p K) ∈ lambdaIdeal p K) :
    x ^ p - (k : ValuedIntegerRing p K) ^ p ∈ (lambdaIdeal p K) ^ (p - 1) := by
  let I : Ideal (ValuedIntegerRing p K) := lambdaIdeal p K
  let J : Ideal (ValuedIntegerRing p K) := I ^ (p - 1)
  let q : ValuedIntegerRing p K →+*
      ValuedIntegerRing p K ⧸ J := Ideal.Quotient.mk J
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change q (x ^ p - (k : ValuedIntegerRing p K) ^ p) = 0
  rw [map_sub, map_pow, map_pow]
  let d : ValuedIntegerRing p K := x - (k : ValuedIntegerRing p K)
  have hx_eq : x = d + (k : ValuedIntegerRing p K) := by
    simp [d]
  have hq_eq : q x = q d + q (k : ValuedIntegerRing p K) := by
    rw [hx_eq, map_add]
  have hp_mem : (p : ValuedIntegerRing p K) ∈ J := by
    change (p : ValuedIntegerRing p K) ∈ (lambdaIdeal p K) ^ (p - 1)
    rw [← span_natCast_prime_eq_lambdaIdeal_pow_pred (p := p) (K := K)]
    exact Ideal.mem_span_singleton_self (p : ValuedIntegerRing p K)
  have hp_zero : ((p : ℕ) : ValuedIntegerRing p K ⧸ J) = 0 := by
    change q (p : ValuedIntegerRing p K) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp_mem
  rw [hq_eq, add_pow]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro m hm hm0
    have hm_lt_succ : m < p + 1 := Finset.mem_range.mp hm
    by_cases hmp : m = p
    · subst m
      have hd_pow : d ^ p ∈ I ^ p := Ideal.pow_mem_pow (by simpa [d] using hx) p
      have hd_zero : (q d) ^ p = 0 := by
        rw [← map_pow]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.pow_le_pow_right (by omega : p - 1 ≤ p) hd_pow)
      simp [hd_zero]
    · have hm_lt : m < p := by omega
      have hchoose_dvd : p ∣ p.choose m :=
        Nat.Prime.dvd_choose_self (Fact.out : Nat.Prime p) hm0 hm_lt
      rcases hchoose_dvd with ⟨t, ht⟩
      have hcoeff_zero : ((p.choose m : ℕ) : ValuedIntegerRing p K ⧸ J) = 0 := by
        rw [ht, Nat.cast_mul, hp_zero, zero_mul]
      simp [hcoeff_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.succ_pos p)))

omit [NumberField.IsCMField K] in
theorem natCast_pow_prime_sub_self_mem_lambdaIdeal_pow_pred (k : ℕ) :
    (k : ValuedIntegerRing p K) ^ p - (k : ValuedIntegerRing p K) ∈
      (lambdaIdeal p K) ^ (p - 1) := by
  let I : Ideal (ValuedIntegerRing p K) := lambdaIdeal p K
  have hzmod : ((k ^ p : ℕ) : ZMod p) = (k : ZMod p) := by
    rw [Nat.cast_pow, ZMod.pow_card]
  have hintCast :
      (((k ^ p : ℕ) : ℤ) : ZMod p) = ((k : ℤ) : ZMod p) := by
    exact_mod_cast hzmod
  have hmod :
      ((k ^ p : ℕ) : ℤ) ≡ (k : ℤ) [ZMOD (p : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff ((k ^ p : ℕ) : ℤ) (k : ℤ) p).mp hintCast
  have hdvd : (p : ℤ) ∣ ((k ^ p : ℕ) : ℤ) - (k : ℤ) :=
    Int.ModEq.dvd hmod.symm
  rcases hdvd with ⟨t, ht⟩
  have hp_mem : (p : ValuedIntegerRing p K) ∈ I ^ (p - 1) := by
    change (p : ValuedIntegerRing p K) ∈ (lambdaIdeal p K) ^ (p - 1)
    rw [← span_natCast_prime_eq_lambdaIdeal_pow_pred (p := p) (K := K)]
    exact Ideal.mem_span_singleton_self (p : ValuedIntegerRing p K)
  have hmem :
      algebraMap ℤ (ValuedIntegerRing p K) (((k ^ p : ℕ) : ℤ) - (k : ℤ)) ∈
        I ^ (p - 1) := by
    rw [ht, map_mul]
    exact (I ^ (p - 1)).mul_mem_right
      (algebraMap ℤ (ValuedIntegerRing p K) t) hp_mem
  simpa [map_sub, map_pow] using hmem

omit [NumberField.IsCMField K] in
theorem kummerLogValuedCyclotomicQuotientDenUnit_pow_prime_sub_natCast_mem_lambdaIdeal_pow_pred
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogValuedCyclotomicQuotientDenUnit
        (p := p) (K := K) hp_three a : ValuedIntegerRing p K) ^ p -
        (kummerLogColumnIndex (p := p) hp_three a : ValuedIntegerRing p K) ∈
      (lambdaIdeal p K) ^ (p - 1) := by
  let k : ℕ := kummerLogColumnIndex (p := p) hp_three a
  let c : ValuedIntegerRing p K :=
    (kummerLogValuedCyclotomicQuotientDenUnit
      (p := p) (K := K) hp_three a : ValuedIntegerRing p K)
  have hck : c - (k : ValuedIntegerRing p K) ∈ lambdaIdeal p K := by
    simpa [c, k] using
      kummerLogValuedCyclotomicQuotientDenUnit_sub_natCast_mem_lambdaIdeal
        (p := p) (K := K) hp_three a
  have hpow :
      c ^ p - (k : ValuedIntegerRing p K) ^ p ∈ (lambdaIdeal p K) ^ (p - 1) :=
    pow_prime_sub_natCast_pow_mem_lambdaIdeal_pow_pred_of_sub_mem
      (p := p) (K := K) hck
  have hfermat :
      (k : ValuedIntegerRing p K) ^ p - (k : ValuedIntegerRing p K) ∈
        (lambdaIdeal p K) ^ (p - 1) :=
    natCast_pow_prime_sub_self_mem_lambdaIdeal_pow_pred (p := p) (K := K) k
  have hsum :
      (c ^ p - (k : ValuedIntegerRing p K) ^ p) +
          ((k : ValuedIntegerRing p K) ^ p - (k : ValuedIntegerRing p K)) ∈
        (lambdaIdeal p K) ^ (p - 1) :=
    ((lambdaIdeal p K) ^ (p - 1)).add_mem hpow hfermat
  change c ^ p - (k : ValuedIntegerRing p K) ∈ (lambdaIdeal p K) ^ (p - 1)
  convert hsum using 1
  ring

omit [NumberField.IsCMField K] in
theorem kummerLogDenUnitPowPredFiniteLog_eq_normalizedQuotientFiniteLog_modP
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    samePrimeFiniteLog (p := p) (K := K) (p - 2)
        ((kummerLogValuedCyclotomicQuotientDenUnit
          (p := p) (K := K) hp_three a : ValuedIntegerRing p K) ^ (p - 1) - 1)
        (kummerLogValuedCyclotomicQuotientDenUnit_pow_pred_sub_one_mem_lambdaIdeal
          (p := p) (K := K) hp_three a) =
      kummerLogNormalizedQuotientFiniteLog (p := p) (K := K) hp_three a (p - 2) := by
  let cU : (ValuedIntegerRing p K)ˣ :=
    kummerLogValuedCyclotomicQuotientDenUnit (p := p) (K := K) hp_three a
  let c : ValuedIntegerRing p K := (cU : ValuedIntegerRing p K)
  let cinv : ValuedIntegerRing p K := (cU⁻¹ : (ValuedIntegerRing p K)ˣ)
  let k : ValuedIntegerRing p K :=
    (kummerLogColumnIndex (p := p) hp_three a : ValuedIntegerRing p K)
  have hcp :
      c ^ p - k ∈ (lambdaIdeal p K) ^ (p - 1) := by
    simpa [cU, c, k] using
      kummerLogValuedCyclotomicQuotientDenUnit_pow_prime_sub_natCast_mem_lambdaIdeal_pow_pred
        (p := p) (K := K) hp_three a
  have hc_inv : c * cinv = 1 := by
    simp [c, cinv]
  have hcpow : c ^ p * cinv = c ^ (p - 1) := by
    calc
      c ^ p * cinv = c ^ ((p - 1) + 1) * cinv := by
        rw [show (p - 1) + 1 = p by omega]
      _ = (c ^ (p - 1) * c) * cinv := by rw [pow_succ]
      _ = c ^ (p - 1) * (c * cinv) := by ring
      _ = c ^ (p - 1) := by rw [hc_inv, mul_one]
  have hsub_eq :
      (c ^ (p - 1) - 1) - (k * cinv - 1) = (c ^ p - k) * cinv := by
    calc
      (c ^ (p - 1) - 1) - (k * cinv - 1) = c ^ (p - 1) - k * cinv := by
        ring
      _ = c ^ p * cinv - k * cinv := by rw [hcpow]
      _ = (c ^ p - k) * cinv := by ring
  have hsub :
      (c ^ (p - 1) - 1) - (k * cinv - 1) ∈ (lambdaIdeal p K) ^ ((p - 2) + 1) := by
    rw [hsub_eq]
    have hmul : (c ^ p - k) * cinv ∈ (lambdaIdeal p K) ^ (p - 1) :=
      ((lambdaIdeal p K) ^ (p - 1)).mul_mem_right cinv hcp
    simpa [show (p - 2) + 1 = p - 1 by omega] using hmul
  have hsub' :
      ((kummerLogValuedCyclotomicQuotientDenUnit
          (p := p) (K := K) hp_three a : ValuedIntegerRing p K) ^ (p - 1) - 1) -
          kummerLogNormalizedQuotientFiniteLogArg (p := p) (K := K) hp_three a ∈
        (lambdaIdeal p K) ^ ((p - 2) + 1) := by
    simpa [cU, c, cinv, k, kummerLogNormalizedQuotientFiniteLogArg] using hsub
  rw [kummerLogNormalizedQuotientFiniteLog]
  exact samePrimeFiniteLog_eq_of_sub_mem (p := p) (K := K)
    (kummerLogValuedCyclotomicQuotientDenUnit_pow_pred_sub_one_mem_lambdaIdeal
      (p := p) (K := K) hp_three a)
    (kummerLogNormalizedQuotientFiniteLogArg_mem_lambdaIdeal
      (p := p) (K := K) hp_three a)
    hsub'

omit [NumberField.IsCMField K] in
theorem kummerLogNormalizedUnitFiniteLog_eq_normalizedQuotientFiniteLog_modP
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogNormalizedUnitFiniteLog (p := p) (K := K) hp_three a (p - 2) =
      kummerLogNormalizedQuotientFiniteLog (p := p) (K := K) hp_three a (p - 2) := by
  rw [kummerLogNormalizedUnitFiniteLog_eq_denUnitPowPredFiniteLog
    (p := p) (K := K) hp_three a (p - 2)]
  exact kummerLogDenUnitPowPredFiniteLog_eq_normalizedQuotientFiniteLog_modP
    (p := p) (K := K) hp_three a

theorem kummerLogColumnFiniteLog_eq_two_nsmul_normalizedQuotientFiniteLog_modP
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    kummerLogColumnFiniteLog (p := p) (K := K) hp_three a (p - 2) =
      2 • kummerLogNormalizedQuotientFiniteLog (p := p) (K := K) hp_three a (p - 2) := by
  rw [kummerLogColumnFiniteLog_eq_two_nsmul_normalizedUnitFiniteLog
    (p := p) (K := K) hp_three a (p - 2)]
  rw [kummerLogNormalizedUnitFiniteLog_eq_normalizedQuotientFiniteLog_modP
    (p := p) (K := K) hp_three a]

theorem concreteKummerLogVector_evalₐ_pow_pred_eq_two_nsmul_normalizedQuotientFiniteLog
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    AdicCompletion.evalₐ (lambdaIdeal p K) ((p - 2) + 1)
        (concreteKummerLogVector (p := p) (K := K) hp_three a :
          DworkCompleteIntegerRing p K) =
      2 • kummerLogNormalizedQuotientFiniteLog (p := p) (K := K) hp_three a (p - 2) := by
  simp [concreteKummerLogVector, kummerLogFixedColumn,
    kummerLogColumnFiniteLog_eq_two_nsmul_normalizedQuotientFiniteLog_modP
      (p := p) (K := K) hp_three a]

/-- The cyclotomic quotient denominator, transported to the completed Dwork
ring.  This is the unit `(E_p(omega(a) * varpi) - 1) / (E_p(varpi) - 1)`
after specialization. -/
noncomputable def kummerLogDworkArtinHasseQuotientDenUnit
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (DworkCompleteIntegerRing p K)ˣ :=
  Units.map (algebraMap (ValuedIntegerRing p K)
    (DworkCompleteIntegerRing p K)).toMonoidHom
    (kummerLogValuedCyclotomicQuotientDenUnit
      (p := p) (K := K) hp_three a)

omit [NumberField.IsCMField K] in
@[simp]
theorem kummerLogDworkArtinHasseQuotientDenUnit_coe
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogDworkArtinHasseQuotientDenUnit
        (p := p) (K := K) hp_three a : DworkCompleteIntegerRing p K) =
      algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)
        (kummerLogValuedCyclotomicQuotientDenUnit
          (p := p) (K := K) hp_three a : ValuedIntegerRing p K) :=
  rfl

omit [NumberField.IsCMField K] in
/-- The Dwork-side quotient denominator is the specialized Artin-Hasse
quotient:

`den(a) * (E_p(varpi) - 1) = E_p(omega(a) * varpi) - 1`.

This is the concrete bridge from the cyclotomic quotient denominator of CU-11b
to the CU-09 Artin-Hasse endpoint. -/
theorem kummerLogDworkArtinHasseQuotientDenUnit_mul_exp_sub_one
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    (kummerLogDworkArtinHasseQuotientDenUnit
        (p := p) (K := K) hp_three a : DworkCompleteIntegerRing p K) *
        (artinHasseExp_eval_scaledDworkParameter p K 1 - 1) =
      artinHasseExp_eval_scaledDworkParameter p K
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p) - 1 := by
  let k : ℕ := kummerLogColumnIndex (p := p) hp_three a
  have hk_lt : k < p := by
    have hk_le := kummerLogColumnIndex_le_half (p := p) hp_three a
    omega
  have hk_val : ((k : ZMod p).val) = k := ZMod.val_natCast_of_lt hk_lt
  let ζi : 𝓞 K := ((zeta_spec p ℚ K).toInteger : 𝓞 K)
  have hglobal' :
      FLT37.cyclotomicUnit p K k * (ζi - 1) = ζi ^ k - 1 := by
    have h := FLT37.zeta_sub_one_mul_cyclotomicUnit (p := p) (K := K) k
    simpa [ζi, mul_comm, mul_left_comm, mul_assoc] using h
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  have hzdef : algebraMap (𝓞 K) R ζi = valuedCyclotomicZetaInteger p K := rfl
  have hmap := congrArg (algebraMap (𝓞 K) S) hglobal'
  rw [artinHasseExp_eval_scaledDworkParameter_eq_zeta_pow]
  rw [artinHasseExp_eval_scaledDworkParameter_eq_zeta_pow]
  rw [hk_val]
  change
    algebraMap R S
        (algebraMap (𝓞 K) R (FLT37.cyclotomicUnit p K k)) *
        (algebraMap R S
          (valuedCyclotomicZetaInteger p K ^ (1 : ZMod p).val) - 1) =
      algebraMap R S
          (valuedCyclotomicZetaInteger p K ^ k) - 1
  simp only [ZMod.val_one, pow_one]
  rw [show (valuedCyclotomicZetaInteger p K : R) = algebraMap (𝓞 K) R ζi from hzdef.symm]
  simp only [IsScalarTower.algebraMap_apply (𝓞 K) R S, map_sub, map_mul, map_pow,
    map_one] at hmap ⊢
  exact hmap

omit [NumberField.IsCMField K] in
/-- The normalized Artin-Hasse numerator `(E_p(T)-1)/T` over the Dwork
integer coefficient ring, represented by shifting the coefficients of
`E_p(T)-1`. -/
def integralArtinHasseNormalizedExpMinusOneSeries :
    PowerSeries (ValuedIntegerRing p K) :=
  PowerSeries.mk fun n =>
    (PowerSeries.coeff (R := ValuedIntegerRing p K) (n + 1))
      (integralExpMinusOneSeries p K)

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- The rational normalized Artin-Hasse numerator `(E_p(T)-1)/T`, represented
by shifting the coefficients of `E_p(T)-1`. -/
def rationalArtinHasseNormalizedExpMinusOneSeries :
    PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    (PowerSeries.coeff (R := ℚ) (n + 1))
      (PadicLogSetup.FormalDwork.expMinusOneSeries p)

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
@[simp]
theorem rationalArtinHasseNormalizedExpMinusOneSeries_coeff (n : ℕ) :
    (PowerSeries.coeff (R := ℚ) n)
        (rationalArtinHasseNormalizedExpMinusOneSeries p) =
      (PowerSeries.coeff (R := ℚ) (n + 1))
        (PadicLogSetup.FormalDwork.expMinusOneSeries p) := by
  simp [rationalArtinHasseNormalizedExpMinusOneSeries]

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
theorem rationalArtinHasseNormalizedExpMinusOneSeries_isPIntegral :
    Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (rationalArtinHasseNormalizedExpMinusOneSeries p) :=
  fun n => by
    simpa [rationalArtinHasseNormalizedExpMinusOneSeries] using
      PadicLogSetup.FormalDwork.expMinusOneSeries_isPIntegral p (n + 1)

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
@[simp]
theorem rationalArtinHasseNormalizedExpMinusOneSeries_constantCoeff :
    PowerSeries.constantCoeff
        (rationalArtinHasseNormalizedExpMinusOneSeries p) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [rationalArtinHasseNormalizedExpMinusOneSeries]

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
theorem rationalArtinHasseNormalizedExpMinusOneSeries_sub_one_isPIntegral :
    Furtwaengler.DieudonneDwork.IsRIntegralPS p
      (rationalArtinHasseNormalizedExpMinusOneSeries p - 1) :=
  (rationalArtinHasseNormalizedExpMinusOneSeries_isPIntegral (p := p)).sub
    (Furtwaengler.DieudonneDwork.IsRIntegralPS.one p)

omit [NumberField.IsCMField K] in
theorem rationalArtinHasseNormalizedExpMinusOneSeries_mapTo_valued :
    (rationalArtinHasseNormalizedExpMinusOneSeries_isPIntegral (p := p)).mapTo
        (rIntegralRatToValuedInteger p K) =
      integralArtinHasseNormalizedExpMinusOneSeries p K := by
  ext n
  rw [Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]
  simp [integralArtinHasseNormalizedExpMinusOneSeries,
    integralExpMinusOneSeries]

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- The factorial-cleared homogeneous coefficient of
`log ((E_p(T)-1)/T)`, before evaluation at a Dwork parameter. -/
def rationalArtinHasseNormalizedFactorialWeightedLogCoeff
    (d n : ℕ) : Furtwaengler.DieudonneDwork.rIntegralRatSubring p :=
  ((d.factorial / n : ℕ) :
      Furtwaengler.DieudonneDwork.rIntegralRatSubring p) *
    ((-1 : Furtwaengler.DieudonneDwork.rIntegralRatSubring p) ^ (n + 1)) *
      (⟨(PowerSeries.coeff (R := ℚ) d)
          ((rationalArtinHasseNormalizedExpMinusOneSeries p - 1) ^ n),
        (rationalArtinHasseNormalizedExpMinusOneSeries_sub_one_isPIntegral
          (p := p)).pow n d⟩ :
        Furtwaengler.DieudonneDwork.rIntegralRatSubring p)

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
theorem coeff_logOf_rationalArtinHasseNormalizedExpMinusOneSeries_eq_sum_Icc
    (d : ℕ) :
    (PowerSeries.coeff (R := ℚ) d)
        (PowerSeries.logOf (rationalArtinHasseNormalizedExpMinusOneSeries p)) =
      ∑ n ∈ Finset.Icc 1 d,
        (((-1 : ℚ) ^ (n + 1)) / n) *
          (PowerSeries.coeff (R := ℚ) d)
            ((rationalArtinHasseNormalizedExpMinusOneSeries p - 1) ^ n) := by
  have hsub0 :
      PowerSeries.constantCoeff
          (rationalArtinHasseNormalizedExpMinusOneSeries p - 1) = 0 := by
    simp [rationalArtinHasseNormalizedExpMinusOneSeries_constantCoeff]
  rw [PowerSeries.logOf_eq]
  exact Furtwaengler.FiniteArtinHasseFormal.coeff_subst_log_eq_sum_Icc
    (rationalArtinHasseNormalizedExpMinusOneSeries p - 1) hsub0 d

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
theorem coe_rationalArtinHasseNormalizedFactorialWeightedLogCoeff
    (d n : ℕ) (hn1 : 1 ≤ n) (hnd : n ≤ d) :
    ((rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n :
        Furtwaengler.DieudonneDwork.rIntegralRatSubring p) : ℚ) =
      (d.factorial : ℚ) *
        (((-1 : ℚ) ^ (n + 1) / n) *
          (PowerSeries.coeff (R := ℚ) d)
            ((rationalArtinHasseNormalizedExpMinusOneSeries p - 1) ^ n)) := by
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn1
  have hdiv : n ∣ d.factorial :=
    Nat.dvd_factorial (Nat.pos_of_ne_zero hn0) hnd
  have hcast_div :
      ((d.factorial / n : ℕ) : ℚ) = (d.factorial : ℚ) / (n : ℚ) :=
    Nat.cast_div hdiv (by exact_mod_cast hn0)
  simp only [rationalArtinHasseNormalizedFactorialWeightedLogCoeff,
    Subring.coe_mul, Subring.coe_natCast, Subring.coe_pow, Subring.coe_neg,
    Subring.coe_one]
  rw [hcast_div]
  field_simp [show (n : ℚ) ≠ 0 by exact_mod_cast hn0]

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
theorem coe_sum_rationalArtinHasseNormalizedFactorialWeightedLogCoeff
    (d : ℕ) :
    (((∑ n ∈ Finset.Icc 1 d,
        rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) :
        Furtwaengler.DieudonneDwork.rIntegralRatSubring p) : ℚ) =
      (d.factorial : ℚ) *
        (PowerSeries.coeff (R := ℚ) d)
          (PowerSeries.logOf
            (rationalArtinHasseNormalizedExpMinusOneSeries p)) := by
  classical
  rw [coeff_logOf_rationalArtinHasseNormalizedExpMinusOneSeries_eq_sum_Icc]
  rw [Finset.mul_sum]
  change (Furtwaengler.DieudonneDwork.rIntegralRatSubring p).subtype
      (∑ n ∈ Finset.Icc 1 d,
        rationalArtinHasseNormalizedFactorialWeightedLogCoeff p d n) =
    ∑ n ∈ Finset.Icc 1 d,
      (d.factorial : ℚ) *
        (((-1 : ℚ) ^ (n + 1) / n) *
          (PowerSeries.coeff (R := ℚ) d)
            ((rationalArtinHasseNormalizedExpMinusOneSeries p - 1) ^ n))
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnd : n ≤ d := (Finset.mem_Icc.mp hn).2
  exact coe_rationalArtinHasseNormalizedFactorialWeightedLogCoeff
    (p := p) d n hn1 hnd

end CyclotomicUnits

end BernoulliRegular

end
