module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHasseLocalModel
public import BernoulliRegular.FLT37.PrimaryUnits.Part2
import Mathlib.Tactic

/-!
# Denominator units for the Kummer--Artin--Hasse local logarithm

The explicit `lambda`-local correction uses truncated logarithms whose
denominators are the integers `1, ..., p - 1`.  This file proves that those
integers are units in the localized/completed local cyclotomic integer ring.

This is deliberately a concrete unit API for the later Kummer--Artin--Hasse
formula files.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- If `0 < n < p`, then the integer `n` is not in the distinguished prime
`lambda` of `𝓞 K`. -/
theorem natCast_notMem_cyclotomicLambda_of_pos_lt {n : ℕ}
    (hn_pos : 0 < n) (hn_lt : n < p) :
    (n : 𝓞 K) ∉ Reflection.Local.cyclotomicLambda p K := by
  intro hn_mem
  have hn_span :
      (n : 𝓞 K) ∈ Ideal.span ({FLT37.zetaSubOne p K} : Set (𝓞 K)) := by
    rw [FLT37.span_zetaSubOne_eq_zetaPrime]
    exact hn_mem
  have hn_div : FLT37.zetaSubOne p K ∣ (n : 𝓞 K) :=
    (Ideal.mem_span_singleton.mp hn_span)
  have hn_div_int :
      (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
        (((n : ℤ) : 𝓞 K)) := by
    simpa [FLT37.zetaSubOne_def] using hn_div
  have hp_dvd_int : (p : ℤ) ∣ (n : ℤ) :=
    (FLT37.zetaSubOne_dvd_intCast_iff (p := p) (K := K) (n := (n : ℤ))).mp
      hn_div_int
  have hp_dvd_nat : p ∣ n :=
    Int.natCast_dvd_natCast.mp hp_dvd_int
  exact (Nat.not_dvd_of_pos_of_lt hn_pos hn_lt) hp_dvd_nat

/-- If `0 < n < p`, then `n` is a unit in the localization at `lambda`. -/
theorem isUnit_natCast_localCyclotomicRing_of_pos_lt {n : ℕ}
    (hn_pos : 0 < n) (hn_lt : n < p) :
    IsUnit (algebraMap (𝓞 K) (Reflection.Local.localCyclotomicRing p K) (n : 𝓞 K)) := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff
    (S := Reflection.Local.localCyclotomicRing p K)
    (I := Reflection.Local.cyclotomicLambda p K)]
  exact natCast_notMem_cyclotomicLambda_of_pos_lt (p := p) (K := K) hn_pos hn_lt

/-- If `0 < n < p`, then `n` is a unit in the completed local integer ring. -/
theorem isUnit_natCast_lambdaLocalIntegerRing_of_pos_lt {n : ℕ}
    (hn_pos : 0 < n) (hn_lt : n < p) :
    IsUnit (algebraMap (Reflection.Local.localCyclotomicRing p K)
      (LambdaLocalIntegerRing p K)
      (algebraMap (𝓞 K) (Reflection.Local.localCyclotomicRing p K) (n : 𝓞 K))) :=
  IsUnit.map
    (algebraMap (Reflection.Local.localCyclotomicRing p K) (LambdaLocalIntegerRing p K))
    (isUnit_natCast_localCyclotomicRing_of_pos_lt (p := p) (K := K) hn_pos hn_lt)

/-- The concrete completed-local unit represented by an integer denominator
`0 < n < p`. -/
def lambdaNatDenominatorUnit {n : ℕ} (hn_pos : 0 < n) (hn_lt : n < p) :
    (LambdaLocalIntegerRing p K)ˣ :=
  (isUnit_natCast_lambdaLocalIntegerRing_of_pos_lt (p := p) (K := K) hn_pos hn_lt).unit

@[simp]
theorem lambdaNatDenominatorUnit_val {n : ℕ}
    (hn_pos : 0 < n) (hn_lt : n < p) :
    (lambdaNatDenominatorUnit (p := p) (K := K) hn_pos hn_lt :
        LambdaLocalIntegerRing p K) =
      algebraMap (Reflection.Local.localCyclotomicRing p K)
        (LambdaLocalIntegerRing p K)
        (algebraMap (𝓞 K) (Reflection.Local.localCyclotomicRing p K) (n : 𝓞 K)) :=
  IsUnit.unit_spec
    (isUnit_natCast_lambdaLocalIntegerRing_of_pos_lt (p := p) (K := K) hn_pos hn_lt)

end KummerArtinHasse
end Furtwaengler
end BernoulliRegular
