module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHasseValuationTrace
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# The p-adic divisibility target for the Kummer--Artin--Hasse trace

In the field `ℚ_[p]`, ordinary divisibility by `p` is vacuous.  The local
Kummer--Artin--Hasse integrality statement needs the stronger assertion that
the trace term lies in `p * ℤ_[p]`.  This file fixes that target explicitly and
specializes it to both the legacy `< p` trace term and the corrected
`log_≤p` trace term.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The `p`-adic integers indexed by a bundled prime. -/
abbrev PadicIntOfPrime (q : Nat.Primes) : Type :=
  @PadicInt q.1 ⟨q.2⟩

/-- Honest p-adic divisibility by the rational prime: `x` lies in
`p * ℤ_[q]` inside `ℚ_[q]`.  This is intentionally not field-level
`Dvd.dvd`. -/
def PadicDivisibleByPrime (q : Nat.Primes) (x : PadicOfPrime q) : Prop :=
  ∃ z : PadicIntOfPrime q,
    x = (q.1 : PadicOfPrime q) * (z : PadicOfPrime q)

theorem padicDivisibleByPrime_iff_norm_le
    (q : Nat.Primes) (x : PadicOfPrime q) :
    PadicDivisibleByPrime q x ↔ ‖x‖ ≤ ((q.1 : ℝ)⁻¹) := by
  have hnorm_p : ‖(q.1 : PadicOfPrime q)‖ = ((q.1 : ℝ)⁻¹) := by
    simp [PadicOfPrime, @Padic.norm_p q.1 ⟨q.2⟩]
  constructor
  · rintro ⟨z, rfl⟩
    have hz_norm : ‖(z : PadicOfPrime q)‖ ≤ 1 := by
      simpa [PadicIntOfPrime, PadicOfPrime] using
        (@PadicInt.norm_le_one q.1 ⟨q.2⟩ z)
    calc
      ‖(q.1 : PadicOfPrime q) * (z : PadicOfPrime q)‖ =
          ((q.1 : ℝ)⁻¹) * ‖(z : PadicOfPrime q)‖ := by
        rw [norm_mul, hnorm_p]
      _ ≤ ((q.1 : ℝ)⁻¹) * 1 :=
        mul_le_mul_of_nonneg_left hz_norm
          (inv_nonneg.mpr (Nat.cast_nonneg q.1))
      _ = ((q.1 : ℝ)⁻¹) := by rw [mul_one]
  · intro hx
    have hq_pos : (0 : ℝ) < q.1 := by
      exact_mod_cast q.2.pos
    refine ⟨⟨x / (q.1 : PadicOfPrime q), ?_⟩, ?_⟩
    · calc
        ‖x / (q.1 : PadicOfPrime q)‖ =
            ‖x‖ / ‖(q.1 : PadicOfPrime q)‖ := norm_div _ _
        _ = ‖x‖ / ((q.1 : ℝ)⁻¹) := by rw [hnorm_p]
        _ ≤ 1 := by
          rw [div_le_one (inv_pos.mpr hq_pos)]
          exact hx
    · have hq_ne : (q.1 : PadicOfPrime q) ≠ 0 := by
        exact_mod_cast q.2.ne_zero
      rw [mul_div_cancel₀ x hq_ne]

/-- The legacy non-vacuous divisibility target for the old `< p` trace term.
The active `A`-term route should use
`lambdaValuedCorrectedATraceDivisibleByP`. -/
def lambdaValuedATraceDivisibleByP
    (u : LambdaValuedPrincipalUnitSubgroup p K 1) : Prop :=
  PadicDivisibleByPrime (lambdaPadicPrime p) (lambdaValuedATrace p K u)

theorem lambdaValuedATraceDivisibleByP_iff_norm_le
    (u : LambdaValuedPrincipalUnitSubgroup p K 1) :
    lambdaValuedATraceDivisibleByP p K u ↔
      ‖lambdaValuedATrace p K u‖ ≤ ((p : ℝ)⁻¹) := by
  simpa [lambdaValuedATraceDivisibleByP, lambdaPadicPrime_val] using
    padicDivisibleByPrime_iff_norm_le
      (q := lambdaPadicPrime p) (x := lambdaValuedATrace p K u)

/-- The exact non-vacuous divisibility target for the corrected
Kummer--Artin--Hasse `A`-term trace. -/
def lambdaValuedCorrectedATraceDivisibleByP
    (u : LambdaValuedPrincipalUnitSubgroup p K 1) : Prop :=
  PadicDivisibleByPrime (lambdaPadicPrime p)
    (lambdaValuedCorrectedATrace p K u)

theorem lambdaValuedCorrectedATraceDivisibleByP_iff_norm_le
    (u : LambdaValuedPrincipalUnitSubgroup p K 1) :
    lambdaValuedCorrectedATraceDivisibleByP p K u ↔
      ‖lambdaValuedCorrectedATrace p K u‖ ≤ ((p : ℝ)⁻¹) := by
  simpa [lambdaValuedCorrectedATraceDivisibleByP, lambdaPadicPrime_val] using
    padicDivisibleByPrime_iff_norm_le
      (q := lambdaPadicPrime p) (x := lambdaValuedCorrectedATrace p K u)

end KummerArtinHasse
end Furtwaengler
end BernoulliRegular
