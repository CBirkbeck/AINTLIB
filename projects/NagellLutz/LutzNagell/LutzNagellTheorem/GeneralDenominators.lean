import LutzNagell.LutzNagellTheorem.GeneralCurve
import LutzNagell.LutzNagellTheorem.PIDDenominators
import Mathlib.RingTheory.Localization.Rat

/-!
# Denominators on general Weierstrass curves

For a rational point on a general Weierstrass curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`
with `aᵢ ∈ ℤ`, if `x.den` equals a prime `p`, then we reach a contradiction.

This is the ℚ/ℤ special case of the general UFD result
`LutzNagell.PID.den_not_prime_of_on_curve`, obtained by instantiating `R = ℤ`, `K = ℚ`.
The bridge is `Rat.isFractionRingDen`, which identifies `x.den` with the `natAbs` of the
ring-theoretic denominator `IsFractionRing.den ℤ x`.

This suffices for the Lutz–Nagell integrality argument: when the rational root theorem gives
`x.den | p` for a prime `p`, we conclude `x.den ≠ p` and hence `x.den = 1`.

## Main results

* `LutzNagell.LutzNagellTheorem.den_ne_prime_of_on_general_curve`: if `(x, y)` is on the
  general Weierstrass curve and `x.den = p` (prime), then `False`.
-/

namespace LutzNagell
namespace LutzNagellTheorem

open WeierstrassCurve

variable (W : WeierstrassCurve ℤ)

/-! ### The key denominator lemma for general Weierstrass curves -/


/-- If `(x, y)` lies on a general Weierstrass curve with integral coefficients and `x.den = p`
for a prime `p`, then we reach a contradiction.

This is the ℚ/ℤ specialisation of `LutzNagell.PID.den_not_prime_of_on_curve`: with `R = ℤ`,
`K = ℚ`, the prime `p = x.den` is exactly the ring-theoretic denominator `IsFractionRing.den ℤ x`
up to sign (`Rat.isFractionRingDen`), so the general "denominator is not prime" lemma applies
directly. -/
theorem den_ne_prime_of_on_general_curve {x y : ℚ}
    (heq : y ^ 2 + (W.a₁ : ℚ) * x * y + (W.a₃ : ℚ) * y =
      x ^ 3 + (W.a₂ : ℚ) * x ^ 2 + (W.a₄ : ℚ) * x + (W.a₆ : ℚ))
    {p : ℕ} (hp : p.Prime) (hden : x.den = p) : False := by
  -- The ring-theoretic denominator `IsFractionRing.den ℤ x` is prime: its `natAbs` is `x.den = p`.
  have hden_prime : Prime (IsFractionRing.den ℤ x : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by rw [Rat.isFractionRingDen x, hden]; exact hp)
  -- Delegate to the general UFD lemma over `R = ℤ`, `K = ℚ`.
  -- `algebraMap ℤ ℚ` is `Int.cast`, so the curve equation matches after `algebraMap_int_eq`.
  refine PID.den_not_prime_of_on_curve W (K := ℚ) (y := y) ?_ hden_prime
  simpa only [algebraMap_int_eq, eq_intCast] using heq

end LutzNagellTheorem
end LutzNagell
