module

public import
  BernoulliRegular.CyclotomicUnits.KummerLogNormalization.ArtinHasseFiniteLogDecomposition

/-!
# Homogeneity of the Artin-Hasse normalized coordinate polynomial powers

The normalized coordinate polynomial at `x` is obtained from its value at `1` by
substituting `T ↦ x * T`. Consequently, each coefficient of a power factors as its
value at `x = 1` times the corresponding power of `x`.

## Main results

* `samePrimeFiniteArtinHasseNormalizedCoordPoly_eq_comp_C_mul_X` gives the substitution formula.
* `samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq_mul_pow` gives coefficient
  homogeneity for powers.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
/-- The coordinate polynomial at `x` is obtained from its value at `1` by substituting
`T ↦ x * T`. -/
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_eq_comp_C_mul_X
    (N : ℕ) (x : ValuedIntegerRing p K) :
    samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N x =
      (samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N 1).comp
        (Polynomial.C x * Polynomial.X) := by
  rw [samePrimeFiniteArtinHasseNormalizedCoordPoly,
    samePrimeFiniteArtinHasseNormalizedCoordPoly, Polynomial.comp,
    Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  rw [Polynomial.eval₂_monomial, mul_pow, ← Polynomial.C_pow, one_pow, mul_one,
    ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul]
  ring

omit [NumberField.IsCMField K] in
/-- The degree-`d` coefficient of the `a`-th power factors as its value at `x = 1`
times `x ^ d`. -/
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq_mul_pow
    (N a d : ℕ) (x : ValuedIntegerRing p K) :
    ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N x) ^ a).coeff d =
      ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N 1) ^ a).coeff d *
        x ^ d := by
  rw [samePrimeFiniteArtinHasseNormalizedCoordPoly_eq_comp_C_mul_X (p := p) (K := K) N x,
    ← Polynomial.pow_comp, Polynomial.comp_C_mul_X_coeff]

end CyclotomicUnits
end BernoulliRegular

end
