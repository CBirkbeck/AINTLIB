import BernoulliRegular.CyclotomicUnits.KummerLogNormalization.ArtinHasseFiniteLogDecomposition

/-!
# Homogeneity of the Artin-Hasse normalized coordinate polynomial powers

The bookkeeping polynomial `samePrimeFiniteArtinHasseNormalizedCoordPoly N x =
∑_{n<N} monomial(n+1)(c_{n+1}·x^{n+1})` (where `c_{n+1}` is the `(n+1)`-th Artin-Hasse coefficient) is
the substitution `T ↦ x·T` of the **unscaled** polynomial `samePrimeFiniteArtinHasseNormalizedCoordPoly
N 1 = ∑_{n<N} monomial(n+1)(c_{n+1})`.  Consequently each coefficient of a power factors a clean `x^d`:

  `coeff_d ((Poly N x)^a) = coeff_d ((Poly N 1)^a) · x^d`.

This is the structural homogeneity that makes the degree-`d` Artin-Hasse log slice depend on the
Dwork-parameter approximant `x` only through the single power `x^d`.  It lets the level-`107` ↔
level-`71` deg-`68` slice comparison reduce to comparing `x₁₀₇^{68}` and `x₇₁^{68}` (which differ by
`(λ)^{139}`) times an `x`-independent constant.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
/-- **The coordinate polynomial is the `T ↦ x·T` substitution of its unscaled (`x = 1`) form**
(proven): `Poly N x = (Poly N 1).comp (C x · X)`.  Both sides are `∑_{n<N} monomial(n+1)(c_{n+1}·
x^{n+1})`: the `comp (C x · X)` sends `monomial (n+1) c` to `monomial (n+1) (c·x^{n+1})`. -/
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_eq_comp_C_mul_X
    (N : ℕ) (x : ValuedIntegerRing p K) :
    samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N x =
      (samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N 1).comp
        (Polynomial.C x * Polynomial.X) := by
  rw [samePrimeFiniteArtinHasseNormalizedCoordPoly,
    samePrimeFiniteArtinHasseNormalizedCoordPoly]
  rw [Polynomial.comp]
  rw [Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  rw [Polynomial.eval₂_monomial]
  rw [mul_pow, ← Polynomial.C_pow]
  rw [one_pow, mul_one]
  rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul]
  ring

omit [NumberField.IsCMField K] in
/-- **Homogeneity of the coordinate-polynomial powers** (proven): `coeff_d ((Poly N x)^a) = coeff_d
((Poly N 1)^a) · x^d`.  Substitution `T ↦ x·T` (`…_eq_comp_C_mul_X`) commutes with taking the `a`-th
power (`comp` is a ring hom in the first argument), and `Polynomial.comp_C_mul_X_coeff` reads off the
`x^d` factor. -/
theorem samePrimeFiniteArtinHasseNormalizedCoordPoly_pow_coeff_eq_mul_pow
    (N a d : ℕ) (x : ValuedIntegerRing p K) :
    ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N x) ^ a).coeff d =
      ((samePrimeFiniteArtinHasseNormalizedCoordPoly (p := p) (K := K) N 1) ^ a).coeff d *
        x ^ d := by
  rw [samePrimeFiniteArtinHasseNormalizedCoordPoly_eq_comp_C_mul_X (p := p) (K := K) N x]
  rw [← Polynomial.pow_comp]
  rw [Polynomial.comp_C_mul_X_coeff]

end CyclotomicUnits
end BernoulliRegular

end
