module

public import BernoulliRegular.GaussSum.PrimeFactorization.PrimesAboveP
public import BernoulliRegular.GaussSum.PrimeFactorization.GaloisAction
public import BernoulliRegular.GaussSum.PrimeFactorization.Valuation
public import BernoulliRegular.GaussSum.PrimeFactorization.Assembly
public import BernoulliRegular.GaussSum.PrimeFactorization.JacobiSums

/-!
# Prime factorization infrastructure for Gauss sums

This umbrella collects the arithmetic setup for the Stickelberger prime
factorization chain. The split `GaloisAction`, `Assembly`, and `JacobiSums`
umbrellas re-export their leaf files, so this file keeps only the stable
boundary imports.
-/
