/-
Copyright (c) 2026 Bernoulli-Regular project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernoulli-Regular project contributors
-/
module

public import Init.Data.Nat.Gcd

/-!
# Fraction arithmetic for Bernoulli evaluation

The integer/natural fraction representation and its arithmetic primitives are shared by
runtime evaluation and proof-producing meta simprocs. Rational interpretation and correctness
proofs are supplied by `BernoulliFast.Cbv.Data`.
-/

-- Simproc refl proofs require clients to unfold these definitions during kernel checking.
@[expose] public section

namespace BernoulliRegular.BernoulliFast.Cbv

/-- Integer numerator and natural denominator, used only for fast ground
normalization by `cbv`. -/
abbrev Frac := Int × Nat

/-- Reduce a fraction by the numerator/denominator gcd, treating a zero denominator as zero. -/
def simplify : Frac → Frac
  | (_, 0) => (0, 1)
  | (p, q) =>
    let g := Nat.gcd p.natAbs q
    (p / (g : Int), q / g)

/-- Negate the numerator. -/
def negF (f : Frac) : Frac := (-f.1, f.2)

/-- Add fractions using a common denominator and reduce the result. -/
def addF : Frac → Frac → Frac
  | (p1, q1), (p2, q2) =>
    let g := Nat.gcd q1 q2
    let lcm := q1 / g * q2
    simplify (p1 * ((q2 / g) : Int) + p2 * ((q1 / g) : Int), lcm)

/-- Multiply fractions and reduce the result. -/
def mulF : Frac → Frac → Frac
  | (p1, q1), (p2, q2) =>
    simplify (p1 * p2, q1 * q2)

/-- Multiply by a natural number, cancelling common factors with the denominator. -/
def mulN (f : Frac) (c : Nat) : Frac :=
  let (p, q) := f
  let g := Nat.gcd c q
  simplify (p * ((c / g) : Int), q / g)

/-- Multiply by an integer and reduce the result. -/
def mulZ (f : Frac) (z : Int) : Frac :=
  let (p, q) := f
  simplify (p * z, q)

/-- Divide by a natural number, cancelling common factors with the numerator. -/
def divN (f : Frac) (d : Nat) : Frac :=
  let (p, q) := f
  let g := Nat.gcd p.natAbs d
  simplify (p / (g : Int), q * (d / g))

end BernoulliRegular.BernoulliFast.Cbv
