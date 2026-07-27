/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.RankInequality
public import BernoulliRegular.Herbrand.Basic

/-!
# Reflection — boundary case at `j = 1` (T043)

The reflection rank inequality from `T042b`
(`reflection_gal_card_le_one_of_oddVanishing`) excludes the boundary
character, namely the `χ` whose twist dual is the distinguished
Teichmüller-tagging character. In the classical setup this is the `ω`-line
on the Galois side, which the `E/E^p` vanishing from `T041` does not cover
(the torsion of cyclotomic units contributes exactly there).

The boundary case is closed using Herbrand's theorem (`T035`). Following
the Herbrand direction (nontrivial odd component `⇒` ordinary Bernoulli
`p`-divisibility), the contrapositive yields: if the relevant ordinary
Bernoulli number is not `p`-adic-divisible, the Galois-side boundary
component is trivial.

Since the current project expresses reflection over the abstract Kummer
pairing `KummerPairingRawComparison` (`T042a`) and Herbrand over the
data-driven `CyclotomicClassGroupPSylowComponent`, we expose the
boundary bound through a small honest bridge
`BoundaryHerbrandBridge` that transports a non-triviality witness of the
reflection component to the ordinary-Bernoulli output of `T035b`.

## Main definitions

* `BoundaryHerbrandBridge R χ n`: bridge recording
  "non-trivial reflection boundary component `⇒` p-adic divisibility of
  `bernoulli n / n`".

## Main results

* `reflection_boundary_gal_eq_bot`: **T043** (subgroup form) — if the
  ordinary Bernoulli `bernoulli n / n` is not `p`-adic-divisible, the
  reflection boundary component is the trivial subgroup.
* `reflection_boundary_gal_card_le_one`: **T043** (cardinality form) —
  same conclusion, phrased as `Nat.card ≤ 1`, the shape `T044a`
  consumes.

## References

* Washington, *Introduction to Cyclotomic Fields*, §10.3, boundary.
* Diekmann, *FLT for regular primes*, §6 (boundary).
-/

@[expose] public section

universe u v

noncomputable section

open NumberField

namespace BernoulliRegular


section Boundary

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
variable {P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)}

/-- Honest bridge from a nontrivial reflection-boundary Galois component to
the ordinary-Bernoulli `p`-divisibility conclusion of Herbrand (`T035`).

The bridge is parameterised by the boundary character `χ_boundary`
(classically the `ω`-line, matching the `T041` distinguished character
under the `characterTwistDual` twist) and the Bernoulli index `n`
(classically `p - 1`, the von-Staudt-Clausen boundary).

Its instantiation chains `T035a`'s
`generalizedBernoulliPDivisible_of_nontrivial_oddComponent` with
`T035b`'s `ordinaryBernoulliPDivisible_of_generalizedBernoulliPDivisible`
through the not-yet-built intrinsic identification of the reflection
component with a `CyclotomicClassGroupPSylowComponent`. We expose the
bridge here to keep `T043` transport-level. -/
structure BoundaryHerbrandBridge
    {N : NondegenerateKummerPairing (p := p) (K := K) P}
    {T : KummerPairingTwistData (p := p) (K := K) N}
    (R : KummerPairingRawComparison (p := p) (K := K) N T)
    (χ_boundary : MulChar (ZMod p)ˣ ℚ) (n : ℕ) where
  /-- If the boundary Galois component is nontrivial, the ordinary
  Bernoulli `bernoulli n / n` is `p`-adic-divisible. -/
  nontrivial_implies_ordinary_bernoulli_pDivisible :
    R.galComponent χ_boundary ≠ ⊥ → OrdinaryBernoulliPDivisible p n

namespace BoundaryHerbrandBridge

variable {p K}
variable {N : NondegenerateKummerPairing (p := p) (K := K) P}
variable {T : KummerPairingTwistData (p := p) (K := K) N}

/-- **T043** (subgroup form): when the boundary Bernoulli is not
`p`-adic-divisible, the reflection boundary component is trivial. -/
theorem reflection_boundary_gal_eq_bot
    {R : KummerPairingRawComparison (p := p) (K := K) N T}
    {χ_boundary : MulChar (ZMod p)ˣ ℚ} {n : ℕ}
    (Br : BoundaryHerbrandBridge (p := p) (K := K) R χ_boundary n)
    (h_notdvd : ¬ OrdinaryBernoulliPDivisible p n) :
    R.galComponent χ_boundary = ⊥ := by
  by_contra h
  exact h_notdvd (Br.nontrivial_implies_ordinary_bernoulli_pDivisible h)

/-- **T043** (cardinality form): when the boundary Bernoulli is not
`p`-adic-divisible, the reflection boundary component has cardinality
`≤ 1`. This is the shape `T044a` consumes. -/
theorem reflection_boundary_gal_card_le_one
    {R : KummerPairingRawComparison (p := p) (K := K) N T}
    {χ_boundary : MulChar (ZMod p)ˣ ℚ} {n : ℕ}
    (Br : BoundaryHerbrandBridge (p := p) (K := K) R χ_boundary n)
    (h_notdvd : ¬ OrdinaryBernoulliPDivisible p n) :
    Nat.card (R.galComponent χ_boundary : Type _) ≤ 1 := by
  have hbot : R.galComponent χ_boundary = ⊥ :=
    Br.reflection_boundary_gal_eq_bot h_notdvd
  rw [hbot]
  simp

end BoundaryHerbrandBridge

end Boundary

end BernoulliRegular

end
