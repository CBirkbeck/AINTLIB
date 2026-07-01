module

public import BernoulliRegular.Reflection.Final

/-!
# Reflection — class-number transfer in the regular-prime degenerate case

This file is the top-level *consumer* of the
`KummerToUnitQuotientInclusion.refl_via_chain_for_regular_prime`
discharge from `ReflectionBridgeChain.lean`.  Combined with the rest of
the reflection chain (`RankInequality.lean`, `Boundary.lean`,
`Final.lean`), it would yield the final `dvd_h_of_dvd_hPlus` transfer
unconditionally in the regular-prime case (i.e. when
`Subsingleton (ClassGroup (𝓞 K))`).

## The degenerate observation

For a number field `K` with `Subsingleton (ClassGroup (𝓞 K))`:

* `h K = Fintype.card (ClassGroup (𝓞 K)) = 1`,
* the injection `Cl(𝓞 K⁺) ↪ Cl(𝓞 K)` of `T044` (proved without any
  axiom) forces `Subsingleton (ClassGroup (𝓞 K⁺)))` as well, hence
  `hPlus K = 1`.

In particular, the hypothesis `(p : ℕ) ∣ hPlus K` of a `T044b`-style
transfer is **vacuously false** for any `p` prime: `p ∣ 1` would force
`p = 1`, contradicting primality.  So the regular-prime form of
`T044b` reduces to the trivial implication "from a contradiction one
may derive anything", and in particular the conclusion `(p : ℕ) ∣ h K`
holds vacuously.

## Why we still package it

This packaging serves three roles:

1. **It records the regular-prime branch as a top-level theorem.**
   Downstream users who already know they are in the regular case (e.g.
   verified small primes such as `p = 23` via
   `BernoulliFast.TwentyThree`) can dispatch to this lemma directly,
   with no `ReflectionMinusNontrivialityBridge` instantiation required.

2. **It composes cleanly with the rest of the reflection chain.**
   In the standard reflection argument, `refl_via_chain_for_regular_prime`
   discharges the Kummer-to-unit-quotient inclusion atom; the present
   lemma absorbs the *consumer side* of the same regular-prime
   discharge, closing the chain end-to-end.

3. **It documents the degenerate nature explicitly.**  The proof goes
   through `Nat.Prime.one_lt`, making the vacuity of the premise
   visible at the proof level.

## Files

* `BernoulliRegular/Reflection/Final.lean` — the bridge-driven `T044b`
  (`dvd_h_of_dvd_hPlus`).
* `BernoulliRegular/Reflection/ReflectionBridgeChain.lean` —
  `KummerToUnitQuotientInclusion.refl_via_chain_for_regular_prime`,
  the upstream regular-prime chain discharge.
* `BernoulliRegular/TotallyRealSubfield/ClassGroup.lean` —
  `classGroupMap_injective`, the unconditional `Cl(𝓞 K⁺) ↪ Cl(𝓞 K)`
  used here to propagate `Subsingleton` from `K` to `K⁺`.

## References

* Washington, *Introduction to Cyclotomic Fields*, §4.14 / §10.3.
* Diekmann, *FLT for regular primes*, §6.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

section ReflectionFinalRegularPrime

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

include hp_odd in
/-- **Subsingleton transfer along `Cl(𝓞 K⁺) ↪ Cl(𝓞 K)`.**

When `Cl(𝓞 K)` is a subsingleton, the unconditional injection
`Cl(𝓞 K⁺) ↪ Cl(𝓞 K)` from `classGroupMap_injective` (Diekmann Prop 55,
unconditional) propagates the property to `Cl(𝓞 K⁺)`. -/
theorem subsingleton_classGroup_maximalRealSubfield_of_subsingleton
    [Subsingleton (ClassGroup (𝓞 K))] :
    Subsingleton (ClassGroup (𝓞 (NumberField.maximalRealSubfield K))) :=
  (classGroupMap_injective p hp_odd K).subsingleton

include hp_odd in
/-- Under `Subsingleton (ClassGroup (𝓞 K))`, the totally real class
number `hPlus K` equals one.  Combined with primality of `p`, this
makes the hypothesis `p ∣ hPlus K` of `T044b` vacuously false. -/
theorem hPlus_eq_one_of_subsingleton
    [Subsingleton (ClassGroup (𝓞 K))] :
    hPlus K = 1 := by
  have hsub :
      Subsingleton (ClassGroup (𝓞 (NumberField.maximalRealSubfield K))) :=
    subsingleton_classGroup_maximalRealSubfield_of_subsingleton p hp_odd K
  exact Nat.le_antisymm (Fintype.card_le_one_iff_subsingleton.mpr hsub) Fintype.card_pos

/-- Under `Subsingleton (ClassGroup (𝓞 K))`, the class number `h K`
equals one.  Hence `p ∣ h K` holds iff `p = 1`. -/
theorem h_eq_one_of_subsingleton
    [hsub : Subsingleton (ClassGroup (𝓞 K))] :
    h K = 1 :=
  Nat.le_antisymm (Fintype.card_le_one_iff_subsingleton.mpr hsub) Fintype.card_pos

include hp hp_odd in
/-- **`T044b`, regular-prime degenerate case.**

Top-level transfer `p ∣ hPlus K ⟹ p ∣ h K` available *unconditionally*
when `Cl(𝓞 K)` is a subsingleton — i.e. in the strong-form regular
case for the relevant `p`-part.  Combined with the regular-prime
discharge of the Kummer-to-unit-quotient inclusion atom
(`KummerToUnitQuotientInclusion.refl_via_chain_for_regular_prime` in
`ReflectionBridgeChain.lean`), this closes the reflection chain
end-to-end without any `ReflectionMinusNontrivialityBridge`
instantiation in the regular case.

**Vacuity of the premise.**  The injection `Cl(𝓞 K⁺) ↪ Cl(𝓞 K)`
proved unconditionally in `classGroupMap_injective`
(Diekmann Prop 55) propagates `Subsingleton` from `K` to `K⁺`, so
`hPlus K = 1`; the premise `(p : ℕ) ∣ hPlus K` then forces
`(p : ℕ) ∣ 1`, contradicting `p.Prime`.  The conclusion is therefore
vacuously true and the proof simply derives a contradiction from the
premise.  The lemma is still useful as a degenerate-case dispatcher
that records the regular-prime branch at the top level. -/
theorem dvd_h_of_dvd_hPlus_of_subsingleton_class_group
    [Subsingleton (ClassGroup (𝓞 K))]
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ h K := by
  -- The premise is vacuous: `hPlus K = 1` forces `p ∣ 1`, hence `p = 1`,
  -- contradicting `p.Prime` (which gives `1 < p`).
  exfalso
  have hone : hPlus K = 1 := hPlus_eq_one_of_subsingleton p hp_odd K
  rw [hone] at h_plus
  exact (Nat.Prime.one_lt hp.out).ne' (Nat.dvd_one.mp h_plus)

include hp hp_odd in
/-- **Regular-prime corollary, `IsRegularPrime`-flavoured form.**

When `K = ℚ(ζ_p)` (in any model — we work over a generic `K` with the
appropriate cyclotomic and CM structure, plus a numerical bridge
`heq` identifying `Fintype.card (ClassGroup (𝓞 K))` with the literal
class number of `CyclotomicField p ℚ` that `IsRegularPrime` is defined
over), regularity of `p` rules out the premise `(p : ℕ) ∣ hPlus K`
vacuously.

Internally this follows the same vacuity route as
`dvd_h_of_dvd_hPlus_of_subsingleton_class_group`: regularity gives
`p.Coprime (h K)`, which combined with `hPlus K ∣ h K` (Diekmann
Prop 55, unconditional) and `p ∣ hPlus K` would force
`p ∣ Nat.gcd p (h K) = 1`. -/
theorem dvd_h_of_dvd_hPlus_of_regular
    (heq : Fintype.card (ClassGroup (𝓞 K)) =
      Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ))))
    (h_reg : IsRegularPrime p)
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ h K := by
  -- Vacuity: `IsRegularPrime p` says `p.Coprime h K`, and `hPlus K ∣ h K`
  -- together with `p ∣ hPlus K` would give `p ∣ h K`, contradicting
  -- coprimality.  We derive a contradiction and conclude vacuously.
  exfalso
  have hPlus_dvd : hPlus K ∣ h K := hPlus_dvd_h p hp_odd K
  have h_dvd : (p : ℕ) ∣ h K := h_plus.trans hPlus_dvd
  have hcop : ¬ (p : ℕ) ∣ h K := by
    rw [BernoulliRegular.h, heq]
    exact hp.out.coprime_iff_not_dvd.mp h_reg
  exact hcop h_dvd

end ReflectionFinalRegularPrime

end BernoulliRegular

end
