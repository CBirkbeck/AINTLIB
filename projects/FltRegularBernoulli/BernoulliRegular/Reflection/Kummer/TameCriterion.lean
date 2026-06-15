module

public import BernoulliRegular.Reflection.Kummer.UnramifiedCriterion

/-!
# Tame Kummer-Dedekind ramification criterion (REF-18 step 1.5, tame case)

For an unramified cyclic degree-`p` Kummer extension `E = K(γ^{1/p})` of
`K = ℚ(ζ_p)`, the per-prime Kummer-Dedekind criterion in
`UnramifiedCriterion.lean` packages the unramifiedness obligation as

```
KummerDedekindUnramifiedAt P v :=
  IsUnramifiedAt (𝓞 E) v.asIdeal → (p : ℤ) ∣ count v γ.
```

This file refines the **tame case** `v ∤ p` of that obligation into a clean
atomic per-prime predicate `TameKummerCriterion P v`, and provides the
two trivial discharges:

1. when `count v γ = 0` (γ is a v-unit) — divisibility holds trivially;
2. when `(p : ℤ) ∣ count v γ` already — divisibility holds by hypothesis,
   so unramifiedness is irrelevant.

## Why a separate atom?

In Washington §10.2 / Borevich-Shafarevich §4.9, the tame-Kummer case
(`v ∤ p`) admits a clean discriminant computation: for `f := X^p - γ`,

> `disc(f) = ± p^p · γ^{p-1}`,

and a prime `v` of `𝓞 K` ramifies in the splitting field iff it divides
the discriminant. Modulo the inert factor `± p^p` (which is a unit at
`v ∤ p`), this gives

> `v` is unramified in `E/K` iff `v_v(γ) ≡ 0 (mod p)`.

The wild case `v ∣ p` (which uses the cyclotomic uniformiser `1 - ζ_p`)
is *not* covered by this file; it is the substantive deferred input
that closes out the bridge.

## What this file delivers

* `TameKummerCriterion P v`: the bare per-prime statement
  `IsUnramifiedAt (𝓞 E) v.asIdeal → (p : ℤ) ∣ count v γ`. This is
  *definitionally equal* to `KummerDedekindUnramifiedAt P v`; the two are
  separate because their *intended discharge route* differs: the tame
  predicate is meant to be discharged either trivially (this file) or via
  the discriminant calculation (deferred), whereas
  `KummerDedekindUnramifiedAt` is the umbrella obligation expected to
  combine the tame and wild routes.

* `tameKummerCriterion_of_count_eq_zero`: trivial discharge when
  `count v γ = 0` (the `γ`-valuation is zero — a v-unit).

* `tameKummerCriterion_of_dvd_count`: trivial discharge when
  `(p : ℤ) ∣ count v γ` already.

* `kummerDedekindUnramifiedAt_of_tameKummerCriterion`: the pointwise
  passage from the tame atom to the umbrella obligation.

## What's *not* discharged here

The substantive Mathlib content that would *prove* `TameKummerCriterion P v`
non-trivially (i.e. when `count v γ ∉ p · ℤ` and `v ∤ p`) is

> for `f = X^p - γ`, the ramification index `e(P|v)` of any prime
> `P ⊂ 𝓞_E` over `v` equals `gcd(p, count v γ)` mod `p` units, hence
> `e(P|v) = 1` iff `p ∣ count v γ`.

This is a Kummer-theoretic ramification statement that is only partially
present in mathlib (`Ideal.ramificationIdx`, `IsUnramifiedAt`,
`Polynomial.discriminant`). Its full deductive proof is left to a
downstream development; this file isolates the trivial cases and
documents the obstruction.

## References

* Washington, *Introduction to Cyclotomic Fields*, §10.2.
* Borevich-Shafarevich, *Number Theory*, §4.9.
* Diekmann, *FLT for regular primes*, §6.
-/

@[expose] public section

noncomputable section

open NumberField FractionalIdeal Polynomial IsDedekindDomain
open scoped nonZeroDivisors

namespace BernoulliRegular

set_option linter.unusedSectionVars false

namespace KummerPresentation

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {χ : MulChar (ZMod p)ˣ ℚ}
variable {Comp : CyclotomicFieldClassGroupPSylowComponent (p := p) K}
variable {Ext : ComponentUnramifiedCyclicDegreePExtension (p := p) K χ Comp}

/-!
### The tame per-prime atom
-/

/-- **Tame Kummer-Dedekind criterion (atomic).**

At a single height-one prime `v ⊂ 𝓞 K`, the assertion that

> if `v` is unramified in `𝓞_E`, then `(p : ℤ) ∣ count v (γ)`.

This is the atomic per-prime form of the *tame* Kummer-Dedekind
ramification criterion. It is definitionally equal to
`KummerDedekindUnramifiedAt P v`; the rename marks the *intended*
discharge route — either by the trivial cases below, or by the
discriminant calculation for `X^p - γ` (Washington §10.2) at a tame
prime `v ∤ p`.

For wild primes `v ∣ p`, the same Prop holds but the discharge requires
the cyclotomic-uniformiser analysis (`1 - ζ_p`) instead. -/
def TameKummerCriterion
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  (∀ Q ∈ v.asIdeal.primesOver (𝓞 Ext.E), Ideal.ramificationIdx v.asIdeal Q = 1) →
    GenValuationDivisibleByPAt v P

/-!
### Trivial discharges

The two discharges below cover the cases where the divisibility statement
is *unconditionally* true — independent of the `IsUnramifiedAt v` premise.
This isolates the substantive content (which only concerns the case
`count v γ ∉ p · ℤ`) and lets downstream files dispatch the trivial
ones cheaply.
-/

/-- **Trivial discharge: γ is a v-unit.**

If `count v (γ) = 0` (i.e. `γ` has trivial valuation at `v`), then
`(p : ℤ) ∣ count v (γ) = 0` holds trivially, and the tame criterion is
satisfied independently of whether `v` is unramified in `E`. -/
theorem tameKummerCriterion_of_count_eq_zero
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K))
    (hcount : FractionalIdeal.count K v
      (toPrincipalIdeal (𝓞 K) K P.genUnit : FractionalIdeal (𝓞 K)⁰ K) = 0) :
    P.TameKummerCriterion v := by
  intro _
  -- Goal: `(p : ℤ) ∣ count v γ`. Use `hcount : count v γ = 0`.
  rw [GenValuationDivisibleByPAt, hcount]
  exact dvd_zero _

/-- **Trivial discharge: `(p : ℤ) ∣ count v γ` already holds.**

If the per-prime divisibility hypothesis is already known at `v`
(perhaps proved by a different route — e.g. from a known global
factorisation), then the tame criterion holds at `v` independently of
the unramifiedness premise. -/
theorem tameKummerCriterion_of_dvd_count
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K))
    (hdvd : P.GenValuationDivisibleByPAt v) :
    P.TameKummerCriterion v :=
  fun _ => hdvd

/-!
### Pointwise passage to the umbrella obligation
-/

/-- **From the tame atom to the umbrella obligation, pointwise.**

The tame per-prime predicate `TameKummerCriterion P v` is *definitionally
equal* to the umbrella per-prime obligation `KummerDedekindUnramifiedAt P v`;
this lemma records the passage so downstream code can keep the two views
syntactically separate while remaining defeq. -/
theorem kummerDedekindUnramifiedAt_of_tameKummerCriterion
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K))
    (h : P.TameKummerCriterion v) :
    P.KummerDedekindUnramifiedAt v :=
  h

/-- **Converse passage**: the umbrella obligation gives back the tame atom
(again, defeq, in the same direction). -/
theorem tameKummerCriterion_of_kummerDedekindUnramifiedAt
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K))
    (h : P.KummerDedekindUnramifiedAt v) :
    P.TameKummerCriterion v :=
  h

/-- **Equivalence**: the tame per-prime atom and the umbrella per-prime
obligation are the same Prop. This is the structural sanity check
licensing the two phrasings to be used interchangeably in proofs. -/
theorem tameKummerCriterion_iff_kummerDedekindUnramifiedAt
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K)) :
    P.TameKummerCriterion v ↔ P.KummerDedekindUnramifiedAt v :=
  Iff.rfl

end KummerPresentation

end BernoulliRegular

end
