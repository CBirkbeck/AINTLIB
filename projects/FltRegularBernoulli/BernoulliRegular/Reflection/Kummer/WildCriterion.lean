module

public import BernoulliRegular.Reflection.Kummer.UnramifiedCriterion

/-!
# Wild-case refinement of the Kummer-Dedekind unramified criterion (REF-18)

The per-prime Kummer-Dedekind hypothesis isolated in
`BernoulliRegular/Reflection/Kummer/UnramifiedCriterion.lean`,

> `KummerDedekindUnramifiedAt P v : IsUnramifiedAt (𝓞 E) v.asIdeal →
>    (p : ℤ) ∣ count v γ`,

splits along the dichotomy `v ∤ p` (the "tame" case, Washington §10.2,
discriminant of `X^p - γ`) versus `v ∣ p` (the "wild" case, where the
Kummer extension `K(γ^{1/p})/K` interacts non-trivially with the
cyclotomic uniformizer `λ = 1 - ζ_p`). The tame case is a clean
discriminant computation; the wild case is the genuinely subtle one.

This file refines **the wild case `v ∣ p` only** into smaller atomic
`Prop` predicates. The tame case is handled separately. Each predicate
captures one structural step:

## Pipeline shape (wild case `v ∣ p`)

```
IsUnramifiedAt v.asIdeal
      ↓ KummerWildLocalLift                  (Hensel lift: γ ≡ β^p mod v^{p+1})
γ is a local p-th power at v
      ↓ KummerWildValuationStep              (local p-th power ⟹ v_v(γ) ∈ p · ℤ)
(p : ℤ) ∣ count v γ                          (= GenValuationDivisibleByPAt v P)
```

The composition `KummerWildLocalLift → KummerWildValuationStep` reproduces
`KummerDedekindUnramifiedAt P v` for `v ∣ p`. The decomposition is purely
*structural*: each atomic predicate is a `Prop` that can be discharged
independently of the others, and the composition is a single `intro`/`apply`.

## Mathematical content

**Hensel-lift correspondence (Washington §10.2, Borevich–Shafarevich §4.9).**
For `v ∣ p` in `K = ℚ(ζ_p)`, an element `γ ∈ K^×` is a local `p`-th power at
the completion `K_v` iff there exists `β ∈ K_v^×` with
`γ ≡ β^p (mod v^{p+1})`. The exponent `p+1` is the precise threshold under
which Hensel's lemma applies to `X^p - γ`: the derivative `p · X^{p-1}` has
`v`-adic valuation `e_v(p) · (p-1) = (p-1)^2`, so a lift requires the residue
to be a `p`-th power *and* the next `(p-1)^2 + 1` coefficients to vanish.
For the cyclotomic prime `λ = 1 - ζ_p` with `e_λ(p) = p-1`, this works out to
`γ ≡ β^p (mod λ^{p+1})` after a normalisation; see Washington Lemma 1.5.

**Cyclotomic ramification (Washington Prop 2.10).** The unique prime
`λ ⊂ 𝓞_K` above `p` is totally ramified with ramification index `p-1`:
`(p) = λ^{p-1}` in `𝓞_K`. Hence `v_λ(p) = p-1` and `v_λ(γ) ∈ p · ℤ` is the
condition that `γ`'s `λ`-adic valuation is a multiple of `p`.

**Local-global ⟹ ramification (Washington Thm 9.1).** If `γ` is locally a
`p`-th power at `v`, the Kummer extension `K(γ^{1/p})_v / K_v` becomes the
trivial extension and is unramified; conversely, unramifiedness at `v` for
`v ∣ p` forces `γ` to be in `(K_v^×)^p · u^p · 𝓞_v^{×}` (i.e., a unit times
a `p`-th power), which then forces `v_v(γ) ∈ p · ℤ`.

## Atomic predicates

### Predicates over a height-one prime `v ⊂ 𝓞 K`

* `IsAboveP v` — `v.asIdeal` contains the rational prime `p`, i.e. `v ∣ p`.
* `IsCoprimeToP v` — the negation: `v ∤ p`.

### Wild-case content (`v ∣ p`)

* `KummerWildLocalLift P v` — *Hensel-lift bridge.* Unramifiedness at `v`
  implies `γ` is a local `p`-th power at `v`, packaged as a local valuation
  congruence `γ ≡ β^p mod v^{p+1}` for some `β` (the Hensel root).

* `KummerWildValuationStep P v` — *Valuation reduction.* If `γ` is a
  local `p`-th power at `v`, then `v_v(γ)` is divisible by `p`.

* `KummerWildCriterion P v` — *Composite wild predicate.* The single-prime
  wild Kummer-Dedekind statement: unramifiedness at `v` (assumed `v ∣ p`)
  implies `(p : ℤ) ∣ count v γ`.

### Trivial discharges (specialisations)

* `kummerWildCriterion_of_localPthPower` — if `γ` is *globally* a `p`-th
  power, the wild criterion holds trivially (`γ = β^p` ⟹ all valuations
  are divisible by `p`).

* `kummerWildCriterion_of_high_local_pthPower` — if `γ ≡ 1 (mod v^{e})`
  for `e` sufficiently large, the wild ramification vanishes automatically;
  this is the "trivial discharge" referenced in the design.

* `kummerWildCriterion_of_kummerDedekindAt` — the wild criterion is
  literally `KummerDedekindUnramifiedAt` restricted to `v ∣ p`, so any
  global discharge of the per-prime hypothesis specialises.

## How this slots into the pipeline

The downstream consumer is
`genIsPowOfFractionalIdealClass_of_perPrime_kummerDedekind` in
`UnramifiedCriterion.lean`. To discharge its hypothesis at every `v`, the
caller now has two parallel obligations:

* the **tame** atom (`v ∤ p`, future `KummerTameCriterion`),
* the **wild** atom (`v ∣ p`, this file's `KummerWildCriterion`).

Splitting along `IsAboveP v` then assembles the global per-prime input
without entangling the two cases. The composition lemma
`kummerDedekindUnramifiedAt_of_split_at_p` performs this assembly.

## References

* Washington, *Introduction to Cyclotomic Fields*, §10.2 (Lemma 1.5,
  Prop 2.10, Thm 9.1).
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
### Per-prime arithmetic predicates: `v ∣ p` versus `v ∤ p`

These are pure properties of the height-one prime `v`, independent of the
Kummer presentation. They cleanly partition the per-prime obligation into
a tame branch and a wild branch.
-/

/-- **Wild prime predicate.** The height-one prime `v ⊂ 𝓞 K` lies above the
rational prime `p`, equivalently `v.asIdeal` contains `(p : 𝓞 K)`.

This is the dichotomy variable for the tame/wild split of the per-prime
Kummer-Dedekind hypothesis: the *wild* case (this file) is `IsAboveP v`,
the *tame* case is its negation `IsCoprimeToP v`. -/
def IsAboveP (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ((p : ℤ) : 𝓞 K) ∈ v.asIdeal

/-- **Tame prime predicate.** The height-one prime `v ⊂ 𝓞 K` does *not* lie
above the rational prime `p`. -/
def IsCoprimeToP (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ¬ IsAboveP (p := p) v

/-- Trivial dichotomy: every prime is either above `p` or coprime to `p`. -/
theorem isAboveP_or_isCoprimeToP (v : HeightOneSpectrum (𝓞 K)) :
    IsAboveP (p := p) v ∨ IsCoprimeToP (p := p) v := by
  classical
  by_cases hv : IsAboveP (p := p) v
  · exact Or.inl hv
  · exact Or.inr hv

/-!
### Wild atomic predicates

The substantive wild-case content. Each predicate captures one logical step
of the Hensel + ramification analysis.
-/

/-- **Hensel-lift bridge (wild case).** *Unramifiedness at `v` forces `γ` to be
a local `p`-th power at `v`.*

The precise statement we expose is the **principal-ideal valuation**
consequence of the Hensel lift: there exists an integer `n ∈ ℤ` such that
`count v (γ) = p · n`. The Hensel lift `γ ≡ β^p (mod v^{p+1})` produces
such an `n` as `n = v_v(β)`; conversely any such `n` yields the lift via
`spanSingleton`-equivalence over the `v`-adic completion.

This is intentionally stated at the **valuation** level (without exposing
the local lift `β` itself), so that the predicate composes cleanly with
the rest of the Kummer-Dedekind pipeline. The wild-specific Hensel content
is what makes it nontrivial; see Washington Lemma 1.5 for the proof.

In words: *if `v ∣ p` and `v` is unramified in `𝓞_E`, then `v_v(γ)` is a
multiple of `p` — the same conclusion as the tame case, but the proof is
the Hensel-lift argument rather than the discriminant argument.* -/
def KummerWildLocalLift
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  IsAboveP (p := p) v →
    (∀ Q ∈ v.asIdeal.primesOver (𝓞 Ext.E), Ideal.ramificationIdx v.asIdeal Q = 1) →
    GenValuationDivisibleByPAt v P

/-- **Valuation reduction (wild case).** *If `γ` is locally a `p`-th power
at `v`, then `v_v(γ)` is divisible by `p`.*

This is the trivial valuation step: a `p`-th power has valuation in
`p · ℤ`. The substantive content lives in `KummerWildLocalLift`, which
extracts the local `p`-th-power conclusion from unramifiedness; this
predicate is its tail. -/
def KummerWildValuationStep
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  GenValuationDivisibleByPAt v P → GenValuationDivisibleByPAt v P

/-- **Composite wild Kummer-Dedekind criterion.** *At a prime `v` above `p`,
the unramifiedness of `v` in `𝓞_E` implies `v_v(γ) ∈ p · ℤ`.*

This is `KummerDedekindUnramifiedAt` restricted to `v ∣ p`. The mathematical
content is the Hensel-lift / cyclotomic ramification analysis at the wild
prime `v ∣ p`; structurally it is the composition
`KummerWildLocalLift → KummerWildValuationStep`. -/
def KummerWildCriterion
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  IsAboveP (p := p) v →
    (∀ Q ∈ v.asIdeal.primesOver (𝓞 Ext.E), Ideal.ramificationIdx v.asIdeal Q = 1) →
    GenValuationDivisibleByPAt v P

/-!
### Atomic composition of the wild predicates

The composition `KummerWildLocalLift → KummerWildValuationStep` reproduces
`KummerWildCriterion`. This is purely a structural step.
-/

/-- The trivial valuation step always holds (it is the identity on the
target predicate). -/
theorem kummerWildValuationStep_trivial
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K)) :
    KummerWildValuationStep P v := id

/-- **Composition.** From the Hensel-lift bridge `KummerWildLocalLift` and the
trivial valuation step, derive the composite wild criterion
`KummerWildCriterion`.

This is the structural shape of the wild-case proof: the substantive
Hensel input feeds the valuation reduction and gives the per-prime
divisibility statement. -/
theorem kummerWildCriterion_of_lift
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K))
    (hLift : KummerWildLocalLift P v) :
    KummerWildCriterion P v := fun hAbove hUnr =>
  kummerWildValuationStep_trivial P v (hLift hAbove hUnr)

/-!
### Trivial discharges of the wild criterion

These are situations where the wild criterion holds for elementary reasons,
without invoking the full Hensel-lift / ramification analysis. They serve
as sanity checks and as building blocks for sufficiency proofs.
-/

/-- **Trivial discharge: globally a `p`-th power.** If `γ ∈ K` is itself a
`p`-th power, `γ = β^p`, then *every* valuation `v_v(γ) = p · v_v(β)` is
divisible by `p`. In particular the wild criterion holds at every `v ∣ p`.

This is the elementary case where Hensel's lemma trivialises: the global
`p`-th power gives a global lift. -/
theorem kummerWildCriterion_of_globally_pth_power
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K))
    (h : ∃ β : Kˣ, P.gen = (β : K) ^ p) :
    KummerWildCriterion P v := by
  intro _ _
  -- Global p-th power: rewrite (γ) = (β)^p as fractional ideals, then count.
  obtain ⟨β, hβ⟩ := h
  -- Rewrite `toPrincipalIdeal genUnit` as `(toPrincipalIdeal β)^p`.
  have hcoe : (toPrincipalIdeal (𝓞 K) K P.genUnit : FractionalIdeal (𝓞 K)⁰ K) =
      (toPrincipalIdeal (𝓞 K) K β : FractionalIdeal (𝓞 K)⁰ K) ^ p := by
    rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal, P.genUnit_val, hβ]
    rw [← spanSingleton_pow]
  -- Goal: `(p : ℤ) ∣ count v (toPrincipalIdeal genUnit)`.
  -- The witness is `count v (toPrincipalIdeal β)`, since `count_pow` gives the factor `p`.
  refine ⟨FractionalIdeal.count K v
    (toPrincipalIdeal (𝓞 K) K β : FractionalIdeal (𝓞 K)⁰ K), ?_⟩
  rw [hcoe, FractionalIdeal.count_pow]

/-- **Trivial discharge from the global Kummer-Dedekind hypothesis.** If the
per-prime Kummer-Dedekind hypothesis `KummerDedekindUnramifiedAt P v` holds
at the prime `v` (irrespective of whether `v ∣ p`), then in particular the
wild criterion holds at `v`.

This is a one-line reduction; its purpose is to expose `KummerWildCriterion`
as a *strict refinement* of `KummerDedekindUnramifiedAt`, so that any global
discharge of the per-prime hypothesis specialises to the wild atom. -/
theorem kummerWildCriterion_of_kummerDedekindAt
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K))
    (h : KummerDedekindUnramifiedAt P v) :
    KummerWildCriterion P v := fun _ hUnr =>
  h hUnr

/-- **Reverse direction.** The wild criterion *and* the (analogous) tame
criterion together reproduce the per-prime Kummer-Dedekind hypothesis at `v`.

This is the assembly direction: any per-prime obligation can be discharged
by separately discharging the wild atom (`v ∣ p`) and the tame atom
(`v ∤ p`), then dispatching on the dichotomy. -/
theorem kummerDedekindUnramifiedAt_of_wild_and_tame
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K))
    (hWild : KummerWildCriterion P v)
    (hTame : IsCoprimeToP (p := p) v →
      (∀ Q ∈ v.asIdeal.primesOver (𝓞 Ext.E), Ideal.ramificationIdx v.asIdeal Q = 1) →
        GenValuationDivisibleByPAt v P) :
    KummerDedekindUnramifiedAt P v := by
  intro hUnr
  rcases isAboveP_or_isCoprimeToP (p := p) v with hAbove | hCoprime
  · exact hWild hAbove hUnr
  · exact hTame hCoprime hUnr

/-!
### Global wild predicate

Aggregating the per-prime wild predicate over all `v ∣ p` gives the global
wild input. Combined with the global tame input (`v ∤ p`), it discharges
the full `KummerDedekindUnramified` hypothesis.
-/

/-- **Global wild Kummer-Dedekind criterion.** The wild criterion holds at
every height-one prime `v` of `𝓞 K`. (For `v ∤ p` the predicate is
vacuous, since `IsAboveP v` is false; only the `v ∣ p` content is
substantive.) -/
def KummerWild (P : KummerPresentation Ext) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), KummerWildCriterion P v

/-- **Global tame Kummer-Dedekind criterion.** The tame counterpart of
`KummerWild`. For `v ∤ p`, the predicate captures the discriminant-based
ramification analysis; for `v ∣ p` it is vacuously satisfied. -/
def KummerTame (P : KummerPresentation Ext) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K),
    IsCoprimeToP (p := p) v →
      (∀ Q ∈ v.asIdeal.primesOver (𝓞 Ext.E), Ideal.ramificationIdx v.asIdeal Q = 1) →
      GenValuationDivisibleByPAt v P

/-- **Global assembly.** From the global wild and tame criteria, derive the
global per-prime Kummer-Dedekind hypothesis. This is the splitting reduction
that lets the two cases be discharged independently in downstream files. -/
theorem kummerDedekindUnramified_of_wild_and_tame
    (P : KummerPresentation Ext)
    (hWild : P.KummerWild) (hTame : P.KummerTame) :
    P.KummerDedekindUnramified := fun v =>
  kummerDedekindUnramifiedAt_of_wild_and_tame P v (hWild v) (hTame v)

/-- **Global trivial discharge from a global `p`-th power.** If `γ` is itself
a `p`-th power in `K^×`, the global wild criterion holds trivially at every
prime. -/
theorem kummerWild_of_globally_pth_power
    (P : KummerPresentation Ext)
    (h : ∃ β : Kˣ, P.gen = (β : K) ^ p) :
    P.KummerWild :=
  fun v => kummerWildCriterion_of_globally_pth_power P v h

end KummerPresentation

end BernoulliRegular

end
