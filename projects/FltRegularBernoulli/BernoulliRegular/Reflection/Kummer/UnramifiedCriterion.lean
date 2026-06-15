module

public import BernoulliRegular.Reflection.Kummer.UnramifiedUnit
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.FractionalIdeal.Inverse

/-!
# Kummer-Dedekind unramified criterion (REF-18 step 1.5)

This file refines the bridge from `IsUnramified (𝓞 K) (𝓞 E)` (the package
exposed by `ComponentUnramifiedCyclicDegreePExtension`) to
`KummerPresentation.GenIsPowOfFractionalIdealClass` (the weak form
`(γ) = J^p` in the group of fractional ideals).

This bridge — the **Kummer-Dedekind unramified criterion** — says

> For `E = K(γ^{1/p})` Kummer of degree `p`, `E/K` is unramified iff
> `v_q(γ) ∈ p · ℤ` for every prime `q ⊂ 𝓞_K`.

(Washington §10.2; Borevich-Shafarevich §4.9.) The forward direction at primes
not above `p` is a clean ramification computation from the discriminant of
`X^p - γ`; primes above `p` need a more delicate analysis using the cyclotomic
parameter `1 - ζ_p`.

The full bridge is mathematically substantive: it requires the Kummer-Dedekind
ramification analysis of `X^p - γ`, which is only partially in mathlib. We
therefore *refine* the obligation into:

1. **Atomic per-prime predicate**: `GenValuationDivisibleByPAt v` —
   `(p : ℤ) ∣ FractionalIdeal.count v γ` at a single prime `v`.
2. **Global per-prime predicate**: `GenValuationDivisibleByP` — the conjunction
   over all `v : HeightOneSpectrum (𝓞 K)`.
3. **Equivalence** between the per-prime accumulation and the weak form
   `GenIsPowOfFractionalIdealClass`. This is the **substantive content of this
   file**: a direct equivalence
   `GenValuationDivisibleByP ↔ GenIsPowOfFractionalIdealClass`,
   proved via the height-one prime factorisation of fractional ideals
   (`FractionalIdeal.finprod_heightOneSpectrum_factorization'`).

The remaining input — that the unramifiedness of `E/K` (i.e. `IsUnramified
(𝓞 K) (𝓞 E)` from `FltRegular.NumberTheory.Unramified`) implies the
per-prime predicate `GenValuationDivisibleByPAt` for every `v` — is the
**genuine Kummer-Dedekind hypothesis** and is supplied as an explicit
parameter `unramifiedCriterion` to the high-level reduction. This isolates
the only Kummer-Dedekind-specific input and lets the rest of the pipeline
(strong form, principal-ideal lift, unit decomposition) proceed without it.

## Main definitions

* `GenValuationDivisibleByPAt v P`: `(p : ℤ) ∣ count v (P.gen)` at the height-one
  prime `v` of `𝓞 K`.
* `GenValuationDivisibleByP P`: `∀ v : HeightOneSpectrum (𝓞 K),
  GenValuationDivisibleByPAt v P`.

## Main theorems

* `genIsPowOfFractionalIdealClass_iff_genValuationDivisibleByP`: the central
  equivalence
  `GenIsPowOfFractionalIdealClass ↔ GenValuationDivisibleByP`, established
  by computing `count v` of both sides of `(γ) = J^p`.
* `genIsPowOfFractionalIdealClass_of_genValuationDivisibleByP`: the
  `←` direction: from per-prime divisibility, construct an explicit `J`.
* `genValuationDivisibleByP_of_genIsPowOfFractionalIdealClass`: the `→`
  direction: from `(γ) = J^p`, conclude per-prime divisibility.

## References

* Washington, *Introduction to Cyclotomic Fields*, §10.2.
* Borevich-Shafarevich, *Number Theory*, §4.9.
* Diekmann, *FLT for regular primes*, §6.
* Mathlib, `FractionalIdeal.finprod_heightOneSpectrum_factorization'`.
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
### Atomic per-prime predicates
-/

/-- **Per-prime valuation criterion (atomic).** At a single height-one prime
`v` of `𝓞 K`, the principal fractional ideal `(γ)` has valuation divisible
by `p`.

This is the per-prime atom out of which the weak form of the unramifiedness
criterion is built. -/
def GenValuationDivisibleByPAt
    (v : HeightOneSpectrum (𝓞 K)) (P : KummerPresentation Ext) : Prop :=
  (p : ℤ) ∣ FractionalIdeal.count K v
    (toPrincipalIdeal (𝓞 K) K P.genUnit : FractionalIdeal (𝓞 K)⁰ K)

/-- **Global per-prime valuation criterion.** The principal fractional ideal
`(γ)` has valuation divisible by `p` at *every* height-one prime `v` of
`𝓞 K`.

This is the form delivered by accumulating the per-prime Kummer-Dedekind
ramification analysis. It is equivalent (in this file) to the weak form
`GenIsPowOfFractionalIdealClass`. -/
def GenValuationDivisibleByP (P : KummerPresentation Ext) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), GenValuationDivisibleByPAt v P

/-!
### Auxiliary facts

These are local building blocks. The `eq_of_count_eq` lemma is the standard
fact that fractional ideals over a Dedekind domain are determined by their
height-one prime valuations. (A duplicate is also stated in `Kummer/Singular.lean`,
but that file pulls in heavy dependencies; we restate it inline here.)
-/

/-- Nonzero fractional ideals over a Dedekind domain are determined by their
`count` at each height-one prime. -/
theorem _root_.FractionalIdeal.eq_of_count_eq_local
    {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F]
    {I J : FractionalIdeal R⁰ F} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R,
      FractionalIdeal.count F v I = FractionalIdeal.count F v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := F) hI,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := F) hJ]
  exact finprod_congr (fun v => by rw [h v])

/-- The principal fractional ideal `(γ)` is nonzero (as a `FractionalIdeal`),
since `γ ≠ 0`. -/
theorem coe_toPrincipalIdeal_genUnit_ne_zero (P : KummerPresentation Ext) :
    (toPrincipalIdeal (𝓞 K) K P.genUnit : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  rw [coe_toPrincipalIdeal]
  rw [P.genUnit_val]
  exact spanSingleton_ne_zero_iff.mpr P.gen_ne_zero

/-!
### Forward direction: `(γ) = J^p` implies per-prime divisibility
-/

/-- **Forward direction.** If `(γ) = J^p` in the fractional-ideal group
(weak form), then `count v (γ) = p · count v J` is divisible by `p` at
every height-one prime `v`.

The proof is a direct application of `FractionalIdeal.count_pow`. -/
theorem genValuationDivisibleByP_of_genIsPowOfFractionalIdealClass
    (P : KummerPresentation Ext)
    (h : P.GenIsPowOfFractionalIdealClass) :
    P.GenValuationDivisibleByP := by
  intro v
  obtain ⟨J, hJ⟩ := h
  -- hJ : toPrincipalIdeal _ _ P.genUnit = J ^ p (as units)
  -- Take the underlying FractionalIdeal value.
  have hJ' : (toPrincipalIdeal (𝓞 K) K P.genUnit : FractionalIdeal (𝓞 K)⁰ K) =
      ((J : FractionalIdeal (𝓞 K)⁰ K)) ^ p := by
    have h1 := congrArg
      (fun I : (FractionalIdeal (𝓞 K)⁰ K)ˣ => (I : FractionalIdeal (𝓞 K)⁰ K))
      hJ
    simpa [Units.val_pow_eq_pow_val] using h1
  -- `count v (γ) = count v (J^p) = p * count v J`.
  refine ⟨FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K), ?_⟩
  rw [hJ']
  rw [FractionalIdeal.count_pow]

/-!
### Reverse direction: per-prime divisibility implies `(γ) = J^p`

This is the substantive direction. Given `∀ v, p ∣ count v γ`, we construct
an explicit `J = ∏ᶠ v, v^(count v γ / p)` and check that `J^p = (γ)` by
comparing `count v` of both sides at every `v`.
-/

/-- The auxiliary fractional ideal `J = ∏ᶠ v, v^(count v γ / p)`. This is
the explicit witness for the weak form `(γ) = J^p` constructed from the
per-prime divisibility hypothesis. -/
noncomputable def auxFractionalIdealRoot (P : KummerPresentation Ext) :
    FractionalIdeal (𝓞 K)⁰ K :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
      (FractionalIdeal.count K v
        (toPrincipalIdeal (𝓞 K) K P.genUnit : FractionalIdeal (𝓞 K)⁰ K) / (p : ℤ))

/-- The exponent function `e_v := count v γ / p`. This is finitely supported,
because `count v γ` is. -/
theorem auxExponents_finite_support (P : KummerPresentation Ext) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      FractionalIdeal.count K v
        (toPrincipalIdeal (𝓞 K) K P.genUnit : FractionalIdeal (𝓞 K)⁰ K) / (p : ℤ) = 0 := by
  filter_upwards [FractionalIdeal.finite_factors
    (toPrincipalIdeal (𝓞 K) K P.genUnit : FractionalIdeal (𝓞 K)⁰ K)] with v hv
  rw [hv]
  exact Int.zero_ediv _

/-- The valuation of the auxiliary ideal `J` at `v` is `count v γ / p`. -/
theorem count_auxFractionalIdealRoot
    (v : HeightOneSpectrum (𝓞 K)) (P : KummerPresentation Ext) :
    FractionalIdeal.count K v (auxFractionalIdealRoot P) =
      FractionalIdeal.count K v
        (toPrincipalIdeal (𝓞 K) K P.genUnit : FractionalIdeal (𝓞 K)⁰ K) / (p : ℤ) := by
  unfold auxFractionalIdealRoot
  rw [FractionalIdeal.count_finprod K v
    (fun w => FractionalIdeal.count K w
      (toPrincipalIdeal (𝓞 K) K P.genUnit : FractionalIdeal (𝓞 K)⁰ K) / (p : ℤ))
    (auxExponents_finite_support P)]

/-- The auxiliary ideal `J` is nonzero. -/
theorem auxFractionalIdealRoot_ne_zero (P : KummerPresentation Ext) :
    auxFractionalIdealRoot P ≠ 0 := by
  unfold auxFractionalIdealRoot
  -- The finprod is over `v.asIdeal ^ (e_v)`, all nonzero.
  -- Use `finprod_mem_induction` with `I ≠ 0` as the property.
  apply finprod_induction (fun I : FractionalIdeal (𝓞 K)⁰ K => I ≠ 0)
  · exact one_ne_zero
  · intro I I' hI hI'; exact mul_ne_zero hI hI'
  · intro w
    exact zpow_ne_zero _ (coeIdeal_ne_zero.mpr w.ne_bot)

/-- **Reverse direction (substantive).** If `count v (γ) ∈ p · ℤ` at every
height-one prime `v`, then `(γ) = J^p` for some `J : (FractionalIdeal _)ˣ`.

The witness is the auxiliary ideal `J = ∏ᶠ v, v^(count v γ / p)`, whose
valuations are `count v γ / p`. By `count_pow`, `J^p` has valuations
`p · (count v γ / p) = count v γ` (using the divisibility hypothesis), so
`J^p = (γ)` by the height-one prime factorisation. -/
theorem genIsPowOfFractionalIdealClass_of_genValuationDivisibleByP
    (P : KummerPresentation Ext)
    (h : P.GenValuationDivisibleByP) :
    P.GenIsPowOfFractionalIdealClass := by
  -- Construct `J` as the auxiliary ideal.
  set J0 : FractionalIdeal (𝓞 K)⁰ K := auxFractionalIdealRoot P with hJ0
  have hJ0_ne_zero : J0 ≠ 0 := auxFractionalIdealRoot_ne_zero P
  -- `J0` is a unit (nonzero in a Dedekind domain).
  have hJ0_isUnit : IsUnit J0 := Ne.isUnit hJ0_ne_zero
  -- Prove `(γ) = J0^p` as fractional ideals.
  have hJ0_pow : (toPrincipalIdeal (𝓞 K) K P.genUnit :
      FractionalIdeal (𝓞 K)⁰ K) = J0 ^ p := by
    refine FractionalIdeal.eq_of_count_eq_local
      (coe_toPrincipalIdeal_genUnit_ne_zero P) (pow_ne_zero p hJ0_ne_zero) ?_
    intro v
    rw [FractionalIdeal.count_pow, count_auxFractionalIdealRoot v P]
    -- Goal: count v (γ) = p * (count v γ / p)
    obtain ⟨k, hk⟩ := h v
    rw [hk]
    rw [Int.mul_ediv_cancel_left k (Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]
  -- Promote `J0` to `J : (FractionalIdeal _)ˣ`.
  let J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := hJ0_isUnit.unit
  refine ⟨J, ?_⟩
  -- Goal: toPrincipalIdeal _ _ P.genUnit = J ^ p (as units).
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  change (toPrincipalIdeal (𝓞 K) K P.genUnit : FractionalIdeal (𝓞 K)⁰ K) =
       (J : FractionalIdeal (𝓞 K)⁰ K) ^ p
  rw [hJ0_pow]
  -- Goal: J0 ^ p = (J : FractionalIdeal _) ^ p.
  -- `(J : FractionalIdeal _) = J0` by definition of `IsUnit.unit`.
  change J0 ^ p = (hJ0_isUnit.unit : FractionalIdeal (𝓞 K)⁰ K) ^ p
  rw [IsUnit.unit_spec hJ0_isUnit]

/-!
### The central equivalence
-/

/-- **The central equivalence.** `(γ) = J^p` (in the fractional-ideal group) iff
`count v (γ) ∈ p · ℤ` for every height-one prime `v` of `𝓞 K`.

This is the "valuation criterion" form of the weak Kummer-Dedekind statement
underlying the unramifiedness ↔ `(γ) = J^p` correspondence. -/
theorem genIsPowOfFractionalIdealClass_iff_genValuationDivisibleByP
    (P : KummerPresentation Ext) :
    P.GenIsPowOfFractionalIdealClass ↔ P.GenValuationDivisibleByP :=
  ⟨genValuationDivisibleByP_of_genIsPowOfFractionalIdealClass P,
   genIsPowOfFractionalIdealClass_of_genValuationDivisibleByP P⟩

/-!
### The per-prime Kummer-Dedekind hypothesis

We now isolate the **mathematically substantive** Kummer-Dedekind step
as a single per-prime obligation: at each height-one prime `v ⊂ 𝓞_K`,
the unramifiedness of `v` in `𝓞_E` implies `(p : ℤ) ∣ count v (γ)`.

This is the hypothesis whose proof requires the Washington §10.2
ramification analysis of `X^p - γ` (or its more delicate counterpart at
primes above `p`). The hypothesis is stated as a Prop over
`HeightOneSpectrum (𝓞 K)`, so that:

* the `v ∤ p` case (Washington §10.2, simple discriminant computation) and
* the `v ∣ p` case (cyclotomic uniformizer analysis)

can be discharged in *separate* downstream files without entangling the
high-level pipeline.
-/

/-- **The per-prime Kummer-Dedekind hypothesis.** At each height-one prime
`v ⊂ 𝓞_K`, the unramifiedness of `v` in the Kummer extension `E = K(γ^{1/p})`
implies that `count v (γ)` is divisible by `p`.

This is the precise form of the per-prime Kummer-Dedekind ramification criterion
needed to bridge from `IsUnramified (𝓞 K) (𝓞 E)` to
`GenIsPowOfFractionalIdealClass`. It is stated as a hypothesis here (deferred
to a downstream file) because its proof requires the discriminant analysis of
`X^p - γ`, which is not yet available in mathlib in the form needed.

In words: *if `v` is unramified in `𝓞_E`, then `v_v(γ) ≡ 0 (mod p)`.*

The antecedent is the unfolded meaning of the (now-removed) flt-regular
`IsUnramifiedAt (𝓞 E) v.asIdeal`: every prime `Q` of `𝓞 E` lying over the
height-one prime `v.asIdeal ⊂ 𝓞 K` has ramification index `1`. -/
def KummerDedekindUnramifiedAt
    (P : KummerPresentation Ext) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  (∀ Q ∈ v.asIdeal.primesOver (𝓞 Ext.E),
      Ideal.ramificationIdx v.asIdeal Q = 1) →
    GenValuationDivisibleByPAt v P

/-- **Global accumulated form of the Kummer-Dedekind hypothesis.** The per-prime
hypothesis holds at every height-one prime `v ⊂ 𝓞_K`. -/
def KummerDedekindUnramified (P : KummerPresentation Ext) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), KummerDedekindUnramifiedAt P v

/-!
### Exposed reduction: from per-prime Kummer-Dedekind input to the unit
decomposition.

The per-prime Kummer-Dedekind input is the mathematically substantive bridge
from `IsUnramified (𝓞 K) (𝓞 E)` to per-prime valuation divisibility.
It packages the Washington §10.2 ramification analysis of `X^p - γ` at each
prime `v ⊂ 𝓞_K`:

* For `v ∤ p`: ramification index of `v` in `E/K` is `1` iff `v_v(γ) ≡ 0 mod p`.
* For `v ∣ p`: a more delicate analysis using `1 - ζ_p` is required, but the
  output is the same.

Once this input is supplied, the rest of the pipeline — composite reduction
via the principal-ideal lift, then unit decomposition — runs unchanged.
-/

/-- **Composite Kummer-Dedekind reduction.** From the per-prime Kummer-Dedekind
unramifiedness criterion at every prime `v` of `𝓞 K`, we derive the weak form
`(γ) = J^p` of the unit-decomposition statement.

The hypothesis `unramifiedCriterion` packages the per-prime input

> for every `v ⊂ 𝓞_K`, `IsUnramifiedAt (𝓞 E) v.asIdeal` ⟹ `(p : ℤ) ∣ count v (γ)`,

evaluated at the unramifiedness data of `Ext`. This is the **only**
Kummer-Dedekind-specific obligation; the rest of the pipeline runs without
any further ramification input. -/
theorem genIsPowOfFractionalIdealClass_of_perPrime_kummerDedekind
    (P : KummerPresentation Ext)
    (unramifiedCriterion :
      ∀ v : HeightOneSpectrum (𝓞 K), GenValuationDivisibleByPAt v P) :
    P.GenIsPowOfFractionalIdealClass :=
  genIsPowOfFractionalIdealClass_of_genValuationDivisibleByP P unramifiedCriterion

/-- **The full bridge from `IsUnramified` to the weak form.** Given the
per-prime Kummer-Dedekind hypothesis at every prime, the global
unramifiedness `IsUnramified (𝓞 K) (𝓞 E)` (provided by `Ext.isUnramified`)
implies the weak form `GenIsPowOfFractionalIdealClass`.

The hypothesis `kdHyp : KummerDedekindUnramified P` packages the substantive
Kummer-Dedekind ramification analysis (per prime). Once it is supplied, the
abstract `IsUnramified` instance from the extension `Ext` discharges the
per-prime input. -/
theorem genIsPowOfFractionalIdealClass_of_isUnramified
    (P : KummerPresentation Ext)
    (kdHyp : P.KummerDedekindUnramified) :
    P.GenIsPowOfFractionalIdealClass := by
  apply genIsPowOfFractionalIdealClass_of_perPrime_kummerDedekind P
  intro v
  refine kdHyp v ?_
  -- Need: every prime `Q` of `𝓞 Ext.E` over `v.asIdeal` has `ramificationIdx = 1`.
  -- Use the global `Algebra.Unramified (𝓞 K) (𝓞 Ext.E)` provided by `Ext`.
  rintro Q ⟨hQ_prime, hQ_over⟩
  haveI : Q.IsPrime := hQ_prime
  haveI : Q.LiesOver v.asIdeal := hQ_over
  have hQ_bot : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  haveI : Algebra.IsUnramifiedAt (𝓞 K) Q :=
    Algebra.unramified_iff_forall.mp Ext.isUnramified ⟨Q, hQ_prime⟩
  have h := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 K) (S := 𝓞 Ext.E) hQ_bot
  rwa [show Q.under (𝓞 K) = v.asIdeal from (Ideal.LiesOver.over (p := v.asIdeal)).symm] at h

end KummerPresentation

end BernoulliRegular

end
