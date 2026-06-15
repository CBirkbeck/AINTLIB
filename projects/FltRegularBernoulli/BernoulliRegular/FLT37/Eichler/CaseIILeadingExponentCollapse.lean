import BernoulliRegular.FLT37.Eichler.CaseIIEx811

/-!
# Washington Exercise 8.11 for `p = 37`: the *valuation half* of the leading-`λ`-exponent collapse,
and reduction of `LeadingExponentEigenCollapse37` to the single Galois-equivariant bridge

This file makes the leading-`λ`-exponent collapse `LeadingExponentEigenCollapse37`
(`CaseIILeadingExponent.lean`) — the **regular-index half of Washington Lemma 9.9** in
eigencomponent form — depend on **exactly one** undischarged input, by **proving** the *valuation
half*
that the previous attempt (`CaseIIEx811.lean`) had to carry as a named `Prop`
(`CompletedLogVanishingThroughLevel36_37`) because of an `isDefEq`/`whnf` tooling wall over
mathlib's `adicCompletionIntegers`.

It imports only; it does **not** modify any existing file.

## What this file proves (real, axiom-clean Lean)

* `completedLogVanishingThroughLevel36_37_proven` — the **valuation half**, now **proven**: for
  every real unit `u` whose degree-`36` completed-log argument has `λ`-valuation `≥ 36`
  (`CompletedLogArgHighValuation37 u`, the proven output of
  `caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred`), the completed (same-prime)
  logarithm `completedLog(u^{36})` vanishes through `λ`-level `36`.  This is Washington Exercises
  8.10/8.11's analytic input ("`≡` rational mod `37`" forces the leading non-constant `λ`-exponent
  `≥ (p-1)/2`); its mathematics is the §0 finite-log vanishing lemmas of `CaseIIEx811.lean`.

* `leadingExponentEigenCollapse37_of_bridge'` — `LeadingExponentEigenCollapse37` from the **single**
  remaining input `LeadingExponentBridge37`, with the valuation half now supplied by the proven
  `completedLogVanishingThroughLevel36_37_proven`.  (The previous
  `leadingExponentEigenCollapse37_of_bridge` needed *two* inputs; this halves it.)

## The `adicCompletionIntegers` `isDefEq`/`whnf` wall, and the workaround

`CompletedLogArgHighValuation37 u` is, by definition, the membership
`completedLogArg(EPlus_completedLogDomainPowPred u) ∈ lambdaIdeal^{36}`.  The degree-`(M+1)`
coordinate of the completed logarithm is `samePrimeFiniteLog M (completedLogArg …)` by the proven
`@[simp]` lemma `completedLog_evalₐ_succ`, so the §0 vanishing lemma
`caseIIEx811_samePrimeFiniteLog_eq_zero_of_le_of_mem_pow36` applies — provided its
`λ^{36}`-membership hypothesis can be fed `u`'s.

The obstruction is that *any* `isDefEq` between two copies of `· ∈ lambdaIdeal^{36}` over the
valuation-completion integer ring
`ValuedIntegerRing = (lambdaHeightOneSpectrum).adicCompletionIntegers` diverges: comparing
`Ideal.pow` over this ring forces a `whnf` of the `CommMonoid (Ideal R)` instance, which forces a
`whnf` of the `adicCompletionIntegers` `CommRing` instance (built by `Subtype`/`Valued` completion
transport), which does not terminate at any feasible heartbeat budget.  This is why the valuation
half was previously carried as a `Prop`.

The workaround uses three moves, each verified to dodge the wall:
* `revert hu; unfold CompletedLogArgHighValuation37` exposes `hu`'s membership content by a
  *syntactic* rewrite of the goal (never an `isDefEq` against the heavy `def`);
* `generalize EPlus_completedLogDomainPowPred … = W` makes the completed-log-domain element opaque;
* `convert hu using 2` discharges the residual `· ∈ lambdaIdeal^{36}` subgoal by *structural*
  congruence to depth `2` (closing the leaves by `rfl`) instead of the diverging `exact`/`isDefEq`.

## The single remaining input, precisely (and why it is *not* a perf issue)

After this file the only undischarged content of `LeadingExponentEigenCollapse37` is
`LeadingExponentBridge37` (`CaseIIEx811.lean`): the Galois-equivariant leading-`λ`-coefficient
bridge of Exercise 8.11 — `completedLog(u^{36})` *vanishing through level `36`* forces the
**regular**
eigencomponents of `realUnitToFreePartModP u` to vanish.  This is a genuine **unbuilt mathematical
comparison**, not a tooling wall: the local logarithm `completedLog` (a `λ`-adic object in
`adicCompletionIntegers` that does *not* factor through the mod-`37` free part — it carries `p`-adic
denominators) and the global mod-`37` free-part class `realUnitToFreePartModP u` (where the
eigencomponents `caseIIResidueProvenance_decomp` live) are connected only through the multi-file
Galois-equivariant comparison between `completedLog`'s `λ`-graded pieces and the global eigenbasis
(the local `Δ`-eigenvalue `ω^n` on `completedPrincipalUnitGradedQuotient … n` is the proven
`completedPrincipalUnitGradedDeltaActionZMod_apply_eq_smul` of
`Reflection/Local/GradedAction.lean`).  The companion `concreteKummerLogMatrix = diag(B)·V`
machinery (`Washington816`) does **not** suffice on its own: it gives the *Dwork-basis* matrix
kernel, which (via the Vandermonde change of basis to the eigenbasis) only forces the regular
eigencomponents to be *equal*, not zero.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Lemma 9.9 (pp. 180–181),
  Exercises 8.10/8.11 (p. 166), Corollary 8.15 (p. 157).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

set_option maxHeartbeats 1000000 in
-- The `convert … using 2` structural-congruence step and the §0 finite-log application over the
-- heavy valuation-completion integer ring `adicCompletionIntegers` exceed the default budget.
/-- **The valuation half, proven** (axiom-clean): for every real unit `u` whose degree-`36`
completed-log argument has `λ`-valuation `≥ 36` (`CompletedLogArgHighValuation37 u`), the completed
(same-prime) logarithm `completedLog(u^{36})` vanishes through `λ`-level `36`: every graded
coordinate `AdicCompletion.evalₐ (λ) N (completedLog (EPlus_completedLogDomainPowPred u))` with
`N ≤ 36` is `0`.

This discharges the named `Prop` `CompletedLogVanishingThroughLevel36_37` of `CaseIIEx811.lean`: its
mathematics is the §0 finite-log vanishing lemmas of that file
(`caseIIEx811_samePrimeFiniteLog_eq_zero_of_le_of_mem_pow36`), and the only obstruction had been the
`adicCompletionIntegers` `isDefEq`/`whnf` wall (see the module docstring), now dodged via
`revert/unfold`, `generalize`, and `convert … using 2`. -/
theorem completedLogVanishingThroughLevel36_37_proven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    CompletedLogVanishingThroughLevel36_37 := by
  intro u hu N hN
  -- Expose `hu`'s membership content by a *syntactic* unfold of the goal (no heavy `isDefEq`).
  revert hu
  unfold CompletedLogArgHighValuation37
  rcases N with _ | M
  · -- Level `0`: the `0`-th completed-log coordinate is `0` definitionally.
    intro _hu
    rw [completedLog_evalₐ]
    rfl
  · -- Level `M+1 ≤ 36`: the coordinate is `samePrimeFiniteLog M (completedLogArg W)`.
    rw [completedLog_evalₐ_succ]
    -- Make the completed-log-domain element opaque before the structural defeq.
    generalize EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u = W
    intro hu
    refine caseIIEx811_samePrimeFiniteLog_eq_zero_of_le_of_mem_pow36
      (M := M) (y := completedLogArg (p := 37) (K := CyclotomicField 37 ℚ) W) (by omega) ?_
      (completedLogArg_mem (p := 37) (K := CyclotomicField 37 ℚ) W)
    -- The residual `· ∈ lambdaIdeal^{36}` subgoal: discharge by *structural* congruence, dodging
    -- the diverging `adicCompletionIntegers` `Ideal.pow` `isDefEq`.
    convert hu using 2

/-- **`LeadingExponentEigenCollapse37` from the single Galois-equivariant bridge** (proven,
axiom-clean given `LeadingExponentBridge37`).

The valuation half is now **proven** (`completedLogVanishingThroughLevel36_37_proven`), so it no
longer needs to be supplied; the **only** remaining input is the Exercise-8.11
leading-`λ`-coefficient bridge `LeadingExponentBridge37` (a genuine unbuilt Galois-equivariant
comparison — see the module docstring; *not* a tooling wall).  This strengthens the previous
two-input `leadingExponentEigenCollapse37_of_bridge` to a single-input reduction. -/
theorem leadingExponentEigenCollapse37_of_bridge'
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hBridge : LeadingExponentBridge37) :
    LeadingExponentEigenCollapse37 :=
  leadingExponentEigenCollapse37_of_bridge completedLogVanishingThroughLevel36_37_proven hBridge

end BernoulliRegular.FLT37.Eichler

end
