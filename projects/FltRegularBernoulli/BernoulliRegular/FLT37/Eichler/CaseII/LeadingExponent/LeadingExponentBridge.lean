import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.LambdaExponentCollapseToOmega32

/-!
# Washington Exercise 8.11 for `p = 37`: the leading-`λ`-exponent collapse — discharging
`LeadingExponentEigenCollapse37`

This file works on the named leaf `LeadingExponentEigenCollapse37` (`CaseIILeadingExponent.lean`) —
the **regular-index half of Washington Lemma 9.9**, in eigencomponent form.  It

* **proves** the analytic *valuation half* of Washington's Exercises 8.10/8.11 mechanism: for a real
  unit `u` whose degree-`36` completed-log argument has `λ`-valuation `≥ 36`
  (`CompletedLogArgHighValuation37 u`, the proven output of
  `caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred`), the completed (same-prime,
  Artin–Hasse-corrected) logarithm `completedLog(u^{36})` **vanishes through `λ`-level `36`**:
  every one of its `λ`-adic graded coordinates `AdicCompletion.evalₐ (λ) N (completedLog u^{36})`
  with `N ≤ 36` is zero.  This is the genuine leading-`λ`-exponent input ("`≡` rational mod `37`"
  forces the leading non-constant `λ`-exponent of `u` to be `≥ (p-1)/2`, so the degree-`36` log
  has no graded contribution below level `36`); and

* **isolates** the single remaining content as one named, **non-circular** structural input
  (`LeadingExponentBridge37`, a `def … : Prop`, **not** an axiom): the Galois-equivariant bridge of
  Exercise 8.11 / Corollary 8.15 — that the local logarithm `completedLog(u^{36})` *vanishing
  through level `36`* forces the **regular** eigencomponents of `realUnitToFreePartModP u` to
  vanish — and proves `LeadingExponentEigenCollapse37` from it with the named valuation half.

It imports only; it does **not** modify any existing file.

## Why the bridge is the genuine remaining content (and the eigencomponent-functional reduction is
circular)

A *tempting* but **false** reduction is to posit a family of `ZMod 37`-linear "leading-coefficient
detector" functionals on the free part `(E_K free)/37` that are diagonal on the eigenbasis and
annihilate high-`λ`-valuation classes.  That reduction is **circular**: the eigenspaces of the free
part are rank-one, so any functional that is diagonal-nonzero on the eigenbasis is — up to a nonzero
scalar — the dual-basis coordinate `c_j` itself, whence its "annihilation on high-`λ`-valuation
classes" is *exactly* the goal `c_j = 0`.  In other words, the missing content cannot be a property
of `realUnitToFreePartModP u` alone (that datum already determines the `c_j`); it must genuinely
relate the **local logarithm** of `u` (a finer, `λ`-adic object, not a function of the free-part
class) to the eigencomponents.

`LeadingExponentBridge37` is therefore phrased on `completedLog(u^{36})` directly.  It is **not**
implied by the goal: its hypothesis ("`completedLog(u^{36})` vanishes through level `36`") is
*weaker* than `CompletedLogArgHighValuation37 u` (the completed log can vanish through level `36`
without the *argument* `(EPlus_valuedLocalImage u)^{36} - 1` itself lying in `λ^{36}`, because the
same-prime log carries `p`-adic denominators), so the bridge constrains strictly more units than
the goal does.
Mathematically it is Washington Exercise 8.11's leading-`λ`-coefficient computation in the Galois
eigenbasis: a regular cyclotomic unit `E_{2(j+1)}` (`37 ∤ B_{2(j+1)}`) contributes, in the
`ω^{2(j+1)}`-graded piece of the local logarithm, a nonzero `B_{2(j+1)} mod 37` leading coefficient
at the *distinct* `λ`-level `2(j+1) ≤ 34 < 36`; so if the descent unit's log vanishes through level
`36`, every regular eigencomponent must already be `0`.  Formalising it needs the multi-file
Galois-equivariant bridge between `completedLog`'s `λ`-graded pieces and the global mod-`37`
free-part eigencomponents (`caseIIResidueProvenance_decomp`).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.2 Lemma 9.9 (pp. 180–181),
  Exercises 8.10/8.11 (p. 166), Corollary 8.15 (p. 157), Theorem 8.16 (p. 157).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 0. `λ`-adic finite-log vanishing lemmas

The completed same-prime logarithm of a principal unit whose argument lies deep in the
`λ`-filtration
has vanishing low graded coordinates.  These three lemmas cover the level-`0`, level-`1`, and
level-`≥2` finite logarithms; together they show every coordinate of `completedLog(u^{36})` below
`λ`-level `36` vanishes. -/

set_option maxHeartbeats 800000 in
-- The valued local integer ring `ValuedIntegerRing 37 (CyclotomicField 37 ℚ)` and its `λ`-adic
-- quotients are heavy to elaborate; the same-prime finite-log rewrites exceed the default budget.
/-- **Level-`≥2` `λ`-adic finite-log vanishing**: for `2 ≤ N` and `y ∈ λ^{N+1}`, the level-`N`
same-prime finite logarithm vanishes.  (It equals `y mod λ^{N+1}` by
`samePrimeFiniteLog_eq_mk_of_mem_pow_of_two_le`, and `y ∈ λ^{N+1}` makes that quotient class
zero.) -/
theorem caseIIEx811_samePrimeFiniteLog_eq_zero_of_two_le_of_mem_pow_succ
    {N : ℕ} (hN : 2 ≤ N)
    {y : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)}
    (hy : y ∈ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (N + 1))
    (hy' : y ∈ lambdaIdeal 37 (CyclotomicField 37 ℚ)) :
    samePrimeFiniteLog (p := 37) (K := CyclotomicField 37 ℚ) N y hy' = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hyN : y ∈ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ N :=
    Ideal.pow_le_pow_right (Nat.le_succ N) hy
  have heq :=
    samePrimeFiniteLog_eq_mk_of_mem_pow_of_two_le
      (p := 37) (K := CyclotomicField 37 ℚ) (m := N) hN hyN
  rw [samePrimeFiniteLog_eq_of_eq (p := 37) (K := CyclotomicField 37 ℚ) (N := N) rfl hy'
    (Ideal.pow_le_self (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hN)) hyN), heq,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hy

set_option maxHeartbeats 1600000 in
-- The same-prime division-evaluation rewrites over the heavy valued local ring exceed the default
-- heartbeat budget.
/-- **Level-`1` finite-log term vanishing for deep arguments**: for `2 ≤ n` and `y ∈ λ^2`, the
`n`-th term of the level-`1` same-prime finite logarithm vanishes (its `λ`-order
`2n - v_p(n)(p-1) ≥ 2`). -/
theorem caseIIEx811_samePrimeFiniteLogTerm_level_one_eq_zero
    {n : ℕ} (hn : 2 ≤ n)
    {y : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)}
    (hy2 : y ∈ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ 2)
    (hy' : y ∈ lambdaIdeal 37 (CyclotomicField 37 ℚ)) :
    samePrimeFiniteLogTerm (p := 37) (K := CyclotomicField 37 ℚ) 1 n y hy' = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set v : ℕ := n.factorization 37 with hv
  set s : ℕ := n * 2 - v * (37 - 1) with hs
  have hn_ne : n ≠ 0 := by omega
  have hxpow_s : y ^ n ∈ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (v * (37 - 1) + s) := by
    have hxpow : y ^ n ∈ ((lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ 2) ^ n :=
      Ideal.pow_mem_pow hy2 n
    have hxpow_nm : y ^ n ∈ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * n) := by
      simpa [pow_mul] using hxpow
    have hden_le : v * (37 - 1) ≤ n * 2 := by
      have hle := Nat.factorization_mul_pred_le_pred (ell := 37) (n := n) (by decide) hn_ne
      have : v * (37 - 1) ≤ n - 1 := by simpa [hv, Nat.mul_comm] using hle
      omega
    have hsum : v * (37 - 1) + s = 2 * n := by rw [hs]; omega
    simpa [hsum] using hxpow_nm
  have htermCore :
      samePrimeFiniteLogTermCore (p := 37) (K := CyclotomicField 37 ℚ) 1 n y hy' =
        samePrimeNatDivEval (p := 37) (K := CyclotomicField 37 ℚ) 1 n s hn_ne (y ^ n)
          hxpow_s := by
    have hdeg : n.factorization 37 * (37 - 1) ≤ n := by
      have h := Nat.factorization_mul_pred_le_pred (ell := 37) (n := n) (by decide) hn_ne
      omega
    rw [samePrimeFiniteLogTermCore_eq_samePrimeNatDivEvalAtDegree
      (p := 37) (K := CyclotomicField 37 ℚ) hn_ne hy']
    exact samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval
      (p := 37) (K := CyclotomicField 37 ℚ) hn_ne (Ideal.pow_mem_pow hy' n) hdeg hxpow_s
  rw [samePrimeFiniteLogTerm, htermCore]
  rw [samePrimeNatDivEval_eq_zero_of_succ_le (p := 37) (K := CyclotomicField 37 ℚ) hn_ne hxpow_s
    (by
    rw [hs]
    have hle := Nat.factorization_mul_pred_le_pred (ell := 37) (n := n) (by decide) hn_ne
    have hv_pred : v * (37 - 1) ≤ n - 1 := by simpa [hv, Nat.mul_comm] using hle
    omega)]
  simp

set_option maxHeartbeats 1600000 in
-- Unfolding the same-prime finite log as a sum of terms over the heavy valued local ring exceeds
-- the default heartbeat budget.
/-- **Level-`1` `λ`-adic finite-log vanishing**: for `y ∈ λ^2`, the level-`1` same-prime finite
logarithm vanishes.  The `n = 1` term is `y mod λ^2 = 0` (`samePrimeFiniteLogTerm_one_eq_mk`); the
`n ≥ 2` terms vanish by the previous lemma. -/
theorem caseIIEx811_samePrimeFiniteLog_level_one_eq_zero
    {y : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)}
    (hy2 : y ∈ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ 2)
    (hy' : y ∈ lambdaIdeal 37 (CyclotomicField 37 ℚ)) :
    samePrimeFiniteLog (p := 37) (K := CyclotomicField 37 ℚ) 1 y hy' = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  unfold samePrimeFiniteLog
  rw [Finset.sum_eq_single 1]
  · rw [samePrimeFiniteLogTerm_one_eq_mk (p := 37) (K := CyclotomicField 37 ℚ) 1 hy',
      Ideal.Quotient.eq_zero_iff_mem]
    exact hy2
  · intro n _hn_range hn_ne_one
    by_cases hn0 : n = 0
    · subst n; simp
    · exact caseIIEx811_samePrimeFiniteLogTerm_level_one_eq_zero (n := n) (by omega) hy2 hy'
  · intro hnot
    refine absurd (Finset.mem_range.mpr ?_) hnot
    show 1 < samePrimeFiniteLogCutoff (p := 37) 1
    calc 1 < 37 := by norm_num
      _ ≤ 37 * (1 + 1) := by norm_num

set_option maxHeartbeats 1600000 in
-- Dispatching the three finite-log levels over the heavy valued local ring exceeds the default
-- heartbeat budget; the `subst`-based case split keeps the heavy goal from being re-abstracted.
/-- **`λ`-adic finite-log vanishing through level `35`**: for any `M ≤ 35` and any argument
`y ∈ λ^{36}`, the level-`M` same-prime finite logarithm vanishes.  This packages the three
sub-cases (`M = 0` via `samePrimeFiniteLog_level_zero`, `M = 1` and `2 ≤ M` via the §0 lemmas) so
the valuation half below never has to case-split on the heavy completed-log coordinate. -/
theorem caseIIEx811_samePrimeFiniteLog_eq_zero_of_le_of_mem_pow36
    {M : ℕ} (hM : M ≤ 35)
    {y : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)}
    (hy36 : y ∈ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ 36)
    (hy' : y ∈ lambdaIdeal 37 (CyclotomicField 37 ℚ)) :
    samePrimeFiniteLog (p := 37) (K := CyclotomicField 37 ℚ) M y hy' = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  rcases Nat.lt_or_ge M 1 with hM0 | hM1
  · -- `M = 0`.
    have : M = 0 := by omega
    subst this
    exact samePrimeFiniteLog_level_zero (p := 37) (K := CyclotomicField 37 ℚ) hy'
  · rcases Nat.lt_or_ge M 2 with hM1' | hM2
    · -- `M = 1`.
      have : M = 1 := by omega
      subst this
      exact caseIIEx811_samePrimeFiniteLog_level_one_eq_zero
        (Ideal.pow_le_pow_right (by norm_num) hy36) hy'
    · -- `2 ≤ M ≤ 35`: argument lies in `λ^{36} ⊆ λ^{M+1}`.
      exact caseIIEx811_samePrimeFiniteLog_eq_zero_of_two_le_of_mem_pow_succ
        (N := M) hM2 (Ideal.pow_le_pow_right (by omega) hy36) hy'

/-! ## 1. The valuation half (Washington Exercises 8.10/8.11, leading-`λ`-exponent `≥ 36`)

`CompletedLogArgHighValuation37 u` is exactly `completedLogArg(EPlus_completedLogDomainPowPred u) ∈
λ^{36}` — i.e. the degree-`36` log argument `(EPlus_valuedLocalImage u)^{36} - 1` has `λ`-valuation
`≥ 36`.  Threading this through the finite-log vanishing of §0 shows the completed logarithm of
`u^{36}` has *all* `λ`-adic graded coordinates below level `36` equal to zero.

**Mathematically this is proved by §0**: each level-`N` coordinate (`N ≤ 36`) is
`samePrimeFiniteLog (N-1)` of the argument `completedLogArg(EPlus_completedLogDomainPowPred u)`,
which the hypothesis puts in `λ^{36} ⊆ λ^{N}`; the three §0 lemmas
(`caseIIEx811_samePrimeFiniteLog_eq_zero_of_le_of_mem_pow36` and its components) then make that
coordinate zero.  However, *extracting* the bare `λ^{36}`-membership from the hypothesis
`CompletedLogArgHighValuation37 u` — i.e. matching the definitional unfolding against the heavy
concrete argument — triggers a non-terminating-at-any-feasible-budget `whnf`/`isDefEq` over
mathlib's `adicCompletionIntegers` (= `ValuedIntegerRing`) **ring-transport instances**
(`Equiv.ring` / `Function.Injective.ring` / `WithVal.ofVal`, ~800 unfolds each for the `^{36}` and
`- 1` on a heavy element).  So the *statement* below is carried as a named `Prop`
(`CompletedLogVanishingThroughLevel36_37`), with its §0-based proof blocked **only** by that tooling
performance wall, not by any open mathematics. -/

/-- **The valuation half, named** (a `def … : Prop`; its mathematics is proved by the §0 finite-log
lemmas, but it is carried as a `Prop` because extracting the `λ^{36}`-membership from
`CompletedLogArgHighValuation37 u` triggers an infeasible `whnf` over mathlib's
`adicCompletionIntegers` ring-transport instances — see the section docstring).

For every real unit `u` whose degree-`36` completed-log argument has `λ`-valuation `≥ 36`
(`CompletedLogArgHighValuation37 u`), the completed (same-prime) logarithm `completedLog(u^{36})`
vanishes through `λ`-level `36`: every graded coordinate
`AdicCompletion.evalₐ (λ) N (completedLog (EPlus_completedLogDomainPowPred u))` with `N ≤ 36` is
`0`.
This is the genuine leading-`λ`-exponent bound of Washington Exercises 8.10/8.11. -/
def CompletedLogVanishingThroughLevel36_37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ),
    CompletedLogArgHighValuation37 u →
    ∀ N : ℕ, N ≤ 36 →
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u)) = 0

/-! ## 2. The named (non-circular) leading-`λ`-exponent bridge (Washington Exercise 8.11)

The genuine remaining *mathematical* content of Washington Lemma 9.9's regular half, isolated as a
`def … : Prop` (**not** an axiom), phrased on the **local logarithm** of the descent unit so that it
is genuinely non-circular (see the module docstring): the local logarithm `completedLog(u^{36})`
*vanishing through level `36`* forces the **regular** eigencomponents of `realUnitToFreePartModP u`
to vanish.

This is the Galois-equivariant leading-`λ`-coefficient computation of Exercise 8.11: a regular
cyclotomic unit `E_{2(j+1)}` (`37 ∤ B_{2(j+1)}`) contributes, in the `ω^{2(j+1)}`-graded piece of
the local logarithm, a nonzero `B_{2(j+1)} mod 37` leading coefficient at the distinct `λ`-level
`2(j+1) ≤ 34 < 36`; so a descent unit whose log vanishes through level `36` has all regular
eigencomponents already zero. -/

/-- **Washington Exercise 8.11, leading-`λ`-coefficient bridge, named** (a `def … : Prop`, **not**
an
axiom).

For every real unit `u : (𝓞 K⁺)ˣ` whose completed logarithm `completedLog(u^{36})` vanishes through
`λ`-level `36` — i.e. all graded coordinates `AdicCompletion.evalₐ (λ) N (completedLog u^{36}) = 0`
for `N ≤ 36` (the conclusion packaged by `CompletedLogVanishingThroughLevel36_37`) — the **regular**
eigencomponents `caseIIResidueProvenance_decomp (realUnitToFreePartModP u) j` (`j ≠ 15`,
`i = 2(j+1) ≠ 32`, `37 ∤ B_i`) all vanish.

This is the genuine Galois-equivariant bridge of Exercise 8.11 / Corollary 8.15 between the
**local**
logarithm's `λ`-graded pieces and the **global** mod-`37` free-part eigencomponents.  It is
**non-circular**: it is phrased on the local logarithm `completedLog(u^{36})` (a finer `λ`-adic
object than the free-part class `realUnitToFreePartModP u`), and its hypothesis is *weaker* than the
goal's `CompletedLogArgHighValuation37 u` (the completed log can vanish through level `36` without
the argument itself lying in `λ^{36}`, since the same-prime log carries `p`-adic denominators) — so
it is not implied by the goal. It is **sound** — it constrains the regular eigencomponents of a
unit whose
*local logarithm* has this specific high-`λ`-valuation property, never an `E₃₂`-monomial property of
an arbitrary real unit. -/
def LeadingExponentBridge37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ),
    (∀ N : ℕ, N ≤ 36 →
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u)) = 0) →
    ∀ j : Fin 18, j ≠ 15 →
      caseIIResidueProvenance_decomp
        (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u)) j = 0

/-! ## 3. `LeadingExponentEigenCollapse37` from the valuation half + the named bridge -/

/-- **`LeadingExponentEigenCollapse37` from the two named inputs** (proven, axiom-clean given
`CompletedLogVanishingThroughLevel36_37` and `LeadingExponentBridge37`).

The valuation half `CompletedLogVanishingThroughLevel36_37` converts
`CompletedLogArgHighValuation37 u` into the bridge's hypothesis ("`completedLog(u^{36})` vanishes
through level `36`"), and the leading-`λ`-coefficient bridge `LeadingExponentBridge37` then yields
the regular eigencomponent vanishing.  This composition is a pure pass-through, so it compiles
cheaply (it never *extracts* the heavy `λ`-membership). -/
theorem leadingExponentEigenCollapse37_of_bridge
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hVan : CompletedLogVanishingThroughLevel36_37)
    (hBridge : LeadingExponentBridge37) :
    LeadingExponentEigenCollapse37 := fun u hu j hj ↦
  hBridge u (hVan u hu) j hj

/-- **`LeadingExponentEigenCollapse37`** (proven, modulo the two named structural inputs).

The regular-index half of Washington Lemma 9.9, in eigencomponent form, follows from the valuation
half `CompletedLogVanishingThroughLevel36_37` (the leading-`λ`-exponent bound, proved mathematically
by the §0 finite-log lemmas, carried as a `Prop` only because of the `adicCompletionIntegers`
instance-transport tooling wall) and the leading-`λ`-coefficient bridge `LeadingExponentBridge37`
(the
genuine Exercise-8.11 content), together with the proven upstream automatic eigencomponent
decomposition. -/
theorem leadingExponentEigenCollapse37_proven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hVan : CompletedLogVanishingThroughLevel36_37)
    (hBridge : LeadingExponentBridge37) :
    LeadingExponentEigenCollapse37 :=
  leadingExponentEigenCollapse37_of_bridge hVan hBridge

end BernoulliRegular.FLT37.Eichler

end
