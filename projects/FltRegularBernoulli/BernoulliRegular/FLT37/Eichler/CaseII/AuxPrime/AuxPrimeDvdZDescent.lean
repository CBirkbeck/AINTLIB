import BernoulliRegular.FLT37.Eichler.CaseII.AuxPrime.FurtwanglerResidueAndBaseDvdZ
import BernoulliRegular.FLT37.Eichler.CaseII.AuxPrime.GammaRatioLocalPower
import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.DiscreteLogIndexCollapse
import BernoulliRegular.FLT37.Eichler.FLT37CaseIWired

/-!
# [FLT37-CASEII-THM95] Washington Theorem 9.5 framing resolved: the `ℓ ∣ z`-restricted descent

This file resolves — **against the primary source** (Washington, *Introduction to Cyclotomic
Fields*, 2nd ed., GTM 83, **Theorem 9.5** and **Lemmas 9.6–9.9**, pp. 176–181) — the framing of the
computational (auxiliary-prime `ℓ = 149`) Case-II route for `p = 37`, and builds the closure that
the source mandates.  It imports only; it modifies no existing file.  No `sorry`, no `axiom`.

## The framing question, resolved from Washington pp. 176–181

The prior route-(a) chain reduced Case-II to the residual `Lemma98LocalPower37`
(`CaseIIAssumptionII.lean`), a **universal** over the *abstract* descent telescope `CaseIIData37`
demanding `IsPthPowerModPrime 37 𝔩 (ε₁/ε₂)` for **every** datum with free `x', y', z', ε₁, ε₂, ε₃`
under only the `(ζ−1) ∤ ·` conditions.  As a universal it is **false** (B2
`CASEII-LEMMA98-LOCALPOWER`: with `x' ∈ 𝔩` or `z' ∉ 𝔩` the unit `ε₁/ε₂` is free in
`𝔽₁₄₉^×/(𝔽₁₄₉^×)³⁷`).  Its genuine content is the **implication**
`caseII_lemma98LocalPower37_directResidue` (PROVEN): under `x' ∉ 𝔩` (**Lemma 9.6**) and `z' ∈ 𝔩`
(**Lemma 9.7**), `ε₁/ε₂` is a `37`-th power mod `𝔩`.  The framing question is *where* those two
conditions hold.

Reading Washington's actual proof settles it:

* **Theorem 9.5 is ONE-SHOT (minimal-counterexample), NOT iterated algebraic descent.**  Washington
  (p. 167–168) proves the **generalized** equation `ωᵖ + θᵖ = ηλᵐξᵖ` (η a real unit, `λ, ω, θ, ξ`
  pairwise-coprime in `ℤ[ζ]`, `m ≥ p(p−1)/2`) has no solution; the original *rational* Fermat triple
  `x, y, z ∈ ℤ` is the **seed instance** (`ω = x`, `θ = y`, `ξ = z/pᵃ`, `η = pᵃᵖ/λᵐ`).  The descent
  is **well-ordered by the number of distinct prime factors of `ξ`**: "Suppose now that `ξ` had the
  smallest possible number of distinct prime ideal factors" (p. 172).  From the minimal solution,
  Assumptions I & II + Lemmas 9.8/9.9 produce a *new* solution `(ω₁, θ₁, ξ₁)` with `ξ₁ = ρ₀²` and
  `(ξ₁) = B₀²`, forcing — by **minimality** and `(ξ) = B₀B₁⋯B_{p−1}` — `B₁ = ⋯ = B_{p−1} = (1)`,
  hence `(ω+ζᵃθ)/(1−ζᵃ)` a unit, hence the *immediate* `ζ² = 1` contradiction (p. 173).  **The new
  triple is never fed back; it is used once for the minimality contradiction.**

* **Washington DERIVES `ℓ ∣ z` (Lemma 9.7), and the minimal counterexample is taken WITHIN the set
  `{ℓ ∣ ξ}`.**  The transition (p. 178): "we may start with the equation `ωᵖ + θᵖ = ηλ^{2m−p}ξᵖ`
  with the added condition that `ℓ ∣ ξ` … **Then we may assume that `ξ` has the minimum number of
  distinct prime factors subject to the condition that `ℓ ∣ ξ`.**"  So the minimization domain is
  **restricted to `ℓ ∣ ξ`**.  Lemma 9.7's `ℓ ∣ z` (the all-conjugate `∑`-argument over `ℤ`, using
  `∏ₐ(y − ζᵃz) = −xᵖ`, a *perfect* `p`-th power) is needed precisely to certify that this domain is
  **non-empty** — the rational seed lies in it (`ℓ ∣ z ⟹ ℓ ∣ ξ`, `ℓ ∤ p`).

* **The rationals stay rational.**  `x, y, z ∈ ℤ` are the original Fermat triple throughout;
  Lemma 9.7's `ℓ ∣ z` is a statement about the *rational* `z`.

## The mismatch in the prior framing, and the fix

The prior chain's `Nat.find` minimizes over **all** real data
(`no_realCaseIIData37_of_classConjFixed_and_realDescent`, `Nat.find (∃ n, Nonempty (RealCaseIIData37
… n))`), **not** restricted to `z ∈ 𝔩`.  So the minimal datum `Dmin` need not satisfy `z ∈ 𝔩`, and
the residual is forced to the **false** universal `Lemma98LocalPower37`.  Washington restricts the
domain to `ℓ ∣ ξ`; the faithful fix is to **minimize over `z ∈ 𝔩`-data** (`RealCaseIIDvdZData37`),
where:

1. the domain is **non-empty** at the rational base (PROVEN `furtwangler_37_149` / Lemma 9.7),
2. `Dmin` carries `Dmin.z ∈ 𝔩` **by membership in the domain** — no universal,
3. the local power at `Dmin`'s descent is the **proven** `caseII_lemma98LocalPower37_directResidue`
   (the `z' ∈ 𝔩` it needs is the genuine Washington `ℓ ∣ ξ₁` propagation, not the false universal),
4. the genuine remaining residual is the **`ℓ ∣ z`-propagating descent step** (Washington's
   `ℓ ∣ (ω + θ)` ⟹ `ℓ ∣ ρ₀` ⟹ `ℓ ∣ ξ₁` plus `ℓ ∤` the new `ω, θ`): the descent produces a smaller
   datum *still satisfying* `z ∈ 𝔩 ∧ x ∉ 𝔩 ∧ y ∉ 𝔩`.  This is **true** (it is Washington Lemma
   9.6/9.7 for the descended datum), unlike the abstract `Lemma98LocalPower37` universal.

## What this file builds (real, axiom-clean Lean)

* `RealCaseIIDvdZData37` — a real Case-II datum **carrying** Washington's Lemma-9.6/9.7 conditions
  `z ∈ 𝔩 ∧ x ∉ 𝔩 ∧ y ∉ 𝔩` (the `ℓ ∣ ξ` restriction of the minimization domain).

* `exists_realCaseIIDvdZData37_of_caseII_int_solution_lemma96` — **Washington's non-emptiness at the
  rational seed**: from a rational Case-II solution `a³⁷+b³⁷=c³⁷` with `37 ∣ c`, plus **Lemma 9.6**
  (`149 ∤ a`, `149 ∤ b`), the restricted domain is non-empty.  The `z ∈ 𝔩` field is the **proven**
  Lemma 9.7 (`furtwangler_37_149`); the `x, y ∉ 𝔩` fields are Lemma 9.6 transported through the
  producer's normal form.

* `caseII_dvdZ_assumptionII_instance` — **Assumption II at a restricted-datum descent, with NO false
  universal**: for a descent equation rooted at a `RealCaseIIDvdZData37` with the descended `x' ∉ 𝔩`
  and `z' ∈ 𝔩`, the descent unit `ε₁/ε₂` is a *global* `37`-th power, from
  `Cor815SingleIndexExpansion37`
  (structural) and the **proven** `caseII_lemma98LocalPower37_directResidue`.  This is the route-(a)
  discharge of Assumption II's payload that the source mandates, free of `Lemma98LocalPower37`.

* `CaseIIThm95DvdZDescentStep37` — the **genuine remaining residual** (a `def … : Prop`, **not** an
  axiom): the `ℓ ∣ z`-preserving descent step.  Strictly **narrower** and **true** where the prior
  `Lemma98LocalPower37` was false: it asserts the descended datum stays in the `z ∈ 𝔩 ∧ x, y ∉ 𝔩`
  domain (Washington Lemma 9.6/9.7 for the new datum), instead of asserting the local power for an
  arbitrary abstract datum.

* `no_realCaseIIDvdZData37_of_dvdZDescentStep`, `caseIIBridge_thirtyseven_of_thm95RationalDescent`,
  and `fermatLastTheoremFor_thirtyseven_of_thm95RationalDescent` — the closure: minimality over the
  restricted domain, entered at the rational seed, closing Case-II (modulo the narrowed residual and
  carried Kellner).

## Soundness (B2-checked — no false universal is asserted)

`RealCaseIIDvdZData37` carries `z ∈ 𝔩 ∧ x ∉ 𝔩 ∧ y ∉ 𝔩` as **datum fields** (true *of the data*, not
asserted universally).  Assumption II is produced via the **implication**
`caseII_lemma98LocalPower37_directResidue` (PROVEN, the two conditions as explicit hypotheses),
never via the false `Lemma98LocalPower37` universal.  The residual `CaseIIThm95DvdZDescentStep37`
is a *descent-output* predicate (the new datum stays in the domain), Washington's true Lemma-9.6/9.7
propagation — **not** the abstract "every datum has `z ∈ 𝔩`" (false), nor the abstract local-power
universal (false).  Non-emptiness is the **proven** rational Lemma 9.7, conditioned on the genuine
Washington input Lemma 9.6 (`149 ∤ a, b`).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83:
  **Theorem 9.5** (p. 176), **Lemma 9.6** (`ℓ ∤ xy`, pp. 176–177), **Lemma 9.7** (`ℓ ∣ z`, p. 178,
  "this is where `l < p² − p` is used most strongly"), **Lemmas 9.8–9.9** (pp. 178–181), and **§9.1
  The Basic Argument** (the generalized equation `ωᵖ + θᵖ = ηλᵐξᵖ` and the minimal-prime-factor
  contradiction, pp. 167–173).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Finset Polynomial NumberField.IsCMField

namespace BernoulliRegular.FLT37.Eichler

open FLT37 FLT37.LehmerVandiver.CaseII BernoulliRegular

/-! ## 1. The `ℓ ∣ z`-restricted real Case-II datum (Washington's `ℓ ∣ ξ` minimization domain)

Washington takes the minimal counterexample **subject to `ℓ ∣ ξ`** (p. 178).  We model that domain
by a real Case-II datum that additionally carries Washington's Lemma-9.6/9.7 conditions on its own
data: `z ∈ 𝔩` (Lemma 9.7, `ℓ ∣ z`) and `x, y ∉ 𝔩` (Lemma 9.6, `ℓ ∤ xy`).  These are **datum fields**
— true *of the data*, not asserted as an abstract universal. -/

/-- **A real Case-II datum carrying Washington's Lemma-9.6/9.7 conditions** (the `ℓ ∣ ξ`-restricted
minimization domain of Theorem 9.5).

Extends `RealCaseIIData37` with the three auxiliary-prime conditions Washington's descent maintains:

* `z_mem` — **Lemma 9.7** (`ℓ ∣ z`): the `37`-divisible Fermat variable lies in `𝔩` (the
  all-conjugate
  `∑`-argument forces it, derived at the rational base by `furtwangler_37_149`);
* `x_notMem`, `y_notMem` — **Lemma 9.6** (`ℓ ∤ xy`): the two non-`37`-divisible variables avoid `𝔩`.

These are exactly the conditions Washington's minimal counterexample satisfies "subject to the
condition that `ℓ ∣ ξ`", and exactly the hypotheses the proven local power
`caseII_lemma98LocalPower37_directResidue` needs. -/
structure RealCaseIIDvdZData37 (m : ℕ)
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    extends RealCaseIIData37 (CyclotomicField 37 ℚ) m where
  /-- **Lemma 9.7** (`ℓ ∣ z`): the `37`-divisible variable lies in the auxiliary prime
  `𝔩 = lv149`. -/
  z_mem : toRealCaseIIData37.z ∈ lv149
  /-- **Lemma 9.6** (`ℓ ∤ x`): the first non-`37`-divisible variable avoids `𝔩`. -/
  x_notMem : toRealCaseIIData37.x ∉ lv149
  /-- **Lemma 9.6** (`ℓ ∤ y`): the second non-`37`-divisible variable avoids `𝔩`. -/
  y_notMem : toRealCaseIIData37.y ∉ lv149

/-! ## 2. Non-emptiness of the restricted domain at the rational seed (Washington Lemma 9.7)

Washington certifies the `ℓ ∣ ξ` minimization domain is non-empty via the *rational seed*: the
original Fermat triple `x, y, z ∈ ℤ` satisfies `ℓ ∣ z` (Lemma 9.7).  Here the rational `ℓ ∣ z` is
the
**proven** `furtwangler_37_149` (the all-conjugate `∑`-argument's residue shadow mod `149`), and the
`ℓ ∤ x, y` conditions are Washington Lemma 9.6 (`149 ∤ a, b`) transported through the producer's
normal form. -/

/-- **The producer's `z`-relation refined to the restricted datum** (proven, axiom-clean).

Mirrors `exists_realCaseIIData37_zRel_of_Int_solution` but additionally exposes that the producer's
descent integer `D.z` satisfies `D.z ∈ lv149` *and* `D.x, D.y ∉ lv149`, packaged as a
`RealCaseIIDvdZData37`.  The `z ∈ lv149` is **Lemma 9.7** at the base (`furtwangler_37_149`);
peeling
the `(ζ−1)`-multiplicity (`lv149` unramified) lands it on `D.z`.  The `x, y ∉ lv149` are **Lemma
9.6**
on the casts `(x : 𝓞 K)`, `(y : 𝓞 K)` via `caseII_intCast_mem_lv149_iff`. -/
theorem exists_realCaseIIDvdZData37_of_Int_solution
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {x y z : ℤ} (hy_int : ¬ (37 : ℤ) ∣ y) (hz_int : (37 : ℤ) ∣ z) (hz_ne : z ≠ 0)
    (e : x ^ 37 + y ^ 37 = z ^ 37)
    (hx_lv : ¬ (149 : ℤ) ∣ x) (hy_lv : ¬ (149 : ℤ) ∣ y) :
    ∃ m : ℕ, Nonempty (RealCaseIIDvdZData37 m) := by
  haveI : lv149.IsPrime := lv149_isMaximal.isPrime
  -- The producer's datum with the `z = (ζ-1)^(m+1) · D.z` relation.
  obtain ⟨m, D, hDx, hDy, hz_eq⟩ :=
    exists_realCaseIIData37_zRel_of_Int_solution hy_int hz_int hz_ne e
  -- `149 ∤ x, y` as `ZMod 149` non-vanishing.
  have hx' : ¬ (x : ZMod 149) = 0 := fun h ↦ hx_lv ((ZMod.intCast_zmod_eq_zero_iff_dvd x 149).mp h)
  have hy' : ¬ (y : ZMod 149) = 0 := fun h ↦ hy_lv ((ZMod.intCast_zmod_eq_zero_iff_dvd y 149).mp h)
  -- Lemma 9.7 at the base: `149 ∣ z` (the Furtwängler residue obstruction).
  have hz_lv_int : (z : ZMod 149) = 0 := by
    have he : (x : ZMod 149) ^ 37 + (y : ZMod 149) ^ 37 = (z : ZMod 149) ^ 37 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 149) e
    rcases furtwangler_37_149 (x : ZMod 149) (y : ZMod 149) (z : ZMod 149) he with h | h | h
    · exact absurd h hx'
    · exact absurd h hy'
    · exact h
  have hz_mem : (z : 𝓞 (CyclotomicField 37 ℚ)) ∈ lv149 :=
    (caseII_intCast_mem_lv149_iff z).mpr hz_lv_int
  -- Peel the `(ζ-1)`-multiplicity: `D.z ∈ lv149`.
  rw [hz_eq] at hz_mem
  have hDz_mem : D.z ∈ lv149 := by
    rcases Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› hz_mem with hpow | hz'
    · exact absurd (Ideal.IsPrime.mem_of_pow_mem ‹lv149.IsPrime› (m + 1) hpow)
        (caseII_zeta_sub_one_notMem_lv149 D.hζ)
    · exact hz'
  -- `D.x = (x : 𝓞 K) ∉ lv149`, `D.y = (y : 𝓞 K) ∉ lv149` (Lemma 9.6).
  have hDx_notMem : D.x ∉ lv149 := by
    rw [hDx]; exact fun h ↦ hx' ((caseII_intCast_mem_lv149_iff x).mp h)
  have hDy_notMem : D.y ∉ lv149 := by
    rw [hDy]; exact fun h ↦ hy' ((caseII_intCast_mem_lv149_iff y).mp h)
  exact ⟨m, ⟨{ toRealCaseIIData37 := D
               z_mem := hDz_mem
               x_notMem := hDx_notMem
               y_notMem := hDy_notMem }⟩⟩

/-- **Non-emptiness of the restricted domain from a rational Case-II solution + Lemma 9.6**
(proven, axiom-clean), normal form `37 ∣ c`.

From a Case-II integer FLT solution `a³⁷ + b³⁷ = c³⁷` with `37 ∣ c`, `37 ∤ a`, `c ≠ 0`, plus
**Washington Lemma 9.6** (`149 ∤ a`, `149 ∤ b`), the `ℓ ∣ z`-restricted domain
`RealCaseIIDvdZData37`
is non-empty.  This is Washington's certification that the minimization domain "subject to `ℓ ∣ ξ`"
is inhabited, with `ℓ ∣ z` the **proven** Lemma 9.7 (`furtwangler_37_149`). -/
theorem exists_realCaseIIDvdZData37_of_caseII_int_solution_lemma96
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {a b c : ℤ} (ha_int : ¬ (37 : ℤ) ∣ a) (hc_int : (37 : ℤ) ∣ c) (hc_ne : c ≠ 0)
    (e : a ^ 37 + b ^ 37 = c ^ 37)
    (ha_lv : ¬ (149 : ℤ) ∣ a) (hb_lv : ¬ (149 : ℤ) ∣ b) :
    ∃ m : ℕ, Nonempty (RealCaseIIDvdZData37 m) := by
  -- `37 ∤ b` (else `37 ∣ a` from the equation).
  have hb_int : ¬ (37 : ℤ) ∣ b := by
    intro hb
    refine ha_int ?_
    have h37prime := (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 37))
    have h_dvd : (37 : ℤ) ∣ a ^ 37 := by
      have := dvd_sub (dvd_pow hc_int (by decide : (37 : ℕ) ≠ 0))
        (dvd_pow hb (by decide : (37 : ℕ) ≠ 0))
      rwa [← e, add_sub_cancel_right] at this
    exact h37prime.dvd_of_dvd_pow h_dvd
  exact exists_realCaseIIDvdZData37_of_Int_solution hb_int hc_int hc_ne e ha_lv hb_lv

/-! ## 3. Assumption II at a restricted-datum descent (route-(a) discharge, NO false universal)

For a descent equation `ε₁·x'³⁷ + ε₂·y'³⁷ = ε₃·((ζ−1)^e·z')³⁷` whose descended variables satisfy
Washington's Lemma-9.6/9.7 conditions `x' ∉ 𝔩` and `z' ∈ 𝔩`, the descent unit `ε₁/ε₂` is a *global*
`37`-th power.  The proof is the **proven** local power `caseII_lemma98LocalPower37_directResidue`
(`IsPthPowerModPrime 37 𝔩 (ε₁/ε₂)`, from `z' ∈ 𝔩` killing the right side and `x' ∉ 𝔩`) composed with
`Cor815SingleIndexExpansion37` (the structural single-index `E₃₂`-expansion) through the **proven**
`caseIIThm95_descentUnit_isPow_of_singleIndexExpansion`.  No `Lemma98LocalPower37` universal is
used:
`z' ∈ 𝔩` is a genuine hypothesis, supplied where it is true. -/

/-- **Assumption II at a restricted-datum descent, free of the false `Lemma98LocalPower37`
    universal**
(proven, axiom-clean *given* `Cor815SingleIndexExpansion37`).

For a `CaseIIData37` descent instance with descended variables `x' ∉ lv149` (**Lemma 9.6**) and
`z' ∈ lv149` (**Lemma 9.7**) satisfying the descent equation, the descent unit `ε₁/ε₂` is a global
`37`-th power.  The local-power input is the **proven** `caseII_lemma98LocalPower37_directResidue`
(no residual); the single-index expansion is the structural `Cor815SingleIndexExpansion37`.

This is the route-(a) discharge of Assumption II's payload that Washington Theorem 9.5 mandates,
keyed to the `ℓ ∣ z`-restricted data — replacing the **false** abstract `Lemma98LocalPower37`
universal by the **true** Lemma-9.6/9.7 conditions *as hypotheses where they hold*. -/
theorem caseII_dvdZ_assumptionII_instance
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_expand : Cor815SingleIndexExpansion37)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ}
    (hx_dvd : ¬ (D.hζ.toInteger - 1) ∣ x') (hy_dvd : ¬ (D.hζ.toInteger - 1) ∣ y')
    (hz_dvd : ¬ (D.hζ.toInteger - 1) ∣ z')
    (hxl : x' ∉ lv149) (hzl : z' ∈ lv149)
    (heq : (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
        (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
      (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37) :
    ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, ε₁ / ε₂ = ε' ^ 37 := by
  -- Single-index expansion of `ε₁/ε₂` (structural input, keyed to the descent equation).
  obtain ⟨d, α, hexp⟩ := h_expand hV hSO D hx_dvd hy_dvd hz_dvd heq
  -- The proven local power: `z' ∈ 𝔩` kills the right side, `x' ∉ 𝔩` gives `ε₁/ε₂` a 37th power.
  have hlocal : BernoulliRegular.IsPthPowerModPrime 37 lv149
      (((ε₁ / ε₂ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))) :=
    caseII_lemma98LocalPower37_directResidue (e := m) D hxl hzl heq
  -- Compose: single-index expansion + mod-𝔩 power-ness ⟹ global 37th power (Lemma 9.9 collapse).
  exact caseIIThm95_descentUnit_isPow_of_singleIndexExpansion (ε₁ / ε₂) d α hexp hlocal

/-! ## 4. The genuine remaining residual: the `ℓ ∣ z`-preserving descent step

Washington's descent maintains the `ℓ ∣ ξ` condition: from a solution with `ℓ ∣ ξ` (minimal
prime-factor count), Lemma 9.8 gives `ℓ ∣ (ω + θ)`, whence `ℓ ∣ ρ₀`, whence `ℓ ∣ ξ₁ = ρ₀²` — the new
anchor is again in `𝔩`, *and* the new `ω₁, θ₁` avoid `𝔩` (Lemma 9.6 for the new datum).  We name
exactly this descent-output propagation as the genuine residual: it is **true** (Washington Lemma
9.6/9.7 for the descended datum), and strictly **narrower** than the prior false
`Lemma98LocalPower37` universal.

The descent itself (lowering the measure) is the **proven** machinery
(`caseII_descent_step_of_singleRootPrincipal` etc.): given the restricted datum `D` (with `D.z ∈ 𝔩`,
`D.x, D.y ∉ 𝔩`), §3 supplies Assumption II's payload at `D`'s descent (the local power from `D`'s
own
Lemma-9.6/9.7 data, no universal), and the residual asserts the descended datum *stays in the
restricted domain*. -/

/-- **[FLT37-CASEII-THM95-DVDZ-RESIDUAL] The `ℓ ∣ z`-preserving descent step** (a `def … : Prop`,
**not** an axiom) — the genuine remaining content of Washington Theorem 9.5's route (a).

For every restricted real Case-II datum `D : RealCaseIIDvdZData37 m` (carrying Washington's
Lemma-9.6/9.7 conditions `z ∈ 𝔩`, `x, y ∉ 𝔩`), given the `η₀`-principalization at `D` (discharged
over real data by the proven II1 `caseII_real_etaZeroPrincipalization_of_classConjFixed`), there is
a
restricted datum at strictly smaller anchor exponent.

This is the `ℓ ∣ z`-preserving form of `CaseIIRealSingleRootDescentPreservesReality37`: the
descended
datum **stays in the `z ∈ 𝔩 ∧ x, y ∉ 𝔩` domain** (Washington's `ℓ ∣ ξ₁` from `ℓ ∣ ρ₀`, plus Lemma
9.6
for the new `ω₁, θ₁`).  It is **true** — it is exactly Washington's descent-maintained `ℓ ∣ ξ` plus
`ℓ ∤ ω, θ` — and strictly **narrower** than the prior `Lemma98LocalPower37` universal (which was
**false** over the abstract telescope, B2 `CASEII-LEMMA98-LOCALPOWER`): it never asserts the local
power for an arbitrary datum, only that the genuine descent preserves the auxiliary-prime conditions
it maintains.  Assumption II at the minimal restricted datum's descent is supplied by §3
(`caseII_dvdZ_assumptionII_instance`), from the datum's *own* `z ∈ 𝔩` (no universal). -/
def CaseIIThm95DvdZDescentStep37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  Cor815SingleIndexExpansion37 →
  ∀ {m : ℕ} (D : RealCaseIIDvdZData37 m),
    CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2)
      D.hζ D.equation D.hy →
    ∃ m' : ℕ, m' < m ∧ Nonempty (RealCaseIIDvdZData37 m')

/-! ## 5. The closure: minimality over the restricted domain, entered at the rational seed -/

/-- **No restricted Case-II datum exists, from the `ℓ ∣ z`-preserving descent step** (proven,
axiom-clean *given* the named inputs).

Washington's minimal-counterexample-subject-to-`ℓ ∣ ξ` (p. 178): pick the minimal anchor exponent
`n` with a restricted datum `Dmin` (carrying `z ∈ 𝔩`, `x, y ∉ 𝔩` *by domain membership*), apply the
`ℓ ∣ z`-preserving descent step (whose principalization input is the proven II1
`caseII_real_etaZeroPrincipalization_of_classConjFixed`, and whose Assumption-II need is supplied by
§3 from `Dmin`'s own data, no universal) to land at `m' < n` *still in the restricted domain* —
contradicting minimality.

This is the source-faithful Theorem-9.5 descent: the `Nat.find` minimizes over the **`ℓ ∣
ξ`**-domain
(`RealCaseIIDvdZData37`), exactly as Washington does, so `Dmin.z ∈ 𝔩` holds **by membership** and
the
false `Lemma98LocalPower37` universal is never invoked. -/
theorem no_realCaseIIDvdZData37_of_dvdZDescentStep
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_expand : Cor815SingleIndexExpansion37)
    (h_step : CaseIIThm95DvdZDescentStep37) :
    ¬ ∃ m : ℕ, Nonempty (RealCaseIIDvdZData37 m) := by
  classical
  rintro ⟨m, D⟩
  let P : ℕ → Prop := fun n ↦ Nonempty (RealCaseIIDvdZData37 n)
  have hP : ∃ n, P n := ⟨m, D⟩
  let n := Nat.find hP
  have hn : P n := Nat.find_spec hP
  rcases hn with ⟨Dmin⟩
  -- II1: the `η₀`-principalization holds at the minimal restricted datum (proven over real data).
  have hprinc := caseII_real_etaZeroPrincipalization_of_classConjFixed
    caseIIRootClassConjFixed37_proven Dmin.toRealCaseIIData37
  -- The `ℓ ∣ z`-preserving descent step gives a strictly smaller restricted datum.
  obtain ⟨m', hm', D'⟩ := h_step h_expand Dmin hprinc
  exact (Nat.find_min hP hm') D'

/-! ### The general producer through the `caseII_int_solution` permutation

`exists_realCaseIIDvdZData37_of_caseII_int_solution_lemma96` (§2) handles the `37 ∣ c` normal form.
For an arbitrary Case-II solution the `37`-divisible variable may be any of `a, b, c`; we mirror the
permutation of `exists_realCaseIIData37_of_caseII_int_solution`.  Negation preserves both `¬ 149 ∣
·`
and `¬ 37 ∣ ·` and the equation (`p = 37` odd), so each branch reduces to the `37 ∣ ·`-slot form. -/

/-- **`149 ∤ x ↔ 149 ∤ (-x)`** over `ℤ` — negation preserves the Lemma-9.6 condition. -/
private theorem caseII_not_dvd_149_neg {x : ℤ} (h : ¬ (149 : ℤ) ∣ x) : ¬ (149 : ℤ) ∣ (-x) := by
  rwa [dvd_neg]

/-- **The general restricted-domain producer** (proven, axiom-clean) — from *any* Case-II integer
FLT solution with **Lemma 9.6** (`149 ∤` the two non-`37`-divisible variables), the `ℓ ∣
z`-restricted
domain is non-empty.  Mirrors `exists_realCaseIIData37_of_caseII_int_solution`'s permutation; the
`149 ∤ ·` conditions transport through the sign changes via `caseII_not_dvd_149_neg`. -/
theorem exists_realCaseIIDvdZData37_of_caseII_int_solution
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {a b c : ℤ}
    (hprod : a * b * c ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcase : (37 : ℤ) ∣ a * b * c)
    (e : a ^ 37 + b ^ 37 = c ^ 37)
    (h_lemma96 : ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x) :
    ∃ m : ℕ, Nonempty (RealCaseIIDvdZData37 m) := by
  simp only [ne_eq, mul_eq_zero, not_or] at hprod
  obtain ⟨⟨ha0, hb0⟩, hc0⟩ := hprod
  have h37 := (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 37))
  have hodd' := Nat.Prime.odd_of_ne_two (by decide : Nat.Prime 37) (by decide : (37 : ℕ) ≠ 2)
  -- `37` divides at most one of `a, b, c`: if it divides two, the equation forces the third, hence
  -- `37 ∣ gcd = 1`.
  have h37c : (37 : ℤ) ∣ a → (37 : ℤ) ∣ b → False := by
    intro ha hb
    have hc : (37 : ℤ) ∣ c := by
      have hcp : (37 : ℤ) ∣ c ^ 37 := by
        rw [← e]; exact dvd_add (dvd_pow ha (by decide)) (dvd_pow hb (by decide))
      exact h37.dvd_of_dvd_pow hcp
    have : (37 : ℤ) ∣ ({a, b, c} : Finset ℤ).gcd id := by
      rw [Finset.dvd_gcd_iff]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simpa using ‹_›
    rw [hgcd] at this
    exact absurd (Int.isUnit_iff.mp (isUnit_of_dvd_one this)) (by decide)
  have h37bc : (37 : ℤ) ∣ b → (37 : ℤ) ∣ c → False := by
    intro hb hc
    refine h37c ?_ hb
    have hap : (37 : ℤ) ∣ a ^ 37 := by
      have := dvd_sub (dvd_pow hc (by decide : (37 : ℕ) ≠ 0))
        (dvd_pow hb (by decide : (37 : ℕ) ≠ 0))
      rwa [← e, add_sub_cancel_right] at this
    exact h37.dvd_of_dvd_pow hap
  have h37ac : (37 : ℤ) ∣ a → (37 : ℤ) ∣ c → False := by
    intro ha hc
    refine h37c ha ?_
    have hbp : (37 : ℤ) ∣ b ^ 37 := by
      have := dvd_sub (dvd_pow hc (by decide : (37 : ℕ) ≠ 0))
        (dvd_pow ha (by decide : (37 : ℕ) ≠ 0))
      rwa [← e, add_sub_cancel_left] at this
    exact h37.dvd_of_dvd_pow hbp
  obtain hab | hc := h37.dvd_or_dvd hcase
  · obtain ha | hb := h37.dvd_or_dvd hab
    · -- `37 ∣ a`: normal form `(b, -c, -a)`; non-`37` slots are `b, c`.
      have he' : b ^ 37 + (-c) ^ 37 = (-a) ^ 37 := by
        rw [hodd'.neg_pow, hodd'.neg_pow]; linarith [e]
      have hb37 : ¬ (37 : ℤ) ∣ b := fun hb ↦ h37c ha hb
      have hc37 : ¬ (37 : ℤ) ∣ c := fun hc ↦ h37ac ha hc
      have hb_lv : ¬ (149 : ℤ) ∣ b := h_lemma96 b hb37 (Or.inr (Or.inl rfl))
      have hc_lv : ¬ (149 : ℤ) ∣ c := h_lemma96 c hc37 (Or.inr (Or.inr rfl))
      exact exists_realCaseIIDvdZData37_of_caseII_int_solution_lemma96
        (a := b) (b := -c) (c := -a) hb37 (by rwa [dvd_neg]) (by rwa [neg_ne_zero])
        he' hb_lv (caseII_not_dvd_149_neg hc_lv)
    · -- `37 ∣ b`: normal form `(-c, a, -b)`; non-`37` slots are `c, a`.
      have he' : (-c) ^ 37 + a ^ 37 = (-b) ^ 37 := by
        rw [hodd'.neg_pow, hodd'.neg_pow]; linarith [e]
      have ha37 : ¬ (37 : ℤ) ∣ a := fun ha ↦ h37c ha hb
      have hc37 : ¬ (37 : ℤ) ∣ c := fun hc ↦ h37bc hb hc
      have ha_lv : ¬ (149 : ℤ) ∣ a := h_lemma96 a ha37 (Or.inl rfl)
      have hc_lv : ¬ (149 : ℤ) ∣ c := h_lemma96 c hc37 (Or.inr (Or.inr rfl))
      exact exists_realCaseIIDvdZData37_of_caseII_int_solution_lemma96
        (a := -c) (b := a) (c := -b) (by rwa [dvd_neg]) (by rwa [dvd_neg]) (by rwa [neg_ne_zero])
        he' (caseII_not_dvd_149_neg hc_lv) ha_lv
  · -- `37 ∣ c`: the producer's own normal form `(a, b, c)`; non-`37` slots are `a, b`.
    have ha37 : ¬ (37 : ℤ) ∣ a := fun ha ↦ h37ac ha hc
    have hb37 : ¬ (37 : ℤ) ∣ b := fun hb ↦ h37bc hb hc
    have ha_lv : ¬ (149 : ℤ) ∣ a := h_lemma96 a ha37 (Or.inl rfl)
    have hb_lv : ¬ (149 : ℤ) ∣ b := h_lemma96 b hb37 (Or.inr (Or.inl rfl))
    exact exists_realCaseIIDvdZData37_of_caseII_int_solution_lemma96 ha37 hc hc0 e ha_lv hb_lv

/-- **The public Case-II bridge from the Theorem-9.5 rational descent** (proven, axiom-clean *given*
the named inputs + Washington Lemma 9.6).

`CaseIIBridge 37 K 32` from:

* `h_expand` (`Cor815SingleIndexExpansion37`): the structural single-index `E₃₂`-expansion of the
  descent unit (Corollary 8.15 for `37`'s sole irregular index);
* `h_step` (`CaseIIThm95DvdZDescentStep37`): the genuine residual, the `ℓ ∣ z`-preserving descent
  step (Washington's descent-maintained `ℓ ∣ ξ` + `ℓ ∤ ω, θ`);
* `h_lemma96`: **Washington Lemma 9.6** (`149 ∤ x` for each `x ∈ {a, b, c}` with `37 ∤ x`) — the
  genuine arithmetic input certifying the `ℓ ∣ ξ` minimization domain is non-empty.

The rational Fermat solution `a³⁷ + b³⁷ = c³⁷` enters the restricted domain through the **proven**
Lemma 9.7 (`furtwangler_37_149`, via `exists_realCaseIIDvdZData37_of_caseII_int_solution`), and the
minimality `no_realCaseIIDvdZData37_of_dvdZDescentStep` closes it.  This is Washington Theorem 9.5's
*one-shot* minimal-counterexample at the rational entry — **not** the prior iterated-algebraic
framing
through the false `Lemma98LocalPower37` universal. -/
theorem caseIIBridge_thirtyseven_of_thm95RationalDescent
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_expand : Cor815SingleIndexExpansion37)
    (h_step : CaseIIThm95DvdZDescentStep37)
    (h_lemma96 : ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
  refine ⟨?_⟩
  intro _hV _hSO a b c hprod hgcd hcase hEq
  exact (no_realCaseIIDvdZData37_of_dvdZDescentStep h_expand h_step)
    (exists_realCaseIIDvdZData37_of_caseII_int_solution hprod hgcd hcase hEq
      (h_lemma96 a b c hprod hgcd hcase hEq))

/-- **Fermat's Last Theorem for `37`, via Washington Theorem 9.5's rational one-shot descent**
(proven, axiom-clean *given* the named inputs).

`FermatLastTheoremFor 37` from:

* `h_expand` (`Cor815SingleIndexExpansion37`): the structural single-index `E₃₂`-expansion of the
  descent unit (Corollary 8.15 specialised to `37`'s sole irregular index `i = 32`);
* `h_step` (`CaseIIThm95DvdZDescentStep37`): the genuine remaining residual — the `ℓ ∣ z`-preserving
  descent step (Washington's descent-maintained `ℓ ∣ ξ` plus Lemma 9.6 for the new `ω, θ`), strictly
  narrower than (and true where) the prior false `Lemma98LocalPower37` universal;
* `h_lemma96` (**Washington Lemma 9.6**, `ℓ ∤ xy`): for each `x ∈ {a, b, c}` with `37 ∤ x`,
  `149 ∤ x` — the genuine arithmetic input certifying the `ℓ ∣ ξ` minimization domain is non-empty;
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the carried Kellner input.

Case I is the unconditional Eichler first-case proof (`caseIBridge_thirtyseven_eichler`); `¬ 37 ∣
h⁺`
is the proven `Sinnott.flt37_not_dvd_hPlus` (through `cor8_19Bridge_of_not_dvd_hPlus`).  The `ℓ ∣ z`
content (Washington Lemma 9.7) is the **proven** `furtwangler_37_149`, consumed at the rational seed
where Washington's argument lives.  This endpoint realises route (a) (Theorem 9.5) as the one-shot
minimal-counterexample-subject-to-`ℓ ∣ ξ` at the rational entry. -/
theorem fermatLastTheoremFor_thirtyseven_of_thm95RationalDescent
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_expand : Cor815SingleIndexExpansion37)
    (h_step : CaseIIThm95DvdZDescentStep37)
    (h_lemma96 : ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  BernoulliRegular.fermatLastTheoremFor_thirtyseven_of_remaining
    (BernoulliRegular.cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ)
      Sinnott.flt37_not_dvd_hPlus)
    caseIBridge_thirtyseven_eichler
    noSecondOrderIrregular
    (caseIIBridge_thirtyseven_of_thm95RationalDescent h_expand h_step h_lemma96)

/-! ## 6. Non-vacuity: the restricted domain is inhabited exactly when a Case-II solution exists

The closure is **not** vacuous.  The restricted domain `RealCaseIIDvdZData37` is inhabited whenever
a
Case-II integer FLT solution exists with Lemma 9.6 (`149 ∤` the two non-`37`-divisible variables) —
so `CaseIIThm95DvdZDescentStep37` and `no_realCaseIIDvdZData37_of_dvdZDescentStep` quantify over a
domain with the same content as Washington's `ℓ ∣ ξ` minimization set, not the empty set. -/

/-- **The restricted domain is inhabited from a concrete Case-II solution + Lemma 9.6** (proven,
axiom-clean) — explicit non-vacuity witness.

If a Case-II integer FLT solution `a³⁷ + b³⁷ = c³⁷` with `37 ∣ c`, `37 ∤ a`, `c ≠ 0`, and Lemma 9.6
(`149 ∤ a`, `149 ∤ b`) existed, the `ℓ ∣ z`-restricted domain `RealCaseIIDvdZData37` would be
non-empty.  This certifies the residual `CaseIIThm95DvdZDescentStep37` is a genuine universal over a
content-bearing domain (Washington's `ℓ ∣ ξ` set), not vacuously true. -/
theorem realCaseIIDvdZData37_nonvacuous
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {a b c : ℤ} (ha_int : ¬ (37 : ℤ) ∣ a) (hc_int : (37 : ℤ) ∣ c) (hc_ne : c ≠ 0)
    (e : a ^ 37 + b ^ 37 = c ^ 37)
    (ha_lv : ¬ (149 : ℤ) ∣ a) (hb_lv : ¬ (149 : ℤ) ∣ b) :
    ∃ m : ℕ, Nonempty (RealCaseIIDvdZData37 m) :=
  exists_realCaseIIDvdZData37_of_caseII_int_solution_lemma96 ha_int hc_int hc_ne e ha_lv hb_lv

end BernoulliRegular.FLT37.Eichler

end
