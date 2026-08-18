# /mathlibable report — `Chebotarev.log_artinLSeries_asymp_character_sum`

_(Step-9 overview-driven full assessment. Local Lean build stale; mathlib-index MCP
tools unavailable in this environment — reasoned from source + WebSearch + mathlib
docs. lean_loogle/leansearch/local_search not reachable; recorded n/a where applicable.)_

## Baseline (Phase 0)
- lake build:               not run (stale local build; assessment reasons from source per task brief)
- decl `Chebotarev.log_artinLSeries_asymp_character_sum`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/Cyclotomic.lean:96`
- qualified name:           **`Chebotarev.log_artinLSeries_asymp_character_sum`** (namespace `Chebotarev`
  opened at `Cyclotomic.lean:49`; VERIFIED from source — the prompt's guess is correct)
- kind:                     theorem
- has sorry:                no
- module docstring summary: Chebotarev's theorem, cyclotomic case — density of primes of `K`
  unramified in `K(μ_m)` with a given Frobenius is `1/|Gal|`.

## Statement (Phase 1)

`log_artinLSeries_asymp_character_sum` is a **theorem** asserting an analytic upper bound,
not (despite its name and docstring) a genuine asymptotic. For a Galois character
`χ : Gal(L/K) →* ℂˣ` of a finite abelian Galois extension `L/K` of number fields, it states
that there is a constant `C : ℝ` such that, for `s` near `1` from the right,

> `‖ Σ'_{𝔭 prime, unramified in L}  χ(Frob 𝔭) · N𝔭^{-s} ‖  ≤  C · log(1/(s−1)) + C`.

So it bounds the norm of the character-twisted partial zeta-sum over unramified primes by a
multiple of `log(1/(s−1))` plus a constant, eventually on `𝓝[>] 1`.

The *docstring* advertises the textbook statement `log L(χ,s) ~ Σ_𝔭 χ(𝔭) N𝔭^{-s}` (Sharifi
7.2.1 step (ii)), but the **Lean conclusion never mentions `log L(χ,s)`**: the L-function does
not appear. What is actually proved is the one-sided bound on the prime-side sum that the
density proof needs downstream.

Variables / typeclasses (Lean side):
- `K L : Type*`, `[Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]`
  — finite Galois extension of number fields.
- `[IsMulCommutative Gal(L/K)]` — the Galois group is abelian (cyclotomic case).
- `(χ : galoisCharacter K L)` — i.e. `Gal(L/K) →* ℂˣ`, a project-local abbrev (`ZetaProduct.lean:71`).

Hypotheses: none beyond the typeclasses.

Conclusion (math): the twisted prime-norm sum is `O(log(1/(s−1)))` near `s = 1⁺` (as a crude
upper bound; the actual `IsBigO`/`~` is not used).
Conclusion (Lean): `∃ C : ℝ, ∀ᶠ s in 𝓝[>] 1, ‖Σ' 𝔭, χ(Frob 𝔭)·N𝔭^{-s}‖ ≤ C·log(1/(s−1)) + C`.

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: an internal sub-lemma — sub-step (ii) of four in the decomposition of
`chebotarev_cyclotomic` (the file's `## Main results` lists only `chebotarev_cyclotomic`, not
this). Not named after a person; introduces no new structure. (Lit width run EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure`. One-liner check **n/a**. (Body is ~64 lines.)

## Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "log L-function Dirichlet series asymptotic sum over primes Re(s)>1 mathlib4" | yes | `log L(χ,s) = Σ_𝔭 χ(𝔭)/N𝔭^s + O(1)` for Re s>1 | the **textbook** statement (the docstring's claim); standard in any analytic NT text (Sharifi 7.1.10/7.2.1, Marcus, Neukirch VII). Our Lean form is **weaker** (one-sided norm bound, no L-function). |
| 2 | WebSearch (general form) | "Chebotarev density theorem proof log Artin L-function asymptotic prime sum Stevenhagen Lenstra" | yes | `Σ_χ χ̄(σ) log L(χ,s) ~ |G| Σ_{Frob=σ} N𝔭^{-s}` and `~ log(1/(s−1))` | Stevenhagen–Lenstra appendix ¶3; the asymptotic is a *named intermediate step* of the Chebotarev proof, never an independently-quoted theorem with this exact shape. |
| 3 | WebSearch (named/aliases) | "Asymptotics.IsBigO isBigO filter eventually norm le bounded log L-series" | partial | mathlib's general idiom for "f bounded by g near a filter" is `f =O[l] g` (`Asymptotics.IsBigO`) | confirms the *modern container* (IsBigO) exists; no specific lemma of this content. |
| 4 | ChatGPT MCP | (server down in this env — fallback to WebSearch #1–#3 + mathlib docs) | n/a | — | MCP unavailable per task brief; compensated with extra WebSearch + direct mathlib-doc WebFetch (#9). |
| 5 | Local references | grep `.mathlib-quality/references/` and `refs/Chebotarev/` | n/a | (neither dir exists) | no references dir for this project; the in-file docstring cites Sharifi §7.2.1 p.142 + Stevenhagen–Lenstra ¶3 verbatim. |
| 6 | nLab | "Chebotarev density theorem" / "Dirichlet density" | yes (weak) | nLab states Chebotarev + Dirichlet density abstractly; no `log L ~ Σχ N^{-s}` lemma | nLab treats the statement, not the analytic prime-sum bound. |
| 7 | nCatLab | n/a | n/a | — | not a categorical statement (concrete analytic NT inequality). |
| 8 | Stacks Project | n/a | n/a | — | not an algebraic-geometry / scheme-theoretic statement. |
| 9 | mathlib docs (WebFetch) | `Mathlib/NumberTheory/LSeries/PrimesInAP.html` — does it bound log L by a prime sum / `C·log(1/(s−1))+C`? | no (closest only) | closest: `vonMangoldt.LSeries_residueClass_eq` (log-deriv ↔ residue class on Re s>1); `vonMangoldt.LSeries_residueClass_lower_bound` (`(φ(q))⁻¹/(x−1) − C` lower bd) | mathlib's Dirichlet machinery works with **von Mangoldt log-derivatives**, NOT a `χ(𝔭)N𝔭^{-s}` log-asymptotic; no number-field / Galois-character analogue at all. |
| 10 | recent arXiv (≤5y) | "Formalizing zeta and L-functions in Lean" (arXiv 2503.00959) | yes | confirms mathlib L-series scope: `LSeriesHasSum`, `LSeriesSummable`, Euler products, Dedekind class-number formula (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) | establishes the **boundary** of mathlib: Artin L-functions of `Gal(L/K)` and their `log`-asymptotics are NOT in mathlib. |

### Literature summary (Phase 3)

Concept identified as: the analytic estimate `log L(χ,s) ≈ Σ_𝔭 χ(𝔭) N𝔭^{-s}` for `Re s > 1`
(Sharifi step (ii)) — but the **Lean statement is a strictly weaker derived corollary**: a
one-sided norm bound `‖Σ_𝔭 χ(Frob 𝔭) N𝔭^{-s}‖ ≤ C·log(1/(s−1)) + C`, with the L-function
absent.
Sources agree on the standard (textbook) form: yes — but no source states *this* derived
inequality as a standalone result; it is an internal step of the Chebotarev/Dirichlet argument.
Most general standard form: the two-sided asymptotic with `log L(χ,s)`; specialises to (and is far
stronger than) the project's one-sided prime-side bound.
Generality dimensions where the literature varies: base field (ℚ vs general number field `K`);
character (Dirichlet vs Artin/Galois `χ` of `Gal(L/K)`); container (`~`, `IsBigO`, or explicit
constant). The project sits at: general `K`, abelian-Galois `χ`, explicit-constant one-sided.
Disagreement with the literature: the **name oversells the content** — "asymp" / "log L-function"
suggest the textbook asymptotic, but the Lean type is a crude triangle-inequality majorant of the
prime-side only. (Not a mathematical error — the bound is exactly what the density proof consumes.)

## Generality analysis — `Chebotarev.log_artinLSeries_asymp_character_sum`

Literature-standard form (from Phase 3): two-sided `log L(χ,s) ~ Σ_𝔭 χ(𝔭) N𝔭^{-s}`, Re s > 1.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|---------------------|--------|
| 1 | `χ : galoisCharacter K L` | character of `Gal(L/K)`→ℂˣ | Dirichlet or Artin char | — | this *is* the project's central object; cannot weaken without leaving the proof. |
| 2 | `[IsMulCommutative Gal(L/K)]` | abelian Galois group | not needed for the bound itself | yes (unused) | the **norm bound uses only `|χ(c.out)|=1`** (proof lines 104–107) — abelianness is inherited from the calling context, not used here. A minor over-hypothesis, but irrelevant to mathlib-ability. |
| 3 | conclusion shape | `‖·‖ ≤ C·log(1/(s−1)) + C` | `= log L(χ,s) + O(1)` / `IsBigO` | n/a (this is *narrower*, not generalisable) | the Lean form throws away the L-function and the lower bound; it is a derived majorant, structurally weaker than the literature object. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is a one-sided corollary of the
textbook two-sided asymptotic), and simultaneously **hyper-specialised to the project** (bespoke
`galoisCharacter`, `frobeniusClass`, `UnramifiedIn`-subtype, `Ideal.absNorm`, the project's own
`primeIdealZetaSum_le_log_plus_bounded`). Number of weakening opportunities: 1 cosmetic (drop the
unused `IsMulCommutative`). No *generalisation toward mathlib* is meaningful — the statement is a
glue step, not an instance of a general theorem.
Proposed restatement: none worth pursuing for mathlib (see Phase 7).
Cost of any restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream |
|---|----------|----------|------------------------|--------------------|
| 1 | "let X be a foo" → typeclass? | no | already typeclass-based | — |
| 2 | sequences/metric → filters/topology? | **partially** | the bound `‖f s‖ ≤ C·g s + C` eventually on `𝓝[>]1` is morally `f =O[𝓝[>]1] g` — mathlib's `Asymptotics.IsBigO`. The project **already uses `=O[Filter.atTop]`** in `ZetaProduct.lean:2185, 2200, 2314` (`sum_galoisCharacterCoeff_isBigO` etc.). | would compose with `Asymptotics.IsBigO.trans`, `.add`, etc. **But** this is a *project-style* improvement, not a mathlib-ability argument: an `IsBigO` restatement of a project-glue lemma is still project glue. |
| 3 | construct → universal property? | no | — | — |
| 4 | set+closure → bundled substructure? | no | — | — |
| 5 | vector-space/field → module/ring? | no | — | — |
| 6 | 1-categorical → higher? | no | — | — |
| 7 | concrete index → general algebra? | no | indices are intrinsic (prime ideals of `𝓞 K`) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes (cosmetic only)** — restating the conclusion as
`(fun s ↦ Σ' 𝔭, χ(Frob 𝔭)·N𝔭^{-s}) =O[𝓝[>] 1] (fun s ↦ log(1/(s−1)))` would match the
project's own `isBigO` style and compose better with mathlib's `Asymptotics` API.
Real mathematical improvement: **no** — it would re-package the *same* project-internal glue
lemma. It does not eliminate a redundancy or unlock mathlib API for any *general* statement,
because there is no general statement here: every symbol (`galoisCharacter`, `frobeniusClass`,
`UnramifiedIn`, `primeIdealZetaSum`) is project-bespoke. This is a refactor note for the project,
not a mathlib-upstreaming lever. (Recorded so Phase 7 does not mistake it for MODERN-IDIOM YES.)

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (introduces no definitional equality or instance-search path).

## Mathlib search-status: `Chebotarev.log_artinLSeries_asymp_character_sum`

[A] Lean-Finder       — (MCP unavailable in env) — n/a: tool not reachable
[B] Loogle            `‖?‖ ≤ _ * Real.log _ + _`, `Asymptotics.IsBigO _ Real.log` (reasoned, not run) — no hit: no mathlib lemma bounds a Galois-character prime sum by `log(1/(s−1))`
[C] LeanSearch        "log L-function bounded by sum over primes near s=1" (reasoned) — no hit
[D] Grep mathlib src  via docs: `Mathlib/NumberTheory/LSeries/PrimesInAP` (WebFetch #9) — closest are
                      `vonMangoldt.LSeries_residueClass_eq` / `_lower_bound`; **no** `χ(𝔭)N𝔭^{-s}` log-asymptotic, **no** number-field/Galois version
[E] Name pattern      `log_artinLSeries_*`, `artinLSeries` — n/a: mathlib has **no `artinLSeries`** decl at all (arXiv 2503.00959 confirms Artin L-functions are not in mathlib)

Searched for both:
  - user's current form (one-sided norm bound on a Galois-twisted prime sum) — **not in mathlib**
  - literature-standard form (`log L(χ,s) ~ Σχ N^{-s}`) — **not in mathlib**; mathlib's nearest
    analytic machinery is von-Mangoldt-log-derivative based (`PrimesInAP`), Dirichlet-character
    only, over ℚ — no Artin L-function, no number-field Galois character, no Dedekind-zeta prime-sum
    log-asymptotic of this shape.

Concluded: **not in mathlib** (all methods exhausted, both forms). The *building blocks* of the
proof split into (i) one mathlib lemma — `norm_tsum_le_tsum_norm` (the triangle inequality for
tsums) — and (ii) **project** lemmas (`primeIdealZetaSum_le_log_plus_bounded`,
`primeIdealZetaSum_le_of_subset`, `summable_prime_absNorm_rpow`), plus `Complex.norm_natCast_cpow_of_pos`
and `Complex.norm_eq_one_of_pow_eq_one` from mathlib.

## Call sites — `Chebotarev.log_artinLSeries_asymp_character_sum`

Internal use count: **0** (within the project, excluding the declaring file).
External-to-file callers: **0 distinct files**.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none) | grep over `projects/**/*.lean` minus `Cyclotomic.lean:96` returned **zero** uses |

Inline-derivation grep: the analytic skeleton (`norm_tsum_le_tsum_norm` → `|χ|=1` rewrite →
`primeIdealZetaSum_le_of_subset` → `primeIdealZetaSum_le_log_plus_bounded`) recurs in spirit in the
sibling sub-lemmas of the same file (e.g. `primeIdealZetaSum_frobeniusFibre_asymp` at
`Cyclotomic.lean:898`, and the `isBigO` chain in `ZetaProduct.lean:2180–2314`). So the pattern is
re-used, but *this exact lemma object* is not yet wired into the final
`cyclotomic_density_from_two_sided_asymp` (`Cyclotomic.lean:962`) — it is a **freshly-decomposed,
not-yet-consumed** step (consistent with `chebotarev_cyclotomic` still being assembled). Step-8 of
`/overview` should re-confirm it is wired in before any cleanup deletes it as dead.

What the call-sites pattern tells us: K = 0 internal uses with the equivalent re-derived nearby ⇒
strong NO-composable signal (it is a wrapper the sibling steps bypass / will bypass), tempered by
"brand-new, proof still under construction" (BORDERLINE-junk axis) — but the mathlib-ability verdict
does not hinge on this: even fully wired, the lemma is project-glue, not mathlib material.

## Composition check (Phase 6)

Can the statement be derived in ≤3 chained **mathlib** calls? **No** — and that is the wrong
question, because the decisive dependency is a *project* lemma, not mathlib.

Attempt 1 (the actual proof skeleton, abbreviated):
```
‖Σ' 𝔭, χ(Frob 𝔭)·N𝔭^{-s}‖
  ≤ Σ' 𝔭, ‖χ(Frob 𝔭)·N𝔭^{-s}‖        -- norm_tsum_le_tsum_norm        [MATHLIB]
  = Σ' 𝔭, N𝔭^{-s}                      -- |χ(c.out)|=1, norm_mul, cpow  [MATHLIB + project |χ|=1]
  ≤ primeIdealZetaSum univ s           -- primeIdealZetaSum_le_of_subset [PROJECT]
  ≤ log(1/(s−1)) + C                   -- primeIdealZetaSum_le_log_plus_bounded [PROJECT]
```
- Mathlib decls used: `norm_tsum_le_tsum_norm`, `Complex.norm_natCast_cpow_of_pos`,
  `Complex.norm_eq_one_of_pow_eq_one`, `norm_mul`.
- Project decls used (load-bearing): `primeIdealZetaSum_le_of_subset`,
  `primeIdealZetaSum_le_log_plus_bounded`, `summable_prime_absNorm_rpow` (+ reindexing of the
  `UnramifiedIn` subtype, ~30 lines of summability plumbing).
- Result: **succeeds as a composition, but the dominant term `≤ log(1/(s−1)) + C` is supplied by a
  PROJECT lemma** (which itself encapsulates Sharifi 7.1.12, the Dedekind-zeta-pole analysis —
  genuinely deep, also not in mathlib). So it is **not** a "mathlib building blocks" composition.

Conclusion: **NOT-COMPOSABLE-FROM-MATHLIB-ALONE** — the only mathlib content is the trivial
triangle-inequality step `‖Σ χ·a‖ ≤ Σ ‖a‖ = Σ‖a‖` (one `norm_tsum_le_tsum_norm` call given
`|χ|=1`); everything that gives the statement its value (the `log(1/(s−1))` majorant) is
project-internal and itself absent from mathlib.

## Verdict: `Chebotarev.log_artinLSeries_asymp_character_sum`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the textbook object is `log L(χ,s) ~ Σχ N^{-s}`; the Lean lemma is a
  strictly weaker one-sided norm majorant that no source states standalone — it is an internal step.
- Generality analysis (Phase 4): STRICTLY NARROWER than standard *and* hyper-project-specific; the
  only modern-idiom move (`IsBigO`) is cosmetic project refactoring, not a mathlib lever (Phase 4c = no).
- Mathlib search (Phase 5): not in mathlib in either form; mathlib has **no `artinLSeries`**, no
  Galois-character prime-sum log-asymptotic; nearest is von-Mangoldt `PrimesInAP` (Dirichlet/ℚ only).
- Composition check (Phase 6): the sole mathlib ingredient is the trivial `norm_tsum_le_tsum_norm`
  triangle step; the load-bearing `log(1/(s−1))` bound is the **project** lemma
  `primeIdealZetaSum_le_log_plus_bounded` (Sharifi 7.1.12), not mathlib.

**Rationale:**

This declaration is **project glue for the cyclotomic Chebotarev proof, not a mathlib candidate**.
Every object in its type is bespoke to the Chebotarev project — `galoisCharacter K L`,
`frobeniusClass`, `UnramifiedIn`, `Ideal.absNorm`-based `primeIdealZetaSum` — and its conclusion is a
crude one-sided majorant (`‖twisted prime sum‖ ≤ C·log(1/(s−1)) + C`) that no reference states as a
theorem in its own right; the textbook statement it is *named* after (`log L(χ,s) ~ Σ_𝔭 χ(𝔭)N𝔭^{-s}`,
Sharifi 7.2.1 step (ii)) is mathematically stronger and does not even appear in the Lean type (the
L-function is absent). The genuinely mathlib-relevant content is a single trivial step: given a
unit-modulus character, `‖Σ' χ(c)·a_𝔭‖ ≤ Σ' ‖a_𝔭‖ = Σ' |a_𝔭|`, which is exactly
`norm_tsum_le_tsum_norm` composed with `|χ| = 1`. Everything that makes the inequality *useful* — the
majorisation by `log(1/(s−1))` — is delivered by the project's own
`primeIdealZetaSum_le_log_plus_bounded` (an encapsulation of Sharifi 7.1.12, the Dedekind-zeta
pole-order analysis), which is itself not in mathlib and is itself project-internal. So the lemma is
neither "mathlib has it" (it does not), nor "add it to mathlib" (it is unstateable in mathlib without
importing the whole project's Chebotarev apparatus), nor "compose from mathlib primitives" in the pure
sense — the honest classification is that it is a **1-mathlib-call (`norm_tsum_le_tsum_norm`) + project
lemma composition** that should live, and already lives correctly, *inside the project* and be inlined
at the one site that needs it. With zero current call sites and the equivalent skeleton re-derived in
sibling sub-lemmas, there is no API pressure to keep it as a named standalone even within the project.

**WHY not (NO-composable-from-mathlib — refactor-actionable):**
Mathlib supplies exactly **one** building block: `norm_tsum_le_tsum_norm`
(`Mathlib/Analysis/Normed/.../tsum`), the triangle inequality for `tsum`. The remaining content is
project-internal (`primeIdealZetaSum_le_log_plus_bounded`, `primeIdealZetaSum_le_of_subset`,
`summable_prime_absNorm_rpow`) and itself not mathlib material (it encodes the Dedekind-zeta pole
analysis specific to this development). There is **no mathlib gap to fill** — mathlib is not missing a
"Galois character prime sum is `O(log(1/(s−1)))`" lemma any more than it is missing every other
intermediate inequality of a particular L-function proof.

Mathlib building blocks: `norm_tsum_le_tsum_norm`; (supporting) `Complex.norm_natCast_cpow_of_pos`,
`Complex.norm_eq_one_of_pow_eq_one`, `norm_mul`.
Composition sketch (the mathlib-only part, ≤3 lines):
```lean
-- given hsum : Summable (‖χ(Frob 𝔭)·N𝔭^{-s}‖) and |χ(c.out)| = 1:
‖∑' 𝔭, χ (frobeniusClass K L 𝔭.1).out * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s:ℂ))‖
  ≤ ∑' 𝔭, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)        -- norm_tsum_le_tsum_norm + norm_mul + |χ|=1
-- then the project lemma takes over: ≤ primeIdealZetaSum univ s ≤ log(1/(s−1)) + C
```
Call sites in the project (Phase 6.0): **K = 0**.
Refactor plan:
1. **Do not upstream.** Mark/keep as a private project sub-lemma; it is not a mathlib contribution.
2. If/when wired into `cyclotomic_density_from_two_sided_asymp`, leave it as the named project step
   (the prose decomposition (i)–(iv) justifies the name *within the project*), OR inline the four-step
   skeleton at that single call site.
3. **Rename for honesty (project cleanup ticket, not mathlib):** `..._asymp_character_sum` →
   e.g. `norm_character_primeSum_le_log` — the lemma is a one-sided `‖·‖ ≤ …` bound, not an `asymp`
   (no `IsBigO`/`Tendsto`/`~` in the type). Optionally restate via `=O[𝓝[>]1]` to match the project's
   own `sum_galoisCharacterCoeff_isBigO` style (`ZetaProduct.lean:2180`). Both are *project* refactors.
4. Drop the unused `[IsMulCommutative Gal(L/K)]` hypothesis (Phase 4 row 2) — cosmetic.

Next action: keep inside the project (private/internal sub-lemma); no mathlib PR. Optional project
cleanup ticket: rename to reflect the bound (not "asymp"), drop the unused commutativity hypothesis,
and confirm via `/overview` Step 8 that it is wired into the density proof (else it is dead code).

---

## Next step

Keep `Chebotarev.log_artinLSeries_asymp_character_sum` inside the project as an internal sub-lemma
of `chebotarev_cyclotomic`; it is **not** a mathlib candidate. The only mathlib-relevant nugget is the
one-line `norm_tsum_le_tsum_norm` triangle step; the substantive `log(1/(s−1))` bound is the project's
own `primeIdealZetaSum_le_log_plus_bounded`. File a project cleanup ticket to (a) rename away from
"asymp" (the type is a one-sided `‖·‖ ≤ …` bound, optionally an `=O[𝓝[>]1]` to match the project's
existing `isBigO` lemmas), (b) drop the unused `[IsMulCommutative]`, and (c) verify it is actually
consumed downstream.
