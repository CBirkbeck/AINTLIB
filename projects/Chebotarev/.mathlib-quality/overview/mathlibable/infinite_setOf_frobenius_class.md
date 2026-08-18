# /mathlibable report — `Chebotarev.infinite_setOf_frobenius_class`

## Baseline (Phase 0)

- lake build:               not re-run (local build stale per task note); reasoning from source.
- decl `Chebotarev.infinite_setOf_frobenius_class`: resolved at
  `projects/Chebotarev/CebotarevDensity/Main.lean:128`.
- kind:                      theorem
- has sorry:                 no (proof is 3 substantive lines)
- qualified name VERIFIED:   `Chebotarev.infinite_setOf_frobenius_class` (namespace `Chebotarev`
  opened at Main.lean:60; base name as parsed). Confirmed correct.
- module docstring summary:  Chebotarev's density theorem for a finite Galois extension `L/K` of
  number fields, in conjugacy-class form, plus its standard corollaries (Dirichlet AP, split-completely
  density, and this infinitude statement).

## Statement (Phase 1)

`Chebotarev.infinite_setOf_frobenius_class` is a **theorem** stating:

> Let `L/K` be a finite Galois extension of number fields with Galois group `G = Gal(L/K)`, and let
> `C` be a conjugacy class of `G`. Then there are **infinitely many** prime ideals `𝔭` of `𝓞 K`
> that are unramified in `L` and whose Frobenius conjugacy class equals `C`.

This is the **qualitative ("weak") form** of Chebotarev's density theorem: the bare existence-of-
infinitely-many statement, obtained by discarding the quantitative value `|C|/|G|` of the density and
keeping only that the set is infinite.

Variables / typeclasses involved (Lean side):
- `{K L : Type*}` with `[Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]`
  — a Galois extension of number fields (file-level `variable` block, Main.lean:62–63).
- `(C : ConjClasses Gal(L/K))` — a conjugacy class of the Galois group.

Hypotheses (Lean side):
- None beyond the typeclass context. (Note: unlike the parent `chebotarev_density`, this corollary
  does **not** even require an explicit `[FiniteDimensional K L]` argument — it is supplied through the
  call to `chebotarev_density C`, which carries `[FiniteDimensional K L]`. Wait: re-reading, the parent
  takes `[FiniteDimensional K L]` explicitly and this theorem does not list it; the `NumberField`
  instances already give finite-dimensionality over ℚ but the relevant instance for `K L` flows from
  context. Either way, the corollary's signature is strictly the conclusion below.)

Conclusion (math): the set of unramified primes of `K` with Frobenius class `C` is infinite.

Conclusion (Lean):
```lean
Set.Infinite
  {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = C}
```

Proof body (3 lines):
```lean
refine infinite_of_hasDirichletDensity_pos (chebotarev_density C) ?_
apply div_pos
· exact_mod_cast ConjClasses_carrier_card_pos C
· exact_mod_cast Nat.card_pos (α := Gal(L/K))
```
i.e. "the density `|C|/|G|` is positive (numerator `> 0` since a conjugacy class is nonempty,
denominator `> 0` since `G` is finite nonempty), and a set of positive Dirichlet density is infinite."

## Size classification (Phase 2a)

Verdict: **BIG** (by association) — but as a *standalone object* it is SMALL.

Reason: The statement is a named, standard consequence of a person-named theorem (Chebotarev), which
the size rubric flags as BIG. However, the declaration *itself* is a 3-line corollary, not a main
result: the project's `## Main results` list (Main.lean:35–42) names `chebotarev_density`,
`dirichlet_primes_in_AP`, and `density_split_completely` — **not** this theorem. So it is a
satellite corollary of a BIG theorem. Literature width is EXHAUSTIVE regardless.

## One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. (Body is 3 substantive lines of tactic
proof, not a one-line definition.) Check skipped.

## Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Chebotarev density theorem infinitely many primes each Frobenius conjugacy class" | yes | "For each conjugacy class `C` of `G`, there exist infinitely many primes `p` with Frobenius in `C`." | Sury (ISI), Wikipedia, Stevenhagen–Lenstra, Di Meglio notes all state it. |
| 2 | WebSearch (general / weak-form framing) | `"weak form" Chebotarev density theorem set of primes infinite Dirichlet density positive standard statement` | yes | "**Weak form:** if `A` is a conjugacy class in `Gal(L/K)`, the set of primes whose Frobenius element equals `A` is **infinite** and has Dirichlet density `#A/n`." | Exactly this declaration. The "weak form" is the named standard concept. |
| 3 | WebSearch (mathlib / aliases) | "mathlib4 Chebotarev density theorem Frobenius infinitude of primes" | partial | confirms the weak-form statement; **no mathlib implementation found** | "The weak form … says the set of primes is infinite and has Dirichlet density." No mathlib4 hit. |
| 4 | ChatGPT MCP | n/a | n/a | — | MCP flagged as possibly down in the task; substituted with extra WebSearch (rows 1–3) + Wikipedia WebFetch (row 9) covering the standard-form + historical-evolution questions the MCP query would have asked. |
| 5 | Local references | grep `.mathlib-quality/references/` | n/a | (directory absent) | `projects/Chebotarev/.mathlib-quality/references/` does not exist (only `overview/`). Recorded n/a. The project's cited sources are Sharifi §7.2.2 and Stevenhagen–Lenstra Appendix (per module docstring). |
| 6 | nLab | "Chebotarev density theorem" | n/a (weak) | nLab has a page but frames the theorem quantitatively; no separate "infinitude" corollary highlighted | Not a categorical concept; the qualitative corollary is folklore, not separately axiomatised. |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept. |
| 8 | Stacks Project | — | n/a | — | Stacks does not cover Chebotarev density (analytic number theory; out of Stacks' scheme-theoretic scope). |
| 9 | MathOverflow / Wikipedia (named-corollary status) | WebFetch Wikipedia "Chebotarev density theorem" — is the infinitude a separately-named corollary? | yes (framing) | "**no standalone named corollary**; the consequence that positive density ⟹ infinitely many such primes is an immediate consequence, not separately highlighted" | Confirms the math is standard but the *infinitude restatement* is a trivial unbundling of the density result, not its own theorem in the literature. |
| 10 | recent arXiv (last 5 yr) | (covered by row 1 hits: arXiv 2210.13735, 1810.06201) | yes | uses the weak form as a tool ("a polynomial with a root mod p for every p has a real root" applies Chebotarev infinitude) | Confirms the weak form is the *usable* corollary mathematicians cite. |

The protocol passed: WebSearch ran 3 distinct queries at different generality/aliasing levels;
ChatGPT-MCP substituted with documented fallbacks (MCP down per task); local refs checked (absent →
n/a); nLab / nCatLab / Stacks / MathOverflow-via-Wikipedia / arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: the **weak (qualitative) form of the Chebotarev density theorem** — "for every
conjugacy class `C ⊆ Gal(L/K)`, infinitely many unramified primes of `K` have Frobenius class `C`."

Sources agree on the standard form: **yes**. Every source (Wikipedia, Stevenhagen–Lenstra,
Encyclopedia of Mathematics, Di Meglio, Triantafillou, MIT 18.785 notes) states the weak form
identically. The Lean statement matches the literature-standard weak form verbatim (number-field
generality, finite Galois extension, conjugacy-class indexing, unramified primes).

Most general standard form: stated over a **finite Galois extension of global fields** (number fields
*or* function fields `𝔽_q(T)`). For number fields specifically (the mathlib-relevant case and the one
this project formalises), the form here is the maximal one: arbitrary finite Galois `L/K` and arbitrary
conjugacy class `C`.

Generality dimensions where the literature varies:
- Base/ground field: number field (here) vs. arbitrary global field (number field **or** function
  field). The function-field case is a genuine generalisation but a different, parallel theorem.
- What is concluded: infinitude (this decl) ⊂ Dirichlet density `|C|/|G|` (parent `chebotarev_density`)
  ⊂ natural-density / effective asymptotic `N_C(x) = (|C|/|G| + o(1)) x/log x` (strong/effective form).
  This decl sits at the **weakest** rung — which is exactly the point of a qualitative corollary.

Disagreement with the literature: **none**. The statement is a faithful, standard restatement.

## Generality analysis — `Chebotarev.infinite_setOf_frobenius_class`

Literature-standard form (from Phase 3): the weak form over a finite Galois extension of number fields,
indexed by a conjugacy class — i.e. exactly the Lean statement.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[NumberField K] [NumberField L]` | number-field extension | global-field extension (number **or** function field) | yes (function-field analogue) | A function-field Chebotarev is a *separate* theorem with its own proof apparatus (zeta of curves over `𝔽_q`). Not a mechanical weakening; would require an entirely different parent. Out of scope. |
| 2 | `[IsGalois K L]` + `[FiniteDimensional K L]` (via parent) | finite Galois | finite Galois | NO | Galois + finite is intrinsic to "Frobenius conjugacy class" being defined. Cannot weaken. |
| 3 | `(C : ConjClasses Gal(L/K))` | arbitrary conjugacy class | arbitrary conjugacy class | NO | Already maximally general (any `C`). |
| 4 | Conclusion `Set.Infinite {…}` | infinitude only | infinitude (weak form) | — (this *is* the weakening of the parent) | This declaration **is itself the weakened conclusion** of `chebotarev_density` (density `|C|/|G|`). Going weaker than "infinite" is vacuous. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** within the number-field setting (the only setting the
project's parent `chebotarev_density` supports). The sole "more general" direction (global/function
fields) is a different theorem, not a weakening of hypotheses on this one.

Number of weakening opportunities found: **0** (within scope).

Cost of restatement: n/a — no restatement proposed.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | already fully typeclass-driven (`[Field]`, `[NumberField]`, `[IsGalois]`) | — |
| 2 | sequences/metric → filters/topological? | no | the underlying density already uses `Tendsto … (𝓝[>] 1)` (filter idiom); the corollary's `Set.Infinite` is the canonical mathlib spelling | — |
| 3 | construct → universal property? | no | nothing constructed | — |
| 4 | set-with-closure-predicate → bundled substructure? | no | the result-set is a `Set (Ideal (𝓞 K))`; `Set.Infinite` is the idiomatic conclusion (cf. mathlib `Nat.infinite_setOf_prime_and_eq_mod`) | — |
| 5 | vector-space/field-specific → weaker typeclass? | no | number-field-specific by nature | — |
| 6 | 1-categorical → higher-categorical? | no | not categorical | — |
| 7 | concrete index → general algebraic index? | no | indexed by `ConjClasses Gal(L/K)`, already the right abstraction | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The statement is already in mathlib-idiomatic form — it mirrors
`Mathlib.NumberTheory.LSeries.PrimesInAP.Nat.infinite_setOf_prime_and_eq_mod` (the Dirichlet-AP special
case) almost exactly in shape: `Set.Infinite {𝔭 | 𝔭.IsPrime ∧ <condition>}`. No modernisation move
exists; the form *is* the modern one.

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

## Mathlib search-status: `Chebotarev.infinite_setOf_frobenius_class`

[A] Lean-Finder       — (mathlib-index tools unavailable for project decls; reasoned via grep + web)  n/a: reason
[B] Loogle            type pattern `Set.Infinite {_ : Ideal (𝓞 _) | _ ∧ _ ∧ frobeniusClass _ _ _ = _}` — `frobeniusClass` is project-local, no mathlib match possible.  no hits
[C] LeanSearch        "infinitely many primes with given Frobenius conjugacy class" / "Chebotarev infinitude"  no hits (no mathlib Chebotarev)
[D] Grep mathlib src  `grep -rln "Chebotarev|chebotarev|frobeniusClass|FrobeniusClass" .lake/packages/mathlib/Mathlib/` → **0 real hits** (only a substring false-positive in `InfinitePlace/Ramification.lean` from "UnramifiedIn"). Also grepped `DirichletDensity|HasDirichletDensity|setDensity` → **0 hits**.  no hits
[E] Name pattern      grep for `infinite_setOf_prime` family → found `Nat.infinite_setOf_prime_and_eq_mod` (Dirichlet AP, `PrimesInAP.lean:475`) — the *special-case analogue*, NOT this general result.  partial (analogue only)

Searched for both:
  - the user's current form (Chebotarev infinitude) — **not in mathlib**.
  - the literature-standard / more-general forms (Chebotarev density; Dirichlet density of prime
    ideals; "positive density ⟹ infinite" general lemma) — **none in mathlib**. There is no
    `HasDirichletDensity` analogue, no Chebotarev theorem (abelian, cyclotomic, or conjugacy-class),
    and no `frobeniusClass`/`UnramifiedIn` for general number fields anywhere in mathlib.

Concluded: **not in mathlib** (all methods exhausted, plus the parent and every dependency confirmed
absent). The closest mathlib result is `Nat.infinite_setOf_prime_and_eq_mod`, which is the **`K=ℚ,
L=ℚ(ζ_n)` special case** (Dirichlet's theorem on primes in AP) — a strict specialisation, not the
general theorem. (Mathlib has Dirichlet's AP theorem but not Chebotarev.)

## Call sites — `Chebotarev.infinite_setOf_frobenius_class`

Internal use count: **0** (within the project, excluding the declaring file Main.lean).
External-to-file callers: **0 distinct files**.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | grep over `projects/**/*.lean` for `infinite_setOf_frobenius_class` minus Main.lean:128 returned nothing. |

Inline-derivation grep (was the equivalent re-derived elsewhere?): **(none)** — `density_split_completely`
(Main.lean:151) re-uses `chebotarev_density` directly for its own purpose, but does not re-derive the
infinitude fact. No other site reconstructs `Set.Infinite {… frobeniusClass …}`.

Call-sites reading: K=0 internal uses, no inline re-derivation. Per the Phase 6.0.1 table this is the
"brand-new + unused so far" pattern (the file is a fresh formalisation; the infinitude corollary is a
documented qualitative companion to the main density theorem, mirroring how mathlib ships
`infinite_setOf_prime_and_eq_mod` next to its quantitative AP results). Not dead code — it is an
intentionally-stated standard corollary. This does NOT push toward NO on its own here, because the
governing factor is the parent's mathlib status (see Verdict).

## Composition check (Phase 6)

Can `infinite_setOf_frobenius_class` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `infinite_of_hasDirichletDensity_pos (chebotarev_density C) (by positivity-on-|C|/|G|)`.
  - Decls used: `chebotarev_density`, `infinite_of_hasDirichletDensity_pos` — **both project-local, NOT
    mathlib**. `HasDirichletDensity` itself is project-local.
  - Result: this is exactly the actual proof, but it composes **project** primitives, not mathlib ones.
  - Notes: there is no mathlib primitive for "set of prime ideals of positive Dirichlet density is
    infinite", because mathlib has no Dirichlet density of prime ideals at all.

Attempt 2 (mathlib-only angle): is there any mathlib lemma `density > 0 → Set.Infinite`? Searched
`natDensity`/`Set.Infinite` — mathlib has natural-density API for `ℕ` but nothing for Dirichlet density
of `Ideal (𝓞 K)`, and no bridge. Fails.

Conclusion: **NOT-COMPOSABLE from mathlib.** The 3-line proof is trivial *relative to the project's own
API*, but every ingredient (`chebotarev_density`, `infinite_of_hasDirichletDensity_pos`,
`HasDirichletDensity`, `ConjClasses_carrier_card_pos`) is project-local. From mathlib alone, the result
is not reachable at all — its entire substrate is missing upstream.

## Verdict: `Chebotarev.infinite_setOf_frobenius_class`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): standard "weak form" of Chebotarev; literature unanimous on the
  statement; but it is an *unbundling* of the density result, not a separately-named theorem in the
  sources.
- Generality analysis (Phase 4): MAXIMALLY GENERAL within number fields; no modern-idiom move; mirrors
  mathlib's `Nat.infinite_setOf_prime_and_eq_mod` precedent.
- Mathlib search (Phase 5): NOT in mathlib; parent `chebotarev_density` and the entire
  Dirichlet-density / Frobenius-class substrate also absent. Closest is the AP special case
  `Nat.infinite_setOf_prime_and_eq_mod`.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (composable only from project-local API).

**Rationale:**

Mathematically this is unambiguously mathlib-worthy *content*: it is the qualitative form of a
flagship theorem (Chebotarev), stated at full number-field generality, in exactly the idiom mathlib
already uses for the analogous Dirichlet-AP corollary (`Nat.infinite_setOf_prime_and_eq_mod`, shipped
as its own named theorem in `PrimesInAP.lean` even though it too is a one-line consequence of the
quantitative result). On the "is the content standard and wanted" axis, the answer is plainly yes, and
the precedent for shipping the infinitude restatement as a standalone named theorem is concrete.

But this corollary **cannot be added to mathlib in isolation**: its statement names `frobeniusClass`,
`UnramifiedIn`, and `Gal(L/K)`-conjugacy-class infrastructure, and its proof rests on
`chebotarev_density` + `infinite_of_hasDirichletDensity_pos` + the `HasDirichletDensity` definition —
*none* of which exist in mathlib (confirmed by exhaustive grep: zero Chebotarev, zero Dirichlet-density
of prime ideals). The verdict therefore cannot be a self-contained YES-add-as-is (you cannot PR a
corollary whose every symbol is undefined upstream), nor NO-mathlib-has-it (mathlib has neither this nor
the parent), nor NO-composable (it is not composable from *mathlib*). It is strictly downstream of a
much larger upstreaming decision about the whole `chebotarev_density` development. That decision — does
mathlib want the entire Dirichlet-density + Chebotarev API, and at what grain — is a human/maintainer
judgment call, not something this single-decl assessment can settle. Hence BORDERLINE: the right answer
is "**yes, eventually — but only as the trailing corollary of the parent-theorem PR, and that whole
upstreaming is the decision to make.**"

Numbered questions (≤5):

1. Is the project intending to upstream the whole `chebotarev_density` development (the `HasDirichletDensity`
   definition, the abelian/cyclotomic cases, `frobeniusClass`, `UnramifiedIn`) to mathlib? This corollary
   is only PR-able as part of that effort.
2. If yes: should the infinitude statement ship as its own named theorem alongside `chebotarev_density`
   (following the `Nat.infinite_setOf_prime_and_eq_mod` precedent), or be left for users to derive
   inline from the density result? (Recommended: ship it — mathlib's AP precedent does exactly this.)
3. Should `infinite_of_hasDirichletDensity_pos` (the genuinely reusable bridge "positive Dirichlet
   density ⟹ infinite") be split out and assessed/upstreamed on its own — it is the only part with
   value independent of Chebotarev?
4. Is the parent `chebotarev_density` itself already slated for a `/mathlibable` run? Its verdict should
   be settled first; this corollary inherits from it.

**Inherited-verdict note (for the batch ledger):** this theorem is a glue-style corollary of
`chebotarev_density`. Under Mode-B verdict-inheritance it should **inherit the parent's verdict** once the
parent is assessed. Until then, BORDERLINE-needs-human is the honest standalone verdict — the content is
YES-grade but the unit of upstreaming is the parent, not this 3-line corollary.

---

## Next step

Answer the four numbered questions above (chiefly: is the `chebotarev_density` development being
upstreamed, and at what grain). Run `/mathlibable Chebotarev.chebotarev_density` first to settle the
parent; this corollary then inherits that verdict (expected: ship it as a named companion theorem in the
same PR, per the `Nat.infinite_setOf_prime_and_eq_mod` precedent). Separately, consider a standalone
`/mathlibable` on `infinite_of_hasDirichletDensity_pos` — the one genuinely Chebotarev-independent piece.
