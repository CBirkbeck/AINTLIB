# /mathlibable report — `Chebotarev.chebotarev_cyclotomic_lowerDensity_ge`

## Verdict: **NO-composable-from-mathlib**

One-line: a one-liner `.hasLower` wrapper extracting the liminf-form from the
parent full-density theorem; K=0 uses (the one consumer inlines it); ≤1-call.

---

### Baseline (Phase 0)

- lake build:               not run — Chebotarev project's own mathlib checkout is absent locally (build stale per task note). Reasoned from source; the statement elaborates as written, every referenced decl resolves in-file/in-project. A sibling mathlib checkout (`LeanModularForms`, commit `747d81a`, 2025-10-27) was used for the authoritative mathlib grep.
- decl `Chebotarev.chebotarev_cyclotomic_lowerDensity_ge`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/Cyclotomic.lean:994`
- qualified name:           **`Chebotarev.chebotarev_cyclotomic_lowerDensity_ge`** (namespace `Chebotarev`, opened at Cyclotomic.lean:49 `namespace Chebotarev`, closed at :1003 `end Chebotarev`; the task's parse `Chebotarev.chebotarev_cyclotomic_lowerDensity_ge` is CONFIRMED — not a guess)
- kind:                     theorem
- has sorry:                no
- module docstring summary: Chebotarev's theorem, cyclotomic case (Sharifi §7.2.1) — file develops the density `1/|Gal(L/K)|` of primes of `𝓞 K` unramified in `K(μ_m)` with Frobenius `= σ`.

---

### Statement (Phase 1)

`Chebotarev.chebotarev_cyclotomic_lowerDensity_ge` is a **theorem** stating:

> Under the hypotheses of the cyclotomic Chebotarev theorem (`K` a number field,
> `m ≥ 1`, `L = K(μ_m)` cyclotomic Galois over `K`, `m % 4 ≠ 2`, `σ ∈ Gal(L/K)`),
> the set of primes `𝔭` of `𝓞 K` unramified in `L` with Frobenius class `[σ]`
> has **lower** Dirichlet density `1/|Gal(L/K)|`.

Crucially, `HasLowerDirichletDensity S δ` (Density.lean:89) is defined as
`liminf (s ↦ ζ_S(s)/ζ_univ(s)) (𝓝[>] 1) = δ` — an **equality** of the liminf
with `δ`, NOT a `≥` inequality. So despite the name suffix `_ge`, the statement
is "the lower density *equals* `1/|G|`", which is exactly the liminf-component
of the full-density statement.

The body is a single projection:
`(chebotarev_cyclotomic K L m hm σ).hasLower`, where
`HasDirichletDensity.hasLower` (Density.lean:241) is itself `h.liminf_eq` —
the standard `Tendsto … (𝓝 δ) → liminf … = δ` extraction.

Variables / typeclasses (Lean side):
- `K L : Type*`, `[Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]` — file-level `variable`s.
- `m : ℕ`, `[NeZero m]`, `[IsCyclotomicExtension {m} K L]` — `L = K(μ_m)`.
- `(hm : m % 4 ≠ 2)` — normalisation excluding the `m ≡ 2 (4)` degenerate corner.
- `(σ : Gal(L/K))`.

Hypotheses (Lean side): all carried by the parent `chebotarev_cyclotomic`; this
wrapper adds none.

Conclusion (math): lower Dirichlet density of the Frobenius-`σ` primes `= 1/|G|`.
Conclusion (Lean): `HasLowerDirichletDensity {𝔭 | …} ((Nat.card Gal(L/K) : ℝ)⁻¹)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a corollary/variant of the main result, body is one `.hasLower`
projection; not itself a `## Main results` deliverable (the file's deliverable
is `chebotarev_cyclotomic` at :982, and `Main.lean`'s top-level theorems).
(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`(chebotarev_cyclotomic K L m hm σ).hasLower`).
One-liner verdict: **n/a — kind is theorem, not def.** The one-line *definition*
rule (defeq/diamond/API-stability exemptions) applies to `def`/`abbrev`/`structure`,
not to theorems. Recorded as a one-line note: this is a one-line *proof term*, a
strong "thin wrapper" signal that feeds Phase 6, but the def-specific exemption
table does not apply.

Conclusion: n/a (theorem). Carried into Phase 6 as a thin-wrapper signal.

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Chebotarev density theorem lower Dirichlet density liminf prime ideals Frobenius"     | yes  | weak Chebotarev: primes with Frobenius in conj. class `A` have Dirichlet density `#A/n` (full limit) | Wikipedia, Stevenhagen–Lenstra, Encyclopedia of Math — all state the **full** density, not a one-sided liminf theorem |
|  2 | WebSearch (general form / defn)  | `"natural density" OR "Dirichlet density" lower density liminf definition analytic number theory` | yes | lower/upper density = liminf/limsup of the ratio; full density exists iff they coincide | Wikipedia "Dirichlet density", Kedlaya 18.785 notes — lower density is the standard *definitional* liminf; not a named theorem |
|  3 | WebSearch (mathlib / formalised) | "mathlib4 Chebotarev density theorem formalization Dirichlet density"                  | no   | — | no mathlib formalisation of Chebotarev or prime density surfaced |
|  4 | WebSearch (nLab proxy)           | `nLab Dirichlet density OR "analytic density" primes definition`                      | yes  | δ(S) via lim_{z→1+} of (Σ_{p∈S} p^{-z})/log(1/(z-1)); natural⇒Dirichlet, equal when both exist | HandWiki/Wikipedia mirror; nLab has no dedicated stronger page. Confirms lower density = liminf is purely definitional |
|  5 | ChatGPT MCP                      | "is the lower-density (liminf) form a named theorem or a trivial extraction; does mathlib have prime density / Chebotarev?" | n/a  | — | **MCP DOWN** — Codex backend errored on both attempts (`Codex failed: Command failed`), exactly the fallback the task warned about. Compensated with extra WebSearch channels (#1,#2,#4,#6) + direct mathlib grep (Phase 5 [D]). |
|  6 | Stacks Project (if alg geom)     | "Stacks project Dirichlet density Chebotarev OR Frobenius primes"                      | n/a  | — | Stacks covers étale-cohomological Chebotarev variants but has no "lower Dirichlet density" theorem distinct from the full density; not the relevant channel for this analytic statement |
|  7 | nCatLab (if categorical)         | —                                                                                     | n/a  | — | not a categorical concept (analytic density of primes) |
|  8 | MathOverflow / MSE               | covered by #1–#2 result sets (Grokipedia/encyclopedia hits)                            | n/a  | — | no MO thread treats "lower Chebotarev density" as a separate result; it is the liminf half of the standard statement |
|  9 | arXiv (last 5y)                  | surfaced in #1/#3 (arXiv:2210.13412 "supplement to Chebotarev", arXiv:1210.3571 "twisted Chebotarev") | yes (tangential) | effective/explicit & twisted Chebotarev | These strengthen/refine the **full** density (error terms, twists); none isolates a "lower-density-only" named theorem |

Protocol pass check:
- WebSearch ≥3 distinct generality levels: ✓ (#1 specific, #2 most-general definitional, #3/#4 aliases/formalised).
- ChatGPT MCP ≥1 query asking standard form + generality + history: attempted twice, **backend down** — documented; extra channels substituted.
- Local references checked: **n/a** — `projects/Chebotarev/.mathlib-quality/references/` absent and `refs/` absent (repo went public; PDFs/refs purged per MEMORY). The companion `chebotarev_cyclotomic.md` report cites Sharifi §7.2.1 and Stevenhagen–Lenstra for the parent; same sources apply.
- nLab checked: ✓ (#4).
- Stacks / nCatLab / MO / arXiv: each checked or `n/a` with reason (#6–#9).

### Literature summary (Phase 3)

Concept identified as: **lower Dirichlet density** (= liminf of the partial-zeta
ratio) **of the Frobenius-fibre primes** in the cyclotomic Chebotarev theorem.

Sources agree on the standard form: **yes** — the weak Chebotarev theorem asserts
the *full* Dirichlet density `#A/[L:K]` (here `1/|G|`, a singleton class). "Lower
density" is the textbook liminf half of the density definition (Wikipedia
"Dirichlet density", Kedlaya 18.785); it is **not** an independently-named theorem.

Most general standard form: the full-density statement (`lim = #A/n`). The
liminf-equals-`δ` form is strictly weaker and follows trivially from it (a
convergent net's liminf equals its limit).

Generality dimensions where the literature varies:
  - notion of density (Dirichlet vs natural): natural ⇒ Dirichlet; for Chebotarev the natural density also holds, so the full Dirichlet density is the standard packaging — strictly stronger than this liminf form.
  - one-sided vs two-sided: the literature states two-sided (the limit); one-sided liminf is a derived convenience, never the headline.

Disagreement with the literature: **none** mathematically, but the literature
treats the lower-density form as a *trivial consequence*, never a result worth
separate naming. The Lean wrapper exists for a downstream proof convenience
(`HasLowerDirichletDensity.mono` chain), not because the math is a distinct theorem.

---

## PHASE 4 — Generality analysis

### Generality analysis — `chebotarev_cyclotomic_lowerDensity_ge`

Literature-standard form (Phase 3): the **full** Dirichlet density `1/|G|`
(`chebotarev_cyclotomic`, Cyclotomic.lean:982). The lower-density form is a
strict weakening of that.

| # | Parameter / hypothesis            | Current Lean form        | Literature-standard form          | Weaker form exists? | Reason |
|---|-----------------------------------|--------------------------|------------------------------------|---------------------|--------|
| 1 | conclusion `HasLowerDirichletDensity … = 1/|G|` | liminf-equals-`δ` | full density (`lim = δ`) — STRONGER | n/a (this *is* the weakening) | The wrapper deliberately drops to the liminf half; the parent already proves the stronger full-limit form |
| 2 | all `K L m σ hm` hypotheses        | inherited verbatim       | identical to parent                | NO | identical to `chebotarev_cyclotomic`; nothing to weaken here that isn't already at the parent |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY WEAKER (not narrower-in-hypotheses but
weaker-in-conclusion) than the standard full-density form** — and the stronger
form already exists in the project as `chebotarev_cyclotomic`.

Number of weakening opportunities (toward more generality): **0** — this
declaration is already a *de-generalisation* (conclusion-weakening) of its
parent. There is nothing to make *more* general; the move that mathlib would
want is the opposite: keep the full-density `chebotarev_cyclotomic` and derive
the liminf form at the call site.

Proposed restatement: **none in the generalise direction.** The relevant action
is removal/inlining (Phase 6/7), not regeneralisation.

Cost of any restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | bundled-hyp → typeclass? | no | already typeclass-driven (parent's instances) | — |
| 2 | sequences → filters? | no | already filter-based (`liminf … (𝓝[>] 1)`, mathlib `Filter.liminf`) | — |
| 3 | construct → universal property? | no | it's a density assertion, no object constructed | — |
| 4 | set+closure → bundled substructure? | no | n/a | — |
| 5 | vector-space/field → module/(semi)ring? | no | the reals here are intrinsic to density | — |
| 6 | 1-categorical → higher? | no | n/a | — |
| 7 | concrete index → general algebra? | no | n/a | — |

Modern-idiom verdict: **no.** The statement is already in mathlib's idiom
(`Filter.liminf` over `𝓝[>] 1`). No modernisation move available — and even if
there were, it would target the parent `chebotarev_cyclotomic`, not this wrapper.

---

## PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional
equalities or typeclass-search paths. Skipped.

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `Chebotarev.chebotarev_cyclotomic_lowerDensity_ge`

Searched against a live mathlib checkout (`LeanModularForms/.lake/packages/mathlib`,
commit `747d81a5`, 2025-10-27) — the Chebotarev project's own mathlib is absent
locally but pins the same daily-bumped mathlib (AINTLIB is one workspace).

[A] Lean-Finder       — (mathlib-index MCP not available in this env)   n/a: tool absent; substituted by direct source grep [D]
[B] Loogle            `HasLowerDirichletDensity`, `liminf _ (𝓝[>] 1) = _`, `Chebotarev`  n/a: loogle MCP not wired here; the *names* don't exist in mathlib (grep [D] is decisive)
[C] LeanSearch        "Dirichlet density of primes", "Chebotarev density theorem"  n/a: tool not wired; WebSearch #3 found no mathlib formalisation
[D] Grep mathlib src  `DirichletDensity|dirichletDensity|analyticDensity|naturalDensity|natDensity|Chebotarev|Cebotarev`  **no hits** anywhere in `Mathlib/`. Also grepped `Mathlib/NumberTheory/**` for `\bdensity\b` → only `Transcendental/Liouville/Residual.lean` (topological residual density of Liouville numbers — unrelated).
[E] Name pattern      `chebotarev_cyclotomic_lowerDensity_ge` / `HasLowerDirichletDensity`  no hits in mathlib (project-local names)

Searched for both:
  - the user's current form (lower Dirichlet density of Frobenius primes) — **not in mathlib**;
  - the literature-standard stronger form (full Chebotarev density) — **not in mathlib** either. The closest mathlib result is `Nat.setOf_prime_and_eq_mod_infinite` / `Nat.forall_exists_prime_gt_and_eq_mod` (`Mathlib/NumberTheory/LSeries/PrimesInAP.lean`), which prove the **infinitude** of primes in an arithmetic progression — Dirichlet's theorem in its existence form, with **no density** statement at all.

Concluded: **not in mathlib** (the literature-standard form and the user's form
are both absent; mathlib has no notion of Dirichlet/analytic/natural density of
primes, and no Chebotarev). The *building blocks* used by this wrapper are
**project-local** (`HasDirichletDensity`, `HasDirichletDensity.hasLower`,
`HasLowerDirichletDensity`), not mathlib.

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `Chebotarev.chebotarev_cyclotomic_lowerDensity_ge`

Internal use count: **0** (within the project, excluding the declaring line).
External-to-file callers: **0 distinct files**.

`grep -rn "chebotarev_cyclotomic_lowerDensity_ge" projects/ --include=*.lean`
returns exactly one line — the declaration itself (Cyclotomic.lean:994).

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | —             |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the wrapper?):
  - **YES — `Abelian.lean:877`**: `have hUlow : HasLowerDirichletDensity (⋃ i ∈ t, S i) … := hUdens.hasLower`. The abelian-case proof builds the lower-density fact it needs by calling `.hasLower` **inline** on a `HasDirichletDensity` term (`hUdens`), feeding `HasLowerDirichletDensity.mono` at :882 — it does **not** route through `chebotarev_cyclotomic_lowerDensity_ge`. This is precisely the "K=0, equivalent re-derived inline" pattern.

> Note on a stale triage record: `…/overview/analysis/07-api-and-junk.md:173`
> lists this decl under "Cross-file Chebotarev spine … (consumed by `Abelian`)".
> The call-site grep **refutes** that: `Abelian` consumes `HasDirichletDensity.hasLower`
> directly, not this wrapper. The decl is unconsumed.

Composability signal (per verdicts table): **K = 0 internal uses, and the same
statement IS re-derived inline at ≥1 site** → "it's a wrapper consumers bypass"
→ verdict leans **NO-composable-from-mathlib** (mathlib has no density notion, so
not NO-mathlib-has-it; the building block is the project's own to-be-upstreamed API).

### Composition check (Phase 6)

Can `chebotarev_cyclotomic_lowerDensity_ge` be derived in ≤3 chained calls?

Attempt 1: `(chebotarev_cyclotomic K L m hm σ).hasLower`
  - Decls used: `Chebotarev.chebotarev_cyclotomic` (the parent, to-be-upstreamed) + `Chebotarev.HasDirichletDensity.hasLower` (project API, = `Filter.Tendsto.liminf_eq`).
  - Result: **succeeds** — this is literally the existing proof body (1 projection call).
  - Notes: `HasDirichletDensity.hasLower` is itself a ≤1-line wrapper of mathlib's `Filter.Tendsto.liminf_eq`. So in pure-mathlib terms the chain is: `chebotarev_cyclotomic` → `.liminf_eq` (mathlib) — **2 calls**, both `≤3`.

Conclusion: **COMPOSABLE** (≤1 project-call, or 2 calls down to mathlib's
`Tendsto.liminf_eq`). It is the canonical "convergent ⇒ liminf equals the limit"
extraction (mathlib `Filter.Tendsto.liminf_eq`), applied to the parent theorem.
Per the Phase 6 heuristics table, `(foo …).hasLower` is a single projection call
— the "yes, composable" row, not a proof in disguise.

---

## PHASE 7 — Verdict

## Verdict: `Chebotarev.chebotarev_cyclotomic_lowerDensity_ge`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the lower-density (liminf) form is a *trivial
  extraction* from the full Chebotarev density (which the parent already proves);
  not a separately-named theorem. ChatGPT MCP down — compensated with 4 WebSearch
  channels + nLab.
- Generality analysis (Phase 4): 0 generalisation opportunities; the decl is a
  conclusion-weakening of its parent. Modern-idiom: none (already filter-based).
- Mathlib search (Phase 5): not in mathlib; mathlib has **no** prime-density
  notion and no Chebotarev (grep over commit `747d81a` = empty). The building
  block `HasDirichletDensity.hasLower` is project-local and wraps mathlib's
  `Filter.Tendsto.liminf_eq`.
- Composition check (Phase 6): **COMPOSABLE** — `(chebotarev_cyclotomic …).hasLower`,
  one projection; K = 0 internal uses; the lone "consumer" (`Abelian.lean:882`)
  inlines `.hasLower` itself.

**Rationale:**

`chebotarev_cyclotomic_lowerDensity_ge` is a one-line proof-term wrapper that
extracts the lower-Dirichlet-density (`liminf = δ`) half of the parent
full-density theorem `chebotarev_cyclotomic`, via the project's own
`HasDirichletDensity.hasLower` (itself a thin wrapper of mathlib
`Filter.Tendsto.liminf_eq`). Mathematically this is the textbook triviality "a
convergent quantity equals its liminf" — the literature never states it as a
separate theorem, and the full-density form (strictly stronger) is the standard
packaging and is already present as `chebotarev_cyclotomic`. The call-site grep
is decisive: the wrapper has **zero** consumers, and the one proof that needs a
lower-density fact (`Abelian.lean:882`, feeding `HasLowerDirichletDensity.mono`)
re-derives it inline as `hUdens.hasLower` rather than calling this wrapper. So it
is a bypassed thin wrapper: the right action is to inline `.hasLower` at any
future call site, not to ship a named lemma. Because mathlib has no density
machinery at all, this is not NO-mathlib-has-it; it is NO-composable — composable
in ≤1 project-call (≤2 down to mathlib) from the parent theorem.

This is **not** a cost-driven downgrade and the verdict does not touch the
parent: `chebotarev_cyclotomic` remains independently **YES-add-as-is** (per its
own report). Only this wrapper is judged redundant.

**WHY not (refactor-actionable):**
Mathlib has the building block (`Filter.Tendsto.liminf_eq`) but, more to the
point, *the project itself* already exposes the one-call extraction
`HasDirichletDensity.hasLower`. The wrapper duplicates a projection that
consumers already perform inline.

Mathlib building blocks / project building blocks:
  - `Chebotarev.chebotarev_cyclotomic` (`projects/Chebotarev/CebotarevDensity/Cyclotomic.lean:982`) — the parent full-density theorem (the genuine YES-to-upstream result).
  - `Chebotarev.HasDirichletDensity.hasLower` (`…/Density.lean:241`, body `h.liminf_eq`) — project API, ≤1-call.
  - mathlib `Filter.Tendsto.liminf_eq` — the underlying mathlib primitive.

Composition sketch (≤3 lines):
```lean
-- wherever a lower-density fact is needed, instead of the wrapper:
example (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2)
    (σ : Gal(L/K)) :
    HasLowerDirichletDensity {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
      frobeniusClass K L 𝔭 = ConjClasses.mk σ} ((Nat.card Gal(L/K) : ℝ)⁻¹) :=
  (chebotarev_cyclotomic K L m hm σ).hasLower
```

Call sites in the project (Phase 6.0): **K = 0.**
Refactor plan: there are no call sites to update. Action: **delete**
`chebotarev_cyclotomic_lowerDensity_ge` from `Cyclotomic.lean` (lines 991–1001).
No consumer breaks (`Abelian.lean` already inlines `.hasLower`). If a future
consumer wants the lower-density form, inline `(chebotarev_cyclotomic …).hasLower`
at that site — exactly as `Abelian.lean:877` already does with its own term.

Caveat for the cleaner: this is a *sorry-free* result with **0 uses**, so it is
fair game for the `lane:cleanup` fleet to remove as dead/wrapper code under
AINTLIB's on-`main` rules (it is not a producer WIP `sorry`). If there is an
intent to keep a public "lower-density corollary" as documentation of the API
surface, that is the single judgment call — but with K=0 and an inline-bypassing
consumer, the default is inline-and-delete.

**Next action:** delete `chebotarev_cyclotomic_lowerDensity_ge`; if/when a
lower-density fact is needed downstream, inline `(chebotarev_cyclotomic …).hasLower`
(as `Abelian.lean` already does). The parent `chebotarev_cyclotomic` is the
result to upstream, not this wrapper.

---

## Next step

Delete `Chebotarev.chebotarev_cyclotomic_lowerDensity_ge` (Cyclotomic.lean:991–1001)
and, at any future call site, inline `(chebotarev_cyclotomic K L m hm σ).hasLower`.
Ship the parent `chebotarev_cyclotomic` to mathlib instead (its own YES report).
