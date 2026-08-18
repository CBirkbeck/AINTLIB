# `/mathlibable` report — `PadicLFunctions.Coleman.cycloClosurePlus`

**Final verdict: `NO-composable-from-mathlib`** — the declaration is a one-line
`Subgroup` intersection `cycloClosure p n ⊓ localUnitsPlus p n` (`= 𝒞_n ∩ 𝒰_n⁺`), a
single use of mathlib's `⊓` (`Subgroup.instMin` / `Subgroup.mem_inf`) on two
**project-specific** subgroups that have no mathlib counterpart. The mathematical
object (the plus part of the local closure of cyclotomic units, `𝒞_n⁺`) is standard
in Iwasawa theory, but it is assembled entirely from project-local objects via the
lattice meet — no new lemma is justified, and every external call site already
unfolds it on contact (`rw [cycloClosurePlus, Subgroup.mem_inf]`).

Mode A, full 10-phase workflow, exhaustive 9-channel literature sweep.

---

## Baseline (Phase 0)

- lake build:               **build not re-run** (stale/slow per task BUILD NOTE); **reasoned from source** — Phase 0 fallback. The declaration, its two dependencies, and the whole file are `sorry`-free; the dependency chain (`cycloClosure`, `localUnitsPlus`, `cycloUnits`, `globalUnits`, `localUnits`, `Subgroup.topologicalClosure`, `ℂ_[p] = PadicComplex`) all resolves.
- decl `PadicLFunctions.Coleman.cycloClosurePlus`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:214`
- kind:                      `def` (`noncomputable def`; body is a single `Subgroup ℂ_[p]ˣ` meet `⊓`)
- has sorry:                 no (whole file: 0 `sorry`/`admit`)
- module docstring summary:  Cyclotomic units — the global modules `𝒟_n` and their local closures `𝒞` (RJW arXiv:2309.15692 §11.3, TeX 3060–3112 + §9 notation), all realised **inside `ℂ_[p]`** (decomposition replan R11.7).

Dependencies read from source:
- `cycloClosure p n` (`CyclotomicUnits.lean:210`) `= 𝒞_n = (cycloUnits p n).topologicalClosure ⊓ localUnits p n` — the **p-adic (topological) closure** of the cyclotomic units `𝒟_n` inside the local units `𝒰_n` (RJW TeX 3090). Itself a one-line `⊓` of `Subgroup.topologicalClosure` (mathlib) applied to the *project-local* `cycloUnits` with the *project-local* `localUnits`. Project-specific (no mathlib counterpart — the whole `ℂ_[p]`-embedded cyclotomic tower is project-defined).
- `localUnitsPlus p n` (`Iwasawa/LocalUnits.lean:115`) `= 𝒰_n⁺ = 𝒪_{K_n⁺}^×` — the totally-real ("plus") part of the local units, the units of `𝒰_n` whose value lies in `K_n⁺ = ℚ_p(ξ+ξ⁻¹)`. Project-specific bundled subgroup of `ℂ_[p]ˣ`.

---

## Statement (Phase 1)

`PadicLFunctions.Coleman.cycloClosurePlus p n` is **a definition** of the following:

Let `p` be a prime and `n : ℕ`. Inside the field `ℂ_[p]` of `p`-adic complex numbers
(mathlib's `PadicComplex p`), let `𝒟_n` be the cyclotomic units of `F_n = ℚ(μ_{p^n})`,
`𝒰_n` the local units `𝒪_{K_n}^×` of the local cyclotomic field `K_n = ℚ_p(ξ_{p^n})`,
`𝒞_n = (𝒟_n)⁻ ∩ 𝒰_n` the **p-adic (topological) closure** of `𝒟_n` inside `𝒰_n`, and
`𝒰_n⁺ = 𝒪_{K_n⁺}^×` the totally-real (plus) part of the local units
(`K_n⁺ = ℚ_p(ξ + ξ⁻¹)`). Then `cycloClosurePlus p n` is the **plus part of the local
closure of the cyclotomic units**,

  `𝒞_n⁺ = 𝒞_n ∩ 𝒰_n⁺`,

realised as the subgroup `cycloClosure p n ⊓ localUnitsPlus p n` of `ℂ_[p]ˣ`. In RJW
(arXiv:2309.15692, TeX 3090) this is the definition `𝒞_n⁺ = 𝒞_n ∩ 𝒰_n⁺`, one of the
plus/minus closure objects feeding the §12 Iwasawa-module structures and the
plus-part descent of the main theorem (`cycloTower1Plus`, `Main.lean`).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (file scope).
- `n : ℕ` — the cyclotomic level (`F_n = ℚ(μ_{p^n})`, `K_n = ℚ_p(μ_{p^n})`).
- ambient: `ℂ_[p] = PadicComplex p` (normed, valued, algebraically closed field; carries a topological-group structure on `ℂ_[p]ˣ` so `topologicalClosure` is meaningful).

Hypotheses (Lean side): none beyond the typeclasses; this is a plain `def`.

Body (math): `cycloClosure p n ⊓ localUnitsPlus p n` — the lattice meet (intersection)
of two subgroups of `ℂ_[p]ˣ`.

Conclusion (math): `cycloClosurePlus p n = 𝒞_n⁺ = 𝒞_n ∩ 𝒰_n⁺`.

Conclusion (Lean): `Subgroup ℂ_[p]ˣ` — n/a (definition, not a proposition).

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: it is a **one-line `⊓` of two already-defined subgroups** — bookkeeping
notation for the plus eigenspace of an object (`𝒞_n`) that is itself defined one
declaration above. It introduces no new structure of its own: the only "new" content
relative to `cycloClosure` is intersecting with the plus part `𝒰_n⁺`. It is not a
named theorem, not a `## Main results` entry (the module's milestone is
`cyclo_mem_cycloTower1`, and the project goal is `thm:iwasawa`, deferred to §12), and
it sits in a family of four sibling one-line `⊓`-defs (`cycloClosure`,
`cycloClosureOne`, `cycloClosureOnePlus`, plus `localUnitsOnePlus`).

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL only frames the report.
The *object* `𝒞_n⁺` is a standard Iwasawa-theory object — but the Lean declaration is
a small lattice combination of project-local pieces, which is what SMALL records.)

---

## One-line check (Phase 2b)

Body line count: **1 substantive line** — `cycloClosure p n ⊓ localUnitsPlus p n`.
One-liner verdict: **ONE-LINER** (a `def` whose body is a single `⊓`).

ONE-LINER exemption check (each row required):

| Exemption                         | Applies? | Evidence                                                                                                                                                                                                                                 |
|-----------------------------------|----------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Avoid defeq abuse                | no       | The opposite is true: every external consumer **unfolds** the def immediately — all four `Main.lean` call sites are `rw [cycloClosurePlus, Subgroup.mem_inf]`, i.e. they rewrite *through* the def to expose the `⊓`. The def is not acting as an unfolding barrier; it is routinely punched through. No proof relies on the spelling being *sealed*. |
| Avoid typeclass diamonds         | no       | It is a `def` returning a `Subgroup`, not an `instance`/`class`; it participates in no typeclass-search path, so there is no instance for it to disambiguate.                                                                              |
| Mark semantic intent / API name  | partial / weak | It does carry the RJW name `𝒞_n⁺` and a docstring (`TeX 3090`), which is *some* semantic-intent value for readers following the source. But there is **no stable downstream API surface**: the def has 0 lemmas about it, and its consumers do not call `cycloClosurePlus p n` as an opaque value — they unfold it. The name is local source-faithfulness scaffolding, not a load-bearing API anchor that re-implementation would protect. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** (the only positive is a weak "semantic
intent" that is undercut by every consumer unfolding the def rather than using it as a
stable opaque name). Per Phase 2b this biases the verdict toward
`NO-composable-from-mathlib` / `NO-mathlib-has-it`, and a YES verdict would require
Phase 7 to *explicitly* justify the one-liner despite no exemption.

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "cyclotomic units p-adic closure local units Iwasawa theory C_n plus part totally real subfield" | yes | `Cyc_n` / `C_n` = cyclotomic units in `L_n`; **closure of cyclotomic units inside the local units**; "plus part of the principal units modulo cyclotomic units" is a classical Iwasawa result; `L_n⁺` the maximal totally real subfield | Hida *Elementary Iwasawa Theory* lecture notes; Coates–Sujatha *Cyclotomic Fields and Zeta Values*; jtnb "Semi-local units modulo cyclotomic units"; arXiv:math/0512015 (Iwasawa) — the closure-of-cyclotomic-units and its plus part are standard |
| 2 | WebSearch (named-after / aliases) | "Coates-Wiles homomorphism cyclotomic units closure principal units U_n C_n plus minus eigenspace Coleman map" | yes | "**The Closure of the Cyclotomic Units**" is a named section; the inclusion `C_n → E_n` (cyclotomic units into their local closure) and its injectivity in cohomology is studied; plus/minus eigenspaces standard | The Coates–Wiles theorem notes (p-adic.com); Coates–Sujatha; Lang *Cyclotomic Fields I & II* (Rubin appendix); Schneider–Venjakob (Lubin–Tate) — confirms `C_n` (closure) is a textbook object, with the `Col`/Coleman-map context exactly matching this file |
| 3 | WebSearch (mathlib / general form, "⊓") | "intersection of subgroups lattice inf mathlib Subgroup or topological closure intersect" | yes | "**The inf of two subgroups is their intersection**"; subgroups form a complete lattice; for closed subgroups, meet = intersection, join = topological closure of generated subgroup | mathlib4 docs `Algebra.Group.Subgroup.Lattice`; Wikipedia *Lattice of subgroups* — confirms the *operation* (`⊓`) is the generic lattice meet, already in mathlib (see Phase 5) |
| 4 | ChatGPT MCP | (intended: "standard definition of the plus part of the local closure of cyclotomic units `𝒞_n⁺ = 𝒞_n ∩ 𝒰_n⁺`; its generality; historical evolution") | n/a | — | **ChatGPT MCP server not installed** in this environment (ToolSearch for an ask-gpt/chatgpt tool returned only Monitor/TaskStop/WebFetch). Compensated with extra WebSearch (#1–3) + WebFetch (#9, #10) + grep over local mathlib (Phase 5 method D), matching the documented fallback used by the sibling reports in this directory. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | (no references dir; no `refs/`) | Neither directory exists in this checkout (`refs/` absent entirely). Source paper is arXiv:2309.15692 (RJW), cited throughout the module docstrings (TeX 3090 for `𝒞_n⁺`). |
| 6 | nLab | "cyclotomic field" / "Iwasawa theory" (closure of cyclotomic units; plus part) | partial | nLab confirms the cyclotomic-field / totally-real-subfield setting and the Iwasawa main-conjecture context; it does **not** carry a dedicated entry for "the closure of the cyclotomic units" or its plus part (these are classical Iwasawa-theory objects, not categorical) | https://ncatlab.org/nlab/show/Iwasawa+theory — the framework is named; the specific `𝒞_n⁺` lattice object is below nLab's granularity |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept; `𝒞_n⁺ = 𝒞_n ∩ 𝒰_n⁺` is a meet of two subgroups in a fixed topological group, with no universal-property formulation beyond "lattice meet" (which is itself the generic `⊓`, already in mathlib). |
| 8 | Stacks Project | "topological closure of subgroup / units of local field" | n/a | (closures of subgroups of topological groups are generic; the *p-adic cyclotomic* unit closure is number theory, not the Stacks scope) | Recorded n/a — the closure-of-cyclotomic-units is Iwasawa theory; the only Stacks-adjacent primitive (closure of a subgroup) is generic topology mathlib already has. |
| 9 | MathOverflow / Math.SE / Wikipedia (WebFetch of mathlib Lattice doc) | does mathlib have `⊓` of subgroups + `Subgroup.mem_inf`; is there a named "topological-closure-intersect-subgroup" combinator? | yes | `Subgroup.instMin` ("inf of two subgroups is their intersection"); `Subgroup.mem_inf : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p'`; `Subgroup.coe_inf : ↑(p ⊓ p') = ↑p ∩ ↑p'`. **No** dedicated "closure ⊓ subgroup" combinator. | WebFetch of https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Subgroup/Lattice.html — "The intersection operations defined here are purely algebraic set intersections, not topological closures." |
| 10 | recent arXiv (last 5 yr) | (returned by #1/#2) | yes | `C_n` (closure of cyclotomic units), plus/minus parts, used as standing notation in cyclotomic-`ℤ_p`-extension work | arXiv:2007.07454 (2020, universal norms), 2008.10310 (2020), jtnb 2024 ("Semi-local units modulo cyclotomic units in the cyclotomic `ℤ_2`-extensions") — the closure of cyclotomic units and its eigenspace decomposition are live, current convention |

### Literature summary (Phase 3)

Concept identified as: **the plus part of the (p-adic / local) closure of the
cyclotomic units**, `𝒞_n⁺ = 𝒞_n ∩ 𝒰_n⁺`, where `𝒞_n` is the closure of the cyclotomic
units `𝒟_n` inside the local units `𝒰_n` and `𝒰_n⁺` is the totally-real part. This is a
standard Iwasawa-theory object — Lang *Cyclotomic Fields I & II* ("The closure of the
cyclotomic units", with Rubin's Euler-system appendix), Washington *Cyclotomic Fields*,
Coates–Sujatha, Hida's lecture notes — and is exactly the family of objects RJW
(arXiv:2309.15692, TeX 3090) introduces to run the Coleman-map / Iwasawa-main-conjecture
argument this file is formalising. The plus/minus eigenspace split of the local closure
is the standard device (Mazur–Wiles, Greenberg).

Sources agree on the standard form: **yes**, with notation varying (`C_n`, `Cyc_n`,
`\overline{C_n}`, `\bar E_n`; the plus part by a `+` superscript or a `(1+J)/2`
idempotent). The mathematical content is uniformly "closure of the cyclotomic units
inside the local units, then take the totally-real eigenspace".

Most general standard form: the object is *already* maximally natural as stated — it is
the meet of a topological closure with a subgroup. The only "generality dimensions" are
in its *inputs* (which field tower, which ambient), not in the `𝒞_n⁺ = 𝒞_n ∩ 𝒰_n⁺`
construction itself, which is just `(closure) ∩ (plus units)`.

Generality dimensions where the literature varies (all in the *inputs*, not the meet):
- ambient field tower: the cyclotomic `ℤ_p`-extension of `ℚ` (this file, via `ℂ_[p]`) ⊂
  cyclotomic `ℤ_p`-extensions of general totally-real / CM / abelian base fields (Lang,
  Washington, the jtnb/arXiv papers) ⊂ Lubin–Tate / Coates–Wiles towers
  (Schneider–Venjakob). RJW and this file work the `ℚ`-cyclotomic case embedded in `ℂ_p`.
- realisation of the closure: *abstract* (closure inside the inverse limit of local
  units, the textbook choice) vs. *embedded in a fixed completion* `ℂ_[p]` (this file's
  project-specific choice).
- "plus": *intrinsic* (eigenspace of complex conjugation `J`) vs. *concrete generator*
  (units valued in `ℚ_p(ξ+ξ⁻¹)`, the only form available p-adically — there is no
  complex conjugation on `ℂ_p`).

Disagreement with the literature: **none mathematically.** The definition
`𝒞_n⁺ = 𝒞_n ∩ 𝒰_n⁺` is exactly the literature's. The only divergences are *presentation*
(the `ℂ_[p]`-embedding and the concrete-generator "plus"), which are project conventions,
not new mathematics.

> **The decisive Phase-3 finding for the verdict.** The literature object is standard,
> but it is built *from* the closure `𝒞_n` and the plus units `𝒰_n⁺`, **by intersection**.
> The novelty (if any) lives entirely in the inputs `cycloClosure` / `localUnitsPlus`
> (the `ℂ_[p]`-embedded p-adic cyclotomic tower), *not* in the act of intersecting them.
> The intersection is the generic lattice meet `⊓`, which mathlib has (Phase 5).

---

## Generality analysis — `cycloClosurePlus` (Phase 4)

Literature-standard form (from Phase 3): `𝒞_n⁺ = 𝒞_n ∩ 𝒰_n⁺` — the meet of the local
closure of the cyclotomic units with the totally-real part of the local units.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | the construction (the `⊓` itself) | `cycloClosure p n ⊓ localUnitsPlus p n` | `𝒞_n ∩ 𝒰_n⁺` (intersection of the two) | no — already maximally general | the construction *is* the generic lattice meet of two subgroups; there is nothing to weaken. `⊓` works for any two subgroups of any group; this is already the most general possible "intersect these two" form (mathlib's `Subgroup.instMin`). |
| 2 | first input | `cycloClosure p n` (project-local `𝒞_n`, embedded in `ℂ_[p]`) | the local closure `𝒞_n` (abstract, in the inverse limit of local units) | yes (in the input) | this is the project's `ℂ_[p]`-embedded cyclotomic tower — itself project-specific with no mathlib analogue (the *whole* `𝒟_n → 𝒞_n` tower is project-defined). Generalising it is a separate, large project-internal matter, not about *this* `⊓`. |
| 3 | second input | `localUnitsPlus p n` (project-local `𝒰_n⁺`, concrete generator `ℚ_p(ξ+ξ⁻¹)`) | the totally-real local units `𝒰_n⁺` (intrinsic eigenspace of `J`) | yes (in the input) | the concrete-generator "plus" is forced by `ℂ_p` having no complex conjugation; again a property of the *input* `localUnitsPlus`, not of the meet. |
| 4 | base field / tower | `ℚ`-cyclotomic, `n`-th layer | general totally-real/CM base + Lubin–Tate | yes (in the inputs) | the whole tower's base is fixed by the project (RJW formalises the `ℚ`-cyclotomic case); not a knob on `cycloClosurePlus`. |

### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL — *for the construction itself*** (the meet `⊓`
of two subgroups is already the most general possible "intersect these two"). All
"weakening opportunities" (rows 2–4) live in the **inputs** `cycloClosure` /
`localUnitsPlus`, i.e. they are about generalising *other* project definitions (the whole
`ℂ_[p]`-embedded cyclotomic tower), not about restating `cycloClosurePlus`. Number of
weakening opportunities *on this declaration*: **0**.

Proposed restatement: **none** — there is no narrower-than-standard form of "intersect
two subgroups" to fix. (Generalising the *inputs* is a project-architecture question
handled in their own assessments — `cycloClosure` is a sibling project-local def; the
`localUnitsPlus`-family resolved to project-local in the existing reports — not a
generalisation of this meet.)

Cost of restatement: n/a (nothing to restate).

This rules out `YES-but-generalise-first`: the declaration is not a *narrower* form of a
standard statement; it is the standard meet, built from project-local inputs.

### 4c. Modern-idiom check (Phase 4c — Bourbaki 2.0)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | the def has no bundled-hypothesis preamble; `p`/`n` are honest parameters of the tower. |
| 2 | sequences/metric → filters/topological? | no | — | the only topology is inside the *input* `cycloClosure` (via `Subgroup.topologicalClosure`, already the idiomatic mathlib form); `cycloClosurePlus` adds none. |
| 3 | construct an object → universal-property class? | no | — | the meet `⊓` *is* the universal object (categorical product in the subgroup lattice / greatest lower bound); mathlib's `Subgroup` complete-lattice already provides it. No further universal property to expose. |
| 4 | set-with-closure-predicate → bundled-substructure type? | no (already bundled) | — | both inputs and the result are already bundled `Subgroup`s; `⊓` is the lattice operation. This is *already* the idiomatic bundled form (contrast the bespoke `where` of `globalUnitsPlus`; this one is the clean `⊓`). |
| 5 | field/metric-specific → weaken typeclasses? | no | — | the meet needs only `Group ℂ_[p]ˣ`; nothing field/metric-specific is imposed by *this* def. |
| 6 | 1-categorical → higher-categorical? | no | — | not a categorification target. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | — | the `n` indexes the *field layer* (intrinsic to the Iwasawa tower), not a spurious concrete index to generalise. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** The declaration is *already* in the modern mathlib idiom —
a bundled `Subgroup` obtained as the lattice meet `⊓` of two bundled `Subgroup`s, with the
topological closure (in the one input that needs it) expressed via mathlib's
`Subgroup.topologicalClosure`. There is no cleaner contemporary formulation; `⊓` is the
canonical mathlib spelling of "intersect two subgroups". One-line reason this is not a
modernisation move: the only thing to "modernise" would be the *inputs* (the `ℂ_[p]`
embedding of the tower), which is a project-architecture matter assessed elsewhere, not a
reformulation of this meet.

---

## Diamond / defeq risk — `cycloClosurePlus` (Phase 4.5)

(`def`, so the phase runs. It is a *plain* `def` returning a `Subgroup` via `⊓`, not an
`instance`/`class`/coercion.)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | a `def` returning a `Subgroup`, not an `instance`; participates in no typeclass-search path. |
| 2 | Reducibility leak | none | no `@[reducible]`; a sealed `def`. Its body is `⊓`, which is itself sealed; consumers reach the components only via the explicit `rw [cycloClosurePlus, Subgroup.mem_inf]` they already write. |
| 3 | Non-canonical unfolding | low | unfolding `cycloClosurePlus p n` exposes `cycloClosure p n ⊓ localUnitsPlus p n`; combined with `Subgroup.mem_inf` this is exactly the intended (and only) usage pattern. No surprise. |
| 4 | Instance priority collision | none | not an `instance`. |
| 5 | Universe-polymorphism issues | none | all types concrete (`ℂ_[p]ˣ`, `ℕ`); no universe variables. |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort`; only the standard `Subgroup → Set` from `SetLike`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE.** Top risks: none. (Moot for the chosen bucket — a NO verdict adds
nothing to mathlib — but recorded for completeness: the meet would be infrastructure-safe.)

---

## Mathlib search-status: `cycloClosurePlus` (Phase 5)

[A] Lean-Finder       (web service) — **n/a in this environment** (no `lean_finder` MCP tool present); folded into the conceptual phrasing of [C]. The relevant fact is the generic `Subgroup` meet, confirmed via [D].
[B] Loogle (`lean_loogle`) — **n/a in this environment** (no Loogle MCP tool present). Type-patterns that would be tried: `Subgroup _ → Subgroup _ → Subgroup _` (→ `· ⊓ ·`, `Subgroup.instMin`), `?x ∈ ?p ⊓ ?p'` (→ `Subgroup.mem_inf`); both confirmed by grep [D].
[C] LeanSearch (`lean_leansearch`) — **n/a in this environment** (no LeanSearch MCP tool present). NL queries that would be tried: "intersection of two subgroups", "membership in inf of subgroups", "topological closure of a subgroup intersected with a subgroup"; the first two resolve to `Subgroup.instMin` / `Subgroup.mem_inf`, the third has **no** mathlib hit (it is not a named combinator).
[D] Grep mathlib src — over `.lake/packages/mathlib/Mathlib/`:
  - `Subgroup.mem_inf` → **hit**: `theorem mem_inf {p p' : Subgroup G} {x : G} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p'` (`Mathlib/Algebra/Group/Subgroup/Lattice.lean:233`).
  - `Subgroup.coe_inf` → **hit**: `((p ⊓ p' : Subgroup G) : Set G) = (p : Set G) ∩ p'` (`Lattice.lean:229`); the complete-lattice instance is in the same file. `Subgroup.instMin` provides `⊓` (WebFetch #9).
  - `Subgroup.topologicalClosure` → **hit** (the def used by the *input* `cycloClosure`; mathlib carries it for `Subgroup` of a topological group, with `le_topologicalClosure`, `isClosed_topologicalClosure`, `topologicalClosure_coe`, all already used in `CyclotomicUnits.lean`).
  - `cycloClosure` / `cyclotomicClosure` / "closure of cyclotomic units" as a **named group/closure object** → **0 hits**. Mathlib's `RingTheory/RootsOfUnity/CyclotomicUnits.lean` has only *facts* about cyclotomic units (`associated_sub_one_pow_sub_one_of_coprime`, `geom_sum_isUnit`, …), no closure subgroup.
  - "topologicalClosure ⊓ ·" as a named combinator → **0 hits** (the only `⊓ … topologicalClosure` hit is an unrelated Stone–Weierstrass lattice lemma on `C(X,ℝ)`).
[E] Name pattern (`lean_local_search`) — **n/a in this environment** (no `lean_local_search` MCP tool present). Grep over mathlib for `cycloClosurePlus` → **0 hits** (no decl by this name, expected — it is project-local).

Searched for both:
- the user's current form (`cycloClosure p n ⊓ localUnitsPlus p n`, a `Subgroup ℂ_[p]ˣ`) — **not in mathlib** as a named object (and shouldn't be: its inputs are project-local).
- the literature-standard form (`𝒞_n ∩ 𝒰_n⁺`, the meet of a closure with a subgroup) — the **building block** (`⊓` of two subgroups, `Subgroup.mem_inf`) **is** in mathlib; the **packaged object** is not (there is no "closure-of-cyclotomic-units" object, plus or otherwise, in mathlib).

Concluded: **"found the building blocks (`Subgroup.instMin`/`⊓`, `Subgroup.mem_inf`,
`Subgroup.coe_inf`, and `Subgroup.topologicalClosure` for the one input that needs a
closure) — a one-call composition yields the form; the *packaged* `cycloClosurePlus`
object is not in mathlib, and correctly so, since both of its inputs (`cycloClosure`,
`localUnitsPlus`) are project-local p-adic-tower objects with no mathlib counterpart."**

---

## Call sites — `cycloClosurePlus` (Phase 6.0)

Internal use count (within the project, **excluding** the declaring file): **0 as a value**;
the name appears in **4 lines of one file** (`IwasawaProof/Main.lean`), every one of them an
**unfolding rewrite** `rw [cycloClosurePlus, Subgroup.mem_inf]`, never a value being passed.
Inside the declaring file there is **1 use as a value** (`CyclotomicUnits.lean:223`, the very
next def `cycloClosureOnePlus := cycloClosurePlus p n ⊓ localUnitsOne p n`).
External-to-file callers: **1 file** (`Main.lean`), in 4 `rw`-unfolding sites.

| Caller file:line | Usage pattern (one-line excerpt) | Code or comment? |
|------------------|----------------------------------|------------------|
| `IwasawaProof/Main.lean:528` | `rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf]` | code (unfold) |
| `IwasawaProof/Main.lean:612` | `rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf] at h` | code (unfold) |
| `IwasawaProof/Main.lean:621` | `rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf] at h` | code (unfold) |
| `IwasawaProof/Main.lean:753` | `rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf]` | code (unfold) |
| `Iwasawa/CyclotomicUnits.lean:223` | `cycloClosureOnePlus := cycloClosurePlus p n ⊓ localUnitsOne p n` (in-file, builds the next `⊓`) | code (value) |

Inline-derivation grep (was `𝒞_n⁺ = 𝒞_n ∩ 𝒰_n⁺` re-derived elsewhere without `cycloClosurePlus`?):
**(none found)** — there is no competing inline `cycloClosure ⊓ localUnitsPlus`; the def is the
single source of the plus-closure. But note its consumers do not *use* it opaquely: at every
`Main.lean` site it is immediately rewritten away into `cycloClosure ⊓ localUnitsPlus` (and
then into the `Subgroup.mem_inf` conjunction). The one in-file value use feeds it straight into
another `⊓`.

What the pattern tells us (per 6.0.1): the usage is the **"K = 1 internal value use, plus
unfold-on-contact"** cell. The single value-level consumer (`cycloClosureOnePlus`) just
intersects it with a third subgroup; the four proof-level consumers unfold it. This is a
classic "thin lattice wrapper" signal: the def names an intersection that callers immediately
re-expand, which **leans `NO-composable`** — the meet could be written inline at the (few,
co-located) sites. (It is not the strongest NO signal: there *is* a small consumer chain
`cycloClosurePlus → cycloClosureOnePlus → cycloTower1Plus`, so the name is doing readability
work in a tower of `⊓`s; that is what keeps it from being dead code, and is the honest case for
*keeping* it project-local — see Phase 7.)

### Composition check (Phase 6)

Can `cycloClosurePlus p n` be obtained from existing primitives in ≤3 chained calls?

Attempt 1 (the definition itself, as a mathlib-primitive composition):
  - Sketch: `cycloClosure p n ⊓ localUnitsPlus p n`.
  - Mathlib decls used: `Subgroup.instMin` (the `⊓` on `Subgroup`), i.e. **one** mathlib
    primitive (the lattice meet). The two operands are project-local subgroups.
  - Result: **succeeds** — exactly one mathlib operation (`⊓`).
  - Membership unfolds in one further step via `Subgroup.mem_inf` (`x ∈ A ⊓ B ↔ x ∈ A ∧ x ∈ B`),
    which is precisely what every `Main.lean` call site does.

Attempt 2 (not needed): n/a — Attempt 1 is a clean 1-call composition.

Conclusion: **COMPOSABLE.** The form is `(project subgroup) ⊓ (project subgroup)` — a single
use of mathlib's `Subgroup` meet, with membership given by `Subgroup.mem_inf`. Per the Phase-6
heuristics table this is the `Foo.bar (Bar.baz hx)`-style single-operation composition
(here `· ⊓ ·`), squarely "composable", not a proof in disguise.

> Scope note. The thing that is *not* in mathlib is the **packaged name** `cycloClosurePlus`
> over **project-local inputs** — not the operation. Because the inputs (`cycloClosure`,
> `localUnitsPlus`) are themselves project-defined p-adic-tower objects, this is
> `NO-composable-from-mathlib` (mathlib supplies the *combinator* `⊓`; the project supplies
> the *operands*), rather than `NO-mathlib-has-it` (mathlib has no `𝒞_n⁺` object to point at)
> and rather than a YES (the meet is one mathlib call, so no new lemma is warranted).

---

## Verdict: `cycloClosurePlus` (Phase 7)

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the object `𝒞_n⁺ = 𝒞_n ∩ 𝒰_n⁺` (plus part of the local
  closure of the cyclotomic units) is **standard** Iwasawa theory (Lang *Cyclotomic Fields*,
  Washington, Coates–Sujatha, Hida; RJW arXiv:2309.15692 TeX 3090) — but it is constructed
  **by intersecting** the closure `𝒞_n` with the plus units `𝒰_n⁺`; the construction is the
  generic lattice meet, and the only project-novel content is in the *inputs*.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL for the construction** (the meet `⊓`
  cannot be weakened; 0 weakening opportunities on *this* decl). Phase 4c: the def is already
  in the modern mathlib idiom (bundled `Subgroup` via `⊓`), so no "modernise-first" YES.
- Mathlib search (Phase 5): **found the building blocks** — `Subgroup.instMin` (`⊓`),
  `Subgroup.mem_inf` (`Lattice.lean:233`), `Subgroup.coe_inf` (`Lattice.lean:229`), and
  `Subgroup.topologicalClosure` (for the one input that closes) — but **no packaged
  `cycloClosurePlus`/closure-of-cyclotomic-units object** (and no "closure ⊓ subgroup"
  combinator).
- Composition check (Phase 6): **COMPOSABLE** — the form is one `⊓` (`cycloClosure p n ⊓
  localUnitsPlus p n`), membership by `Subgroup.mem_inf`. Call sites: 1 in-file value use
  (feeding another `⊓`) + 4 external `rw`-unfold sites — a thin lattice wrapper consumers
  re-expand on contact.

**Rationale.**
`cycloClosurePlus p n` is the plus part of the local closure of the cyclotomic units,
`𝒞_n⁺ = 𝒞_n ∩ 𝒰_n⁺` — a genuinely standard Iwasawa-theory object. But mathlib-worthiness is
not "is the object standard"; it is "is *this declaration* the right thing for mathlib to
own". And this declaration is a **one-line lattice meet** of two **project-specific**
subgroups: `cycloClosure p n` (the `ℂ_[p]`-embedded closure of the project's cyclotomic
units, itself a project-local object with no mathlib counterpart) and `localUnitsPlus p n`
(the project's totally-real local units). The *operation* that combines them — intersection
of subgroups — is already in mathlib as the complete-lattice meet `⊓` (`Subgroup.instMin`),
with membership `Subgroup.mem_inf`. So there is nothing new to *add*: the building block is
mathlib's, and the operands are the project's. A reader needing `𝒞_n⁺` writes
`cycloClosure ⊓ localUnitsPlus` and reasons about membership with `Subgroup.mem_inf` — which
is exactly what every external call site in `Main.lean` already does
(`rw [cycloClosurePlus, Subgroup.mem_inf]`). The one-liner has no Phase-2b exemption (it is
not a defeq barrier — consumers punch through it; not an instance — no diamond; its name is
only weak source-faithfulness scaffolding), which per the gate forecloses a YES on a
one-liner without an explicit override, and there is none to give: this is not a missing
mathlib primitive, it is a project-local naming of `A ⊓ B`.

This is `NO-composable-from-mathlib` rather than the neighbouring buckets for precise
reasons. It is **not** `NO-mathlib-has-it`: mathlib has no `𝒞_n⁺` object (nor any
closure-of-cyclotomic-units group) to cite and specialise from — Phase 5 found facts about
cyclotomic units but no closure object — so the "found in mathlib as `<X>`" requirement
fails. It is **not** `YES-add-as-is` / `YES-but-generalise-first`: the construction is one
mathlib call (`⊓`), maximally general and already idiomatic, with no weakening to do and no
new content to contribute (Phase 4/4c/6). It is **not** `BORDERLINE`: the buckets do not
genuinely tie — the only judgment in play (should the *project* keep this readability
wrapper in its tower of `⊓`s?) is a project-cleanup question, **not** a mathlib-inclusion
question, and the mathlib-inclusion answer is unambiguous (mathlib should not own a named
`⊓` of two foreign subgroups). For completeness the contrast with the sibling
`globalUnitsPlus` (NO-mathlib-has-it) is instructive: there, mathlib *did* have the abstract
object (`realUnits`/`(𝓞 K⁺)ˣ`); here, mathlib has only the *combinator* `⊓`, and the object
is assembled from project-local pieces — which is exactly the `NO-composable-from-mathlib`
signature.

**WHY not (refactor-actionable).** Mathlib already has the building blocks; the user's form
is a **single** mathlib call (`⊓`), so no new lemma is justified — it is inlineable. The
mathlib primitives are:
- `Subgroup.instMin` — the lattice meet `⊓` on `Subgroup G` ("the inf of two subgroups is
  their intersection").
- `Subgroup.mem_inf : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p'` (`Mathlib/Algebra/Group/Subgroup/Lattice.lean:233`).
- `Subgroup.coe_inf : ↑(p ⊓ p') = ↑p ∩ ↑p'` (`Lattice.lean:229`).
- (for the closure input, already used by `cycloClosure`) `Subgroup.topologicalClosure`,
  with `Subgroup.le_topologicalClosure`, `Subgroup.isClosed_topologicalClosure`.

Mathlib building blocks: `Subgroup.instMin` (`⊓`), `Subgroup.mem_inf`, `Subgroup.coe_inf`.
Composition sketch (≤3 lines — the def *is* the composition):
```lean
-- the object:
example (p n) : Subgroup ℂ_[p]ˣ := cycloClosure p n ⊓ localUnitsPlus p n
-- membership at every call site (what Main.lean already writes):
--   rw [Subgroup.mem_inf]   -- u ∈ cycloClosure p n ⊓ localUnitsPlus p n ↔ u ∈ cycloClosure p n ∧ u ∈ localUnitsPlus p n
```
Call sites in the project (from Phase 6.0): **5** total — 1 in-file value use
(`CyclotomicUnits.lean:223`, inside `cycloClosureOnePlus`), and 4 `rw`-unfold sites in
`IwasawaProof/Main.lean` (lines 528, 612, 621, 753).

Refactor plan (project-internal — this is **not** a mathlib PR):
- **Recommended: keep the def project-local; do not PR.** The mathlib-inclusion verdict is a
  firm NO (a named `⊓` of two project-local subgroups is not a mathlib contribution).
  Whether to *inline* it in the project is a minor cleanup call, and on balance the def earns
  its keep **locally**: it gives the RJW name `𝒞_n⁺` (TeX 3090) to a node in a readable tower
  of `⊓`s (`cycloClosure → cycloClosurePlus → cycloClosureOnePlus → cycloTower1Plus`), and the
  four `Main.lean` sites read more clearly unfolding a named layer than a raw double `⊓`.
- **If a cleanup pass does choose to inline** (optional): at the in-file site
  `CyclotomicUnits.lean:223` replace `cycloClosurePlus p n` with `cycloClosure p n ⊓
  localUnitsPlus p n` (so `cycloClosureOnePlus = cycloClosure ⊓ localUnitsPlus ⊓ localUnitsOne`);
  at each of the four `Main.lean` sites, drop `cycloClosurePlus,` from the `rw [...]` list and
  expand the membership with one extra `Subgroup.mem_inf` against the inlined `⊓` (mechanical —
  the goals are already `Subgroup.mem_inf`-shaped). No new mathematics either way.
- Either way: do **not** open a mathlib PR for `cycloClosurePlus` — mathlib already provides
  the only general thing here (the `Subgroup` meet `⊓` with `Subgroup.mem_inf`); the object is
  built from project-local p-adic-tower inputs.

Next action: do **not** open a mathlib PR. Treat `cycloClosurePlus` as project-local
scaffolding — keep it for readability in the tower of `⊓`s (recommended), or inline the single
`⊓` at its 5 co-located call sites in a cleanup pass. Reserve mathlib-upstreaming effort for
the file's genuinely p-adic results (e.g. `norm_le_one_of_isIntegral_int`, the `zpPow` /
`zpPow_mem_cycloUnits_topologicalClosure` density machinery), not this lattice-meet `def`.

---

## Next step

Do **not** open a mathlib PR for `cycloClosurePlus`. It is a one-line lattice meet
`cycloClosure p n ⊓ localUnitsPlus p n` (`= 𝒞_n ∩ 𝒰_n⁺`) of two **project-local** subgroups,
combined with mathlib's existing `Subgroup` meet `⊓` (`Subgroup.instMin`, membership via
`Subgroup.mem_inf : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p'`, `Mathlib/Algebra/Group/Subgroup/Lattice.lean:233`).
Mathlib has the combinator but no `𝒞_n⁺`/closure-of-cyclotomic-units object to specialise from,
so this is `NO-composable-from-mathlib`, not `NO-mathlib-has-it`. Keep it project-local — it is
a readable named node in the `⊓`-tower `cycloClosure → cycloClosurePlus → cycloClosureOnePlus →
cycloTower1Plus` (recommended), or, as an optional project cleanup, inline the single `⊓` at its
five co-located call sites (1 in `CyclotomicUnits.lean:223`, 4 `rw`-unfolds in `Main.lean`). No
new lemma is justified and no mathlib contribution is warranted.
