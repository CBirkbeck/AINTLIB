# /mathlibable report — `EllSequence.map_rel₄`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz theorem; elliptic
> curves; division polynomials; elliptic divisibility sequences).
> Reasoned from source (local Lean build stale); mathlib index + WebSearch used.

## Verdict (TL;DR)

**`BORDERLINE-needs-human`** — `map_rel₄` is a trivial mechanical ring-hom
functoriality `simp`-helper for `rel₄`, with **one** internal consumer
(`map_net`). It is *not* independently mathlib-worthy. But mathlib's own EDS file
already ships the *identical idiom* (`@[simp] map_normEDS`, `map_preNormEDS`,
`map_complEDS`, …). So the live question is whether the whole new `EllSequence` /
`rel₄` / `net` track — a formalization of the 2026 preprint Xu, *On Elliptic
Sequences over Commutative Rings* — should be upstreamed; if it is, `map_rel₄`
rides along as part of that package exactly like `map_normEDS`. That upstreaming
decision is a human call (new-preprint provenance + scope).

Qualified name: **`map_rel₄`** (resolves as `EllSequence.map_rel₄` to callers).

---

### Baseline (Phase 0)
- lake build:               not run (local build is stale per task; reasoned from source)
- decl `map_rel₄`:          ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1165`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS): defines IsEllSequence/normEDS/complEDS and the EllSequence relation machinery (`addMulSub`/`rel₄`/`net`), proves `normEDS` is an EDS.

**Qualified-name resolution.** `map_rel₄` is declared at line 1165, which lies
*between* `end EllSequence` (line 1112) and the next `namespace EllSequence`
(line 1356) — i.e. at the **top level** of the file (the file has no outer
`namespace`, only an `@[expose] public section` at line 81). Its body references
`rel₄`, `addMulSub` unqualified because `open EllSequence` is in scope (line 599).
The matching `map_net` is invoked **bare** (`← map_net`) at line 1467 in the same
file. The companion HasseWeil copy refers to `EllSequence.map_net` (line 958),
i.e. its copy sits *inside* `namespace EllSequence`; that file is a separate
(diverged) duplicate. For the NagellLutz target the literal qualified name is
`map_rel₄`; callers in `EllSequence`-opened scope see it as `EllSequence.map_rel₄`.
Either spelling resolves to the same decl.

---

### Statement (Phase 1)

`map_rel₄` states that a ring homomorphism `f : R → S` **commutes with the
four-index elliptic relation `rel₄`**: for any integers `p, q, r, s`,
```
f (rel₄ W p q r s) = rel₄ (f ∘ W) p q r s.
```
Here `rel₄ W a b c d = addMulSub W a b · addMulSub W c d − addMulSub W a c ·
addMulSub W b d + addMulSub W a d · addMulSub W b c`, where
`addMulSub W m n = W((m+n).tdiv 2) · W((m−n).tdiv 2)`. Mathematically this is the
(near-trivial) functoriality of a fixed polynomial expression in the values of a
ℤ-indexed sequence `W : ℤ → R`: pushing `f` through products, sums and
differences. It is the `rel₄` member of a uniform family of "push a ring hom
through this EDS construct" lemmas.

Variables / typeclasses (Lean side):
- `{R : Type u} {S : Type v} [CommRing R] [CommRing S]` — source/target comm rings.
- `(W : ℤ → R)` — the integer-indexed sequence.
- `{F} [FunLike F R S] [RingHomClass F R S] (f : F)` — a **bundled-morphism-class**
  ring hom (note: *more general* than mathlib's `f : R →+* S`; see Phase 4).
- `(p q r s : ℤ)` — the four indices.

Hypotheses: none.

Conclusion (math): `f` commutes with `rel₄`.
Conclusion (Lean): `f (rel₄ W p q r s) = rel₄ (⇑f ∘ W) p q r s`.

Proof body (one line): `simp_rw [rel₄, map_add, map_sub, map_mul, map_addMulSub]`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: helper `simp`-style functoriality lemma; not a named theorem, not a new
structure, not a `## Main statement`. (Lit width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — the one-liner def heuristic
does **not** apply. Recorded as n/a. (For the record, the *proof* is a single
`simp_rw`, reinforcing that this is mechanical functoriality, not new content.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found                              | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | Stange elliptic nets `rel₄` four-index net relation division polynomial recurrence      | yes  | the 3-index net relation `W(p+q)W(p−q)W(r)²=…`   | researchgate/arXiv 0710.1316 (Stange, *Elliptic nets and elliptic curves*) — the *relation*, not its functoriality |
|  2 | WebSearch (general / source)     | "On Elliptic Sequences over Commutative Rings" arXiv 2604.05280 rel4 net addMulSub      | yes  | "elliptic relations": 4-parameter homogeneous quartic family among terms | **Xu 2026** — the exact source paper this `EllSequence` track formalizes |
|  3 | WebSearch (functoriality / Lean) | ring homomorphism functoriality EDS normEDS preNormEDS pushforward Lean mathlib          | yes  | mathlib `map_normEDS` family (the idiom)          | functoriality of EDS constructs is a *formalization-internal* `@[simp]` family, never a paper theorem |
|  4 | ChatGPT MCP                      | (unavailable this session — per task; substituted by extra WebSearch #1–#3 + mathlib source read) | n/a | —                                                | MCP down; fallbacks used as instructed |
|  5 | Local references                 | `.mathlib-quality/references/` and `refs/NagellLutz/`                                    | n/a  | (absent)                                          | neither dir exists — recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                        | n/a  | —                                                | nLab has no elliptic-net page; functoriality of a fixed polynomial map is not an nLab-level concept |
|  7 | nCatLab                          | —                                                                                       | n/a  | —                                                | not a categorical concept (a single ring-hom naturality of a concrete expression) |
|  8 | Stacks Project                   | elliptic divisibility sequence / division polynomial                                     | n/a  | —                                                | Stacks does not cover EDS / elliptic nets |
|  9 | MathOverflow / MSE               | elliptic net relation over commutative rings generality                                  | n/a  | —                                                | covered by the Xu preprint (#2); no separate Q&A needed for a functoriality helper |
| 10 | recent arXiv (≤5 yr)             | elliptic sequences commutative rings 2025–2026                                           | yes  | Xu 2604.05280 (2026); Stange 2025/521 isogeny div polys | confirms this is an **active, brand-new** development |

**Protocol satisfied:** WebSearch ran 3 distinct queries at different generality
levels (specific `rel₄`, source paper, functoriality/Lean idiom). ChatGPT MCP
recorded n/a-with-reason (down this session; compensated by extra WebSearch +
direct mathlib-source reading). Local refs, nLab, nCatLab, Stacks, MathOverflow,
arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: the **four-index "elliptic relation" `rel₄`** of Stange's
elliptic nets, in the commutative-ring formulation of **Xu, *On Elliptic
Sequences over Commutative Rings*, arXiv 2604.05280 (2026)** — `map_rel₄`
specifically is the *ring-hom functoriality* of that relation.
Sources agree on the standard form: yes — the relation is standard (Stange);
`rel₄`/`addMulSub`/`net` are the project's faithful Lean encoding of Xu's
"elliptic relations" / building blocks.
Most general standard form: the relation holds over any commutative ring (Xu's
whole point), so its functoriality across a ring hom is automatic.
Generality dimensions where the literature varies: only the *coefficient ring*
(field → arbitrary commutative ring); Xu already takes the most general (any
commutative ring).
Disagreement with the literature: **none** — but note the literature treats
`rel₄` functoriality as trivial scaffolding, never as a named result. There is no
"theorem" in any paper called anything like `map_rel₄`; it is purely a
formalization convenience, exactly like mathlib's `map_normEDS`.

---

### Generality analysis — `map_rel₄` (Phase 4)

Literature-standard target: functoriality of `rel₄` over **any commutative ring**
along **any ring homomorphism** (Xu 2026 works over arbitrary commutative rings).

| # | Parameter / hypothesis              | Current Lean form                              | Literature-standard form          | Weaker form? | Reason |
|---|-------------------------------------|------------------------------------------------|-----------------------------------|--------------|--------|
| 1 | `[CommRing R] [CommRing S]`          | comm rings                                      | comm ring (Xu's setting)          | NO           | `rel₄` is a comm-ring polynomial expression; CommRing is exactly right |
| 2 | `[FunLike F R S] [RingHomClass F R S]` | bundled-morphism **class** hom               | a ring hom                        | already MAX  | this is the *modern* generalization — strictly more general than mathlib's `f : R →+* S` |
| 3 | `(W : ℤ → R)`                        | ℤ-indexed sequence                              | ℤ-indexed (Stange/Xu use ℤ or a group) | borderline | the relation is stated for ℤ indices in the project; matches source |
| 4 | `(p q r s : ℤ)`                      | four integer indices                            | four integer indices              | NO           | intrinsic to `rel₄` |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (indeed *more* general than mathlib's
sibling `map_normEDS`, which fixes `f : R →+* S`; this lemma uses the
`RingHomClass F R S` class form).
Number of weakening opportunities found: 0.
Cost of restatement: n/a (nothing to weaken).

### Modern-idiom check (Phase 4c)

| #  | Question                                                              | Applies? | Notes |
|----|-----------------------------------------------------------------------|----------|-------|
| 1  | Bundled hyps → typeclasses?                                           | already done | uses `RingHomClass F R S` (the class form) — more modern than mathlib's own `map_normEDS` |
| 2  | sequences/metric → filters/topology?                                  | no       | purely algebraic identity; no limits |
| 3  | construction → universal property?                                   | no       | it's a fixed polynomial map, not a construction |
| 4  | set+closure-predicate → bundled substructure?                        | no       | n/a |
| 5  | field/metric-specific → weaken typeclass?                            | no       | already at CommRing |
| 6  | 1-categorical → higher-categorical?                                  | no       | n/a |
| 7  | concrete index ℕ/ℤ/ℝ → general monoid/group?                         | maybe (whole track) | Stange's nets are over general groups; this is a *track-wide* design choice, not specific to `map_rel₄`, and the source uses ℤ indices here |

Modern idiom available: **no further** (the lemma already uses the modern
`RingHomClass` form). One-line reason: it is a finite ring-equality of a fixed
quartic expression; there is no additional contemporary idiom to adopt. If
anything, upstreaming would *narrow* it to match mathlib's existing
`f : R →+* S` convention in that file — but that's a style alignment, not a
generalisation gap.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **lemma** (introduces no definitional equality and no
typeclass-search path). Skipped.

---

### Mathlib search-status: `map_rel₄` (Phase 5)

mathlib pin: `09b373db…` (2026-06-21). Searched
`.lake/packages/mathlib/Mathlib/`.

[A] Lean-Finder       "ring hom commutes elliptic relation / rel₄"     no hits (concept absent from mathlib)
[B] Loogle            `f (rel₄ _ _ _ _ _) = rel₄ _ _ _ _ _`            n/a — `rel₄` / `addMulSub` are not mathlib names
[C] LeanSearch        "map ring hom through four-index EDS relation"    no hits
[D] Grep mathlib src  `rel₄`, `addMulSub`, `EllSequence`, `map_rel₄`    **no hits anywhere in Mathlib/** (these constructs do not exist in mathlib)
[E] Name pattern      `map_normEDS`, `map_preNormEDS`, `map_complEDS`   **HITS** — mathlib HAS the identical-idiom family (see below), but NOT for `rel₄`

Searched for both the user's form (functoriality of `rel₄`) and the
literature-standard form. Neither `rel₄`/`addMulSub`/`net` nor their
functoriality exist in mathlib.

**Crucial adjacent fact.** mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
(lines 505–546) contains a `section Map` with the **exact same family of
lemmas**, all tagged `@[simp]`:
`map_preNormEDS'`, `map_preNormEDS`, `map_complEDS₂`, `map_normEDS`,
`map_complEDS'`, `map_complEDS` — each of the form
`f (Construct b c d n) = Construct (f b) (f c) (f d) n`. The project's
`map_preNormEDS`/`map_normEDS`/`map_complEDS₂`/`map_complEDS` are **literal
duplicates** of these. `map_rel₄` is the *missing sibling* for the `rel₄`/`net`
constructs — which are absent from mathlib only because the constructs themselves
are new (Xu 2026). Difference: mathlib uses `f : R →+* S`; the project uses
`RingHomClass F R S`.

Concluded: **not in mathlib** (all methods exhausted; the construct `rel₄`
itself is absent), **but the lemma family it belongs to *is* an established,
`@[simp]`-blessed mathlib idiom** for sibling EDS constructs.

---

### Composition check (Phase 6)

#### Call sites — `map_rel₄` (Phase 6.0)

Internal use count (excluding the declaring file lines 1165–1166): **0 direct**;
but **1 essential consumer** — `map_net` (line 1169), whose entire proof is
`simp_rw [net_eq_rel₄, map_rel₄]`. `map_net` is in turn used at line 1467
(`net_normEDS`, the bridge proving `net (normEDS …) = 0`), and the diverged
HasseWeil copy uses `EllSequence.map_net` at line 958.

External-to-file callers: 0 (the only consumer, `map_net`, is in the same file).

| Caller file:line                                                | Usage pattern |
|-----------------------------------------------------------------|---------------|
| `…/LutzNagell/EllipticDivisibilitySequence.lean:1169` (`map_net`) | `simp_rw [net_eq_rel₄, map_rel₄]` |

Inline-derivation grep: none — `map_rel₄` is the sole route to `map_net`; not
re-derived elsewhere.

Call-sites signal: **K = 1 internal consumer** (`map_net`). On the Phase-6.0
table this is the "possibly the wrong grain / could be inlined" pattern in
isolation — but here the consumer chain (`map_rel₄` → `map_net` → `net_normEDS`)
is real and load-bearing for the development, and it is the faithful Lean mirror
of mathlib's own per-construct `map_*` family.

#### Composition attempt (Phase 6a)

Can `map_rel₄` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `simp_rw [rel₄, map_add, map_sub, map_mul, map_addMulSub]` (the actual
proof).
- Mathlib decls used: `map_add`, `map_sub`, `map_mul` (all mathlib).
- **Plus** `rel₄` (project def) and `map_addMulSub` (project lemma, line 1162) —
  neither is in mathlib.
- Result: **fails as a mathlib-only composition** — it depends on the project's
  own `rel₄` unfolding and `map_addMulSub`, which presuppose the `addMulSub`/`rel₄`
  defs that mathlib lacks.

Conclusion: **NOT-COMPOSABLE from mathlib** (the building blocks `rel₄`,
`addMulSub`, `map_addMulSub` are project-local; mathlib only supplies the generic
`map_add/map_mul/map_sub`). It *would* be a trivial 1-line composition **inside a
world where `rel₄`/`addMulSub`/`map_addMulSub` exist** — i.e. it is trivial
*relative to its own track*, which is exactly why it is not a standalone
contribution but a rider on that track.

---

## Verdict: `map_rel₄`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature (Phase 3): the construct `rel₄` is from Xu 2026 (arXiv 2604.05280),
  *On Elliptic Sequences over Commutative Rings* — a brand-new preprint this
  track formalizes; `rel₄` functoriality is never a named paper result, only
  scaffolding (mirrors mathlib's own `map_normEDS` `@[simp]` family).
- Generality (Phase 4): **MAXIMALLY GENERAL** — already uses the `RingHomClass F
  R S` class form, *more* general than mathlib's sibling `map_normEDS`
  (`f : R →+* S`).
- Mathlib search (Phase 5): **not in mathlib** (the `rel₄`/`net`/`addMulSub`
  constructs are absent), **but the identical `map_*` lemma idiom is already in
  mathlib** for the normEDS/complEDS constructs (all `@[simp]`).
- Composition (Phase 6): **NOT-COMPOSABLE** from mathlib alone (needs project-only
  `rel₄`, `addMulSub`, `map_addMulSub`); call-sites **K = 1** (sole consumer
  `map_net`).

**Rationale.**
`map_rel₄` in isolation is a textbook *trivial functoriality `simp`-helper*: a
ring hom commutes with a fixed quartic expression, proved by one `simp_rw`. With a
single internal consumer and a one-line mechanical proof, it would never be
proposed to mathlib *on its own*. The reason it is **not** a clean NO is that
mathlib's own EDS file (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`,
§Map, lines 505–546) deliberately ships *exactly this family* — `map_preNormEDS`,
`map_normEDS`, `map_complEDS`, … each `@[simp]` — establishing that "one ring-hom
pushforward lemma per EDS construct" is the *intended* mathlib idiom. `map_rel₄`
is the missing sibling for the `rel₄`/`net` constructs, absent from mathlib only
because those constructs are themselves new (Xu 2026). So the decision is not
about this lemma at all: it is about whether the whole new **`EllSequence` /
`rel₄` / `net`** track gets upstreamed into mathlib's EDS file. If it does,
`map_rel₄` (renamed/aligned to `EllSequence.rel₄`'s home, and possibly downshifted
to mathlib's `f : R →+* S` convention + `@[simp]`) goes in **as part of that
package**, exactly mirroring `map_normEDS`. If the track stays project-local (a
WIP formalization of a 2026 preprint, which AINTLIB explicitly tolerates),
`map_rel₄` stays with it. That upstream-or-not judgment — gated on the preprint's
maturity, mathlib's appetite for the elliptic-net layer, and naming/`@[simp]`
alignment — is a human call. Note also that the project already duplicates
mathlib's `map_preNormEDS`/`map_normEDS`/`map_complEDS₂`/`map_complEDS`
verbatim, so a refactor that re-bases this file onto mathlib's EDS file (deleting
the duplicates) is the natural home for resolving `map_rel₄` too.

**Numbered questions (for the human):**
1. Is the `EllSequence` / `rel₄` / `net` track (Xu 2026, arXiv 2604.05280)
   intended for eventual mathlib upstreaming, or to stay a project-local WIP? If
   upstream, `map_rel₄` ships **with** `rel₄`/`net` as the sibling of
   `map_normEDS`; if local, it stays here. (yes-upstream / no-local)
2. Given the project **already re-declares mathlib's `map_preNormEDS` /
   `map_normEDS` / `map_complEDS₂` / `map_complEDS` verbatim**, should this whole
   file be re-based onto `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
   (importing those, adding only the genuinely-new `EllSequence`/`rel₄`/`net`
   layer)? That refactor is the right place to decide `map_rel₄`'s fate. (yes/no)
3. If upstreamed: keep the project's **more general** `RingHomClass F R S` form,
   or align to mathlib's existing `f : R →+* S` convention in that file (and tag
   `@[simp]`) to match the sibling `map_*` lemmas? (class-form / bundled-form)

**Next action:** user answers Q1–Q3. If Q1 = no-local → close as project-internal
helper (no mathlib action). If Q1 = yes-upstream → fold `map_rel₄` into the
`rel₄`/`net` upstreaming PR alongside `map_net`, aligned to the `map_normEDS`
sibling (per Q3), and run the file re-basing of Q2 to drop the four already-in-
mathlib duplicates. Re-run `/mathlibable map_rel₄` once the track's upstream
status is decided.

---

## Sources

- Xu, *On Elliptic Sequences over Commutative Rings*, arXiv:2604.05280 (2026) — the source paper for the `EllSequence`/`rel₄`/`net` track.
- Stange, *Elliptic nets and elliptic curves*, arXiv:0710.1316 — origin of the elliptic-net relation.
- Stange, *Division polynomials for arbitrary isogenies*, eprint 2025/521 — confirms active development.
- mathlib `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` §Map (lines 505–546, pin 09b373db, 2026-06-21) — the established `@[simp] map_*` EDS-functoriality idiom and the verbatim duplicates of `map_preNormEDS`/`map_normEDS`/`map_complEDS₂`/`map_complEDS`.
