# /mathlibable report — `map_net`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences / Stange elliptic nets).
> Re-run 2026-06-21 with independently-verified evidence (mathlib source read directly;
> Xu's source paper positively identified). Verdict unchanged from the 2026-06-18 run.

### Baseline (Phase 0)
- lake build:               ⚠ not re-run (local build stale per task brief); decl read directly from source
- decl `map_net`:           ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1168`
- kind:                     `lemma`
- has sorry:                no
- module docstring summary: defines elliptic divisibility sequences (EDS) and constructs normalised
  EDSs from initial terms; this project **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence`
  and extends it with Stange's elliptic-net machinery (`addMulSub`, `rel₄`, `net`, …) not in mathlib.

**Qualified name (VERIFIED):** `map_net` (root namespace).
Namespace audit at line 1168: the outer `namespace EllSequence` (opened line 90) closed at line 597;
the second `namespace EllSequence` (line 1079) closed at line 1112; `section Map` (line 1116) opens no
namespace. Net open-namespace depth at line 1168 = 0 ⇒ the lemma is **top-level**, qualified name
`map_net` (the parsed name was correct). Contrast: sibling lemmas in the same section that *do* need
namespaced names are written explicitly (`EllSequence.map_compl'`, `EllSequence.map_compl` at lines
1140/1152) — confirming the section is at root and `net`/`rel₄`/`addMulSub` are reached via the
`open EllSequence` at line 884.

Source (verbatim):
```lean
lemma map_net (p q r s : ℤ) : f (net W p q r s) = net (f ∘ W) p q r s := by
  simp_rw [net_eq_rel₄, map_rel₄]
```

---

### Statement (Phase 1)

`map_net` states a **naturality / functoriality** fact: a ring homomorphism commutes with the
"elliptic-net" polynomial expression `net`.

For a commutative ring `R`, a sequence `W : ℤ → R`, a (bundled) ring hom `f : R → S`, and integers
`p q r s`, with

  net(W, p, q, r, s) = W(p+q+s)·W(p−q)·W(r+s)·W(r)
                       − W(p+r+s)·W(p−r)·W(q+s)·W(q)
                       + W(q+r+s)·W(q−r)·W(p+s)·W(p),

the lemma asserts

  f(net(W, p, q, r, s)) = net(f ∘ W, p, q, r, s).

`net` is the building block of **Stange's elliptic-net relation** / **Xu's elliptic relation**
(WebSearch confirmed the exact formula and the source papers — see Phase 3). Mathematically the
content is: *the net expression is a ℤ-coefficient polynomial in finitely many values of `W`, hence
natural in the coefficient ring* — apply `f`, which preserves `+`, `−`, `×`, and it passes through.

Variables / typeclasses (Lean side):
- `{R S} [CommRing R] [CommRing S]` — source/target commutative rings
- `(W : ℤ → R)` — the sequence
- `{F} [FunLike F R S] [RingHomClass F R S] (f : F)` — a bundled ring hom (class form, not `R →+* S`)
- `(p q r s : ℤ)` — the four net indices

Hypotheses: none (unconditional).

Conclusion (math): `f` commutes with `net`.
Conclusion (Lean): `f (net W p q r s) = net (f ∘ W) p q r s`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a glue/naturality `map_*` lemma whose body is a 2-step `simp_rw`; not a new structure, not a
named theorem, not a `## Main statements` entry. (Literature width was run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — the one-liner gate (which biases *definitions*
toward NO) does not apply. Recorded as a one-line note: the **proof** body is one substantive line
(`simp_rw [net_eq_rel₄, map_rel₄]`), reinforcing that the statement is trivial plumbing, but Phase 2b
imposes no constraint on lemmas.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found                              | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | Stange elliptic nets "net" relation division polynomials elliptic divisibility sequence                 | yes  | **exact net relation** confirmed as Stange's elliptic-net axiom; division polys give EDS | arXiv 0710.1316 ("Elliptic nets and elliptic curves"); arXiv 2512.09601; Wikipedia EDS; Ward 1948 recurrence |
|  2 | WebSearch (general form)         | ring homomorphism commutes with EDS normEDS map_normEDS Lean mathlib                                     | partial | mathlib has `normEDS`; the naturality step is not a *named* literature result | mathlib4_docs EllipticDivisibilitySequence; arXiv 2604.05280; arXiv 1101.3839 |
|  3 | WebSearch (named source paper)   | arXiv 2604.05280 "Elliptic Sequences over Commutative Rings" elliptic net rel4 universal normEDS         | yes  | **identified the project's source paper**: Junyan Xu, *On Elliptic Sequences over Commutative Rings*; "elliptic relations E(a,b,c,d) are **equivalent to the axiom for elliptic nets defined by Stange**" | this is exactly `rel₄`/`net`; treats EDS over arbitrary commutative rings; naturality used implicitly |
|  4 | ChatGPT MCP                      | Is `f(net W …)=net (f∘W) …` a citable result or trivial ring-hom-commutes-with-polynomial?               | n/a  | (MCP **down** per task brief — not invoked to avoid a failed Codex exec) | fell back to WebSearch ×3 + direct mathlib-source precedent |
|  5 | Local references                 | (no `.mathlib-quality/references/` directory present for NagellLutz)                                     | n/a  | dir absent (refs are local-only & gitignored)    | recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                                        | n/a  | nLab has no elliptic-net page; concept is arithmetic-geometry, not categorical | the naturality is the generic "polynomial functor preserves ring maps" — folklore |
|  7 | nCatLab                          | —                                                                                                       | n/a  | not a categorical concept (no functor/2-cat content beyond "natural in the ring") | — |
|  8 | Stacks Project                   | elliptic net / division polynomial                                                                       | n/a  | Stacks has no elliptic-net/EDS chapter | not the right venue |
|  9 | MathOverflow / MSE               | (covered by #1–#3; no thread isolates the naturality of the net polynomial as a stated lemma)            | n/a  | —                                                | the fact is used implicitly, never highlighted |
| 10 | recent arXiv (≤5y)               | elliptic nets over commutative rings / valuations / CM (2604.05280, 2512.09601)                          | yes  | Xu 2604.05280 treats EDS over general rings; naturality used implicitly, never a headline | confirms the *general-ring* setting is standard; the `map_*` step is never a named result |

Protocol pass: WebSearch ran 3 distinct queries at different generality levels (specific Stange-net,
general EDS-naturality, named-source-paper). ChatGPT MCP recorded as down with fallback. Local refs,
nLab, nCatLab, Stacks, MathOverflow, arXiv each checked or `n/a` with reason.

### Literature summary (Phase 3)

Concept identified as: the **naturality of Stange's elliptic-net relation** `net` (= Junyan Xu's
"elliptic relation" `rel₄`, in the `d`-shifted/3-symmetric form) under a ring homomorphism — i.e.
`net` is a ℤ-polynomial expression in the values of `W`, hence natural in the coefficient ring.
Source paper positively identified: **Junyan Xu, *On Elliptic Sequences over Commutative Rings*
(arXiv:2604.05280)**, whose elliptic relations are *equivalent to Stange's elliptic-net axiom*
(arXiv:0710.1316). The project's `EllSequence.net`/`rel₄`/`addMulSub` is a Lean formalisation of that
relation.
Sources agree on the standard form: yes (the `net` formula is exactly Stange's relation). The
**naturality** itself is never stated as a named/citable theorem — it is the folklore "a ring hom
commutes with a polynomial expression," invoked implicitly whenever one base-changes an EDS / net
polynomial (here: specialising the **universal** net polynomial over `MvPolynomial Param ℤ` via
`aeval`).
Most general standard form: for any `CommRing` map `f : R → S`, `f` commutes with any ℤ-polynomial
combination of the `W` values; `net` is one such combination.
Generality dimensions where the literature varies:
  - coefficient ring: ℤ (classical EDS) up to **arbitrary commutative rings** (Xu 2604.05280); the
    project's `[CommRing R]` is already at the general end.
  - the map: literature speaks of ring homomorphisms generally; the project uses the **bundled-class**
    form `[RingHomClass F R S]`, *more* general than a bare `R →+* S` (covers `AlgHom`, `RingEquiv`,
    `MvPolynomial.aeval`'s ring-hom, etc.) — see Phase 4c.
Disagreement with the literature: none.

---

### Generality analysis — `map_net`

Literature-standard form (Phase 3): `f` commutes with the net expression, for `f` any ring hom and
`R`, `S` any commutative rings — exactly what the project states.

| # | Parameter / hypothesis                | Current Lean form                | Literature-standard form        | Weaker form exists? | Reason |
|---|---------------------------------------|----------------------------------|----------------------------------|---------------------|--------|
| 1 | `[CommRing R] [CommRing S]`          | commutative rings                | commutative rings                | NO                  | `net` mixes `+`,`−`,`×`; needs a (comm) ring on both sides. Already maximal. |
| 2 | `[FunLike F R S] [RingHomClass F R S] (f : F)` | bundled ring-hom class | "a ring homomorphism"            | NO (already maximal)| class form is **strictly more general** than `R →+* S`; the modern mathlib idiom. |
| 3 | `(W : ℤ → R)`                        | sequence on ℤ                    | sequence on ℤ                    | NO                  | `net` indices are genuine integers (`p−q`, `p+q+s`); domain is intrinsically ℤ. |
| 4 | `(p q r s : ℤ)`                      | four integer indices             | four integer indices             | NO                  | the relation is defined on integer index-tuples. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.**
Number of weakening opportunities found: 0. The project form is in fact *more* general than mathlib's
own analogous `map_normEDS` (which fixes `f : R →+* S`): `map_net` already uses `RingHomClass F R S`.
Proposed restatement: none needed.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Mathlib downstream |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                                  | no       | already a typeclass-driven `RingHomClass` hypothesis | — |
|  2 | sequences/metric → filters/topology?                                                       | no       | purely algebraic identity; no limits | — |
|  3 | construct an object → universal-property class?                                            | no/n.a.  | it's an equation about a fixed expression | — |
|  4 | set-with-closure → bundled substructure?                                                    | no       | no substructure here | — |
|  5 | vector-space/field-specific → weaken typeclasses?                                           | no       | already `CommRing`, the right level | — |
|  6 | 1-categorical → higher-categorical?                                                         | no       | "natural in the ring" is the whole content; no higher structure | — |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive structure?                                        | **partial** | Stange's *full* nets are `ℤⁿ → R` (this is the **rank-1** slice `ℤ → R`). A genuinely-general elliptic-net API would index by `ℤⁿ`. | would unify with multi-rank elliptic nets — but that is a **`net`-side** redesign, not a `map_net` change |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for `map_net` itself). The lemma already uses the contemporary
`RingHomClass` bundling. The only "modernisation" lever (row 7: `ℤ → R` ⟶ `ℤⁿ → R` full elliptic
nets) is a change to the **underlying `net` definition**, not to its naturality lemma — and is exactly
the kind of API-design decision that belongs to the `net`/`rel₄` upstreaming question, not here.
One-line reason: `map_net` is the `map_*` companion of `net`; its form is forced by `net`'s form.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equalities or typeclass-search paths).

---

### Mathlib search-status: `map_net`

[A] Lean-Finder       (semantic-index tool not loadable this session)             n/a: used authoritative grep of the *pinned* mathlib tree (`.lake/packages/mathlib`, rev 09b373db6e24) instead
[B] Loogle            (not loadable)                                              n/a: same
[C] LeanSearch        (not loadable)                                              n/a: same
[D] Grep mathlib src  `map_net`, `def net `, `def rel₄`, `def addMulSub`, `net_eq_rel`, `EllSequence`, `elliptic net`, `Stange` over `.lake/packages/mathlib/Mathlib/` | **no hits** for any
[E] Name pattern      `map_net` / `map_rel₄` / `map_addMulSub` across mathlib     | **no hits**

Searched for both:
  - the user's current form (`map_net`) — absent.
  - the literature-standard "naturality of the net polynomial" — absent (mathlib has **no** `net` /
    `rel₄` / `addMulSub` / `EllSequence`-namespace / elliptic-net concept at all; grep over the whole
    tree returned nothing for `namespace EllSequence`, `Stange`, `def net`).

**Decisive context (read directly from mathlib source).**
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` *does* carry the analogous `map_*` naturality
lemmas for **its own** EDS defs — `map_preNormEDS'`, `map_preNormEDS`, `map_complEDS₂`, `map_normEDS`,
`map_complEDS'`, `map_complEDS` (lines 510–545), **all `@[simp]`**, each proved by `simp [<def>,
apply_ite f]`, in a `section Map` with `variable (f : R →+* S)`. So the *pattern* (ship a `map_*` lemma
next to each EDS def) is mathlib-idiomatic. But mathlib's EDS file is built from bare sections
(`IsEllDivSequence`, `PreNormEDS`, `NormEDS`, `ComplEDS`, `Map`) and has **no `net`/`rel₄`/`addMulSub`
and no `EllSequence` namespace** — these are project-original Stange/Xu elliptic-net additions.
`map_net` is the `map_*` companion of a def that is not upstream.

Concluded: **not in mathlib** (five-method search exhausted via the authoritative pinned tree; the
literature-standard form is also absent because the parent `net` concept is absent).

---

### Call sites — `map_net`

Internal use count (this NagellLutz project, excluding the declaring line): **1**
- `EllipticDivisibilitySequence.lean:1467` — inside `net_normEDS`:
  `rw [normEDS_eq_aeval, show … = (⇑(aeval (Param.rec b c d))) ∘ universalNormEDS from rfl, ← map_net,
   universalNormEDS, IsEllSequence.normEDS.net, map_zero] …`
  (rewrites a `net` of a normalised EDS back through `aeval` to reduce to the **universal**
  `MvPolynomial Param ℤ` net — the exact use-case mathlib's own `map_normEDS` serves).

External-to-file / cross-project (the duplicated tracks the task flagged — verified by grep):
| Caller file:line                                                              | Usage pattern |
|-------------------------------------------------------------------------------|---------------|
| `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:140` | duplicate **definition** of `map_net` (forked copy) |
| `projects/HasseWeil/.../EllipticDivisibilitySequence.lean:958`                 | `rw [← EllSequence.map_net, universalNormEDS, h, map_zero]` (that copy's 1 use, in `net_normEDS`) |

So `map_net` is **duplicated** across the consolidation monorepo (NagellLutz + HasseWeil), each copy
with exactly **one** consumer — the universal-net reduction. No site re-derives the identity inline;
everyone calls `map_net`. Pattern = "K=1 internal use, but the analogous lemma is real `@[simp]` API in
mathlib's own EDS file" → leans NO-composable as a *standalone* decl, but the duplication + the mathlib
precedent make it a genuine "ships-with-`net`" candidate, hence the human question below.

Inline-derivation grep (was `f (net …) = net (f∘…)` re-derived without `map_net`?): (none found).

---

### Composition check (Phase 6)

Can `map_net` be derived from mathlib in ≤3 chained calls? **As stated against the project's `net`,
it cannot — because `net`, `rel₄`, `addMulSub` are not in mathlib.** The question only makes sense
relative to the project's own (non-mathlib) defs, where the proof is:

Attempt 1 (the actual project proof): `by simp_rw [net_eq_rel₄, map_rel₄]`
  - Project decls used: `net_eq_rel₄`, `map_rel₄` (and transitively `map_addMulSub`, then mathlib
    `map_add` / `map_sub` / `map_mul`).
  - Result: succeeds in 2 `simp_rw` rewrites. Unrolled to mathlib primitives it is pure
    `map_add` / `map_sub` / `map_mul` plumbing over the `net`/`rel₄`/`addMulSub` unfolds.
  - Notes: the canonical "ring hom commutes with a polynomial expression" — trivial *given* the defs,
    but the defs are project-local.

Conclusion: **NOT-COMPOSABLE from mathlib alone** (mathlib lacks `net`). It IS a ≤3-call composition
from the project's own elliptic-net API. The lemma's fate is therefore inseparable from whether that
API (`net`/`rel₄`/`addMulSub` + their `map_*` companions) is upstreamed.

---

## Verdict: `map_net`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): `net` = Stange's elliptic-net relation / Xu's "elliptic relation"
  (formula matched verbatim; source paper arXiv:2604.05280 positively identified). The naturality is
  folklore "ring hom commutes with a ℤ-polynomial expression," never a citable result.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — already uses `RingHomClass` (more general
  than mathlib's own `map_normEDS`, which fixes `R →+* S`). No weakening available.
- Mathlib search (Phase 5): **not in mathlib**; parent `net`/`rel₄`/`addMulSub` also absent; but
  mathlib *does* keep the analogous `map_*` lemmas (`map_normEDS`, …, all `@[simp]`) for its own EDS
  defs — the pattern is idiomatic.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (no `net`); a 2-call composition from the
  project's own (non-upstream) net API.

**Rationale:**

`map_net` is neither independently shippable to mathlib nor independently rejectable — its status is
**entirely downstream of the parent `net`/`rel₄`/`addMulSub` definitions**, which encode Stange's
elliptic-net relation (= Xu's elliptic relation, arXiv:2604.05280) and are *not* in mathlib. If those
defs are upstreamed, then `map_net` (together with `map_rel₄`, `map_addMulSub`) **should** ship with
them: mathlib's existing `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` already keeps exactly
this kind of `@[simp]` naturality lemma next to every EDS def (`map_preNormEDS`, `map_normEDS`,
`map_complEDS`, …), precisely so that base-changing to the universal polynomial ring via `aeval` is one
rewrite — which is the sole way `map_net` is used in both forks (line 1467 here). If the elliptic-net
API is *not* upstreamed (e.g. judged too niche, or pending a more general `ℤⁿ → R` multi-rank net
redesign per Phase 4c row 7), then `map_net` stays a project-local helper and there is nothing to add —
the bare identity is a trivial `map_add`/`map_mul` composition no one would add on its own.

The decision is a **mathematical-taste / API-scope** call the skill cannot make alone: *should mathlib
gain Stange/Xu's elliptic-net layer (`net`/`rel₄`/`addMulSub`) on top of its existing EDS file?* That
is the real question; `map_net` rides along with the answer. This is consistent with the sibling
verdicts already on file: `rel₄` and `net_eq_rel₄` → `YES-add-as-is`; the parent `net` → flagged
against mathlib's EDS framework; and the directly-analogous glue lemma `map_addMulSub` → also
`BORDERLINE-needs-human`. (Note: unlike mathlib's analogues, the project's `map_net` is **not** tagged
`@[simp]` — a one-line fix if upstreamed.)

Numbered questions (≤5):
  1. Should the **Stange/Xu elliptic-net API** (`EllSequence.net`, `rel₄`, `addMulSub`, `net_eq_rel₄`)
     be upstreamed into mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`? (yes ⇒
     `map_net` ships with it as `YES-add-as-is`, tagged `@[simp]`; no ⇒ `map_net` stays project-local
     and is `NO-composable-from-mathlib`.)
  2. If yes to (1): keep the net at the current **rank-1** generality (`ℤ → R`), or redesign to
     Stange's full **multi-rank** form (`ℤⁿ → R`) first (Phase 4c row 7)? (A redesign would change
     `map_net`'s signature accordingly.)
  3. Independently of mathlib: the project **duplicates** `map_net` (+ `net`/`rel₄`/`addMulSub`) across
     NagellLutz and HasseWeil. Should these be de-duplicated into one shared `Common/` module within
     AINTLIB now (an on-`main` cleanup ticket), regardless of the mathlib decision?

**Next action:** answer the questions above. If (1) = yes, treat `map_net` + `map_rel₄` +
`map_addMulSub` as a single PR riding on the `net`/`rel₄`/`addMulSub` definitions (add `@[simp]`, place
in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` beside the existing `map_*` EDS lemmas),
then re-run `/mathlibable map_net` to convert to `YES-add-as-is`. If (1) = no, the verdict collapses to
`NO-composable-from-mathlib` (de-duplicate the local copies into a shared AINTLIB helper per Q3; no
mathlib action).

---

## Next step

Answer the three numbered questions — chiefly Q1: *should mathlib gain the Stange/Xu elliptic-net layer
(`net`/`rel₄`/`addMulSub`)?* `map_net` is the naturality companion of `net` and ships with whatever
that answer is. mathlib precedent (its own `@[simp] map_normEDS` family) means: if `net` goes up,
`map_net` goes up with it (add `@[simp]`); if not, `map_net` is a trivial project-local helper.
