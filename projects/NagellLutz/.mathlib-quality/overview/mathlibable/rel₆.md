# /mathlibable report — `EllSequence.rel₆`

## Verdict (TL;DR)

**`NO-composable-from-mathlib`** — `rel₆` is a one-line reducible `abbrev`,
`addMulSub W k l * rel₄ W a b c d`, a ≤1-call product of two other project defs whose
defining equation (`rel₆_eq`) is `rfl`. It carries no independent mathematical content and
has no name in the literature: it is internal readable notation for the index-shuffling
reduction lemmas (`rel₆_eq₃`, `rel₆_eq₃'`, `rel₆_eq₁₀`, `addMulSub_sq_mul_rel₄_eq₉`). It is
not a standalone mathlib target. (Framing caveat: the whole `addMulSub`/`rel₄`/`rel₆` layer
is mathlib's own authors' in-flight upstream code — see Verdict — so even as part of that
fork, `rel₆` travels with `rel₄` as a convenience abbrev, never as an independent
contribution.)

---

### Baseline (Phase 0)
- lake build:               stale per task note — reasoning from source; decl elaborates in the green `main` build (CLAUDE.md).
- decl `EllSequence.rel₆`:   ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:302`
- kind:                      `abbrev` (reducible definition)
- has sorry:                 no
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and constructs normalised EDSs (`preNormEDS`, `normEDS`); the `addMulSub`/`rel₄`/`net` Stange-elliptic-net machinery proves `normEDS` is elliptic. `rel₆` is a helper of that machinery.

Qualified name **VERIFIED**: namespace `EllSequence` opens at line 90 and is not closed
before line 302, so the parsed `EllSequence.rel₆` is correct.

---

### Statement (Phase 1)

`EllSequence.rel₆` is a **definition** (an `abbrev`). For a commutative ring `R`, a sequence
`W : ℤ → R`, and six integers `k l a b c d`, it is

```lean
/-- The four-index elliptic relation multiplied by a two-index "coefficient". -/
abbrev rel₆ (k l a b c d : ℤ) : R := addMulSub W k l * rel₄ W a b c d
```

i.e. the **four-index elliptic relation `rel₄ W a b c d` multiplied by a single two-index
"coefficient" `addMulSub W k l`**, where

- `addMulSub W m n := W ((m+n).tdiv 2) * W ((m-n).tdiv 2)` (the half-index building block,
  using truncated division so `(-m).tdiv 2 = -(m.tdiv 2)`), and
- `rel₄ W a b c d := addMulSub W a b · addMulSub W c d − addMulSub W a c · addMulSub W b d
  + addMulSub W a d · addMulSub W b c` (the signed sum over the three pairings of four
  indices — the symmetric "elliptic relation").

The name "`rel₆`" simply counts the six index slots: two for the scalar coefficient (`k,l`)
plus four for the relation (`a,b,c,d`). Mathematically it is a **homogeneous degree-6 form**
in the values of `W` — but it is nothing more than the degree-4 `rel₄` form scaled by one
extra `addMulSub` factor.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (fully general; no field/characteristic/domain hypothesis).
- `(W : ℤ → R)` — the sequence.
- `(k l a b c d : ℤ)` — the six indices.

Hypotheses: none on the `abbrev` itself.

Conclusion (math): n/a — definition (an element of `R`).
Conclusion (Lean): `R`.

**Why it exists.** It is purely a readability device for the *index-reduction* lemmas that
follow it: `rel₆_eq₃`, `rel₆_eq₃'`, `rel₆_eq₁₀`, and `addMulSub_sq_mul_rel₄_eq₉`. These
express how a `rel₄` paired with a fixed-index coefficient decomposes into a signed sum of
other such `rel₄`-with-coefficient terms (the algebraic engine of "every Somos 4 is a Somos
k" — van der Poorten–Swart / Stange). Writing each summand as `addMulSub W _ _ * rel₄ W _ _ _ _`
would be unreadable; `rel₆ W _ _ _ _ _ _` is the abbreviation that makes those 10-term
identities legible.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: It is **not** a named mathematical object — it is a notational abbreviation
(`coefficient × rel₄`) introduced to state a handful of internal reduction lemmas. It is not
listed under `## Main definitions` (which names `IsEllSequence`, `preNormEDS`, `normEDS`,
`complEDS`, …, not `rel₆`), it is not named in any reference, and it is downstream of the
genuine primitives `addMulSub`/`rel₄`. Contrast `rel₄` itself, which is BIG (the namesake of
Xu 2026 and the keystone of the whole layer).

(Literature width is EXHAUSTIVE regardless; recorded here for framing only.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`addMulSub W k l * rel₄ W a b c d`).
One-liner verdict: **ONE-LINER** — and additionally it is declared `abbrev` (i.e.
`@[reducible]`), so it is *intended* to unfold transparently; the defining glue lemma
`rel₆_eq` is proved by `rfl`.

Exemption check (each row required):

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | **no**   | The opposite: it is `abbrev`/`@[reducible]` precisely so it *does* unfold to `addMulSub _ _ * rel₄ _ _ _ _` freely; `rel₆_eq` (`:= rfl`, `@[simp]`) and the proofs `simp only [rel₆_eq]` / `simp_rw [rel₆, rel₄]` rely on transparent unfolding. It is not a sealing barrier. |
| Avoid typeclass diamonds          | **no**   | Produces a term of `R`; introduces no instance/class; no search path involved. |
| Mark semantic intent / API name   | **no**   | The "API" it would anchor (`rel₆_eq₃`, `rel₆_eq₁₀`, …) is itself internal scaffolding for `rel₄_of_anti_oddRec_evenRec` → `rel₄_normEDS`; no external consumer depends on the *name* `rel₆` (it never leaves the file, and the HasseWeil copy is a sibling fork, not a consumer). It is convenience notation, not a stable public anchor. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** — a strong negative signal for standalone mathlib
inclusion. Carried into Phase 7: the verdict is biased toward NO-composable / NO-mathlib-has-it.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Ward elliptic divisibility sequence three-term recurrence … relation between four terms / elliptic net" | yes  | Ward 3-index relation; Stange net relation | arXiv:0710.1316; Wikipedia EDS; Colorado EDS formulary — the underlying `rel₄`/net relation, not `rel₆` |
|  2 | WebSearch (general form)         | "elliptic divisibility sequence general addition formula W(m+n)W(m−n) … Somos quadratic relation"       | yes  | `W_{m+n}W_{m−n}=W_{m+1}W_{m−1}W_n²−W_{n+1}W_{n−1}W_m²`; "every Somos 4 is a Somos k" | van der Poorten–Swart direct-coherence proof — the *reduction* `rel₆` serves, but `rel₆` itself is unnamed |
|  3 | WebSearch (named-after / aliases)| "'elliptic net' OR 'Somos' relation 'four index relation' coefficient multiply six index lemma formalization Lean" | no | — | no source names a "rel₆" / "six-index" object; the coefficient×relation product is a proof device, not a named entity |
|  4 | WebSearch (author / upstream PR) | "Junyan Xu / Angdinata EllipticDivisibilitySequence mathlib pull request elliptic relation … 2026"     | yes  | **arXiv:2604.05280, Xu (2026)** "elliptic relations" = `rel₄`; ITP 2023 group-law paper | confirms `rel₄`/`addMulSub` is the named layer (Xu 2026); `rel₆` is internal to its proofs, not in the paper's named API |
|  5 | ChatGPT MCP                      | standard name + generality of a `coefficient × rel₄` six-index product                                  | n/a  | — | **MCP down** per task note (fallbacks used); mirrors the sibling `rel₄.md` / `addMulSub₄` runs |
|  6 | Local references                 | `.mathlib-quality/references/` + `refs/NagellLutz/`                                                     | n/a  | (directories absent) | neither dir exists — recorded n/a |
|  7 | nLab                             | elliptic divisibility sequence / elliptic net                                                          | n/a  | (no page) | nLab has no EDS / elliptic-net entry (confirmed in sibling `rel₄.md` run) |
|  8 | nCatLab (if categorical)         | —                                                                                                      | n/a  | — | not a categorical concept (a recurrence/identity on ℤ → R) |
|  9 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | — | Stacks has no EDS / elliptic-net / Somos material |
| 10 | MathOverflow / MSE               | six-index / coefficient-times-relation elliptic identity                                                | no   | — | no MO/MSE thread on a "rel₆"-style product; only the underlying recurrences appear |
| 11 | recent arXiv (last 5 years)      | "On Elliptic Sequences over Commutative Rings"                                                          | yes  | **arXiv:2604.05280 (Xu, 2026)** — defines "elliptic relations" (`rel₄`); `rel₆` not a named object | the algebraic companion to this very Lean file; `rel₆` is an unexposed proof helper within it |
| 12 | Loogle / LeanSearch (mathlib)    | `EllSequence.rel₆`, `addMulSub`, six-index elliptic                                                     | no   | — | no hit (see Phase 5) |

Protocol passed: WebSearch ran 4 distinct queries at different generality levels (specific
3-index/net form; general Somos/addition-formula form; named-after/six-index aliases;
author/upstream-PR); ChatGPT MCP recorded `n/a` with the documented outage; local refs, nLab,
nCatLab, Stacks, MO/MSE, arXiv all checked/recorded.

### Literature summary (Phase 3)

Concept identified as: **no independent literature concept.** `rel₆` is the (named-in-the-paper)
"elliptic relation" `rel₄` — i.e. Xu 2026's symmetric quartic, equivalently Stange's elliptic-net
relation (arXiv:0710.1316) and Ward's 3-index relation — **multiplied by one extra half-index
coefficient `addMulSub W k l`**. The literature names the relation (`rel₄`/net) and studies the
*reductions* it satisfies ("every Somos 4 is a Somos k"; van der Poorten–Swart coherence). It does
**not** name the bookkeeping product `coefficient × relation`; that is an implementation device for
writing those reductions.

Sources agree on the standard form: **yes** for the underlying relation (`rel₄`/net/Ward); **n/a**
for `rel₆` (no source names it).
Most general standard form (of what `rel₆` is built from): a homogeneous quartic elliptic relation
over an arbitrary commutative ring (Xu 2026). `rel₆` is that, scaled by one `addMulSub` factor.
Disagreement with the literature: none — `rel₆` is simply not a literature object.

---

### Generality analysis — `EllSequence.rel₆`

Literature-standard form (Phase 3): there is no literature-standard "`rel₆`". Its components are
already at maximal generality (`rel₄`/`addMulSub` over an arbitrary `CommRing`, no hypotheses —
established in the sibling `rel₄.md`, verdict MAXIMALLY GENERAL).

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|--------------------------|---------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring         | (n/a — not a lit object)  | NO                  | already the floor; the product uses `+ − ·` only. Inherited from `rel₄`/`addMulSub`. |
| 2 | `(W : ℤ → R)`          | unconstrained sequence   | unconstrained             | NO                  | pointwise polynomial expression in `W`; no structure assumed. |
| 3 | `(k l a b c d : ℤ)`    | six integer indices      | (n/a)                     | NO                  | the six slots are exactly what the reduction lemmas need; not a weakenable hypothesis. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (inherits the `CommRing`, no-hypothesis floor of its
components `rel₄`/`addMulSub`).
Number of weakening opportunities found: **0**.
Cost of restatement: n/a — nothing to restate.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances? | no | — (already `[CommRing R]`; `W` is a bare hypothesis as it must be) | — |
|  2 | sequences/metric → filters/nets/topology? | no | — (algebraic identity, no limits/topology) | — |
|  3 | construct object → universal-property class? | no | — (it is `coefficient × relation`, no universal property) | — |
|  4 | set-with-closure-predicate → bundled substructure? | no | — (not a substructure) | — |
|  5 | vector-space/metric/field-specific → weaken typeclass? | no | — (already at `CommRing`) | — |
|  6 | 1-categorical → higher-categorical? | no | — (elementary commutative algebra) | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid? | no | — (the six ℤ indices are intrinsic to the EDS rank-1 reduction lemmas) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. One-line reason: `rel₆` is not a concept to re-formulate — it is a
one-line product abbreviation over the already-modern `rel₄`/`addMulSub` primitives. If anything,
the *modern* move is to NOT have a named `rel₆` at all and write `addMulSub _ _ * rel₄ _ _ _ _`
inline (which is exactly what `rel₆` unfolds to).

---

### Diamond / defeq risk — `EllSequence.rel₆`

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond            | none    | Produces a *term* of `R`; introduces no instance/class. No search path affected. |
| 2 | Reducibility leak            | low     | It **is** an `abbrev` (`@[reducible]`), so the body `addMulSub _ _ * rel₄ _ _ _ _` is exposed to defeq/unification everywhere. This is *intended* (the proofs unfold it), and the body is a shallow product of two existing defs, so the leak is benign — but it is a genuine reducibility exposure, unlike the sealed `def rel₄`. |
| 3 | Non-canonical unfolding      | low     | `rel₆_eq` is `@[simp]` (and `:= rfl`), so `simp` rewrites `rel₆ _ … → addMulSub _ _ * rel₄ _ …` routinely. Expected and controlled; not surprising given the abbrev intent. |
| 4 | Instance priority collision  | n/a     | Not an `instance`. |
| 5 | Universe-polymorphism issues | none    | `R : Type u`, result in `R`; no forced universe annotation. |
| 6 | Coercion ambiguity           | none    | No `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW** (a reducible `abbrev` that deliberately unfolds; benign shallow body). Top
risks: none HIGH. Note: the reducibility exposure is by design and is the reason a YES verdict is
*not* warranted — the construct's whole purpose is to be unfolded, i.e. inlined.

---

### Mathlib search-status: `EllSequence.rel₆`

[A] Lean-Finder       six-index elliptic relation / coefficient × four-index relation        no hits
[B] Loogle            `EllSequence.rel₆`, `addMulSub`, `?a * EllSequence.rel₄ ?W ?a ?b ?c ?d`  no hits — "unknown identifier 'EllSequence.rel₆'"
[C] LeanSearch        "elliptic relation times coefficient six index elliptic divisibility sequence"  no hits
[D] Grep mathlib src  `rel₆|rel₄|addMulSub|net|EllSequence` over `.lake/packages/mathlib/Mathlib/`  no hits (only the unrelated `IsEllSequence`/`IsEllDivSequence` predicates in the canonical EDS file; zero occurrences of `rel₆`/`rel₄`/`addMulSub`/`EllSequence`-namespace anywhere in the tree, incl. `AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`)
[E] Name pattern      `abbrev rel₆` / `def rel₆` in mathlib tree                               no hits

Searched for both the user's form (`rel₆`, `coefficient × rel₄`) and the literature-standard
component forms (`rel₄`/`addMulSub`; Stange's `net`; Ward's 3-index relation). Mathlib's
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines, current pin) defines
`IsEllSequence`/`IsDivSequence`/`IsEllDivSequence`/`preNormEDS`/`normEDS`/`complEDS` and **lists
"prove that normEDS satisfies IsEllDivSequence" as a still-open TODO**, but contains **no
`EllSequence` namespace and none of the `addMulSub`/`rel₄`/`rel₆`/`net` relational layer**.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the component forms). The whole
relational layer — including `rel₆` — is absent from published mathlib. (See Verdict for the
crucial framing: it is mathlib's own authors' code, in-flight via an upstream PR.)

---

### Call sites — `EllSequence.rel₆`

Internal use count: **11** occurrences inside the declaring live file
(`EllipticDivisibilitySequence.lean`), excluding the `abbrev` line 302 itself. All 11 are within
the same file; **no external-to-file consumer** (the HasseWeil
`Auxiliary/EllipticDivisibilitySequence.lean` and the dead `…Original.lean` are sibling forks of
the same source, not downstream users).

| Caller (`EllipticDivisibilitySequence.lean`):line | Usage pattern (one-line excerpt) |
|---------------------------------------------------|----------------------------------|
| rel₆_eq:304 (`@[simp]`, `:= rfl`)                 | `rel₆ W k l a b c d = addMulSub W k l * rel₄ W a b c d` — the **rfl glue lemma** |
| rel₆_eq₃:320 / rel₆_eq₃':328                      | `rel₆ W c d m n r c = rel₆ W m c n r c d − rel₆ W n c m r c d + rel₆ W r c m n c d` (and the `d`-fixed variant) |
| rel₆_eq₁₀:336                                     | the 10-term reduction: `rel₆ W c d m n r s = … − 2 * rel₆ W m d n r s c` |
| addMulSub_sq_mul_rel₄_eq₉:347,350 (comments)      | references `rel₆_eq₃'`/`rel₆_eq₁₀` to relate `(addMulSub W c d)² * rel₄ …` to `rel₆` terms |
| rel₄_fix₁_of_fix₂:429–432                         | `rw [mul_comm, ← rel₆_eq]; rw [rel₆_eq₃]; … simp only [rel₆_eq]` — uses `rel₆`/`rel₆_eq₃` then unfolds back |
| rel₄_of_fix₂:444                                  | `rw [mul_comm, ← rel₆_eq, rel₆_eq₁₀]; simp only [rel₆_eq]` — uses `rel₆_eq₁₀` then unfolds back |

Inline-derivation grep: the consumers (`rel₄_fix₁_of_fix₂`, `rel₄_of_fix₂`) **fold into `rel₆`
via `← rel₆_eq` and immediately unfold back via `simp only [rel₆_eq]`** — i.e. `rel₆` is used as
transient notation *within* a proof, then erased. This is the signature of a notation-convenience
abbreviation, not of a load-bearing named object: every use is bracketed by fold/unfold against the
`rfl` lemma `rel₆_eq`.

Composability signal: **all uses are intra-file, transient (folded then unfolded), and mediated by
the `rfl` lemma `rel₆_eq` → notation convenience, not real API. Strongly NO-composable-leaning.**

---

### Composition check (Phase 6)

Can `EllSequence.rel₆` be obtained from existing primitives in ≤3 calls?

Attempt 1: against the project's own primitives (the realistic case, since `addMulSub`/`rel₄`
are the in-flight upstream defs).
  - `rel₆ W k l a b c d` **is by definition** `addMulSub W k l * rel₄ W a b c d` — a single `*`.
  - The defining equation is `rel₆_eq : rel₆ W k l a b c d = addMulSub W k l * rel₄ W a b c d`,
    proved `:= rfl`.
  - Result: **succeeds in 0–1 calls** (it is a definitional product; `rfl` closes the equation).

Attempt 2: against *current* published mathlib.
  - Mathlib lacks both `addMulSub` and `rel₄`, so `rel₆` cannot be written from mathlib today.
  - But this is the same gap that `rel₄`/`addMulSub` themselves face — and those are being
    upstreamed. Once they land, `rel₆` is a one-line `abbrev` over them, i.e. trivially inline-able
    as `addMulSub _ _ * rel₄ _ _ _ _`.

Conclusion: **COMPOSABLE** — `rel₆` is a ≤1-call product (`addMulSub × rel₄`) with a `rfl`
defining equation. It is the textbook "wrapper that consumers fold/unfold" rather than a primitive
that must be added. Inlining it (writing `addMulSub _ _ * rel₄ _ _ _ _`, or keeping it as
purely local notation) costs nothing.

---

## Verdict: `EllSequence.rel₆`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): **no independent literature concept** — `rel₆` is the named
  "elliptic relation" `rel₄` (Xu 2026, arXiv:2604.05280; ≡ Stange net / Ward 3-index) scaled by
  one `addMulSub` coefficient. The literature names the *relation* and its *reductions*, never the
  `coefficient × relation` product.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (inherits `CommRing`, no-hypothesis floor of its
  components); Phase 4c found no modern idiom (the modern move is to inline it). One-liner check:
  **ONE-LINER WITHOUT-EXEMPTION**.
- Mathlib search (Phase 5): **not in mathlib** (5 methods + component forms; whole relational layer
  absent) — but mathlib also lacks its components, which are themselves in-flight upstream.
- Composition check (Phase 6): **COMPOSABLE** — definitionally `addMulSub W k l * rel₄ W a b c d`
  (≤1 call; defining equation `rel₆_eq` is `rfl`).
- Diamond/defeq risk (Phase 4.5): **LOW** (a reducible `abbrev` that deliberately unfolds — the
  reducibility exposure is exactly why it is inline-able, not addable).

**Rationale.**

`EllSequence.rel₆` is not a mathematical object that mathlib should hold as a named declaration; it
is a one-line `abbrev`, `addMulSub W k l * rel₄ W a b c d`, introduced solely so that the
index-shuffling reduction lemmas (`rel₆_eq₃`, `rel₆_eq₃'`, `rel₆_eq₁₀`, and the comment-annotated
`addMulSub_sq_mul_rel₄_eq₉`) can be written legibly. Its defining equation `rel₆_eq` is `@[simp]`
and `:= rfl`; every consumer (`rel₄_fix₁_of_fix₂`, `rel₄_of_fix₂`) folds into `rel₆` with
`← rel₆_eq` and unfolds straight back with `simp only [rel₆_eq]`, which is the exact behavioural
signature of transient proof notation rather than load-bearing API. The literature (Ward; Stange's
elliptic nets, arXiv:0710.1316; Xu's *On Elliptic Sequences over Commutative Rings*,
arXiv:2604.05280) names the underlying *relation* (`rel₄`) and studies its *reductions* ("every
Somos 4 is a Somos k"; van der Poorten–Swart coherence), but assigns no name to the
`coefficient × relation` product — because it is a bookkeeping device, not a concept. It is a
ONE-LINER WITHOUT-EXEMPTION (the `abbrev`/`@[reducible]` status is the opposite of a defeq-sealing
barrier; it anchors no externally-depended-upon name; it gates no instance), and it composes from
its neighbours in a single `*`. All four signals point the same way: this is `NO-composable`.

**Crucial framing (consistent with the sibling reports).** The entire `addMulSub`/`rel₄`/`rel₆`/`net`
layer in this file is **mathlib's own authors' code** — David Kurniadi Angdinata (author of mathlib's
existing `EllipticDivisibilitySequence.lean`, identical copyright header) and Junyan Xu — sitting in
NagellLutz as a fork that runs *ahead* of mathlib master and discharges its open `normEDS`-is-elliptic
TODO, and it is being **upstreamed via an open mathlib PR** (the elementary-algebraic group-law /
division-polynomial development). So the right action for `rel₆` is not "PR this abbrev to mathlib": it
travels inside that PR as a convenience abbreviation over `rel₄`/`addMulSub` (if the authors keep it at
all), or is inlined. Against *today's* mathlib it is non-writable only because its components are
likewise not-yet-merged — and once they land, `rel₆` is a ≤1-call composition. Either way the
five-bucket label scoped to "should AINTLIB add `rel₆` to mathlib as a standalone declaration" is
**NO** — and the precise reason is composability (it is `addMulSub × rel₄`), so **NO-composable-from-
mathlib** rather than NO-mathlib-has-it.

**WHY not (refactor-actionable).**
Mathlib does not currently have `rel₆`, but it should not gain it as an independent declaration:
`rel₆` is definitionally `addMulSub W k l * rel₄ W a b c d`, and its defining `rfl` lemma `rel₆_eq`
plus the fold/unfold usage pattern show it is pure notation. The building blocks are
`EllSequence.addMulSub` and `EllSequence.rel₄` (both in this same file, both part of the in-flight
upstream layer; both assessed in the sibling reports — `rel₄.md` = YES-add-as-is keystone,
`addMulSub` part of the same unit).

Mathlib building blocks: `EllSequence.addMulSub`, `EllSequence.rel₄`
(`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:94` and `:103`; the upstream
mathlib home will be `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`).
Composition sketch (≤1 line):
```lean
-- rel₆ W k l a b c d  ≡  (by definition / rel₆_eq)
example : rel₆ W k l a b c d = addMulSub W k l * rel₄ W a b c d := rfl
```
Call sites in our project (from Phase 6.0): **11**, all intra-file, all transient.
Refactor plan (only if one wanted to remove `rel₆` from the upstreamed surface): at each of the 11
sites, `rel₆ W k l a b c d` is replaced by `addMulSub W k l * rel₄ W a b c d`; the reduction lemmas
`rel₆_eq₃`/`rel₆_eq₃'`/`rel₆_eq₁₀` would be restated in those unfolded terms (their proofs are
`simp_rw [rel₆, rel₄]; ring`, which already unfold `rel₆`, so they survive verbatim modulo the name).
**However**, since this whole file is in-flight upstream code by the mathlib authors, the realistic
action is *not* to refactor here but to let the upstream PR decide whether to keep `rel₆` as a local
convenience abbreviation — and to NOT treat `rel₆` as a separate AINTLIB→mathlib contribution.
Next action: keep `rel₆` as the file's internal notation (it is harmless and improves readability of
`rel₆_eq₁₀`); do not PR it standalone; let it ride with the `rel₄`/`addMulSub` upstream PR (or be
inlined there at the authors' discretion).

---

## Next step

Do not propose `EllSequence.rel₆` as a standalone mathlib addition. It is a one-line reducible
`abbrev` = `addMulSub W k l * rel₄ W a b c d` (≤1-call composition, `rfl` defining equation, transient
fold/unfold usage) with no independent name in the literature. It belongs *inside* the in-flight
upstream PR of the `addMulSub`/`rel₄` relational layer (David Angdinata / Junyan Xu, arXiv:2604.05280)
as optional internal notation, or inlined — never as a separate contribution. The actionable verdict:
**NO-composable-from-mathlib**; leave it as file-local notation and let it travel with `rel₄`.
