# /mathlibable report — `EllSequence.Rel₄OfValid`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz theorem; elliptic
> curves; division polynomials; elliptic divisibility sequences).
> Declaration source: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:417`.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale, per task brief); reasoned from source.
- decl `EllSequence.Rel₄OfValid`: ✓ resolved at `…/EllipticDivisibilitySequence.lean:417`
  (qualified name = `EllSequence.Rel₄OfValid`; `namespace EllSequence` opens at line 90,
  no nested namespace at the decl — the `section Rel₄OfValid` at line 412 is a *section*,
  not a namespace, so it does **not** prefix the name).
- kind:                      `def` (returns `Prop`)
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences — defines EDS and constructs
  normalised EDSs from initial terms." This file is a **fork/extension of
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`** that adds the entire
  `addMulSub`/`rel₄`/`net`/`Rel₃`/`Rel₄OfValid` apparatus in order to *prove* `normEDS` is an
  EDS (`isEllDivSequence_normEDS`, the file's Main statement — which mathlib lists only as a TODO).

---

### Statement (Phase 1)

`Rel₄OfValid W a b c d` is a **definition of a guarded proposition** — the four-index elliptic
relation asserted only on *valid* index tuples:

> For a sequence `W : ℤ → R` over a commutative ring `R`, and integers `a b c d`:
> *if* `a, b, c, d` all have the same parity *and* they are nonnegative and strictly
> decreasing (`0 ≤ d < c < b < a`), *then* the four-index elliptic relation
> `rel₄ W a b c d = 0` holds.

In the literature (Ward / Stange / Xu) the underlying relation is
`E(a,b,c,d): h_{a+b}h_{a−b}h_{c+d}h_{c−d} = h_{a+c}h_{a−c}h_{b+d}h_{b−d} − h_{b+c}h_{b−c}h_{a+d}h_{a−d}`,
asserted for `a > b > c > d ≥ 0`. Here it is encoded via `rel₄ W a b c d := addMulSub W a b *
addMulSub W c d − addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c`, with
`addMulSub W m n := W ((m+n).tdiv 2) * W ((m−n).tdiv 2)` (so the half-sum/half-difference indices
are realised; `tdiv` is used so sign lemmas hold unconditionally).

Variables / typeclasses (Lean side):
- `R : Type*` `[CommRing R]` — the coefficient ring (most general scalar setting; ✓).
- `W : ℤ → R` — the sequence (a bare function; ✓).
- `a b c d : ℤ` — the four indices.

Hypotheses (folded into the `Prop` as antecedents of an implication):
- `HaveSameParity₄ a b c d` — `a.negOnePow = b.negOnePow ∧ … = c … = d` (all same parity).
- `StrictAnti₄ a b c d` — `0 ≤ d ∧ d < c ∧ c < b ∧ b < a` (nonneg + strictly decreasing).

Conclusion (math): the elliptic relation vanishes on the valid tuple.
Conclusion (Lean): `Prop` — namely `HaveSameParity₄ a b c d → StrictAnti₄ a b c d → rel₄ W a b c d = 0`.
This is a `def` (it *names* a proposition); it is not itself a proved theorem.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a proof-internal scaffolding `def` (a guarded relation used as the carrier of one
induction). Not a named mathematical structure, not a person/place-named theorem, and not a
"Main definition" of the file (it is absent from the docstring's `## Main definitions` list,
lines 41–51). It exists only to state and run the induction behind `rel₄_of_anti_oddRec_evenRec`.

(Literature width is EXHAUSTIVE regardless; recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`HaveSameParity₄ a b c d → StrictAnti₄ a b c d → rel₄ W a b c d = 0`).
One-liner verdict: **ONE-LINER** (a `def` whose body is a single implication-chain `Prop`).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                | no       | No downstream proof depends on the RHS *not* unfolding; on the contrary the in-file lemmas (`rel₄_fix₁_of_fix₂` etc.) repeatedly destructure it as `fun same anti ↦ …`, i.e. they *do* unfold it. It is an abbreviation-for-readability, not a sealed barrier. |
| Avoid typeclass diamonds         | no       | `Prop`-valued; introduces no instance and no `Mul`/`Zero`/`AddCommMonoid` search path. |
| Mark semantic intent / API name  | no       | No consumer outside the declaring file (Phase 6.0: K=0 external). The name is convenient locally but is not a stable API surface any other development depends on. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION**. Carried into Phase 7: biases strongly toward a NO verdict.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "EDS four-index relation Ward addMulSub net Stange elliptic net"                               | yes  | `E(a,b,c,d): h_{a+b}h_{a−b}h_{c+d}h_{c−d} = h_{a+c}h_{a−c}h_{b+d}h_{b−d} − h_{b+c}h_{b−c}h_{a+d}h_{a−d}`, for `a>b>c>d≥0` | exact match to `rel₄`; "relations E(a,b,c,d) are equivalent to Stange's elliptic-net axiom" |
|  2 | WebSearch (general / proof form) | "Stange elliptic nets four-index quadratic relation … normalised EDS satisfies … induction"   | yes  | "standard EDSs are shown to be elliptic … using intricate implications among elliptic relations" | confirms the induction-over-relations proof strategy this file formalises |
|  3 | WebSearch (named-after / source) | "arXiv 2604.05280 On Elliptic Sequences over Commutative Rings Angdinata … valid indices"      | yes  | same `E(a,b,c,d)` family | **source paper located** — author **Junyan Xu**; project naming (`net`, `rel₄`, "Stange", "characteristic 3") tracks this paper |
|  4 | ChatGPT MCP                      | (self-contained Q on whether "relation-restricted-to-valid-tuples" is a named object / has a more general form) | n/a | — | Codex MCP errored (stdin read failure); fallback = channels 1–3 + 9 + arXiv fetch, which already resolve the question |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "elliptic"/"Ward"/"relation"                          | n/a  | (no references dir for NagellLutz) | dir absent — recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                              | n/a  | — | nLab has no EDS/elliptic-net entry; not a category-theoretic object. n/a with reason. |
|  7 | nCatLab                          | —                                                                                              | n/a  | — | not a categorical concept. |
|  8 | Stacks Project                   | —                                                                                              | n/a  | — | EDS recurrences are not a Stacks (scheme-theoretic AG) topic. |
|  9 | MathOverflow / Math.SE           | (covered by WebSearch #1–#3 result set: Wikipedia "Elliptic divisibility sequence", arXiv)     | yes  | Wikipedia confirms Ward's quartic recurrence; no separate name for the valid-tuple guard | — |
| 10 | recent arXiv (≤5 yr)             | arXiv 2604.05280 (Xu), 2512.09601, 2102.07573, 1909.12654                                      | yes  | all use the relation `E(a,b,c,d)` with `a>b>c>d≥0` as the *domain*; none names the guarded predicate | — |
| 11 | arXiv source fetch               | `arxiv.org/abs/2604.05280` abstract                                                            | yes  | Xu, "elliptic relations" = homogeneous quartic family; proof "purely algebraic … without complex analysis" | confirms author + that the index constraints are the assertion domain, not a named sub-object |

The protocol passes: WebSearch ran 3 queries at distinct generality levels; ChatGPT MCP attempted
(errored — fallbacks cover it); local refs checked (n/a); nLab/nCatLab/Stacks/MathOverflow/arXiv
each checked or recorded n/a with reason.

### Literature summary (Phase 3)

Concept identified as: the **four-index elliptic relation** `E(a,b,c,d)` of an elliptic
sequence (Ward; Stange's elliptic-net axiom; Xu, *On Elliptic Sequences over Commutative Rings*,
arXiv 2604.05280). The Lean `rel₄`/`net`/`addMulSub` names map directly onto this paper.

Sources agree on the standard form: **yes** — the relation `E(a,b,c,d)` is the named object; the
constraints `a > b > c > d ≥ 0` (and implicit same-parity, via the half-index divisions) are the
**domain over which the relation is asserted**, *not* a separately-named mathematical object.

Most general standard form: the relation itself, over an arbitrary commutative ring, for valid
(nonneg, decreasing, same-parity) tuples — which is exactly what the file's `rel₄` (general object)
plus the `Rel₄OfValid` guard (the assertion domain) encode.

Disagreement with the literature: **none**. `Rel₄OfValid` faithfully encodes "the relation holds
on valid tuples". Crucially, **the literature gives no name** to "the relation guarded by its
validity domain" as a standalone reusable notion — that packaging is a Lean proof-engineering
choice (it is the induction's carrier), not a mathematical concept anyone cites.

---

### Generality analysis — `EllSequence.Rel₄OfValid` (Phase 4)

Literature-standard form: the elliptic relation `E(a,b,c,d)` over a commutative ring, asserted for
valid index tuples.

| # | Parameter / hypothesis        | Current Lean form                  | Literature-standard form        | Weaker form exists? | Reason |
|---|-------------------------------|------------------------------------|---------------------------------|---------------------|--------|
| 1 | `[CommRing R]`               | commutative ring                   | commutative ring                | NO                  | already the maximal natural setting for these quartic relations; the paper is "over commutative rings". |
| 2 | `W : ℤ → R`                  | bare ℤ-indexed sequence            | ℤ-indexed sequence              | NO                  | EDS are intrinsically ℤ-indexed; nothing to weaken. |
| 3 | `HaveSameParity₄`/`StrictAnti₄` antecedents | implication antecedents | the validity domain `a>b>c>d≥0`, same parity | n/a              | these are *the domain*, not strength knobs — weakening them would change the statement's meaning, not generalise it. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for what it encodes — the relation over a general
`CommRing`, on the literature's exact validity domain). K = 0 weakening opportunities.

Note this does **not** push toward YES: "maximally general" here only means the *scalar/index*
setting is already maximal. The decl's problem for mathlib is not generality but that it is a
**proof-scoped guard predicate with no standalone mathematical content**, not that it is too narrow.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
| 1 | bundled hyps → typeclasses/instances? | no | — | `HaveSameParity₄`/`StrictAnti₄` are runtime index predicates on a fixed tuple, not a typeclass-able structure. |
| 2 | sequences/metric → filters/topology? | no | — | finite algebraic identity; no limiting process. |
| 3 | construction → universal-property class? | no | — | it is an asserted equation, not a constructed object. |
| 4 | set-with-closure → bundled substructure? | no | — | no closure/lattice structure here. |
| 5 | vector-space/field-specific → weaker typeclass? | no | — | already `CommRing`, the natural floor. |
| 6 | 1-categorical → higher-categorical? | no | — | not categorical. |
| 7 | concrete index ℕ/ℤ/ℝ → general monoid/group? | no | — | the relation is genuinely about ℤ-indices with parity; generalising the index type is not a recognised move and the proof (parity bookkeeping, `negOnePow`) depends on ℤ. |

Modern idiom available: **no**. One-line reason: this is a bespoke induction-carrier predicate
over fixed ℤ-indices; there is no contemporary mathlib idiom that re-expresses "the relation
guarded by its validity domain" as a more composable object — the *general* object (the relation
`rel₄`) is already the separately-defined, idiomatic piece.

### Diamond / defeq risk — (Phase 4.5)

n/a — kind is `def` returning `Prop`. It introduces no instance, no coercion, no reducibility
attribute, and no universe constraint beyond `R`'s. (For completeness: a `Prop`-valued
non-`@[reducible]` `def` carries no diamond/defeq risk; the in-file proofs unfold it explicitly
via pattern-matching lambdas, which is intended.) Overall risk: **NONE**.

---

### Mathlib search-status: `EllSequence.Rel₄OfValid` (Phase 5)

[A] Lean-Finder       "elliptic relation valid indices", "four index relation EDS"  — no hits (index doc reasoned)
[B] Loogle            `Rel₄OfValid`, `_ → _ → rel₄ _ _ _ _ _ = 0` shape             — no hits (name absent; the whole rel₄ apparatus is absent from mathlib)
[C] LeanSearch        "elliptic relation holds for decreasing same-parity indices"   — no hits
[D] Grep mathlib src  `Rel₄OfValid` / `OfValid` / `StrictAnti₄` / `HaveSameParity₄` / `addMulSub` / `rel₄` / `Rel₃` / `\bnet\b` / `isEllDivSequence_normEDS` over `.lake/packages/mathlib/Mathlib/` | **zero matches for every term** — the pinned mathlib (`d90090f`, May 2026) EDS file (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, 547 lines) contains *none* of this machinery |
[E] Name pattern      `grep -rn "EllSequence"` mathlib tree                          — no `EllSequence` namespace in mathlib at all

Searched for both: the user's form (`Rel₄OfValid`) **and** the literature-standard object (the
elliptic relation `E(a,b,c,d)` / `rel₄` / Stange-net axiom). Neither is in mathlib.

Decisive corroboration: mathlib's own EDS file lists, under `## Main statements`,
`* TODO: prove that normEDS satisfies IsEllDivSequence` and
`* TODO: prove that a normalised sequence satisfying IsEllDivSequence can be given by normEDS`.
So mathlib has **not** yet proved `normEDS` is an EDS — and `Rel₄OfValid` is precisely a cog in the
project's machine for discharging that TODO. It is unambiguously new relative to mathlib.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard form). The
broader `rel₄`/`net` apparatus is also absent.

---

### Call sites — `EllSequence.Rel₄OfValid` (Phase 6.0)

Internal use count (within the project, excluding the declaring file): **K = 0**.
External-to-file callers: **0 distinct files**.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none outside the declaring file) | — |

All 9 occurrences are inside `EllipticDivisibilitySequence.lean` itself (lines 412, 417, 421, 428,
443, 458, 459, 479, 507). The consumers are the sibling lemmas of the same induction:
`rel₄_fix₁_of_fix₂`, `rel₄_of_fix₂`, `rel₄_of_min₂`, and the main result
`rel₄_of_anti_oddRec_evenRec` (which runs `Int.strongRec` with `Rel₄OfValid` as the motive).

Inline-derivation grep: the only *other* place the same `def` appears verbatim is
`…/EllipticDivisibilitySequenceOriginal.lean:396` — a **stale verbatim duplicate** of the whole
file (1572 lines, byte-identical `Rel₄OfValid` def, **imported nowhere** in the project). That is a
dedup artifact, not an independent consumer.

Signal (per Phase 6.0.1 table): **K = 0 internal uses outside the declaring file, no external
re-derivation** → this is a *file-private induction carrier*, not a reusable API. Combined with the
Phase 2b `ONE-LINER WITHOUT-EXEMPTION` finding, the case for NO is strong.

### Composition check (Phase 6)

Can `Rel₄OfValid W a b c d` be expressed from mathlib in ≤3 calls?

There is nothing to "derive" — it is a `def` of a proposition, not a lemma with a proof obligation.
The right framing: *does mathlib supply the pieces so this predicate need not be a named mathlib
def?* Yes, trivially: the predicate is literally
`HaveSameParity₄ a b c d → StrictAnti₄ a b c d → rel₄ W a b c d = 0`, i.e. an `→`-chain over
already-local notions. Anyone needing it inlines the implication at the (one) use site. It is glue
notation, the kind of thing that lives **inside** a proof/file, not a library export.

Conclusion: **COMPOSABLE / INLINE-ABLE** — it is a local abbreviation for an implication, with the
general object (`rel₄`) and the index predicates already to hand. No standalone mathlib def is warranted.

---

## Verdict: `EllSequence.Rel₄OfValid`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the named object is the elliptic relation `E(a,b,c,d)` (Ward /
  Stange / Xu arXiv 2604.05280); the validity constraints are its *assertion domain*, never a
  separately-named reusable notion. `Rel₄OfValid` = "relation guarded by its domain", a Lean
  packaging choice.
- Generality (Phase 4): MAXIMALLY GENERAL in scalars/indices, but that is not the issue — there is
  no more-general *standard* form, and Phase 4c found no modern idiom; it is simply not a
  standalone concept.
- Mathlib search (Phase 5): not in mathlib; the entire `rel₄` apparatus is absent and mathlib's EDS
  file flags `normEDS`-is-an-EDS only as a TODO.
- Composition (Phase 6): COMPOSABLE/INLINE-ABLE — a one-line implication over the already-defined
  general relation `rel₄` and the index predicates; K = 0 external consumers.

**Rationale:**

`Rel₄OfValid` is not a mathematical object mathlib would carry; it is **proof-engineering glue** —
a one-line `Prop`-valued `def` that bundles two side-conditions (`HaveSameParity₄`, `StrictAnti₄`)
as the antecedents of "`rel₄ = 0`" so that this guarded statement can serve as the **motive of the
strong induction** in `rel₄_of_anti_oddRec_evenRec` (the file's route to `isEllDivSequence_normEDS`).
The literature is unambiguous that the *relation* `E(a,b,c,d)` is the named thing and the
constraints `a>b>c>d≥0` are merely the domain on which it is asserted; no source names or reuses
"the relation restricted to its valid domain" as an object. It is a one-liner with no Phase-2b
exemption (the in-file proofs unfold it freely, it guards no defeq, anchors no instance, and has no
stable-API consumers), and its call-site profile is K = 0 outside the declaring file — the textbook
signature of a file-private helper. So even though it is genuinely *absent* from mathlib, the right
action is not to upstream it: it should stay inside the proof (or be inlined), while the genuinely
mathlib-worthy artifacts in this file are the *general* objects and the *theorems* — `rel₄`/`net`
(if upstreamed at all) and above all the main result `isEllDivSequence_normEDS` /
`rel₄_of_anti_oddRec_evenRec`, which discharge mathlib's standing TODO. `Rel₄OfValid` rides along as
private scaffolding of that proof, not as an independent declaration.

(Note on bucket choice: this is **not** NO-mathlib-has-it — mathlib provably lacks it. The
distinction that matters for the refactor is that it is *composable/inline-scoped glue*, so it
should never be a separate mathlib `def`; if the surrounding proof is upstreamed, `Rel₄OfValid`
becomes a `let`/local notion inside that proof, not a public symbol.)

**WHY not (refactor-actionable):**
Mathlib has the building blocks for the *statement* — the implication arrow, and (were the apparatus
upstreamed) the general relation `rel₄` plus the index predicates. The predicate is the 0-call
composition "antecedents `→` `rel₄ = 0`". It is needed only as the induction carrier of one theorem.

- Mathlib building blocks: plain `→` over `EllSequence.rel₄` (general object, same file, line 103)
  and the index predicates `EllSequence.StrictAnti₄` (line 207) / `EllSequence.HaveSameParity₄`
  (line 210). (None of these are *in* mathlib yet either — they would be upstreamed, if at all,
  alongside the main theorem, not as independent decls.)
- Composition sketch (the def is its own ≤1-line expansion):
  ```lean
  -- `Rel₄OfValid W a b c d` is definitionally:
  example : Prop := HaveSameParity₄ a b c d → StrictAnti₄ a b c d → rel₄ W a b c d = 0
  ```
- Call sites in our project (from Phase 6.0): **K = 0** outside the declaring file (9 in-file uses;
  plus 1 stale duplicate copy in `EllipticDivisibilitySequenceOriginal.lean`).
- Refactor plan:
  1. **Do not** propose `Rel₄OfValid` as a standalone mathlib declaration.
  2. If/when the proof of `isEllDivSequence_normEDS` is upstreamed, fold `Rel₄OfValid` into that
     development as a *file-local* abbreviation (it can stay a private `def`/`let` used only by
     `rel₄_fix₁_of_fix₂` / `rel₄_of_fix₂` / `rel₄_of_min₂` / `rel₄_of_anti_oddRec_evenRec`).
  3. **Project hygiene (independent of mathlib):** delete the stale verbatim duplicate
     `EllipticDivisibilitySequenceOriginal.lean` (imported nowhere; a `lane:cleanup` dedup ticket).

**Next action:** keep `Rel₄OfValid` as in-file induction scaffolding; do not upstream it on its own.
Direct mathlib-upstreaming effort at the *theorems* in this file — chiefly the main result
`rel₄_of_anti_oddRec_evenRec` / `isEllDivSequence_normEDS`, which fills mathlib's documented EDS
TODO — and assess `rel₄` / `net` separately as the candidate *general* definitions. Separately,
file a cleanup ticket to remove the duplicate `EllipticDivisibilitySequenceOriginal.lean`.

---

## Next step

Keep `Rel₄OfValid` as proof-internal glue (inline / file-local); it is not a standalone mathlib
declaration. Channel upstreaming effort to the surrounding theorems (`isEllDivSequence_normEDS` /
`rel₄_of_anti_oddRec_evenRec`) that discharge mathlib's EDS TODO, and to the *general* objects
`rel₄` / `net`. File a `lane:cleanup` ticket to delete the stale duplicate
`EllipticDivisibilitySequenceOriginal.lean`.
