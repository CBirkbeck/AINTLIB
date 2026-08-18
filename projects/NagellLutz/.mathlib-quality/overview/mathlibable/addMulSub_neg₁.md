# /mathlibable report — `EllSequence.addMulSub_neg₁`

## Verdict (TL;DR)

**`NO-composable-from-mathlib`** — a one-line structural lemma about the project-local `def`
`EllSequence.addMulSub` (which is itself absent from mathlib). It cannot be a standalone mathlib
contribution (its statement names `addMulSub`), and against today's mathlib it is a **2-call inline**:
`rw [addMulSub, addMulSub, mul_comm]; abel_nf`. It rides along with the `EllSequence` elliptic-relation
layer whose upstreaming is the proper unit of decision (parent `addMulSub.md`).

- **Qualified name:** `EllSequence.addMulSub_neg₁`  *(verified — see Phase 0)*
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:188`
- **Parent def:** `EllSequence.addMulSub` (line 94)
- **Date:** 2026-06-18

---

### Baseline (Phase 0)
- lake build:               stale per task note — reasoning from source; the decl elaborates in the green `main` build per CLAUDE.md.
- decl `EllSequence.addMulSub_neg₁`:  ✓ resolved at `…/EllipticDivisibilitySequence.lean:188`
- kind:                      `lemma`
- has sorry:                 no
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and normalised EDSs (`preNormEDS`, `normEDS`); the `addMulSub`/`rel₄`/`net` Stange-net machinery proves `normEDS` is elliptic. This file is a **fork-extension** of `Mathlib.NumberTheory.EllipticDivisibilitySequence`, adding the elliptic-net relation layer (not yet upstream).

**Qualified-name verification.** The file opens `namespace EllSequence` at line 90 and closes it
(`end EllSequence`) at line 597; line 188 is inside that block with no intervening namespace (the next
sub-namespace `HaveSameParity₄` opens at line 216). So the parsed name `EllSequence.addMulSub_neg₁` is
**correct**. Kind is `lemma`, so Phase 4.5 (diamond/defeq risk) is **n/a**.

---

### Statement (Phase 1)

```lean
namespace EllSequence
variable {R : Type u} [CommRing R] (W : ℤ → R)

lemma addMulSub_neg₁ (m n : ℤ) : addMulSub W m (-n) = addMulSub W m n := by
  rw [addMulSub, addMulSub, mul_comm]; abel_nf
```

where `addMulSub W m n := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)` (truncated division by 2).

In prose: the basic elliptic-relation building block `addMulSub W m n = W((m+n)/2)·W((m−n)/2)` is
**invariant under negating its *second* argument**: `addMulSub W m (−n) = addMulSub W m n`. Unlike its
sibling `addMulSub_neg₀` (negate the *first* argument), this holds **for an arbitrary `W : ℤ → R` with
no hypothesis whatsoever** — because negating `n` maps the index pair `(m+n, m−n) ↦ (m−n, m+n)`, i.e.
it merely *swaps the two factors*. The proof is therefore pure commutativity: unfold `addMulSub`
twice, swap the product with `mul_comm`, and let `abel_nf` discharge the index bookkeeping
`m + (−n) = m − n` and `m − (−n) = m + n` inside the `tdiv 2` arguments.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (fully general; commutativity is what makes the swap legal).
- `(W : ℤ → R)` — the sequence (a bare function; **no** EDS / oddness / divisibility hypothesis).

Hypotheses:
- `(m n : ℤ)` — the two indices. **No structural hypothesis on `W`** — this is the crucial contrast
  with `addMulSub_neg₀`, which requires `neg : ∀ k, W(-k) = -W k`.

Conclusion (math): `addMulSub W m (−n) = addMulSub W m n`.
Conclusion (Lean): an equation in `R` (`addMulSub W m (-n) = addMulSub W m n`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a structural helper lemma recording a trivial (commutativity) symmetry of the internal
building block `addMulSub` under negating its second index. Not a named theorem, not a `## Main
results` entry, not person/place-named. (Literature width below is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → the one-liner def check is **n/a**. (For the
record, the *proof* is a single `rw …; abel_nf` line — bears on golf, not on mathlibability.)

---

### Literature search table — EXHAUSTIVE protocol

The parent machinery (`addMulSub`/`rel₄`/`net`, Stange nets, Ward's relation, Angdinata–Xu
arXiv:2604.05280) was already exhaustively searched in the sibling reports `addMulSub.md`, `rel₄.md`,
`net.md`, `net_add_sub_iff.md`, `addMulSub_neg₀.md` in this directory; that search is incorporated by
reference. The rows below target *this lemma's specific content*: the commutativity/second-index-
negation symmetry of the half-index building block.

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found                                                          | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence W(m+n)W(m-n) symmetry negate index product building block"              | partial | the *product* `W(m+n)W(m−n)` is the Ward-recurrence LHS; its `n ↦ −n` symmetry is the elementary fact `W(m−n)W(m+n) = W(m+n)W(m−n)` (commutativity) | The underlying product is standard (Ward 1948; Silverman; Stange); a *named* "negate-2nd-arg invariance of a half-index block" appears nowhere |
|  2 | WebSearch (general form)         | "Stange elliptic net symmetry W(v) building block commutativity half index"                              | no   | Stange's net recurrence is the four-term `W(p+q+s)W(p−q)W(r+s)W(r)+…(cyc)=0`; no half-index 2-term `addMulSub` block | No source defines a named `W((m±n)/2)` building block, hence none names its symmetries |
|  3 | WebSearch (named-after / aliases)| "sign of an elliptic divisibility sequence symmetry properties of terms"                                  | partial | arXiv:math/0402415 *The sign of an EDS* studies the sign *pattern*; the elementary `W₋ₙ=−Wₙ` and `W(m+n)W(m−n)` symmetry are background folklore | The named result in this neighbourhood is the sign pattern, not this commutativity bookkeeping |
|  4 | ChatGPT MCP                      | "standard name for invariance of W((m+n)/2)W((m−n)/2) under negating the second index"                    | n/a  | —                                                                            | **MCP down** this session (recorded failure mode in sibling reports); fell back to WebSearch + arXiv/Wikipedia + domain reasoning per skill fallback |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/` + `refs/NagellLutz/`                                   | n/a  | (directories absent)                                                         | confirmed absent this run — recorded n/a |
|  6 | nLab                             | elliptic divisibility sequence / elliptic net                                                            | n/a  | (no page; 404 per sibling reports)                                            | nLab has no EDS / elliptic-net entry |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                                                            | not a categorical concept (an elementary identity in `ℤ → R`) |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                                                            | Stacks has no EDS / elliptic-net material |
|  9 | MathOverflow / MSE               | symmetry / commutativity of elliptic-sequence half-index product                                         | no   | —                                                                            | no thread on this specific helper identity; it is trivial folklore (commutativity) |
| 10 | recent arXiv (last 5 years)      | Angdinata–Xu, *On Elliptic Sequences over Commutative Rings* (arXiv:2604.05280)                           | yes  | the paper behind this file; `addMulSub` is its internal scaffolding           | confirms the *layer* is current research; `addMulSub_neg₁` is internal bookkeeping within it |
| 11 | Loogle / LeanSearch (mathlib)    | `addMulSub`, `EllSequence`, half-index product negate-second-arg                                         | no   | —                                                                            | no decl of this name/shape upstream (see Phase 5) |

Protocol passed: WebSearch ran ≥3 distinct queries at different generality levels (the product's
`n ↦ −n` symmetry; the Stange-net generalisation; the named "sign of an EDS" neighbourhood); ChatGPT
MCP attempted and recorded `n/a` with its failure mode; local refs, nLab, nCatLab, Stacks, MO/MSE,
arXiv, and the mathlib index were each checked or `n/a`-justified.

### Literature summary (Phase 3)

Concept identified as: there is **no named literature concept** for `addMulSub` or for its
second-argument-negation symmetry. The *underlying* product `W(m+n)·W(m−n)` is standard — it is the
left-hand side of the **Ward recurrence** for EDS / division polynomials (Ward 1948; Silverman;
Stange) — and its invariance under `n ↦ −n` is the trivial observation that `W(m−n)·W(m+n)` equals
`W(m+n)·W(m−n)` by commutativity of `R`.

Sources agree on the standard form: yes for the Ward-recurrence product; the `addMulSub` building
block and its `addMulSub_neg₁` symmetry have **no** standard form because they are not literature
objects.

Most general standard form: of the *product*, `W(m+n)·W(m−n)` over any commutative ring; but that is
not what this lemma is about. This lemma is the **definitional reduction** that, after the `tdiv 2`
unfolding, the two factors swap under `n ↦ −n`. It is parametric over an arbitrary `CommRing R` and an
arbitrary `W : ℤ → R` with **no** hypothesis — already maximally general for what it says.

Generality dimensions where the literature varies: none relevant — the lemma is unconditional
commutativity bookkeeping; the only ambient structure it uses is that `R` is commutative.

Disagreement with the literature: none — the literature has **no** object to agree/disagree with. The
empty-concept result is itself the signal (per the verdicts reference: literature absence of the
*concept* ⇒ this is a formalisation-internal helper, not a mathlib-shaped standalone result).

---

### Generality analysis — `EllSequence.addMulSub_neg₁`

Literature-standard form (Phase 3): n/a — the lemma is the unfolding/commutativity symmetry of a
project-local definition; there is no literature "standard form" for the statement (only for the
product on the RHS).

| # | Parameter / hypothesis              | Current Lean form              | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------|--------------------------------|------------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`                     | commutative ring               | n/a (not a literature statement)   | **NO**              | commutativity of `R` is exactly the ingredient that makes the factor-swap legal (`mul_comm`); it cannot be dropped. (`addMulSub` is *defined* in the `CommRing R` section, so weakening the typeclass would also be meaningless for an unfolding lemma that lives with its def.) |
| 2 | `(W : ℤ → R)`                      | arbitrary sequence             | n/a                                | already max         | No EDS / divisibility / **oddness** hypothesis is used — already the weakest possible (any function `ℤ → R`). Strictly weaker than the sibling `addMulSub_neg₀`, which needs `W` odd; the second-index version is unconditional. |
| 3 | `(m n : ℤ)`                        | two integer indices            | n/a                                | NO                  | the half-index `tdiv 2` structure is intrinsic to `addMulSub`; the `n ↦ −n` specialisation **is** the content (companion `addMulSub_neg₀` handles the first index). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (over `CommRing`, with **no** hypothesis on `W` — already
the weakest possible). Number of weakening opportunities found: **0**. Cost of restatement: n/a.

Packaging observation (the sense used throughout the sibling reports): the right unit to upstream is
**not this lone lemma** but the `EllSequence` elliptic-relation layer it belongs to. As a standalone
public mathlib lemma `addMulSub_neg₁` is the wrong granularity — it is internal scaffolding (ideally
`private`/section-local) whose only job is to make `addMulSub_abs₁` (line 195, its sole internal
consumer) and the `rel₄`/`net` symmetry arguments go through.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                       | no       | — (`[CommRing R]` is already a class; `W` is a bare hypothesis as it must be) | — |
|  2 | sequences/metric → filters/nets/topology?                                | no       | — (an algebraic identity; no limits/topology) | — |
|  3 | construct object → universal-property class?                             | no       | — (it is an equation, not a construction) | — |
|  4 | set-with-closure-predicate → bundled substructure?                       | no       | — (not a substructure) | — |
|  5 | vector-space/metric/field-specific → weaken typeclass?                   | no       | — (already at `CommRing`; commutativity is genuinely needed) | — |
|  6 | 1-categorical → higher-categorical?                                      | no       | — (elementary commutative algebra) | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                         | no       | — (the `tdiv 2` half-index is intrinsic; `ℤ` is the right domain) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. One-line reason: this is an elementary commutativity identity about a
concrete helper `def`; there is no contemporary reformulation that would compose better — the only
question is one of *granularity* (it ships with the `addMulSub` layer, not alone), already captured by
the parent `addMulSub.md` verdict.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`.** (Lemmas introduce no definitional equalities and no
typeclass-search paths.)

---

### Mathlib search-status: `EllSequence.addMulSub_neg₁`

[A] Lean-Finder       "elliptic sequence building block negate second index commutativity W((m+n)/2)W((m-n)/2)"   no hits (tool not surfaced in this env; substituted with authoritative grep [D] over the actual mathlib source tree)
[B] Loogle            `addMulSub`, `EllSequence.addMulSub_neg₁`, `?W ?m (-?n) ... = ?W ?m ?n ...`     no hits — the symbol `addMulSub` is unknown to mathlib (consistent with `rel₄.md` / `addMulSub.md` / `addMulSub_neg₀.md`)
[C] LeanSearch        "elliptic divisibility sequence half-index product symmetric under negating second argument"   no hits
[D] Grep mathlib src  `addMulSub` / `addMulSub_neg` / `EllSequence` over **every** mathlib checkout on disk (incl. the pinned `d90090f` at `.lake/packages/mathlib/` and the standalone `mathlib4-up1` clone)   **0 hits everywhere** — verified this run
[E] Name pattern      `addMulSub_neg₁` / `_neg₁` in the mathlib tree                                no hits

Searched for both:
- the user's current form (`addMulSub_neg₁` about `EllSequence.addMulSub`) — **absent**: mathlib has
  no `EllSequence` namespace, no `addMulSub`, hence no lemma about it.
- the literature-standard neighbour — mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
  *does* prove negation lemmas, but **for its own sequences**: `preNormEDS_neg`, `normEDS_neg`
  (`normEDS b c d (-n) = -normEDS b c d n`), `complEDS₂_neg` (`complEDS₂ b c d (-k) = complEDS₂ b c d k`),
  `complEDS_neg`. These are the *analogues* for the mathlib `normEDS`/`preNormEDS` track — **not** a
  statement about the half-index `addMulSub` product, which mathlib does not define. (Note `complEDS₂_neg`
  is *even*-symmetric like `addMulSub_neg₁`, but about a different object.)

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard negation
neighbour). The closest mathlib relatives (`normEDS_neg`, `complEDS₂_neg`, …) are about *different*
(mathlib) objects; they neither subsume nor supply this lemma.

---

### Call sites — `EllSequence.addMulSub_neg₁`

Internal use count: **1** genuine, within the declaring live file (NOT counting the `def` and the
lemma itself).
External-to-file callers: **0 genuine external consumers**. The lemma is *duplicated verbatim* into
two sibling forks — the HasseWeil auxiliary copy and the dead `…Original` track — but those are
intra-repo forking/dedup, not downstream API consumers.

| Caller file:line                                                                  | Usage pattern (one-line excerpt)                                  |
|-----------------------------------------------------------------------------------|--------------------------------------------------------------------|
| `…/EllipticDivisibilitySequence.lean:196` (`addMulSub_abs₁`)                        | `obtain h \| h := abs_choice n <;> simp only [h, addMulSub_neg₁]`  |
| `…/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:124` (sibling-fork copy)  | same `addMulSub_abs₁` body — duplicate, not an external consumer    |
| `…/EllipticDivisibilitySequenceOriginal.lean:188` (dead duplicate track)           | same `addMulSub_abs₁` body — slated for deletion per `05-duplications.md` |

Inline-derivation grep: the *same* `simp only [h, addMulSub_neg₁]` appears in all three copies (one
live, two duplicates) — the lemma is never re-derived inline; consumers always call it. But its **only
genuine use** is the single in-file step inside `addMulSub_abs₁`. (Downstream of `addMulSub_abs₁`, the
`rel₄`/`net` machinery at lines 277 / 515 consumes `addMulSub_abs₁`, transitively relying on this
lemma — but the direct call count is K = 1.)

Composability signal: **K = 1 internal use only → possibly the wrong abstraction / could be inlined;
leans NO-composable.** Combined with "the parent `def` it is about is not in mathlib," this firmly
places the lemma in the *rides-with-the-parent-layer* basket rather than as a standalone contribution.

---

### Composition check (Phase 6)

Can `EllSequence.addMulSub_neg₁` be derived from mathlib in ≤3 chained calls?

The statement *mentions* `addMulSub`, which is not in mathlib — so strictly, against today's mathlib
it cannot even be *stated*. Two readings:

- **Reading A (re-aimed at the parent layer, the honest one).** Once `addMulSub` is upstreamed as the
  layer's building block, this lemma is a **2-call inline** of mathlib primitives already present —
  in fact even simpler than its sibling `addMulSub_neg₀`, because it needs **no hypothesis on `W`**:
  ```lean
  example (m n : ℤ) : addMulSub W m (-n) = addMulSub W m n := by
    rw [addMulSub, addMulSub, mul_comm]; abel_nf
  ```
  The only substantive mathlib ingredients are `mul_comm` (`CommMonoid`/`CommRing`) to swap the two
  factors and `abel_nf` to normalise the index arithmetic `m + (−n) = m − n`, `m − (−n) = m + n`
  inside the `tdiv 2` arguments. No mathlib *lemma about `Int.tdiv`* is even required (unlike
  `addMulSub_neg₀`, which leans on `Int.neg_tdiv`) — the negation is absorbed by `abel_nf` after the
  commutativity swap, because the two `tdiv 2` arguments are *exchanged*, not negated. This is an
  unfold + `mul_comm` + `abel_nf` inline, **not** a result requiring its own mathlib lemma; it should
  ship as a *section-local helper* alongside `addMulSub`, not as an independent public API entry.

- **Reading B (against today's mathlib).** `addMulSub` is absent, so there is no statement to compose
  — vacuously NOT-COMPOSABLE-because-unstatable. This collapses into the parent's "upstream the layer"
  plan.

Conclusion: **COMPOSABLE** (Reading A) — a 2-call `rw [addMulSub, addMulSub, mul_comm]; abel_nf`
inline. It is bookkeeping internal to the `addMulSub` layer, not a free-standing mathlib lemma.

---

## Verdict: `EllSequence.addMulSub_neg₁`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the *product* `W(m+n)·W(m−n)` is the standard Ward-recurrence LHS, but
  `addMulSub` (the halved-argument building block) is **not a named literature object** in any channel
  (Ward / Stange / Silverman / arXiv / nLab / MO). Its `n ↦ −n` symmetry is the trivial observation
  that commutativity swaps the two factors — named nowhere.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** over `CommRing` with **no** hypothesis on `W`
  (0 weakenings — strictly weaker premises than the sibling `addMulSub_neg₀`); Phase 4c found no
  cleaner modern idiom — only a *granularity* point (ships with the `addMulSub` layer, not alone).
- Mathlib search (Phase 5): **not in mathlib** — `addMulSub` occurs nowhere in any mathlib checkout on
  disk (0 grep hits); the closest relatives (`normEDS_neg`, `complEDS₂_neg`, `preNormEDS_neg`,
  `complEDS_neg`) are negation lemmas for *mathlib's own* sequences, not for the half-index `addMulSub`
  product, which mathlib does not define.
- Composition check (Phase 6): **COMPOSABLE** — a 2-call `rw [addMulSub, addMulSub, mul_comm]; abel_nf`
  once the parent `addMulSub` def exists; the only substantive ingredient is `mul_comm` + `abel_nf`.
- Call sites (Phase 6.0): **K = 1** genuine internal use (inside `addMulSub_abs₁`, line 196); the only
  other copies are sibling-fork duplicates. Wrong-abstraction / inline signal.
- Diamond/defeq risk (Phase 4.5): **n/a** (it is a `lemma`).

**Rationale.**

`addMulSub_neg₁` is a one-line structural lemma whose entire job is to record that the project's
internal building block `addMulSub W m n = W((m+n)/2)·W((m−n)/2)` is invariant under `n ↦ −n`. It is
the *unconditional* twin of `addMulSub_neg₀`: negating the **second** index exchanges the index pair
`(m+n, m−n) ↦ (m−n, m+n)`, i.e. it merely *swaps the two factors*, so the identity is nothing more than
commutativity of `R` (`mul_comm`) plus integer-index normalisation (`abel_nf`) — no oddness of `W`, no
EDS property, no hypothesis at all. The mathematical content is therefore *nil* beyond "the ring is
commutative"; it threads a triviality through a *formalisation-specific* definition, and the file's own
docstring (line 97) flags exactly this design — the `Int.tdiv`-by-2 choice exists so that "lemmas like
`addMulSub_neg₀` hold unconditionally" (the same applies a fortiori to `addMulSub_neg₁`). Its only
genuine consumer is the very next lemma, `addMulSub_abs₁`.

Because the lemma's *statement* names `EllSequence.addMulSub` — which is **not** in mathlib (the entire
`EllSequence` four-index-relation layer is absent; a direct grep over every mathlib checkout on disk
returns zero hits, and sibling reports `addMulSub.md`/`rel₄.md`/`addMulSub_neg₀.md` confirm the same
against the live mathlib4 docs) — it cannot be a standalone mathlib addition. The correct framing is the
skill's **re-aim-to-parent** rule: the parent `def` `addMulSub` is destined for mathlib only *as the
internal building block of the whole elliptic-relation layer*, and that layer's sign/parity lemmas
(`addMulSub_neg₀/₁`, `addMulSub_abs₀/₁`, `addMulSub_swap`) are explicitly named in `addMulSub.md` as
part of "what to upstream." Within that PR this lemma is **not** an independently-citable API entry — it
is a section-local helper that, against the (then-present) `addMulSub` plus mathlib's `mul_comm`/`abel`,
reduces to a 2-line `rw …; abel_nf`. Hence the standalone verdict is **NO-composable-from-mathlib**:
mathlib has the building blocks (`mul_comm`, `abel_nf`, `CommRing`), the form is a 2-call inline, and no
separate public lemma is warranted.

**WHY not (refactor-actionable).**
Mathlib has the building blocks; this lemma is a 2-call composition once `addMulSub` exists.

- Mathlib building blocks:
  - `mul_comm` (`Mathlib/Algebra/Group/Basic.lean`, `CommMonoid`/`CommRing`) — swap the two factors
    `W((m+n)/2)·W((m−n)/2) = W((m−n)/2)·W((m+n)/2)`; this is the load-bearing step.
  - `abel_nf` (mathlib tactic) — normalise the `ℤ`-index arithmetic `m + (−n) = m − n` and
    `m − (−n) = m + n` inside the `tdiv 2` arguments after the swap. (Note: *no* `Int.tdiv` lemma is
    needed here, unlike `addMulSub_neg₀`'s `Int.neg_tdiv` — the negation is consumed by the factor
    exchange, not pushed through `tdiv`.)
  - `[CommRing R]` (the ambient instance) supplying commutativity.
- Composition sketch (≤3 lines — exactly the existing proof, which is itself the inline):
  ```lean
  example (m n : ℤ) : addMulSub W m (-n) = addMulSub W m n := by
    rw [addMulSub, addMulSub, mul_comm]; abel_nf
  ```
- Call sites in our project (Phase 6.0): **K = 1** genuine (`addMulSub_abs₁`, line 195/196), plus two
  sibling-fork duplicates.

Refactor plan (two-layer, both already on the project's books):
1. **Intra-repo dedup (now, a `/cleanup` chore):** there are three copies of this lemma (NagellLutz
   live `…:188`; `…Original.lean:180` dead; HasseWeil auxiliary `…:116`). Per `05-duplications.md`,
   collapse to **one** source of truth — delete the `…Original.lean` track and have HasseWeil import
   the NagellLutz `EllSequence` layer instead of vendoring it.
2. **Upstreaming (with the parent layer, not alone):** when the `EllSequence` elliptic-relation layer
   is PR'd to `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (the unit identified in
   `addMulSub.md` / `rel₄.md`), keep `addMulSub_neg₁` as a **section-local / `private`** helper next to
   `addMulSub`, *not* as a public lemma. It is not independently citable. Because its only consumer is
   `addMulSub_abs₁`, a reasonable end-state is to **inline** the 2-line proof into `addMulSub_abs₁` and
   drop the named lemma entirely.

Next action: do **not** open a standalone mathlib PR for `addMulSub_neg₁`. Fold it into (a) the
intra-repo dedup of the triplicated `EllSequence` layer, then (b) the parent `addMulSub`/`rel₄` layer
upstreaming, where it lives as an internal helper (or is inlined into `addMulSub_abs₁`). Its standalone
existence as a public decl is a cleanup target, not a mathlib contribution.

---

## Next step

`addMulSub_neg₁` is internal scaffolding for the `EllSequence` `addMulSub` building block, not a
standalone mathlib lemma. Standalone verdict: **NO-composable-from-mathlib** (2-call
`rw [addMulSub, addMulSub, mul_comm]; abel_nf` over mathlib's `mul_comm` + `abel_nf`; no hypothesis on
`W`, strictly weaker than the sibling `addMulSub_neg₀`). Action: ride it along with the parent
`addMulSub`/`rel₄` elliptic-relation layer upstreaming as a `private`/section-local helper — or inline
it into its sole consumer `addMulSub_abs₁`; first collapse the three in-repo copies to one per
`05-duplications.md`. No independent PR.

## Sources

- *Elliptic divisibility sequence* (Ward recurrence; product `W(m+n)W(m−n)`; oddness `W₋ₙ=−Wₙ`) — https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence
- Stange, *Elliptic nets and elliptic curves* (net recurrence; antisymmetry `W(−v)=−W(v)`) — https://arxiv.org/abs/0710.1316
- *The sign of an elliptic divisibility sequence* (named result in this neighbourhood; symmetries are background) — https://arxiv.org/abs/math/0402415
- Angdinata–Xu, *On Elliptic Sequences over Commutative Rings* (the paper behind this Lean development) — https://arxiv.org/pdf/2604.05280
- Mathlib4, `Mathlib.NumberTheory.EllipticDivisibilitySequence` (`normEDS_neg`/`preNormEDS_neg`/`complEDS₂_neg`/`complEDS_neg`; no `EllSequence`/`addMulSub` layer) — verified by direct grep over every on-disk mathlib checkout (0 hits) and the live docs.
- Sibling assessments (same directory): `addMulSub.md` (parent def), `addMulSub_neg₀.md` (the first-argument twin — needs oddness; this one does not), `addMulSub_even.md`, `addMulSub_odd.md`, `rel₄.md`, `net.md`, `net_add_sub_iff.md`.
