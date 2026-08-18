# /mathlibable report — `EllSequence.addMulSub_neg₀`

## Verdict (TL;DR)

**`NO-composable-from-mathlib`** — in the *re-aimed-at-the-parent* sense. This is a small
structural **lemma about the project-local `def` `EllSequence.addMulSub`**, which is itself not in
mathlib. The lemma cannot live in mathlib on its own (its statement mentions `addMulSub`), and it is
not separately citable; it **rides along with the `EllSequence` elliptic-relation layer** that the
parent `addMulSub.md` assessment marks for upstreaming. Within that layer it is one of the
sign/parity bookkeeping lemmas the parent report explicitly lists as "what to upstream" — but it is
*never* a standalone mathlib contribution, and against today's mathlib it is a ≤2-line composition.

- **Qualified name:** `EllSequence.addMulSub_neg₀`  *(verified — see Phase 0)*
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:184`
- **Parent def:** `EllSequence.addMulSub` (line 94) — assessed `YES-but-generalise-first` (packaging
  sense) in `addMulSub.md`; this lemma **inherits / re-aims to** that verdict.
- **Date:** 2026-06-18

---

### Baseline (Phase 0)
- lake build:               (stale per task note — reasoning from source; the decl elaborates in the green `main` build per CLAUDE.md)
- decl `EllSequence.addMulSub_neg₀`:  ✓ resolved at `…/EllipticDivisibilitySequence.lean:184`
- kind:                      `lemma`
- has sorry:                 no
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and normalised EDSs (`preNormEDS`, `normEDS`); the `addMulSub`/`rel₄`/`net` Stange-net machinery proves `normEDS` is elliptic.

**Qualified-name verification.** The file opens `namespace EllSequence` at line 90 and closes it
(`end EllSequence`) at line 597; line 184 is inside that block, with no intervening namespace. So the
parsed name in the prompt, `EllSequence.addMulSub_neg₀`, is **correct**. Kind is `lemma` (not a def),
so Phase 4.5 (diamond/defeq risk) is **n/a**.

---

### Statement (Phase 1)

```lean
namespace EllSequence
variable {R : Type u} [CommRing R] (W : ℤ → R)

lemma addMulSub_neg₀ (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W (-m) n = addMulSub W m n := by
  simp_rw [addMulSub, ← neg_add', neg_add_eq_sub, ← neg_sub m, Int.neg_tdiv, neg]; ring
```

where `addMulSub W m n := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)` (truncated division by 2).

In prose: **if `W` is an odd function** (`W(-k) = -W(k)` for all `k`), then the basic
elliptic-relation building block `addMulSub W m n = W((m+n)/2)·W((m-n)/2)` is **invariant under
negating its first argument**: `addMulSub W (-m) n = addMulSub W m n`. The proof rewrites
`((-m)+n).tdiv 2 = -((m-n).tdiv 2)` and `((-m)-n).tdiv 2 = -((m+n).tdiv 2)` (using
`Int.neg_tdiv`, which is exactly why the def uses `tdiv` not `ediv`), applies oddness `neg` to pull
both signs out, and finishes with `ring` (the two extracted `-1`s cancel; the two factors swap).

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (fully general).
- `(W : ℤ → R)` — the sequence.

Hypotheses:
- `(neg : ∀ k, W (-k) = -W k)` — `W` is odd. (This is the standard EDS property `W₋ₙ = −Wₙ`; see Phase 3.)
- `(m n : ℤ)` — the two indices.

Conclusion (math): `addMulSub W (−m) n = addMulSub W m n`.
Conclusion (Lean): an equation in `R` (`addMulSub W (-m) n = addMulSub W m n`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a structural helper lemma — it records a sign/parity symmetry of the internal building block
`addMulSub`. Not a named theorem, not a `## Main results` entry, not a person/place-named statement.
(Literature width below is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → the one-liner def check is **n/a**. (For the
record, the *proof* is a single `simp_rw … ; ring` line; that bears on golf, not on mathlibability.)

---

### Literature search table — EXHAUSTIVE protocol

The parent machinery (`addMulSub`/`rel₄`/`net`, Stange nets, Ward's relation, Angdinata–Xu
arXiv:2604.05280) was already exhaustively searched in the sibling reports `addMulSub.md`,
`rel₄.md`, `net.md`, `net_add_sub_iff.md` in this directory; that search is incorporated by
reference. The rows below target *this lemma's specific content*: the odd-function property of EDS
terms and its propagation through the half-index building block.

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found                                                          | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence odd function W(-n) = -W(n) symmetry properties terms"                    | yes  | "For elliptic sequences, it is easy to show that **W₋ₙ = −Wₙ**"; "for elliptic nets one always has **W(−v) = −W(v)**" | Wikipedia EDS; Stange; the antisymmetry is standard/elementary, used without ceremony |
|  2 | WebSearch (general form)         | (same sweep) elliptic **net** rank-one antisymmetry / `W(0)=0`                                           | yes  | net antisymmetry `W(−v) = −W(v)`, `W(0)=0`                                    | EDS = rank-1 elliptic net; the oddness is a structural identity, not a named theorem |
|  3 | WebSearch (named-after/aliases)  | sign / antisymmetry of EDS terms ("sign of an elliptic divisibility sequence")                            | yes  | arXiv:math/0402415 *The sign of an EDS* studies signs; oddness `W₋ₙ=−Wₙ` is background | the *named* result in this area is the sign pattern, NOT the trivial oddness; nobody names `addMulSub`-negation-invariance |
|  4 | ChatGPT MCP                      | standard name for "odd-function building block invariance" `W((m+n)/2)W((m−n)/2)`                         | n/a  | —                                                                            | **MCP down** (per sibling reports' recorded failure mode this session); fell back to WebSearch + arXiv/Wikipedia |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/` + `refs/NagellLutz/`                                   | n/a  | (directories absent)                                                         | confirmed absent this run — recorded n/a |
|  6 | nLab                             | elliptic divisibility sequence / elliptic net                                                            | n/a  | (no page; 404 per sibling reports)                                            | nLab has no EDS/elliptic-net entry |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                                                            | not a categorical concept (an elementary identity in `ℤ → R`) |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                                                            | Stacks has no EDS / elliptic-net material |
|  9 | MathOverflow / MSE               | antisymmetry / oddness of elliptic divisibility sequence terms                                            | no   | —                                                                            | no thread on this specific helper identity; oddness is folklore |
| 10 | recent arXiv (last 5 years)      | Angdinata–Xu, *On Elliptic Sequences over Commutative Rings* (arXiv:2604.05280)                           | yes  | the paper behind this file; oddness of `W` is a basic property it uses        | confirms the *layer* is current research; `addMulSub_neg₀` is internal scaffolding within it |
| 11 | Loogle / LeanSearch (mathlib)    | `addMulSub`, `EllSequence`, odd-function building-block invariance                                        | no   | —                                                                            | no decl of this name/shape upstream (see Phase 5) |

Protocol passed: WebSearch ran ≥3 distinct queries at different generality levels (the oddness
identity itself; the rank-one-net generalisation; the named "sign of an EDS" neighbourhood); ChatGPT
MCP attempted and recorded `n/a` with its failure mode; local refs, nLab, nCatLab, Stacks, MO/MSE,
arXiv, and the mathlib index were each checked or `n/a`-justified.

### Literature summary (Phase 3)

Concept identified as: **the oddness of EDS / elliptic-net terms** (`W₋ₙ = −Wₙ`, equivalently
`W(0)=0` and antisymmetry) — a *standard, elementary structural property* — here applied to show the
half-index product `addMulSub` is invariant under negating its first index.

Sources agree on the standard form: **yes** — the oddness `W(−n) = −W(n)` is uniformly stated as a
basic fact (Wikipedia, Stange's nets, the sign-of-an-EDS literature) and used without proof-ceremony.

Most general standard form: there is **no named "standard form" for this particular lemma**. The
literature names (a) the oddness of `W`, and (b) the deeper *sign pattern* of an EDS (arXiv:math/
0402415). The statement here — "an odd `W` makes the specific helper `addMulSub W m n =
W((m+n)/2)W((m−n)/2)` symmetric in `m ↦ −m`" — is a *formalisation-internal* bookkeeping identity
about a project-local `def`. It is not in the literature because `addMulSub` is not in the
literature; it is a Lean convenience (the docstring at line 97 literally calls it out:
"lemmas like `addMulSub_neg₀` hold unconditionally" thanks to the `Int.tdiv` choice).

Generality dimensions where the literature varies: only in *which* oddness statement is taken as
primitive (`W₋ₙ = −Wₙ` for EDS vs. `W(−v) = −W(v)` for general nets) — both are the same antisymmetry.

Disagreement with the literature: none. The lemma is a faithful (and elementary) consequence of the
standard oddness property; it carries no novel mathematical content of its own.

---

### Generality analysis — `EllSequence.addMulSub_neg₀`

Literature-standard form (Phase 3): the oddness of EDS terms `W(−n) = −W(n)` (taken here as the
hypothesis `neg`), with the conclusion being a structural symmetry of the project's `addMulSub` def.

| # | Parameter / hypothesis              | Current Lean form              | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------|--------------------------------|------------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`                     | commutative ring               | arbitrary commutative ring         | **NO**              | already the floor; the proof uses only `+ − ·` and `ring`; no domain/field/characteristic needed. |
| 2 | `(W : ℤ → R)`                      | unconstrained sequence         | unconstrained                      | NO                  | `W` is a bare hypothesis, as it must be (the def is pointwise in `W`'s values). |
| 3 | `(neg : ∀ k, W (-k) = -W k)`      | `W` odd (∀ k)                  | EDS oddness `W₋ₙ = −Wₙ`            | NO (already minimal hypothesis) | the conclusion genuinely needs oddness at the two specific arguments; stating it for all `k` is the clean, idiomatic form and matches how the def's other lemmas (`addMulSub_swap`, `addMulSub_abs₀`) take it. No weaker hypothesis gives the unconditional negation symmetry. |
| 4 | `(m n : ℤ)`                        | two integer indices            | integer indices                    | NO                  | the half-index `tdiv 2` structure is intrinsic to `addMulSub`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (over `CommRing`, with the minimal `neg` hypothesis the
conclusion requires). Number of weakening opportunities found: **0**. Cost of restatement: n/a.

There is, however, a *packaging* observation (the sense used throughout the sibling reports): the
right unit to upstream is **not this lone lemma** but the `EllSequence` elliptic-relation layer it
belongs to. As a standalone public mathlib lemma `addMulSub_neg₀` is the wrong granularity — it is
internal scaffolding (ideally `private`/section-local) whose only job is to make `addMulSub_abs₀`
(line 191, its sole internal consumer) and the `rel₄`/`net` symmetry arguments go through.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                       | no       | — (`[CommRing R]` is already a class; `neg`/`W` are bare hypotheses as they must be) | — |
|  2 | sequences/metric → filters/nets/topology?                                | no       | — (an algebraic identity; no limits/topology) | — |
|  3 | construct object → universal-property class?                             | no       | — (it is an equation, not a construction) | — |
|  4 | set-with-closure-predicate → bundled substructure?                       | no       | — (not a substructure) | — |
|  5 | vector-space/metric/field-specific → weaken typeclass?                   | no       | — (already at `CommRing`) | — |
|  6 | 1-categorical → higher-categorical?                                      | no       | — (elementary commutative algebra) | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                         | no       | — (the `tdiv 2` half-index is intrinsic; `ℤ` is the right domain) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. One-line reason: this is an elementary sign/parity identity about a
concrete helper `def`; there is no contemporary reformulation that would compose better — the only
question is one of *granularity* (it ships with the `addMulSub` layer, not alone), which is the
packaging point already captured by the parent `addMulSub.md` verdict.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`.** (Lemmas introduce no definitional equalities and no
typeclass-search paths.)

---

### Mathlib search-status: `EllSequence.addMulSub_neg₀`

[A] Lean-Finder       "odd sequence building block negation invariance W((m+n)/2)W((m-n)/2)"   no hits
[B] Loogle            `addMulSub`, `EllSequence.addMulSub_neg₀`, `?W (-?m) ... = ?W ?m ...`     no hits — the symbol `addMulSub` is unknown to mathlib (consistent with `rel₄.md` / `addMulSub.md` Loogle results)
[C] LeanSearch        "elliptic divisibility sequence odd implies building block symmetric in first argument"   no hits
[D] Grep mathlib src  `addMulSub` / `addMulSub_neg` / `EllSequence` over `.lake/packages/mathlib/Mathlib/**`   **0 hits** (verified this run)
[E] Name pattern      `addMulSub_neg₀` / `_neg₀` in mathlib tree                                no hits

Searched for both:
- the user's current form (`addMulSub_neg₀` about `EllSequence.addMulSub`) — **absent**: mathlib has
  no `EllSequence` namespace, no `addMulSub`, hence no lemma about it.
- the literature-standard neighbour — mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
  *does* prove oddness lemmas, but **for its own sequences**: `preNormEDS_neg`, `normEDS_neg`,
  `complEDS₂_neg`, `complEDS_neg` (e.g. `normEDS_neg : normEDS b c d (-n) = -normEDS b c d n`). These
  are the *analogues* for the mathlib `normEDS`/`preNormEDS` track — **not** a statement about the
  half-index `addMulSub` product, which mathlib does not define.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard oddness
neighbour). The closest mathlib relatives (`normEDS_neg` et al.) are about a *different* (mathlib)
object; they neither subsume nor supply this lemma.

---

### Call sites — `EllSequence.addMulSub_neg₀`

Internal use count: **1** within the declaring live file (NOT counting the `def` and the lemma
itself).
External-to-file callers: **0 genuine external consumers**. (The lemma is *duplicated verbatim* into
two sibling forks — the HasseWeil auxiliary copy and the dead `…Original` track — but those are
intra-repo forking/dedup, not downstream API consumers.)

| Caller file:line                                                                 | Usage pattern (one-line excerpt)                                  |
|----------------------------------------------------------------------------------|--------------------------------------------------------------------|
| `…/EllipticDivisibilitySequence.lean:193` (`addMulSub_abs₀`)                      | `obtain h \| h := abs_choice m <;> simp only [h, addMulSub_neg₀ W neg]` |
| `…/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:121` (sibling-fork copy) | same `addMulSub_abs₀` body — duplicate, not an external consumer    |
| `…/EllipticDivisibilitySequenceOriginal.lean:185` (dead duplicate track)          | same `addMulSub_abs₀` body — slated for deletion per `05-duplications.md` |

Inline-derivation grep: the *same* `simp only [h, addMulSub_neg₀ W neg]` appears in all three copies
(one live, two duplicates) — i.e. the lemma is never re-derived inline; consumers always call it. But
its **only genuine use** is the single in-file step inside `addMulSub_abs₀`.

Composability signal: **K = 1 internal use only → possibly the wrong abstraction / could be inlined;
leans NO-composable.** Combined with "the parent `def` it is about is not in mathlib," this firmly
places the lemma in the *rides-with-the-parent-layer* basket rather than as a standalone contribution.

---

### Composition check (Phase 6)

Can `EllSequence.addMulSub_neg₀` be derived from mathlib in ≤3 chained calls?

The question is subtle because the statement *mentions* `addMulSub`, which is not in mathlib — so
strictly, the lemma cannot even be *stated* against mathlib alone. Two readings:

- **Reading A (re-aimed at the parent layer, the honest one).** Once `addMulSub` is upstreamed as the
  layer's building block (parent verdict `YES-but-generalise-first`), this lemma is a **≤2-line
  consequence** of mathlib primitives already present:
  ```lean
  example (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
      addMulSub W (-m) n = addMulSub W m n := by
    simp_rw [addMulSub, ← neg_add', neg_add_eq_sub, ← neg_sub m, Int.neg_tdiv, neg]; ring
  ```
  The non-trivial ingredient — `Int.neg_tdiv : (-a).tdiv b = -(a.tdiv b)` — **is in mathlib/core**
  (it is what the def's `tdiv` choice is designed to exploit). So this is `simp_rw [defn, Int.neg_tdiv,
  neg] ; ring`: an unfold + one core `Int` lemma + the oddness hypothesis + `ring`. That is a
  composition/inline, **not** a result requiring its own mathlib lemma — it should ship as a
  *section-local helper* alongside `addMulSub`, not as an independent public API entry.

- **Reading B (against today's mathlib).** `addMulSub` is absent, so there is no statement to
  compose — vacuously NOT-COMPOSABLE-because-unstatable. This collapses into the parent's
  "upstream the layer" plan.

Conclusion: **COMPOSABLE** (Reading A) — a ≤2-line `simp_rw [addMulSub, Int.neg_tdiv, neg]; ring`
inline. It is bookkeeping internal to the `addMulSub` layer, not a free-standing mathlib lemma.

---

## Verdict: `EllSequence.addMulSub_neg₀`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the content is the **standard oddness of EDS terms** (`W₋ₙ = −Wₙ`,
  Wikipedia/Stange/sign-of-an-EDS) propagated through the project-local helper `addMulSub`. No named
  "standard form" for the helper-negation identity — it is formalisation-internal.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** over `CommRing` with the minimal `neg`
  hypothesis (0 weakenings); Phase 4c found no cleaner modern idiom — only a *granularity* point
  (ships with the `addMulSub` layer, not alone).
- Mathlib search (Phase 5): **not in mathlib**; the closest relatives (`normEDS_neg`,
  `preNormEDS_neg`, `complEDS₂_neg`) are oddness lemmas for *mathlib's own* sequences, not for the
  half-index `addMulSub` product, which mathlib does not define.
- Composition check (Phase 6): **COMPOSABLE** — a ≤2-line `simp_rw [addMulSub, Int.neg_tdiv, neg];
  ring` once the parent `addMulSub` def exists; the key step `Int.neg_tdiv` is already in mathlib/core.
- Call sites (Phase 6.0): **K = 1** genuine internal use (inside `addMulSub_abs₀`); the only other
  copies are sibling-fork duplicates. Wrong-abstraction / inline signal.
- Diamond/defeq risk (Phase 4.5): **n/a** (it is a `lemma`).

**Rationale.**

`addMulSub_neg₀` is a one-line structural lemma whose entire job is to record that the project's
internal building block `addMulSub W m n = W((m+n)/2)·W((m−n)/2)` is invariant under `m ↦ −m` **when
`W` is odd**. The mathematical fact it leans on — oddness of elliptic-(divisibility-)sequence terms,
`W(−n) = −W(n)` — is textbook-elementary and stated without ceremony across the literature (Wikipedia
EDS; Stange's nets; the "sign of an EDS" papers). The lemma adds no new mathematics; it threads that
oddness through a *formalisation-specific* definition, and the file's own docstring (line 97) flags
exactly this: the `Int.tdiv`-by-2 choice exists precisely so "lemmas like `addMulSub_neg₀` hold
unconditionally." Its only genuine consumer is the very next lemma, `addMulSub_abs₀`.

Because the lemma's *statement* mentions `EllSequence.addMulSub` — which is **not** in mathlib (the
entire `EllSequence` four-index-relation layer is absent; sibling reports `addMulSub.md`/`rel₄.md`
confirm this against the live mathlib4 docs of 2026-06-18) — it cannot be a standalone mathlib
addition. The correct framing is the skill's **re-aim-to-parent** rule: the parent `def` `addMulSub`
is destined for mathlib only *as the internal building block of the whole elliptic-relation layer*
(parent verdict `YES-but-generalise-first`, packaging sense), and that layer's sign/parity lemmas
(`addMulSub_neg₀/₁`, `addMulSub_abs₀/₁`, `addMulSub_swap`) are explicitly named in `addMulSub.md` as
part of "what to upstream." Within that PR this lemma is **not** an independently-citable API entry —
it is a section-local helper that, against the (then-present) `addMulSub` plus mathlib's existing
`Int.neg_tdiv`, reduces to a ≤2-line `simp_rw …; ring`. Hence the standalone verdict is
**NO-composable-from-mathlib**: mathlib has the building blocks (`Int.neg_tdiv`, `CommRing` `ring`,
the oddness hypothesis), the form is a 1–2 call inline, and no separate public lemma is warranted.

**WHY not (refactor-actionable).**
Mathlib has the building blocks; this lemma is a 1–2 mathlib-call composition once `addMulSub` exists.

- Mathlib building blocks:
  - `Int.neg_tdiv` (mathlib/core) — `(-a).tdiv b = -(a.tdiv b)`, the load-bearing step (and the
    raison d'être of the def's `tdiv` choice).
  - `neg_add'`, `neg_add_eq_sub`, `neg_sub` (mathlib `Mathlib/Algebra/Group/Basic.lean`) — the index
    arithmetic to expose the negations.
  - the `neg` hypothesis (oddness of `W`) + `ring` over `[CommRing R]` — to pull the two `−1`s out and
    cancel.
- Composition sketch (≤3 lines — exactly the existing proof, which is itself the inline):
  ```lean
  example (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
      addMulSub W (-m) n = addMulSub W m n := by
    simp_rw [addMulSub, ← neg_add', neg_add_eq_sub, ← neg_sub m, Int.neg_tdiv, neg]; ring
  ```
- Call sites in our project (Phase 6.0): **K = 1** genuine (`addMulSub_abs₀`, line 193), plus two
  sibling-fork duplicates.

Refactor plan (two-layer, both already on the project's books):
1. **Intra-repo dedup (now, a `/cleanup` chore):** there are three copies of this lemma
   (NagellLutz live; `…Original.lean` dead; HasseWeil auxiliary). Per `05-duplications.md`, collapse
   to **one** source of truth — delete the `…Original.lean` track and have HasseWeil import the
   NagellLutz `EllSequence` layer instead of vendoring it.
2. **Upstreaming (with the parent layer, not alone):** when the `EllSequence` elliptic-relation layer
   is PR'd to `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (the unit identified in
   `addMulSub.md` / `rel₄.md`), keep `addMulSub_neg₀` as a **section-local / `private`** helper next
   to `addMulSub`, *not* as a public lemma. It is not independently citable and should not get its own
   mathlib name. If, post-cleanup, `addMulSub_abs₀` is the only consumer, consider inlining the
   ≤2-line proof into `addMulSub_abs₀` and dropping the named lemma entirely.

Next action: do **not** open a standalone mathlib PR for `addMulSub_neg₀`. Fold it into (a) the
intra-repo dedup of the triplicated `EllSequence` layer, then (b) the parent `addMulSub`/`rel₄` layer
upstreaming, where it lives as an internal helper. (Its standalone existence as a public decl is a
cleanup target, not a mathlib contribution.)

---

## Next step

`addMulSub_neg₀` is internal scaffolding for the `EllSequence` `addMulSub` building block, not a
standalone mathlib lemma. Standalone verdict: **NO-composable-from-mathlib** (≤2-line
`simp_rw [addMulSub, Int.neg_tdiv, neg]; ring` over mathlib's `Int.neg_tdiv` + the oddness
hypothesis). Action: ride it along with the parent `addMulSub`/`rel₄` elliptic-relation layer
upstreaming as a `private`/section-local helper (see `addMulSub.md`); first collapse the three
in-repo copies to one per `05-duplications.md`. No independent PR.

## Sources

- *Elliptic divisibility sequence* (oddness `W₋ₙ = −Wₙ`, four-index recurrence) — https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence
- Stange, *Elliptic nets and elliptic curves* (net antisymmetry `W(−v) = −W(v)`) — https://arxiv.org/abs/0710.1316
- *The sign of an elliptic divisibility sequence* (named result in this neighbourhood; oddness is background) — https://arxiv.org/abs/math/0402415
- Angdinata–Xu, *On Elliptic Sequences over Commutative Rings* (the paper behind this Lean development) — https://arxiv.org/pdf/2604.05280
- Mathlib4 docs, `Mathlib.NumberTheory.EllipticDivisibilitySequence` (`normEDS_neg`/`preNormEDS_neg`/`complEDS₂_neg`; no `EllSequence`/`addMulSub` layer; open `normEDS`-is-elliptic TODOs) — https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
- Sibling assessments (same directory): `addMulSub.md` (parent def, `YES-but-generalise-first`), `rel₄.md`, `net.md`, `net_add_sub_iff.md`.
