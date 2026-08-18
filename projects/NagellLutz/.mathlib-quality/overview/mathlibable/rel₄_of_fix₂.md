# /mathlibable report — `EllSequence.rel₄_of_fix₂`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences). Single declaration.

---

### Baseline (Phase 0)

- lake build:               ⚠ not re-run (local build stale per task note); reasoning from source.
- decl `EllSequence.rel₄_of_fix₂`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:442`
  (inside `namespace EllSequence` @ line 90, `section Rel₄OfValid` @ line 412).
- qualified name:           `EllSequence.rel₄_of_fix₂` (VERIFIED — namespace walk: `namespace EllSequence`
  at line 90 is the only enclosing namespace; section `Rel₄OfValid` adds no namespace).
- kind:                      `lemma` (theorem-like; Phase 4.5 diamond check n/a).
- has sorry:                 no.
- module docstring summary:  Elliptic divisibility sequences (EDS) — defines `IsEllSequence`,
  `preNormEDS`, `normEDS`, `complEDS`; this file is a **fork+extension** of
  `Mathlib.NumberTheory.EllipticDivisibilitySequence` adding the `EllSequence.rel₄`/`net`/
  `Rel₄OfValid` four-index-relation machinery (NOT in current mathlib).

---

### Statement (Phase 1)

`EllSequence.rel₄_of_fix₂` is a **lemma**, a technical sub-step inside a strong induction. Setup
(section variables of `section Rel₄OfValid`): `W : ℤ → R` a sequence into a commutative ring `R`;
fixed indices `c₀ d₀ : ℤ` with `par : c₀.negOnePow = d₀.negOnePow` (same parity), `le : 0 ≤ d₀`,
`lt : d₀ < c₀`; an induction hypothesis `rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b c₀ d₀`; and
`mem : addMulSub W c₀ d₀ ∈ R⁰` (the two-index coefficient is a non-zero-divisor).

The statement: for all `b c d : ℤ` with `hc : c₀ < d` and `par' : d.negOnePow = d₀.negOnePow`,
`Rel₄OfValid W a b c d`.

Here `Rel₄OfValid W a b c d` abbreviates "`HaveSameParity₄ a b c d → StrictAnti₄ a b c d →
rel₄ W a b c d = 0`": the four-index elliptic relation `rel₄` vanishes on quadruples of
non-negative, equal-parity, strictly-decreasing indices.

**Mathematical content (prose).** This is the **second** of the two index-freeing lemmas in the
single-index strong induction (the first being its only dependency, `rel₄_fix₁_of_fix₂`). Assuming
the four-index elliptic relation already vanishes on every valid quadruple `(a', b, c₀, d₀)` with
`a' ≤ a` (smaller leading index, both lower indices fixed at `c₀, d₀`), `rel₄_fix₁_of_fix₂`
upgraded the conclusion to **one** fixed index; `rel₄_of_fix₂` here completes the step by removing
the **last** fixed index, proving the relation for a fully general valid quadruple `(a, b, c, d)`
(with `d > c₀`, `d` of the right parity). The proof is the ten-term algebraic identity `rel₆_eq₁₀`
(a `rel₄` with no fixed lower index expands as a signed sum of ten `rel₄`s each carrying a fixed
index), every summand killed by the one-fixed-index lemmas `fix₁ := (rel₄_fix₁_of_fix₂ …).1` /
`fix₂ := (rel₄_fix₁_of_fix₂ …).2` (and a re-aimed induction hypothesis `rel`), then the
non-zero-divisor `mem.2` cancels the `addMulSub W c₀ d₀` coefficient. It is the third of three
"key lemmas" (`rel₆_eq₃`, `rel₆_eq₃'`, `rel₆_eq₁₀`) feeding the reduction; the parity/ordering
side-conditions on the ten summands are discharged by `linarith`.

Conclusion (math): the four-index elliptic relation, known with two fixed lower indices, holds with
**no** fixed lower index (any valid quadruple). Conclusion (Lean): `Rel₄OfValid W a b c d`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a helper lemma — the second intermediate index-freeing rung of a strong induction (NOT in
`## Main statements`, which lists only `isEllDivSequence_normEDS`; not person/place-named). The
*parent* result of this induction (`rel₄_of_anti_oddRec_evenRec` → `IsEllSequence` for `normEDS`)
is BIG; this is one internal rung of its proof's ladder.

(Literature width run EXHAUSTIVE regardless — see Phase 3.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-line check **n/a**. (Body is a multi-line
tactic proof — `rel₆_eq₁₀` rewrite, six `fix₁`/`fix₂` applications, three `rel`, a re-aimed
`rel₄_fix₁_of_fix₂`, and a 10-fold `linarith` side-condition discharge — not a one-liner.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | EDS four-index relation rel4 Ward Stange elliptic nets proof                            | yes  | elliptic-net relation `W(p+q+s)W(p−q)W(r+s)W(r) − … = 0`; four-index `rel₄` is its same-parity form | concept = elliptic relation / elliptic net defining relation |
|  2 | WebSearch (general / over-rings) | mathlib EDS IsEllSequence normEDS division polynomial Angdinata over commutative ring   | yes  | arXiv:2604.05280 "On Elliptic Sequences over Commutative Rings" (Junyan Xu, Apr 2026) | the *exact* source paper; references mathlib4 PR #13782 |
|  3 | WebSearch (named-after / aliases)| Ward EDS recurrence implies elliptic; van der Poorten–Swart Somos-4 ⇒ Somos-k          | yes  | "gap-2 recurrence + nonzero initials ⇒ full relation; general m entailed by m=2" | van der Poorten–Swart arXiv:math/0412293 — exactly `rel₄_of_anti_oddRec_evenRec`'s thesis |
|  4 | ChatGPT MCP                      | (MCP flagged down per task note; substituted by the source paper directly — arXiv:2604.05280 — and by the already-completed sibling `rel₄_fix₁_of_fix₂` lit sweep) | n/a  | paper confirms four-index relation + single-index induction with progressively-freed fixed indices + Lean formalization | fallback used per task instructions |
|  5 | Local references                 | `.mathlib-quality/references/` grep                                                    | n/a  | directory absent (`projects/NagellLutz/.mathlib-quality/references/` does not exist; `refs/` store absent in this checkout) | recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                       | n/a  | nLab has no dedicated page; concept lives in NT/arithmetic-geometry literature, not categorical | not a categorical concept |
|  7 | nCatLab                          | —                                                                                      | n/a  | —                   | not a categorical concept |
|  8 | Stacks Project                   | elliptic divisibility sequence                                                          | n/a  | not in Stacks       | Stacks = scheme-theoretic AG foundations; EDS recurrence theory out of scope |
|  9 | MathOverflow / MSE               | EDS recurrence ⇒ elliptic; coherence of Ward's definition                              | yes  | confirms coherence proofs (σ-function vs. direct algebraic induction); matches the induction approach | background, no new *named* form for this rung |
| 10 | recent arXiv (last 5 yr)         | elliptic sequences commutative rings 2024–2026                                          | yes  | arXiv:2604.05280 (2026) is the state-of-the-art over-ℤ → over-`CommRing` generalization | = the development this file forks |

Protocol pass: WebSearch ≥3 distinct generality levels ✓; ChatGPT MCP substituted (down per task)
by direct source-paper reading + the sibling sweep ✓; local refs checked (absent) ✓;
nLab/Stacks/nCatLab checked + n/a-with-reason ✓; MathOverflow + arXiv ✓.

### Literature summary (Phase 3)

Concept identified as: the **four-index elliptic relation** `rel₄` (the same-parity / "valid"
specialization of Stange's **elliptic-net** defining relation `net`), and the theorem that the
single-index even/odd recurrences (`OddRec`/`EvenRec`, i.e. gap-2 Somos relations) **imply** the
full elliptic relation — equivalently, that `normEDS` is an `IsEllSequence`. The specific source is
**Junyan Xu, arXiv:2604.05280, "On Elliptic Sequences over Commutative Rings" (Apr 2026)**, the
modern treatment over an arbitrary `CommRing`; classical antecedents: Ward (1948), van der
Poorten–Swart (every Somos-4 is a Somos-k, arXiv:math/0412293), Stange (elliptic nets,
arXiv:0710.1316).

Sources agree on the standard form: **yes** at the level of the *theorem* (recurrences ⇒ elliptic
relation). **However, `rel₄_of_fix₂` itself is NOT a named result in the literature** — it is the
second of two index-freeing lemmas internal to *one particular proof strategy* (the single-index
strong induction with progressively-freed fixed indices) that Xu's paper / the Lean formalization
adopt. The literature names the endpoints (the recurrences; the elliptic relation; coherence), not
this intermediate `rel₆_eq₁₀`-expansion rung.

Most general standard form: over an arbitrary commutative ring `R`, exactly as stated here (the
paper's whole point is dropping the integral-domain/field hypotheses). The non-zero-divisor
conditions (`W 1, W 2 ∈ R⁰`, surfacing here as `mem : addMulSub W c₀ d₀ ∈ R⁰`) are the right
replacement for "nonzero initial terms".

Generality dimensions where the literature varies:
  - coefficient ring: ℤ (Ward) → integral domain → **arbitrary `CommRing`** (Xu 2026 = here). Here is maximal.
  - integrality of terms: classical assumes nonzero terms in a domain; here uses `∈ R⁰` (non-zero-divisor). Maximal.

Disagreement with the literature: none. The Lean form is the maximally-general (over-`CommRing`)
formulation and matches arXiv:2604.05280.

---

### Generality analysis — `EllSequence.rel₄_of_fix₂`

Literature-standard form (Phase 3): over an arbitrary `CommRing`, with non-zero-divisor hypotheses
on the relevant `addMulSub`/initial terms — which is precisely the section setup here.

| # | Parameter / hypothesis                         | Current Lean form                  | Literature-standard form               | Weaker form exists? | Reason |
|---|------------------------------------------------|------------------------------------|----------------------------------------|---------------------|--------|
| 1 | `[CommRing R]`                                 | arbitrary commutative ring         | arbitrary commutative ring (Xu 2026)   | NO                  | already the most general base; proof is pure ring algebra (`ring` via `rel₆_eq₁₀`) + cancel-by-nonzerodivisor |
| 2 | `mem : addMulSub W c₀ d₀ ∈ R⁰`                 | coefficient is a non-zero-divisor  | "nonzero initial terms", generalized to `∈ R⁰` | NO          | the exact `CommRing`-correct weakening of "domain + nonzero"; final cancellation (`mem.2`) needs it |
| 3 | `rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid …`       | induction hypothesis (well-founded on `a`) | n/a — internal to the induction | NO              | this *is* the IH of the strong induction; not a free parameter to weaken |
| 4 | `hc : c₀ < d`, `par' : d.negOnePow = d₀.negOnePow` | order + parity on the freed index `d` | the genuine hypotheses placing `d` in a valid quadruple | NO       | these are the side-conditions of the induction rung, consumed by the `linarith` discharge; not slack |
| 5 | indices `a b c d c₀ d₀ : ℤ`                    | ℤ-indexed, same-parity, ordered    | ℤ-indexed (sequences are ℤ→R)          | NO                  | EDS are intrinsically ℤ-indexed; parity/order are the genuine hypotheses of `Rel₄OfValid` |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**.
Number of weakening opportunities found: 0.
Cost of restatement: n/a (nothing to restate). The over-`CommRing`, `∈ R⁰` formulation is already
the literature frontier (Xu 2026).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                          | Applies? | Proposed reformulation | Downstream |
|----|-----------------------------------------------------------------------------------|----------|------------------------|------------|
|  1 | "let X be a foo" → typeclass/instance?                                             | no       | hypotheses are non-zero-divisor membership + an induction hypothesis + order/parity facts; not typeclass-shaped | — |
|  2 | sequences/metric → filters/topology?                                              | no       | finite algebraic identity over ℤ-indices; no limit/topology present | — |
|  3 | construction → universal-property class?                                          | no       | this is an equation-vanishing lemma, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                                | no       | no substructure here | — |
|  5 | vector-space/field-specific → weaken typeclasses?                                 | no — already done | already over arbitrary `CommRing` with `R⁰` (the modern weakening) | already maximal |
|  6 | 1-categorical → higher-categorical?                                               | no       | n/a | — |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                                    | no       | EDS are definitionally ℤ-indexed; generalizing the index is a *different* theory (elliptic nets over ℤⁿ), not a reformulation of this lemma | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The lemma is already in the contemporary mathlib idiom (arbitrary
`CommRing`, non-zero-divisor submonoid `R⁰`, `Int.negOnePow` for parity). It is a finite
combinatorial/algebraic identity (`rel₆_eq₁₀` is a `ring` fact); there is no
filter-/topology-/category-theoretic restatement to make. One-line reason: it is an internal
`rel₆_eq₁₀`-rewrite-plus-cancellation step, not a structural definition with a higher abstraction.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instance-search paths introduced).

---

### Mathlib search-status: `EllSequence.rel₄_of_fix₂`

[A] Lean-Finder       — (index = current mathlib)        no hits — concept absent from mathlib
[B] Loogle            `rel₄`, `addMulSub`, `Rel₄OfValid` type-pattern   no hits — these symbols don't exist in mathlib
[C] LeanSearch        "four-index elliptic relation free fixed index"   no hits — closest is `IsEllSequence`, unrelated to this rung
[D] Grep mathlib src  `grep -rnE "rel₄_of_fix₂|Rel₄OfValid|\brel₄\b|addMulSub|rel₆|HaveSameParity₄|StrictAnti₄|rel₄_of_min₂|rel₄_of_anti_oddRec_evenRec"` over `.lake/packages/mathlib/Mathlib/`  → **0 matches** (re-run for this report)
[E] Name pattern      `rel₄_of_fix₂`, `rel₄_fix₁_of_fix₂`, `rel₄_of_min₂`, `rel₄_of_anti_oddRec_evenRec` over mathlib  → **0 matches**

Cross-checks:
  - The pinned mathlib EDS file (`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`,
    547 lines) contains ONLY `IsEllSequence`/`IsDivSequence`/`IsEllDivSequence`/`preNormEDS`/`normEDS`/
    `complEDS*` and their basic lemmas/`map_*`. There is **no** `EllSequence` namespace, **no**
    `rel₄`/`net`/`rel₆`/`Rel₄OfValid`/`OddRec`/`EvenRec`, and `normEDS` is **not** proven to be an
    `IsEllSequence` there (`grep` for `isEllSequence_normEDS` / `sorry` → 0 hits). Confirmed against
    the pinned source directly.
  - The upstreaming is **in flight**: source paper arXiv:2604.05280 (Junyan Xu) cites mathlib4
    **PR #13782** ("feat(EllipticCurve): …division-polynomial / EDS-elliptic machinery"), which is
    **open / not merged**. So this whole `rel₄`/`Rel₄OfValid` development is pending upstream, not present.

Searched for both the user's form AND the literature-standard (recurrences-⇒-elliptic) theorem.

Concluded: **not in mathlib** (all 5 methods + the pinned-source read exhausted; the entire
`EllSequence.rel₄`/`Rel₄OfValid` track is absent from current mathlib and only present in an open,
not-yet-merged PR).

---

### Call sites — `EllSequence.rel₄_of_fix₂`

Internal use count (this file, excluding the declaration itself): **1 use**.
  - `EllipticDivisibilitySequence.lean:461` — inside `rel₄_of_min₂`, the immediately-following lemma
    of the **same induction**: `refine rel₄_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a)
    (dMin_lt_cMin a) rel (addMulSub_mem_nonZeroDivisors one two a) _ _ _ hc ?_ …`. It specializes
    `c₀ := cMin a`, `d₀ := dMin a` and discharges the `c₀ < d` branch.

External-to-file callers (within `projects/NagellLutz/`): **0 distinct files** (full-repo grep of
`projects/` returns only line 461 of the live file plus the duplicate copies — see below).

| Caller file:line                                   | Usage pattern (excerpt)                                                       |
|----------------------------------------------------|-------------------------------------------------------------------------------|
| NagellLutz/…/EllipticDivisibilitySequence.lean:461 | `refine rel₄_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel …` |

Inline-derivation grep (re-derived elsewhere without this lemma?): **none** — but note **whole-file
duplication**: the lemma exists byte-for-byte in two sibling forks,
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:421` and
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:364` (the same forked file
copied into another project + an "Original" snapshot). That is an intra-repo dedup concern (a
`/cleanup` / `lane:cleanup` issue), **orthogonal** to the mathlibable question.

Call-sites signal: **K = 1** internal use, inside the *single* consumer `rel₄_of_min₂` two rungs
down the same strong induction, **0** external-to-file consumers. This is the signature of *proof
scaffolding*, not a reusable API lemma — it exists solely to be consumed by `rel₄_of_min₂` (which in
turn feeds `rel₄_of_anti_oddRec_evenRec`), nowhere else. (Per the verdicts reference, `K = 1`
internal-only leans toward NO-composable / packaging concern.)

---

### Composition check (Phase 6)

Can `EllSequence.rel₄_of_fix₂` be derived from mathlib in ≤3 chained calls? **No.**

Attempt 1: it depends on `rel₆_eq₁₀` (the ten-term `rel₆ = Σ rel₆` algebraic expansion), `rel₆_eq`,
`addMulSub`, `Rel₄OfValid`, `HaveSameParity₄`, `StrictAnti₄`, its sibling `rel₄_fix₁_of_fix₂`, and
the induction hypothesis `rel` — **all project-local, none in mathlib**. There are no mathlib
building blocks to compose, because the entire `rel₄`/`rel₆`/`net` layer is absent from mathlib.
  - Mathlib decls used: (none available).
  - Result: fails.

Conclusion: **NOT-COMPOSABLE** from mathlib (the prerequisites themselves are the missing
development). Equally, it is not a 1–3 call composition *within the project* either: its proof is a
genuine multi-step tactic argument (`rel₆_eq₁₀` rewrite; `have fix₁`/`fix₂` from
`rel₄_fix₁_of_fix₂`; six `fix₁`/`fix₂` rewrites + three `rel le_rfl` + one re-aimed
`rel₄_fix₁_of_fix₂`; then a 10-fold parity/order discharge by `linarith` and cancellation by
`mem.2`).

---

## Verdict: `EllSequence.rel₄_of_fix₂`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the *theorem family* (recurrences ⇒ elliptic relation, over an
  arbitrary `CommRing`) is standard and current — Xu arXiv:2604.05280, Ward, van der Poorten–Swart.
  But `rel₄_of_fix₂` itself is **not** a named literature result; it is the second of two
  index-freeing rungs internal to one specific proof strategy.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; already the modern over-`CommRing`/`R⁰` idiom;
  no weakening (4b) and no modernization (4c) available.
- Mathlib search (Phase 5): NOT in mathlib — the whole `EllSequence.rel₄`/`Rel₄OfValid` track is
  absent (0 grep matches in pinned mathlib) and sits in an **open, unmerged** PR (#13782).
- Composition check (Phase 6): NOT-COMPOSABLE (its prerequisites are themselves not in mathlib);
  call-sites K = 1 (single internal consumer, 0 external) → proof-scaffolding signature.

**Rationale (why BORDERLINE rather than a clean YES or NO):**

This is the classic "right *development*, wrong *grain*" situation, and it is consistent with the
sibling verdict on `rel₄_fix₁_of_fix₂` (the lemma `rel₄_of_fix₂` is built directly on top of, at
lines 445–448). The surrounding development — `EllSequence.rel₄`/`net`/`Rel₄OfValid` culminating in
`rel₄_of_anti_oddRec_evenRec` and `normEDS` being an `IsEllSequence` — is genuinely mathlib-worthy:
it is the over-commutative-ring generalization of Ward's coherence theorem, written up in
arXiv:2604.05280 and already targeted at mathlib via PR #13782. So a naive "not in mathlib +
maximally general + not composable" reading points at YES-add-as-is. **But that verdict would be
wrong for *this* declaration in isolation**, because `rel₄_of_fix₂` is not a standalone result a
mathematician would state — it is proof scaffolding (call-sites: 1 internal use, inside the same
strong induction's `rel₄_of_min₂`, 0 external consumers; it is one of the three `rel₆`-expansion
lemmas `rel₄_fix₁_of_fix₂` / `rel₄_of_fix₂` / `rel₄_of_min₂` that exist only to carry the
induction). Whether it should appear in mathlib **as its own named lemma** versus be folded into /
shipped-with the parent proof is exactly an authorial-packaging judgment the skill should not make
unilaterally. The honest answer: **the development belongs in mathlib (and is en route); this
particular lemma should be upstreamed *as part of that development, not assessed or PR'd as a
standalone unit*.** It neither merits its own "feat: add `rel₄_of_fix₂`" PR (NO-as-standalone) nor
is it redundant/composable junk to delete (the NO buckets misfire — mathlib lacks it and it is
load-bearing locally).

There is also a second, repo-internal wrinkle the human should note: this file is a **fork of
mathlib's EDS file**, and the lemma is **byte-duplicated** across three places (NagellLutz target;
`…EllipticDivisibilitySequenceOriginal.lean`; HasseWeil's `Auxiliary/`). The mathlibable disposition
and the intra-repo dedup are separate actions.

**Numbered questions (≤5):**
1. Should this whole `EllSequence.rel₄`/`Rel₄OfValid` track (forked here from mathlib) be upstreamed
   **as one unit**, tracking/reviving mathlib PR #13782 + arXiv:2604.05280 — rather than assessing
   its internal lemmas one-by-one? (If **yes**, this lemma's verdict is "ships with the parent
   development; do not PR standalone" and no further per-lemma mathlibable work is needed on the
   `Rel₄OfValid` internals.)
2. Independently: should `EllSequence.rel₄_of_fix₂` retain its **own name** in the upstreamed
   version, or be inlined into / merged with its only consumer `rel₄_of_min₂` (and its sibling
   `rel₄_fix₁_of_fix₂`)? (A `/decompose-proof`-style packaging call.)
3. Is the intended upstream target literally mathlib **PR #13782** (revive/rebase it), or a fresh PR
   series re-deriving arXiv:2604.05280? (Determines whether "already in flight" closes this.)
4. The lemma is duplicated across NagellLutz (×2, including the `…Original` snapshot) and HasseWeil
   — should the repo first dedup these into one shared `Common/` copy (a `lane:cleanup` issue)
   before any upstreaming is considered?

**Next action:** user answers the questions. If Q1 = yes (the expected answer given PR #13782 /
arXiv:2604.05280), treat `rel₄_of_fix₂` as **ships-with-parent**: no standalone PR, no further
standalone mathlibable assessment of the `Rel₄OfValid` internal lemmas; fold them into the existing
upstreaming effort and resolve the intra-repo triplication via a `lane:cleanup` ticket.

---

## Next step

User answers the four questions above (most decisively Q1). Expected resolution: this lemma is
**part of an in-flight mathlib contribution** (PR #13782 / Junyan Xu arXiv:2604.05280), to be
upstreamed *with* the `EllSequence.rel₄`/`Rel₄OfValid` development as a unit — not PR'd or deleted
as a standalone declaration — with the cross-project byte-duplication handled separately as repo
cleanup. This mirrors the sibling verdict on `rel₄_fix₁_of_fix₂`.
