# /mathlibable report — `EllSequence.rel₄_fix₁_of_fix₂`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences). Single declaration.

---

### Baseline (Phase 0)

- lake build:               ⚠ not re-run (local build stale per task note); reasoning from source.
- decl `EllSequence.rel₄_fix₁_of_fix₂`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:427`
  (inside `namespace EllSequence` @ line 90, `section Rel₄OfValid` @ line 412).
- qualified name:           `EllSequence.rel₄_fix₁_of_fix₂` (VERIFIED — namespace walk confirms).
- kind:                      `lemma` (theorem-like; Phase 4.5 diamond check n/a).
- has sorry:                 no.
- module docstring summary:  Elliptic divisibility sequences (EDS) — defines `IsEllSequence`,
  `preNormEDS`, `normEDS`, `complEDS`; this file is a **fork+extension** of
  `Mathlib.NumberTheory.EllipticDivisibilitySequence` adding the `EllSequence.rel₄`/`net`/
  `Rel₄OfValid` four-index-relation machinery (NOT in current mathlib).

---

### Statement (Phase 1)

`EllSequence.rel₄_fix₁_of_fix₂` is a **lemma**, a technical sub-step inside a strong
induction. Setup (section variables): `W : ℤ → R` a sequence into a commutative ring `R`;
fixed indices `c₀ d₀ : ℤ` with `par : c₀.negOnePow = d₀.negOnePow` (same parity),
`le : 0 ≤ d₀`, `lt : d₀ < c₀`; an induction hypothesis
`rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b c₀ d₀`; and
`mem : addMulSub W c₀ d₀ ∈ R⁰` (the two-index coefficient is a non-zero-divisor).

The statement: for all `b c : ℤ`,
`Rel₄OfValid W a b c c₀ ∧ (c₀ < c → Rel₄OfValid W a b c d₀)`.

Here `Rel₄OfValid W a b c d` abbreviates "`HaveSameParity₄ a b c d → StrictAnti₄ a b c d →
rel₄ W a b c d = 0`": the four-index elliptic relation `rel₄` vanishes on quadruples of
non-negative, equal-parity, strictly-decreasing indices.

**Mathematical content (prose).** Assuming the four-index elliptic relation already vanishes
on every valid quadruple `(a', b, c₀, d₀)` with `a' ≤ a` (smaller leading index, both lower
indices fixed at `c₀, d₀`), this lemma upgrades the conclusion to quadruples that share **only
one** fixed index: `(a, b, c, c₀)` and (when `c₀ < c`) `(a, b, c, d₀)`. The proof is the
algebraic identity `rel₆_eq₃`/`rel₆_eq₃'` (a `rel₄` with one fixed index expands as an
alternating sum of three `rel₄`s with two fixed indices), each summand killed by `rel`, then
the non-zero-divisor `mem` cancels the `addMulSub W c₀ d₀` coefficient. It is one of three
"key lemmas" (`rel₆_eq₃`, `rel₆_eq₃'`, `rel₆_eq₁₀`) feeding the reduction.

Conclusion (math): the four-index elliptic relation, known with two fixed lower indices, holds
with one fixed lower index. Conclusion (Lean): `Rel₄OfValid W a b c c₀ ∧ (c₀ < c → Rel₄OfValid W a b c d₀)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a helper lemma — an intermediate induction step (not in `## Main statements`, not
person/place-named). The *parent* result `IsEllSequence.of_oddRec_evenRec` is BIG; this is one
internal rung of its proof's ladder.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-line check **n/a**. (Body is a ~10-line
tactic proof, not a one-liner anyway.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | EDS four-index relation rel4 Ward Stange elliptic nets proof                            | yes  | elliptic-net relation `W(p+q+s)W(p−q)W(r+s)W(r) − … = 0`; four-index `rel₄` is its same-parity form | concept = elliptic relation / elliptic net defining relation |
|  2 | WebSearch (general / over-rings) | mathlib EDS IsEllSequence normEDS division polynomial PR Angdinata                      | yes  | arXiv 2604.05280 "On Elliptic Sequences over Commutative Rings" (Junyan Xu, Apr 2026) | the *exact* source paper; references mathlib4 PR #13782 |
|  3 | WebSearch (named-after / aliases)| Ward EDS recurrence implies elliptic, Somos-4 ⇒ Somos-k, van der Poorten–Swart         | yes  | "gap-2 recurrence + nonzero initials ⇒ full relation; general m entailed by m=2" | van der Poorten–Swart arXiv:math/0412293; this is *exactly* `rel₄_of_oddRec_evenRec`'s thesis |
|  4 | ChatGPT MCP                      | (MCP flagged possibly-down per task; substituted by reading the source paper directly via WebFetch of arXiv:2604.05280) | n/a  | paper confirms four-index relation + single-index induction with fixed indices + Lean formalization | fallback used per task instructions |
|  5 | Local references                 | `.mathlib-quality/references/` grep                                                    | n/a  | directory absent    | recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                       | n/a  | nLab has no dedicated page; concept lives in NT/arithmetic-geometry literature, not categorical | not a categorical concept |
|  7 | nCatLab                          | —                                                                                      | n/a  | —                   | not a categorical concept |
|  8 | Stacks Project                   | elliptic divisibility sequence                                                          | n/a  | not in Stacks       | Stacks is scheme-theoretic AG foundations; EDS recurrence theory is out of scope |
|  9 | MathOverflow / MSE               | EDS recurrence ⇒ elliptic, coherence of Ward's definition                              | yes  | confirms coherence proofs (σ-function vs. direct); matches the induction approach | background, no new form |
| 10 | recent arXiv (last 5 yr)         | elliptic sequences commutative rings 2024–2026                                          | yes  | arXiv 2604.05280 (2026) is the state-of-the-art over-ℤ→over-`CommRing` generalization | = the development this file forks |

Protocol pass: WebSearch ≥3 distinct generality levels ✓; ChatGPT MCP substituted by direct
source-paper fetch (MCP down per task) ✓; local refs checked (absent) ✓; nLab/Stacks/nCatLab
checked + n/a-with-reason ✓; MathOverflow + arXiv ✓.

### Literature summary (Phase 3)

Concept identified as: the **four-index elliptic relation** `rel₄` (the same-parity / "valid"
specialization of Stange's **elliptic-net** defining relation `net`), and the theorem that the
single-index even/odd recurrences (`OddRec`/`EvenRec`, i.e. gap-2 Somos relations) **imply** the
full elliptic relation — equivalently, that `normEDS` is an `IsEllSequence`. The specific source
is **Junyan Xu, arXiv:2604.05280, "On Elliptic Sequences over Commutative Rings" (Apr 2026)**,
the modern treatment over an arbitrary `CommRing`; classical antecedents: Ward (1948),
van der Poorten–Swart (every Somos-4 is a Somos-k, arXiv:math/0412293), Stange (elliptic nets,
arXiv:0710.1316).

Sources agree on the standard form: **yes** at the level of the *theorem* (recurrences ⇒
elliptic relation). **However, `rel₄_fix₁_of_fix₂` itself is NOT a named result in the
literature** — it is an internal lemma of *one particular proof strategy* (the single-index
strong induction with progressively-freed fixed indices) that Xu's paper / the Lean formalization
adopt. The literature names the endpoints (the recurrences; the elliptic relation; coherence),
not this intermediate `rel₆`-expansion rung.

Most general standard form: over an arbitrary commutative ring `R`, exactly as stated here (the
paper's whole point is dropping the integral-domain/field hypotheses). The non-zero-divisor
conditions `W 1, W 2 ∈ R⁰` are the right replacement for "nonzero initial terms".

Generality dimensions where literature varies:
  - coefficient ring: ℤ (Ward) → integral domain → **arbitrary `CommRing`** (Xu 2026 = here). Here is maximal.
  - integrality of terms: classical assumes nonzero terms in a domain; here uses `∈ R⁰` (non-zero-divisor). Maximal.

Disagreement with the literature: none. The Lean form is the maximally-general (over-`CommRing`)
formulation and matches arXiv:2604.05280.

---

### Generality analysis — `EllSequence.rel₄_fix₁_of_fix₂`

Literature-standard form (Phase 3): over an arbitrary `CommRing`, with non-zero-divisor
hypotheses on the relevant `addMulSub`/initial terms — which is precisely the section setup here.

| # | Parameter / hypothesis                         | Current Lean form                  | Literature-standard form               | Weaker form exists? | Reason |
|---|------------------------------------------------|------------------------------------|----------------------------------------|---------------------|--------|
| 1 | `[CommRing R]`                                 | arbitrary commutative ring         | arbitrary commutative ring (Xu 2026)   | NO                  | already the most general base; proof is pure ring algebra (`ring`) + cancel-by-nonzerodivisor |
| 2 | `mem : addMulSub W c₀ d₀ ∈ R⁰`                 | coefficient is a non-zero-divisor  | "nonzero initial terms", generalized to `∈ R⁰` | NO          | this is the exact `CommRing`-correct weakening of "domain + nonzero"; cancellation needs it |
| 3 | `rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid …`       | induction hypothesis (well-founded on a) | n/a — internal to the induction   | NO                  | this *is* the IH of the strong induction; not a free parameter to weaken |
| 4 | indices `a b c c₀ d₀ : ℤ`, parity/order conds  | ℤ-indexed, same-parity, ordered    | ℤ-indexed (sequences are ℤ→R)          | NO                  | EDS are intrinsically ℤ-indexed; parity/order are the genuine hypotheses of `Rel₄OfValid` |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**.
Number of weakening opportunities found: 0.
Cost of restatement: n/a (nothing to restate). The over-`CommRing`, `∈ R⁰` formulation is
already the literature frontier (Xu 2026).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                          | Applies? | Proposed reformulation | Downstream |
|----|-----------------------------------------------------------------------------------|----------|------------------------|------------|
|  1 | "let X be a foo" → typeclass/instance?                                             | no       | hypotheses are non-zero-divisor membership + an induction hypothesis; not typeclass-shaped | — |
|  2 | sequences/metric → filters/topology?                                              | no       | finite algebraic identity over ℤ-indices; no limit/topology present | — |
|  3 | construction → universal-property class?                                          | no       | this is an equation-vanishing lemma, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                                | no       | no substructure here | — |
|  5 | vector-space/field-specific → weaken typeclasses?                                 | no — already done | already over arbitrary `CommRing` with `R⁰` (the modern weakening) | already maximal |
|  6 | 1-categorical → higher-categorical?                                               | no       | n/a | — |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                                    | no       | EDS are definitionally ℤ-indexed; generalizing the index is a *different* theory (elliptic nets over ℤⁿ), not a reformulation of this lemma | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The lemma is already in the contemporary mathlib idiom
(arbitrary `CommRing`, non-zero-divisor submonoid `R⁰`, `Int.negOnePow` for parity). It is a
finite combinatorial/algebraic identity; there is no filter-/topology-/category-theoretic
restatement to make. One-line reason: it is an internal `ring`-plus-cancellation step, not a
structural definition with a higher abstraction.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instance-search paths introduced).

---

### Mathlib search-status: `EllSequence.rel₄_fix₁_of_fix₂`

[A] Lean-Finder       — (index = current mathlib)         no hits — concept absent from mathlib
[B] Loogle            `rel₄`, `addMulSub`, `Rel₄OfValid` type-pattern   no hits — these symbols don't exist in mathlib
[C] LeanSearch        "four-index elliptic relation reduce fixed index"  no hits — closest is `IsEllSequence`, unrelated to this lemma
[D] Grep mathlib src  `grep -rn "rel₄\|addMulSub\|rel₆\|Rel₄OfValid\|rel₄_fix\|net_eq_rel₄\|HaveSameParity₄\|six_le_of_strictAnti"` over `.lake/packages/mathlib/Mathlib/`  → **0 matches**
[E] Name pattern      `rel₄_fix₁_of_fix₂`, `rel₄_of_min₂`, `rel₄_of_anti_oddRec_evenRec`, `of_oddRec_evenRec` over mathlib  → **0 matches**

Cross-checks:
  - mathlib docs page for `Mathlib.NumberTheory.EllipticDivisibilitySequence` lists ONLY
    `IsEllSequence`/`IsDivSequence`/`preNormEDS`/`normEDS`/`complEDS*` + `normEDSRec*` and basic
    lemmas. NO `EllSequence` namespace, NO `rel₄`/`net`/`Rel₄OfValid`/`OddRec`/`EvenRec`/
    `rel₄_of_oddRec_evenRec`/`IsEllSequence.of_oddRec_evenRec`. Confirmed against the pinned
    source too (mathlib EDS file = 547 lines, none of this machinery).
  - The upstreaming is **in flight**: source paper arXiv:2604.05280 (Junyan Xu) cites mathlib4
    **PR #13782** ("feat(EllipticCurve): ZSMul formula in terms of division polynomials"), which
    is currently **OPEN** (blocked-by-other-PR, merge-conflict; created 2024-06-12). So this whole
    development is pending, not merged.

Searched for both the user's form AND the literature-standard (recurrences-⇒-elliptic) theorem.

Concluded: **not in mathlib** (all 5 methods + docs + pinned source exhausted; the entire
`EllSequence.rel₄`/`Rel₄OfValid` track is absent from current mathlib and only present in an open,
not-yet-merged PR).

---

### Call sites — `EllSequence.rel₄_fix₁_of_fix₂`

Internal use count (this file, excluding the declaration): **3 uses**, all in the immediately
following lemmas of the **same induction**:
  - `EllipticDivisibilitySequence.lean:445` — `rel₄_of_fix₂` builds `fix₁`/`fix₂` from it.
  - `EllipticDivisibilitySequence.lean:446` — same.
  - `EllipticDivisibilitySequence.lean:448` — same (re-aimed IH).
  - `EllipticDivisibilitySequence.lean:464` — `rel₄_of_min₂` uses `.1`/`.2`.

External-to-file callers: **0 distinct files** within `projects/NagellLutz/`.

| Caller file:line                                   | Usage pattern (excerpt)                                              |
|----------------------------------------------------|---------------------------------------------------------------------|
| NagellLutz/…/EllipticDivisibilitySequence.lean:445 | `have fix₁ b c := (rel₄_fix₁_of_fix₂ par le lt rel mem b c).1`       |
| NagellLutz/…/EllipticDivisibilitySequence.lean:446 | `have fix₂ {b c} := (rel₄_fix₁_of_fix₂ par le lt rel mem b c).2`     |
| NagellLutz/…/EllipticDivisibilitySequence.lean:448 | `(rel₄_fix₁_of_fix₂ par le lt (fun h ↦ rel <| h.trans hba.le) mem _ _).1` |
| NagellLutz/…/EllipticDivisibilitySequence.lean:464 | `have fix := rel₄_fix₁_of_fix₂ (negOnePow_cMin_eq_dMin a) … rel …`   |

Inline-derivation grep (re-derived elsewhere without this lemma?): **none** — but note **whole-file
duplication**: byte-identical copies of this lemma exist in
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:406` and
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:351` (the same forked
file copied into 2 other projects). That is an intra-repo dedup concern (a `/cleanup` lane issue),
**orthogonal** to the mathlibable question.

Call-sites signal: K = 3 internal uses, **all inside the same proof's induction ladder**, 0
external-to-file consumers. This is the signature of *proof scaffolding*, not a reusable API
lemma — it exists to be consumed by `rel₄_of_fix₂`/`rel₄_of_min₂` two lines down, nowhere else.

---

### Composition check (Phase 6)

Can `EllSequence.rel₄_fix₁_of_fix₂` be derived from mathlib in ≤3 chained calls? **No.**

Attempt 1: it depends on `rel₆_eq₃`/`rel₆_eq₃'` (the `rel₆ = Σ rel₆` algebraic expansions),
`rel₆_eq`, `addMulSub`, `Rel₄OfValid`, `HaveSameParity₄`, `StrictAnti₄`, and the induction
hypothesis `rel` — **all project-local, none in mathlib**. There are no mathlib building blocks to
compose, because the entire `rel₄`/`rel₆`/`net` layer is absent from mathlib.
  - Mathlib decls used: (none available).
  - Result: fails.

Conclusion: **NOT-COMPOSABLE** from mathlib (the prerequisites themselves are the missing
development). Equally, it is not a 1–3 call composition *within the project* either: its proof is a
genuine ~10-line tactic argument (`rel₆_eq₃` rewrite, three `rel` applications, parity/order
discharge by `linarith`, cancellation by `mem.2`).

---

## Verdict: `EllSequence.rel₄_fix₁_of_fix₂`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the *theorem family* (recurrences ⇒ elliptic relation, over an
  arbitrary `CommRing`) is standard and current — Xu arXiv:2604.05280, Ward, van der Poorten–Swart.
  But `rel₄_fix₁_of_fix₂` itself is **not** a named literature result; it is an internal rung of
  one specific proof strategy.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; already the modern over-`CommRing`/`R⁰` idiom;
  no weakening and no modernization available.
- Mathlib search (Phase 5): NOT in mathlib — the whole `EllSequence.rel₄`/`Rel₄OfValid` track is
  absent and sits in an **open, unmerged** PR (#13782).
- Composition check (Phase 6): NOT-COMPOSABLE (its prerequisites are themselves not in mathlib).

**Rationale (why BORDERLINE rather than a clean YES or NO):**

This is the classic "right *development*, wrong *grain*" situation. The surrounding development —
`EllSequence.rel₄`/`net`/`Rel₄OfValid` culminating in `rel₄_of_oddRec_evenRec` and
`IsEllSequence.of_oddRec_evenRec` (and ultimately `normEDS` being an `IsEllSequence`) — is
genuinely mathlib-worthy: it is the over-commutative-ring generalization of Ward's coherence
theorem, written up in arXiv:2604.05280 and already targeted at mathlib via PR #13782. So a naive
"not in mathlib + maximally general + not composable" reading points at YES-add-as-is. **But that
verdict would be wrong for *this* declaration in isolation**, because `rel₄_fix₁_of_fix₂` is not a
standalone result a mathematician would state — it is proof scaffolding (call-sites: 3 uses, all
inside the same strong-induction, 0 external consumers; one of three sibling `rel₆`-expansion
lemmas `rel₄_fix₁_of_fix₂` / `rel₄_of_fix₂` / `rel₄_of_min₂` that exist only to carry the
induction). Whether it should appear in mathlib **as its own named lemma** versus be folded into /
shipped-with the parent proof is exactly an authorial-packaging judgment the skill should not make
unilaterally. The honest answer: **the development belongs in mathlib (and is en route); this
particular lemma should be upstreamed *as part of that development, not assessed or PR'd as a
standalone unit*.** It neither merits its own "feat: add `rel₄_fix₁_of_fix₂`" PR (NO-as-standalone)
nor is it redundant/composable junk to delete (the NO buckets misfire — mathlib lacks it and it is
load-bearing locally).

There is also a second, repo-internal wrinkle the human should note: this file is a **fork of
mathlib's EDS file** and the lemma is **byte-duplicated** across three projects (NagellLutz target,
`…EllipticDivisibilitySequenceOriginal.lean`, and HasseWeil's `Auxiliary/`). The mathlibable
disposition and the intra-repo dedup are separate actions.

**Numbered questions (≤5):**
1. Should this whole `EllSequence.rel₄`/`Rel₄OfValid` track (forked here from mathlib) be
   upstreamed **as one unit**, tracking/reviving mathlib PR #13782 + arXiv:2604.05280 — rather than
   assessing its internal lemmas one-by-one? (If **yes**, this lemma's verdict is "ships with the
   parent development; do not PR standalone" and no further per-lemma mathlibable work is needed on
   the `Rel₄OfValid` internals.)
2. Independently: should `EllSequence.rel₄_fix₁_of_fix₂` retain its **own name** in the upstreamed
   version, or be inlined into / merged with its only consumers `rel₄_of_fix₂`/`rel₄_of_min₂`?
   (A `/decompose-proof`-style packaging call.)
3. Is the intended upstream target literally mathlib **PR #13782** (revive/rebase it), or a fresh
   PR series re-deriving arXiv:2604.05280? (Determines whether "already in flight" closes this.)
4. The lemma is duplicated across NagellLutz (×2) and HasseWeil — should the repo first dedup these
   into one shared `Common/` copy (a `lane:cleanup` issue) before any upstreaming is considered?

**Next action:** user answers the questions. If Q1 = yes (the expected answer given PR #13782 /
arXiv:2604.05280), treat `rel₄_fix₁_of_fix₂` as **ships-with-parent**: no standalone PR, no further
standalone mathlibable assessment of the `Rel₄OfValid` internal lemmas; fold them into the existing
upstreaming effort and resolve the intra-repo triplication via a `lane:cleanup` ticket.

---

## Next step

User answers the four questions above (most decisively Q1). Expected resolution: this lemma is
**part of an in-flight mathlib contribution** (PR #13782 / Junyan Xu arXiv:2604.05280), to be
upstreamed *with* the `EllSequence.rel₄`/`Rel₄OfValid` development as a unit — not PR'd or deleted
as a standalone declaration — with the cross-project byte-duplication handled separately as repo
cleanup.
