# /mathlibable report — `EllSequence.rel₄_of_min₂`

Project: NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; elliptic divisibility sequences).
File: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:457`.
Run: `/overview` Step-9 mathlibable assessment, single declaration.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note); reasoned from source.
- decl `EllSequence.rel₄_of_min₂`: resolved at `EllipticDivisibilitySequence.lean:457`, namespace `EllSequence` (opened line 90).
- kind:                      `theorem`
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences (EDS): defines EDSs and constructs normalised EDSs from initial terms" (Ward, *Memoir on Elliptic Divisibility Sequences*).
- VERIFIED qualified name:   `EllSequence.rel₄_of_min₂` ✓ (matches the parsed name in the task).

---

### Statement (Phase 1)

`rel₄_of_min₂` is an **internal inductive-reduction step** in the formalised proof that a sequence
`W : ℤ → R` (with `W 1, W 2` non-zero-divisors) satisfies the four-index elliptic-net relation
`rel₄ W a b c d = 0` on all same-parity, strictly-decreasing, nonnegative quadruples.

Concretely, define
`Rel₄OfValid W a b c d := HaveSameParity₄ a b c d → StrictAnti₄ a b c d → rel₄ W a b c d = 0`
(the relation `rel₄ W a b c d := addMulSub W a b * addMulSub W c d − addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c` restricted to the "valid" regime), and let
`cMin a`, `dMin a` be the parity-matched **minimal** top two indices (`dMin a = if Even a then 0 else 1`, `cMin a = dMin a + 2`).

The theorem states: **if** `rel₄` vanishes on every quadruple of the *minimal* shape `(a', b, cMin a, dMin a)` for all `b` and all `a' ≤ a`, **then** it vanishes on `(a, b, c, d)` for *all* `b, c, d` (under the validity hypotheses). It is the step "having killed the relation on the minimal cases below `a`, kill it on arbitrary cases at `a`", assembling `rel₄_fix₁_of_fix₂` and `rel₄_of_fix₂` and discharging the relative-order technical conditions on the indices.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]`, `(W : ℤ → R)` — the EDS-candidate sequence.
- `nonZeroDivisors` scope (`R⁰`).

Hypotheses (Lean side):
- `(one : W 1 ∈ R⁰)`, `(two : W 2 ∈ R⁰)` — non-zero-divisor anchors (give `addMulSub W (cMin a) (dMin a) ∈ R⁰` so cancellation is legal).
- `(rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b (cMin a) (dMin a))` — the inductive hypothesis on minimal cases.
- `(b c d : ℤ)` — the target indices.

Conclusion (math): the four-index elliptic-net relation holds at `(a,b,c,d)` given it holds on all minimal cases below.
Conclusion (Lean): `Rel₄OfValid W a b c d`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper/inductive-step lemma about a bespoke predicate (`Rel₄OfValid`); not a named theorem, not a `## Main statement` (the file's only listed main statement is `isEllDivSequence_normEDS`), not a new structure. (Lit width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem` → n/a (one-line check applies to `def`/`abbrev`/`structure`). Body is a multi-line tactic proof.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (general framework) | "Stange elliptic nets net relation Ward EDS four-index recurrence" | yes (framework) | Stange's elliptic-net 4-parameter recurrence on `(p,q,r,s)`; Ward's EDS recurrence (rank-1) | the *framework* is published; the specific lemma is not |
| 2 | WebSearch (recurrence / division-poly form) | "EDS Ward memoir three-term recurrence W(m+n)W(m−n) division polynomial same parity indices" | yes (recurrence) | `Ψ_{m+n}Ψ_{m−n} = Ψ_{m+1}Ψ_{m−1}Ψ_n² − Ψ_{n+1}Ψ_{n−1}Ψ_m²`; equivalently the `Rel₃`/`IsEllSequence` form | the math object the framework computes; no "minimal-case reduction" lemma |
| 3 | WebSearch (named/aliases) | (covered by #1/#2: "Somos", "elliptic net", "division polynomial recurrence") | no (for this lemma) | — | no source states a "reduce to minimal indices `cMin/dMin`" lemma |
| 4 | ChatGPT MCP | n/a — MCP down per task note; substituted with the two structured WebSearches at framework + recurrence generality, plus reasoning from the file's own docstring (cites Ward) | n/a | — | fallback used as instructed |
| 5 | Local references | `ls projects/NagellLutz/.mathlib-quality/` and `refs/` | n/a | no PDFs; `refs/` absent | only reference named in-file is Ward's *Memoir* |
| 6 | nLab | "elliptic divisibility sequence" / "elliptic net" | n/a | not an nLab topic at this granularity | concept is number-theoretic/combinatorial, no categorical nLab entry for the reduction lemma |
| 7 | nCatLab | — | n/a | not categorical | finite ring-identity bookkeeping |
| 8 | Stacks Project | "elliptic divisibility sequence" | n/a | not in Stacks | Stacks covers schemes/AG foundations, not EDS recurrences |
| 9 | MathOverflow / MSE | "elliptic net recurrence minimal indices reduction" | no | — | no analog of this internal step |
| 10 | recent arXiv | "elliptic nets" (Stange 0710.1316; signs 1702.08102; van der Poorten math/0412293) | yes (framework) | confirms #1/#2; none states the formal minimal-case reduction | these are the canonical sources; the lemma is a formalisation artifact |

### Literature summary (Phase 3)

Concept identified as: **Stange's elliptic-net four-index recurrence** (general), specialising to **Ward's elliptic-divisibility-sequence recurrence** (rank 1) — equivalently the `Rel₃`/`IsEllSequence` form and the division-polynomial identity `Ψ_{m+n}Ψ_{m−n} = Ψ_{m+1}Ψ_{m−1}Ψ_n² − Ψ_{n+1}Ψ_{n−1}Ψ_m²`.
Sources agree on the standard form of the *recurrence*: yes.
Most general standard form: Stange's 4-parameter net recurrence.
But: `rel₄_of_min₂` **is not** a standard published statement. It is one **inductive-bookkeeping step** in the formal proof that this project's `rel₄`/`net` apparatus satisfies the recurrence — it reduces the general valid quadruple to a parity-matched "minimal" pair of top indices `(cMin a, dMin a)`. No paper isolates this step; it exists because the formalisation runs an `Int.strongRec` induction on the largest index `a`.
Disagreement with the literature: none — the literature simply operates at a different grain (it states the recurrence and its consequences, never this formal reduction).

---

### Generality analysis (Phase 4)

Literature-standard form: the elliptic-net recurrence itself (already at full `CommRing` generality in this development).

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form? | Reason |
|---|------------------------|-------------------|---------------------|--------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring (Ward/Stange work over rings/fields) | NO | already maximally general; `rel₄`/`addMulSub` are ring expressions |
| 2 | `W 1, W 2 ∈ R⁰` | non-zero-divisors | the cancellation the proof needs | NO | exactly the hypotheses that make `addMulSub W (cMin a)(dMin a) ∈ R⁰`, i.e. the cancellation in `mem.2`; can't be weakened |
| 3 | `Rel₄OfValid`/`StrictAnti₄`/`HaveSameParity₄`/`cMin`/`dMin` scaffolding | bespoke project predicates | (no literature analog) | n/a | these are formalisation-internal; not parameters one would "generalise" |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** for what it is (a `CommRing`-level internal step). Number of weakening opportunities: 0. It is, however, **narrow in audience**: it is phrased entirely in project-private vocabulary and is not a statement any consumer outside this proof would invoke.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|-----------|
| 1 | bundled hyps → typeclasses? | no | — | hyps `W 1,W 2 ∈ R⁰` are genuine data, not a "let X be a foo" preamble |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic ring identity; no topology |
| 3 | construction → universal property? | no | — | it's a relation-vanishing step, nothing to characterise universally |
| 4 | set+closure → bundled substructure? | no | — | no substructure here |
| 5 | vector-space/field → module/(semi)ring? | no | — | already `CommRing`; `rel₄` needs subtraction (ring), can't drop to semiring |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index → general monoid? | no | — | indices are genuinely `ℤ` (parity, `negOnePow`, strong induction on `ℤ`); not generalisable to an abstract index |

Modern idiom available: **no**. One-line reason: this is a finite ring-identity reduction step driven by an integer strong-induction; there is no contemporary mathlib idiom that reorganises it — its shape is dictated by the proof, not by a classical-vs-modern formulation choice.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (introduces no definitional equality or typeclass-search path).

---

### Mathlib search-status: `EllSequence.rel₄_of_min₂` (Phase 5)

[A] Lean-Finder    — n/a (mathlib-index tool); reasoned via direct grep of the pinned mathlib `d90090f`.
[B] Loogle          — type pattern is in terms of `Rel₄OfValid`/`cMin`/`dMin`, none of which exist in mathlib ⇒ unindexable; no hit.
[C] LeanSearch      — NL query "reduce four-index elliptic relation to minimal indices"; no mathlib result (concept absent).
[D] Grep mathlib src — searched `.lake/packages/mathlib/Mathlib/` for: `Rel₄OfValid`, `StrictAnti₄`, `HaveSameParity₄`, `def cMin`, `def dMin`, `def addMulSub`, `def avg₄`, `def rel₄`, `EvenRec`, `rel₄_of_min`, `rel₄_of_anti_oddRec_evenRec` → **0 hits each**. (`OddRec`: 2 hits, both UNRELATED — `Nat`/`evenOddRec`-style names, not this project's `OddRec W m` predicate.)
[E] Name pattern     — `rel₄_of_min₂` appears ONLY in three sibling project forks (NagellLutz current + `…Original.lean` + `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`); never in mathlib.

Mathlib EDS coverage check: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines) HAS the *construction* API — `IsEllSequence` (defined directly via the `Rel₃`-style equation), `IsDivSequence`, `IsEllDivSequence`, `preNormEDS'/preNormEDS`, `complEDS₂/complEDS'/complEDS`, `normEDS`, `normEDSRec`, `isEllDivSequence_normEDS`. It has **NONE** of the `addMulSub` / `rel₄` / `net` / `Rel₄OfValid` / `cMin` / `dMin` permutation-relation apparatus. That entire `rel₄`-relational framework (Stange-net flavoured) is **new in this project**.

Searched for both the user's form and the literature-standard recurrence (the latter = mathlib's `IsEllSequence`, which is present but is a *different, higher-level* object — the end goal, not this internal step).

Concluded: **not in mathlib** — neither the lemma nor any of the predicates it is phrased in. The statement is **not expressible** from mathlib primitives, because the very vocabulary (`rel₄`, `addMulSub`, `Rel₄OfValid`, `cMin`, `dMin`) is project-local.

---

### Composition check (Phase 6)

#### Call sites — `EllSequence.rel₄_of_min₂` (Phase 6.0)

Internal use count (this NagellLutz module, excluding the declaring file's own lines): **0**.
The only intra-project caller is **in the same file** — `rel₄_of_anti_oddRec_evenRec` at `EllipticDivisibilitySequence.lean:484` (the main inductive argument feeds `rel₄_of_min₂` as the per-`a` reduction inside `Int.strongRec`).

| Caller file:line | Usage pattern |
|------------------|---------------|
| `EllipticDivisibilitySequence.lean:484` (same file) | `… ↦ rel₄_of_min₂ one two fun {a' b} haa same anti ↦ by …` |
| `…/EllipticDivisibilitySequenceOriginal.lean:461` | sibling FORK — duplicate copy, not a real external consumer |
| `…/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:401` | sibling FORK — duplicate copy, not a real external consumer |

External-to-file callers (genuine): **0**. Inline re-derivation elsewhere: none (the framework is self-contained).

Call-site reading: this is a single-use, same-file inductive step — a textbook "private helper for one theorem" shape. It is not API anyone composes against; its sole purpose is to factor the big induction in `rel₄_of_anti_oddRec_evenRec`.

#### Composition attempt (Phase 6a)

Can `rel₄_of_min₂` be derived from mathlib in ≤3 chained calls? **No** — mathlib lacks `rel₄`, `addMulSub`, `Rel₄OfValid`, `cMin`, `dMin`, so the statement cannot even be written, let alone composed. Within the *project*, it is itself the composition of `rel₄_fix₁_of_fix₂` + `rel₄_of_fix₂` + the `cMin/dMin` specialisation lemmas (`negOnePow_cMin_eq_dMin`, `dMin_nonneg`, `dMin_lt_cMin`, `addMulSub_mem_nonZeroDivisors`, `dMin_le`, `add_two_le_iff_lt_of_even_sub`) — a multi-`have` proof with non-trivial order reasoning, i.e. a genuine proof, NOT a ≤3-call mathlib composition.

Conclusion: **NOT-COMPOSABLE from mathlib** (vocabulary absent). Project-internally it is a real proof, not a one-liner.

---

## Verdict: `EllSequence.rel₄_of_min₂`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the *framework* (Stange elliptic nets / Ward EDS recurrence / division-polynomial identity) is standard and published; **this specific lemma is not** — it is a formal inductive-reduction step with no literature analog.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for an internal `CommRing`-level step; no modern-idiom reorganisation; but **audience-narrow**, phrased entirely in project-private vocabulary.
- Mathlib search (Phase 5): **not in mathlib**; mathlib's EDS file has the construction API (`IsEllSequence`, `normEDS`, …) but none of the `rel₄`/`net`/`addMulSub`/`Rel₄OfValid`/`cMin`/`dMin` apparatus this lemma lives in.
- Composition check (Phase 6): NOT-COMPOSABLE (the statement isn't expressible from mathlib primitives); single same-file caller, 0 genuine external consumers.

**Rationale:**

`rel₄_of_min₂` is not a mathematical theorem a mathematician would cite — it is **proof engineering**: the "reduce an arbitrary valid quadruple to the minimal top-index pair `(cMin a, dMin a)`" step inside the `Int.strongRec` induction that proves this project's elliptic-net relation `rel₄ W a b c d = 0`. Its statement is built entirely from bespoke, project-private definitions (`Rel₄OfValid`, `StrictAnti₄`, `HaveSameParity₄`, `cMin`, `dMin`, `addMulSub`, `rel₄`), none of which exist in mathlib. So in isolation the lemma is firmly NOT mathlib material: it has one same-file caller, zero genuine external consumers, and no published analog.

The reason the verdict is **BORDERLINE rather than a flat NO** is that the lemma cannot be assessed independently of its framework. The *framework it belongs to* — a Stange-elliptic-net–flavoured `rel₄`/`net` relational layer culminating in `rel₄_of_anti_oddRec_evenRec` (which proves the four-index relation from the odd/even division-polynomial recurrences) — **is** mathematically real, is **absent from mathlib**, and plausibly **should** be upstreamed to sit alongside the existing `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` and the division-polynomial files this project also forks. If that decision is YES, then `rel₄_of_min₂` rides along **as an internal/`private` step of that upstream** (not a standalone public API entry). If that decision is NO, it stays project-local. That upstreaming call is a mathematical-taste + library-scope judgment the skill cannot make alone — it depends on whether mathlib wants the elliptic-net relational machinery at all, and at what granularity its internal lemmas are exposed.

Numbered questions (≤5):
1. Do you intend to upstream the whole `rel₄` / `net` / elliptic-net relational framework (the layer ending in `rel₄_of_anti_oddRec_evenRec`, proving the four-index relation from the odd/even recurrences) to mathlib alongside the existing `EllipticDivisibilitySequence`/`DivisionPolynomial` files? (yes/no)
2. If yes: should the internal scaffolding lemmas like `rel₄_of_min₂` (and `rel₄_fix₁_of_fix₂`, `rel₄_of_fix₂`) be shipped as `private`/`@[local]` helpers of that PR rather than public API? (yes/no)
3. If no upstreaming is planned: confirm `rel₄_of_min₂` is purely project-internal proof-engineering and should be excluded from any mathlibable list (so this assessment is closed as "internal, do not contribute"). (yes/no)
4. Note for dedup (out of scope for this verdict but worth flagging): three byte-identical forks of this lemma exist — `NagellLutz/…/EllipticDivisibilitySequence.lean`, `NagellLutz/…/EllipticDivisibilitySequenceOriginal.lean`, and `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`. Should these be consolidated into one shared `Common/` module before any upstreaming work? (yes/no)

**Next action:** user answers the questions above; the verdict resolves to NO-composable-from-mathlib (if the framework is *not* upstreamed — the lemma is internal and inexpressible from mathlib) or folds into a single framework-level upstreaming PR with `rel₄_of_min₂` as a private helper (if it *is*). The lemma is never a standalone `YES-add-as-is`.

---

## Next step

User answers questions 1–4. If no upstreaming: close as internal (effectively NO-composable-from-mathlib — not expressible from mathlib primitives, single same-file caller). If upstreaming the `rel₄`/elliptic-net framework: include `rel₄_of_min₂` as a `private` step of that PR, and first consolidate the three forks into a shared module.
