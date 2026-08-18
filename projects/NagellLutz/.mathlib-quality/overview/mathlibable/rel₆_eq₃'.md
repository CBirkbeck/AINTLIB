# /mathlibable report — `EllSequence.rel₆_eq₃'`

## Verdict: **BORDERLINE-needs-human**

One-line: an internal `ring`-provable identity in a not-yet-upstreamed EDS-relations
apparatus that is itself a near-verbatim copy of David Angdinata's mathlib EDS code;
the only real question is the upstreaming policy for the whole `rel₄`/`rel₆` block.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — statement is a closed `ring` identity, no elaboration ambiguity)
- decl `EllSequence.rel₆_eq₃'`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:328`
- qualified name:           `EllSequence.rel₆_eq₃'` (namespace `EllSequence` open lines 90–597; nested `HaveSameParity₄`/`transf` close at 297/299 before line 328 — VERIFIED)
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  defines elliptic divisibility sequences (EDS) and constructs normalised EDSs; author David Kurniadi Angdinata (same author as mathlib's EDS + DivisionPolynomial files)

---

### Statement (Phase 1)

`rel₆_eq₃'` is a **polynomial identity** in the algebraic apparatus the file builds for
proving the four-index elliptic relation. With `W : ℤ → R` (`R` a commutative ring):

- `addMulSub W m n := W((m+n).tdiv 2) * W((m−n).tdiv 2)` — the basic building block.
- `rel₄ W a b c d := addMulSub W a b * addMulSub W c d − addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c` — the four-index relation (three pairings of four indices).
- `rel₆ W k l a b c d := addMulSub W k l * rel₄ W a b c d` — `rel₄` scaled by a two-index coefficient (an `abbrev`).

The lemma asserts, for all `c d m n r : ℤ`:

```
rel₆ W c d m n r d = rel₆ W m d n r c d − rel₆ W n d m r c d + rel₆ W r d m n c d
```

Mathematically: a `rel₄` with one fixed index `d` and three free indices `m,n,r` (scaled by
`addMulSub W c d`) re-expands as a signed combination of three `rel₆`'s, each sharing the
**smaller** fixed index `d` and two of `m,n,r`. It is the mirror image of the sibling
`rel₆_eq₃` (line 320), which shares the **larger** fixed index `c`. Both feed the
ten-term expansion `rel₆_eq₁₀` (line 336) and the `Rel₄OfValid` induction.

- Conclusion (math): an algebraic re-expansion identity (no hypotheses, holds in every comm ring).
- Conclusion (Lean): an equation in `R`.
- Proof: `by simp_rw [rel₆, rel₄]; ring` — a pure ring identity after unfolding two definitions.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma — an unfold-then-`ring` algebraic identity, scaffolding for the
`Rel₄OfValid` induction. Not a named theorem, not a `## Main statements` entry, not a structure.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — one-liner check is **n/a**. (The *proof*
is one line, but Phase 2b concerns one-line *definitions*; this gate does not apply to lemmas.)
The one-line `ring` proof is, however, the central signal for Phase 6.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence four-index relation … rel₄ addMulSub formalization Lean mathlib" | partial | EDS/elliptic-net recurrence, not this identity | Wikipedia + arXiv 0803.0728 confirm the net relation; no "rel₆_eq₃'" |
|  2 | WebSearch (author / general)     | "Angdinata … mathlib rel₄ rel₆ EllSequence net Stange formalisation"                            | partial | mathlib EDS API; ITP 2023 group-law paper | confirms this is Angdinata's territory; the `rel₄`/`rel₆` apparatus is not in the literature as named results |
|  3 | WebSearch (named-after / source) | Ward *Memoir on EDS*; Stange *elliptic nets* defining recurrence                                 | yes  | $`W(p+q+s)W(p-q)W(r+s)W(r) - \dots = 0`$ (the `net` relation) | the file's `net`/`rel₄` are formalisations of Ward/Stange; `rel₆_eq₃'` is a derived algebraic step, not in either |
|  4 | ChatGPT MCP                      | standard form / generality / history of the identity                                            | n/a  | — | MCP down per task; substituted with extra WebSearch + direct mathlib-source grep (the load-bearing check) |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/`, `refs/NagellLutz/`                           | n/a  | — | neither directory exists (verified); module cites only "M Ward, Memoir on EDS" |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                               | n/a  | — | nLab has no EDS/elliptic-net page; not a category-theoretic concept |
|  7 | nCatLab (categorical)            | —                                                                                              | n/a  | — | not a categorical concept |
|  8 | Stacks Project (alg geom)        | —                                                                                              | n/a  | — | EDS recurrences are not a Stacks topic (division polynomials appear only tangentially) |
|  9 | MathOverflow / MSE               | EDS four-index relation generality                                                              | n/a  | — | folded into WebSearch #1–3; surfaces the net relation only, never this internal step |
| 10 | recent arXiv (≤5y)               | "recurrence relation for elliptic divisibility sequences" (arXiv 2102.07573)                    | yes  | recurrence relations for EDS | confirms the genre; the specific `rel₆` bookkeeping identity is a formalisation artifact, not a paper result |

### Literature summary (Phase 3)

- Concept identified as: an **internal algebraic identity** in the proof of the four-index
  elliptic relation for EDS / elliptic nets (Ward, Stange). It is one of the three
  re-expansion identities (`rel₆_eq₃`, `rel₆_eq₃'`, `rel₆_eq₁₀`) the formalisation uses to
  drive the `Rel₄OfValid` strong induction.
- Sources agree on the standard form: **n/a** — the literature names the *net relation*
  (degree-4 in `W`), not these `rel₄`/`rel₆` bookkeeping identities. `rel₆_eq₃'` has no
  literature analog as a standalone statement; it is a `ring` consequence of how `rel₄` is
  bundled.
- Most general standard form: the underlying mathematics (the net relation) is already at full
  generality (arbitrary comm ring `R`, arbitrary `W : ℤ → R`).
- Disagreement with the literature: none — the file's `net` deliberately reorders Stange's two
  terms and swaps two signs to make equivalence with `rel₄` unconditional in char 3 (documented
  at lines 107–119). `rel₆_eq₃'` sits downstream of that and inherits the choice.

---

### Generality analysis — `EllSequence.rel₆_eq₃'` (Phase 4)

Literature-standard form: n/a (no standalone literature statement). Compare instead against the
maximal Lean generality the identity itself admits.

| # | Parameter / hypothesis | Current Lean form        | Max-general form          | Weaker exists? | Reason |
|---|------------------------|--------------------------|---------------------------|----------------|--------|
| 1 | `[CommRing R]` (on `W`'s codomain, file-level `variable`) | commutative ring | commutative ring | NO | the proof is `ring`; commutativity is genuinely required (the three pairings multiply `addMulSub` terms in both orders). Cannot drop to non-comm. |
| 2 | `W : ℤ → R`             | arbitrary integer-indexed sequence | arbitrary | NO | no structure assumed on `W`; fully general already |
| 3 | indices `c d m n r : ℤ` | integers                 | integers                  | NO | `addMulSub` uses `Int.tdiv 2`; the identity is over ℤ-indices by construction |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for what it states). K = 0 weakening opportunities.
It holds over an arbitrary commutative ring with an arbitrary integer-indexed sequence; nothing
to weaken. (The identity is "small" not because it is over-specialised but because it is a
narrow bookkeeping step.)

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Note |
|---|----------|----------|------|
| 1 | typeclasses instead of bundled hypotheses? | no | already a bare `variable [CommRing R]`; no bundled hyps |
| 2 | filters/topology instead of sequences/metric? | no | finite algebraic identity; no limits |
| 3 | universal-property class instead of construction? | no | it's an equation, not a construction |
| 4 | bundled substructure instead of set+predicate? | no | no substructure |
| 5 | weaken vector-space/field to module/ring? | no | already at comm-ring; ring is essential (Phase 4 row 1) |
| 6 | 1-categorical → higher-categorical? | no | not categorical |
| 7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid? | no | the index ring is intrinsically ℤ (the `.tdiv 2` halving and the additive ℤ-structure are load-bearing for `addMulSub`) |

Modern idiom available: **no**. One-line reason: this is a finite commutative-ring identity
whose form is fully determined by the (already-general) `rel₄`/`rel₆` definitions; there is no
contemporary reformulation that improves organisation.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`.** (No definitional equalities or typeclass-search paths introduced.)

---

### Mathlib search-status: `EllSequence.rel₆_eq₃'` (Phase 5)

| Method | Queries | Result |
|--------|---------|--------|
| [A] Lean-Finder | — | n/a: index tool not available in this environment |
| [B] Loogle | — | n/a: not available; substituted by exhaustive grep over the pinned mathlib source (authoritative) |
| [C] LeanSearch | — | n/a: not available |
| [D] **Grep mathlib src** | `rel₆`, `rel₄`, `addMulSub`, `namespace EllSequence`, `net`, `invarNum` over **all of** `.lake/packages/mathlib/Mathlib/` | **ZERO hits.** None of these identifiers exist anywhere in the pinned mathlib. |
| [E] Name pattern | `EllipticDivisibilitySequence.lean` content listing | mathlib's file (547 lines) is the **old** API: `IsEllSequence`, `preNormEDS`, `normEDS`, `complEDS` — **no** `rel₄`/`rel₆`/`addMulSub`/`net`/`Rel₄OfValid`/`EllSequence` namespace |

Searched for both the current form and the underlying net relation. Cross-checked the mathlib
DivisionPolynomial files (`Basic.lean`, `Degree.lean`) and the public mathlib4_docs page
(WebSearch #1/#2 both surfaced it) — all show the pre-`rel₄` API.

Concluded: **not in mathlib** (the entire `rel₄`/`rel₆` apparatus — definitions and all three
re-expansion identities — is absent from the pinned mathlib; this is new, not-yet-upstreamed
code). The local pin is a same-day mathlib (`d90090f`), so this reflects current mathlib HEAD.

**Provenance note:** the file header credits David Kurniadi Angdinata — the author of mathlib's
existing EDS and `DivisionPolynomial` files. The `net`/`rel₄`/`rel₆` block is plainly *staged*
for upstreaming (mathlib-style docstrings, copyright header, `## Main statements`), and three
near-identical copies exist in the repo (NagellLutz current + `…Original` + HasseWeil/Auxiliary),
i.e. a vendored mathlib-track that has not yet landed upstream.

---

### Call sites — `EllSequence.rel₆_eq₃'` (Phase 6.0)

Internal use count (NagellLutz, excluding the declaring line + comments): **1**
External-to-file callers: 0 (within NagellLutz). Also used in HasseWeil's vendored copy.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `EllipticDivisibilitySequence.lean:431` | `on_goal 2 => rw [rel₆_eq₃']` — inside `rel₄_fix₁_of_fix₂`, the second goal of the `Rel₄OfValid` induction; the sibling `rel₆_eq₃` rewrites goal 1 on line 430 |

Inline-derivation grep: none — it is genuinely used via `rw`, not re-derived inline. It is one of
a coordinated triple (`rel₆_eq₃` / `rel₆_eq₃'` / `rel₆_eq₁₀`) that the `Rel₄OfValid` proof rewrites with.

Signal: K = 1 internal use. A single call site is, per the Phase-6 table, a "could be inlined"
signal — but here inlining is awkward because the proof uses it as a *rewrite rule* in a
goal-directed induction (lines 429–432), and it is paired with its sibling/ten-term cousin. It is
deliberate proof structure, not an over-abstraction.

### Composition check (Phase 6)

Can `rel₆_eq₃'` be derived from mathlib in ≤3 chained calls? **No mathlib call is involved at all.**
The statement is about `rel₆`/`rel₄`/`addMulSub`, none of which exist in mathlib (Phase 5). There
are no mathlib building blocks to compose: the lemma *is* `simp_rw [rel₆, rel₄]; ring` over
project-local definitions. So it is not "composable from mathlib primitives" — it is a one-`ring`
proof over **project-local** primitives that mathlib does not (yet) have.

Conclusion: **NOT-COMPOSABLE from mathlib** (mathlib lacks the very definitions the statement
mentions). This is *not* the NO-composable bucket — that bucket requires mathlib to already have
the building blocks. Here mathlib has nothing; the whole apparatus is the candidate.

---

## Verdict: `EllSequence.rel₆_eq₃'`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): no standalone literature analog; it is an internal algebraic
  step in formalising the Ward/Stange net relation. The underlying mathematics is standard and
  already maximally general.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; no modern-idiom improvement (Phase 4c: no).
- Mathlib search (Phase 5): **not in mathlib** — the entire `rel₄`/`rel₆`/`addMulSub`/`net`
  apparatus is absent; mathlib's EDS file is the older pre-`rel₄` API. Author is the mathlib EDS
  author, so this is staged-but-not-landed code.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (mathlib lacks the definitions); a
  one-`ring` proof over project-local primitives. K = 1 internal call site (the `Rel₄OfValid`
  induction), paired with siblings `rel₆_eq₃`/`rel₆_eq₁₀`.

**Rationale:**

On the pure merits this lemma is "true, general, and absent from mathlib", which superficially
points at a YES. But two facts move it to BORDERLINE. First, `rel₆_eq₃'` is not a result anyone
would PR on its own: it is a `ring`-provable bookkeeping identity (`simp_rw [rel₆, rel₄]; ring`)
that exists only to rewrite one goal inside the `Rel₄OfValid` strong induction, in lockstep with
its sibling `rel₆_eq₃` and the ten-term `rel₆_eq₁₀`. Its mathlibability is **entirely inherited**
from the parent decision: *should the whole `rel₄`/`rel₆`/`net`/`Rel₄OfValid` block go to
mathlib?* If yes, this lemma rides along (it is a private-grade helper, possibly even
`private`/`local` in the eventual PR); if the block is reorganised, this exact identity may
dissolve into a different lemma. Assessing it in isolation is the wrong grain.

Second, this is **vendored mathlib-track code by the mathlib EDS author**, present in three
near-identical copies across the repo. The realistic outcome is not "AINTLIB PRs `rel₆_eq₃'`" but
"Angdinata lands the whole `rel₄`/`rel₆` development upstream, after which all three local copies
are deleted in a mathlib bump." The human judgment needed is the policy call on that block as a
whole — not on this single identity. Hence BORDERLINE, with the questions aimed at the block.

**Numbered questions (≤5):**

1. Is the `rel₄`/`rel₆`/`net`/`Rel₄OfValid` apparatus (NagellLutz `EllipticDivisibilitySequence.lean`
   lines ~92–507) **already an open or planned mathlib PR** by David Angdinata? If so, this lemma
   is part of it and AINTLIB should take no independent upstreaming action.
2. If it is to be upstreamed via AINTLIB instead, should the whole block be the unit of work
   (one `/mathlibable` run on the *block*, then one PR), rather than per-lemma assessments of
   internal helpers like this one?
3. In any upstreaming, should `rel₆_eq₃'` (and `rel₆_eq₃`, `rel₆_eq₁₀`) be `private`/`local`
   helpers scoped to the `Rel₄OfValid` proof, rather than public API?
4. There are three copies of this lemma in the repo (NagellLutz current,
   `EllipticDivisibilitySequenceOriginal.lean`, HasseWeil `Auxiliary/`). Is de-duplicating these
   into a shared `Common/` module (an AINTLIB-internal cleanup) the more urgent action than
   mathlib upstreaming?

**Next action:** confirm whether the `rel₄`/`rel₆` EDS-relations block is already on a mathlib
upstreaming track (question 1). If yes → no independent action; this lemma lands with it. If no →
re-run `/mathlibable` (or `/overview` then `/develop`) on the **whole block** as one unit, not on
this internal helper. Independently, consider an AINTLIB cleanup ticket to de-duplicate the three
in-repo copies into `Common/`.
