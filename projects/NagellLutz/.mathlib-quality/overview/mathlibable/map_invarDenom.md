# /mathlibable report — `map_invarDenom`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz theorem; elliptic
> divisibility sequences). Run 2026-06-21. Local Lean build stale; assessment
> reasons from source + pinned mathlib source + official mathlib4 docs + WebSearch.
> ChatGPT MCP was down (Codex error); the lit/idiom channel used WebSearch fallback.
>
> NOTE: this supersedes an earlier (18 Jun) draft that recorded the qualified name as
> `EllSequence.map_invarDenom` and verdict `NO-composable-from-mathlib`. The qualified
> name was **wrong** (see Phase 0 — the lemma is at the root namespace), and the
> earlier draft did not weigh the cross-project byte-identical duplicate or the
> parent-API-upstreaming question, which is what makes the honest verdict BORDERLINE.

## Baseline (Phase 0)

- lake build:               ⚠ not run (stale per task note); reasoned from source
- decl `map_invarDenom`:     ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1174`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and constructs normalised EDS from initial terms; this file is an **extended fork** of `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

### Qualified-name verification (REQUIRED — corrects the prior draft)

The task's "parsed qualified name" was `map_invarDenom` — **VERIFIED as the root-level
name** by tracking `namespace EllSequence` depth across the whole file:

```
 90: OPEN  EllSequence  (depth → 1)
597: CLOSE EllSequence  (depth → 0)
1079: OPEN EllSequence  (depth → 1)        ← Complement section reopen
1112: CLOSE EllSequence (depth → 0)
 >>> line 1174 (map_invarDenom): EllSequence-depth = 0     ← ROOT namespace
1356: OPEN EllSequence  (depth → 1)
1431: CLOSE EllSequence (depth → 0)
```

- `map_invarDenom` sits in `section Map` (opens line 1116, `end Map` line 1201). That
  section is **not** inside any namespace — the `EllSequence` namespace closed at 597,
  reopened 1079–1112, and closed again *before* `section Map`.
- Line 599 `open EllSequence` (no `in`) persists to EOF — that is why the body names
  `invarDenom` unqualified even though the lemma is at root.
- **Fully-qualified lemma name: `map_invarDenom` (root namespace).**
- Its *subject*, the def, IS namespaced: `EllSequence.invarDenom` (def at line 145,
  inside the 90–597 block). The prior draft conflated the def's namespace with the
  lemma's.

## Statement (Phase 1)

`map_invarDenom` says a ring homomorphism commutes with `invarDenom`, pushed through
the underlying sequence by composition.

`EllSequence.invarDenom W s n := W (n + s) * W n * W (n - s)` is the **denominator of
an invariant of an elliptic sequence**: per the file docstring, for each `s` the ratio
`invarNum W s n / invarDenom W s n` is a constant independent of `n` — the (shifted)
denominator of Shipsey/Stange's conserved quantity `I_n` for elliptic sequences.

The lemma: for `f` a ring hom `R → S` and `W : ℤ → R`,
`f (invarDenom W s m) = invarDenom (f ∘ W) s m`.

Variables / typeclasses (Lean side):
- `R S : Type*`, `[CommRing R] [CommRing S]` — source/target rings.
- `W : ℤ → R` — the sequence.
- `f : F`, `[FunLike F R S] [RingHomClass F R S]` (file `variable`, lines 85–86) — a
  **bundled-ring-hom-class** morphism. (More general than mathlib's own EDS `map_*`
  lemmas, which use `f : R →+* S`.)
- `s m : ℤ` — shift and index.

Hypotheses: none beyond the typeclass context.

Conclusion (math): the EDS-invariant denominator is natural in the ring — it commutes
with ring homomorphisms applied termwise to `W`.

Conclusion (Lean): `f (invarDenom W s m) = invarDenom (f ∘ W) s m`.

Proof (one substantive line): `simp_rw [invarDenom, map_mul, Function.comp]` — unfold
the def, push `f` through the two multiplications via `map_mul`, fold the composition.
Pure functoriality glue.

## Size classification (Phase 2a)

Verdict: **SMALL** — one-line helper functoriality lemma about a def; not a named
theorem, not a `## Main results` entry, not a new structure. (Lit width exhaustive
regardless.)

## One-line check (Phase 2b)

Body line count: 1 substantive line (`simp_rw [...]`).
One-liner verdict: **n/a — kind is `lemma`, not `def`.** (2b's def-exemption table
applies to `def`/`abbrev`/`structure`.) Triviality signal recorded for Phase 6/7: the
proof is a 3-lemma `simp_rw` (`invarDenom` unfold + `map_mul` + `Function.comp`) — the
canonical "ring hom through a product" glue shape.

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                       | Query                                                                      | Hit?    | Standard form found                                  | Notes |
|----|-------------------------------|----------------------------------------------------------------------------|---------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)     | EDS invariant numerator/denominator `W(n+s)W(n)W(n-s)` Ward/Stange          | partial | recurrence + invariant context, not this exact denom | confirms EDS framework; Ward 1948, Stange nets |
|  2 | WebSearch (general/invariant) | EDS invariant ratio independent of n, conserved quantity, Shipsey/Stange    | yes     | `I_n` = sum of three ratios, **independent of n**     | matches the file's `invarNum/invarDenom` docstring exactly |
|  3 | WebSearch (mathlib presence)  | `Mathlib.NumberTheory.EllipticDivisibilitySequence` declaration list        | yes     | mathlib has `normEDS` API + `map_*` up to `map_complEDS` | mathlib does NOT have `invar*`/`net`/`rel₄` |
|  4 | ChatGPT MCP                   | idiom/generality of `f(invarDenom W)=invarDenom (f∘W)`; named-vs-glue line   | **n/a** | — (Codex/MCP errored; warned-down in task)           | fell back to WebSearch + direct mathlib source reading |
|  5 | Local references              | grep `projects/NagellLutz/.mathlib-quality/references/`                      | n/a     | (no references dir)                                  | dir absent — recorded n/a |
|  6 | nLab                          | "elliptic divisibility sequence" / functoriality of a product               | n/a     | no nLab EDS page; map-fact is generic ring-hom functoriality | not a categorical concept |
|  7 | nCatLab                       | —                                                                          | n/a     | —                                                    | not categorical |
|  8 | Stacks Project                | —                                                                          | n/a     | —                                                    | not a scheme/AG concept |
|  9 | MathOverflow / Math.SE        | elliptic sequence invariant constant ratio                                  | partial | same `I_n` invariant                                 | folds into #2 |
| 10 | recent arXiv (≤5y)            | Stange "Division polynomials for arbitrary isogenies" (2025), elliptic nets  | yes     | EDS/net relation machinery actively used             | parent relation API is live research; the map-lemma is not a named result |

### Literature summary (Phase 3)

Concept identified as: the **denominator of the elliptic-sequence invariant**
(Shipsey/Stange `I_n`), shifted by `s`. The *lemma* itself — "a ring hom commutes with
`invarDenom` of `f ∘ W`" — is **not a named object in the literature**; it is generic
ring-homomorphism functoriality of a product.
Sources agree on the standard form: yes, for the underlying invariant (the parent
def). The map-lemma has no literature "standard form"; its correctness is `map_mul`
twice.
Most general standard form (of the map fact): a ring (even monoid) hom commutes with
any finite product of values of a function — `map_mul`/`map_prod`.
Generality dimensions where the literature varies: none meaningful for the map-fact;
the parent invariant is over an arbitrary commutative ring `R`, which the def takes.
Disagreement with the literature: none.

## Generality analysis (Phase 4)

Literature/idiom target of the map fact: generic functoriality `f (a*b*c) = f a*f b*f c`
for any `MulHomClass`, instantiated at `a,b,c = W(n+s), W n, W(n-s)`.

| # | Parameter / hypothesis           | Current Lean form                     | Idiom target                        | Weaker exists? | Reason |
|---|----------------------------------|---------------------------------------|-------------------------------------|----------------|--------|
| 1 | `f` morphism class               | `[FunLike F R S][RingHomClass F R S]` | `MulHomClass F R S` suffices        | yes (in principle) | proof uses only `map_mul`; `RingHomClass` stronger than needed |
| 2 | `[CommRing R]`, `[CommRing S]`   | comm rings                            | `Mul` only                          | yes (in principle) | only multiplication touched; commutativity unused |
| 3 | `W : ℤ → R`                       | sequence indexed by `ℤ`               | same                                | no             | `invarDenom`'s signature fixes this |

### Generality verdict (Phase 4b)

The current form is **EFFECTIVELY MAXIMALLY GENERAL within the `invarDenom` API** — it
is already stated over `RingHomClass F`, *more* general than mathlib's sibling
`map_normEDS`/`map_complEDS` (which use `f : R →+* S`).
Available further weakenings: 2 (`MulHomClass`/`Mul`) — recorded but **counter-idiomatic**:
every sibling `map_*` lemma in both mathlib's EDS file and this file is uniformly a
ring hom; weakening just this one breaks family uniformity for no gain.
Proposed restatement: none. Cost of any restatement: CHEAP but **counter-idiomatic —
do not do it**.

### Modern-idiom check (Phase 4c)

| #  | Question                                                  | Applies? | Note |
|----|-----------------------------------------------------------|----------|------|
|  1 | typeclass-ify a "let X be a foo" preamble?                | no       | already hypothesis-free over `RingHomClass F` |
|  2 | sequences/metric → filters/topology?                      | no       | finite algebraic identity; no limits |
|  3 | construction → universal-property class?                  | no       | it's an equation |
|  4 | set-with-closure-predicate → bundled substructure?        | no       | n/a |
|  5 | field-specific → weaken typeclasses?                      | partial  | `RingHomClass`→`MulHomClass` possible but counter-idiomatic (see 4b) |
|  6 | 1-categorical → higher-categorical?                       | no       | n/a |
|  7 | concrete index ℤ → arbitrary monoid?                      | no       | index structurally ℤ via `invarDenom` |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The idiomatic move is to *match the `map_*` family*,
which it already does (indeed exceeds — it's stated more generally than mathlib's six
EDS `map_*` lemmas). The `MulHomClass` weakening is real but not an organisational
improvement.

## Mathlib search-status (Phase 5)

The mathlib-index MCP tools (loogle/leansearch) were **not exposed** in this
environment, so Phase 5 used the two most authoritative substitutes: (D) direct grep
over the **pinned mathlib source** this repo builds against, cross-checked against the
**official mathlib4 docs website**. Both agree.

```
[A] Lean-Finder       n/a — MCP not exposed
[B] Loogle            n/a — MCP not exposed; substituted by [D] direct source grep
[C] LeanSearch        n/a as MCP; substituted by official mathlib4 docs page fetch — confirms absence
[D] Grep mathlib src  'invarDenom|invarNum|map_invar|net|rel₄|addMulSub' in
                      .lake/packages/mathlib/.../EllipticDivisibilitySequence.lean
                          → NO HITS for any of them. mathlib's map_* family stops at:
                          map_preNormEDS', map_preNormEDS, map_complEDS₂, map_normEDS,
                          map_complEDS', map_complEDS.
[E] Name pattern      'map_invarDenom' repo-wide → only the two FORK copies
                      (NagellLutz, HasseWeil); zero in mathlib.
```

Searched for both forms (user's `map_invarDenom` / `EllSequence.invarDenom`, and the
underlying invariant): **neither is in mathlib**. mathlib has `IsEllSequence` and the
`normEDS` tower, but NOT the `invar*`/`net`/`rel₄` relation API this lemma belongs to.

Concluded: **not in mathlib** (both forms; via pinned mathlib source + official docs).
The parent `invarDenom` def is itself absent, so the map lemma about it cannot be there.

## Composition check + call sites (Phase 6)

### Call sites — `map_invarDenom`

Internal use count (NagellLutz, excluding declaring line): **1**
- `.../EllipticDivisibilitySequence.lean:1496` —
  `simp only [map_mul, map_invarNum, map_invarDenom, map_add, map_pow, aeval_X] at this`
  (in the proof of `invar₂_normEDS`, reducing a normalised EDS to the universal
  `MvPolynomial` EDS via `aeval`).

External: **byte-identical duplicate in another project**:
- `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:146` —
  identical `map_invarDenom` (and `map_invarNum` at 143), in the same
  `map_addMulSub → map_rel₄ → map_net → map_invarNum → map_invarDenom` chain.
  (HasseWeil uses `f : R →+* S`; NagellLutz uses `RingHomClass F` — small generality
  skew between forks.)

| Caller file:line                                              | Usage pattern |
|---------------------------------------------------------------|---------------|
| NagellLutz/.../EllipticDivisibilitySequence.lean:1496         | `simp only [..., map_invarDenom, ...] at this` (rewriting under `aeval`) |
| HasseWeil/.../Auxiliary/EllipticDivisibilitySequence.lean:146 | duplicate *declaration* (same lemma re-stated) |

Inline-derivation grep: the parent/sibling lemmas (`map_invarNum`, `map_net`,
`map_rel₄`, `map_addMulSub`) form a contiguous functoriality block; `map_invarDenom`
is consumed as one entry of a `simp` set, never re-derived inline.

### Composition check

Attempt 1: `by simp only [EllSequence.invarDenom, map_mul, Function.comp]`
  - Mathlib decls used: `map_mul` (twice, through `a*b*c`), `Function.comp`.
  - Result: **succeeds** (it is the project's own proof, modulo `simp` vs `simp_rw`).
  - Caveat: the only non-mathlib symbol is the *project-local* def `invarDenom`.

Conclusion: **COMPOSABLE** as a proof — but the composition's subject `invarDenom` is
**itself not in mathlib**. "Inline at the call site instead of having the lemma" only
makes sense within a world where `invarDenom` exists; there is no pure-mathlib
statement to inline this into. The composition presupposes the project's (or a future
mathlib's) `invarDenom`.

## Verdict: `map_invarDenom`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature (Phase 3): the *parent* invariant is real, literature-grounded
  (Shipsey/Stange `I_n`); the *map-lemma itself* is generic ring-hom functoriality
  with no named-literature form.
- Generality (Phase 4): already at/above the EDS `map_*` family convention (over
  `RingHomClass F`); only weakening (`MulHomClass`) is counter-idiomatic; no
  modernisation.
- Mathlib search (Phase 5): **not in mathlib**, either form — and neither is its
  subject `invarDenom`, nor the surrounding `net`/`rel₄`/`invarNum` API.
- Composition (Phase 6): COMPOSABLE as `simp [invarDenom, map_mul]`, **but** the
  composition presupposes `invarDenom`, which mathlib lacks. K=1 internal use;
  byte-identical duplicate in HasseWeil.

**Rationale:**

The verdict turns on a judgment the skill cannot settle alone, because two readings
genuinely fit and point at different buckets:

*Reading A — glue (→ NO-composable-from-mathlib).* In isolation this is a one-line
`simp_rw [invarDenom, map_mul, Function.comp]`: a ring hom through a triple product.
Mathlib routinely inlines such facts. If `invarDenom` were a throwaway local
abbreviation you would delete `map_invarDenom` and write `simp [invarDenom, map_mul]`
at the single call site (line 1496). This is the earlier draft's verdict.

*Reading B — necessary companion of a coherent API that should be upstreamed
(→ YES-add-as-is).* `map_invarDenom` is **not** standalone. It is the last link of a
uniform `map_addMulSub → map_rel₄ → map_net → map_invarNum → map_invarDenom` chain
that exactly mirrors mathlib's own `map_preNormEDS → … → map_complEDS` family.
Mathlib's EDS file maintains a `map_*` companion for *every* EDS helper it defines —
precisely so proofs can reduce a normalised EDS to the universal `MvPolynomial` EDS
via `aeval`, which is exactly what line 1496 does. The only reason `map_invarDenom`
"isn't in mathlib" is that its whole parent layer — `net`, `rel₄`, `invarNum`,
`invarDenom`, the `IsEllSequence`-relation theory — has not been upstreamed yet. That
this lemma is **duplicated byte-for-byte across two independent projects** (NagellLutz
+ HasseWeil) is a strong signal it is shared infrastructure, not project-local glue.
If/when the `invar*`/`net`/`rel₄` block goes upstream, `map_invarDenom` ships *with
it* as a required `@[simp]`-style companion — you would not upstream the parent API
without its functoriality lemmas.

A `simp`-closable one-liner whose subject is absent from mathlib, with K=1 internal
use, is not self-evidently a YES; but a cross-project-duplicated `map_*` family
companion is not self-evidently a NO either. The deciding question is **policy about
the parent API**, which only a human can answer. Hence BORDERLINE.

**Numbered questions for the user (≤5):**

1. Is the parent EDS-relation API in this file — `EllSequence.invarNum`, `invarDenom`,
   `net`, `rel₄`, `addMulSub`, and the `IsEllSequence` relation lemmas (the part of
   this file that is a **superset** of mathlib's
   `NumberTheory.EllipticDivisibilitySequence`) — intended to be upstreamed to
   mathlib? If **yes**, `map_invarDenom` ships as a companion → effectively
   **YES-add-as-is** (one PR with the parent block).
2. If that block is **not** slated for mathlib, keep `map_invarDenom` as a named lemma,
   or inline its single use (line 1496) as `simp [invarDenom, map_mul]` and delete it
   → **NO-composable-from-mathlib**?
3. The lemma is **duplicated** in
   `projects/HasseWeil/.../Auxiliary/EllipticDivisibilitySequence.lean:146` (identical
   statement, but over `f : R →+* S` vs `RingHomClass F`). Deduplicate into a shared
   `Common/` module first (an AINTLIB cleanup ticket) — settling which generality is
   canonical — before any mathlib decision?
4. If upstreaming: keep the **more general `RingHomClass F`** form (NagellLutz's) — to
   match and slightly exceed mathlib's EDS `map_*` convention — or downgrade to
   `R →+* S` for uniformity with the existing six `map_*` siblings?

**If "yes, upstream the parent API; keep RingHomClass; dedup first":** verdict
collapses to **YES-add-as-is**, target
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, shipped in the same PR as
`invarNum`/`invarDenom`/`net`/`rel₄`/`addMulSub` and their sibling `map_*` lemmas
(`map_addMulSub`, `map_rel₄`, `map_net`, `map_invarNum`). Must **not** be split out
alone.
**If "no upstream; local glue":** verdict collapses to **NO-composable-from-mathlib**
— inline `simp [invarDenom, map_mul]` at line 1496 and delete, after deduplicating
against HasseWeil.

---

## Next step

User answers questions 1–4; the pivotal one is **Q1** (is the parent
`invar*`/`net`/`rel₄` EDS-relation layer headed for mathlib?). Then re-run
`/mathlibable map_invarDenom` — but this lemma should never be assessed or shipped
independently of its `map_*` family and the parent `invarDenom` def. Given the
byte-identical HasseWeil duplicate, an **AINTLIB dedup cleanup ticket** (fold both
copies into a shared module, pick the canonical generality) is the right *immediate*
action regardless of the mathlib decision.
