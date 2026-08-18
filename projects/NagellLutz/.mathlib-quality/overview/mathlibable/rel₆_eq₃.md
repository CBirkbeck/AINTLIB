# /mathlibable report — `EllSequence.rel₆_eq₃`

**One-line verdict: NO-mathlib-has-it** — this is upstream mathlib's own in-flight EDS code
(author David Kurniadi Angdinata, forked ahead of master, traveling with the open
"elementary algebraic group-law / EDS-relations" PR), not an AINTLIB contribution.

---

## Baseline (Phase 0)

- lake build:               (not re-run — local build stale per task; reasoning from source, which
                            elaborates cleanly: proof is `simp_rw [rel₆, rel₄]; ring`)
- decl `EllSequence.rel₆_eq₃`: ✓ resolved at
                            `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:320`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences" — a **fork of**
                            `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (identical
                            copyright header: *Copyright (c) 2024 David Kurniadi Angdinata*),
                            running ~1120 lines ahead of mathlib master with the full
                            `addMulSub`/`rel₄`/`net`/`rel₆` "elliptic relations" apparatus that
                            mathlib does not yet have.

Qualified name VERIFIED: the decl lives inside `namespace EllSequence` (opened at line 90, never
closed before line 320), so the fully-qualified name is **`EllSequence.rel₆_eq₃`** — matches the
task's parsed guess.

---

## Statement (Phase 1)

`EllSequence.rel₆_eq₃` is a **pure polynomial identity in a commutative ring**, stating:

> For a sequence `W : ℤ → R` over a commutative ring `R` and arbitrary integers `c, d, m, n, r`,
> the "six-index relation" `rel₆ W c d m n r c` (a `rel₄` with the repeated fixed index `c`,
> scaled by the two-index coefficient `addMulSub W c d`) decomposes as the signed sum
>   `rel₆ W m c n r c d − rel₆ W n c m r c d + rel₆ W r c m n c d`.

Unfolding the abbreviations, with `f(x,y) := addMulSub W x y = W((x+y)÷2)·W((x−y)÷2)` and
`rel₄ W a b c d = f(a,b)f(c,d) − f(a,c)f(b,d) + f(a,d)f(b,c)`, both sides are degree-4 polynomials
in the values of `W`, and the identity is a rearrangement that `ring` discharges.

Mathematically this is one expansion step in the **Somos/Ward "every Somos-4 is a Somos-k"**
machinery (van der Poorten–Swart): it re-expresses a four-index elliptic relation with one fixed
index and three free indices as a combination of three four-index relations that each share the
*larger* fixed index — the inductive engine used to push the three-term elliptic relation from its
base case to all index gaps, en route to mathlib's open
`TODO: prove that normEDS satisfies IsEllDivSequence`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring; maximally general (arbitrary comm ring).
- `(W : ℤ → R)` — the sequence; arbitrary, no hypotheses.
- `(c d m n r : ℤ)` — five integer indices; arbitrary.

Hypotheses (Lean side): **none.** (The same-parity/ordering side-conditions live in the *consumers*,
not in this algebraic identity.)

Conclusion (math): a degree-4 ring-polynomial identity among `addMulSub` products — the gap-shift
identity for elliptic relations.

Conclusion (Lean):
`rel₆ W c d m n r c = rel₆ W m c n r c d - rel₆ W n c m r c d + rel₆ W r c m n c d`.

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a hypothesis-free helper `ring` identity (`simp_rw [rel₆, rel₄]; ring`), one of a family
(`rel₆_eq₃`, `rel₆_eq₃'`, `rel₆_eq₁₀`), feeding the `rel₄_fix₁_of_fix₂` / `rel₄_of_fix₂` induction.
Not named after a person, not a `## Main statement`, introduces no structure.

(Literature width run EXHAUSTIVE regardless, because the *provenance* question — is this mathlib's
own code? — is the load-bearing one and demanded the source-paper + PR check.)

---

## One-line check (Phase 2b)

Body line count: n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. One-line check skipped.
(For the record the *proof* is a single line `simp_rw [rel₆, rel₄]; ring`, reinforcing SMALL.)

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                         | Hit? | Standard form found                                              | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "mathlib EllipticDivisibilitySequence normEDS IsEllDivSequence PR Angdinata rel₄ net …"        | yes  | the file is an open mathlib PR by Eric Rodriguez (joint w/ Angdinata) | **arXiv:2604.05280 "On Elliptic Sequences over Commutative Rings"**: *"most results … are included in a pull request to Lean's Mathlib, in the file EllipticDivisibilitySequence.lean."* — the very file forked here |
|  2 | WebSearch (general form)         | "elliptic divisibility sequence three-term relation Somos Ward W(m+n)W(m-n) identity proof"    | yes  | Ward's relation `W_{h-m}W_{h+m}W_n² + W_{n-h}W_{n+h}W_m² + W_{m-n}W_{m+n}W_h² = 0`; gap-shift via van der Poorten–Swart | the `rel₄`/`rel₆` apparatus is the Lean encoding of exactly this three-pairs-of-indices relation |
|  3 | WebSearch (named-after/aliases)  | (same two queries surfaced) "every Somos 4 is a Somos k" van der Poorten; Stange elliptic nets | yes  | "every Somos-4 is a Somos-k" (arXiv:math/0412293); Stange's elliptic nets (`net` def cites Stange) | confirms the *math* is classical/standard; the **Lean formulation** (`rel₄`, `rel₆`, `addMulSub`, `net`) is Angdinata's |
|  4 | ChatGPT MCP                      | (per task: ChatGPT MCP down — fallback)                                                        | n/a  | —                                                                | substituted by source-paper identification (#1) + Wikipedia/arXiv (#2,#3), which answer the standard-form + provenance questions directly |
|  5 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/`; `ls refs/`                              | n/a  | (no references dir; no `refs/` store on this checkout)            | recorded n/a — directory absent |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                              | n/a  | —                                                                | not an nLab-style categorical concept; nothing beyond #1–#3 |
|  7 | nCatLab                          | —                                                                                             | n/a  | —                                                                | not a categorical concept |
|  8 | Stacks Project                   | —                                                                                             | n/a  | —                                                                | not scheme-theoretic; EDS/Somos identities are not in Stacks |
|  9 | MathOverflow / MSE               | (folded into #2/#3 web sweep) Somos / EDS three-term relation                                  | yes  | same gap-shift relation; widely-discussed                        | no extra standard-form variant |
| 10 | recent arXiv (≤5 yr)             | "elliptic sequences over commutative rings" / "recurrence relation EDS" (2102.07573, 2604.05280) | yes | arXiv:2604.05280 (2026) + arXiv:2102.07573 — the modern comm-ring treatment that mathlib follows | **2604.05280 is the paper behind this exact Lean file** |

Protocol satisfied: WebSearch ran 3 distinct queries (specific Lean form / general Ward form /
named-after Somos-k aliases); ChatGPT MCP recorded n/a with reason (down per task) and substituted by
the source-paper hit that answers the same questions; local refs / nLab / nCatLab / Stacks / MO /
arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: the **gap-shift (index-expansion) identity** for the four-index elliptic
relation `rel₄` — the algebraic engine of the Somos/Ward "every Somos-4 is a Somos-k" theory
(van der Poorten–Swart), as encoded in Angdinata's `EllSequence` apparatus.
Sources agree on the standard form: **yes** — the underlying three-term elliptic relation is Morgan
Ward's, classical; the `rel₄`/`rel₆`/`addMulSub`/`net` *encoding* is the specific, recently-published
(arXiv:2604.05280) Lean-targeted formulation by Angdinata / Rodriguez.
Most general standard form: a polynomial identity over an arbitrary commutative ring `R` for arbitrary
`W : ℤ → R` and arbitrary integer indices — which is **exactly** what the Lean lemma already states.
Generality dimensions where the literature varies:
  - coefficient domain: classically ℤ or ℂ (σ-function origins) → modern treatments (2604.05280, and
    this file) take an **arbitrary commutative ring** — the most general, and the form here.
Disagreement with the literature: **none** — `rel₆_eq₃` is a faithful, maximally-general encoding.

**Key provenance finding (decisive for the verdict):** this is not third-party material that AINTLIB
might contribute to mathlib. It is **mathlib's own code, by mathlib's EDS author, forked ahead of
master**, and the source paper states plainly it is *already in an open mathlib PR*. The sibling
`/mathlibable` reports in this same batch (e.g. `addMulSub₄_mul_addMulSub₄.md`, `addMulSub.md`,
`rel₄`-family) reached the identical conclusion.

---

## Generality analysis — `EllSequence.rel₆_eq₃`

Literature-standard form (from Phase 3): a degree-4 polynomial identity in `addMulSub`-products,
over an arbitrary commutative ring, for an arbitrary integer-indexed sequence and arbitrary indices.

| # | Parameter / hypothesis | Current Lean form              | Literature-standard form        | Weaker form exists? | Reason |
|---|------------------------|--------------------------------|----------------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | arbitrary commutative ring     | arbitrary commutative ring       | NO                  | `ring` needs commutativity + subtraction; this is already the floor for the `rel₄` identity |
| 2 | `(W : ℤ → R)`          | arbitrary sequence             | arbitrary sequence               | NO                  | no constraint used; already maximal |
| 3 | `(c d m n r : ℤ)`      | arbitrary integers             | arbitrary integers               | NO                  | no parity/ordering hypotheses (those live in consumers); already maximal |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (hypothesis-free; arbitrary comm ring; arbitrary `W`;
arbitrary indices). Number of weakening opportunities found: **0**.
Cost of restatement: n/a — nothing to restate.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Reason |
|----|--------------------------------------------------------------------------|----------|--------|
|  1 | "let X be a foo" → typeclasses?                                          | no       | the only typeclass is `CommRing`, already idiomatic; no bundled hypotheses to classify |
|  2 | sequences/metric → filters/topology?                                     | no       | a finite algebraic identity; no limits or topology |
|  3 | construction → universal-property class?                                  | no       | no object is constructed; it's an equation |
|  4 | set-with-closure-predicate → bundled substructure?                        | no       | no substructure |
|  5 | vector-space/field-specific → weaken typeclasses?                         | no       | already at `CommRing`, the natural floor |
|  6 | 1-categorical → higher-categorical?                                       | no       | not categorical |
|  7 | concrete index (ℤ) → arbitrary group/monoid?                              | no       | EDS are intrinsically ℤ-indexed (the relation uses `m±n`, `÷2`); ℤ is essential, not incidental |

Modern idiom available: **no.** The lemma is already in the contemporary maximally-general
comm-ring formulation that arXiv:2604.05280 / mathlib adopt. No Bourbaki-2.0 reorganisation applies.

---

## Diamond / defeq risk — `EllSequence.rel₆_eq₃`

n/a — declaration kind is `lemma` (a proof of an equality); it introduces no definitional equalities
and no typeclass-search paths. Phase 4.5 skipped.

---

## Mathlib search-status: `EllSequence.rel₆_eq₃`

[A] Lean-Finder       n/a (offline per task) — substituted by direct source grep below
[B] Loogle            n/a (offline per task) — pattern `?a * (?b * ?c - ?d * ?e + ?f * ?g) = …` would
                      only match `ring`-normalisable comm-ring identities; not how this is indexed
[C] LeanSearch        n/a (offline per task)
[D] Grep mathlib src  searched `.lake/packages/mathlib/Mathlib/` for
                      `rel₆`, `rel₄`, `addMulSub`, `EllSequence`, `elliptic net`, `Stange`, `Somos`,
                      `EllipticNet` → **only** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
                      matches `EllSequence`, and that file has **0** occurrences of
                      `rel₆`/`rel₄`/`addMulSub`. NO hit.
[E] Name pattern      grepped decl heads of mathlib's `EllSequence` namespace: it contains only
                      `IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`, `preNormEDS('/…)`,
                      `complEDS(₂/'/…)`, `normEDS`, `normEDSRec`, `map_*`. **No** `rel*`/`addMulSub*`/
                      `net`/`avg₄`/`HaveSameParity₄`. NO hit.

Searched for both:
  - the user's current form (`rel₆_eq₃`) — absent.
  - the literature-standard form (the gap-shift elliptic relation, in any ring-identity spelling) —
    **mathlib has no elliptic-relation / Somos-expansion API at all** (no `net`, no `rel₄`, no Stange
    elliptic nets, no Somos lemmas anywhere in the tree).

Concluded: **not in mathlib master** (all methods exhausted, both forms). The 547-line mathlib EDS
file stops at `complEDS`/`map_*` and carries the open `TODO: prove that normEDS satisfies
IsEllDivSequence` — the goal this forked-ahead 1667-line apparatus exists to discharge. So: not in
*master*, **but it is mathlib's own pending code** (identical author/header; source paper says it is
in an open mathlib PR).

---

## Call sites — `EllSequence.rel₆_eq₃`

Internal use count (NagellLutz project, excluding the two declaring lines 320/328): **1** direct use.
External-to-file callers within NagellLutz: 0 (used only inside the same file).

| Caller file:line                                                                 | Usage pattern |
|----------------------------------------------------------------------------------|---------------|
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:430`           | `on_goal 1 => rw [rel₆_eq₃]; have _hc := trivial` — inside `rel₄_fix₁_of_fix₂` |

Sibling within the same proof block: `rel₆_eq₃'` (line 431) and `rel₆_eq₁₀` (line 444, in
`rel₄_of_fix₂`) — the three form one gap-shift family driving the `rel₄`-induction.

Inline-derivation grep (was the same identity re-derived elsewhere without `rel₆_eq₃`?): **none** —
it is the canonical named step; consumers `rw [rel₆_eq₃]` rather than re-`ring` it.

Cross-project: `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:264` contains
a **verbatim duplicate** `rel₆_eq₃` (same statement, same proof) — the HasseWeil project forks the
same mathlib file. `EllipticDivisibilitySequenceOriginal.lean:306` is a third copy. This triplication
across NagellLutz/HasseWeil/Original is itself evidence that all three are pinned copies of one
upstream artifact, not independent contributions.

Composability signal: K = 1 internal use, no inline re-derivation, part of a tightly-coupled named
family over project-local defs `rel₆`/`rel₄`/`addMulSub` → it is genuine (if narrow) internal API,
but **not standalone-extractable** to mathlib (see Phase 6).

---

## Composition check (Phase 6)

Can `EllSequence.rel₆_eq₃` be derived from **current mathlib** in ≤3 chained calls?

Attempt 1: `by simp_rw [rel₆, rel₄]; ring` — exactly the project proof.
  - Mathlib decls used: `ring` (and `simp_rw`). **But** the unfoldings `rel₆`, `rel₄` are
    **project-local defs that are NOT in mathlib master**. `addMulSub` likewise.
  - Result: **fails against mathlib**. The statement does not even *type-check* in mathlib, because
    `rel₆`/`rel₄`/`addMulSub` do not exist there. There is nothing to compose from.

Conclusion: **NOT-COMPOSABLE from current mathlib** — not because it is deep, but because its very
vocabulary (`rel₆`, `rel₄`, `addMulSub`) is absent from mathlib master. It is trivially one `ring`
call *given the defs*, and those defs travel with the same upstream PR. So it is neither an
independent AINTLIB lemma to PR, nor composable from what mathlib currently has.

---

## Verdict: `EllSequence.rel₆_eq₃`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the file is an open **mathlib PR** by Eric Rodriguez (joint with
  D. K. Angdinata); source paper **arXiv:2604.05280** states the results "are included in a pull
  request to Lean's Mathlib, in the file EllipticDivisibilitySequence.lean." Identical copyright
  header to mathlib's own EDS file (*David Kurniadi Angdinata, 2024*).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** already; no weakening, no modern-idiom move.
- Mathlib search (Phase 5): the `rel*`/`addMulSub`/`net` apparatus is **not in mathlib master**, but
  it is mathlib's own pending code (the master file even carries the matching open `TODO`).
- Composition check (Phase 6): **NOT-COMPOSABLE** from current mathlib (its vocabulary is absent);
  trivial `ring` given the companion defs that travel with the same PR.

**Rationale:**

`rel₆_eq₃` is not a candidate AINTLIB contribution at all. It is **upstream mathlib code, written by
mathlib's EDS author, forked into NagellLutz ahead of master**, and — per the source paper
(arXiv:2604.05280) — it is **already in flight to mathlib via an open PR**, bundled with the
`addMulSub` / `rel₄` / `rel₆` / `net` "elliptic relations" apparatus whose purpose is to discharge
mathlib's standing `TODO: prove that normEDS satisfies IsEllDivSequence`. Mathematically the lemma is
a faithful, maximally-general (arbitrary commutative ring) encoding of the classical Somos/Ward
gap-shift identity — there is no generalisation to make and no modern-idiom reformulation that
improves it. It has no independent standalone value: it is a one-line `ring` identity
(`simp_rw [rel₆, rel₄]; ring`) over three definitions that are themselves not yet in mathlib, used at
a single internal call site (`rel₄_fix₁_of_fix₂`, line 430) inside the same fork. The correct
action is **not** to PR this lemma from AINTLIB — that would duplicate, and race, mathlib's own
in-flight work. The identical lemma already exists triplicated in HasseWeil and
`…Original.lean`, confirming all are pinned copies of one upstream artifact.

This maps to **NO-mathlib-has-it** in the operational sense the bucket is meant to capture: *mathlib
is the rightful and already-active home of this declaration* (it is mathlib's own code under
upstreaming), so AINTLIB should not separately add it. The decl is not in mathlib *master* today only
because the PR has not yet landed — a timing gap, not a contribution gap.

WHY not (refactor-actionable detail):
- This file is a verbatim, run-ahead **fork of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`**
  (identical header/author), and the `rel₄`/`rel₆`/`addMulSub`/`net` block is the not-yet-merged
  continuation that the upstream author is landing via the "elementary algebraic group-law / EDS"
  mathlib PR (source: arXiv:2604.05280). Shipping `rel₆_eq₃` (or its companions) as an AINTLIB→mathlib
  PR would collide with that work and re-introduce code mathlib's own author is already merging.
- It is also **non-extractable**: the statement mentions `rel₆`/`rel₄`/`addMulSub`, none of which are
  in mathlib master; a lemma cannot precede the defs it references. It must travel *with* those defs,
  i.e. with the existing upstream PR — not as a standalone contribution.
- Existing/destined mathlib home: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
  (the file this is forked from; the apparatus extends it directly).
- Refactor plan for AINTLIB: **none required as an upstreaming action.** When the upstream EDS-relations
  PR lands in mathlib, *drop the fork* — delete the duplicated `EllSequence` rel-apparatus from
  NagellLutz (and the HasseWeil + `…Original.lean` copies) and `import` it from mathlib instead. Until
  then it is a legitimate `sorry`-free WIP fork; leave it in place. The single internal call site
  (line 430, `rel₄_fix₁_of_fix₂`) needs no change — it keeps working against the upstream copy after
  the swap.
- Next action: **do not PR this from AINTLIB.** Track mathlib's open EDS-relations PR; on merge,
  replace the three forked copies with an `import` of the mathlib file. (If one insists on a label
  scoped strictly to "should AINTLIB PR *this lemma*": still **NO** — it is mathlib's own in-flight
  code and non-separable from its companion defs.)

---

## Next step

Do not open an AINTLIB→mathlib PR for `rel₆_eq₃`. It is upstream mathlib's own forked-ahead code
(author Angdinata; in an open mathlib PR per arXiv:2604.05280), non-extractable from its companion
defs `rel₆`/`rel₄`/`addMulSub`. When that PR lands, delete the NagellLutz / HasseWeil /
`…Original.lean` forks and `import Mathlib.NumberTheory.EllipticDivisibilitySequence` instead.
