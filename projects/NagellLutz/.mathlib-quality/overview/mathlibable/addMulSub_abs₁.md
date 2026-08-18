# /mathlibable report — `EllSequence.addMulSub_abs₁`

> Step-9 (overview) mathlibable assessment, NagellLutz project (Nagell–Lutz theorem; elliptic
> divisibility sequences). Run with the local Lean build **stale** (Phase 0 build artifacts empty);
> reasoning is from the source statement, the vendored mathlib source tree
> (`.lake/packages/mathlib`, rev `d90090f`), WebSearch, and grep. ChatGPT MCP (Codex) was **down**
> this session — its channel is recorded `n/a (tool down)` and compensated by extra WebSearch + grep.

---

### Baseline (Phase 0)
- lake build:               ⚠ stale (build/lib empty) — reasoned from source per task instructions
- decl `EllSequence.addMulSub_abs₁`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:195`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences — defines `IsEllSequence`, `preNormEDS`,
  `normEDS`, and (unlike upstream mathlib) **proves** `isEllDivSequence_normEDS`. A forward-port /
  extension of `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

**Namespace verification.** The lemma sits inside `namespace EllSequence` (opened line 90, closed
line 597). Parsed qualified name in the task prompt — `EllSequence.addMulSub_abs₁` — is **CORRECT**.

---

### Statement (Phase 1)

```lean
lemma addMulSub_abs₁ (m n : ℤ) : addMulSub W m |n| = addMulSub W m n := by
  obtain h | h := abs_choice n <;> simp only [h, addMulSub_neg₁]
```

`addMulSub_abs₁` states that the helper expression `addMulSub W m n` is **invariant under taking the
absolute value of its second argument**: `addMulSub W m |n| = addMulSub W m n`.

Here `addMulSub` is a **project-local** definition (line 94 of the same file):
`addMulSub W m n := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)` — the "basic building block of elliptic
relations", representing `W((m+n)/2) · W((m−n)/2)` when `m, n` share parity. `tdiv` (truncated
division) is used precisely so the function is *even* in each argument unconditionally. The lemma is
an immediate corollary of the sibling evenness lemma `addMulSub_neg₁` (line 188:
`addMulSub W m (-n) = addMulSub W m n`).

Variables / typeclasses (Lean side):
- `R : Type*` `[CommRing R]` — the codomain ring (file-level `variable`).
- `W : ℤ → R` — the sequence (file-level `variable`).
- `m n : ℤ` — the two integer indices.

Hypotheses: none.

Conclusion (math): an even-in-its-second-argument expression is unchanged by `|·|` on that argument.
Conclusion (Lean): `addMulSub W m |n| = addMulSub W m n`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: incidental congruence/bookkeeping helper for a Lean-local definition; not a named theorem,
not a `## Main statement`, introduces no structure. It is one of a family
(`addMulSub_neg₀/neg₁/abs₀/abs₁/same/swap/even/odd`) of micro-lemmas that normalise `addMulSub`
arguments so the big `rel₄`/`net` permutation proofs go through.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — one-liner *def* check is **n/a**. (For the record
the proof body is a single tactic line, reinforcing the SMALL classification.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                              | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence Ward addMulSub W((m+n)/2) W((m−n)/2) building block elliptic net Stange" | partial | Ward recurrence; Stange elliptic nets | confirms the *subject* (`addMulSub`) is the parity-building-block of EDS/nets; **no** named "abs-invariance" lemma |
|  2 | WebSearch (general form)         | "mathlib even function f \|x\| = f x abs_choice Function.Even absolute value argument"               | no   | —                   | no canonical mathlib lemma for "even ⟹ f\|x\|=fx"; only generic `Even`/abs docs surfaced |
|  3 | WebSearch (provenance / named-after) | "Angdinata Lean mathlib elliptic divisibility sequence normEDS IsEllDivSequence formalization" | yes  | source = **arXiv 2604.05280** "On Elliptic Sequences over Commutative Rings" | this is the paper behind the `EllSequence` API; mathlib docs confirm upstream still has the `normEDS`-is-EDS **TODO** this project discharges |
|  4 | ChatGPT MCP                      | (standard-form + generality + history prompt; then short retry)                                    | n/a  | —                   | **tool down** — Codex `exec` failed both attempts this session; compensated by extra WebSearch (#1–3) + grep (Phase 5 [D]) |
|  5 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/`                                               | n/a  | —                   | no `references/` dir under this project's `.mathlib-quality/` (only `overview/`) |
|  6 | nLab                             | "elliptic divisibility sequence" / "even function absolute value"                                  | n/a  | —                   | not a categorical concept; nLab has no EDS page and no named lemma for this triviality |
|  7 | nCatLab                          | —                                                                                                  | n/a  | —                   | not categorical |
|  8 | Stacks Project                   | —                                                                                                  | n/a  | —                   | not an algebraic-geometry/scheme-theoretic statement (it is an integer-index parity identity) |
|  9 | MathOverflow / Math.SE           | "even function f(\|n\|)=f(n)"                                                                        | n/a  | —                   | folklore triviality; no canonical reference — the fact that `f` even ⟹ `f∘abs = f` needs no citation |
| 10 | recent arXiv (≤5 yrs)            | covered by #3 → arXiv 2604.05280                                                                    | yes  | the `EllSequence`/`addMulSub`/`net`/`rel₄` framework | the helper lemma is part of that paper's Lean infrastructure, not a stated result of the paper |

### Literature summary (Phase 3)

Concept identified as: **a parity-normalisation bookkeeping lemma** for the EDS "building block"
`addMulSub` (the paper-level object is the *elliptic relation building block* `W((m+n)/2)·W((m−n)/2)`
from Ward / Stange, formalised in arXiv 2604.05280; the *lemma itself* is just "this is even in arg 2,
hence `|·|`-invariant").
Sources agree on a standard form: **no named form exists** — neither the EDS literature nor mathlib
gives this congruence an independent name. It is the well-known triviality "an even function is
invariant under `|·|`", specialised to `addMulSub`.
Most general standard form: for any even `f : ℤ → R` (`f (-n) = f n`), `f |n| = f n`.
Generality dimensions where the literature varies: none of mathematical substance — the only axis is
"which even function" and "which argument", both of which are Lean-implementation choices.
Disagreement with the literature: none.

---

### Generality analysis — `EllSequence.addMulSub_abs₁`

Literature-standard form (from Phase 3): "if `f` is even then `f |n| = f n`" — here instantiated at
`f = addMulSub W m (·)`, which is even by `addMulSub_neg₁`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `W : ℤ → R`, `[CommRing R]` | sequence into a comm ring | arbitrary even fn into any type with the right `|·|` source | yes (vacuously) | the result has nothing to do with `R` being a ring or with `W` being a sequence — it is purely "even ⟹ abs-invariant" |
| 2 | second argument `n : ℤ` | integer | any linearly-ordered additive group element where `abs_choice` holds | yes | `abs_choice` is the only `ℤ`-specific fact and it generalises to any `LinearOrder`+`Neg` with the lattice abs |
| 3 | the function `addMulSub W m ·` | the specific EDS block | **any** even function | yes | maximal generality is the generic `Function`-level statement, which mathlib already supports via `abs_choice` |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN the generic even-function statement** — but this is the
*correct* narrowness, because the lemma exists to rewrite the *specific* term `addMulSub W m |n|` by
`simp` inside larger proofs. The "more general" form is not a better mathlib lemma; it is the *already
existing* generic pattern (`abs_choice` + the evenness fact), which is exactly how this one-liner is
proved. So there is **no generalisation worth shipping** — the general statement is the trivial folklore
fact, and the specific statement is glue for a non-mathlib definition.
Number of weakening opportunities found: 0 *that yield a mathlib-worthy lemma* (all "weakenings" land
on the generic even-abs triviality that needs no lemma).
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | bundled hyps → typeclasses? | no | — | no "let X be a foo" preamble here |
| 2 | sequences/metric → filters/topology? | no | — | finite algebraic identity, no limits |
| 3 | construction → universal property? | no | — | not a construction |
| 4 | set+closure → bundled substructure? | no | — | no substructure |
| 5 | vector-space/field-specific → weaker typeclass? | no | — | already over an arbitrary `CommRing`; `R` is irrelevant anyway |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index → general additive structure? | technically yes (`ℤ` → ordered group) | the generic even-abs lemma | **but** that target is the folklore `abs_choice` triviality, not a contribution — see 4b |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (the only "modernisation" is to replace this term-specific glue with the
already-existing generic `abs_choice` pattern — i.e. *delete it and inline*, which is the
NO-composable conclusion, not a YES-but-generalise restatement).
One-line reason: there is no organisational improvement to make; the lemma is a 2-call composition of
existing primitives over a Lean-local definition.

---

### Diamond / defeq risk — `EllSequence.addMulSub_abs₁`

**n/a — declaration kind is `lemma`** (no definitional equalities or typeclass-search paths
introduced). Phase 4.5 skipped.

---

### Mathlib search-status: `EllSequence.addMulSub_abs₁`

[A] Lean-Finder       — n/a: tool not exposed in this environment.
[B] Loogle            — n/a: tool not exposed in this environment (lean_loogle unavailable).
[C] LeanSearch        — n/a: tool not exposed in this environment (lean_leansearch unavailable).
[D] Grep mathlib src  `addMulSub`, `namespace EllSequence`, `abs₁`/`abs₀` over `.lake/packages/mathlib/`
                      → **zero hits**. The subject `addMulSub` and the whole `EllSequence` namespace
                      **do not exist in mathlib** (rev `d90090f`). Mathlib's
                      `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` has `IsEllSequence`,
                      `preNormEDS`, `normEDS` — but NOT `addMulSub`, `net`, `rel₄`, `HaveSameParity₄`,
                      and still carries the `normEDS`-is-`IsEllDivSequence` **TODO** that this project
                      proves. → this file is an in-development *extension* of that mathlib file.
[E] Name pattern      grep `addMulSub_abs` across the repo → appears **only** in the 3 forked EDS files
                      (HasseWeil aux, NagellLutz `…Original`, NagellLutz current), identical text. No
                      mathlib occurrence.

Searched for both the user's current form (`addMulSub W m |n| = addMulSub W m n`) and the
literature-standard form ("even `f` ⟹ `f |x| = f x`"). The generic form is also **not** a named
mathlib lemma; mathlib handles it inline via `abs_choice` (e.g.
`Mathlib/RingTheory/Prime.lean:72`, `Mathlib/NumberTheory/NumberField/ClassNumber.lean:156,159`,
`Mathlib/Analysis/Convex/Gauge.lean:284` all do `obtain h | h := abs_choice …` exactly as here).

Concluded: **not in mathlib** — and *cannot* be, since its subject `addMulSub` is not in mathlib. The
generic even-abs fact it specialises is also not a mathlib lemma; mathlib inlines it via `abs_choice`.

---

### Call sites — `EllSequence.addMulSub_abs₁`

Internal use count (this NagellLutz file, excluding the declaring line): **2**
External-to-file callers in the repo: 2 other files, but both are **copies of the same forked API**
(not independent consumers).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:277` | `simp_rw [addMulSub_abs₁, addMulSub, addMulSub₄, sub_add_sub_comm, same.avg₄_add_avg₄]` (inside `avg₄`/`addMulSub₄` proof) |
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:515` | `simp_rw [rel₄, addMulSub_abs₀ W neg, addMulSub_abs₁]` (inside the `rel₄` permutation proof) |
| `…/EllipticDivisibilitySequenceOriginal.lean:266,494` | identical two uses — duplicate of this file |
| `…/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:233,429` | identical two uses — third copy of the same fork |

Inline-derivation grep (was the equivalent re-derived without `addMulSub_abs₁`?): **none** — every
`addMulSub … |…|` site goes through `addMulSub_abs₀`/`abs₁`. (The other `|·|` occurrences found, e.g.
lines 273/229–232, are *consumers* that the lemma is designed to rewrite, not bypasses.)

**Call-sites signal:** K = 2 internal uses, no external (non-fork) consumer, no inline bypass. Per the
Phase-6.0.1 table this is a small, real-but-local helper — "internal glue used a couple of times,
travels with its definition" — leaning toward a NO bucket (it is not standalone API; it is part of the
`addMulSub` micro-API).

---

### Composition check (Phase 6)

Can `EllSequence.addMulSub_abs₁` be derived from mathlib in ≤3 chained calls?

There are two layers here, and **both** point to NO-composable:

**Layer 1 — given the project's own `addMulSub_neg₁`** (the sibling evenness lemma, itself a
2-line `rw …; abel_nf`):
```
Attempt 1:  obtain h | h := abs_choice n <;> simp only [h, addMulSub_neg₁]
  - Mathlib decls used: abs_choice (the ONLY mathlib primitive)
  - Project decls used: addMulSub_neg₁ (sibling, one line away)
  - Result: SUCCEEDS — this is literally the existing proof; 2 "calls" (case-split + rewrite).
```
This is exactly the idiom mathlib itself uses everywhere for even/abs facts (`abs_choice` then close
both branches). No new lemma is warranted — it is inlineable in one tactic line.

**Layer 2 — the deeper reason:** the *statement* mentions `addMulSub`, which **is not in mathlib at
all**. A lemma about `addMulSub` therefore cannot stand alone in mathlib; it can only ever exist
*bundled with* `addMulSub` (i.e. as part of upstreaming the whole `EllSequence` API / arXiv
2604.05280). Within that bundle it is a trivial congruence helper composed from `addMulSub_neg₁` +
`abs_choice` — it is **glue**, not an independent target.

Conclusion: **COMPOSABLE** (1 tactic line from `abs_choice` + the sibling `addMulSub_neg₁`).

---

## Verdict: `EllSequence.addMulSub_abs₁`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): no named result; subject is the EDS building block of arXiv 2604.05280,
  but the lemma is incidental parity bookkeeping ("even ⟹ abs-invariant"), unnamed in the literature
  and in mathlib. ChatGPT MCP down → compensated with 3 WebSearch queries + grep.
- Generality analysis (Phase 4): the only "more general" form is the folklore even-abs triviality that
  mathlib inlines via `abs_choice`; no mathlib-worthy generalisation. No modern idiom (4c).
- Mathlib search (Phase 5): **not in mathlib**, and *cannot* be — `addMulSub` / `EllSequence` are not
  in mathlib (this file extends mathlib's EDS file; the generic even-abs fact is also not a named
  mathlib lemma, it is inlined via `abs_choice`).
- Composition check (Phase 6): **COMPOSABLE** — one tactic line, `obtain h | h := abs_choice n <;>
  simp only [h, addMulSub_neg₁]`.

**Rationale.**
`addMulSub_abs₁` is a one-line `simp`-helper that says the Lean-local building block `addMulSub W m n`
is unchanged when `|·|` is applied to its second argument. It is not an independently mathlib-able
lemma for two compounding reasons. First, its subject `addMulSub` does not exist in mathlib — this
file is a forward-port that *extends* `Mathlib.NumberTheory.EllipticDivisibilitySequence` (which still
carries the very `normEDS`-is-an-EDS TODO this project discharges, and which lacks the
`addMulSub`/`net`/`rel₄` machinery from arXiv 2604.05280). A lemma whose statement names a
non-mathlib definition can only travel *with* that definition, as part of the larger `EllSequence`
upstreaming bundle — never as a standalone PR. Second, even granting that bundle, the lemma is a
trivial 2-call composition: case-split on `abs_choice n` (the sole mathlib primitive) and rewrite by
the sibling evenness lemma `addMulSub_neg₁`. This is precisely the `abs_choice`-then-close-both-branches
idiom mathlib already uses inline in `RingTheory/Prime.lean`, `NumberField/ClassNumber.lean`,
`Analysis/Convex/Gauge.lean`, etc. There is no general "even ⟹ `f|x|=fx`" lemma in mathlib to cite and
none is wanted; the pattern is short enough to inline.

So within the project this lemma is fine and should stay as local glue (K = 2 honest internal uses, no
inline bypass). It simply is **not** a mathlib contribution in its own right: if/when the `EllSequence`
API is upstreamed, this and its siblings (`addMulSub_neg₀/neg₁/abs₀/same/swap`) ride along as part of
that file's internal API; they are not separate mathlib lemmas, and each is a ≤2-call composition.

**WHY not (refactor-actionable).**
Mathlib has the building block — `abs_choice` (`Mathlib/Algebra/Order/AbsoluteValue/…`, the
`|a| = a ∨ |a| = -a` disjunction) — and the project already has the evenness fact `addMulSub_neg₁`
one screen up. The exact form is the 1-line composition below. No standalone mathlib lemma is needed
or possible (the subject is non-mathlib).

Mathlib building blocks: `abs_choice` (only mathlib dependency) + project-internal `addMulSub_neg₁`.

Composition sketch (≤3 lines — it *is* the current proof):
```lean
example (W : ℤ → R) (m n : ℤ) : addMulSub W m |n| = addMulSub W m n := by
  obtain h | h := abs_choice n <;> simp only [h, addMulSub_neg₁]
```

Call sites in this project (Phase 6.0): K = 2 (lines 277 and 515), both inside the `EllSequence`
fork's own proofs.

Refactor plan: **no mathlib action.** Keep `addMulSub_abs₁` as local glue exactly where it is — it is
correctly factored (the two `simp_rw` call sites genuinely reuse it, and inlining the `abs_choice`
case-split into each `simp_rw` would be strictly worse). The only "mathlib" consequence is negative:
do **not** file a PR for this lemma in isolation. It is upstream-relevant only as part of the whole
`EllSequence` / `addMulSub` API (arXiv 2604.05280) — and there it is internal-API glue, not a
headline lemma. If that whole API is ever upstreamed, this lemma travels with `addMulSub` and stays a
1-line proof; it never becomes an independent mathlib declaration.

Next action: none toward mathlib. Leave the lemma in place as project-local infrastructure. (If
desired, the broader question "should the entire `EllSequence` extension be upstreamed to
`Mathlib.NumberTheory.EllipticDivisibilitySequence`?" is a separate, BIG decision about the *file*,
not about this glue lemma — run `/mathlibable` on the headline results like `isEllDivSequence_normEDS`
for that, not on `addMulSub_abs₁`.)

---

## Next step

No mathlib action for `addMulSub_abs₁`. It is a ≤2-call composition (`abs_choice` + the sibling
`addMulSub_neg₁`) about a Lean-local definition (`addMulSub`) that is not in mathlib; it is correct,
correctly-factored local glue and should stay in the project. Do not PR it standalone.
