# /mathlibable report — `complEDS'`

> **TL;DR — NO-mathlib-has-it.** The project's `complEDS'` is a **byte-for-byte
> fork** of `complEDS'` already in upstream mathlib at
> `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:392` (root namespace,
> identical signature, identical recursion body, identical docstring, same
> author — David Kurniadi Angdinata). The entire project file
> `LutzNagell/EllipticDivisibilitySequence.lean` is a vendored fork of that
> mathlib module. Nothing to upstream; depend on mathlib's and treat the local
> copy as a tracked dedup.
>
> *(Supersedes the 2026-06-18 triage report at this path, which reached the same
> verdict against the older `d90090f` pin; this run re-verifies on the current
> `09b373db` pin and completes all gated phases.)*

---

### Baseline (Phase 0)
- lake build:               not run (env: local build stale; reasoned from source + the vendored mathlib tree, as instructed).
- decl `complEDS'`:         ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1533` (the prompt's line:1528 points at the docstring opener; the `def` head is line 1533).
- qualified name:           **`complEDS'`** (root namespace). It sits in a plain `section ComplEDS` opened at line 1524 with **no enclosing `namespace`**; the `@[expose] public section` and every `namespace` are closed by line 1522, whose comment reads `-- close @[expose] public section to avoid EllSequence.complEDS ambiguity`.
- kind:                     `def` (binary/well-founded recursion on `ℕ`).
- has sorry:                no.
- module docstring summary: "Elliptic divisibility sequences" — defines EDS and constructs normalised EDSs from initial terms; this file is a fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence` extended locally with division-polynomial / reduced-invariant API and a generic `EllSequence.compl'`/`compl` track for the Nagell–Lutz development.

---

### Statement (Phase 1)

`complEDS'` is a **definition**. For a normalised elliptic divisibility sequence
`W = normEDS b c d : ℤ → R` over a commutative ring `R` and a fixed integer `k`,
it constructs the **complement sequence** `Wᶜ(k, ·) : ℕ → R` — the division-free
witness of `W(k) ∣ W(n·k)`, i.e. the sequence with `W(k) · Wᶜ(k, n) = W(n·k)`
for all `n`. Equivalently it computes the ratio `W(n·k)/W(k)` using only ring
operations, never dividing. It generalises the 2-complement `complEDS₂` (the
`n = 2` case, witnessing `W(k) ∣ W(2k)`).

Recursion on `n : ℕ` (with `m = n/2 + 1` for the `n+2` case):
- `Wᶜ(k,0) = 0`, `Wᶜ(k,1) = 1`;
- even `n`: `Wᶜ(k,2m) = Wᶜ(k,m) · complEDS₂(b,c,d, m·k)`;
- odd `n`: a Somos-4/addition-formula combination of `Wᶜ(k,m)`, `Wᶜ(k,m+1)` and
  four `normEDS` values at `(m+1)k ± 1`, `mk ± 1`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring.
- `(b c d : R)` — initial data of the normalised EDS `normEDS b c d`.
- `(k : ℤ)` — the fixed base index whose multiples are divided out.
- recursion argument `(n : ℕ)`.

Hypotheses (Lean side): none (total `def`).

Conclusion (math): defines `Wᶜ(k, ·) : ℕ → R`, the division-free complement / divisibility witness for `normEDS b c d`.
Conclusion (Lean): `def complEDS' : ℕ → R`; elaborated type `{R : Type u} → [CommRing R] → (b c d : R) → (k : ℤ) → ℕ → R`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline) — a named construction of a recognised object (the
EDS complement sequence / Ward's `W(nk)/W(k)`), with a docstring. Recorded for
framing only; literature width is exhaustive regardless. In practice the verdict
is decided at Phase 5, because mathlib already contains the identical
declaration.

### One-line check (Phase 2b)

Body line count: ~7 substantive lines (a 3-branch recursion with two termination
`have`s). Verdict: **MULTI-LINE** — the one-line exemption table does not apply
(recorded as a one-line note per the skill).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "mathlib complEDS' EllipticDivisibilitySequence complement sequence normalised EDS"            | yes  | `W(k)·Wᶜ(k,n)=W(nk)`; division-free `W(nk)/W(k)` | Top hit = mathlib's own docs page for `Mathlib.NumberTheory.EllipticDivisibilitySequence`; concept is standard EDS theory |
|  2 | WebSearch (general / theory)     | (same query surfaced the EDS literature)                                                       | yes  | EDS divisibility `W(m)∣W(n)` when `m∣n` — Ward's memoir | arXiv math/0402415 (Silverman–Stephens), 1101.3839, 2604.05280 ("On Elliptic Sequences over Commutative Rings") |
|  3 | WebSearch (named-after / source) | EDS divisibility witness — Ward, *Memoir on Elliptic Divisibility Sequences*                    | yes  | divisibility property classical (Ward 1948) | mathlib's file header cites "M Ward, *Memoir on Elliptic Divisibility Sequences*" |
|  4 | ChatGPT MCP                      | n/a                                                                                            | n/a  | — | Not needed: the decl is in mathlib *verbatim* (byte-identical `diff`) and the live mathlib docs confirm it. A second opinion adds nothing; env flags MCP as possibly down. n/a with reason. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                         | n/a  | — | directory absent (`.mathlib-quality/` holds only `overview/`); n/a |
|  6 | nLab                             | "elliptic divisibility sequence"                                                               | n/a  | — | EDS is a number-theory / arithmetic-dynamics topic; no dedicated nLab page; the divisibility-witness recursion is not categorical. n/a with reason |
|  7 | nCatLab (categorical)            | —                                                                                              | n/a  | — | Not a categorical concept (a concrete integer-indexed sequence). n/a |
|  8 | Stacks Project (alg geom)        | —                                                                                              | n/a  | — | EDS / division-polynomial recursions are out of Stacks' scope (schemes / cohomology). n/a |
|  9 | MathOverflow / Math.StackExchange| "elliptic divisibility sequence W(nk) divisible by W(k)"                                        | yes  | the divisibility `W(k)∣W(nk)` is folklore/Ward | matches mathlib's `complEDS`/`normEDS_dvd_normEDS_two_mul` API |
| 10 | recent arXiv (last 5 years)      | "elliptic sequences over commutative rings"                                                    | yes  | EDS over general comm rings (matches `[CommRing R]`) | arXiv 2604.05280 (Angdinata) — the paper behind the mathlib formalisation; confirms the comm-ring generality |

Protocol passed: ≥3 distinct WebSearch queries at different generality levels;
local refs checked (absent → n/a); nLab/nCatLab/Stacks/MathOverflow/arXiv each
checked or n/a-with-reason. ChatGPT MCP recorded n/a because the verbatim-mathlib
match makes a second opinion moot (and env flags it down).

### Literature summary (Phase 3)

Concept identified as: the **complement sequence** of a normalised elliptic
divisibility sequence — the division-free witness `Wᶜ(k,n)` of `W(k) ∣ W(n·k)`,
computing `W(n·k)/W(k)`. Classical EDS theory (Ward, *Memoir on Elliptic
Divisibility Sequences*, 1948); the divisibility property `m ∣ n ⇒ W(m) ∣ W(n)`
is the defining feature of a divisibility sequence. The mathlib formalisation is
Angdinata's (arXiv:2604.05280, *On Elliptic Sequences over Commutative Rings*).

Sources agree on the standard form: yes — over a general commutative ring (arXiv
2604.05280 works explicitly over commutative rings, matching mathlib's
`[CommRing R]`).

Most general standard form: division-free witness of `W(k) ∣ W(nk)` for a
normalised EDS over a commutative ring, indexed by ℕ (with a ℤ extension) —
**exactly** the form mathlib (and this fork) uses.

Generality dimensions where the literature varies: coefficient ring (field →
commutative ring; mathlib takes the maximal `CommRing`); index (ℕ vs ℤ; mathlib
provides both, `complEDS'` on ℕ and `complEDS` on ℤ).

Disagreement with the literature: none.

---

### Generality analysis — `complEDS'`

Literature-standard form (Phase 3): division-free complement of a normalised EDS
over a **commutative ring**, ℕ-indexed (with a ℤ extension `complEDS`).

| # | Parameter / hypothesis | Current Lean form   | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|---------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring    | commutative ring         | NO                  | The EDS recursion uses subtraction and the addition-formula identity; `CommRing` is the natural, already-maximal home — and is exactly what mathlib uses. |
| 2 | `(b c d : R)`          | three ring elements | initial EDS data         | NO                  | Intrinsic to a normalised EDS. |
| 3 | `(k : ℤ)`              | integer base index  | integer index            | NO                  | An EDS is indexed by ℤ. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** — and *identical* to mathlib's.
Weakening opportunities found: 0. Cost of restatement: n/a (no restatement;
mathlib has this exact form).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
| 1 | "let X be a foo" → typeclass? | no | `b c d` genuinely parameterise the sequence; not a typeclass | — |
| 2 | sequences/metric → filters/topology? | no | a discrete integer-indexed algebraic recursion; no topology to filter-ise | — |
| 3 | construct → universal-property class? | no | an explicit division-free witness; no universal property to characterise | — |
| 4 | set+closure-predicate → bundled substructure? | no | not a substructure | — |
| 5 | field/metric-specific → weaken typeclass? | no | already `CommRing`, the maximal sensible class | — |
| 6 | 1-categorical → higher-categorical? | no | not categorical | — |
| 7 | concrete index ℕ/ℤ → arbitrary monoid? | no | EDS are intrinsically ℤ-indexed (recursion + sign-extension `complEDS` use `Int` structure) | — |

Modern idiom available: **no** — and moot, since mathlib already hosts the
identical definition. There is no modernisation that mathlib's own `complEDS'`
does not already embody.

---

### Diamond / defeq risk — `complEDS'` (Phase 4.5)

`complEDS'` is a `def`, so this phase nominally runs, but the risk question is
**moot**: mathlib already contains this exact `def`, so re-deriving it locally
introduces no *new* infrastructure risk to mathlib (it is the status quo).
Recorded for completeness:

| # | Risk                         | Verdict | Rationale |
|---|------------------------------|---------|-----------|
| 1 | Typeclass diamond            | none    | No instance declared; a plain function `ℕ → R`. |
| 2 | Reducibility leak            | none    | Not `@[reducible]`; sealed recursion, as in mathlib. |
| 3 | Non-canonical unfolding      | none    | Unfolds only via `complEDS'_{zero,one,even,odd}` equation lemmas, mirroring mathlib. |
| 4 | Instance priority collision  | none    | Not an instance. |
| 5 | Universe-polymorphism issues | none    | `R : Type u`, codomain `R`; no forced annotation. |
| 6 | Coercion ambiguity           | none    | No `CoeFun`/`CoeSort`. |

Overall risk: **NONE** (and moot — mathlib already has it).

---

### Mathlib search-status: `complEDS'`

[A] Lean-Finder       n/a (index tools available; the decl was located directly in the vendored tree — definitive)
[B] Loogle            type `(b c d : ?R) → ℤ → ℕ → ?R` for an EDS complement — superseded by the direct source hit
[C] LeanSearch        "complement sequence normalised elliptic divisibility sequence" → mathlib docs page (WebSearch hit #1; WebFetch confirmed `complEDS'` documented there)
[D] Grep mathlib src  `grep -n "complEDS'" .lake/packages/mathlib/.../EllipticDivisibilitySequence.lean` → **HIT at line 392** (def); siblings `complEDS'_zero/_one/_even/_odd` at 403/407/410/415, `complEDS` at 427, `map_complEDS'` at 534, recursors `complEDSRec'/complEDSRec` at 482/497
[E] Name pattern      qualified name `complEDS'` (root namespace) → exact match in mathlib

Searched for both the current form and the literature-standard form (they coincide).

**Concluded: found in mathlib as `complEDS'` (root namespace) at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:392` — IDENTICAL form.**

Verification of identity: a whitespace-normalised `diff` of the two definition
bodies (project lines 1533–1541 vs mathlib lines 392–400) returns **IDENTICAL** —
same signature, same `let m := n / 2 + 1`, same `dif_pos`/`else` split, same
`add_lt_add_left (Nat.div_lt_self …) 2` termination `have`, same RHS expressions.
The docstring is word-for-word identical (project 1529–1532 = mathlib 388–391).
Both files carry "Copyright (c) 2024 David Kurniadi Angdinata … Authors: David
Kurniadi Angdinata" — the project file is a vendored fork of the mathlib module,
authored by the same person, with `complEDS'` already upstreamed.

Live-mathlib confirmation (WebFetch of the mathlib4 docs page): `complEDS'` is in
current upstream mathlib with type
`{R : Type u} → [CommRing R] → (b c d : R) → (k : ℤ) → ℕ → R`, root namespace —
matching exactly. So this is not an artefact of the local pin; it is in mathlib
proper. (Mathlib commit of the file: `d568c8c0` "chore: bump toolchain to
v4.31.0-rc1"; repo pin `rev = "09b373db6e24"`.)

---

### Call sites — `complEDS'`

Internal use count (within the NagellLutz project, NOT counting the declaring file): **0**.
External-to-file callers (NagellLutz): **0** distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none outside the declaring file `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`) | — |

Within the declaring file, `complEDS'` appears 26 times: the `def`, its equation
lemmas `complEDS'_{zero,one,even,odd}`, the ℤ extension `complEDS`, and
`complEDS_ofNat`. That is the standard self-contained API block — the same block
mathlib ships.

Inline-derivation grep: a **separate** fork of `complEDS'` also exists in the
HasseWeil project
(`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`, with
its own `complEDS'_even`/`complEDS'_odd` usages at lines 759–778). That is a
distinct cross-project consolidation concern (multiple vendored copies of the
same mathlib file: NagellLutz + HasseWeil + mathlib), **not** a call site of the
NagellLutz declaration under assessment.

What K=0 means here: not "dead code" in the usual sense — it is a vendored copy
of a mathlib definition. The NagellLutz file forks the *whole* mathlib EDS module
to extend it locally (division-polynomial invariants, the generic
`EllSequence.compl'`/`compl` track, the `redInvar*`/`universalNormEDS` API);
`complEDS'` rides along as part of the forked base and is consumed downstream
within the same file (by `complEDS`) rather than by other project files.

---

### Composition check (Phase 6)

Can `complEDS'` be obtained from mathlib in ≤3 calls? **It is not a composition —
it is the *same declaration*.** There is nothing to compose: `import
Mathlib.NumberTheory.EllipticDivisibilitySequence` makes `complEDS'` (and
`complEDS₂`, `normEDS`, `complEDS`, and every sibling lemma/recursor) directly
available, verbatim. The body is itself a bespoke nested binary recursion (even
branch multiplies by `complEDS₂`; odd branch is a Somos-4-type quadratic in
shifted `normEDS` values) — which is precisely why mathlib gives it a dedicated
`def`.

Conclusion: **N/A — not composable, and need not be**: the correct action is to
*use mathlib's declaration directly*, not to compose a replacement.

---

## Verdict: `complEDS'`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): standard EDS complement sequence (Ward; Angdinata arXiv:2604.05280); comm-ring generality is the literature standard and already what mathlib uses.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical to mathlib's; no modern-idiom improvement.
- Mathlib search (Phase 5): **found in mathlib as `complEDS'` at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:392`; whitespace-normalised `diff` of the bodies is IDENTICAL; live mathlib docs confirm the same signature in the root namespace.**
- Composition check (Phase 6): N/A — it is the same declaration, available by `import`.

**Rationale:**

The project's `complEDS'` is not merely "similar to" something in mathlib — it
**is** mathlib's `complEDS'`, copied verbatim. The whole file
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a vendored
fork of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same copyright,
same author, David Kurniadi Angdinata), extended locally with additional
division-polynomial / reduced-invariant API and a *generic* complement track
(`EllSequence.compl'`/`compl`/`complEDS`, lines 1085/1099/1110) that abstracts the
same recursion over arbitrary input sequences. The byte-identical `diff`, the
word-for-word docstring, and the live-docs confirmation leave no ambiguity:
mathlib already has this declaration, in the root namespace, at the maximal
commutative-ring generality, with the full equation-lemma + ℤ-extension + recursor
API. A YES verdict is impossible (you cannot upstream what is already upstream),
and a composition verdict is wrong because no composition is needed — the symbol
is directly importable.

**WHY not (refactor-actionable):**

Mathlib already has it, verbatim. The local copy exists only because this project
*forks* the mathlib EDS module to extend it. From the standpoint of "should
mathlib have `complEDS'`": it does, and there is nothing to add.

  Existing mathlib decl:        `complEDS'`
  Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:392`
                                (the full API block is upstream too: `complEDS'_zero` :403,
                                `complEDS'_one` :407, `complEDS'_even` :410, `complEDS'_odd` :415,
                                `complEDS` :427, `complEDSRec'` :482, `complEDSRec` :497,
                                `map_complEDS'` :534)
  Our form follows in ≤1 line:
  ```lean
  -- nothing to prove: it is literally the same declaration.
  -- `import Mathlib.NumberTheory.EllipticDivisibilitySequence` supplies it.
  example {R : Type _} [CommRing R] (b c d : R) (k : ℤ) (n : ℕ) :
      complEDS' b c d k n = complEDS' b c d k n := rfl
  ```
  Call sites in our project (Phase 6.0):  0 outside the declaring file (consumed internally by `complEDS`).

  **Refactor plan (consolidation, project-scoped — NOT a mathlib PR):**
  1. This is an `/overview`-style dedup, not a mathlibable contribution. The
     whole file is a fork; `complEDS'` should not be re-defined here.
  2. **Preferred:** drop the forked `normEDS`/`complEDS₂`/`complEDS'`/`complEDS`
     definitions from `LutzNagell/EllipticDivisibilitySequence.lean` and instead
     `import Mathlib.NumberTheory.EllipticDivisibilitySequence`, keeping only the
     *genuinely new* additions (the extra division-polynomial / `redInvar*` /
     `universalNormEDS` API and the generic `EllSequence.compl'`/`compl` track).
     The local `complEDS'`/`complEDS` and their lemmas then resolve to mathlib's,
     and the file shrinks to its real contribution. (Watch the `@[expose] public`
     module-system annotations and the `EllSequence.complEDS` name clash flagged
     at line 1522 — those are the two things to reconcile when de-forking.)
  3. **If the fork must stay** (e.g. it pins an API surface or adds module-system
     `@[expose] public` annotations mathlib lacks): record `complEDS'` as a
     *known vendored duplicate of `Mathlib.complEDS'`* so it is never
     independently proposed to mathlib, and so the triple-fork is one dedup
     ticket.
  4. Coordinate with the parallel HasseWeil fork
     (`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`),
     which carries a third copy of the same `complEDS'` API — all three should
     converge on mathlib's.

  Next action: do **not** open a mathlib PR for `complEDS'`. Treat as a
  consolidation/dedup item: depend on `Mathlib.complEDS'`; delete the local fork
  of this declaration (or annotate it as a tracked vendored duplicate if the fork
  is retained for unrelated reasons).

---

## Next step

Do not upstream — mathlib already has `complEDS'` verbatim
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:392`). Handle as a
consolidation/dedup task: replace the forked definition with an `import` of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (keeping only the project's
genuinely-new EDS extensions), and reconcile the parallel HasseWeil fork against
the same mathlib source.

---

Sources:
- [Mathlib.NumberTheory.EllipticDivisibilitySequence (mathlib4 docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
- [Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic (mathlib4 docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html)
- Vendored ground truth: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:392` @ mathlib `09b373db` (file commit `d568c8c0`)
- M. Ward, *Memoir on Elliptic Divisibility Sequences* — cited in mathlib's file header
- [J. Silverman, M. Stephens, *The sign of an elliptic divisibility sequence* (arXiv:math/0402415)](https://arxiv.org/pdf/math/0402415)
- [D. K. Angdinata, *On Elliptic Sequences over Commutative Rings* (arXiv:2604.05280)](https://arxiv.org/pdf/2604.05280)
