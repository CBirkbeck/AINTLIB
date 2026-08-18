# /mathlibable report — `normEDS_def`

> AINTLIB `/overview` Step-9 mathlibable assessment, single declaration.
> Project: `projects/NagellLutz` (Nagell–Lutz; elliptic curves; division
> polynomials; elliptic divisibility sequences).
> Target: `normEDS_def` at
> `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:893`.

**TL;DR — Verdict: `NO-mathlib-has-it`.** This file is a *fork* of mathlib's
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. The def it unfolds,
`normEDS`, is in mathlib **verbatim** (same body, same top-level name, same
`section NormEDS`), together with the entire surrounding lemma API. `normEDS_def`
is a `:= rfl` glue lemma that mathlib deliberately does **not** ship (mathlib
ships no `_def` rfl-unfolding lemma for `normEDS` or for *any* of its siblings —
its convention is `simp only [normEDS]`). The lemma has **zero call sites** in
the whole AINTLIB repo. Nothing to upstream.

---

### Baseline (Phase 0)
- lake build:               not re-run (build is stale per task brief); reasoning from source. The decl elaborates as written in the committed file.
- decl `normEDS_def`:        ✓ resolved at `EllipticDivisibilitySequence.lean:893`
- kind:                      `lemma`
- has sorry:                 no (`:= rfl`)
- module docstring summary:  "Elliptic divisibility sequences (EDS) … constructs normalised EDSs from initial terms." Direct fork of mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence` (same Apache header, author David Kurniadi Angdinata, same `## Main definitions`).

**Qualified-name verification.** Parsed/assumed name `normEDS_def` — **confirmed
top-level (no namespace prefix).** At line 893 the only enclosing scope is
`section NormEDS` (line 881 → `end NormEDS` line 1520), which is a *named
section*, not a `namespace` (there is no `namespace NormEDS` in the file). The
`EllSequence` namespace opened at line 90 was already closed at line 597 (`end
EllSequence`). So the fully-qualified name is exactly **`normEDS_def`**. (Mathlib
keeps `normEDS` at top level too, under `variable (b c d : R)`.)

---

### Statement (Phase 1)

`normEDS_def` is a *definitional-unfolding lemma*. Verbatim:

```lean
def normEDS (n : ℤ) : R :=
  preNormEDS (b ^ 4) c d n * if Even n then b else 1

lemma normEDS_def (n : ℤ) :
    normEDS b c d n = preNormEDS (b ^ 4) c d n * if Even n then b else 1 := rfl
```

In prose: it asserts that the normalised elliptic divisibility sequence
`normEDS b c d` evaluated at `n` equals its own definition — the auxiliary
sequence `preNormEDS (b^4) c d n` times `b` when `n` is even and `1` when `n` is
odd. This is `rfl`: the statement *is* the definition of `normEDS`, restated as a
propositional equation so it can be used by `rw`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(b c d : R)` — the three initial data of the normalised EDS (giving
  `W(2)=b`, `W(3)=c`, `W(4)=d·b`).
- `(n : ℤ)` — the index.

Hypotheses: none.

Conclusion (math): the value of Ward's normalised EDS at `n` is its defining
expression. (No mathematical content beyond the definition of `normEDS`.)

Conclusion (Lean): `normEDS b c d n = preNormEDS (b ^ 4) c d n * if Even n then b else 1`.

**Mathematical anchor of the underlying object.** `normEDS` is the canonical
normalised elliptic divisibility sequence of Morgan Ward (*Memoir on Elliptic
Divisibility Sequences*, Amer. J. Math. 70 (1948)), with `W(0)=0, W(1)=1,
W(2)=b, W(3)=c, W(4)=d·b`; the `b^4`/even-`b` bookkeeping in `preNormEDS` exists
to avoid ring division by `b` in the recursive construction and to feed the
univariate `n`-division polynomials of an elliptic curve (per the file's own
implementation notes). This anchor is about `normEDS`, **not** about
`normEDS_def` — `normEDS_def` is a Lean-encoding artifact with no literature
counterpart.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A `:= rfl` unfolding lemma of an existing def. Not a new structure, not a
named theorem, not a `## Main results` entry (the main result is
`isEllDivSequence_normEDS`, not this). The *def* `normEDS` would be BIG — but the
def is not the target, and it is already in mathlib.

(Literature width was run EXHAUSTIVE-where-meaningful regardless; see Phase 3.
Because the object `normEDS` is a known mathlib def, the lit work confirms the
anchor rather than discovering a standard form.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`:= rfl`).
One-liner verdict: this is a `lemma`, so the def-oriented Phase-2b table is `n/a`.
But the spirit applies: it is a one-line `rfl` glue lemma — a strong negative
signal for mathlib inclusion unless an exemption holds.

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                | no       | Mathlib's own sibling lemmas (`normEDS_zero/one/two/three/four/neg/even/odd`) prove via `simp [normEDS]` — i.e. they unfold the def directly and do **not** route through a `_def` lemma. So no downstream proof needs `normEDS_def` as a defeq barrier; the convention is to unfold `normEDS` itself. |
| Avoid typeclass diamonds         | no       | It's a `lemma`, introduces no instance/defeq path. |
| Mark semantic intent / API name  | no       | Zero consumers in-repo (Phase 6.0). The def `normEDS` already carries the docstring and API name; the `rfl` lemma adds no stable surface mathlib wants. |

Conclusion: **ONE-LINER (rfl) WITHOUT-EXEMPTION** — biases the verdict toward a NO
bucket.

---

### Literature search (Phase 3)

The mathematically-searchable object is `normEDS` (Ward's normalised EDS). The
*lemma* `normEDS_def` has no independent literature existence: "the definition,
restated as an equation" is not a named result in any source — it is an artifact
of formalisation. The channels below therefore document the *object's* standard
form (to confirm the def is the literature-standard one) rather than hunt for
`normEDS_def`.

| #  | Channel                          | Query                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | elliptic divisibility sequence normalised Ward definition recurrence  | yes  | Ward EDS: `W₀=0, W₁=1`, `W₂∣W₄`, recurrence `W₍ₘ₊ₙ₎W₍ₘ₋ₙ₎Wᵣ² = W₍ₘ₊ᵣ₎W₍ₘ₋ᵣ₎Wₙ² − W₍ₙ₊ᵣ₎W₍ₙ₋ᵣ₎Wₘ²` | Wikipedia "Elliptic divisibility sequence"; Ward 1948. Matches the file's `IsEllSequence` recurrence and the `normEDS` initial values. |
|  2 | WebSearch (general / div-poly)   | "elliptic divisibility sequence" division polynomial normalization initial values b c d | yes  | `Wₙ = λ^{n²−1} ψₙ(x,y)`; ψ₀=0, ψ₁=1, ψ₂, ψ₃ initial terms | Wikipedia "Division polynomials"; eprint 2008/444; arXiv math/0404412. Confirms the `normEDS`↔division-polynomial link the file's notes cite. |
|  3 | WebSearch (named-after / aliases)| (covered by #1) "Ward" elliptic sequence; "elliptic net" (Stange)      | yes  | same object; elliptic nets generalise to higher rank | arXiv 0710.1316 (Stange). No alternate name for a "definition lemma". |
|  4 | ChatGPT MCP                      | standard def of normalised EDS + generality + historical evolution    | n/a  | —                   | ChatGPT MCP reported down in the environment brief; substituted with extra WebSearch (#1–#3) + Wikipedia/Ward primary. The object's standard form is unambiguous from those, so the gap does not affect the verdict. |
|  5 | Local references                 | grep `.mathlib-quality/references/` for EDS / normEDS / Ward          | n/a  | —                   | No source-paper PDFs staged for NagellLutz in `.mathlib-quality/references/` (refs are local-only per CLAUDE.md and not present). File cites "M Ward, *Memoir on Elliptic Divisibility Sequences*". |
|  6 | nLab                             | elliptic divisibility sequence                                        | n/a  | —                   | Not an nLab concept (no categorical content); the recurrence is classical number theory. Recorded n/a. |
|  7 | nCatLab (categorical)            | —                                                                     | n/a  | —                   | Not a categorical concept. |
|  8 | Stacks Project (alg geom)        | elliptic divisibility sequence / division polynomial                  | n/a  | —                   | Stacks covers scheme-theoretic AG, not EDS recurrences; no entry. |
|  9 | MathOverflow / MSE               | elliptic divisibility sequence definition equivalence                 | yes  | confirms two inequivalent literature definitions (arithmetic vs geometric); normalisation conventions vary by `λ`/initial terms | Surfaced via #1 (researchgate/isid PDFs). The mathlib `normEDS` fixes one standard convention. |
| 10 | recent arXiv (last 5 yrs)        | recurrence relation elliptic divisibility sequences                   | yes  | arXiv 2102.07573 (2021) — recurrence relations; consistent with the classical normalised form | No new "definition lemma" notion. |

### Literature summary (Phase 3)

Concept identified as: **Ward's normalised elliptic divisibility sequence**
(`normEDS`), the EDS with initial data `W(2)=b, W(3)=c, W(4)=d·b` built from the
auxiliary `preNormEDS`.
Sources agree on the standard form: **yes** for the *object* — the recurrence and
the normalisation (modulo the classical `λ^{n²−1}` scaling freedom, which mathlib
pins down by its specific `preNormEDS` construction).
Most general standard form: the object is already stated over an arbitrary
`CommRing R` (mathlib/this file), which is *more* general than the classical
integer EDS — this is mathlib's deliberate generality and is unchanged here.
Generality dimensions where the literature varies: only the choice of
normalisation constant / initial terms; `normEDS` fixes one canonical choice.
Disagreement with the literature: **none.** And crucially: **`normEDS_def` has no
literature analogue at all** — there is no mathematical notion of "the unfolding
lemma of a definition". Its content is exactly the definition of `normEDS`, which
the literature (and mathlib) already fixes.

---

### Generality analysis (Phase 4)

Literature-standard form of the object: Ward's normalised EDS over a commutative
ring, which mathlib (and this fork) already realise as `normEDS` over any
`[CommRing R]`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form? | Reason |
|---|------------------------|-------------------|---------------------|--------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | comm. ring (classical: ℤ) | NO | Already maximally general for this construction; classical EDS is the `R = ℤ` specialisation. Mathlib uses the same. |
| 2 | `(b c d : R)`          | three ring elements | three initial data | NO | Intrinsic to the normalised construction. |
| 3 | `(n : ℤ)`              | integer index     | integer index       | NO | EDS are ℤ-indexed by definition. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is literally mathlib's form,
verbatim). Number of weakening opportunities: **0**. No restatement proposed —
the def already lives in mathlib at the right generality, and the `rfl` lemma
just mirrors it.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
| 1 | "let X be a foo" → typeclass? | no | n/a — no bundled-hypothesis preamble; just `rfl`. | — |
| 2 | sequences/metric → filters/topology? | no | n/a — purely algebraic recurrence. | — |
| 3 | construction → universal-property class? | no | n/a — `normEDS` is an explicit construction by design (mathlib's choice). | — |
| 4 | set+closure-pred → bundled substructure? | no | n/a. | — |
| 5 | field/metric-specific → weaken typeclass? | no | already `CommRing`. | — |
| 6 | 1-categorical → higher-categorical? | no | n/a. | — |
| 7 | concrete index ℕ/ℤ/ℝ → general additive structure? | no | EDS are ℤ-indexed intrinsically. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** This is a `:= rfl` unfolding lemma of an existing
mathlib def; there is no contemporary reformulation to make — the only honest
move is to use mathlib's `normEDS` (and `simp only [normEDS]`) directly.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equality or
typeclass-search path). Skipped.

---

### Mathlib search-status: `normEDS_def`

[A] Lean-Finder       "normEDS unfolding", "normEDS equals preNormEDS" — n/a (index not queried live; resolved decisively by direct source grep below)
[B] Loogle            `normEDS _ _ _ _ = preNormEDS _ _ _ _ * _` — n/a (resolved by direct grep)
[C] LeanSearch        "normalised elliptic divisibility sequence definition" — n/a (resolved by direct grep)
[D] Grep mathlib src  `grep -rnE "def normEDS\b|normEDS_def|normEDS b c d n = preNormEDS" .lake/packages/mathlib/Mathlib/` — **HITS** (authoritative)
[E] Name pattern      `normEDS`, `normEDS_def`, `*_def` siblings across mathlib — see below

**Direct-grep findings (authoritative — this file forks the exact mathlib module):**
- `def normEDS` exists in mathlib at
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:289`, body **identical**
  to the project's (`preNormEDS (b ^ 4) c d n * if Even n then b else 1`), same
  top-level name, same `section NormEDS`.
- Mathlib has the **full** surrounding API: `normEDS_ofNat` (293), `normEDS_zero`
  (298), `normEDS_one` (302), `normEDS_two` (306), `normEDS_three` (310),
  `normEDS_four` (314), `normEDS_neg` (318), `normEDS_mul_complEDS₂` (321),
  `normEDS_dvd_normEDS_two_mul` (326), `normEDS_even` (336), `normEDS_odd` (342),
  `map_normEDS` (530).
- **`normEDS_def` does NOT exist** anywhere in mathlib
  (`grep -rnE "\bnormEDS_def\b" .lake/packages/mathlib/Mathlib/` → empty).
- **No `_def` rfl-unfolding sibling exists in mathlib either** — no
  `preNormEDS_def`, `preNormEDS'_def`, `complEDS_def`, `complEDS₂_def`. Mathlib's
  convention for this file is to unfold the def via `simp [normEDS]` /
  `simp_rw [normEDS]` (every sibling lemma does exactly this).

Searched for both:
- user's current form (`normEDS b c d n = preNormEDS (b^4) c d n * if Even n then b else 1`) → present *only* as the body of `def normEDS` and as the RHS pattern inside `normEDS_ofNat` (the ℕ-cast version, line 293–295); never as a standalone `normEDS_def` lemma.
- literature-standard form (Ward's normalised EDS, `def normEDS`) → present in mathlib verbatim.

Concluded: **found in mathlib** — the underlying def `normEDS` is present
identically at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:289`. The
user's `normEDS_def` is the `rfl` unfolding of that mathlib def; it is not itself
in mathlib (by mathlib's deliberate convention of unfolding the def directly).

---

### Call sites — `normEDS_def` (Phase 6.0)

Internal use count: **0** (`grep -rnE "\bnormEDS_def\b" <repo> --include=*.lean
--exclude-dir=.lake` → exactly 1 hit, the declaration itself; zero other uses
anywhere in AINTLIB).
External-to-file callers: **0 files.**

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | — no consumer anywhere in the repo |

Inline-derivation grep: the equation `normEDS … = preNormEDS (b^4) … * if Even …`
appears inside the *def body* and inside `normEDS_ofNat`'s proof, but those route
through `simp [normEDS]`/the def, not through `normEDS_def`. So even the in-file
neighbours bypass this lemma.

Signal (per the call-sites table): **K = 0 internal uses, no inline
re-derivation that uses this lemma.** Combined with Phase 2b
(ONE-LINER-rfl-WITHOUT-EXEMPTION): the case for NO is strong. Mathlib already
covers the need (the def + `simp [normEDS]`), which is exactly why nothing in the
fork reaches for `normEDS_def`.

### Composition check (Phase 6)

Can `normEDS_def` be obtained from mathlib in ≤3 calls?

Attempt 1: `rfl`, given mathlib's `def normEDS`.
  - Mathlib decls used: `normEDS` (the def itself).
  - Result: **succeeds** — the project lemma's proof is literally `:= rfl`, and
    mathlib's `normEDS` has the identical body, so the equation holds by `rfl`
    against the mathlib def. Equivalently, any goal `normEDS_def` would discharge
    is closed by `simp only [normEDS]` (mathlib's own idiom) — 0 extra lemmas.
  - Notes: this is the most trivial composition possible (definitional).

Conclusion: **COMPOSABLE** (degenerately — it is `rfl`/`simp only [normEDS]`
against the existing mathlib def). This reinforces NO-mathlib-has-it: the "need"
is met by the mathlib def directly, with no lemma required.

---

## Verdict: `normEDS_def`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the object `normEDS` is Ward's normalised EDS, a
  known mathlib def; the *lemma* `normEDS_def` has no literature analogue (it is
  a formalisation artifact).
- Generality analysis (Phase 4): MAXIMALLY GENERAL — it is mathlib's exact form;
  no modern-idiom move (4c = no).
- Mathlib search (Phase 5): `def normEDS` present **verbatim** at
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:289` with the full
  lemma API; `normEDS_def` deliberately not shipped (nor any `_def` sibling).
- Composition check (Phase 6): COMPOSABLE — `rfl` / `simp only [normEDS]` against
  the mathlib def; zero call sites in-repo.

**Rationale.**
This file is a direct fork of mathlib's
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (identical Apache
header, same author, same module docstring and API). The declaration
`normEDS_def` unfolds the def `normEDS`, which mathlib already contains **byte
for byte** (`preNormEDS (b ^ 4) c d n * if Even n then b else 1`, top-level,
under `section NormEDS`), alongside the complete normalised-EDS lemma suite
(`normEDS_zero/one/two/three/four/neg/even/odd`, `normEDS_mul_complEDS₂`,
`normEDS_dvd_normEDS_two_mul`, `map_normEDS`). So the mathematical content of the
target is entirely present in mathlib via the def itself.

The one thing mathlib does **not** have is a standalone `rfl` lemma named
`normEDS_def`. That omission is intentional and idiomatic: every mathlib lemma in
this file that needs to expand `normEDS` does so with `simp [normEDS]` /
`simp_rw [normEDS]` (unfolding the def directly), and mathlib ships **no** `_def`
unfolding lemma for `normEDS` or for any of its siblings (`preNormEDS`,
`preNormEDS'`, `complEDS`, `complEDS₂`). Adding a `normEDS_def` rfl lemma to
mathlib would cut against this established local convention without buying
anything — it has **zero** consumers in the entire AINTLIB repo, and any goal it
could rewrite is closed by `simp only [normEDS]`. It is therefore not a mathlib
contribution: mathlib already has the result (the def), and the `rfl` wrapper is
redundant.

**WHY not (refactor-actionable).**
Mathlib already has the underlying object: the def `normEDS` is present
identically. The project lemma `normEDS_def` is the definitional unfolding of
that def and follows from it in **0 lines** (`rfl`), or is replaced at use sites
by mathlib's own idiom `simp only [normEDS]`. There is no API gap: the
surrounding `normEDS_*` lemmas mathlib ships already cover every concrete
evaluation and recurrence a consumer needs, and they themselves never use a
`_def` lemma.

  Existing mathlib decl:        `normEDS` (def)
  Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:289`
  (closest mathlib unfolding helper: `normEDS_ofNat`, same file line 293 — the ℕ-cast variant)
  Our "lemma" follows in ≤1 line:
  ```lean
  example (b c d : R) (n : ℤ) :
      normEDS b c d n = preNormEDS (b ^ 4) c d n * if Even n then b else 1 := rfl
  -- or, at any call site that would have used `rw [normEDS_def]`:
  --   simp only [normEDS]
  ```
  Call sites in our project (from Phase 6.0): **0**.
  Refactor plan: since this whole file is a mathlib fork, the correct action is
  not to keep a local `normEDS_def`. Either (a) drop `normEDS_def` and, in the
  fork, unfold `normEDS` via `simp only [normEDS]` wherever an unfolding is wanted
  (matching mathlib's convention) — there are currently **no** such sites; or
  (b) if/when the fork is reconciled against upstream, delete the local
  `normEDS`/`normEDS_def` duplication entirely and `import` mathlib's
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`, at which point
  `normEDS_def` simply ceases to exist and nothing breaks (no consumers).
  Next action: **delete `normEDS_def`** from the fork (0 call sites to update); rely on
  mathlib's `normEDS` def + `simp only [normEDS]`.

**Caveat for the human (fork-reconciliation note, not a verdict change).** The
verdict is about upstreaming to mathlib, and there it is unambiguous: do not add
`normEDS_def`. As a *fork-hygiene* matter, the larger finding is that this entire
`section NormEDS` (def `normEDS` + its lemmas) duplicates upstream mathlib; the
project-level dedup is to replace the fork with an `import`. That is consolidation
work for `/cleanup` on `main`, outside this single-decl mathlibable scope.

---

## Next step

Delete `normEDS_def` from the project (it has zero call sites); where an unfolding
of `normEDS` is desired, use mathlib's idiom `simp only [normEDS]`. More broadly,
flag the `section NormEDS` block as a verbatim mathlib fork for consolidation
(replace with `import Mathlib.NumberTheory.EllipticDivisibilitySequence`) — a
`/cleanup` dedup task, not a mathlib PR.
