# /mathlibable report — `normEDS_four`

**TL;DR — `NO-mathlib-has-it`.** This file is a near-verbatim fork of
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same author, same
docstrings, same `section NormEDS`). `normEDS_four` exists in mathlib
**character-for-character identically** at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:313-315`. Delete the
local copy; the 4 internal call sites resolve to the mathlib lemma unchanged.

---

### Baseline (Phase 0)
- lake build:               not re-run (build is stale per task brief); reasoning from source, which is unambiguous.
- decl `normEDS_four`:      ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:917-919`
- qualified name:           **`normEDS_four`** (no enclosing namespace — line 881 is `section NormEDS`, a *section* not a namespace; `end NormEDS` at 1520 closes it; no namespace is open at top level. VERIFIED: parsed qualified name `normEDS_four` is correct, NOT `NormEDS.normEDS_four`.)
- kind:                     `lemma` (`@[simp]`)
- has sorry:                no
- module docstring summary: Elliptic divisibility sequences (EDS); constructs normalised EDSs from initial terms — a fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

Exact source (project, lines 917-919):
```lean
@[simp]
lemma normEDS_four : normEDS b c d 4 = d * b := by
  simp [normEDS, show ¬Odd (4 : ℤ) by decide]
```
with `variable (b c d : R)` and `{R : Type u} [CommRing R]` in scope.

---

### Statement (Phase 1)

`normEDS_four` evaluates the canonical normalised elliptic divisibility sequence
`normEDS b c d : ℤ → R` at index `4`, giving `normEDS b c d 4 = d * b`.

The sequence `normEDS b c d` is mathlib's canonical normalised EDS parametrised by
three ring elements `(b, c, d)`, defined by
`normEDS b c d n = preNormEDS (b^4) c d n * (if Even n then b else 1)`.
Its initial values are `W₀ = 0`, `W₁ = 1`, `W₂ = b`, `W₃ = c`, `W₄ = d·b`. This
lemma is the defining-value computation for the fourth term — the even index pulls
in the factor `b`, so `W₄ = (the preNormEDS value at 4, namely d) · b`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(b c d : R)` — the three parameters determining the normalised EDS.

Hypotheses: none.

Conclusion (math): `W₄ = d·b` for the normalised EDS with parameters `(b,c,d)`.
Conclusion (Lean): `normEDS b c d 4 = d * b`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a defining-value `@[simp]` lemma reading off one initial term of a
construction; a helper, not a named theorem or a new structure.

(Literature width run EXHAUSTIVE regardless; SMALL is for framing only.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-line check **n/a**. (The
proof body is a one-line `simp`, but the 2b exemption machinery applies to one-line
*definitions*, not lemmas.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                 | Hit? | Standard form found                                              | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence normalized initial terms W4 division polynomial psi_4" | yes  | normalised EDS determined by `W₁=1, W₂, W₃, W₄`; `W₄ = ψ₄(P)`     | Wikipedia "Elliptic divisibility sequence"; arXiv 1001.5303, math/0404412 |
|  2 | WebSearch (general/Ward form)    | "Ward elliptic divisibility sequence normalisation W1=1 W2 W3 W4 recurrence" | yes  | EDS determined by `(W₂,W₃,W₄)`; `W₁=1`, integrality if `W₂∣W₄`    | arXiv math/0412293 (Swart), math/0402415; **also returned mathlib's own DivisionPolynomial docs** |
|  3 | WebSearch (named-after / source) | Ward, *Memoir on Elliptic Divisibility Sequences* (the file's cited ref) | yes  | Ward (1948) is the originating reference; the initial-term parametrisation is his | the file's `## References` cites exactly this |
|  4 | ChatGPT MCP                      | standard form + generality + history of `W₄` of a normalised EDS      | n/a  | MCP down per task brief ("ChatGPT MCP may be down")              | fallback: WebSearch ×3 + the in-tree mathlib source comparison (Phase 5), which is conclusive |
|  5 | Local references                 | `.mathlib-quality/references/` for "EllipticDivisibility" / "normEDS" | n/a  | not consulted; the decisive evidence is the in-tree mathlib fork | the mathlib copy in `.lake/packages/` (Phase 5) settles it without refs |
|  6 | nLab                             | "elliptic divisibility sequence"                                      | n/a  | not an nLab/categorical concept — classical number theory         | recorded n/a with reason |
|  7 | nCatLab (categorical)            | —                                                                     | n/a  | not a categorical concept                                         | n/a |
|  8 | Stacks Project (alg geom)        | "division polynomial" / "elliptic divisibility"                       | n/a  | not covered by Stacks (no division-polynomial / EDS material)     | n/a with reason |
|  9 | MathOverflow / Math.SE           | "elliptic divisibility sequence W_4 normalization"                    | yes (via #1/#2 result set) | confirms `(W₂,W₃,W₄)` parametrisation is folklore-standard | covered by the arXiv/Wikipedia hits |
| 10 | recent arXiv (last 5y)           | "recurrence relation for elliptic divisibility sequences"             | yes  | arXiv 2102.07573 — same normalisation conventions                 | no newer/more-general form of the *value* `W₄` |

### Literature summary (Phase 3)

Concept identified as: **the fourth initial value `W₄` of a normalised elliptic divisibility sequence** (Ward; division-polynomial `ψ₄`).
Sources agree on the standard form: **yes** — a normalised EDS is fixed by `W₁ = 1` and the triple `(W₂, W₃, W₄)`; mathlib parametrises this triple as `(b, c, d·b)`, i.e. `W₂ = b`, `W₃ = c`, `W₄ = d·b`. The lemma is the trivial read-off of `W₄`.
Most general standard form: the value `W₄` is a *defining datum*; there is no "more general" mathematical statement of "what `W₄` is" — it is a definitional fact about a specific construction.
Generality dimensions where the literature varies: the literature works over `ℤ` (integer EDS) or a field; mathlib already states this over an **arbitrary `CommRing R`**, which is *more* general than the classical integer/field setting. No further generalisation is available.
Disagreement with the literature: none. mathlib's `d·b` parametrisation is a deliberate convention (the factor of `b` from the even index) documented in the module's Implementation-notes and matching Ward.

---

### Generality analysis — `normEDS_four`

Literature-standard form (from Phase 3): `W₄` is a defining value of the
normalised EDS; classically stated over `ℤ` or a field.

| # | Parameter / hypothesis | Current Lean form          | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|----------------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | arbitrary commutative ring | `ℤ` or a field           | NO                  | Already strictly *more* general than the literature; `CommRing` is the natural home for `normEDS` (built from `preNormEDS` over any `CommRing`). Cannot weaken below `CommRing` — the EDS recurrence needs subtraction and multiplication. |
| 2 | `(b c d : R)`          | three free ring elements   | three free parameters    | NO                  | These are the defining parameters; nothing to weaken. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (indeed more general than the classical literature, which uses `ℤ`/fields).
Number of weakening opportunities found: 0.
Cost of restatement: n/a — nothing to restate.

### Modern-idiom check (Phase 4c)

| #  | Question                                                            | Applies? | Proposed reformulation | Downstream |
|----|--------------------------------------------------------------------|----------|------------------------|------------|
|  1 | "let X be a foo" → typeclass/instance?                             | no       | — `b c d` are data, not structure | — |
|  2 | sequences/metric → filters/topological?                           | no       | — purely algebraic identity over a `ℤ`-index | — |
|  3 | construct object → universal-property class?                      | no       | — `W₄` is a value, not a constructed object with a UP | — |
|  4 | set-with-closure-predicate → bundled substructure?                | no       | — not a substructure | — |
|  5 | vector-space/field-specific → weaken typeclass?                   | no       | — already over `CommRing`, maximally weak | — |
|  6 | 1-categorical → higher-categorical?                               | no       | — not categorical | — |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                    | no       | — index is `ℤ`; EDS theory is intrinsically `ℤ`-indexed; this is the value at the literal index `4` | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a definitional value-lemma in an already
maximally-general (`CommRing`, `ℤ`-indexed) form that mathlib itself ships. There
is no contemporary reformulation to make.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equalities or
typeclass-search paths).

---

### Mathlib search-status: `normEDS_four`

[A] Lean-Finder       "normalised EDS fourth term value"                — superseded by the direct source hit below
[B] Loogle            `normEDS _ _ _ 4 = _ * _`                          — superseded by the direct source hit below
[C] LeanSearch        "value of normalized elliptic divisibility sequence at 4" — superseded by the direct source hit
[D] Grep mathlib src  `grep -nE "normEDS_four" .lake/packages/mathlib/...`  — **HIT**
[E] Name pattern      `normEDS_four` over `.lake/packages/mathlib/Mathlib/` — **HIT** (1 def + 1 downstream use)

Direct grep result (decisive):
- `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:313-315`:
  ```lean
  @[simp]
  lemma normEDS_four : normEDS b c d 4 = d * b := by
    simp [normEDS, show ¬Odd (4 : ℤ) by decide]
  ```
  — **identical** statement, identical `@[simp]`, identical proof, identical
  `variable (b c d : R)` / `[CommRing R]` context (both in a top-level
  `section NormEDS`, so both have qualified name `normEDS_four`).
- `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:424`:
  `normEDS_four ..` — mathlib's own downstream use, mirrored verbatim by the
  project at `DivisionPolynomial.lean:347` (`normEDS_four ..`).

Searched for both forms (current and literature-standard): identical; mathlib's is
already over `CommRing` (the most general form).

Concluded: **found in mathlib as `normEDS_four`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:314`); identical form.**
Mathlib version pinned at rev `09b373db6e24` in this repo's `lakefile.toml`.

---

### Call sites — `normEDS_four`

Internal use count: **3** distinct external sites within the NagellLutz tree
(excluding the declaring file's own line 918), plus 1 in a separate HasseWeil fork
of the same upstream file — all of which are *forked* mirrors of mathlib usages:

| Caller file:line | Usage pattern (one-line excerpt) |
|---|---|
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1236` | `simp only [normEDS_one, normEDS_two, normEDS_three, normEDS_four]` |
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1275` | `... (by rw [h₂₄, h₁₂, normEDS_four]; ring)⟩` |
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:347` | `normEDS_four ..`  (mirror of mathlib `DivisionPolynomial/Basic.lean:424`) |
| `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:711` | `simp only [normEDS_one, normEDS_two, normEDS_three, normEDS_four]` (a *separate* fork of the same mathlib file in another project) |

Inline-derivation grep: (none — every site uses the named lemma; HasseWeil keeps its
own forked copy of the whole file rather than re-deriving).

Signal: K ≥ 3 internal uses, no inline re-derivation. But this is a **forked mathlib
lemma**, so the call-site signal is inherited wholesale from mathlib — it argues for
keeping the *mathlib* lemma, not for adding the local copy.

---

### Composition check (Phase 6)

Can `normEDS_four` be derived from mathlib in ≤3 chained calls?

Attempt 1: it *is* a mathlib lemma — `exact normEDS_four` (once the local copy is
removed and mathlib's `normEDS` is in scope).
  - Mathlib decls used: `normEDS_four` itself.
  - Result: succeeds trivially — identity, not a composition.

Conclusion: the question is moot — mathlib **has** the exact lemma (Phase 5), so this
is `NO-mathlib-has-it`, not `NO-composable-from-mathlib`. (For completeness: even from
scratch it is the one-liner `by simp [normEDS, show ¬Odd (4 : ℤ) by decide]`, mathlib's
own proof.)

---

## Verdict: `normEDS_four`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): `W₄` is a standard defining value of a normalised EDS (Ward; `ψ₄`); WebSearch #1/#2 even surface mathlib's own EDS/DivisionPolynomial docs.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — already over `CommRing`, more general than the classical `ℤ`/field literature; no modern-idiom move.
- Mathlib search (Phase 5): **found in mathlib as `normEDS_four`** at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:314`; *identical* statement, `@[simp]`, and proof.
- Composition check (Phase 6): moot — mathlib has the exact lemma.

**Rationale:**

The NagellLutz project file `EllipticDivisibilitySequence.lean` is a near-verbatim
**fork** of `Mathlib.NumberTheory.EllipticDivisibilitySequence` (identical
copyright/author header — David Kurniadi Angdinata, 2024 — identical module docstring,
identical `section NormEDS`, identical `normEDS`/`preNormEDS` API). The declaration
`normEDS_four` is reproduced **character-for-character** from mathlib: same `@[simp]`
attribute, same statement `normEDS b c d 4 = d * b`, same proof
`by simp [normEDS, show ¬Odd (4 : ℤ) by decide]`, same `variable (b c d : R)` with
`[CommRing R]`, same (empty) namespace so the same qualified name. There is nothing to
add, generalise, or compose: mathlib already ships this exact lemma at the most general
reasonable typeclass (`CommRing`, strictly more general than the classical
integer/field setting of Ward and the references).

This is a textbook `NO-mathlib-has-it`. The project keeps a local fork (so the local
`normEDS_four` currently shadows mathlib's via the re-`open EllSequence` and the
`section`-level redefinition of `normEDS`), but the cleanup action is to drop the fork
and depend on mathlib's `normEDS` API directly.

**WHY not (refactor-actionable):**
Mathlib already has `normEDS_four`, verbatim, at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:314`. The project's
`normEDS_four` is identical and adds zero new content. The local copy exists only
because the *entire* `normEDS` construction was forked into the project (the file
re-derives `preNormEDS`, `normEDS`, `complEDS`, etc.). So the refactor is not "replace
one lemma" but "delete the fork of the upstream `normEDS` API and import mathlib's", at
which point `normEDS_four` (and its siblings `normEDS_one/two/three`) resolve to the
mathlib lemmas with no call-site edits.

Existing mathlib decl:        `normEDS_four`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:314`
Our form follows in ≤1 line:
```lean
example {R : Type*} [CommRing R] (b c d : R) : normEDS b c d 4 = d * b := normEDS_four ..
```
Call sites in our project (from Phase 6.0): 3 (+1 in a separate HasseWeil fork of the same file).
Refactor plan: at the local-fork level, delete the project's re-definition of the
`normEDS` block (incl. `normEDS_four`) and use mathlib's
`Mathlib.NumberTheory.EllipticDivisibilitySequence`. The four call sites
(`EllipticDivisibilitySequence.lean:1236`, `:1275`, `DivisionPolynomial.lean:347`, and
`HasseWeil/.../EllipticDivisibilitySequence.lean:711`) use `normEDS_four` identically
to mathlib (line 1275's `rw [..., normEDS_four]` and `DivisionPolynomial.lean:347`'s
`normEDS_four ..` mirror mathlib `DivisionPolynomial/Basic.lean:424` exactly), so **no
argument-order changes are needed** — the names bind to the upstream lemma unchanged.
NB: this dedup is a *project/consolidation* task (the whole forked EDS file is the
unit), not a mathlib PR.
Next action: **delete the forked `normEDS` API (including `normEDS_four`) from the
NagellLutz project and depend on mathlib's; the 4 call sites are source-compatible.**

---

## Next step

Delete `normEDS_four` (with the rest of the forked `normEDS` block) from the NagellLutz
project and depend on `Mathlib.NumberTheory.EllipticDivisibilitySequence`. The 3
in-project call sites (plus the HasseWeil fork's) use the lemma identically to mathlib,
so no call-site argument changes are required. Track as a consolidation/dedup ticket,
not a mathlib PR.
