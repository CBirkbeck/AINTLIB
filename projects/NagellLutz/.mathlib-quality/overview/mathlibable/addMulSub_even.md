# /mathlibable report — `EllSequence.addMulSub_even`

## Verdict: **NO-composable-from-mathlib**

One-line rationale: an unfolding lemma for the project-local helper `addMulSub`
(absent from mathlib); once `addMulSub` is unfolded it is a ≤3-call computation.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); decl elaborates in the committed file
- decl `EllSequence.addMulSub_even`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:173`
- qualified name:           `EllSequence.addMulSub_even` (inside `namespace EllSequence`, line 90 … `end EllSequence`, line 597) — VERIFIED
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences" — defines EDS, `preNormEDS`/`normEDS`, and a new `addMulSub`/`rel₄`/`net` (Stange elliptic-net) relation layer. This file is a **fork** of `Mathlib.NumberTheory.EllipticDivisibilitySequence`, extended with the elliptic-net machinery not yet upstream.

---

### Statement (Phase 1)

`EllSequence.addMulSub_even` states: for `W : ℤ → R` (R a commutative ring) and
integers `m, n`,

> `addMulSub W (2·m) (2·n) = W (m + n) · W (m − n)`.

Here `addMulSub` is a **project-local definition** (same file, line 94):

```lean
def addMulSub (m n : ℤ) : R := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)
```

i.e. the two-term product `W((m+n)/2)·W((m−n)/2)` using **truncated** integer
division by 2 (chosen so `(-k).tdiv 2 = -(k.tdiv 2)`, making sign/`neg`/`abs`
lemmas hold unconditionally). It is intended for arguments of the **same
parity**, and is the basic building block of the four-index relation `rel₄` and
Stange's net relation `net` (lines 103, 115). The lemma `addMulSub_even` is the
unfolding fact that on **even** arguments `2m, 2n` the truncated halvings cancel
exactly, recovering the standard EDS product `W(m+n)·W(m−n)`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (mathematical role: ring the sequence lands in).
- `(W : ℤ → R)` — the sequence (an EDS / elliptic net, though the lemma needs no EDS hypothesis).
- `(m n : ℤ)` — the (to-be-doubled) indices.

Hypotheses: none.

Conclusion (math): doubling both index-arguments of the halved-product building
block yields the ordinary two-term product `W(m+n)·W(m−n)`.

Conclusion (Lean): `addMulSub W (2 * m) (2 * n) = W (m + n) * W (m - n)`.

Proof body (one line):
```lean
simp_rw [addMulSub, ← left_distrib, ← mul_sub_left_distrib, Int.mul_tdiv_cancel_left _ two_ne_zero]
```
The only mathlib lemma it consumes is `Int.mul_tdiv_cancel_left`; everything else
is `addMulSub`-unfolding + `left_distrib`/`mul_sub_left_distrib` arithmetic.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line helper lemma that unfolds a project-local auxiliary
definition (`addMulSub`) on even arguments. Not a named theorem, not a `## Main
statements` entry, not person/place-named. (Literature width still run
EXHAUSTIVE per protocol.)

### One-line check (Phase 2b)

Body line count: 1 substantive line.
One-liner verdict: n/a — kind is `lemma`, not `def`. (The Phase-2b def
exemptions concern one-line *definitions*; this is a lemma, so the check is
informational only.) Recorded: this is a single-`simp_rw` unfolding lemma.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "elliptic divisibility sequence W(m+n) W(m-n) product identity even indices" | partial | `W(m+n)W(m−n)` appears only as the **LHS of the Ward recurrence** `W(m+n)W(m−n)W(r)² = W(m+r)W(m−r)W(n)² − W(n+r)W(n−r)W(m)²` | The *product* is standard; an `addMulSub`-style halved-argument building block is not mentioned. |
| 2 | WebSearch (general form / Stange) | "Stange elliptic nets four-index relation addMulSub building block W((m+n)/2) W((m-n)/2)" | no | Stange's net recurrence is `W(p+q+s)W(p−q)W(r+s)W(r) + …(cyc)… = 0` (four-term, four-index) | No source uses a 2-term `W((m+n)/2)·W((m−n)/2)` named block; the `addMulSub`/`rel₄` packaging is the formalization's own. |
| 3 | WebSearch (named-after / aliases) | "nLab elliptic divisibility sequence Ward recurrence … two-term product W(m+n)W(m-n) standard name" | partial | Confirmed the identity `ψ_{m+n}ψ_{m−n} = ψ_{m+1}ψ_{m−1}ψ_n² − ψ_{n+1}ψ_{n−1}ψ_m²` is the **Ward recurrence**; division-polynomial form in Silverman | The product `ψ_{m+n}ψ_{m−n}` is standard; "reduce halved-arg product to it on even args" is not a named result anywhere. |
| 4 | ChatGPT MCP | (self-contained query: is `addMulSub` a named object; is `addMulSub_even` a named theorem?) | n/a | — | **MCP unavailable** (Codex backend errored — matches the task's "ChatGPT MCP may be down"). Fell back to WebSearch + domain reasoning per skill fallback. |
| 5 | Local references | grep `projects/NagellLutz/.mathlib-quality/references/` | n/a | — | Directory **absent** for this project — recorded n/a. |
| 6 | nLab | "elliptic divisibility sequence" / "Ward recurrence" | partial | nLab has no dedicated EDS page with an `addMulSub`-style block; folded into the WebSearch #3 result | Not a categorical concept; no abstract `addMulSub` notion. |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept (a concrete integer-indexed ring-valued identity). |
| 8 | Stacks Project (alg geom) | — | n/a | — | EDS/division-polynomial recurrences are not in Stacks; not the right venue. |
| 9 | MathOverflow / Math.SE | EDS halved-argument product / Stange net building block | no | — | No discussion of a named `W((m±n)/2)` building block; only the standard recurrence/divisibility discussions surface. |
| 10 | recent arXiv (≤5 yrs) | "elliptic net algorithm" / "division polynomials for arbitrary isogenies" (Stange 2025), "explicit valuation of elliptic nets" (2025) | partial | Modern elliptic-net algorithm papers use *blocks of consecutive terms* `W(i,0)`, `W(i,1)` for pairing computation — different bookkeeping; **none** define `addMulSub` | Confirms the 2-term halved-argument block is a Lean-formalization convenience, not a community object. |

### Literature summary (Phase 3)

Concept identified as: there is **no named literature concept** for `addMulSub`
(the halved-argument two-term product `W((m+n)/2)·W((m−n)/2)` indexed by the
un-halved arguments). The *underlying* product `W(m+n)·W(m−n)` is standard — it
is the left-hand side of the **Ward recurrence** for EDS / division polynomials
(Ward 1948; Silverman; Stange).
Sources agree on the standard form: yes for the Ward recurrence; the `addMulSub`
building block has **no** standard form because it is not a literature object.
Most general standard form (of the *product*): `W(m+n)·W(m−n)` over any
commutative ring, no constraint — but that is not what this lemma is *about*;
this lemma is about the **definitional reduction** of `addMulSub` to that
product on even arguments.
Generality dimensions where the literature varies: none relevant — the lemma is
a definitional unfolding, parametric over an arbitrary `CommRing R` and arbitrary
`W : ℤ → R` already (no EDS hypothesis used), i.e. already at maximal coefficient
generality for what it says.
Disagreement with the literature: none — but the literature has **no** object to
agree/disagree with. The empty-concept result is itself the signal (per the
verdicts reference: literature absence of the *concept* ⇒ this is a
formalization-internal helper, not a mathlib-shaped standalone result).

---

### Generality analysis — `EllSequence.addMulSub_even`

Literature-standard form (from Phase 3): n/a — the lemma is the unfolding of a
project-local definition; there is no literature "standard form" for the
statement (only for the product on its RHS).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]` | commutative ring | n/a (not a literature statement) | NO | The RHS `W(m+n)·W(m−n)` is a ring product; commutative not even essential, but `addMulSub` is defined in the `CommRing R` section — weakening the typeclass is meaningless for an unfolding lemma that lives with its def. |
| 2 | `(W : ℤ → R)` | arbitrary sequence | n/a | already max | No EDS/divisibility/oddness hypothesis is used — already the weakest possible (any function `ℤ → R`). |
| 3 | `(m n : ℤ)` even-doubled args | `2*m, 2*n` | n/a | NO | The "even" specialisation **is the content** of the lemma (companion `addMulSub_odd` handles the odd case). Generalising the index away would delete the lemma. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (vacuously — it is an unfolding lemma
with no unused hypotheses; coefficient generality is already an arbitrary
`CommRing` and arbitrary `W`).
Number of weakening opportunities found: 0.
Proposed restatement: none — there is nothing to generalise; the lemma exists
solely to unfold `addMulSub` on even arguments.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" → typeclass/instance? | no | — | No bundled hypotheses; the lemma already takes a bare `W`. |
| 2 | sequences/metric → filters/topology? | no | — | Finite algebraic identity over ℤ; no analysis/topology present. |
| 3 | construction → universal-property class? | no | — | It is an equation between ring elements, not a construction. |
| 4 | set-with-closure → bundled substructure? | no | — | No subset/closure predicate involved. |
| 5 | vector-space/field-specific → module/(semi)ring? | no | — | Already over an arbitrary `CommRing`; the statement does not even need invertibility. |
| 6 | 1-categorical → higher-categorical? | no | — | Not categorical. |
| 7 | concrete index ℕ/ℤ/ℝ → arbitrary group/monoid? | no | — | The index is intrinsically `ℤ` with halving by 2; this *is* the EDS index ring. Generalising the index is not meaningful for this helper. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: this is a definitional-unfolding lemma for a bespoke
formalization helper (`addMulSub`); there is no classical-vs-modern formulation
question — the only "form" is "unfold the def on even arguments".

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is **lemma** (no definitional equalities or
typeclass-search paths introduced). Skipped.

---

### Mathlib search-status: `EllSequence.addMulSub_even`

[A] Lean-Finder       (index tool not surfaced in this env)                 n/a: tool unavailable; substituted with authoritative grep [D] over the actual mathlib source tree present at `.lake/packages/mathlib/`.
[B] Loogle            (index tool not surfaced in this env)                 n/a: same as [A].
[C] LeanSearch        (index tool not surfaced in this env)                 n/a: same as [A].
[D] Grep mathlib src  `addMulSub` across all of `Mathlib/`                  **no hits** — `grep -rln "addMulSub" .lake/packages/mathlib/Mathlib/` returns nothing. The concept does not exist in mathlib at all.
[D'] Grep mathlib src  upstream `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines) for `addMulSub` / the bare identity | **no** | Upstream uses a different design (`preNormEDS'`, `normEDS`, …); `W(m+n)·W(m−n)` appears only inside the `IsEllSequence` Ward recurrence (lines 83–84), never as a standalone reduction. No `addMulSub` / `rel₄` / `net`. |
[D''] Grep mathlib src  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` for `tdiv`/halving helper | **no** | No truncated-div-by-2 halving building block in the division-polynomial files either. |
[E] Name pattern      grep for `addMulSub`, `_even` halving lemmas in mathlib | no hits | — |

Searched for both:
  - the user's current form (`addMulSub W (2m) (2n) = W(m+n)·W(m−n)`) — not in mathlib (the `addMulSub` symbol is absent);
  - the literature-standard form (the Ward-recurrence product `W(m+n)·W(m−n)`) — present **only** as part of `IsEllSequence`'s recurrence, never as this reduction lemma.

Concluded: **not in mathlib** (the local mathlib tree was grepped directly;
`addMulSub` occurs nowhere in `Mathlib/`, and no analogous halved-argument
reduction lemma exists). The declaration is about a definition that has not been
upstreamed.

---

### Call sites — `EllSequence.addMulSub_even`

Internal use count: **1** (within the NagellLutz project, excluding the declaring file).
External-to-file callers: 1 distinct file (the *same* file's later proof; the other matches are duplicate copies — see note).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:310` | `simp_rw [addMulSub_even, add_zero, sub_zero]` (inside the `addMulSub`/`rel₄` machinery, deriving a `rel₄`/`net` consequence) |

Duplicate-copy matches (NOT independent consumers):
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:165,296` — a **backup/original copy** of the very same file (re-declares + re-uses `addMulSub_even` identically).
- `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:100,154` — a **separate project's own duplicated fork** of the same EDS file (re-declares the lemma locally; does not import this one). These confirm the helper is part of a duplicated `addMulSub` track, not a shared public API consumed across projects.

Inline-derivation grep (was the equivalent re-derived elsewhere without using `addMulSub_even`?):
  - (none) — every occurrence goes through the named lemma; but each occurrence is inside a copy of the same `addMulSub` framework.

Call-sites signal: **K = 1 genuine internal use**, all inside the `addMulSub`
machinery of the same file. Per the verdicts reference ("K = 1 internal use only
→ possibly the wrong abstraction; could be inlined; lean toward NO-composable"),
this reinforces NO-composable: the lemma is a private unfolding step of the
`addMulSub`/`rel₄`/`net` development, not a reusable public result.

---

### Composition check (Phase 6)

Can `EllSequence.addMulSub_even` be derived from mathlib in ≤3 chained calls?

The lemma is *about a project-local definition* `addMulSub`, so "compose from
mathlib" means: after unfolding `addMulSub` (which is the project's own def, not
mathlib), is the residual identity a ≤3-call mathlib computation?

Attempt 1 (the actual proof, verbatim):
```lean
simp_rw [addMulSub, ← left_distrib, ← mul_sub_left_distrib, Int.mul_tdiv_cancel_left _ two_ne_zero]
```
  - Mathlib decls used: `Int.mul_tdiv_cancel_left` (the one substantive mathlib
    lemma), plus the ring rewrites `left_distrib`, `mul_sub_left_distrib`
    (`2*m + 2*n = 2*(m+n)` and `2*m − 2*n = 2*(m−n)`, then cancel the `tdiv 2`).
  - Result: **succeeds** — a single `simp_rw` with the def-unfold + one mathlib
    cancellation lemma. This is a 1-to-2-call composition once `addMulSub` is
    unfolded.
  - Notes: the only project-specific ingredient is `addMulSub` itself
    (`unfold addMulSub` / `simp [addMulSub]`); the arithmetic core is pure
    mathlib.

Conclusion: **COMPOSABLE** (relative to the `addMulSub` def). The identity is
`simp [addMulSub, Int.mul_tdiv_cancel_left]`-closable — a definitional unfolding,
not a theorem requiring new content.

---

## Verdict: `EllSequence.addMulSub_even`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the *product* `W(m+n)·W(m−n)` is the standard Ward-recurrence LHS, but `addMulSub` (the halved-argument building block) is **not a named literature object** in any channel (Ward / Stange / Silverman / arXiv / nLab / MO). The statement "halved-arg product reduces to `W(m+n)W(m−n)` on even args" is a definitional unfolding, named nowhere.
- Generality analysis (Phase 4): MAXIMALLY GENERAL vacuously (0 weakenings); no modern-idiom reformulation (Phase 4c all "no").
- Mathlib search (Phase 5): **not in mathlib** — `addMulSub` occurs nowhere in `Mathlib/`; upstream `EllipticDivisibilitySequence.lean` uses an entirely different design and has no analogous reduction lemma.
- Composition check (Phase 6): **COMPOSABLE** — the proof is one `simp_rw` unfolding `addMulSub` plus the single mathlib lemma `Int.mul_tdiv_cancel_left`.

**Rationale (1–2 paragraphs):**

`addMulSub_even` is not a mathematical theorem in its own right; it is the
unfolding lemma that says the project's bespoke helper
`addMulSub W m n := W((m+n).tdiv 2)·W((m−n).tdiv 2)` collapses to the ordinary
EDS product `W(m+n)·W(m−n)` when its arguments are even. The `addMulSub` /
`rel₄` / `net` layer is a **Lean-formalization convenience** (Angdinata's
elliptic-net development, a fork-extension of
`Mathlib.NumberTheory.EllipticDivisibilitySequence`) for expressing Stange's
four-index relation uniformly across parities; it is **not** an object in the
EDS / elliptic-net literature, where the analogous content is just the Ward
recurrence. Because mathlib does not contain `addMulSub` at all, this lemma
cannot be shipped to mathlib as a standalone result — and it should not be: it
is internal API glue whose fate is bound to that of the `addMulSub` definition.
Whether *that definition* belongs upstream is a separate, larger question (the
whole `addMulSub`/`rel₄`/`net` elliptic-net framework would be assessed as one
unit, def-first); this individual unfolding lemma is not the grain at which the
mathlib decision is made.

Operationally, the lemma is COMPOSABLE: its proof is a single `simp_rw`
unfolding `addMulSub` together with exactly one mathlib lemma,
`Int.mul_tdiv_cancel_left`. Its sole genuine call site (1 internal use, inside
the same file's machinery) could inline `simp [addMulSub, Int.mul_tdiv_cancel_left]`
directly. The other repository matches are duplicate copies of the same forked
file (`…Original.lean`) and HasseWeil's independent fork — duplication of the
helper track, not independent consumers, which only strengthens "internal glue,
not public API". Per the verdicts reference, literature-absence-of-the-concept
plus a ≤3-call mathlib composition plus K = 1 use is the NO-composable profile.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; the user's form is a 1-call (post-unfold)
composition. Building blocks:
- `addMulSub` — the project's own definition (the thing being unfolded; *not*
  mathlib, and not upstreamed).
- `Int.mul_tdiv_cancel_left` (`Mathlib/Data/Int/...`, the `Init.Data.Int.DivMod`
  / mathlib `Int` API) — `2 * k` truncated-divided by `2` is `k`.
- ring rewrites `left_distrib`, `mul_sub_left_distrib` (core/mathlib).

Composition sketch (≤3 lines, the existing proof):
```lean
example (W : ℤ → R) (m n : ℤ) :
    EllSequence.addMulSub W (2 * m) (2 * n) = W (m + n) * W (m - n) := by
  simp_rw [EllSequence.addMulSub, ← left_distrib, ← mul_sub_left_distrib,
    Int.mul_tdiv_cancel_left _ two_ne_zero]
```

Call sites in the project (from Phase 6.0): **K = 1** genuine
(`EllipticDivisibilitySequence.lean:310`).

Refactor plan (mathlib-direction only — see the important caveat below):
- This lemma should **stay in the project**. It is correct, useful internal
  API for the `addMulSub`/`rel₄`/`net` development, and inlining its one use as
  `simp [addMulSub, Int.mul_tdiv_cancel_left]` would *reduce* readability of the
  net-relation proofs, not improve it. The NO-composable verdict means only
  that **it is not a standalone mathlib contribution** — not that it is bad
  project code.
- If/when the `addMulSub`/`rel₄`/`net` *framework* is considered for upstreaming
  (the proper unit of that decision), `addMulSub_even` rides along **with** the
  `addMulSub` def and its siblings (`addMulSub_odd`, `addMulSub_same`,
  `addMulSub_neg₀/₁`, `addMulSub_abs₀/₁`, `addMulSub_swap`,
  `addMulSub_mem_nonZeroDivisors`, `addMulSub₄`, …) as one coherent API — it is
  not separable from them.

Next action: **keep `addMulSub_even` in the project as internal API.** Do not
PR it as a standalone lemma. Treat it as part of the `addMulSub`/`rel₄`/`net`
elliptic-net layer, whose upstreaming (if pursued) is a separate, framework-level
`/mathlibable` evaluation run **def-first** over `EllSequence.addMulSub` and the
whole net-relation development.

---

## Next step

Keep `addMulSub_even` as project-internal API for the `addMulSub`/`rel₄`/`net`
development. It is **not** a standalone mathlib contribution (NO-composable: a
one-`simp_rw` unfolding of a project-local def whose only substantive mathlib
ingredient is `Int.mul_tdiv_cancel_left`). The mathlib question is correctly
asked of the *whole `addMulSub` elliptic-net framework as one unit*, def-first —
not of this individual unfolding lemma.
