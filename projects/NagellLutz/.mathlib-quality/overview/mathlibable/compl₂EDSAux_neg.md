# /mathlibable report — `compl₂EDSAux_neg`

Project: NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; EDS).
Declaration: `compl₂EDSAux_neg`
Location: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1036`
Assessed: Step-9 /overview mathlibable, single-decl manual run (lean index MCP unavailable; reasoned from source + local mathlib grep + WebSearch).

---

## Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — statement + proof read verbatim).
- decl `compl₂EDSAux_neg`:  ✓ resolved at `EllipticDivisibilitySequence.lean:1036`.
- qualified name:           **`compl₂EDSAux_neg`** (ROOT namespace). The enclosing `namespace EllSequence` closes at line 597; `IsEllSequence` 643–702; `PreNormEDS` section 704–879. Line 1036 sits inside `section Complement` (1011) and the file-level `@[expose] public section` only — neither prefixes the name. VERIFIED: parsed name is correct, no namespace prefix.
- kind:                     `lemma` (theorem-like; Phase 4.5 diamond check n/a).
- has sorry:                no.
- module docstring summary: "Elliptic divisibility sequences (EDS) and construction of normalised EDSs from initial terms" — a project FORK/extension of `Mathlib.NumberTheory.EllipticDivisibilitySequence` (same author, David Kurniadi Angdinata; same Apache header).

---

## Statement (Phase 1)

`compl₂EDSAux_neg` states the negation-reflection identity for an auxiliary expression `compl₂EDSAux` attached to a normalised elliptic divisibility sequence:

> For a commutative ring `R`, fixed `b c d : R`, and `m : ℤ`,
> `compl₂EDSAux b c d (-m) = -compl₂EDS b c d m - compl₂EDSAux b c d m`.

Here (lines 1017–1018, 1032–1034):
- `compl₂EDSAux b c d m := preNormEDS (b^4) c d (m-2) * preNormEDS (b^4) c d (m+1)^2 * (if Even m then 1 else b)`
  — i.e. the **single second product term** (sign dropped) of the 2-complement difference.
- `compl₂EDS b c d m := (p(m-1)^2 * p(m+2) − p(m-2) * p(m+1)^2) * (if Even m then 1 else b)`, with `p = preNormEDS (b^4) c d`
  — the **standard 2-complement** witnessing `W(m) ∣ W(2m)` (identical to mathlib's `complEDS₂`).

Variables / typeclasses: `R` a `CommRing`; `b c d : R`; `m : ℤ`.
Hypotheses: none.
Conclusion (math): the auxiliary half-complement at `-m` equals minus the full complement minus the auxiliary at `m`.
Conclusion (Lean): the displayed equation in `R`.

Proof body (verbatim): `simp_rw [compl₂EDSAux, compl₂EDS, neg_sub_left, neg_add_eq_sub, ← neg_sub m, preNormEDS_neg, even_neg]; ring`. → unfold both defs, push the negation through `preNormEDS_neg` + `even_neg`, close by `ring`. Pure mechanical negation-symmetry bookkeeping.

---

## Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a helper `_neg` symmetry lemma about a one-line auxiliary `def`; not a named theorem, not a `## Main statement`, introduces no new structure. (Literature width run EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner exemption table n/a. Note for context: the *parent object* `compl₂EDSAux` IS a one-line `def` (line 1017–1018); its own mathlibability is the governing question (see Phase 6/7). `compl₂EDSAux_neg` is the symmetry API that accompanies that def.

---

## Literature search table — EXHAUSTIVE protocol

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "elliptic divisibility sequence omega division polynomial second coordinate Jacobian Stange" | yes | EDS / division polynomials `ψ,φ,ω`; `[n](x,y)=(φ_n/ψ_n², ω_n/ψ_n³)` | Stange eprint 2025/521; Wikipedia EDS; arXiv 2102.07573. `ω` is the standard name for the Y-coordinate numerator. |
| 2 | WebSearch (general form / negation) | "division polynomial psi omega phi elliptic curve recurrence negation W(-n) = -W(n)" | yes | `ψ_{-n} = -ψ_n` (odd); `φ_{-n}=φ_n`, `ω` even-type symmetry | Sutherland MIT 18.783 Lec 5; the **negation symmetries of division polynomials are standard textbook facts**. |
| 3 | WebSearch (named-after / mathlib aliases) | "\"elliptic divisibility sequence\" complement W(2n)/W(n) auxiliary normalised recurrence Lean mathlib" | yes | mathlib `complEDS₂`, `preNormEDS`; arXiv 2604.05280 "On Elliptic Sequences over Commutative Rings" | The arXiv paper is THIS project's own upstreaming writeup. Mathlib doc confirms aux sequences exist "to allow the definition of univariate n-division polynomials … omitting a factor of the bivariate 2-division polynomial" — exactly `compl₂EDSAux`'s purpose. |
| 4 | ChatGPT MCP | self-contained: is `compl₂EDSAux` a named object; is the `_neg` identity standard; general-file vs specific-file | n/a | — | Codex MCP down (as flagged in task env); fell back to channels 1–3 + grep. Recorded as attempted-but-unavailable. |
| 5 | Local references | (no `.mathlib-quality/references/` PDFs found for this decl) | n/a | — | dir not populated for NagellLutz; recorded n/a. |
| 6 | nLab | "elliptic divisibility sequence" / "division polynomial" | no | — | nLab has no dedicated EDS/division-polynomial page at this granularity; not a category-theoretic object. |
| 7 | nCatLab | (categorical?) | n/a | — | not a categorical concept. |
| 8 | Stacks Project | division polynomial / EDS | n/a | — | Stacks does not cover elliptic-curve division polynomials at this level. |
| 9 | MathOverflow / MSE | division polynomial negation symmetry generality | yes (subsumed) | `ψ_{-n}=-ψ_n` etc. confirmed standard | same facts as #2; no separate "half-complement aux" object appears anywhere. |
| 10 | recent arXiv (≤5y) | Stange 2503.15428 / 2025-521 "Division polynomials for arbitrary isogenies"; arXiv 2604.05280 | yes | confirms `ψ/φ/ω` framework + recurrences | none of these name a "second-product-term-only" auxiliary; it is an implementation device, not a literature object. |

### Literature summary (Phase 3)

Concept identified as: the **negation/reflection symmetry of an auxiliary term in the normalised-EDS / division-polynomial recurrence**, in service of the `ωₙ` (Y-coordinate) division polynomial.
Sources agree on the standard form: yes — for the *named* objects (`ψ,φ,ω`, the 2-complement). The negation symmetries (`ψ_{-n}=-ψ_n`, `φ_{-n}=φ_n`, complement even) are **standard, ubiquitous textbook facts**.
Most general standard form: division polynomials over any base ring; the symmetries hold over an arbitrary `CommRing` (which is exactly the generality used here and in mathlib).
Generality dimensions where the literature varies: base ring (ℤ classically → arbitrary `CommRing` in modern mathlib; the decl is already at the maximal `CommRing` generality).
Disagreement with the literature: **`compl₂EDSAux` itself is NOT a named literature object.** It is a bespoke decomposition — the single product term `p(m-2)·p(m+1)²·(unit)`, one half of the 2-complement difference `compl₂EDS` — introduced *purely as an implementation device* so the `ω` polynomial can be written without a stray factor of the bivariate `ψ₂`. The mathlib doc note (channel 3) states this design rationale verbatim. The `_neg` identity is therefore not a "named result"; it is the mechanical symmetry bookkeeping for that device.

---

## Generality analysis — `compl₂EDSAux_neg`

Literature-standard form (from Phase 3): negation symmetry of EDS/division-polynomial auxiliaries, over an arbitrary commutative ring.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` (implicit on `b c d : R`) | arbitrary commutative ring | arbitrary commutative ring | NO | already maximal; matches mathlib's `complEDS₂_neg`, `normEDS_neg`, `preNormEDS_neg`, `preΨ_neg`, `Ψ_neg`, `Φ_neg`. `ring` + `preNormEDS_neg` need nothing weaker. |
| 2 | `m : ℤ` | integer index | integer index | NO | EDS/division polynomials are intrinsically ℤ-indexed; no monoid generalisation is meaningful. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it already sits at `CommRing` + ℤ-index, the same generality as the entire surrounding mathlib EDS/division-polynomial API).
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Notes |
|---|----------|----------|-------|
| 1 | bundled hyps → typeclasses? | no | already typeclass-driven (`CommRing`). |
| 2 | sequences/metric → filters/topology? | no | a purely algebraic integer-indexed identity; no analysis. |
| 3 | construction → universal property? | no | it's an equational symmetry lemma, not a construction. |
| 4 | set+closure-pred → bundled substructure? | no | n/a. |
| 5 | field/metric-specific → weaker typeclass? | no | already `CommRing` (maximal). |
| 6 | 1-categorical → higher-categorical? | no | n/a. |
| 7 | concrete index ℕ/ℤ/ℝ → general monoid? | no | division-polynomial recurrence is intrinsically ℤ-indexed; matches mathlib. |

Modern idiom available: **no**. The lemma is already stated in the exact idiom of the surrounding mathlib API (it is, definitionally, the missing sibling of `complEDS₂_neg`). One-line reason: there is no organisational improvement to make — the only question is *whether the underlying object belongs in mathlib at all*, not how to phrase it.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no new definitional equality / typeclass-search path introduced).

---

## Mathlib search-status: `compl₂EDSAux_neg`

[A] Lean-Finder       — n/a: lean-index MCP unavailable in this environment (per task). Compensated by Methods D/E over the actual pinned mathlib source.
[B] Loogle            — n/a: same reason. Type-pattern target would be `compl₂EDSAux _ _ _ (-_) = _`; the head symbol `compl₂EDSAux` provably does not exist in mathlib (Method D), so Loogle could only miss.
[C] LeanSearch        — n/a: same reason; substituted by WebSearch channels 1–3 hitting the mathlib4_docs pages directly.
[D] Grep mathlib src  — **DONE, decisive.** `grep -rln "compl₂EDSAux|complEDS₂Aux|complEDSAux"` over all of `.lake/packages/mathlib/Mathlib/` → **0 hits**. The auxiliary object is absent from mathlib entirely. Mathlib's `NumberTheory/EllipticDivisibilitySequence.lean` has the FULL 2-complement `complEDS₂` (def line 246) with `complEDS₂_neg` (line 272: `complEDS₂ b c d (-k) = complEDS₂ b c d k`), but NO "second-term-only" auxiliary and NO `compl₂EDSAux`-style `_neg` lemma.
[E] Name pattern      — **DONE.** `grep -E "(def|lemma|theorem) [A-Za-z0-9']*Aux"` over the mathlib EDS file and the whole `DivisionPolynomial/` dir → **0 `*Aux` decls.** Mathlib's analogous negation lemmas are `preNormEDS_neg`, `normEDS_neg`, `complEDS₂_neg`, `complEDS_neg`, `preΨ_neg`, `ΨSq_neg`, `Ψ_neg`, `Φ_neg`, `ψ_neg`, `φ_neg` — none about a half-complement auxiliary.

Searched for both:
- the user's current form (`compl₂EDSAux_neg`) — not in mathlib.
- the literature-standard / sibling form (`complEDS₂_neg`) — **IS in mathlib** (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:272`), but it is about a **different object** (the full complement `complEDS₂` = project's `compl₂EDS`, whose project sibling `compl₂EDS_neg` at line 1044 already duplicates it). It does **not** subsume `compl₂EDSAux_neg`, which is about the strictly-different auxiliary half-term.

**Critical adjacent finding.** Mathlib's `AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` lists the `ωₙ` family as an **explicit open TODO** — line 71 ("* TODO: the bivariate polynomials `ωₙ`.") under `## Main definitions`, and line 83 ("TODO: implementation notes for the definition of `ωₙ`."). The project's `compl₂EDSAux` exists precisely to **discharge that TODO**: it is the ingredient of `WeierstrassCurve.ω` in `DivisionPolynomialOmega.lean:74–78` (the Y-coordinate of `[n]` in Jacobian coordinates).

Concluded: **not in mathlib** (all available methods exhausted, plus the sibling-form search). The auxiliary object and its `_neg` helper are project-frontier work targeting mathlib's open `ωₙ` gap.

---

## Call sites — `compl₂EDSAux_neg`

Internal use count (of the LEMMA itself): **0** within the active project tree (grep `compl₂EDSAux_neg\b`, excluding the `_neg_one`/`_neg_two` simp lemmas, returns only its own definition site in the active file and one in the `…Original.lean` backup copy). No consumer currently calls `compl₂EDSAux_neg`.

But the **parent def `compl₂EDSAux`** is heavily used (17 refs in the declaring file; external callers):

| Caller file:line | Usage pattern |
|------------------|---------------|
| `LutzNagell/DivisionPolynomialOmega.lean:78` | `- compl₂EDSAux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + …` — **defines `WeierstrassCurve.ω`** (the ω TODO!) |
| `LutzNagell/DivisionPolynomialOmega.lean:112` | `… map_compl₂EDSAux …` — ω map-compatibility proof |
| `LutzNagell/ZSMul.lean:279` | `compl₂EDSAux_two` in the `smulY`/`ω` scalar-multiplication computation |
| `EllipticDivisibilitySequence.lean` (self) | `redInvarNum` (reduced-invariant numerator), `compl₂EDSAux_mul_b`, `map_compl₂EDSAux` |

Inline-derivation grep: the `_neg` identity is not re-derived inline elsewhere (no consumer needs it yet — the ω-track is even-symmetric via `compl₂EDS_neg`/`ψc_neg`, so the auxiliary's `_neg` is currently latent API).

What the pattern tells us: K=0 for the lemma is NOT "dead junk" — it is **completeness API** for a one-line auxiliary `def` that itself has K≥3 genuine uses driving an actual mathlib-TODO feature. By the skill's def-first / verdict-inheritance logic, the lemma's fate is **governed by the parent def's fate**, not by its own (currently-zero) call count.

---

## Composition check (Phase 6)

Can `compl₂EDSAux_neg` be derived from mathlib in ≤3 chained calls?

Attempt 1: rewrite via mathlib's `complEDS₂_neg` / `preNormEDS_neg`.
- Result: **fails at the head symbol.** The statement's LHS is `compl₂EDSAux b c d (-m)` — `compl₂EDSAux` is not a mathlib symbol, so there is no mathlib lemma to rewrite with and nothing to inline at a call site. The proof intrinsically unfolds `compl₂EDSAux` (a project def) before `preNormEDS_neg` can fire.

Conclusion: **NOT-COMPOSABLE.** Not because the math is deep (the proof is a 1-line `simp_rw … ; ring`), but because the lemma is *about a project-local definition that does not exist in mathlib*. You cannot compose, inline, or restate it without first adding `compl₂EDSAux` to mathlib. The lemma is therefore inseparable from its parent def — it is not standalone-refactorable, and it is not "already-in-mathlib".

---

## Verdict: `compl₂EDSAux_neg`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the negation symmetries of EDS/division-polynomial terms are standard textbook facts at `CommRing` generality; but `compl₂EDSAux` itself is an **unnamed implementation device** (a half-complement), not a literature object. The mathlib doc itself states the design rationale ("omitting a factor of the bivariate 2-division polynomial").
- Generality (Phase 4): MAXIMALLY GENERAL; no modern-idiom improvement — it is already the exact sibling-idiom of mathlib's `complEDS₂_neg`.
- Mathlib search (Phase 5): `compl₂EDSAux` and its `_neg` are absent from all of mathlib (Methods D+E, 0 hits). Mathlib HAS the full-complement sibling `complEDS₂_neg` but for a different object. **Mathlib has an OPEN, NAMED TODO for the `ωₙ` family** (`DivisionPolynomial/Basic.lean:71,83`) that this auxiliary exists to discharge.
- Composition (Phase 6): NOT-COMPOSABLE — the lemma is about a project def with no mathlib counterpart; it cannot be inlined or restated from mathlib primitives.

**Rationale.**
`compl₂EDSAux_neg` is a textbook-mechanical negation-symmetry lemma (`simp_rw [defs, preNormEDS_neg, even_neg]; ring`) and, taken in isolation, it is exactly the kind of `_neg` API that mathlib maintains in bulk (`preNormEDS_neg`, `normEDS_neg`, `complEDS₂_neg`, `preΨ_neg`, `Ψ_neg`, `Φ_neg`, `ψ_neg`, `φ_neg`). That alone would push toward YES. **But it is not a freestanding result:** it is the symmetry helper for the one-line auxiliary `def compl₂EDSAux`, which is itself bespoke scaffolding the project built to construct the `ω` division polynomial — the precise object mathlib flags as an open TODO. So the lemma is mathlibable *if and only if* `compl₂EDSAux` and the surrounding `WeierstrassCurve.ω` development are upstreamed to discharge mathlib's `ωₙ` gap.

That conditional is a genuine human/policy judgment the skill must not resolve unilaterally, for three reasons. (1) **Scope/grain:** the right unit of contribution is "the ω-division-polynomial track" (def `compl₂EDSAux` + its `_mul_b`, `map_*`, the `redInvarNum`/`ω` machinery), not this individual `_neg` helper; whether mathlib wants `compl₂EDSAux` as the *vehicle* for `ωₙ`, or a different decomposition, is a design call for a mathlib reviewer (mathlib's own `ωₙ` plan in `Basic.lean` may prescribe a different shape). (2) **Possible redundancy of the auxiliary:** mathlib already carries the full complement `complEDS₂`; whether the *half*-complement `compl₂EDSAux` earns its own name in mathlib, or should be inlined into the `ω` definition, is exactly the "is this one-liner worth a named def" judgment — and the lemma rides on that answer. (3) **Latent (K=0) consumer:** no current code calls `compl₂EDSAux_neg`; it is completeness API, so its inclusion is contingent on the def shipping, not on demonstrated demand. None of (1)–(3) is resolvable from search evidence alone.

**Numbered questions for the human:**
1. Is the project's `ω`-division-polynomial track (the `compl₂EDSAux` machinery culminating in `WeierstrassCurve.ω`) intended to be upstreamed to mathlib to discharge the open `ωₙ` TODO in `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` (lines 71, 83)? (yes/no)
2. If yes — should `compl₂EDSAux` be a *named* mathlib `def` (in which case `compl₂EDSAux_neg` ships with it as standard `_neg` API), or should the half-complement be inlined into the `ω` definition (in which case this lemma disappears)?
3. Should the mathlib `ωₙ` construction follow this project's exact decomposition (`compl₂EDS` = full complement, `compl₂EDSAux` = second term only), or does the mathlib maintainer prefer a different scaffolding that would make this specific lemma moot?

**If the human answers "1: yes, 2: named def, 3: this decomposition"**, the verdict collapses to **YES-add-as-is** — proposed location `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (next to `complEDS₂_neg`) or alongside the new `ωₙ` definition in `DivisionPolynomial/Basic.lean`; proposed PR: ship as ONE PR with the whole `compl₂EDSAux` + `ω` track (not standalone), titled "feat(AlgebraicGeometry/EllipticCurve): add ωₙ division polynomials"; pre-PR: run `/generalise` (expected: no change — already maximal) and `/cleanup`.

**If the human answers "2: inline"**, the verdict collapses to **NO-composable-from-mathlib** (the lemma is absorbed into the `ω` definition's proof and no separate lemma is kept).

**Next action:** user answers questions 1–3; re-run `/mathlibable compl₂EDSAux_neg` (or assess the parent `compl₂EDSAux` + `WeierstrassCurve.ω` as the real unit of contribution — that is the decision this lemma hangs on).

---

## Next step

User answers the three numbered questions. The pivotal one is whether the project's `ωₙ` track is destined for mathlib's open `ωₙ` TODO and, if so, whether `compl₂EDSAux` survives as a named def. Until then, this `_neg` helper is mathlibable-in-principle but only as a rider on that larger, not-yet-upstreamed development — hence BORDERLINE, not a self-resolving YES/NO.
