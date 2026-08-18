# /mathlibable report — `EllSequence.HaveSameParity₄.strictAnti₄_transf`

## Verdict: **BORDERLINE-needs-human**

One-line: a project-internal descent-bookkeeping lemma with no literature name and exactly one genuine call site — but it travels with the `EllSequence.rel₄` four-index-relation apparatus (Junyan Xu, arXiv:2604.05280) that *is* genuinely mathlib-bound. Whether it ships as an internal lemma of that upstreaming, or is dropped/privatised, is a packaging call for a human.

---

### Baseline (Phase 0)
- lake build:               ⚠ not run (env: local build stale, per task note); decl read directly from source.
- decl `EllSequence.HaveSameParity₄.strictAnti₄_transf`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:290`
- qualified name:           VERIFIED — `namespace EllSequence` (L90) › `section transf` (L202) › `namespace HaveSameParity₄` (L216) › `theorem strictAnti₄_transf` (L290). Matches the prompt's guess exactly.
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS): defines EDSs and constructs normalised EDSs from initial terms; this fork additionally develops the `EllSequence.rel₄` four-index elliptic relation and its proof.

### Statement (Phase 1)

`strictAnti₄_transf` states: **if four integers `a,b,c,d` have the same parity (`same : HaveSameParity₄ a b c d`) and are nonnegative and strictly decreasing (`anti : StrictAnti₄ a b c d`, i.e. `0 ≤ d < c < b < a`), then their image under the "half-sum reflection" transformation `T(a,b,c,d) = (s−d, s−c, s−b, |s−a|)` — where `s = avg₄ a b c d = (a+b+c+d)/2` — is again nonnegative and strictly decreasing (`StrictAnti₄ (s−d) (s−c) (s−b) |s−a|`).**

Project-local definitions involved:
- `StrictAnti₄ a b c d := 0 ≤ d ∧ d < c ∧ c < b ∧ b < a` (L207)
- `HaveSameParity₄ a b c d := a.negOnePow = b.negOnePow ∧ b.negOnePow = c.negOnePow ∧ c.negOnePow = d.negOnePow` (L210)
- `avg₄ a b c d := (a + b + c + d) / 2` (L214)

Hypotheses (Lean side):
- `same : HaveSameParity₄ a b c d` — needed only for the first conjunct, via `same.avg₄_add_avg₄` (so that `2s = a+b+c+d`, making `s − d > s − c` etc. provable by `linarith`).
- `anti : StrictAnti₄ a b c d` — the ordering being transported.

Conclusion (math): the transformed 4-tuple is still nonneg + strictly decreasing.
Conclusion (Lean): `StrictAnti₄ (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a|`.

Proof (4 lines): `obtain ⟨hd, hdc, hcb, hba⟩ := anti; refine ⟨abs_nonneg _, abs_lt.mpr ⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [← sub_pos]; · rw [sub_neg_eq_add, sub_add_sub_comm, same.avg₄_add_avg₄]; linarith only [hd, hdc]; all_goals linarith only [hdc, hcb, hba]`. Pure `Int`-arithmetic / `linarith` after one rewrite with `avg₄_add_avg₄`.

### Size classification (Phase 2a)
Verdict: **SMALL**. Reason: a helper lemma — a single inductive-step invariant inside the proof of `rel₄_of_anti_oddRec_evenRec`; not a named theorem, not a `## Main results` entry.

### One-line check (Phase 2b)
n/a — kind is `theorem`, not `def`. (Body is a 4-line tactic proof, not a one-line definition.)

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|--------------------|-------|
| 1 | WebSearch (specific form) | "elliptic divisibility sequence … four index relation proof descent strictly decreasing indices" | partial | The 4-index relation `W(m+n)W(m−n)W(r)² = W(m+r)W(m−r)W(n)² − W(n+r)W(n−r)W(m)²` is standard (Ward); proven *by induction*. | No source surfaces the half-sum reflection T or a strict-decrease-preservation lemma as a standalone result. |
| 2 | WebSearch (general / formalisation) | "\"elliptic divisibility sequence\" net Somos addMulSub three-term relation rel4 formalization Lean mathlib" | yes | Identifies the source: an elementary algebraic proof of the n-th multiple/division-polynomial formula, formalised in Lean, "most results in a PR to mathlib's `EllipticDivisibilitySequence.lean`". | Author David Kurniadi Angdinata / Junyan Xu. This is exactly the apparatus this fork develops. |
| 3 | WebSearch (named-after / aliases) | (covered by #1: "Ward", "Somos", "division polynomial") | yes | Ward's recursion; Somos-k relations; "every Somos 4 is a Somos k". | The *relation* is named; the *descent's index-reflection step* is not. |
| 4 | arXiv fetch (the source paper) | arXiv:2604.05280 "On Elliptic Sequences over Commutative Rings" (Junyan Xu) | yes (paper) | Confirms `IsEllSequence` ↔ Lean; theorems 2.x–6.x on elliptic sequences over comm rings. | The transformation `T`, `StrictAnti`, and `HaveSameParity` do **not** appear as named statements in the paper's surfaced structure — consistent with internal proof bookkeeping. |
| 5 | Local references | `ls projects/NagellLutz/.mathlib-quality/references/`; `ls refs/` | n/a | dir absent | No references/ dir and no `refs/NagellLutz/` PDFs in this checkout — recorded n/a. |
| 6 | nLab | "elliptic divisibility sequence" | n/a | — | EDS is an arithmetic/recurrence object; nLab has no descent-reflection lemma of this shape. Not categorical. |
| 7 | nCatLab | — | n/a | — | Not a categorical concept. |
| 8 | Stacks Project | — | n/a | — | Not an algebraic-geometry/scheme-theoretic statement (it is an `Int`-arithmetic ordering lemma). |
| 9 | MathOverflow / MSE | "elliptic divisibility sequence integrality induction" | partial | Ward's integrality/divisibility proofs use induction; the specific index transformation isn't a cited lemma. | — |
| 10 | recent arXiv (≤5y) | "elliptic sequences commutative rings" | yes | arXiv:2604.05280 (the source) + arXiv:1505.00194 (Somos-4/5 divisibility). | None state T/strict-decrease as a reusable lemma. |
| — | ChatGPT MCP | (attempted: asked whether T and its strict-decrease lemma are a named standard result) | **DOWN** | — | Codex command failed (env note: ChatGPT MCP may be down). Falling back on WebSearch + arXiv + reasoning, which are conclusive here. |

### Literature summary (Phase 3)
- Concept identified as: **the half-sum / "average" reflection `T(a,b,c,d) = (s−d, s−c, s−b, |s−a|)` used in the descent proof that division-polynomial sequences satisfy the four-index elliptic relation.** The *relation* is classical (Ward); the *transformation and its invariant* are an internal device of the Angdinata–Xu elementary-algebraic proof (arXiv:2604.05280), the one being upstreamed to mathlib.
- Sources agree on the standard form: **n/a** — there is no "standard form" of this lemma. It is not a named result. The literature names the relation it serves, not this step.
- Most general standard form: none exists in the literature as a citable statement.
- Disagreement with the literature: none — the lemma is simply below the literature's granularity (a proof-internal index manipulation).

### Generality analysis (Phase 4)

Literature-standard form: n/a (no standalone literature statement). The "ambient" general object is `IsEllSequence` over an arbitrary `CommRing`, which mathlib already has.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | indices `a b c d : ℤ` | integers | ℤ (EDS are ℤ-indexed) | NO | The relation and division polynomials are intrinsically ℤ-indexed; `negOnePow`/parity is a ℤ notion. Already maximal for the domain. |
| 2 | `same : HaveSameParity₄ …` | same `negOnePow` | — | NO meaningfully | Essential: without it `avg₄_add_avg₄` (i.e. `2·avg₄ = a+b+c+d`) fails (the `/2` truncates), and the first conjunct breaks. |
| 3 | `anti : StrictAnti₄ …` | `0 ≤ d < c < b < a` | — | NO | This is precisely the descent's well-founded measure; weakening it removes the point of the lemma. |

#### Generality verdict (Phase 4b)
The current form is: **MAXIMALLY GENERAL for its (intrinsically narrow, ℤ-arithmetic) domain.** Number of weakening opportunities: 0. There is no more-general literature target to aim at — this is not a "specialisation of a general theorem", it is a bespoke step.

#### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Why |
|---|----------|----------|-----|
| 1 | "let X be a foo" → typeclass? | no | Hypotheses are propositions about specific integers, not structure on a carrier. |
| 2 | sequences/metric → filters/topology? | no | Finite arithmetic ordering on a 4-tuple; no limiting process. |
| 3 | construction → universal property? | no | No object is constructed. |
| 4 | set+closure-pred → bundled substructure? | no | No substructure. |
| 5 | vector-space/field → module/ring weakening? | no | Domain is ℤ; the relation it serves is already stated over arbitrary `CommRing` upstream. |
| 6 | 1-categorical → higher-categorical? | no | Not categorical. |
| 7 | concrete index ℕ/ℤ/ℝ → general additive structure? | no | The parity (`negOnePow`) and the half-integer `avg₄` are ℤ-specific; generalising the index type is meaningless here. |

Modern idiom available: **no.** Reason: this is a finite `Int`-arithmetic invariant of a specific descent; there is no contemporary mathlib reformulation that reorganises it — it is glue, not a concept.

### Diamond / defeq risk (Phase 4.5)
n/a — declaration kind is `theorem` (introduces no definitional equalities or instance-search paths).

### Mathlib search-status (Phase 5)

[A] Lean-Finder    — n/a (MCP index unavailable in this stale-build env).
[B] Loogle         — n/a (MCP index unavailable). Type-pattern would be `StrictAnti₄ _ _ _ _` → no such symbol exists in mathlib (confirmed by [D]).
[C] LeanSearch     — n/a (MCP index unavailable).
[D] **Grep mathlib src** (authoritative here) — searched `.lake/packages/mathlib/Mathlib/`:
   - `StrictAnti₄ | HaveSameParity₄ | avg₄ | _transf | SameParity | addMulSub | rel₄` across `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` and `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/*` → **zero hits**.
   - Same patterns across the **entire** `Mathlib/` tree → **zero hits**.
   - Mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines) contains only: `IsEllSequence`/`IsDivSequence`/`IsEllDivSequence` (defs), and the `preNormEDS`/`normEDS`/`complEDS` *constructions* + recurrences. It does **not** contain the `EllSequence.rel₄` four-index relation, `net`, `addMulSub`, the `transf` section, or any descent proof. That whole apparatus is **new in this fork** (the in-progress upstreaming of arXiv:2604.05280).
[E] Name pattern   — grep `strictAnti₄ | _transf | HaveSameParity` in mathlib → zero hits.

Searched for both the user's form and the (non-existent) literature-standard form.

**Concluded:** *not in mathlib* (grep-exhaustive over the full tree, both forms). Mathlib has the ambient `IsEllSequence` definition but not this proof, and a fortiori not this proof-internal step.

### Composition check (Phase 6)

#### Call sites — `strictAnti₄_transf`
Internal use count (this project, excluding declaring file): **K = 1** genuine.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `NagellLutz/.../EllipticDivisibilitySequence.lean:492` | `refine ih _ ?_ same.transf (same.strictAnti₄_transf anti)` — supplies the strict-decrease side-condition so the inductive hypothesis `ih` applies after the `transf` rewrite (L491 `rw [← same.rel₄_transf]`). |

Duplicate copies in sibling forks (NOT independent consumers — they are the *same lemma + same single call site*, the duplicated General*/PID*/Original tracks the prompt flagged):
- `HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:246` (decl) + `:407` (its own call site).
- `NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:279` (decl) + `:469` (its own call site).

Inline-derivation grep (re-derived elsewhere without the lemma?): none.

Signal: **K = 1, no inline re-derivation.** Per the call-sites table, K=1 leans toward "possibly inlinable / wrong abstraction" — but here the single caller is the well-founded descent and the lemma is one of three side-conditions fed to `ih`; it is a natural sub-step, not an accidental wrapper.

#### Composition attempt
Can the *statement* be produced from mathlib in ≤3 chained calls? No — the conclusion is a 4-conjunct `StrictAnti₄` (itself a project-local `∧`-predicate), proven by `refine ⟨abs_nonneg _, abs_lt.mpr ⟨_,_⟩, _, _⟩ <;> rw[←sub_pos]; …; linarith`. That is a genuine (if short) proof with a case split on the `abs` and an `avg₄_add_avg₄` rewrite — a real `linarith` argument over 4 hypotheses, not a `.trans`/`.symm`/single-call composition.

**Conclusion: NOT-COMPOSABLE** (as a standalone mathlib-primitive composition). But note: it is also *not worth a standalone mathlib lemma* — it is inseparable from the descent it serves.

---

## Verdict: `EllSequence.HaveSameParity₄.strictAnti₄_transf`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature (Phase 3): the four-index *relation* is classical (Ward), but T and its strict-decrease invariant are **not a named result** — they are internal to the Angdinata–Xu elementary-algebraic proof (arXiv:2604.05280) that is itself being upstreamed to mathlib. Lit search returned no standalone form (the "literature absence ⇒ not automatically YES" anti-pattern applies).
- Generality (Phase 4): MAXIMALLY GENERAL for its intrinsically narrow ℤ-arithmetic domain; no more-general target; no modern-idiom reformulation (4c all "no").
- Mathlib (Phase 5): not in mathlib (grep-exhaustive, both forms). Critically, **mathlib's EDS file does not yet contain the parent `rel₄` apparatus at all** — so the question is entangled with an in-flight upstreaming.
- Composition (Phase 6): NOT-COMPOSABLE as a primitive chain, but K=1 and the lemma is inseparable from its single descent call site.

**Rationale.**
This lemma sits exactly on the seam the task warned about. On the one hand it is, in isolation, a piece of proof-internal bookkeeping: a four-conjunct `Int`-ordering invariant about a bespoke half-sum reflection, with no name in the literature, one real call site, and no life outside the proof of `rel₄_of_anti_oddRec_evenRec`. Taken alone, that profile says "do not add as a standalone mathlib lemma" — it would never be cited by name, and it is built on three project-local predicates (`StrictAnti₄`, `HaveSameParity₄`, `avg₄`) that themselves are private to this descent.

On the other hand, the *parent* construction — `EllSequence.rel₄` and the elementary-algebraic proof that division-polynomial/normalised-EDS sequences satisfy the four-index elliptic relation — is genuinely mathlib-bound: it is the Junyan Xu / David Angdinata development (arXiv:2604.05280), explicitly described as a PR to mathlib's `EllipticDivisibilitySequence.lean`, and mathlib's current file already hosts the sibling `IsEllSequence`/`normEDS` material it extends. If and when that proof lands in mathlib, `strictAnti₄_transf` (and `transf`, `rel₄_transf`, `avg₄`, `HaveSameParity₄`, `StrictAnti₄`, `six_le_of_strictAnti₄`, …) go with it — most likely as `private`/section-local lemmas *inside* that proof, not as public API. So the verdict is not "no" in the sense of "delete and inline at the one call site" (that would damage the readability of a proof that is itself a planned mathlib contribution), nor "yes-add-as-is" (no one wants this exposed as a top-level mathlib theorem). The right disposition depends on a packaging decision a human owns: does this fork ship the `rel₄` descent upstream as a unit, and if so at what visibility? That cannot be grounded in the search evidence alone.

**Numbered questions (≤5):**
1. Is the `EllSequence.rel₄` four-index-relation development in this fork intended to be upstreamed to mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (i.e. is it the arXiv:2604.05280 / Angdinata–Xu proof being prepared)? If **yes** → `strictAnti₄_transf` ships *with* it as an internal lemma; this triage closes as "bundled, not standalone".
2. If upstreamed, should the descent's bookkeeping lemmas (`strictAnti₄_transf`, `transf`, `rel₄_transf`, `six_le_of_strictAnti₄`, `avg₄`, `addMulSub₄`, …) be `private` / section-scoped inside the proof, rather than public `theorem`s? (Recommended: yes — they have no independent consumers.)
3. The lemma exists in three copies (`NagellLutz` × 2 incl. `…Original.lean`, `HasseWeil/Auxiliary`). Is the canonical copy `NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`, with the others slated for de-duplication onto it? (This is a cleanup-track question, but it bears on which copy, if any, is the upstreaming source.)
4. If the `rel₄` development is **not** going upstream, should `strictAnti₄_transf` simply remain a project-internal helper (no mathlib action, no inlining) given it is load-bearing for the descent at L492? (Recommended: yes — leave as-is, mark non-mathlibable.)

**Next action:** user answers Q1 (the pivot). If Q1 = yes → mark BORDERLINE resolved as "ships bundled with the `rel₄` upstreaming; make it `private`/internal per Q2; not a standalone PR." If Q1 = no → resolve as effectively NO (project-internal helper; keep, do not inline, do not PR). Either way the lemma is **not** a standalone mathlib addition and **not** a delete-and-inline target.

---

## Next step
Answer Q1 above (is the `EllSequence.rel₄` descent being upstreamed to mathlib's `EllipticDivisibilitySequence.lean`?). That single answer collapses this BORDERLINE to "bundle as an internal lemma" (yes) or "keep project-local, non-mathlibable" (no). In neither branch is `strictAnti₄_transf` a top-level mathlib theorem or an inline-at-call-site deletion.
