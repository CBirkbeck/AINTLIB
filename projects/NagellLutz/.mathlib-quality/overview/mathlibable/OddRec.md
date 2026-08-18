# /mathlibable report — `IsEllSequence.oddRec`

**Verdict: BORDERLINE-needs-human**

> One-line rationale: Not in mathlib; standard "elliptic ⇒ odd recurrence" but a one-call glue lemma over project-only `OddRec`/`rel₃_iff_oddRec` — ships only **with** the new `EllSequence` framework (a maintainer/API-direction call).

Project: NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS).
File: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:650`.
Run: Step-9 overview mathlibable assessment (single declaration), 2026-06-18.

> Note on this file: a prior run wrote an assessment of the **def** `EllSequence.OddRec`
> (line 355) here. The task target is the **lemma** `IsEllSequence.oddRec` (line 650), so this
> file has been rewritten for that lemma. The `OddRec` def assessment is preserved in
> `OddRec.md`; the bridge lemma in `rel₃_iff_oddRec.md`.

---

### Baseline (Phase 0)
- lake build:               NOT run (local build known-stale per task brief; reasoned from source — the
                            decl elaborates in the project and is consumed downstream in two projects, so it is real).
- decl `IsEllSequence.oddRec`: ✓ resolved at `EllipticDivisibilitySequence.lean:650`.
- qualified name (VERIFIED): **`IsEllSequence.oddRec`**. The outer namespace `EllSequence`
  *closes* at L597 (`end EllSequence`); `namespace IsEllSequence` opens at L643 (NOT nested in
  `EllSequence`); `IsEllSequence` is itself a `_root_` def (L135). So the base name `oddRec`
  inside `namespace IsEllSequence` qualifies to `IsEllSequence.oddRec`. The task's parse is correct.
- kind:                      `lemma` (`theorem`).
- has sorry:                 no.
- module docstring summary:  "Elliptic divisibility sequences (EDS) and the construction of normalised
                            EDSs from initial terms" — a project fork/extension of
                            `Mathlib.NumberTheory.EllipticDivisibilitySequence` (same author header,
                            David Kurniadi Angdinata).

Full signature & proof (section context `variable {R : Type u} [CommRing R] (W : ℤ → R)`,
`variable (ell : IsEllSequence W)` + `include ell` at L647–648):
```lean
lemma oddRec (m : ℤ) : OddRec W m := (rel₃_iff_oddRec W m).mp (ell _ _ _)
```

---

### Statement (Phase 1)

`IsEllSequence.oddRec` says: **every elliptic sequence satisfies the odd-index duplication
recurrence**. Concretely, if `W : ℤ → R` is an elliptic sequence (i.e. `IsEllSequence W`: the
symmetric three-index elliptic relation `Rel₃ W m n r` holds for all `m n r`), then for every `m`,

> `W(2m+1) · W(1)³ = W(m+2) · W(m)³ − W(m−1) · W(m+1)³`.

The proof is a one-call extraction: instantiate the universally-quantified elliptic relation at the
specific indices `(m+1, m, 1)` — `ell (m+1) m 1 : Rel₃ W (m+1) m 1` — and push it through the
algebraic equivalence `rel₃_iff_oddRec W m : Rel₃ W (m+1) m 1 ↔ OddRec W m` (a pure `ring`
rearrangement, L363–364). The `ell _ _ _` lets unification fill `(m+1) m 1` from the expected
`Rel₃ W (m+1) m 1` on the iff's left.

Variables / typeclasses (Lean side):
- `R : Type u`, `[CommRing R]` — coefficient ring; maximal natural generality (the relation is polynomial; no domain / nonzero-divisor / characteristic hypotheses).
- `W : ℤ → R` — integer-indexed sequence.
- `ell : IsEllSequence W` (included) — the sole hypothesis: `W` is elliptic.
- `m : ℤ` — the index.

Hypotheses: `ell : IsEllSequence W`.
Conclusion (math): the displayed odd-duplication recurrence.
Conclusion (Lean): `OddRec W m` (a project-local `Prop`, L355).

---

### Size classification (Phase 2a)

Verdict: **SMALL** (leans BIG-adjacent).
Reason: it is a corollary/specialisation — it instantiates the general 3-index elliptic relation at
fixed indices and rewrites to a named recurrence (the dual of `IsEllSequence.evenRec`, L651). It is
*not* a `def`/`class`, not named after a person, not itself a "Main statement". It is, however, a
load-bearing API lemma feeding the project's BIG main result `isEllDivSequence_normEDS`. Literature
width is EXHAUSTIVE regardless.

### One-line check (Phase 2b)

Kind is `lemma`, not `def` → one-line check **n/a**. (For the record the body is one line, but the
def-one-liner negative-signal logic applies to `def`/`abbrev`/`structure`, not theorems.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form) | Ward EDS "an elliptic sequence satisfies" odd recurrence `W(2m+1)W(1)^3 = W(m+2)W(m)^3 − W(m−1)W(m+1)^3` | partial | EDS doubling recurrences are standard; arXiv math/0412293, 2102.07573, 2604.05280 | exact 4-factor odd form pinned by Wikipedia (#4) |
|  2 | WebSearch (general / direction) | "elliptic divisibility sequence" even/odd duplication formulas derived from the elliptic relation | yes | the even–odd recurrences are *consequences* of (and, with side conditions, equivalent to) the symmetric Ward relation | confirms the *forward* implication this lemma states is the textbook route |
|  3 | WebSearch (named aliases / nets) | Stange elliptic net relation ⇒ term-by-term recurrence; division-polynomial recurrence | yes | nets generalise EDS; the net/`rel₄` relation specialises to the single-index recurrences | arXiv 0710.1316 (Stange), eprint 2025/521 |
|  4 | WebFetch Wikipedia "EDS" | exact odd duplication formula + side condition | **yes (verbatim)** | **odd: `W₂ₙ₊₁W₁³ = Wₙ₊₂Wₙ³ − Wₙ₊₁³Wₙ₋₁` (n≥2)** | term-for-term identical to `OddRec`, incl. the explicit un-normalized `W₁³`; the article states it *as a property elliptic sequences satisfy* — i.e. exactly this lemma |
|  5 | ChatGPT MCP | confirm "elliptic ⇒ odd recurrence" is the standard implication + mathlib-gap | n/a | — | MCP down in this environment (per task brief); compensated by verbatim Wikipedia (#4) + the in-repo sibling reports (`OddRec.md`, `rel₃_iff_oddRec.md`, `of_oddRec_evenRec.md`) which already establish the literature anchor |
|  6 | Local references | `projects/NagellLutz/.mathlib-quality/references/`, `refs/NagellLutz/` | n/a | — | neither directory present |
|  7 | nLab | `elliptic divisibility sequence` | n/a | — | no nLab page; not a categorical concept |
|  8 | nCatLab | (categorical reformulation) | n/a | — | not a categorical concept |
|  9 | Stacks Project | EDS / elliptic sequence | n/a | — | out of scope (integer-sequence arithmetic, not scheme theory) |
| 10 | MathOverflow / arXiv (recent) | recurrences ⇒/⇐ elliptic relation; commutative-ring EDS | yes | van der Poorten–Swart coherence (math/0412293); **Xu, "On Elliptic Sequences over Commutative Rings", arXiv:2604.05280 (2026)** — Thm 2.2 is the *converse* (recurrences ⇒ elliptic) that the project's `of_oddRec_evenRec` formalises; this lemma is the trivial *forward* direction of that circle | 2604.05280 acknowledges D. K. Angdinata, the file's author — freshly-formalised current research |

Protocol pass: WebSearch ran 3 distinct queries at different generality (specific odd form / general
"consequence of the elliptic relation" / named-aliases-nets); Wikipedia fetch gave the verbatim
formula stated as a property of elliptic sequences; recent-arXiv channel run; local refs / nLab /
nCatLab / Stacks each checked and recorded `n/a` with reason; ChatGPT MCP recorded down with
compensating in-repo + Wikipedia evidence.

### Literature summary (Phase 3)

Concept identified as: **the odd-index doubling (duplication) recurrence of an elliptic divisibility
sequence**, here as the *forward* statement "an elliptic sequence satisfies it".
Sources agree on the standard form: **yes** — Wikipedia gives the equation verbatim (matching `OddRec`
exactly, including the un-normalized `W₁³`); Ward's memoir and the modern net literature (Stange;
Xu 2604.05280) treat the even–odd recurrences as the canonical consequence of / equivalent to the
symmetric elliptic relation.
Most general standard form: over an arbitrary commutative ring `R`, for any `W : ℤ → R` satisfying the
symmetric elliptic relation, the odd recurrence holds at every index — exactly the Lean statement.
Generality dimensions where the literature varies:
  - **Coefficient ring**: classically `ℤ` (Ward) → arbitrary `CommRing` (Xu 2604.05280, and this
    file). Lean form is at the most general end.
  - **Normalisation**: `W(1)=1` (classical) vs. keeping `W(1)³` explicit (un-normalized). Lean form is
    the more general un-normalized one.
Disagreement with the literature: **none**. The Lean statement is the literature-standard fact at
literature-maximal generality.

---

### Generality analysis — `IsEllSequence.oddRec`

Literature-standard form (Phase 3): over any `CommRing`, an elliptic sequence satisfies the
un-normalized odd recurrence at every integer index.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]` | commutative ring | commutative ring | NO | the elliptic relation and the recurrence are polynomial identities over a comm. ring; `CommRing` is already the maximal sensible class — no domain/field/char assumption is used |
| 2 | `ell : IsEllSequence W` | full symmetric 3-index relation, ∀ indices | the elliptic relation | NO (intrinsic) | the proof only needs the *single* instance `ell (m+1) m 1`, but the lemma's natural hypothesis is "`W` is elliptic"; weakening to "`W` satisfies `Rel₃` at `(m+1,m,1)`" would make a strictly weaker, less useful lemma — not a generalisation worth taking |
| 3 | `W : ℤ → R` | ℤ-indexed sequence | ℤ-indexed sequence | NO | the recurrence is inherently about integer indices `2m+1, m±1, m+2`; no monoid generalisation applies |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**.
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream this enables |
|----|----------|----------|------------------------|--------------------------|
|  1 | "let X be a foo" preambles → typeclasses / instances? | no | — | `IsEllSequence W` is a `Prop`-valued hypothesis on a bare function; this is already mathlib's own idiom (mathlib's `IsEllSequence` is the same shape). Bundling into a class is not how mathlib states EDS. |
|  2 | sequences / metric → filters / topology? | no | — | finite algebraic identity; no limiting/topological content. |
|  3 | construction → universal-property class? | no | — | it is an equational property, not a construction. |
|  4 | set+closure-predicate → bundled substructure? | no | — | n/a. |
|  5 | vector-space/metric/field-specific → weaker typeclass? | no | — | already `CommRing`, the weakest sensible. |
|  6 | 1-categorical → higher-categorical? | no | — | n/a. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid? | no | — | `ℤ` is essential (indices `2m+1`, `m−1`, `m+2`; negative indices matter for the full EDS theory). |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The statement is a finite polynomial identity over a comm. ring,
already in mathlib's own EDS idiom (bare `W : ℤ → R` + a `Prop` hypothesis). No reorganisation is a
real improvement.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no new definitional equality, no typeclass-search path introduced).

---

### Mathlib search-status: `IsEllSequence.oddRec`

Searched the **pinned mathlib** this project forks (`.lake/packages/mathlib`) and the live docs.

```
[A] Lean-Finder       "elliptic sequence satisfies odd recurrence"   no hits (concept absent upstream)
[B] Loogle            (IsEllSequence _ → _) / OddRec pattern          n/a — `OddRec` is not a mathlib symbol, so no type pattern to query
[C] LeanSearch        "an elliptic divisibility sequence satisfies the odd duplication recurrence"  no hits
[D] Grep mathlib src  `oddRec`, `OddRec`, `Rel₃`, `rel₃_iff_oddRec`   0 hits across all of .lake/packages/mathlib
[E] Name pattern      `IsEllSequence.` lemmas in mathlib              only `IsEllSequence.smul` / `.map` exist; NO `.oddRec`, `.evenRec`, `.neg`, `.of_oddRec_evenRec`
```

Whole-mathlib grep results (verified this run):
- `grep -rnE "\boddRec\b|\bOddRec\b" .lake/packages/mathlib/Mathlib` → **0 hits**.
- `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` is the **older, smaller** version: it
  defines `IsEllSequence` with the elliptic relation **inlined** (no `Rel₃` abstraction), then
  `IsEllSequence.smul`/`.map`, then jumps straight to `preNormEDS'`. It has **no** `OddRec`/`EvenRec`
  predicate, **no** `rel₃_iff_oddRec` bridge, **no** `IsEllSequence.oddRec` lemma, and (per the
  sibling reports' live-docs check) still lists `normEDS satisfies IsEllDivSequence` as a TODO.
- `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` — 0 hits for any
  of the recurrence apparatus.

Searched for both:
  - the user's current form (`IsEllSequence W → OddRec W m`) — absent (both `IsEllSequence`-with-`Rel₃`
    and `OddRec` differ from / are missing upstream).
  - the literature-standard form ("elliptic ⇒ odd duplication recurrence") — absent in any guise.

Concluded: **not in mathlib** (all methods exhausted: pinned source + name search + live docs; both
the user's form and the literature-standard form). Mathlib *cannot even state this lemma today*,
because the conclusion `OddRec W m` is a project-private predicate absent upstream. So this is firmly
**NOT** `NO-mathlib-has-it`.

---

### Call sites — `IsEllSequence.oddRec`

Internal use count (NagellLutz, outside L650): **1**.
External-to-file callers: HasseWeil project (a sibling fork) — **2 distinct sites**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `…/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:692` | `… (fun _ _ ↦ ell.oddRec _) (fun _ _ ↦ ell.evenRec _) same` — feeds `IsEllSequence.rel₄` (which underlies `.net`, `.invar`, and ultimately `isEllDivSequence_normEDS`) |
| `…/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:570` | `… (fun _ _ ↦ ell.oddRec _) (fun _ _ ↦ ell.evenRec _) same` (sibling-fork copy of the same `rel₄` proof) |
| `…/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:699` | `erw [Nat.cast_add, …, ellW.oddRec, h1, ellU.oddRec]` — uses the odd recurrence directly in a Hasse–Weil EDS computation |

Inline-derivation grep (was the equivalent re-derived without this lemma?): consumers route through
`ell.oddRec`; the only "inline" reproductions are the **duplicate-track copies** of the whole lemma
(`EllipticDivisibilitySequenceOriginal.lean:622`, `HasseWeil/Auxiliary/…:525`) — i.e. the same lemma
forked across files (a dedup target on `main`), not a sign the abstraction is bypassed.

Signal: K = 1 in-file but it is a genuine API lemma — the named "elliptic ⇒ odd recurrence"
extraction, the dual of `IsEllSequence.evenRec`, on the critical path to the file's BIG main theorem,
and it has **real external consumers in another project** (HasseWeil, 2 sites). This is the
"public-API / consumers-exist" pattern, not "K=1 ⇒ inline it".

---

### Composition check (Phase 6)

Can `IsEllSequence.oddRec` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `(rel₃_iff_oddRec W m).mp (ell (m+1) m 1)` — exactly the project's own one-call proof.
  - Mathlib decls used: **none**. `rel₃_iff_oddRec` is project-local (L363); `ell` is the hypothesis;
    `Rel₃` and `OddRec` are project-local defs.
  - Result: **fails as a mathlib composition** — every primitive it composes (`rel₃_iff_oddRec`,
    `Rel₃`, `OddRec`) is absent from mathlib.

Attempt 2 (state it purely from mathlib): unfold to the bare equation and prove from `ell` by
specialising the inlined mathlib `IsEllSequence` at `(m+1, m, 1)` then `ring_nf`.
  - This would be a small `by … ring` proof — but the *conclusion* `OddRec W m` cannot be written at
    all without first adding the `OddRec` predicate to mathlib. There is nothing in current mathlib to
    state, let alone compose.
  - Result: **fails** — blocked at the statement, not just the proof.

Conclusion: **NOT-COMPOSABLE from current mathlib.** The one-call composition is real, but only
*inside* the new `EllSequence`/`IsEllSequence`-extension framework. It is NOT
`NO-composable-from-mathlib`, because the building blocks are the very thing that would have to land
upstream first.

---

## Verdict: `IsEllSequence.oddRec`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): standard, verbatim-matched (Wikipedia odd formula; Ward; Xu
  arXiv:2604.05280). "Elliptic ⇒ odd recurrence" is the textbook forward implication.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (CommRing; un-normalized; nothing to weaken; no
  modern-idiom improvement).
- Mathlib search (Phase 5): NOT in mathlib — and *unstatable* upstream today (conclusion `OddRec` is a
  project-only predicate; mathlib's EDS file is the older, smaller version).
- Composition check (Phase 6): NOT-COMPOSABLE from current mathlib (the one-call proof needs
  project-only `rel₃_iff_oddRec`/`Rel₃`/`OddRec`).

**Rationale.**
`IsEllSequence.oddRec` is a correct, standard, maximally-general, genuinely-used API lemma — the named
"every elliptic sequence satisfies the odd-index duplication recurrence" fact (dual to
`IsEllSequence.evenRec`), consumed in NagellLutz's `rel₄` machinery and at three sites across the
HasseWeil project. In a vacuum that profile points at a YES bucket. But the lemma is meaningless
upstream in isolation: its conclusion type `OddRec W m` is a project-private predicate that mathlib
does not have, and its one-line proof is a projection through the project-private bridge
`rel₃_iff_oddRec` out of the project's own `Rel₃`-flavoured `IsEllSequence`. Mathlib literally cannot
state this lemma today. So it cannot be a standalone `YES-add-as-is`, cannot be
`NO-composable-from-mathlib` (the building blocks aren't in mathlib), and cannot be `NO-mathlib-has-it`
(verified absent from the pinned tree and the live docs).

The correct *unit of contribution* is the whole new `EllSequence` framework — `Rel₃`, `rel₄`, `net`,
`OddRec`, `EvenRec`, the `rel₃_iff_*` bridges, `of_oddRec_evenRec`, on through
`isEllDivSequence_normEDS` — which is active, recently-published research (Xu, *On Elliptic Sequences
over Commutative Rings*, arXiv:2604.05280, 2026, acknowledging the file's author Angdinata) that
plausibly supersedes mathlib's current EDS file and is in fact being upstreamed by that author (cf.
the open EDS PRs noted in the sibling reports `invarDenom.md`, `addMulSub₄_mul_addMulSub₄.md`).
**Within that framework**, `IsEllSequence.oddRec` is a small, well-named, load-bearing lemma that
should travel *with* the framework (and there becomes a YES line item, exactly as the siblings
`rel₃_iff_evenRec`, `rel₄_of_oddRec_evenRec`, and `of_oddRec_evenRec` were judged). The genuine
decision — *adopt the `EllSequence` framework into mathlib (extending/replacing the existing EDS API),
and if so carry this lemma along* — is a maintainer call about API direction, coordinated with the
author, not a mechanical one. This is consistent with the BORDERLINE verdicts already recorded for the
lemma's own building blocks `rel₃_iff_oddRec` and `Rel₃`.

**Numbered questions for the human (≤5):**
1. Is the `EllSequence`/elliptic-net framework being upstreamed to
   `Mathlib.NumberTheory.EllipticDivisibilitySequence` (it appears to be, by the file's author
   D. K. Angdinata / Xu, arXiv:2604.05280)? If **yes**, `IsEllSequence.oddRec` ships *as-is* as one
   line item of that PR series — do not PR it standalone.
2. Should the upstream form name the predicate `OddRec` and expose `IsEllSequence.oddRec` as public
   API (matching this file), or fold the odd recurrence inline into the proof of
   `IsEllSequence.of_oddRec_evenRec` and skip the standalone extraction lemma?
3. Before any upstreaming, deduplicate the cross-project/track copies
   (`EllipticDivisibilitySequenceOriginal.lean:622`, `HasseWeil/Auxiliary/…:525`) on `main` so a
   single canonical `IsEllSequence.oddRec` is the one promoted — agreed?

**Next action:** do **not** PR this lemma standalone. Track it as a line item in the
"upstream the `EllSequence`/elliptic-net framework" effort (coordinate with D. K. Angdinata, whose code
and paper this is). If/when the framework lands, `IsEllSequence.oddRec` goes in as-is alongside
`IsEllSequence.evenRec`, `IsEllSequence.neg`, and `IsEllSequence.of_oddRec_evenRec`. Resolve questions
1–3, after which the verdict collapses to YES-add-as-is (within the batch) or "drop in favour of an
inline proof".

---

## Next step

Do not PR standalone. Ship `IsEllSequence.oddRec` as one line item of the EDS-framework upstreaming
PR series (the `Rel₃` / `OddRec` / `rel₃_iff_oddRec` / `of_oddRec_evenRec` / `isEllDivSequence_normEDS`
bundle), coordinated with the file's author. Answer questions 1–3 to collapse the verdict.
