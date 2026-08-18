# /mathlibable report — `invarNum_normEDS_two`

_Project: NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials;
elliptic divisibility sequences). Run as part of /overview Step-9 mathlibable
assessment. Re-run 2026-06-21 (supersedes the earlier 2026-06-18 pass; same
verdict, NO-composable-from-mathlib). Local Lean build stale; reasoned from
source + WebSearch + authoritative grep over the pinned mathlib
(`.lake/packages/mathlib`)._

---

### Baseline (Phase 0)

- lake build:               (not re-run — local build is stale per task note;
  reasoning from source. The decl elaborates: it is referenced by name at
  `EllipticDivisibilitySequence.lean:1487` and has a duplicate twin in the
  HasseWeil fork, so it is a real, type-correct declaration.)
- decl `invarNum_normEDS_two`: resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:976`
- **qualified name:** `invarNum_normEDS_two` (ROOT namespace — VERIFIED: at
  line 976 the only open `namespace` block, `EllSequence` (lines 90–597), is
  already closed; the decl sits in `section NormEDS` (881–1520) with no
  enclosing `namespace`. `EllSequence` is brought in only via `open EllSequence`
  at line 884, which is why the body writes `invarNum` unqualified. So the
  fully-qualified name is the bare `invarNum_normEDS_two`.)
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and
  constructs normalised EDSs from initial terms; this file is a project FORK /
  extension of `Mathlib.NumberTheory.EllipticDivisibilitySequence`, adding the
  `invarNum`/`invarDenom` "invariant" apparatus that upstream mathlib does not have.

---

### Statement (Phase 1)

```lean
lemma invarNum_normEDS_two : invarNum (normEDS b c d) 1 2 = (d + b ^ 4) * b := by
  simp [invarNum, right_distrib, ← pow_succ, ← pow_add]
```

`invarNum_normEDS_two` is a **concrete numerical evaluation**. It computes the
value, at `s = 1, n = 2`, of the *numerator of the EDS invariant* applied to the
canonical normalised EDS `W = normEDS b c d` (with `W0=0, W1=1, W2=b, W3=c,
W4=d·b`). Unfolding `invarNum W 1 2` gives
`(W4·W1² + W3²·W0)·W1² + W2³·W2²`, and substituting the canonical values yields
`(d·b·1 + c²·0)·1 + b³·b² = d·b + b⁵ = (d + b⁴)·b`. The proof is a single
`simp` that unfolds `invarNum`, the `normEDS` evaluation lemmas, and folds the
powers with `pow_succ`/`pow_add`.

Mathematically: this is the `n = 2` base case that **pins the constant value of
the EDS invariant**. The EDS invariant (a conserved quantity `I_n` independent
of `n` — see Phase 3) for the canonical normalised sequence equals `d + b⁴`
after clearing the common factor `b·c`; this lemma supplies the numerator half
of that base case (`invarDenom_normEDS_two` supplies `c·b`, the denominator half).

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (maximally general for the
  algebra involved; no integrality, domain, or field hypothesis).
- `(b c d : R)` — the three normalised-EDS parameters (`W2, W3`, and `W4 = d·b`).

Hypotheses (Lean side): none.

Conclusion (math): `invarNum(normEDS_{b,c,d}, 1, 2) = (d + b⁴)·b`.
Conclusion (Lean): `invarNum (normEDS b c d) 1 2 = (d + b ^ 4) * b`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a single fixed-index evaluation of a project-local definition; not a
named theorem, not a new structure, not a `## Main statement` of the file
(the file's headline is `isEllDivSequence_normEDS`). It is a one-off computation
feeding one downstream lemma.

(Literature width was EXHAUSTIVE regardless — recorded for framing only.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure`. The one-liner-definition
exemption machinery is **n/a**. As a *proof*, the body is one `simp` line —
which is itself a strong "this is glue, not API" signal carried into Phase 7.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | EDS invariant constant ratio `W(n+2)W(n-1)²` independent of n                                           | yes  | the conserved quantity `I_n` (first integral), independent of `n` | Found the explicit `I_n` formula (Hone/Swart, integrable-systems form); confirms `invarNum`/`invarDenom` are its cleared numerator/denominator |
|  2 | WebSearch (general / canonical form) | Ward EDS invariant `b c d` normalised initial values                                                | yes  | canonical EDS `W0=0,W1=1,W2=b,W3=c,W4=d·b`; `b∣d` ⇒ integral | Confirms the exact `normEDS` parametrisation used here; Ward 1940s origin |
|  3 | WebSearch (named-after / integrable-systems aliases) | Hone–Swart Somos-4 conserved quantity / first integral of EDS, value `d+b⁴`                    | partial | the conserved quantity / "translation invariant" of Somos-4/EDS exists and is named | The *invariant* is named & studied; its *numerator-value-at-n=2* is NOT isolated as a result |
|  4 | ChatGPT MCP                      | "Is the value of the invariant numerator at n=2 a named result, and is the canonical invariant `d+b⁴`?" | n/a  | (MCP/Codex down — errored, per task note)             | Fallback: WebSearch #1–3 + Wikipedia + first-principles computation cover the question |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/`, `refs/NagellLutz/`                                  | n/a  | (no references dir; both absent)                      | recorded n/a — no local PDFs to consult |
|  6 | nLab                             | "elliptic divisibility sequence"                                                                       | n/a  | nLab has no dedicated EDS page                         | EDS is a number-theory/integrable-systems topic, not a category-theory one |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | not a categorical concept                             | a polynomial identity over a CommRing; nothing categorical |
|  8 | Stacks Project (alg geom)        | "elliptic divisibility sequence" / "division polynomial invariant"                                     | n/a  | not covered in Stacks                                 | Stacks does not treat EDS / division-polynomial invariants |
|  9 | MathOverflow / MathSE            | EDS conserved quantity / invariant value for canonical sequence                                        | yes (via #1) | same conserved-quantity `I_n`                  | corroborates #1; no statement of the n=2 numerator value as a lemma |
| 10 | recent arXiv (≤5 yr) + classics  | "recurrence relation for elliptic divisibility sequences" (2102.07573); van der Poorten; Stange elliptic nets (0710.1316) | yes  | the invariant/first-integral viewpoint is standard    | invariants appear as tools; none names the `n=2` numerator evaluation |

Protocol pass check:
- WebSearch ran ≥3 distinct queries at different generality levels (specific
  ratio form; canonical `b,c,d` form; integrable-systems / named-after aliases). ✓
- ChatGPT MCP attempted; errored (Codex down) — fallback channels cover it. ✓ (n/a w/ reason)
- Local references checked (absent → n/a w/ reason). ✓
- nLab checked (no EDS page → n/a). ✓
- Stacks / nCatLab / MathOverflow / arXiv each checked or n/a-with-reason. ✓

### Literature summary (Phase 3)

Concept identified as: the **invariant (conserved quantity / first integral) of
an elliptic divisibility sequence** — `I_n`, independent of `n`. The project's
`invarNum`/`invarDenom` are its numerator and denominator after clearing
fractions; `invarNum_normEDS_two` is the value of that **numerator at the second
term** of the canonical normalised sequence.

Sources agree on the standard form: yes — the *invariant* `I_n` is a genuine,
named object (Ward → Hone–Swart → van der Poorten → Stange). But:

Most general standard form: the literature's object of study is the **invariant
itself** (`I_n` constant in `n`), and at most its *constant value* for a given
sequence. The literature does **NOT** isolate "the value of the invariant
numerator at `n=2`" as a named/standalone result. It is precisely the kind of
intermediate base-case computation one does *en route* to identifying the
constant — which is exactly its role in the Lean development (it feeds
`invar₂_normEDS_of_mem_nonZeroDivisors` to show the invariant equals `d + b⁴`).

Generality dimensions where the literature varies:
  - coefficient ring: classically ℤ; modern treatments (and this file) work over
    an arbitrary CommRing `R`. The Lean form is already at the **most general**
    (bare `CommRing`) end.
  - which invariant normalisation: literature uses the fraction `I_n`; the
    project uses the cleared `invarNum`/`invarDenom` pair. Equivalent.

Disagreement with the literature: **none** mathematically. The gap is one of
*granularity*: the literature never names this particular evaluation; it is a
computation, not a theorem-with-a-name.

---

## Generality analysis — `invarNum_normEDS_two`

Literature-standard form (from Phase 3): the invariant `I_n` of an EDS is
constant in `n`; for the canonical normalised sequence its (cleared) value is
`d + b⁴`. The relevant *named* result is the constancy/value of the **invariant**
— not the per-index numerator value.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | `[CommRing R]` | arbitrary commutative ring | classically ℤ; modern = comm ring | NO | already maximally general; the identity is a polynomial identity in `b,c,d` valid over any CommRing. `CommRing` is the natural floor for `normEDS`. |
| 2 | `s = 1`, `n = 2` (literal indices) | fixed `s=1, n=2` | n/a — literature doesn't fix these | — (specialisation, not a hypothesis) | This is the whole point: it is a *specialisation* of the general `invarNum`/invariant to one index. Generalising the index gives back `invarNum_normEDS` (sibling general-`n` lemma, line 972) or the invariant-constancy theorem `invar₂_normEDS` — both already in the project. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** on its ring parameter, but it is by
construction a **fixed-index SPECIALISATION** (a single evaluation) of the
project's own more-general results. There is no literature-standard "more
general invarNum_normEDS_two" to aim at — the general object is `invarNum`
itself (project-local, separately assessed BORDERLINE) and the invariant-value
theorem `invar₂_normEDS` (project-local).
Number of weakening opportunities found: 0.
Proposed restatement: none (already maximally general on `R`; the literal
indices are the definition of "the n=2 evaluation").
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclasses? | no | — | no bundled-hypothesis preamble; just `(b c d : R)` |
|  2 | sequences/metric → filters/topology? | no | — | a finite polynomial identity; no limits/topology |
|  3 | construction → universal property? | no | — | it is an equation, not a construction |
|  4 | set+closure-pred → bundled substructure? | no | — | no substructure here |
|  5 | vector-space/field-specific → weaker typeclass? | no | — | already at `CommRing`, the floor |
|  6 | 1-categorical → higher-categorical? | no | — | not categorical |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid? | no | — | the *whole content* is a specific `ℤ`-index (`n=2`); generalising the index destroys the lemma's purpose (it becomes the already-existing general `invarNum_normEDS`) |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a finite, fixed-index polynomial
evaluation over the most general sensible ring. There is no contemporary
mathlib reformulation that is a *mathematical* improvement — the only "more
abstract" versions are (a) the general-`n` numerator lemma and (b) the
invariant-constancy theorem, both already present separately in the project.
Reason it is not a modernisation move: there is nothing to abstract; it is a
leaf computation.

---

## Diamond / defeq risk — `invarNum_normEDS_two`

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search
paths introduced). Phase 4.5 skipped.

---

## Mathlib search-status: `invarNum_normEDS_two`

[A] Lean-Finder       (MCP not available here)            n/a — covered by [D]/[E] grep over the actual pinned mathlib source, which is authoritative
[B] Loogle            type-pattern `invarNum _ _ _ = _`   n/a — `invarNum` is not a mathlib constant, so no Loogle pattern can match; confirmed by [D]
[C] LeanSearch        "value of EDS invariant numerator at second term"  n/a (MCP not available) — WebSearch hit the mathlib docs page (Phase 3 #2/#10) which lists the upstream EDS API: no invarNum
[D] Grep mathlib src  `invarNum`, `invarDenom`, `invariant`/`conserved` in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` and `Mathlib/AlgebraicGeometry/EllipticCurve/`  →  **ZERO hits** for `invarNum`/`invarDenom` anywhere in mathlib; zero "invariant/conserved" lemmas in the EDS file
[E] Name pattern      `normEDS_two`, `_normEDS_two`, `invar*` in the upstream EDS file  →  upstream HAS `normEDS_zero/one/two/three/four` (the value building blocks) but NO `invar*` of any kind

Searched for both:
  - the user's current form (`invarNum (normEDS b c d) 1 2 = …`) — absent; its
    very subject `invarNum` is absent from mathlib.
  - the literature-standard form (the EDS invariant / conserved quantity) —
    absent: mathlib's EDS file defines `IsEllSequence`, `IsDivSequence`,
    `IsEllDivSequence`, `preNormEDS`, `normEDS` and the `normEDS_k` evaluations,
    but has **no notion of the invariant `I_n`** at all.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard
invariant form). Mathlib *does* have the **building blocks for the value** —
`normEDS_zero` (=0), `normEDS_one` (=1), `normEDS_two` (=b), `normEDS_three` (=c),
`normEDS_four` (=d·b) — but it has neither `invarNum` nor any invariant lemma,
so the *statement* `invarNum … = …` is not expressible against pure mathlib.

---

## Call sites — `invarNum_normEDS_two`

Internal use count (NagellLutz `.lean`, excluding the declaring line 976): **1**
External-to-file callers (within NagellLutz): **1 — itself** (same file, the
consumer is 511 lines below the declaration).

| Caller file:line | Usage pattern (one-line excerpt) |
|---|---|
| `LutzNagell/EllipticDivisibilitySequence.lean:1487` | `convert invar_normEDS 1 m (2 : ℤ) <;> simp only [invarNum_normEDS_two, invarDenom_normEDS_two]` — inside `private lemma invar₂_normEDS_of_mem_nonZeroDivisors`, the base case pinning the invariant constant to `d + b⁴` |

Cross-project note (consolidation duplication, per CLAUDE.md): the **HasseWeil**
project carries a *parallel fork* of this same file with its **own copy** of the
lemma —
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:612`
(declaration) used at its own line 971. That is duplicated source from the same
upstream author (David Angdinata), **not** a downstream consumer of NagellLutz's
lemma. It does not raise the genuine internal-use count; it is itself a candidate
for dedup on `main`.

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`invarNum_normEDS_two`?): (none — the only places this value is needed are the
single NagellLutz call site and the HasseWeil duplicate).

Call-sites signal: **K = 1 internal use** (one site only), with no external
consumers and a sibling duplicate fork → per the Phase-6 table this leans toward
**NO-composable / inline**: the lemma is a single-use computation, not a
load-bearing API surface.

---

## Composition check (Phase 6)

Can `invarNum_normEDS_two` be obtained without a standalone lemma?

Attempt 1 (pure mathlib): **impossible as stated.** The statement mentions
`invarNum`, which is not a mathlib declaration. There is no mathlib expression
whose normal form *is* `invarNum (normEDS b c d) 1 2`, so there is nothing for a
pure-mathlib composition to equal. → fails at the level of the statement, not the proof.

Attempt 2 (the real composition — project def + mathlib building blocks): unfold
the **project-local** `invarNum` definition, then close with mathlib's `normEDS`
evaluations and `ring`:
```lean
example : invarNum (normEDS b c d) 1 2 = (d + b ^ 4) * b := by
  simp only [invarNum, normEDS_zero, normEDS_one, normEDS_two,
    normEDS_three, normEDS_four]   -- normEDS_{0..4} are upstream mathlib lemmas
  ring
```
  - Decls used: project-local `invarNum` (1 unfold) + mathlib `normEDS_zero/one/two/
    three/four` + `ring`. Effectively the existing proof
    `simp [invarNum, right_distrib, ← pow_succ, ← pow_add]`.
  - Result: **succeeds** — it is a 2-step (`simp only` + `ring`) unfold-and-normalise.
  - Notes: this is a *definitional unfolding of a project-local symbol* followed
    by a ring computation. It composes ≤3 steps, but it is NOT a "pure mathlib
    composition" — it necessarily routes through the project's own `invarNum`.

Conclusion: **COMPOSABLE** (as an unfold-and-`ring` over the project's `invarNum`
plus mathlib's `normEDS_k` evaluations). It carries no standalone mathematical
content beyond "evaluate the local definition at fixed indices."

---

## Verdict: `invarNum_normEDS_two`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the *invariant* of an EDS is a real named object
  (Ward/Hone–Swart/Stange), but the **value of its numerator at `n=2`** is never
  isolated as a named result — it is an intermediate base-case computation.
- Generality analysis (Phase 4): MAXIMALLY GENERAL on its ring, but a fixed-index
  SPECIALISATION by construction; no modern-idiom improvement (4c all `no`).
- Mathlib search (Phase 5): not in mathlib; moreover its subject `invarNum` is
  entirely absent from mathlib. The building blocks for the *value*
  (`normEDS_{0..4}`) are present.
- Composition check (Phase 6): COMPOSABLE — `simp only [invarNum, normEDS_*] ;
  ring`, a ≤3-step unfold over the project-local definition.

**Rationale:**

`invarNum_normEDS_two` is not a candidate for mathlib in its own right. It is a
one-line `simp` evaluation of the project-local `invarNum` at the single index
pair `s=1, n=2`, producing the concrete value `(d+b⁴)·b`. Three independent
signals converge on NO-composable. (i) Its subject, `EllSequence.invarNum`, does
not exist in mathlib at all — so the lemma cannot "already be in mathlib," and
its statement is not even expressible against pure mathlib; the natural home of
any such evaluation is *next to* `invarNum`, and `invarNum` itself was assessed
BORDERLINE (its mathlib-worthiness is the open question, not this leaf's).
(ii) The literature names the *invariant* `I_n`, never the value of its numerator
at a specific term; this lemma is the textbook intermediate computation, with no
standalone theorem-status in the field. (iii) It has exactly one internal call
site (line 1487, the `n=2` base case pinning the constant `d+b⁴`) and no external
consumers — only a duplicate copy in the HasseWeil fork, which is itself dedup
fodder. The proof is a 2-step unfold-and-`ring`. Such a glue/evaluation lemma is
inlined at its single use site, or kept as a trivial private `@[simp]` companion
of `invarNum` — it is never shipped to mathlib as a standalone result.

A note on cost: the verdict is not driven by any "too expensive to generalise"
consideration (which would force BORDERLINE) — the lemma is trivially cheap; it
is driven by the *absence of standalone API value* and the *absence of the
subject from mathlib*.

**WHY not (refactor-actionable):**
Mathlib has the building blocks for the numeric value — the upstream evaluations
`Mathlib.NumberTheory.EllipticDivisibilitySequence.normEDS_zero/one/two/three/four`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:298–314`) — but it does
**not** have `invarNum`, and the value follows from those building blocks plus
one definitional unfold by a `simp only … ; ring`. No new mathlib lemma is
warranted; the right action is to inline (or keep private next to `invarNum`).

Mathlib building blocks:
`Mathlib.NumberTheory.EllipticDivisibilitySequence.normEDS_zero`,
`…normEDS_one`, `…normEDS_two`, `…normEDS_three`, `…normEDS_four`
(all in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`), composed with
the project-local `invarNum` unfold and `ring`.

Composition sketch (≤3 lines):
```lean
-- in place of `simp only [invarNum_normEDS_two, invarDenom_normEDS_two]` at the call site:
simp only [invarNum, invarDenom, normEDS_zero, normEDS_one, normEDS_two,
  normEDS_three, normEDS_four]
ring
```

Call sites in this project (from Phase 6.0): **K = 1**
(`EllipticDivisibilitySequence.lean:1487`, inside
`invar₂_normEDS_of_mem_nonZeroDivisors`).

Refactor plan:
- This decl's *fate is coupled to the parent `invarNum`* (assessed BORDERLINE).
  - If the project keeps `invarNum` as project-local API: keep
    `invarNum_normEDS_two` too, but consider marking it `private` (its only
    consumer is 511 lines below in the same file) or folding its content into
    the `simp only` at line 1487 (the composition sketch above) and deleting the
    standalone lemma. Either way it does **not** go to mathlib on its own.
  - If `invarNum` is ever upstreamed: this evaluation ships *with it*, in the
    same PR, as a trivial `@[simp]` evaluation companion (alongside
    `invarNum_normEDS` and `invarDenom_normEDS_two`) — never as a standalone
    feature PR.
- Cross-project dedup (separate `main` cleanup ticket): the HasseWeil twin
  (`HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:612`) and this
  declaration are duplicate source; they should be unified into one shared copy
  during consolidation.

**Next action:** do not PR to mathlib. Inline the composition at the single call
site (line 1487), or keep the lemma private next to `invarNum`; resolve its real
status only when the parent `invarNum` BORDERLINE question is answered, and
dedup the HasseWeil twin on `main`.

---

## Next step

Do not submit to mathlib. Inline the 2-line `simp only [invarNum, normEDS_*]; ring`
composition at `EllipticDivisibilitySequence.lean:1487`, or keep
`invarNum_normEDS_two` as a private companion of the project-local `invarNum`.
Its mathlib fate is inherited from the parent `invarNum` (BORDERLINE); on its
own it is a single-use, unfold-and-`ring` evaluation with no standalone API value.
Separately, dedup the identical HasseWeil-fork copy during `main` consolidation.
