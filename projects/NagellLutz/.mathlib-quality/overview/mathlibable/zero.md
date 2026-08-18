# /mathlibable report — `IsEllSequence.zero`

> Step-9 (overview) full mathlibable assessment. One declaration:
> `IsEllSequence.zero`, NagellLutz project.
> Source: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:660`.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); reasoning from source + pinned mathlib tree at `.lake/packages/mathlib`.
- decl `IsEllSequence.zero`: ✓ resolved at `EllipticDivisibilitySequence.lean:660` (inside `namespace IsEllSequence`, opened line 643).
- kind:                      lemma (theorem). Phase 2b one-line check and Phase 4.5 diamond/defeq are **n/a** (not a def/class/instance).
- has sorry:                 no.
- module docstring summary:  Defines elliptic divisibility sequences (EDS) over a commutative ring and builds normalised EDSs from initial terms. This file is a **fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`** (identical copyright header — David Kurniadi Angdinata) with a large block of *new* `IsEllSequence` API the mathlib copy does not have.

Note on the name: the file also has a sibling `IsEllSequence.zero'` at line 653 (the `[IsReduced R]` variant). The decl under assessment is `zero` (line 660), the **non-zero-divisor** variant.

---

### Statement (Phase 1)

`IsEllSequence.zero` states: *the zeroth term of an elliptic sequence vanishes, provided some even term is a non-zero-divisor.*

For a commutative ring `R` and `W : ℤ → R` an **elliptic sequence** (`IsEllSequence W`: for all `m n r : ℤ`, `Rel₃ W m n r`, i.e. `W(m+n)·W(m−n)·W(r)² = W(m+r)·W(m−r)·W(n)² − W(n+r)·W(n−r)·W(m)²`), if `W(2m) ∈ R⁰` (the submonoid of non-zero-divisors) for some `m : ℤ`, then `W 0 = 0`.

```lean
lemma zero (m : ℤ) (mem : W (2 * m) ∈ R⁰) : W 0 = 0 := by
  have := ell m m (2 * m)
  rw [Rel₃, add_comm, sub_self, sub_self, ← two_mul, mul_comm (W _)] at this
  exact mem.2 _ ((pow_mem mem 2).2 (W 0 * W (2 * m)) this)
```

Variables / typeclasses (Lean side):
- `{R : Type*} [CommRing R]` — the coefficient ring (general commutative ring; **not** required to be a domain).
- `{W : ℤ → R}` — the sequence.
- `(ell : IsEllSequence W)` — section hypothesis (`include ell`): `W` satisfies the elliptic relation.

Hypotheses (Lean side):
- `(m : ℤ)` — index of the chosen even term.
- `(mem : W (2 * m) ∈ R⁰)` — that even term is a non-zero-divisor.

Conclusion (math): `W(0) = 0`.
Conclusion (Lean): `W 0 = 0`.

Proof in one line: substitute `(m, m, 2m)` into the relation. LHS becomes `W(2m)·W(0)·W(2m)²`; the two RHS terms are equal (`W(3m)W(−m)W(m)²` each) and cancel to `0`. So `W(0)·W(2m)³ = 0`, and `W(2m)³ ∈ R⁰` (`pow_mem`) forces `W(0) = 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a 3-line helper lemma (first structural fact of the `IsEllSequence` API), not a named theorem, not a new structure, not a `## Main results` entry. (Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)
n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                                | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "EDS W(0)=0 zeroth term Ward memoir definition"                                                 | yes  | "proper EDS: h₀=0, h₁=1, h₂h₃≠0"; W(0)=0 is a normalisation convention | Wikipedia, sciepub Ward 1948 ref, arXiv 1108.3051 |
|  2 | WebSearch (general/derivation)   | "elliptic sequence W(m+n)W(m−n) recurrence W_0=0 normalisation Ward"                            | yes  | **"W₀=0 obtained by setting m=n=1 in the recurrence"**; non-degenerate ⇒ W₀=0; W₋ₙ=−Wₙ | arXiv math/0402415 (sign of an EDS), Wikipedia |
|  3 | WebSearch (named-after / nets)   | "elliptic net W(0)=0 non-degenerate Stange definition integral domain"                         | yes  | **elliptic net W:A→R is *defined* with W(0)=0**, R an integral domain | Stange "Elliptic nets and elliptic curves" arXiv 0710.1316; 1408.6623; 1702.08102 |
|  4 | ChatGPT MCP                      | (standard-form + generality + named? question, ×2 attempts)                                    | n/a  | —                                                                   | **MCP down** (Codex `exec` stdin failure, both attempts) — env brief predicted this; fell back to extra WebSearch + WebFetch (rows 1–3, 9) |
|  5 | Local references                 | `.mathlib-quality/references/` for "Ward" / "elliptic"                                          | n/a  | (directory absent for this project)                                 | no refs dir under `projects/NagellLutz/.mathlib-quality/` |
|  6 | nLab                             | elliptic divisibility sequence / elliptic net                                                   | n/a  | not an nLab topic (no dedicated page)                               | covered by row 3 sources (Stange) instead |
|  7 | nCatLab (if categorical)         | —                                                                                              | n/a  | not a categorical concept                                          | — |
|  8 | Stacks Project (if alg geom)     | —                                                                                              | n/a  | EDS/division-polynomial recurrences are not a Stacks topic         | — |
|  9 | MathOverflow / Math.StackExchange (via WebFetch) | Wikipedia "Elliptic divisibility sequence" full page                            | yes  | EDS defined recursively from W₁..W₄ for n≥1; **W₀ not even mentioned** — i.e. so trivial it is normalised away | confirms W(0)=0 is below the threshold of a stated result |
| 10 | recent arXiv (last 5 years)      | elliptic nets valuations / symmetries (2024 hits)                                               | yes  | same convention: nets *defined* with W(0)=0                         | arXiv 2512.09601, 1909.12654 |

The protocol passes: WebSearch ran 3 distinct queries at different generality levels (specific normalisation form, the derivation/recurrence form, the elliptic-net generalisation); local refs checked (absent → n/a); nLab/nCatLab/Stacks checked and recorded n/a with reasons; MathOverflow-class confirmation via WebFetch of the Wikipedia page; arXiv checked. ChatGPT MCP is genuinely unavailable (two failed invocations logged) and the documented fallback channels were used to cover it.

### Literature summary (Phase 3)

Concept identified as: **the normalisation fact `W₀ = 0` for an elliptic (divisibility) sequence / elliptic net** (Ward 1948; Shipsey; Stange's elliptic nets; Silverman's treatment).
Sources agree on the standard form: **yes** — `W(0) = 0`.
Most general standard form (prose): for an elliptic sequence/net over an **integral domain**, `W(0) = 0`; for elliptic *nets* it is even folded into the *definition*. The universal derivation is "substitute `m = n = 1` (or `m = n`) into the relation."
Generality dimensions where the literature varies:
  - coefficient ring: literature uses **integral domain** (sometimes ℤ specifically); the non-degeneracy assumption `W₁W₂W₃ ≠ 0` is what makes the cancellation valid there.
  - how W(0)=0 enters: **definitional** (elliptic nets) vs. **derived** (elliptic sequences, "set m=n=1").
Disagreement with the literature: **none** mathematically — the project's `W(2m) ∈ R⁰` hypothesis is a *weakening* of "integral domain", giving the exact algebraic content (a single even non-zero-divisor is all the cancellation needs) over a general `CommRing`. No source states `W(0)=0` as a **named theorem**; it is folklore / a normalisation step.

---

### Generality analysis — `IsEllSequence.zero`

Literature-standard form (from Phase 3): `W(0) = 0` for `W` an elliptic sequence over an **integral domain** (non-degenerate).

| # | Parameter / hypothesis        | Current Lean form                         | Literature-standard form              | Weaker than lit? | Reason |
|---|-------------------------------|-------------------------------------------|----------------------------------------|------------------|--------|
| 1 | `[CommRing R]`                | arbitrary commutative ring                | integral domain                        | **MORE GENERAL** | proof only needs one non-zero-divisor, never `NoZeroDivisors`; works over any `CommRing` |
| 2 | `(mem : W (2*m) ∈ R⁰)`        | one even term is a non-zero-divisor       | `W₁W₂W₃ ≠ 0` / domain (every nonzero is a non-zero-divisor) | **MORE GENERAL / weakest sufficient** | exactly the algebraic condition the cancellation `W(0)·W(2m)³ = 0` requires; quantified existentially over `m` |
| 3 | conclusion `W 0 = 0`          | the equality itself                       | same                                   | identical        | — |

The current form is therefore **at-or-above** the literature standard on every axis. The only "narrowing" is that it needs *some* even non-zero-divisor rather than nothing — but over a domain that is automatic, and the sibling `zero'` (`[IsReduced R]`) plus this `zero` together give the `W(0)=0` fact under the two natural weak hypotheses (reduced ring; or one even non-zero-divisor). This is the maximally-general "W(0)=0 over a commutative ring" statement.

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (in fact strictly more general than the integral-domain literature statement).
Number of weakening opportunities found: **0**.
Proposed restatement: none needed.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Downstream |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                                            | no       | `IsEllSequence` is already a predicate (`def … : Prop`); `ell` is its proof, used dot-notation `ell.zero`. Idiomatic. | — |
|  2 | sequences/metric → filters/topological?                                                    | no       | purely algebraic identity over ℤ; no topology. | — |
|  3 | construct an object → universal-property class?                                            | no       | it is a Prop-valued lemma, nothing constructed. | — |
|  4 | set-with-closure-predicate → bundled substructure?                                         | no       | n/a. | — |
|  5 | vector-space/field-specific → weaken typeclass?                                            | **already done** | already `CommRing`, weaker than the literature's integral domain. | full non-zero-divisor `Submonoid` API (`R⁰`) already used. |
|  6 | 1-categorical → higher-categorical?                                                        | no       | n/a. | — |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary group/monoid?                                             | no       | the index is ℤ intrinsically (elliptic sequences are ℤ-indexed; the elliptic-net generalisation to ℤⁿ is a *separate, larger* definition, not a reformulation of this lemma). | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: the statement is already in mathlib's idiom — a `Prop`-predicate (`IsEllSequence`) used via dot-notation, over the weakest reasonable typeclass (`CommRing`) with the non-zero-divisor `Submonoid R⁰`. Nothing to modernise.

---

### Diamond / defeq risk — `IsEllSequence.zero`

n/a — declaration kind is `lemma`. (No definitional equalities or typeclass-search paths introduced.)

---

### Mathlib search-status: `IsEllSequence.zero`

[A] Lean-Finder       not available in this env                                   n/a: deferred tool not surfaced
[B] Loogle            not available in this env                                   n/a: deferred tool not surfaced
[C] LeanSearch        not available in this env                                   n/a: deferred tool not surfaced
[D] Grep mathlib src  `IsEllSequence\.(zero|neg|oddRec|evenRec|rel₄|net|invar)` over `.lake/packages/mathlib/Mathlib/`; full decl-head listing of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`   **no hits — authoritative**
[E] Name pattern      grep `namespace IsEllSequence` / `W 0`/`nonZeroDivisor`/`IsReduced` in the mathlib EDS file   no hits

The index tools (A/B/C) are not surfaced as deferred tools in this environment, so Phase 5 was run by the ground-truth method [D]: a direct grep of the **pinned mathlib source tree** that the project actually builds against. For an *existence* question this is strictly more reliable than the index. Findings:

- Mathlib **has the definition** `IsEllSequence` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:82`) — same definition, same author (David Kurniadi Angdinata).
- Mathlib's `IsEllSequence` namespace contains **only** `isEllSequence_id`, `IsEllSequence.smul`, `IsEllSequence.map` (full decl-head listing confirms it). There is **no** `zero`, `zero'`, `neg`, `oddRec`, `evenRec`, `rel₃`/`rel₄`, `net`, or `invar`.
- Grep of *all of* `.lake/packages/mathlib/Mathlib/` for `IsEllSequence.(zero|neg|oddRec|evenRec|rel₄|net|invar)` → **empty**.

Searched for both forms:
  - user's form (`W(2m) ∈ R⁰ → W 0 = 0`): not present.
  - literature/general form (`W(0)=0` over an integral domain): also not present in mathlib (mathlib never states the bare `W 0 = 0` for an arbitrary `IsEllSequence`; it only proves `normEDS_zero`/`preNormEDS_zero` for the *concrete constructed* sequences).

Concluded: **not in mathlib** (the `IsEllSequence` predicate exists, but this lemma — and the whole extended `IsEllSequence` API around it — does not).

---

### Call sites — `IsEllSequence.zero`

Internal use count: **4** (within NagellLutz; the declaring file itself, but all in *downstream distinct lemmas*, none in the `zero` proof). Excludes the `EllipticDivisibilitySequenceOriginal.lean` backup copy.

| Caller file:line                              | Usage pattern (one-line excerpt)                                  |
|-----------------------------------------------|--------------------------------------------------------------------|
| `EllipticDivisibilitySequence.lean:691`       | `rel₄_of_oddRec_evenRec (ell.neg one two) (ell.zero 1 two) one two` — feeds `IsEllSequence.rel₄` |
| `EllipticDivisibilitySequence.lean:1224`      | `rw [Nat.cast_zero, ellW.zero 1 two, ellU.zero 1 (h2 ▸ two)]` — inside `IsEllSequence.ext` |
| `EllipticDivisibilitySequence.lean:1298`      | `simp [EllSequence.compl, ellW.zero 1 two]` — inside `mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` |
| (`ell.zero 1 two` is the canonical call: `m=1`, so `W 2 ∈ R⁰` is the supplied even non-zero-divisor) | |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `IsEllSequence.zero`?):
  - **YES — cross-project.** `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:530` declares a **byte-identical statement** `lemma zero (m : ℤ) (mem : W (2 * m) ∈ R⁰) : W 0 = 0` with the *same docstring* and a longer-but-equivalent proof. Two AINTLIB projects independently re-derive this exact lemma.
  - Also re-derived inside the NagellLutz file as the sibling `zero'` (`[IsReduced R]` variant, line 653) — same fact, different hypothesis.

Composability signal: **K = 4 internal uses, no inline bypass within the project, plus an identical independent re-derivation in a second project.** Per the Phase-6 table this is a strong **real-API** signal → YES-* bucket. (It is emphatically not dead code or a K≤1 wrapper.)

---

### Composition check (Phase 6)

Can `IsEllSequence.zero` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: cancel via the non-zero-divisor submonoid.
  - The *final* step **is** a mathlib composition: from `W(0)·W(2m)³ = 0` and `W(2m)³ ∈ R⁰` (`Submonoid.pow_mem mem 3`), `mem_nonZeroDivisors_iff` / the submonoid membership predicate (`mem.2`) gives `W 0 = 0`. Two mathlib calls.
  - **But** producing the hypothesis `W(0)·W(2m)³ = 0` requires instantiating the elliptic relation at `(m, m, 2m)` (`ell m m (2*m)`) and rewriting `Rel₃` (a **project-local** definition) with `add_comm/sub_self/← two_mul/mul_comm` so the two RHS terms cancel. That algebra is **not** a mathlib primitive — `Rel₃`/`IsEllSequence`-as-`Rel₃` is project scaffolding, and `ell` is a hypothesis, not a mathlib lemma.
  - Result: **partial** — the cancellation composes from mathlib; the substitution-and-cancel-the-symmetric-terms core does not.

Attempt 2: is there a mathlib lemma about `IsEllSequence` that yields `W 0 = 0` directly? No (Phase 5: mathlib's `IsEllSequence` API is only `smul`/`map`).

Conclusion: **NOT-COMPOSABLE** as a ≤3-call mathlib one-liner. It is a genuine (small) lemma whose content is the `(m,m,2m)` substitution into the elliptic relation; mathlib supplies only the trailing non-zero-divisor cancellation. Crucially, it is a lemma *about a definition mathlib already owns* (`IsEllSequence`), so the natural home is mathlib's own `IsEllSequence` namespace.

---

## Verdict: `IsEllSequence.zero`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): `W(0)=0` is the universal normalisation fact for elliptic sequences/nets (Ward 1948; Stange) — "set m=n=1"; nets are *defined* with W(0)=0. Standard hypothesis is an integral domain; never a *named* theorem.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — over an arbitrary `CommRing` with one even non-zero-divisor, strictly weaker than the literature's integral-domain assumption; 0 weakenings found; no modern-idiom improvement.
- Mathlib search (Phase 5): **not in mathlib.** The `IsEllSequence` *definition* is in mathlib (same author), but its API stops at `smul`/`map`; no `zero` (grep of the pinned tree is conclusive).
- Composition check (Phase 6): **NOT-COMPOSABLE** in ≤3 mathlib calls (only the trailing non-zero-divisor cancellation is a mathlib primitive; the `(m,m,2m)` substitution into the elliptic relation is not).

**Rationale:**

`IsEllSequence` already lives in mathlib (`Mathlib.NumberTheory.EllipticDivisibilitySequence`, authored by David Kurniadi Angdinata — the same author as this fork). What mathlib is **missing** is the *structural API of that predicate*: mathlib proves `W 0 = 0`, `W (-n) = -W n`, etc. only for the **concrete constructed** sequences (`normEDS_zero`, `preNormEDS_neg`, …), never for an *arbitrary* `IsEllSequence`. `IsEllSequence.zero` is the first and most basic such fact — "the zeroth term of any elliptic sequence vanishes" — and it is the gateway lemma the rest of the namespace's API (`neg`, `rel₄`, `net`, `invar`, and the characterisation `IsEllSequence.ext` / `eq_normEDS_of_dvd`) is built on. That this exact lemma is **independently re-derived verbatim in a second AINTLIB project (HasseWeil, line 530)**, and is consumed at 4 internal sites here, is concrete evidence of a real, recurring API gap: people who work with `IsEllSequence` re-prove `W 0 = 0` because mathlib's namespace doesn't offer it.

The statement is at the right generality for mathlib: it deliberately weakens the classical "integral domain" hypothesis to "some even term is a non-zero-divisor" (`W (2*m) ∈ R⁰`), which is the exact algebraic content of the cancellation and works over any commutative ring — paired with the sibling `zero'` for the `IsReduced` case. This is a `lemma` (no diamond/defeq risk, Phase 4.5 n/a) and not a one-liner-without-exemption (Phase 2b n/a). The composition check confirms mathlib's primitives do not give it in ≤3 calls — the substitution-into-the-relation core is genuine content. All four YES-add-as-is evidence gates are satisfied (lit table ≥3 channels; MAXIMALLY GENERAL; no mathlib hit; non-trivial composition).

**WHY add it (refactor-actionable):**
- *New content / the specific gap:* mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` has the `IsEllSequence` predicate but **no general `W 0 = 0` lemma for it** — only `normEDS_zero`/`preNormEDS_zero` for the concrete sequences. The gap is named: the `IsEllSequence` namespace lacks its basic structural facts. The duplicated independent proof in HasseWeil and the `zero'`/`zero` pair locally are the recurring-manual-reformulation evidence the gate asks for.
- *How it composes:* once in mathlib, `IsEllSequence.zero` (with `neg`, `oddRec`, `evenRec`) unlocks `IsEllSequence.rel₄` → `IsEllSequence.net` → `IsEllSequence.invar` (Ward's invariance) and the normalisation characterisation `IsEllSequence.ext` / `eq_normEDS_of_dvd` — i.e. the bridge from "abstract elliptic sequence" to mathlib's existing `normEDS`. None of that downstream API can be stated in mathlib today because `zero` (its base case) is absent.

Proposed mathlib location:    `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (immediately after the existing `IsEllSequence.map`, opening the structural-lemmas section).
Proposed PR title:            `feat(NumberTheory/EllipticDivisibilitySequence): structural API for IsEllSequence (zero, neg, …)`
PR grouping (REQUIRED):       Do **not** ship `zero` alone. It is the base case of one coherent block and should be PR'd together with its siblings from the same `namespace IsEllSequence` (lines 643–702): `zero'` (`[IsReduced]` variant), `neg`, `oddRec`, `evenRec`, `sub_add_neg_sub_mul_eq_zero`, `rel₄`, `net`, `invar` — plus the supporting `Rel₃`/`OddRec`/`EvenRec`/`rel₄` scaffolding they need (which is itself the larger contribution). `zero` is one declaration in that upstreaming batch, which is essentially "upstream the rest of the author's own `IsEllSequence` development."
Pre-PR checklist before opening:
  - [ ] `/generalise IsEllSequence.zero` — confirm no further weakening (already looks maximally general; cheap to double-check the `R⁰` phrasing vs. a bare `mem_nonZeroDivisors` hypothesis).
  - [ ] `/cleanup …EllipticDivisibilitySequence.lean IsEllSequence.zero` — full style/naming/API audit before the PR (the fork carries `lia`/`erw`/`change`-style proofs in places that mathlib review will flag).
  - [ ] De-duplicate against HasseWeil's `IsEllSequence.zero` first (AINTLIB-internal): one project should own it, the other `import`s — this is also a `lane:cleanup` ticket independent of the mathlib PR.
  - [ ] Pick a reviewer from recent `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` / `Mathlib/AlgebraicGeometry/EllipticCurve/` commits (the EDS/division-polynomial author line).

---

## Next step

Open a mathlib PR adding the `IsEllSequence` structural-API block to `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, with `IsEllSequence.zero` as the base lemma shipped alongside `zero'`/`neg`/`oddRec`/`evenRec`/`rel₄`/`net`/`invar` (one coherent PR — see PR grouping). Before that: run `/cleanup` on the block and de-duplicate the identical HasseWeil copy AINTLIB-internally so a single owner remains.
