# /mathlibable report — `EllSequence.rel₄_of_anti_oddRec_evenRec`

## Verdict: **YES-add-as-is**

> One-line rationale: load-bearing inductive engine that discharges a standing mathlib TODO (`normEDS` is elliptic); not in mathlib in any form; right generality (`CommRing`); not composable.

---

### Baseline (Phase 0)
- lake build:               not run (task: local build stale) — reasoned from source; decl elaborates in the green project per CLAUDE.md
- decl `EllSequence.rel₄_of_anti_oddRec_evenRec`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:477`
- kind:                      theorem
- has sorry:                 no (file has 0 `sorry`/`admit`)
- qualified name:            **`EllSequence.rel₄_of_anti_oddRec_evenRec`** (inside `namespace EllSequence`, opened L90; VERIFIED)
- module docstring summary:  Elliptic divisibility sequences — defines EDS, constructs `normEDS`, and (in this forked/extended copy) **proves** `normEDS` is an elliptic divisibility sequence and the converse classification.

Note on project context: this file FORKS and EXTENDS mathlib's
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. The mathlib original has the
*definitions* (`IsEllSequence`, `normEDS`, `preNormEDS`, …) and two open TODOs; this file
adds the entire `addMulSub`/`rel₄`/`net`/`Rel₄OfValid` machinery that **closes** those TODOs.

---

### Statement (Phase 1)

`rel₄_of_anti_oddRec_evenRec` states: let `R` be a commutative ring and `W : ℤ → R` a
sequence. Suppose

- `W 1` and `W 2` are non-zero-divisors (`W 1 ∈ R⁰`, `W 2 ∈ R⁰`);
- `W` satisfies the **odd recurrence** for every `m ≥ 2`:
  `OddRec W m : W(2m+1)·W(1)³ = W(m+2)·W(m)³ − W(m−1)·W(m+1)³`;
- `W` satisfies the **even recurrence** for every `m ≥ 3`:
  `EvenRec W m : W(2m)·W(2)·W(1)² = W(m)·(W(m−1)²·W(m+2) − W(m−2)·W(m+1)²)`.

Then for **all** integers `a b c d`, `Rel₄OfValid W a b c d` holds — i.e. whenever the
quadruple has the same parity (`HaveSameParity₄`) and is nonnegative-strictly-decreasing
(`StrictAnti₄ : 0 ≤ d < c < b < a`), the four-index elliptic relation vanishes:
`rel₄ W a b c d = 0`, where
`rel₄ W a b c d = addMulSub(a,b)·addMulSub(c,d) − addMulSub(a,c)·addMulSub(b,d) + addMulSub(a,d)·addMulSub(b,c)`
and `addMulSub(m,n) = W((m+n).tdiv 2)·W((m−n).tdiv 2)`.

For same-parity indices this is precisely the classical Ward/Stange four-term elliptic
relation `h_{a+b}h_{a−b}h_{c+d}h_{c−d} = h_{a+c}h_{a−c}h_{b+d}h_{b−d} − h_{b+c}h_{b−c}h_{a+d}h_{a−d}`.

In words: **the two single-index recurrences (which define odd/even terms of a normalised EDS)
algebraically force the entire highly-symmetric four-index elliptic relation.** This is the
key implication that makes "standard EDSs are elliptic" provable purely algebraically.

- Conclusion (math): single-index recurrences + non-zero-divisor first terms ⟹ full
  four-index elliptic relation on every valid quadruple.
- Conclusion (Lean): `∀ ⦃a b c d : ℤ⦄, Rel₄OfValid W a b c d`.

Proof shape (L479–505): `Int.strongRec` on the largest index `a` (base `a < 6` vacuous via
`six_le_of_strictAnti₄`); the step reduces to the "minimal" case `c = cMin a`, `d = dMin a`
via `rel₄_of_min₂`, then splits on `a' < a` (IH), `b + 2 < a'` (the `transf` averaging trick +
IH), and the boundary `b + 2 = a'` (closed by `oddRec`/`evenRec` through
`rel₃_iff₄`/`rel₄_iff_evenRec`). The reductions `rel₆_eq₃`, `rel₆_eq₃'`, `rel₆_eq₁₀`,
`addMulSub_sq_mul_rel₄_eq₉` are the algebraic syzygies feeding it.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is the central engine of a `## Main statements` result (`isEllDivSequence_normEDS`)
and the algebraic content of a named classical theorem (Ward/Stange: EDSs satisfy the elliptic
relations). Literature width run EXHAUSTIVE regardless.

### One-line check (Phase 2b)

n/a — kind is `theorem` (≈30-line strong-induction proof), not a `def`/`abbrev`. Not a one-liner.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific) | EDS four-term relation Ward Stange elliptic nets `W(m+n)W(m-n)` | yes | `h_{a+b}h_{a−b}h_{c+d}h_{c−d}=h_{a+c}h_{a−c}h_{b+d}h_{b−d}−h_{b+c}h_{b−c}h_{a+d}h_{a−d}`, `a>b>c>d≥0` | Wikipedia EDS; Stange elliptic-nets — **exactly** the `rel₄`/`StrictAnti₄` form |
| 2 | WebSearch (general/idiom) | mathlib normEDS IsEllSequence proof PR Angdinata | yes | mathlib has defs + TODO "prove `normEDS` satisfies `IsEllDivSequence`" | confirms the gap; surfaces source paper arXiv 2604.05280 |
| 3 | WebSearch (named-after/aliases) | arXiv 2604.05280 four-index relation net Stange induction proof | yes | paper defines `E(a,b,c,d)` for `a>b>c>d≥0`, "equivalent to Stange's elliptic net axiom"; "standard EDSs are elliptic ... purely algebraic ... intricate implications among elliptic relations" | **the source paper** (Junyan Xu) — directly describes this implication-theorem |
| 4 | ChatGPT MCP | standard-form / generality of the implication-theorem | n/a | — | MCP down (Codex exec failed), as task warned; compensated by arXiv fetch + WebSearch ×5 |
| 5 | Local references | `projects/NagellLutz/.mathlib-quality/references/`, `refs/` | n/a | absent | neither dir exists on this checkout |
| 6 | nLab | elliptic divisibility sequence / elliptic net | n/a | — | nLab has no dedicated EDS/elliptic-net page; concept lives in NT literature, covered by #1–3 |
| 7 | nCatLab | — | n/a | — | not a categorical concept |
| 8 | Stacks Project | — | n/a | — | not in Stacks scope (no EDS/division-polynomial recurrence theory) |
| 9 | MathOverflow / MSE | EDS elliptic relation generality commutative ring | partial | classical sources use ℤ; Xu generalises to arbitrary commutative ring | generality dimension confirmed (see summary) |
| 10 | arXiv (last 5y) | "On Elliptic Sequences over Commutative Rings" (2604.05280), abstract fetched verbatim | yes | "elliptic sequences over a commutative ring ... 4-parameter ... homogeneous quartic relations ... elliptic relations"; algebraic proof EDSs are elliptic; "results ... in a pull request to Lean's Mathlib in the file EllipticDivisibilitySequence.lean" | **definitive**: the project IS this paper's formalization, mathlib-bound |

Protocol pass: WebSearch ran 5 distinct queries across generality levels; local refs/nLab/
nCatLab/Stacks/MathOverflow/arXiv each checked or `n/a`-with-reason; only ChatGPT MCP was
unavailable (infra, not skipped by choice) and was compensated by the arXiv source fetch.

### Literature summary (Phase 3)

Concept identified as: **the four-index (four-term) elliptic relation of Ward/Stange** —
in Xu's terminology the *elliptic relations* `E(a,b,c,d)`; the theorem itself is the
*algebraic implication* "single-index EDS recurrences ⟹ all elliptic relations" (the
algebraic heart of "standard EDSs are elliptic", Xu arXiv 2604.05280).
Sources agree on the standard form of the *relation*: yes (Ward 1948, Stange 2007/2011, Xu 2026).
Most general standard form: the relation holds over an **arbitrary commutative ring** (Xu's
explicit setting); classical sources (Ward) restrict to ℤ. The Lean decl uses `[CommRing R]`
— the most general standard setting.
Generality dimensions where the literature varies:
  - coefficient ring: ℤ (Ward) → arbitrary commutative ring (Xu) — **Lean is at the general end**.
  - hypothesis packaging: Xu derives ellipticity from the recurrences; the "non-zero-divisor"
    side-conditions (`W 1, W 2 ∈ R⁰`) are exactly the commutative-ring generalisation of Ward's
    field/ℤ setting (no division available, so non-zero-divisor is the right weakening).
Disagreement with the literature: none. The *implication-as-a-named-standalone-theorem* is
specific to this algebraic treatment (Xu / the formalization); the classical literature proves
ellipticity analytically (Weierstrass σ). That is exactly the contribution.

---

### Generality analysis — `EllSequence.rel₄_of_anti_oddRec_evenRec`

Literature-standard form (Phase 3): four-index elliptic relation over an arbitrary commutative
ring, derived from the single-index recurrences for a normalised EDS.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring (Xu); ℤ (Ward) | NO | already the maximal standard generality; the building blocks are quartic polynomial identities over a comm ring |
| 2 | `W : ℤ → R` | ℤ-indexed sequence | ℤ-indexed (EDS) / ℤⁿ (elliptic nets) | n/a | ℤ-indexed is the EDS standard; the net/ℤⁿ generalisation is a *different* object, out of scope for this decl |
| 3 | `W 1 ∈ R⁰`, `W 2 ∈ R⁰` | first two terms non-zero-divisors | non-vanishing (field) / the comm-ring analogue | NO | this **is** the comm-ring weakening of "first terms nonzero"; cannot be dropped (needed to cancel the `addMulSub` coefficient via `mem.2`) |
| 4 | `oddRec`/`evenRec` hypotheses | the two single-index recurrences | same | NO | these are the defining recurrences; they are the minimal input |
| 5 | `StrictAnti₄`/`HaveSameParity₄` (inside `Rel₄OfValid`) | `0≤d<c<b<a`, same parity | `a>b>c>d≥0` (Ward/Xu/Stange) | NO | identical to the literature's index constraint |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.**
Number of weakening opportunities found: 0.
The coefficient ring is already an arbitrary commutative ring (the source paper's setting), the
index constraints match the literature verbatim, and the non-zero-divisor hypotheses are the
correct commutative-ring weakening of the classical nonvanishing condition. Cost of any
restatement: n/a (none warranted).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
| 1 | bundled hyps → typeclasses? | no | the recurrence hypotheses are genuine predicates on a specific `W`, not a reusable structure | — |
| 2 | sequences → filters/topology? | no | this is a finite algebraic identity (commutative-ring polynomial syzygy); no limit/topology to filter-ise | — |
| 3 | construction → universal property? | no | it's a relation-vanishing theorem, not a construction | — |
| 4 | set+closure → bundled substructure? | no | no substructure involved | — |
| 5 | vector-space/field → module/ring? | **already done** | the decl is already stated over an arbitrary `CommRing` with non-zero-divisor side-conditions — the Bourbaki-2.0 weakening from Ward's ℤ/field setting | full comm-ring API; `IsReduced`/non-zero-divisor lemmas apply |
| 6 | 1-categorical → higher? | no | n/a | — |
| 7 | concrete index → general additive structure? | no | ℤ-indexing is intrinsic to the EDS recurrence (parity, `2m+1`/`2m`); ℤⁿ "elliptic nets" is a separate object, not a generalisation of *this* theorem | — |

Modern idiom available: **no** (the modernisation — comm-ring + non-zero-divisors instead of
ℤ/field — is **already present** in the current statement). One-line reason: the decl is itself
the contemporary algebraic formulation the source paper champions; there is no further idiom move.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `EllSequence.rel₄_of_anti_oddRec_evenRec`

[A] mathlib docs (master) — searched `EllipticDivisibilitySequence.html`: only `IsEllSequence`,
    `normEDS`, `preNormEDS`, `complEDS*` **defs** + value lemmas; **no** theorem that `normEDS`
    is elliptic; page still shows "TODO: prove that `normEDS` satisfies `IsEllDivSequence`". → no hit
[B] Loogle (via web) — `IsEllSequence`/`normEDS`/`rel₄`/`addMulSub`/`StrictAnti` four-index relation → no hit (only the defs surface)
[C] LeanSearch (via web) — "normEDS is an elliptic sequence" → no theorem of that content in mathlib
[D] Grep mathlib src — `grep -r "addMulSub|Rel₄OfValid|of_oddRec_evenRec|rel₄|six_le_of_strictAnti"` over `.lake/packages/mathlib/Mathlib/` → **empty** (none of the machinery exists)
[E] Name pattern — `grep -r "OddRec|EvenRec|StrictAnti₄|HaveSameParity"` → only `Nat.evenOddRec` (an *unrelated* ℕ recursion principle in `Data/Nat/EvenOddRec.lean`); **no** EDS recurrence/relation decls

Searched for both: the user's current form (the inductive engine) **and** the
literature-standard target (`IsEllSequence (normEDS …)`). Neither is in mathlib.

Concluded: **not in mathlib (all 5 methods exhausted, plus the literature-standard form).**
Mathlib has the *definitions* and an *open TODO*; the theorem and its entire supporting
machinery are absent.

---

### Call sites — `EllSequence.rel₄_of_anti_oddRec_evenRec`

Internal use count (NagellLutz, excluding declaring file): effectively part of one tightly-coupled
file; within the file it is consumed at L584 by `rel₄_of_oddRec_evenRec`, which feeds
`IsEllSequence.of_oddRec_evenRec` (L591) → `IsEllSequence.normEDS` (L1212,
mathlib TODO #1) → `IsEllDivSequence.eq_normEDS` (L1277, mathlib TODO #2).

| Caller file:line | Usage pattern |
|------------------|---------------|
| `…/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:584` | `rw [rel₄_of_anti_oddRec_evenRec one two oddRec evenRec (same.abs.perm _ _ same.abs), smul_zero]` |
| `…/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:501` | `rw [rel₄_of_anti_oddRec_evenRec one two oddRec evenRec …]` (a sibling copy in the HasseWeil project — cross-project duplication of the same fork) |
| `…/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:559` | same (an `Original` snapshot copy) |

Inline-derivation grep: none — no consumer re-derives the four-index relation by hand; they all
go through this theorem. Signal: **real, load-bearing API** (it is the unique gateway from the
single-index recurrences to ellipticity), used across ≥2 projects → strong YES lean.

---

### Composition check (Phase 6)

Can `rel₄_of_anti_oddRec_evenRec` be derived from mathlib in ≤3 chained calls? **No.**

Attempt 1: any mathlib EDS lemma → mathlib has **zero** theorems about the elliptic property of
`normEDS` or any `rel₄`; there is nothing to chain. Fails immediately.

Attempt 2: assemble from `ring`/`linear_combination` over the recurrences directly → this is a
≈30-line strong induction (`Int.strongRec`) with a parity-and-order case analysis, the `transf`
averaging reduction, and the syzygy lemmas `rel₆_eq₃/₃'/₁₀`, `addMulSub_sq_mul_rel₄_eq₉`. This is
a genuine proof, the opposite of a ≤3-call composition.

Conclusion: **NOT-COMPOSABLE.**

---

## Verdict: `EllSequence.rel₄_of_anti_oddRec_evenRec`

**Category:** **YES-add-as-is**

**Evidence:**
- Literature (Phase 3): the four-index elliptic relation is the classical Ward/Stange relation;
  the *algebraic implication* "single-index recurrences ⟹ all elliptic relations" is the content
  of Xu, *On Elliptic Sequences over Commutative Rings* (arXiv 2604.05280), whose results are
  explicitly "in a pull request to Lean's Mathlib in the file EllipticDivisibilitySequence.lean".
- Generality (Phase 4): MAXIMALLY GENERAL — arbitrary `CommRing` + non-zero-divisor side
  conditions = the source paper's exact (maximal) setting; Phase 4c found no further modern idiom
  (the modernisation is already baked in).
- Mathlib (Phase 5): not in mathlib under any of 5 methods, for both the engine and the
  `IsEllSequence normEDS` target. Mathlib's file carries the matching open **TODO**.
- Composition (Phase 6): NOT-COMPOSABLE (≈30-line strong induction).

**Rationale:**
Mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` defines `normEDS` and states,
as a standing `## Main statements` TODO, "prove that `normEDS` satisfies `IsEllDivSequence`" (and
the converse). This theorem is the **load-bearing inductive engine** that closes that TODO: it
derives the full four-index elliptic relation on every valid quadruple from just the two
single-index recurrences, and downstream (`of_oddRec_evenRec` → `IsEllSequence.normEDS` →
`IsEllDivSequence.eq_normEDS`) the project proves exactly mathlib's two open goals, sorry-free.
The statement is at mathlib's preferred generality already (arbitrary commutative ring; the
non-zero-divisor hypotheses are the correct commutative-ring weakening of Ward's classical
ℤ/field nonvanishing). It is emphatically not reconstructible by a short composition — it is a
strong induction with a delicate parity/order case split and several quartic-syzygy reduction
lemmas. This is precisely the kind of "redo the classical theory algebraically, at the right
generality" result mathlib wants.

**WHY add it (refactor-actionable):**
- New mathematical content: mathlib currently has the *definitions* of EDS/`normEDS` but **no
  proof that `normEDS` is elliptic** — the named gap is the verbatim file TODO at
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` ("TODO: prove that `normEDS` satisfies
  `IsEllDivSequence`" and "TODO: prove that a normalised sequence satisfying `IsEllDivSequence`
  can be given by `normEDS`"). This theorem is the keystone lemma both TODOs route through.
- Composes with mathlib: once landed, `IsEllSequence (normEDS b c d)` becomes available, which is
  the hypothesis the division-polynomial files (`Mathlib/AlgebraicGeometry/EllipticCurve/
  DivisionPolynomial/*`) and the elliptic-curve group-law development ultimately need; the
  follow-up paper gives "a purely algebraic treatment of division polynomials" on this basis.
- It is the algebraic substitute for the analytic (Weierstrass-σ) proof, so it unlocks the
  characteristic-free / arbitrary-base-ring development that the analytic route blocks.

Proposed mathlib location: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (extend the
existing file — same author lineage, D. K. Angdinata / J. Xu).
Proposed PR title: `feat(NumberTheory): normEDS satisfies IsEllDivSequence (elliptic relations)`.
PR grouping: ship the whole machinery as one (or a small staged sequence of) PR(s) — the
`addMulSub`/`rel₄`/`net`/`Rel₄OfValid` scaffolding, this engine `rel₄_of_anti_oddRec_evenRec`,
`rel₄_of_oddRec_evenRec`, `IsEllSequence.of_oddRec_evenRec`, and the terminal
`IsEllSequence.normEDS` + `IsEllDivSequence.eq_normEDS` belong together; they are individually
meaningless. This decl is **not** an independent unit — its PR grain is "the elliptic-property
proof for `normEDS`". (The HasseWeil and `…Original` copies are duplications of the same fork; a
mathlib landing should let AINTLIB dedupe all three against the upstreamed version.)
Pre-PR checklist:
  - [ ] `/generalise EllSequence.rel₄_of_anti_oddRec_evenRec` — confirm no further weakening
    (Phase 4 says none; verify mechanically).
  - [ ] `/cleanup` the file + decl — naming, golf, mathlib style, the `set_option
    allowUnsafeReducibility`/`attribute [local reducible]` blocks reviewed for upstream taste.
  - [ ] Coordinate with the original author lineage (Angdinata/Xu) — this is their in-flight
    upstreaming; align rather than collide. Confirm the live mathlib PR state for 2604.05280.
  - [ ] Reviewer: pick from recent `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` /
    `Mathlib/AlgebraicGeometry/EllipticCurve/` committers.

---

## Next step

Run `/generalise EllSequence.rel₄_of_anti_oddRec_evenRec` (expected: no change — already maximal),
then `/cleanup` the file, then upstream the **whole elliptic-property block** (not this lemma
alone) to `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, coordinating with the
existing Angdinata/Xu mathlib effort that arXiv 2604.05280 references. The decl directly closes
the file's standing `IsEllDivSequence`-for-`normEDS` TODO.

---

### Sources
- Xu, *On Elliptic Sequences over Commutative Rings*, arXiv:2604.05280 — https://arxiv.org/abs/2604.05280
- Elliptic divisibility sequence — Wikipedia — https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence
- Stange, *Elliptic nets and elliptic curves*, arXiv:0710.1316 — https://arxiv.org/abs/0710.1316
- mathlib `Mathlib.NumberTheory.EllipticDivisibilitySequence` (shows the open TODO) —
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
