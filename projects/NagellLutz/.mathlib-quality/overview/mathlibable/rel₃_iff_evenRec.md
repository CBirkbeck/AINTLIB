# /mathlibable report — `EllSequence.rel₃_iff_evenRec`

## Verdict: **YES-add-as-is** (ships as part of the EDS-relations batch)

One-line: the even-term elliptic recurrence ⇔ 3-index elliptic relation at `(m+1, m-1, 1)`.
A hypothesis-free ring identity, classical (Ward 1948), and **not in mathlib** —
mathlib's EDS file still lists "prove `normEDS` is an `IsEllDivSequence`" as a TODO,
and this lemma is one of the bricks in that missing proof.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale, per task brief); reasoned from source. Decl elaborates in-project (it is imported by the main theorem below).
- decl `EllSequence.rel₃_iff_evenRec`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:368`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  defines elliptic divisibility sequences (EDS) and constructs normalised EDSs from initial terms (a substantially expanded **fork** of `Mathlib.NumberTheory.EllipticDivisibilitySequence`).

Namespace: opened `namespace EllSequence` at line 90 ⇒ qualified name **`EllSequence.rel₃_iff_evenRec`** (matches the parsed name).

---

### Statement (Phase 1)

`EllSequence.rel₃_iff_evenRec` states, for a sequence `W : ℤ → R` over a commutative ring `R` and any `m : ℤ`:

> The three-index elliptic relation `Rel₃ W (m+1) (m-1) 1` holds **iff** the even-term recurrence `EvenRec W m` holds.

Unfolding the two sides:

- `Rel₃ W (m+1) (m-1) 1` is `W(2m)·W(2)·W(1)² = W(m+2)·W(m)·W(m-1)² − W(m)·W(m-2)·W(m+1)²`
  (the relation `W(a+b)W(a−b)W(c)² = W(a+c)W(a−c)W(b)² − W(b+c)W(b−c)W(a)²` at `a=m+1, b=m−1, c=1`).
- `EvenRec W m` is `W(2m)·W(2)·W(1)² = W(m)·(W(m−1)²·W(m+2) − W(m−2)·W(m+1)²)`.

These two right-hand sides are equal by commutative-ring rearrangement, so the `↔` is a **pure polynomial identity**.

Variables / typeclasses (Lean side):
- `R : Type*` with `[CommRing R]` — the coefficient ring.
- `W : ℤ → R` — the sequence (a plain function; no oddness/normalisation assumed).
- `m : ℤ` — the index.

Hypotheses (Lean side): **none** beyond `[CommRing R]`. No nonzerodivisor, no `W(−n) = −W(n)`, no `W 1 = 1`.

Conclusion (math): the even-index elliptic recurrence at `m` is equivalent to the 3-index elliptic relation at `(m+1, m−1, 1)`.
Conclusion (Lean): `Rel₃ W (m + 1) (m - 1) 1 ↔ EvenRec W m`.

Proof body: `rw [Rel₃, EvenRec]; ring_nf` (with two `attribute [local reducible]` lines on `Nat.rawCast` / `instAddMonoidWithOne` so `ring_nf` normalises the numeral casts — plumbing only, no mathematical content). The `EllipticDivisibilitySequenceOriginal.lean` sibling proves the identical statement with `rw [Rel₃, EvenRec]; ring_nf; simp only [Nat.rawCast]`, confirming it is the same ring identity.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (a corollary/specialisation: it instantiates the general 3-index relation at fixed indices and rewrites to a named recurrence). It is, however, a load-bearing API lemma for the project's **BIG** main result `isEllDivSequence_normEDS`.
(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` ⇒ one-liner check **n/a**. (The proof is a one-liner, but the one-liner heuristic targets `def` bodies, not lemma proofs. A short proof is not a negative signal for a theorem.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | Ward "Memoir on Elliptic Divisibility Sequences" duplication formula recurrence W(2m+1) W(2m) odd even | yes | `h_{2n+1}=h_{n+2}h_n³−h_{n−1}h_{n+1}³` (n≥2); `h_{2n}h_2 = h_n(h_{n+2}h_{n−1}²−h_{n+1}²h_{n−2})` (n≥3) | Exactly the project's `OddRec`/`EvenRec` with `h_1 = 1`. Source: ResearchGate "EDS over Finite Fields"; Wikipedia. |
| 2 | WebSearch (general form) | mathlib EDS Rel₃ EvenRec OddRec rel₄ normEDS IsEllDivSequence | yes (concept) | general elliptic recurrence `W_{m+n}W_{m−n}W_r²=W_{m+r}W_{m−r}W_n²−W_{n+r}W_{n−r}W_m²` | arXiv 2604.05280 "On Elliptic Sequences over Commutative Rings" (2026) and arXiv 2102.07573 "A recurrence relation for EDS" are the modern commutative-ring treatments. |
| 3 | WebSearch (named-after / aliases) | "duplication formula" / "addition formula" elliptic divisibility sequence Stange elliptic nets | yes | same two recurrences; called the **duplication / even-odd recurrences** | Stange, "Formulary for elliptic divisibility sequences and elliptic nets" (math.colorado.edu) — the canonical reference for `rel₄`/`net`. |
| 4 | ChatGPT MCP | (self-contained question on whether the even/odd recurrences are standard + whether the ⇔ is hypothesis-free) | n/a | — | **MCP server down** (Codex exec failed). Compensated with extra WebSearch + direct ring-identity verification (below). |
| 5 | Local references | `.mathlib-quality/references/` (NagellLutz) | n/a | — | Reference PDFs are LOCAL-ONLY/gitignored (`refs/<project>/`), absent in this checkout. Recorded n/a. |
| 6 | nLab | "elliptic divisibility sequence" | n/a | — | Not an nLab topic (not categorical); the abstract content lives in the arithmetic-geometry literature, already covered by #1–3. |
| 7 | nCatLab | — | n/a | — | Not a categorical concept. |
| 8 | Stacks Project | — | n/a | — | EDS recurrences are not in Stacks (number theory / classical sequences, not its scheme-theory scope). |
| 9 | MathOverflow / MathSE | elliptic divisibility sequence even odd recurrence zero-divisor | yes | confirms even-odd recurrence "requires h₁, h₂ not zero-divisors" *to run the sequence forward* | The nonzerodivisor caveat is about **inverting** to recover terms, not about the bare ⇔; matches how the fork isolates nonzerodivisor use in `addMulSub_mem_nonZeroDivisors`. |
| 10 | recent arXiv (≤5 yr) | elliptic sequences commutative rings recurrence 2021–2026 | yes | arXiv 2604.05280 (2026), arXiv 2102.07573 (2021) | These papers generalise EDS recurrences to arbitrary commutative rings — precisely the project's setting (`[CommRing R]`, no field). |

Protocol passes: WebSearch ran ≥3 queries at distinct generality levels (specific duplication formula / general elliptic recurrence / named aliases); ChatGPT MCP attempted (down — substituted with manual identity check + extra channels); local refs checked (n/a, gitignored); nLab/nCatLab/Stacks/MO/arXiv each checked with reasons.

### Literature summary (Phase 3)

Concept identified as: the **even-term (duplication) recurrence** of an elliptic divisibility sequence — Ward (1948), §"Memoir on Elliptic Divisibility Sequences"; the modern commutative-ring framing is Stange's elliptic nets and arXiv 2604.05280 / 2102.07573.
Sources agree on the standard form: **yes** — `h_{2n}h_2 = h_n(h_{n+2}h_{n−1}² − h_{n+1}²h_{n−2})`, identical to `EvenRec W m` (with `W 1 = 1`).
Most general standard form: stated over an arbitrary commutative ring for `W : ℤ → R`. The project's lemma is **even more general than the textbook statement** in one respect: it does NOT assume `W 1 = 1` (it keeps the `W(1)²` factor on the LHS), and it asserts the full **two-way equivalence** with the 3-index relation, not just the forward recurrence.
Generality dimensions where the literature varies:
  - coefficient ring: ℤ (Ward) → arbitrary commutative ring (arXiv 2604.05280; the project) — the project is at the most general end.
  - normalisation: `W 1 = 1` usually assumed in the literature; the project does **not** assume it.
Disagreement with the literature: none. The literature's "zero-divisor" caveat applies to running the recurrence forward, not to this bare ⇔; the project correctly factors that hypothesis out into separate lemmas.

---

### Generality analysis — `EllSequence.rel₃_iff_evenRec`

Literature-standard form (from Phase 3): even-term duplication recurrence over a commutative ring, normally with `W 1 = 1`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]` | commutative ring | comm. ring (often just ℤ) | NO | The statement is a polynomial identity over a commutative ring; `CommRing` is already the minimal structure that makes the formula typecheck (needs `+`, `−`, `*`, `^`). Commutativity is essential (the rearrangement reorders products). |
| 2 | `W : ℤ → R` | arbitrary function | EDS / normalised sequence | already maximal | The lemma assumes **nothing** about `W` — not oddness, not normalisation, not the divisibility property. It is the bare relation⇔recurrence equivalence. Cannot be weakened further. |
| 3 | `m : ℤ` | integer index | integer index | already maximal | Indices are intrinsically ℤ for two-sided sequences. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**.
Number of weakening opportunities found: 0. The lemma already drops the usual `W 1 = 1` normalisation and asks for nothing beyond `CommRing`. It is strictly *more* general than the textbook statement.
Cost of restatement: n/a (no restatement needed).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|-----------|
| 1 | "let X be a foo" preambles → typeclasses? | no | — | Already a bare function + `CommRing`; nothing to bundle. |
| 2 | sequences/metric → filters/topology? | no | — | Finite algebraic identity; no limiting process. |
| 3 | construction → universal property? | no | — | It's an equivalence of two explicit equations, not a construction. |
| 4 | set+closure-predicate → bundled substructure? | no | — | n/a. |
| 5 | vector-space/field-specific → weaken typeclass? | no | — | Already at `CommRing`, the weakest sensible ring class here. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive structure? | no | — | The index ℤ is intrinsic to two-sided EDS; the `+1/−1` offsets and `W(2m)` are ℤ-specific. Generalising the index would lose the content. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a finite commutative-ring polynomial identity stated at the maximal natural generality; there is no contemporary mathlib idiom that reorganises it. One-line reason: an explicit equation⇔equation lemma over `CommRing` with no structure to abstract.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`.** No definitional equalities or typeclass-search paths are introduced.

(For context, the *definitions* this lemma is stated against — `Rel₃`, `EvenRec`, `rel₄`, `addMulSub`, `net` — would each warrant their own Phase 4.5 if assessed; but they are out of scope for this single-decl run.)

---

### Mathlib search-status: `EllSequence.rel₃_iff_evenRec`

[A] Lean-Finder       — (index tool not available in this env)   n/a: compensated by [C]/[D]/live-docs
[B] Loogle            `Rel₃ _ _ _ _ ↔ EvenRec _ _`, `_ ↔ _` over EDS   n/a (tool unavailable); type-pattern would need the project's own `Rel₃`/`EvenRec` which are not in mathlib, so a mathlib-only Loogle cannot match by construction
[C] LeanSearch (via web) "elliptic divisibility sequence even recurrence relation iff"   no hits in mathlib
[D] Grep mathlib src  `EvenRec`, `OddRec`, `rel₄`, `def Rel₃`, `addMulSub`, `def net` over `.lake/packages/mathlib/Mathlib/`   **0 hits** (none of these symbols exist in pinned mathlib)
[E] gh code search (mathlib master) `EvenRec repo:leanprover-community/mathlib4` → **total_count = 0**; `addMulSub …` → **0**; PRs `EllipticDivisibilitySequence Rel`/`EvenRec elliptic` → none
[F] live mathlib4 docs  fetched `Mathlib/NumberTheory/EllipticDivisibilitySequence.html` → confirms NO `Rel₃`/`rel₄`/`EvenRec`/`OddRec`/`net`/`addMulSub`; and `normEDS satisfies IsEllDivSequence` is still listed as a **TODO**.

Searched for both:
  - the user's current form (`Rel₃ … ↔ EvenRec …`) — not in mathlib (the very predicates `Rel₃`/`EvenRec` are absent).
  - the literature-standard form (even-term duplication recurrence) — not in mathlib in any guise. Mathlib's EDS file has `preNormEDS_even`/`normEDS_even` (definitional even-index *unfolding* lemmas for the constructed `normEDS`), which are a different thing: they compute `normEDS`'s value, they do **not** state the Ward even recurrence as an equivalence with the elliptic relation.

Concluded: **not in mathlib** (all available methods exhausted, pinned source + master code-search + live docs, both the user's form and the literature-standard form). Mathlib's EDS development is the *older, smaller* version (66 top-level decls; main EDS theorem unproven); the project file is an expanded fork (200 top-level decls) that supplies exactly this missing apparatus.

---

### Call sites — `EllSequence.rel₃_iff_evenRec`

Internal use count: **1** in this project file outside its own line (line 651), plus mirrored uses in the two sibling forks.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:651` | `lemma evenRec (m : ℤ) : EvenRec W m := (rel₃_iff_evenRec W m).mp (ell _ _ _)` — derives the even recurrence for any elliptic sequence; this `IsEllSequence.evenRec` is in turn consumed (with `oddRec`) to prove the main result `isEllDivSequence_normEDS`. |
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:623` | same (sibling "original" copy). Also used at line 482 via `rel₄_iff_evenRec`. |
| `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:526` | same (HasseWeil's duplicated copy at :291/:526). |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?): the *forward* direction is the only thing consumers need, and they all route through this lemma (`.mp`). No site re-derives the `Rel₃ ⇔ EvenRec` rearrangement inline. (The three copies are the same lemma duplicated across forked files — a dedup target on `main`, not a sign of redundancy.)

Signal: K = 1 *per file* but it is the **sole bridge** from the abstract elliptic relation to the computable even recurrence, and it sits on the critical path to the project's main theorem. Not the "K=1 ⇒ inline it" case — inlining a `ring_nf` over this many monomials at the call site would be ugly and the named lemma documents the Ward recurrence. This is a genuine API lemma.

---

### Composition check (Phase 6)

Can `EllSequence.rel₃_iff_evenRec` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `Iff.rfl` / `by rfl` — fails. The two sides (`Rel₃` and `EvenRec`) are *not* definitionally equal; they are equal only after a nontrivial commutative-ring rearrangement (`ring_nf` over ~6 monomials, including a regrouping of `W(m)·… − W(m)·…` into `W(m)·(… − …)`).
  - Mathlib decls used: none.
  - Result: fails.

Attempt 2: any 1–3 call mathlib composition — fails. The predicates `Rel₃` and `EvenRec` **do not exist in mathlib**, so no mathlib lemma can mention them; the equivalence cannot be a composition of mathlib lemmas. The only "tactic" that closes it is `ring_nf`, which is a general decision procedure, not a cited composition (per the Phase-6 heuristic table, `by …; ring_nf` is "NOT — that's a real proof", albeit a short one).

Conclusion: **NOT-COMPOSABLE** from mathlib. (It IS a one-line *proof*, but it is not a composition of existing mathlib *declarations* — the objects it relates are new.)

---

## Verdict: `EllSequence.rel₃_iff_evenRec`

**Category:** **YES-add-as-is**

**Evidence:**
- Literature search (Phase 3): the even-term recurrence is classical (Ward 1948) and standard (Stange's formulary; arXiv 2604.05280); the project's form is *at or above* the literature generality (commutative ring, no `W 1 = 1`).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — 0 weakening opportunities; no modern-idiom restatement applies.
- Mathlib search (Phase 5): **not in mathlib** — pinned source + master code-search + live docs all negative for both the user's form and the standard form; the predicates `Rel₃`/`EvenRec` themselves are absent and mathlib's EDS main theorem is still a TODO.
- Composition check (Phase 6): **NOT-COMPOSABLE** (the related objects don't exist in mathlib; only a bare `ring_nf` closes it).

**Rationale:**

This lemma is one elementary brick in a development that mathlib *wants but does not have*: a proof that normalised EDSs satisfy the elliptic-divisibility property. Mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence` defines `IsEllSequence`/`normEDS` but explicitly leaves "prove `normEDS` satisfies `IsEllDivSequence`" as a TODO (verified on the live docs page). The NagellLutz/HasseWeil fork is exactly the upstream-bound completion of that TODO (authored by David Angdinata, mathlib's elliptic-curve/division-polynomial maintainer — the file header and the `DivisionPolynomial.*` lineage make the intent plain). Within that development, `rel₃_iff_evenRec` is the named equivalence that turns the symmetric 3-index elliptic relation into the computable even-term recurrence; it is consumed at `IsEllSequence.evenRec` and lands on the critical path to the main theorem. The statement is correct, maximally general (commutative ring, no normalisation assumed), names a textbook concept, and matches the literature exactly.

It is a *small* lemma, but mathlib routinely includes such named specialisation lemmas when (a) they correspond to a classically-named identity and (b) they are reused. Both hold. It should be upstreamed **as part of the EDS-relations group**, not on its own.

**WHY add it:**
- **New content / named gap:** mathlib's EDS file has the definitions but not the relations theory; "prove `normEDS` is `IsEllDivSequence`" is an explicit standing TODO in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. `rel₃_iff_evenRec` (with `rel₃_iff_oddRec`, `rel₄_iff_evenRec`) is precisely the bridge that TODO needs. This is not "searched and didn't find it" — it is filling a named hole.
- **Composes with mathlib:** once `Rel₃`/`EvenRec`/`rel₄` exist upstream, the even/odd recurrences plug straight into `normEDS_even`/`normEDS_odd` and the `DivisionPolynomial` files, letting the EDS-property proof go through and unblocking downstream elliptic-curve results.

Proposed mathlib location:    `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (the existing file — this fork *is* its extension), or a new `Mathlib/NumberTheory/EllipticDivisibilitySequence/Relations.lean` if the file is split.
Proposed PR title:            `feat(NumberTheory): even/odd recurrences for elliptic sequences`
PR grouping (REQUIRED):       Ship together with the rest of the relations apparatus this lemma depends on and sits beside — **`EllSequence.Rel₃`, `EllSequence.rel₄`, `EllSequence.addMulSub`, `EllSequence.net`, `EllSequence.EvenRec`, `EllSequence.OddRec`, `EllSequence.rel₃_iff_oddRec`, `EllSequence.rel₃_iff_evenRec`, `EllSequence.rel₄_iff_evenRec`** (and onward to `isEllDivSequence_normEDS`). This single `↔` lemma is meaningless upstream without the `Rel₃`/`EvenRec` definitions, so it cannot be a standalone PR — it is one line item in the EDS-completion PR series.

Pre-PR checklist before opening:
- [ ] Resolve the three-way duplication first (NagellLutz / NagellLutz-Original / HasseWeil all carry identical copies) — pick the canonical home, likely `Common/`, before upstreaming.
- [ ] `/generalise EllSequence.rel₃_iff_evenRec` — confirm no further weakening (expected: none; already maximal).
- [ ] `/cleanup` the file — note the `set_option allowUnsafeReducibility true` + `attribute [local reducible] Nat.rawCast …` plumbing in the proof; mathlib reviewers will want that justified or replaced (the `Original` copy closes it with plain `ring_nf; simp only [Nat.rawCast]`, which may be the cleaner upstream form).
- [ ] Coordinate with David Angdinata / the existing EDS file owner — this is their development returning home.

---

## Next step

Upstream as part of the **EDS-relations group PR** to `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (with `Rel₃`/`rel₄`/`EvenRec`/`OddRec`/`net`/`addMulSub` and the sibling `rel₃_iff_oddRec`, `rel₄_iff_evenRec`). Do **not** PR this lemma alone — it is one line in the development that discharges mathlib's standing "normEDS is an EDS" TODO. First dedup the three forked copies and run `/cleanup` on the proof's reducibility plumbing.
