# /mathlibable report — `EllSequence.rel₄_iff_evenRec`

Project: NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; elliptic
divisibility sequences). Step-9 mathlibable assessment, single declaration.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; reasoning from source).
- decl `EllSequence.rel₄_iff_evenRec`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:373`
  (inside `namespace EllSequence`, opened L90, closed L597 — qualified name **confirmed**).
- kind:                      lemma (theorem).
- has sorry:                 no.
- module docstring summary:  "Elliptic divisibility sequences (EDS) … constructs normalised
  EDSs from initial terms." File is a **fork/extension of mathlib's upstreamed
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`** (identical header, author D. K.
  Angdinata) carrying a *new* `EllSequence` namespace of four-index elliptic-relation
  machinery (`addMulSub`, `rel₄`, `net`, `OddRec`/`EvenRec`, …).

---

### Statement (Phase 1)

`EllSequence.rel₄_iff_evenRec` states, for `W : ℤ → R` (`R` a commutative ring) and `m : ℤ`:

> The four-index elliptic relation `rel₄ W (2m+1) (2m-1) 3 1 = 0` holds **iff** Ward's
> even-index recurrence `EvenRec W m` holds.

Unfolding the two project-private definitions:

- `addMulSub W a b := W((a+b).tdiv 2) * W((a-b).tdiv 2)`.
- `rel₄ W a b c d := addMulSub(a,b)·addMulSub(c,d) − addMulSub(a,c)·addMulSub(b,d)
  + addMulSub(a,d)·addMulSub(b,c)` — the symmetric three-partition "bracket" / Plücker-like
  quartic in the `W`-values; `= 0` is the four-index elliptic-net relation written so all four
  indices permute freely.
- `EvenRec W m  :⟺  W(2m)·W(2)·W(1)² = W(m)·(W(m-1)²·W(m+2) − W(m-2)·W(m+1)²)` — Ward's
  classical even-term recursion.

So the lemma equates one specific index-specialization of the four-index relation with the
even recurrence.

Variables / typeclasses: `{R : Type u} [CommRing R]`, `W : ℤ → R`, `m : ℤ`.
Hypotheses: none. (`W` is **not** assumed odd, **not** assumed a genuine EDS — the statement
is an unconditional algebraic equivalence.)
Conclusion (math): `rel₄`-at-`(2m+1,2m-1,3,1)` vanishes ⟺ Ward's even recurrence at `m`.
Conclusion (Lean): `rel₄ W (2*m+1) (2*m-1) 3 1 = 0 ↔ EvenRec W m`.

Proof body: rewrite the LHS indices to `(2m+1, 2(m-1)+1, 2·1+1, 2·0+1)`, expand each
`addMulSub`-of-odd via `addMulSub_odd`, then `ring_nf`. I.e. **a polynomial identity after
unfolding** — `unfold + ring`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a helper/bridge `lemma` (not a `def`/`class`, not under `## Main results`, not named
after a person/place). It is the even-index sibling of `rel₃_iff_oddRec` / `rel₃_iff_evenRec`
/ `rel₃_iff₄`. (Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` → one-liner check **n/a**. (The proof is
multi-line anyway.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                         | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | "elliptic divisibility sequence even index recurrence Ward W(2m) doubling formula"            | yes  | `W₂ₙ·W₂·W₁² = W₍ₙ₊₂₎·Wₙ·W₍ₙ₋₁₎² − Wₙ·W₍ₙ₋₂₎·W₍ₙ₊₁₎²` | Wikipedia + Silverman/Stephens lit; the `h₂ₙh₂ = hₙ(h₍ₙ₊₂₎h₍ₙ₋₁₎² − h₍ₙ₋₂₎h₍ₙ₊₁₎²)` normalised duplication form **= the project's `EvenRec`**. |
| 2  | WebSearch (general form)         | "Ward elliptic divisibility sequence recursion formulas odd even W(2n+1) W(2n)"               | yes  | even: `W₂ₙW₂W₁² = W₍ₙ₊₂₎WₙW₍ₙ₋₁₎² − WₙW₍ₙ₋₂₎W₍ₙ₊₁₎²` (n≥3); odd: `W₍₂ₙ₊₁₎W₁³ = W₍ₙ₊₂₎Wₙ³ − W₍ₙ₊₁₎³W₍ₙ₋₁₎` (n≥2) | **Exact match** to project's `EvenRec`/`OddRec`. Ward 1948; four initial values `W₁..W₄`. |
| 3  | WebSearch (named-after / source) | "arxiv 2604.05280 elliptic sequences commutative rings rel₄ four-index relation"             | yes  | `E(a,b,c,d): h₍ₐ₊ᵦ₎h₍ₐ₋ᵦ₎h₍c₊d₎h₍c₋d₎ = h₍ₐ₊c₎h₍ₐ₋c₎h₍ᵦ₊d₎h₍ᵦ₋d₎ − h₍ᵦ₊c₎h₍ᵦ₋c₎h₍ₐ₊d₎h₍ₐ₋d₎` for `a>b>c>d≥0` | **"On Elliptic Sequences over Commutative Rings", J. Xu (arXiv 2604.05280, 2026)** — the *source paper* for this file's `EllSequence` four-index relation = the project's `rel₄`. |
| 4  | ChatGPT MCP                      | self-contained ask: is `rel₄@(2m+1,2m-1,3,1) ↔ EvenRec` a named result or glue?              | n/a  | —                   | **MCP down** (Codex backend error, as warned in brief). Mitigated by #1–#3 + #6 + arXiv source. |
| 5  | Local references                 | `.mathlib-quality/references/` grep                                                           | n/a  | —                   | Directory **absent** for NagellLutz (only `overview/` present). Recorded n/a. |
| 6  | nLab                             | "elliptic divisibility sequence"                                                             | yes  | Ward recurrence; division-polynomial origin | nLab has the EDS notion + Ward recurrence; **no separate "rel₄ ↔ even-recurrence" lemma** (it is an internal manipulation). |
| 7  | nCatLab (categorical)            | —                                                                                            | n/a  | —                   | Not a categorical concept; no higher-categorical content. n/a. |
| 8  | Stacks Project (alg geom)        | —                                                                                            | n/a  | —                   | EDS / Ward recurrences are not in Stacks (not its scope). n/a. |
| 9  | MathOverflow / MSE               | EDS recurrence even-index derivation from elliptic relation                                  | yes  | even/odd recurrence are the standard "doubling" relations | Treated as routine specializations of the elliptic/net relation; **no one cites a named "rel₄ at these indices = even recurrence" theorem**. |
| 10 | recent arXiv (≤5 yr)             | "A recurrence relation for EDS" (2102.07573); Xu 2604.05280; "every Somos-4 is Somos-k"      | yes  | four-index/elliptic-net relations ⇒ the standard recurrences | The four-index relation **is** the modern packaging; the even/odd recurrences are its specializations. |

The protocol passes: WebSearch ran 3 queries at distinct generality (specific even-form,
general odd+even, source paper); local refs / nLab / Stacks / nCatLab / MathOverflow / arXiv
each checked or n/a-with-reason; ChatGPT MCP attempted but backend-down (mitigated).

### Literature summary (Phase 3)

Concept identified as: **Ward's even-index recurrence for elliptic divisibility sequences**
(`EvenRec`), and the **four-index elliptic-net / elliptic relation** (`rel₄`, = Stange's net
relation = Xu's `E(a,b,c,d)`).

Sources agree on the standard form: **yes**. `EvenRec` is verbatim Ward's even recursion
`W₂ₙW₂W₁² = W₍ₙ₊₂₎WₙW₍ₙ₋₁₎² − WₙW₍ₙ₋₂₎W₍ₙ₊₁₎²`. `rel₄` is verbatim the symmetric four-index
elliptic relation of Xu (arXiv 2604.05280) / Stange's elliptic nets.

Most general standard form: the recurrence and the four-index relation are stated over an
arbitrary commutative ring `R` (Xu's setting), `W` indexed by `ℤ` — which is **exactly** the
project's generality (`[CommRing R]`, `W : ℤ → R`, no oddness/EDS hypothesis).

Generality dimensions where the literature varies:
  - coefficient ring: `ℤ` (Ward) → arbitrary commutative ring (Xu, mathlib) — project already
    at the general end.
  - index domain: `ℕ`/`ℤ` — project uses `ℤ`, the general choice.

Disagreement with the literature: **none on the two component notions.** The *equivalence
itself* (`rel₄@(2m+1,2m-1,3,1) ↔ EvenRec`) is **not a named/quotable result anywhere** — it is
the routine "specialize the four-index relation to get the even recurrence" step. The
literature derives the even recurrence *from* the elliptic relation by exactly this kind of
index substitution; no source elevates the equivalence to a citable theorem.

---

### Generality analysis — `EllSequence.rel₄_iff_evenRec`

Literature-standard form (Phase 3): even recurrence + four-index relation over an arbitrary
commutative ring, `W : ℤ → R`, no side hypotheses.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`        | commutative ring  | commutative ring (Xu)    | NO                  | `rel₄`/`EvenRec` are quartic polynomial identities; commutativity is genuinely used by `ring`. Cannot drop to non-comm. |
| 2 | `W : ℤ → R`           | arbitrary `ℤ`-seq | arbitrary `ℤ`-seq        | NO                  | Already maximal: no oddness, no EDS, no divisibility assumed — strictly an algebraic identity. |
| 3 | `m : ℤ`               | free integer      | free integer             | NO                  | Already fully general over `ℤ`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the equivalence as stated — it is hypothesis-
free over an arbitrary commutative ring, matching Xu's generality).
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | typeclasses instead of bundled hyps? | no | — | already typeclass-only (`[CommRing R]`); no bundled "let W be an EDS" preamble (intentionally — it is a pure identity). |
| 2 | filters/topology instead of sequences/metric? | no | — | finite algebraic identity; no analysis. |
| 3 | universal-property class instead of construction? | no | — | it is an `Iff` of two predicates, not a construction. |
| 4 | bundled substructure instead of set+closure? | no | — | n/a. |
| 5 | weaken vector-space/field to module/ring? | no | — | already at arbitrary `CommRing`. |
| 6 | 1-categorical → higher-categorical? | no | — | no categorical content. |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive structure? | no | — | the index `2m+1, 2m-1, 3, 1` and the `tdiv 2` halving are **intrinsically `ℤ`-arithmetic** (parity/odd-even); not generalizable to an abstract additive monoid. |

Modern idiom available: **no**. One-line reason: the lemma is already a hypothesis-free
ring-level identity; there is no contemporary mathlib idiom that reorganizes a concrete
"`rel₄` specialization ↔ Ward even recurrence" bridge — its content *is* the bridge.

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`** (no new definitional equalities or typeclass-search
paths introduced).

---

### Mathlib search-status: `EllSequence.rel₄_iff_evenRec`

[A] Lean-Finder       — (deferred tool unavailable in this env)         n/a: tool not loadable.
[B] Loogle            — (deferred tool unavailable in this env)         n/a: tool not loadable.
[C] LeanSearch        — (deferred tool unavailable in this env)         n/a: tool not loadable.
[D] Grep mathlib src  `EllSequence`, `rel₄`/`rel4`, `EvenRec`, `OddRec`, `addMulSub`,
                       `four.index`, `iff.*[Rr]ec`, `Stange`, `elliptic net`
                       over `.lake/packages/mathlib/Mathlib/`                 **no hits** (zero).
[E] Name pattern      same terms, namespace-aware over the whole mathlib tree  **no hits**.

Searched for both:
  - user's current form (`rel₄ … ↔ EvenRec`) — **absent**.
  - the literature-standard components — mathlib's
    `Mathlib.NumberTheory.EllipticDivisibilitySequence` has **only** `IsEllSequence` (the
    single bundled three-index relation `W(m+n)W(m-n)W(r)² = …`), `IsDivSequence`,
    `IsEllDivSequence`, `preNormEDS`, `normEDS`. **No** `addMulSub`, **no** `rel₄`/four-index
    relation, **no** `net`, **no** `OddRec`/`EvenRec`, **no** `*_iff_*Rec` bridge lemmas.

Concluded: **not in mathlib** (grep methods D+E exhausted over the pinned mathlib tree, for
both the user's form and the underlying `rel₄`/`EvenRec` notions). Neither side of the `Iff`
exists in mathlib as a named object, so the equivalence cannot be there either.

Note on the project's own forks (per task brief): the duplicate copies live at
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:294` and
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:355` — these are
**sibling project files, not mathlib**, so they don't count as "mathlib has it" (they are the
same upstreaming-bound development, flagged separately for dedup).

---

### Call sites — `EllSequence.rel₄_iff_evenRec`

Internal use count (this project, excluding the declaring file): **0**.
Within the declaring file `EllipticDivisibilitySequence.lean`: **1** real consumer —
`:504  convert (rel₄_iff_evenRec W (m + 1)).mpr …` inside the `Rel₄OfValid` /
`rel₄_of_anti_oddRec_evenRec` induction that powers `IsEllSequence.of_oddRec_evenRec`
(the bridge that ultimately proves `normEDS` is an elliptic sequence).

| Caller file:line | Usage pattern |
|------------------|---------------|
| `EllipticDivisibilitySequence.lean:504` | `convert (rel₄_iff_evenRec W (m + 1)).mpr (evenRec _ ?_) using 2` |

Sibling-fork callers (same role, other files — not separate consumers):
`HasseWeil/.../EllipticDivisibilitySequence.lean:418`,
`NagellLutz/.../EllipticDivisibilitySequenceOriginal.lean:482`.

Inline-derivation grep (was the equivalence re-derived elsewhere without this lemma?):
(none — the only derivations are the three fork copies of the lemma itself.)

Signal: `K = 0` external-to-file, **1 essential in-file consumer**. It is real glue inside the
`oddRec`/`evenRec` ⇒ elliptic-relation machinery — not dead code, but its meaning is
inseparable from the surrounding `rel₄`/`EvenRec` API; it has no independent life.

---

### Composition check (Phase 6)

Can `rel₄_iff_evenRec` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: state it via existing mathlib decls.
  - Mathlib decls available: only `IsEllSequence` (a bundled three-index `Prop`).
  - Result: **fails at the statement level.** The lemma's *vocabulary* — `rel₄`, `addMulSub`,
    `EvenRec` — does not exist in mathlib. There is nothing to compose: you cannot even *write*
    the LHS/RHS using mathlib names. Mathlib provides no four-index `rel₄`, no `addMulSub`
    halving bracket, no `EvenRec` predicate.

Attempt 2: derive `EvenRec` from `IsEllSequence` instead.
  - That is a *different* lemma (`IsEllSequence → EvenRec`, the project's `evenRec`), not this
    `rel₄ ↔ EvenRec` equivalence, and it still needs the project's `rel₃`/`rel₄` defs.
  - Result: not this statement.

Conclusion: **NOT-COMPOSABLE from mathlib.** Both sides of the `Iff` are project-private
notions absent from mathlib; no 1–3 mathlib-call composition can express, let alone prove, it.
(Within the *project* it is a one-shot `unfold + ring`, but that uses project defs, not
mathlib primitives — so it is not a mathlib composition.)

---

## Verdict: `EllSequence.rel₄_iff_evenRec`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): both components are textbook-standard (Ward's even recurrence;
  Stange/Xu four-index elliptic relation), over an arbitrary commutative ring — but the
  *equivalence itself is not a named/quotable theorem*; it is the routine "specialize the
  four-index relation to the even recurrence" step. Source paper: arXiv 2604.05280 (Xu, 2026).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (hypothesis-free over `CommRing`,
  matching the literature/Xu generality); no modern-idiom reformulation available.
- Mathlib search (Phase 5): **not in mathlib** — mathlib's EDS file has only `IsEllSequence`/
  `normEDS`; **no** `rel₄`/`addMulSub`/`EvenRec`/`net`/`*_iff_*Rec` API whatsoever.
- Composition check (Phase 6): **NOT-COMPOSABLE** — both sides are project-private; mathlib has
  no vocabulary to express the statement.

**Rationale.**
This is a **glue/bridge lemma**, not a standalone contribution. It asserts that one specific
index-specialization of the project's four-index relation `rel₄ W (2m+1) (2m-1) 3 1 = 0` is
equivalent to Ward's even recurrence `EvenRec W m`; the proof is `unfold + ring_nf`, a pure
polynomial identity with no hypotheses on `W`. It is the even-index sibling of the file's
`rel₃_iff_oddRec` / `rel₃_iff_evenRec` / `rel₃_iff₄` family, and it exists solely to feed the
`rel₄_of_anti_oddRec_evenRec` induction that proves `normEDS` is an elliptic sequence (its one
in-file consumer at L504).

It is genuinely **not in mathlib** (Phase 5) and genuinely **not composable from mathlib**
(Phase 6: mathlib lacks `rel₄`, `addMulSub`, and `EvenRec`), so the two NO buckets are both
**wrong**. But it is *also not a YES-as-is*: shipping this single `Iff` to mathlib in isolation
is meaningless — it is only intelligible *as part of* the whole `EllSequence` four-index-
relation development (the `addMulSub`/`rel₄`/`net`/`OddRec`/`EvenRec`/`Rel₄OfValid` API that
formalizes Xu's arXiv 2604.05280 / Stange's elliptic nets). **That surrounding API is the real
mathlib-worthy unit**, and it is *already an active upstreaming-bound development* (this file is
an explicit fork of mathlib's `EllipticDivisibilitySequence`, with an `…Original.lean` prior
version and a parallel HasseWeil copy — classic pre-PR staging). Whether `rel₄_iff_evenRec`
"belongs in mathlib" is therefore a **packaging judgment about the parent API**, not a property
of this lemma — which is exactly what BORDERLINE is for. The generality cost is not the issue
(it is already maximal); the unit-of-contribution is.

A note on why not BORDERLINE-by-cost: cost plays no role here — the lemma is one line and
maximally general. The borderline is purely about *grain* (lemma vs. the API it lives in) and
*timing* (the parent development's mathlib trajectory).

**Numbered questions for the human (≤5):**

1. Is the whole `EllSequence` four-index-relation API (`addMulSub`, `rel₄`, `net`, `OddRec`/
   `EvenRec`, `Rel₄OfValid`, `rel₃_iff₄`, …) intended to be PR'd to mathlib as the
   formalization of Xu's *On Elliptic Sequences over Commutative Rings* (arXiv 2604.05280)? If
   **yes**, `rel₄_iff_evenRec` ships **with that PR as supporting API** (→ effectively
   YES-add-as-is, but *only as part of the bundle*, never standalone).

2. If that API is **not** mathlib-bound (kept as a project-local tool to prove `normEDS` is an
   EDS / for Nagell–Lutz), then this lemma stays project-internal and is **out of scope** for a
   mathlib PR (→ effectively NO, by "supporting infrastructure for a project goal").

3. Naming/packaging: when the bundle goes up, should `rel₄_iff_evenRec` + `rel₃_iff_evenRec` +
   `rel₃_iff_oddRec` + `rel₃_iff₄` be grouped as one "elliptic-relation ⇔ recurrence" PR, with
   the `def`s (`rel₄`, `addMulSub`, `net`, `EvenRec`, `OddRec`) landing first?

4. Dedup precondition (independent of mathlib): the **three identical copies** —
   `NagellLutz/.../EllipticDivisibilitySequence.lean:373` (this one),
   `NagellLutz/.../EllipticDivisibilitySequenceOriginal.lean:355`, and
   `HasseWeil/.../EllipticDivisibilitySequence.lean:294` — should be collapsed to one shared
   `Common/` location before any upstreaming. Confirm the canonical copy.

**Next action:** answer Q1/Q2 to fix the bucket (YES-as-part-of-the-API-bundle vs.
NO-project-internal). If the `EllSequence` API is mathlib-bound, re-run `/mathlibable` on the
**parent `def`s first** (`EllSequence.rel₄`, `EllSequence.addMulSub`, `EllSequence.net`,
`EllSequence.EvenRec`) — their verdicts determine this glue lemma's by inheritance — and treat
`rel₄_iff_evenRec` as supporting API shipped in the same PR. Independently, file a dedup ticket
to unify the three copies (Q4).

---

## Next step

Answer Q1/Q2 (is the `EllSequence` four-index-relation API mathlib-bound?) to resolve the
bucket. If yes → assess the parent `def`s with `/mathlibable`; this lemma ships as supporting
API in that bundle. If no → project-internal, out of scope. Either way, dedup the three
identical copies (Q4) first.
