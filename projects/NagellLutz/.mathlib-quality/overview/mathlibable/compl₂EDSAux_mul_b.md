# /mathlibable report — `compl₂EDSAux_mul_b`

> Project: NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS).
> File: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1025`.
> This project **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence` and
> `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`, so the vendored mathlib
> tree (`.lake/packages/mathlib`) was checked FIRST.

Mode A, single declaration, full workflow. Local Lean build is stale, so this assessment
reasons from the source statement + the vendored mathlib tree, the mathlib index, and a
web literature sweep.

---

### Baseline (Phase 0)

- lake build:               not run (env: local build stale; reasoned from source + vendored mathlib source, per task brief)
- decl `compl₂EDSAux_mul_b`: ✓ resolved at `EllipticDivisibilitySequence.lean:1025`
- kind:                     `lemma` (theorem)
- has sorry:                no (proof: `simp_rw […]; split_ifs <;> ring`)
- qualified name:           **`compl₂EDSAux_mul_b`** — the lemma sits inside `section Complement`
  (opened line 1010) with NO enclosing `namespace`; the nearest `namespace EllSequence` opens at
  1079, *after* this lemma. So the fully-qualified name is the bare base name in the root namespace.
- module docstring summary: EDS / division-polynomial machinery for the Nagell–Lutz theorem; this
  file forks `Mathlib.NumberTheory.EllipticDivisibilitySequence` and adds a `Complement` section
  plus the `ω`-family / reduced-invariant support.

---

### Statement (Phase 1)

`compl₂EDSAux_mul_b` states, for a commutative ring `R`, elements `b c d : R`, and `m : ℤ`:

> `compl₂EDSAux b c d m * b = normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2`.

The project's auxiliary def (line 1016) is

> `compl₂EDSAux b c d m := preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * (if Even m then 1 else b)`,

and `normEDS b c d n = preNormEDS (b⁴) c d n * (if Even n then b else 1)` is the canonical normalised
elliptic divisibility sequence. Mathematically, `compl₂EDSAux` is the **subtrahend term** of the EDS
"duplication / even" recurrence

  W(2m)·W(2) = W(m)·( W(m-1)²·W(m+2)  −  W(m-2)·W(m+1)² ),
                          └─ minuend ─┘     └─ subtrahend ─┘

written at the `preNormEDS` level with the `(if Even m then 1 else b)` parity factor that converts
`preNormEDS (b⁴)…` into `normEDS …`. The lemma says: that subtrahend half, once multiplied by `b`,
is exactly `W(m-2)·W(m+1)²` for the *normalised* sequence `W = normEDS`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (where the EDS lives).
- `(b c d : R)` — the three normalised-EDS parameters (`W₂ = b`, `W₃ = c`, `W₄ = d·b`).
- `(m : ℤ)` — the index.

Hypotheses: none.
Conclusion (math): the subtrahend term of the EDS duplication formula, times `b`, equals `W(m-2)·W(m+1)²`.
Conclusion (Lean): `compl₂EDSAux b c d m * b = normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** — a one-step algebraic-bookkeeping lemma relating a project-internal auxiliary
def to a product of `normEDS` values; not a named theorem, not a `## Main results` entry, no new
structure. (Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def` — the one-liner gate does not apply. (Context note: the *def* it serves,
`compl₂EDSAux`, is itself a one-line `def`; that one-liner's status is the crux — see Phase 6/7.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                   | Hit? | Standard form found              | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "EDS duplication formula W(2m) recurrence division polynomial ψ(m-2)ψ(m+1)²"             | yes  | W₂ₙψ₂ = ψₙψₙ₊₂ψₙ₋₁² − ψₙψₙ₋₂ψₙ₊₁² | arXiv 2102.07573; Stange formulary; eprint 2008/444 — the *full* duplication identity; the two terms are never separately named |
|  2 | WebSearch (general form)         | "normalised EDS W(m) divides W(2m) complement witness Ward recurrence"                   | yes  | W₂ₙW₂ = Wₙ(Wₙ₊₂Wₙ₋₁² − Wₙ₋₂Wₙ₊₁²) | mathlib4 docs; Wikipedia "Elliptic divisibility sequence"; Shipsey/Stange — the literature standard, matching `complEDS₂` |
|  3 | WebSearch (named-after / aliases)| "Ward elliptic divisibility sequence recurrence division polynomial doubling"            | yes  | same as #1/#2 (Ward 1948)        | the recurrence is Ward's; `W(2m)/W(m)` is bundled, its two summands are not individually christened |
|  4 | ChatGPT MCP                      | (MCP down in this env — fallback to #1–#3 + nLab + arXiv)                                | n/a  | —                                | recorded n/a: server unavailable; covered by the three WebSearch generality levels + arXiv |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                  | n/a  | (no `references/` dir)           | only an `overview/` subdir exists under `.mathlib-quality/`; recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "division polynomial"                                 | no   | —                                | nLab has no dedicated EDS / division-polynomial-recurrence page; not a categorical concept |
|  7 | nCatLab (categorical)            | —                                                                                       | n/a  | —                                | not a categorical concept |
|  8 | Stacks Project (alg geom)        | "division polynomial" / "elliptic divisibility"                                          | n/a  | —                                | Stacks does not treat the EDS duplication recurrence at this granularity |
|  9 | MathOverflow / Math.SE           | EDS recurrence W(2m) terms                                                               | no   | —                                | discussions treat the full duplication formula; no separately-named subtrahend half |
| 10 | recent arXiv (last 5 years)      | "recurrence relation for elliptic divisibility sequences"                               | yes  | arXiv 2102.07573 (2021)          | states the full duplication recurrence; confirms the two summands are not individually named objects |

### Literature summary (Phase 3)

Concept identified as: the **subtrahend term of the EDS duplication ("even") recurrence**
`W(2m)·W(2) = W(m)·(W(m-1)²W(m+2) − W(m-2)W(m+1)²)` (Ward's recurrence / division-polynomial
doubling formula).

Sources agree on the standard form: **yes** — the literature uniformly states the *full* duplication
identity and packages `W(2m)/W(m)` as a single "complement" quantity (mathlib's `complEDS₂`). The
individual summand `W(m-2)·W(m+1)²` is **not a named object anywhere in the literature**; it only ever
appears inside the difference.

Most general standard form: the full duplication recurrence over an arbitrary commutative ring —
exactly what mathlib already carries.

Generality dimensions where the literature varies:
  - coefficient setting: classical (ℤ; division polynomials of an elliptic curve) → abstract
    (normalised EDS over any commutative ring). Both mathlib and this project use the most general
    (commutative-ring) form.

Disagreement with the literature: **the user's `compl₂EDSAux` has no literature counterpart** — it is
a project-internal *decomposition* of the standard complement into its two summands; `compl₂EDSAux_mul_b`
is the "half" of the literature's full duplication identity.

---

### Generality analysis — `compl₂EDSAux_mul_b`

Literature-standard form (from Phase 3): the full duplication recurrence; the complement
`W(m-1)²W(m+2) − W(m-2)W(m+1)²` (mathlib `complEDS₂_mul_b`). There is no "standard form" for the
half-term lemma because the half-term is not a standard object.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form     | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring (any base)  | NO                  | already maximally general; a polynomial identity over a commutative ring — exactly mathlib's setting |
| 2 | `(b c d : R)`          | three EDS params  | same                         | NO                  | intrinsic to the normalised-EDS definition |
| 3 | `(m : ℤ)`              | integer index     | integer index                | NO                  | EDS are ℤ-indexed; the `if Even m` parity correction is essential |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** in its typeclass/index parameters (it already matches
mathlib's commutative-ring, ℤ-indexed setting). The non-standard aspect is not generality but
**granularity**: the statement isolates a sub-term that the literature and mathlib never split out.
Weakening opportunities found: 0. Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
| 1 | bundled hyps → typeclasses?            | no | — | already `CommRing`-driven |
| 2 | sequences/metric → filters/topology?   | no | — | finite algebraic identity; no analysis |
| 3 | construction → universal property?     | no | — | no universal property |
| 4 | subset-predicate → bundled substructure?| no | — | not a substructure |
| 5 | field-specific → modules/(semi)ring?   | no | — | already over a general commutative ring |
| 6 | 1-categorical → higher-categorical?    | no | — | not categorical |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive? | no | — | index is ℤ; parity split essential, no useful generalisation |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. A finite polynomial identity already at mathlib's idiomatic
generality. The only "reformulation" in play is the *reverse* of a modernisation: mathlib
deliberately **bundles** the two summands into `complEDS₂` and proves the combined `complEDS₂_mul_b`,
whereas this project **un-bundles** them. Un-bundling is a granularity choice, not a modernisation.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equalities or instances).

---

### Mathlib search-status: `compl₂EDSAux_mul_b`

[A] Lean-Finder       (index reasoning)                                  no exact hit for the half-term lemma
[B] Loogle            `compl₂EDSAux`; `_ * _ = normEDS _ * normEDS _ ^ 2` no hit: `compl₂EDSAux` is not a mathlib name
[C] LeanSearch        "complement subtrahend EDS times b equals normEDS"  no hit
[D] Grep mathlib src  `EDSAux`, `compl.*aux`, `aux.*compl` over
                      `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
                      AND `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`  **no hit** — mathlib has NO `*EDSAux` def/lemma at all
[E] Name pattern      `complEDS₂` family in the mathlib EDS file          **partial**: mathlib has the *bundled* `complEDS₂` + `complEDS₂_mul_b`

Searched for both forms:
  - user's current form (half-term `compl₂EDSAux b c d m * b = …`) — **not in mathlib**;
  - literature-standard / bundled form (`complEDS₂_mul_b`) — **mathlib HAS it**, at
    `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:329`:
    ```
    lemma complEDS₂_mul_b (k : ℤ) : complEDS₂ b c d k * b =
        normEDS b c d (k - 1) ^ 2 * normEDS b c d (k + 2)
          - normEDS b c d (k - 2) * normEDS b c d (k + 1) ^ 2
    ```

Structural facts established by the grep (the key project-context check):
- The project's `compl₂EDS` (line 1031) is **definitionally identical** to mathlib's `complEDS₂`
  (line 246) — same `preNormEDS`-based formula, modulo the rename `complEDS₂ → compl₂EDS`. Likewise
  the project's `compl₂EDS_mul_b` (line 1062) is mathlib's `complEDS₂_mul_b` (line 329) verbatim.
  **This whole complement track is a fork of mathlib.**
- The project additionally pulls the **subtrahend half** of `complEDS₂` out into its own def
  `compl₂EDSAux` (line 1016). **Mathlib has no analogue** — the subtrahend appears only inside the
  difference in `complEDS₂` / `complEDS₂_mul_b` (mathlib lines 248, 331), never standalone.

Concluded: **partial match — mathlib has the bundled `complEDS₂_mul_b`, but NOT the half-term
`compl₂EDSAux_mul_b`, and NOT the underlying `compl₂EDSAux` def. The half-term is a project-specific
decomposition of an identity mathlib carries in bundled form.**

---

### Call sites — `compl₂EDSAux` / `compl₂EDSAux_mul_b`

Internal use count of def `compl₂EDSAux` (excluding its declaring block): **≥ 5** distinct sites.
External-to-file callers: **2 other files** (`ZSMul.lean`, `DivisionPolynomialOmega.lean`) plus this
file's `ω`/`redInvarNum` block.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| EllipticDivisibilitySequence.lean:1365 | `… + 2 * compl₂EDSAux b c d m` (inside `redInvarNum`) |
| EllipticDivisibilitySequence.lean:1369 | `redInvarNum … - … - 2 * compl₂EDSAux b c d m` |
| EllipticDivisibilitySequence.lean:1374 | `rw [compl₂EDSAux_mul_b, invarNum_normEDS]; ring`  ← the lemma's sole call site |
| EllipticDivisibilitySequence.lean:1421 | `map_compl₂EDSAux : f (compl₂EDSAux …) = compl₂EDSAux (f b) …` |
| ZSMul.lean:279                          | `rw [… compl₂EDSAux_two, sub_zero, Affine.addY, …]` |
| DivisionPolynomialOmega.lean:78         | `- compl₂EDSAux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3` (the `ω` def) |
| DivisionPolynomialOmega.lean:112        | `simp_rw [ω, …, map_compl₂EDSAux]` |

Inline-derivation grep (was the half-term identity re-derived elsewhere without the lemma?):
  - (none) — the lemma `compl₂EDSAux_mul_b` itself has exactly **one** call site (line 1374), inside
    the proof connecting `redInvarNum` to `invarNum`.

Call-sites signal: the **def** `compl₂EDSAux` is real, load-bearing project API — it is literally how
the `ω` family of division polynomials and the reduced-invariant numerator are *defined* (docstring
line 1014: *"appears in the definition of the numerator of the reduced invariant and in the definition
of the `ω` family of division polynomials"*). The **lemma** `compl₂EDSAux_mul_b` is a single-use bridge
inside that machinery (K = 1). Per the heuristic, K = 1 leans NO/borderline for the *lemma* on its own;
but its existence is entirely subordinate to the *def*, whose mathlib-status is the actual question.

---

### Composition check (Phase 6)

Can `compl₂EDSAux_mul_b` be derived from mathlib in ≤3 chained calls?

Attempt 1 — `simp` from the def (the project proof): `simp_rw [compl₂EDSAux, normEDS, Int.even_add,
Int.even_sub, …]; split_ifs <;> ring`.
  - Mathlib decls used: `Int.even_add`, `Int.even_sub`, `even_two`, `Int.not_even_one`, plus `ring`.
  - Result: **succeeds**, but only because `compl₂EDSAux` is the project's own def — this is *unfold +
    ring*, presupposing the (non-mathlib) `compl₂EDSAux`. It is NOT a composition of mathlib lemmas
    about a mathlib object.

Attempt 2 — derive the half from mathlib's bundled `complEDS₂_mul_b`: recovering `W(m-2)·W(m+1)²` from
`complEDS₂_mul_b` (which gives the *difference* `W(m-1)²W(m+2) − W(m-2)W(m+1)²`) would also require the
minuend `W(m-1)²·W(m+2)` separately.
  - Result: **fails as a ≤3-call composition** — the minuend half is *also* not separately available in
    mathlib (mathlib never splits `complEDS₂`), so there is no clean `a = (a−b) + b` route.

Conclusion: **NOT-COMPOSABLE** from mathlib *as a mathlib-object lemma*. The only proof is "unfold the
project's own `compl₂EDSAux` and `ring`", which is not a mathlib composition. So this is not a clean
NO-composable case (you cannot inline it at call sites from mathlib primitives) — yet it also adds no
new *mathematics*: it is one half of an identity mathlib already proves in bundled form, about a def
mathlib deliberately chose not to introduce.

---

## Verdict: `compl₂EDSAux_mul_b`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the duplication recurrence and its complement are standard (Ward;
  mathlib `complEDS₂`); the **subtrahend half on its own is not a named object** in any source.
- Generality analysis (Phase 4): MAXIMALLY GENERAL in parameters; no modern-idiom move; the only
  non-standard feature is granularity (un-bundling mathlib's `complEDS₂`).
- Mathlib search (Phase 5): mathlib has the **bundled** `complEDS₂_mul_b`
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:329`) and the def `complEDS₂` (line 246),
  which this project re-derives as `compl₂EDS` / `compl₂EDS_mul_b`. Mathlib has **no** `compl₂EDSAux`
  def and **no** half-term lemma.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib as a mathlib-object lemma (proof is
  unfold-the-project-def + `ring`); but it is one *half* of `complEDS₂_mul_b`.

**Rationale.**
This lemma is not mathlib-worthy on its own terms, and its fate is bound to a prior design question
that only a human (ideally a mathlib EDS maintainer) should settle: **should mathlib split its bundled
`complEDS₂` complement into the two summands of the duplication formula?** Mathlib today deliberately
keeps the complement bundled — it defines `complEDS₂` as the whole difference and proves
`complEDS₂_mul_b` for the difference. This project instead introduces `compl₂EDSAux` for the subtrahend
`preNormEDS(b⁴) c d (m-2)·preNormEDS(b⁴) c d (m+1)²·(parity)` because that exact sub-term recurs as a
*building block* of the project's `ω`-family division polynomials and reduced-invariant numerator (its
docstring and 5+ call sites confirm this). `compl₂EDSAux_mul_b` is then the natural "half" bridging
lemma, used once. So: the *lemma* is a single-use internal bridge (K = 1, leaning NO); the *def* it
serves is genuine project API; and **neither has a mathlib analogue** because mathlib chose the bundled
granularity. It is not NO-mathlib-has-it (mathlib lacks the half), not cleanly NO-composable (you can't
inline it from mathlib primitives — the complementary minuend half is equally unavailable), and not YES
(the half-term is not a literature object; shipping it would mean *also* shipping `compl₂EDSAux`, i.e.
asking mathlib to adopt the un-bundled granularity — a taste call about API shape, not a coverage gap).

**Numbered questions for the user / a mathlib EDS maintainer (≤5):**

1. **API-shape call:** should mathlib expose the subtrahend term of the duplication recurrence as its
   own definition (an upstream `complEDS₂Aux` / `preNormEDS`-subterm), or keep `complEDS₂` bundled as
   today? Only if "expose it" does `compl₂EDSAux_mul_b` become a candidate (the accompanying
   `…Aux_mul_b` half-lemma).
2. **Scope:** the sole motivation for un-bundling here is this project's `ω`-family division polynomials
   / reduced-invariant numerator (Nagell–Lutz). Is that machinery itself heading to mathlib? If it stays
   project-local, the half-term def + lemma should stay project-local too.
3. **Fork reconciliation (process, not mathlib-inclusion):** this file re-derives mathlib's entire
   `complEDS₂` track under renamed identifiers (`complEDS₂ → compl₂EDS`, `complEDS₂_mul_b →
   compl₂EDS_mul_b`, …). The cleaner action than upstreaming `compl₂EDSAux_mul_b` is to **delete the
   forked `compl₂EDS*` track and import mathlib's `complEDS₂*`**, keeping only `compl₂EDSAux` (+ its
   lemma) as the genuinely-new project-local delta. Should this be filed as a dedup/cleanup ticket on
   `main` instead of a mathlib PR?

**Next action:** user (or a mathlib EDS maintainer) answers Q1–Q3 — chiefly Q1, the API-shape decision
on whether mathlib should un-bundle `complEDS₂`. The most likely resolution is to keep
`compl₂EDSAux`/`compl₂EDSAux_mul_b` project-local and instead file the fork-reconciliation cleanup (Q3).
Re-run `/mathlibable compl₂EDSAux_mul_b` once Q1 is decided.

---

## Next step

User (or a mathlib EDS maintainer) answers the three numbered questions above — chiefly Q1, whether
mathlib should un-bundle `complEDS₂`. The most likely resolution is to keep
`compl₂EDSAux`/`compl₂EDSAux_mul_b` project-local and file a cleanup ticket to drop the forked
`compl₂EDS*` track in favour of mathlib's `complEDS₂*`.
