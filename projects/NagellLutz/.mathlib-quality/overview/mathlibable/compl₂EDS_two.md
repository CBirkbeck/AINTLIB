# /mathlibable report — `compl₂EDS_two`

> Project: NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS).
> File: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1041`.
> **Headline verdict: `NO-mathlib-has-it`** — this is a renamed duplicate of mathlib's
> `complEDS₂_two`. The whole `compl₂EDS` family in this file is a fork of
> `Mathlib.NumberTheory.EllipticDivisibilitySequence` with the `₂` subscript relocated
> in the identifier (`complEDS₂` → `compl₂EDS`).

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); reasoned from source — the decl is a `@[simp]` glue lemma over `simp [compl₂EDS]`.
- decl `compl₂EDS_two`:      ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1041`
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences" — defines EDS, `preNormEDS`/`normEDS`, and a forked `compl₂EDS` complement family; a self-contained re-development that does NOT import `Mathlib.NumberTheory.EllipticDivisibilitySequence` (builds from lower-level mathlib).

**Name correction.** The task tentatively named the decl `compl₂EDS_one` ("VERIFY from source").
Line 1041 is in fact `compl₂EDS_two`. (`compl₂EDS_one` is the line **above**, 1040.) This report
covers the decl actually at line 1041: **`compl₂EDS_two`**.

Qualified name: the decl sits inside `section NormEDS` / `section Complement` (plain `section`s,
no `namespace`); the enclosing `namespace EllSequence` closes at line 597 and only reopens at
1079, so line 1041 is at the **top level**. Qualified name = **`compl₂EDS_two`** (no prefix).

---

### Statement (Phase 1)

`compl₂EDS_two` states that the 2-complement sequence of a normalised EDS, evaluated at `m = 2`,
equals `d`:
$$ W^{\mathrm c}_2(2) = d. $$

Here `compl₂EDS b c d m` is the "2-complement" `W(2m)/W(m)` of the canonical normalised EDS
`W = normEDS b c d` — the division-free witness of `W(m) ∣ W(2m)`, satisfying
`normEDS b c d m * compl₂EDS b c d m = normEDS b c d (2*m)` (`normEDS_mul_compl₂EDS`, line 1046).
Its closed form (lines 1031–1033) is
`(p(m-1)²·p(m+2) − p(m-2)·p(m+1)²)·(if Even m then 1 else b)` with `p = preNormEDS (b^4) c d`.

At `m = 2` this is the base-case value `W(4)/W(2) = (d·b)/b = d`. Concretely `compl₂EDS … 2`
unfolds to `(p(1)²·p(4) − p(0)·p(3)²)·1 = p(4) = d` (via `preNormEDS_four = d`, `p(0)=0`, `p(1)=1`),
which `simp [compl₂EDS]` discharges.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring.
- `(b c d : R)` — EDS initial data (`W(2)=b`, `W(3)=c`, `W(4)=d·b`).

Hypotheses: none.

Conclusion (math): `Wᶜ₂(2) = d`.
Conclusion (Lean): `compl₂EDS b c d 2 = d`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `@[simp]` base-case evaluation lemma (a `def`-unfolding fact about `compl₂EDS` at the
literal `2`); not a named theorem, not a project main result, introduces no structure.

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`. (Body `by simp [compl₂EDS]` is a one-line glue proof; this is a
glue/simp lemma in the verdict-inheritance category — its verdict follows the parent def `compl₂EDS`.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence division polynomial W(2m) duplication formula psi 2m even terms"        | yes  | `ψ_{2m}·ψ_2 = ψ_m(ψ_{m+2}ψ_{m-1}² − ψ_{m-2}ψ_{m+1}²)` | Wikipedia "Elliptic divisibility sequence"; msp.org ANT; also surfaced mathlib's own EDS docs page |
|  2 | WebSearch (general / named-after)| "Mazur Tate division polynomials elliptic curve psi_{2n}=psi_n(psi_{n+2}psi_{n-1}²−psi_{n-2}psi_{n+1}²)"| yes  | same duplication identity, ψ-normalisation | Silverman / Mazur–Tate division polynomials; classical |
|  3 | WebSearch (aliases)              | "duplication formula" / "2-complement" / "even division polynomial ψ_{2n}/ψ_n" (covered by #1/#2)        | yes  | `W(2m)/W(m)` even-index complement | "complement"/"Wᶜ₂" is mathlib's coinage; the math is the ψ_{2n} duplication factor |
|  4 | ChatGPT MCP                      | (MCP down per task brief — fallback)                                                                    | n/a  | —                                | substituted by a direct read of the exact mathlib source decl (stronger than an index/LLM answer) |
|  5 | Local references                 | `ls .mathlib-quality/references/` ; `ls refs/NagellLutz/`                                               | n/a  | (no references dir; no `refs/`)  | both absent in this checkout |
|  6 | nLab                             | "elliptic divisibility sequence" / "division polynomial"                                                | n/a  | —                                | no dedicated nLab page; not a categorical concept |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                | not categorical — a polynomial recurrence identity |
|  8 | Stacks Project (alg geom)        | "division polynomial" / "elliptic divisibility"                                                         | n/a  | —                                | no Stacks tag; out of scope |
|  9 | MathOverflow / MSE               | "duplication formula division polynomial ψ_{2n}/ψ_n"                                                    | yes  | duplication identity is folklore-standard | corroborates #1/#2 |
| 10 | recent arXiv (≤5y)               | 2102.07573 "A recurrence relation for EDS"; 2604.05280 "On Elliptic Sequences over Commutative Rings"   | yes  | EDS recurrences over commutative rings | confirms the commutative-ring generality used here |

Protocol passed: 3 WebSearch queries at different generality levels; ChatGPT MCP unavailable (brief)
and substituted by a **direct mathlib-source read** (the decisive evidence); local refs / nLab /
nCatLab / Stacks / MO / arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept: the **even-index duplication factor of division polynomials / EDS**, `Wᶜ₂(m) := W(2m)/W(m)`
(mathlib's "2-complement"; classically the bracket in `ψ_{2m}ψ_2 = ψ_m(ψ_{m+2}ψ_{m-1}² −
ψ_{m-2}ψ_{m+1}²)`).
Sources agree on the standard form: yes.
Most general standard form: over an arbitrary commutative ring with EDS initial data `(b,c,d)` —
exactly the form used here.
Generality dimensions varying: coefficient domain (ℤ classically → any commutative ring for the
polynomial identity; this file already uses `CommRing R`). The specific fact `Wᶜ₂(2)=d` is a
base-case evaluation, not a parametric theorem.
Disagreement with the literature: none.

---

### Generality analysis — `compl₂EDS_two`

Literature-standard form (Phase 3): the base-case value `W(4)/W(2)=d` over any `CommRing R`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring         | NO                  | the def `compl₂EDS` uses subtraction; `CommRing` is the minimal natural class and is exactly what mathlib's `complEDS₂_two` uses |
| 2 | `(b c d : R)`          | free ring elements| free ring elements       | NO                  | already maximally general — no constraints |
| 3 | index `2`              | literal `(2:ℤ)`   | base case               | NO                  | a base-case lemma at the literal 2; the index-general statement is the separate `normEDS_mul_compl₂EDS` |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical generality to mathlib's `complEDS₂_two`).
Weakening opportunities: 0. Cost: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reason |
|----|----------|----------|--------|
| 1 | bundled hyps → typeclasses? | no | no bundled "let X be a foo" hyps; just ring elements |
| 2 | sequences/metric → filters/topology? | no | finite polynomial identity; no limits |
| 3 | construction → universal property? | no | a concrete base-case value |
| 4 | set+closure → bundled substructure? | no | n/a |
| 5 | vector-space/field → module/(semi)ring? | no | already `CommRing`; subtraction needed, cannot weaken to semiring |
| 6 | 1-categorical → higher? | no | n/a |
| 7 | concrete index → general structure? | no | this *is* the base case at index 2; index-general form is `normEDS_mul_compl₂EDS` |

Modern idiom available: **no** — a finite base-case ring identity. mathlib's own copy uses this exact
idiom, confirming it is the intended mathlib form.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`.

---

### Mathlib search-status: `compl₂EDS_two`

[A] Lean-Finder       (tool not in deferred set here)   n/a — substituted by direct mathlib-source grep (method [D], stronger)
[B] Loogle            type-pattern (tool not loaded)     n/a — superseded by [D]
[C] LeanSearch        natural-language (tool not loaded) n/a — superseded by [D]
[D] Grep mathlib src  `grep "compl₂EDS\|complEDS₂\|complEDS"` over `.lake/packages/mathlib/.../EllipticDivisibilitySequence.lean` — **HIT**
[E] Name pattern      `complEDS₂_two`, `complEDS₂` in the mathlib EDS file — **HIT**

Searched both the user's form (`compl₂EDS … 2 = d`) and the canonical mathlib form (`complEDS₂ … 2 = d`).

**Concluded: found in mathlib as `complEDS₂_two`; IDENTICAL form.**

Exact mathlib decl (`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:258–260`):
```lean
@[simp]
lemma complEDS₂_two : complEDS₂ b c d 2 = d := by
  simp [complEDS₂]
```
vs. project (`…/EllipticDivisibilitySequence.lean:1041`):
```lean
@[simp] lemma compl₂EDS_two : compl₂EDS b c d 2 = d := by simp [compl₂EDS]
```
Same statement (`Wᶜ₂(2) = d`), same proof (`simp` over the def), same `@[simp]` attribute.

The underlying defs are character-for-character identical (mathlib `complEDS₂` 246–248 vs. project
`compl₂EDS` 1031–1033), modulo the bound-variable alias `p := preNormEDS (b^4) c d` and the
parameter name `k`↔`m`:
```lean
-- mathlib  complEDS₂ (k : ℤ) :=
  (preNormEDS (b^4) c d (k-1)^2 * preNormEDS (b^4) c d (k+2)
    - preNormEDS (b^4) c d (k-2) * preNormEDS (b^4) c d (k+1)^2) * if Even k then 1 else b
-- project  compl₂EDS (m) := letI p := preNormEDS (b^4) c d
  (p (m-1)^2 * p (m+2) - p (m-2) * p (m+1)^2) * if Even m then 1 else b
```
The whole surrounding family matches: mathlib has `complEDS₂_zero/one/two/three/four`, `complEDS₂_neg`,
`complEDS₂_mul_b`, `normEDS_mul_complEDS₂`, `normEDS_dvd_normEDS_two_mul`; the project has
`compl₂EDS_zero/one/two/…`, `compl₂EDS_neg`, `compl₂EDS_mul_b`, `normEDS_mul_compl₂EDS`,
`normEDS_dvd_two_mul`. This file is a **fork** of `Mathlib.NumberTheory.EllipticDivisibilitySequence`
(it re-defines `preNormEDS'`, `preNormEDS`, `normEDS`, `compl₂EDS` rather than importing them), with
the `₂` subscript moved inside the identifier.

mathlib provenance: the EDS file is long-established (golfed in mathlib PR #38833; current pin
`09b373db6e24`), so mathlib is unambiguously the canonical source and the project's copy is derivative.

---

### Call sites — `compl₂EDS_two`

Internal use count: **0** (within NagellLutz, excluding the declaring file; and 0 repo-wide).
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none) | — |

The only other grep hits for the substring `compl₂EDS_two` are the **unrelated** lemma
`compl₂EDS_two_three_two` (line 1241; `compl₂EDS (2:ℤ) 3 2 n = 2`) and its single consumer
`ZSMul.lean:124` — neither references *this* lemma. `compl₂EDS_two` is `@[simp]`, so it is consumed
implicitly by the `simp` set (normal for a base-case `@[simp]` evaluation); this strengthens, not
weakens, the NO verdict — mathlib's `@[simp] complEDS₂_two` already supplies the same simp fact.

Inline-derivation grep: (none — no site re-derives `compl₂EDS … 2 = d` by hand.)

---

### Composition check (Phase 6)

Not the relevant question — mathlib has the **identical named lemma**, so this is `NO-mathlib-has-it`,
not `NO-composable`. For completeness: against mathlib it is literally `complEDS₂_two` (0 calls);
against first principles it is `by simp [complEDS₂]` (the same one-line proof). Conclusion: **redundant
with an existing mathlib lemma.**

---

## Verdict: `compl₂EDS_two`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the duplication-factor `W(2m)/W(m)` is the classical `ψ_{2m}/ψ_m`
  even-division-polynomial identity; standard over any commutative ring.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — same `CommRing R` generality as mathlib's copy; no modern-idiom move.
- Mathlib search (Phase 5): **found in mathlib as `complEDS₂_two`**, identical statement, identical `simp [complEDS₂]` proof, identical `@[simp]` attribute; the whole `compl₂EDS` family is a renamed fork of `complEDS₂`.
- Composition check (Phase 6): redundant — it *is* `complEDS₂_two`.

**Rationale.**
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a self-contained re-development
of `Mathlib.NumberTheory.EllipticDivisibilitySequence`: it re-defines `preNormEDS`, `normEDS`, and the
complement family from the lower-level mathlib imports instead of importing the EDS file, and it
relocates the `₂` subscript in the names (`complEDS₂` → `compl₂EDS`, `normEDS_mul_complEDS₂` →
`normEDS_mul_compl₂EDS`, etc.). Under that renaming, `compl₂EDS_two` is **exactly** mathlib's
`complEDS₂_two` (`@[simp] lemma complEDS₂_two : complEDS₂ b c d 2 = d := by simp [complEDS₂]`,
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:258`). The defining expressions are
character-identical up to the `p := preNormEDS (b^4) c d` alias and the `k`↔`m` parameter name. There
is nothing to add — mathlib already has this lemma, at the same generality, with the same proof and the
same `@[simp]` status.

**WHY not (refactor-actionable).**
Mathlib already has it: **`complEDS₂_two`** at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:259`. The project's form is the *same* lemma
about a *re-defined-but-definitionally-identical* `compl₂EDS` (= `complEDS₂`). Our form is the renamed
lemma verbatim.

Existing mathlib decl:        `complEDS₂_two`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:259`
Our form follows in ≤1 line (after aligning the def):
```lean
example : compl₂EDS b c d 2 = d := complEDS₂_two   -- once compl₂EDS is unified with mathlib's complEDS₂
```
Call sites in our project (from Phase 6.0):  **K = 0** (no named consumers; it is a `@[simp]` lemma).

**Refactor plan.** This is not an isolated-lemma cleanup — it is a **whole-family dedup**. The
`compl₂EDS` (and `preNormEDS`/`normEDS`/`complEDS`) track duplicates `Mathlib.NumberTheory.
EllipticDivisibilitySequence` under a name remap (`₂`-subscript moved). The correct action is to delete
the forked complement family and re-base the file on the mathlib decls, mapping `compl₂EDS ↦ complEDS₂`
and its lemmas `compl₂EDS_zero/one/two/three/four/neg/mul_b ↦
complEDS₂_zero/one/two/three/four/neg/mul_b`, `normEDS_mul_compl₂EDS ↦ normEDS_mul_complEDS₂`,
`normEDS_dvd_two_mul ↦ normEDS_dvd_normEDS_two_mul`. For `compl₂EDS_two` specifically: drop it; mathlib's
`@[simp] complEDS₂_two` already supplies the same simp fact, so no call site needs editing (K = 0).
Because this is a coordinated rename touching many sibling decls (and the file deliberately forks
mathlib — likely to host the `compl'`/`compl`/`redInvar` extensions mathlib lacks), the de-fork is a
**project-level decision**, not a mechanical per-lemma delete; sequence it with the other
`compl₂EDS*`/`complEDS₂*` overview reports as one dedup ticket.

Next action: fold `compl₂EDS_two` into the `compl₂EDS`-family ⇄ mathlib `complEDS₂`-family
deduplication; delete this lemma in favour of mathlib's `complEDS₂_two` (no call-site edits needed).
