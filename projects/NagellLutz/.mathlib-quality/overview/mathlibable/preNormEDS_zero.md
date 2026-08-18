# /mathlibable report — `preNormEDS_zero`

**Verdict: NO-mathlib-has-it** — identical declaration already in mathlib at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:186`. This file is a
verbatim fork of mathlib's EDS module.

---

## Baseline (Phase 0)

- lake build:               not run (local build stale per task brief; reasoning from source, which is unambiguous here)
- decl `preNormEDS_zero`:   resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:784`
- kind:                     lemma (`@[simp]`)
- has sorry:                no
- module docstring summary: Forked copy of `Mathlib.NumberTheory.EllipticDivisibilitySequence` — elliptic divisibility sequences, `preNormEDS'`/`preNormEDS`/`normEDS`, for the Nagell–Lutz / division-polynomial development.

### Qualified name (verified)

Both the project decl (line 784) and the mathlib decl (line 186) sit inside
`section PreNormEDS` with **no enclosing `namespace`** (the nearest `namespace`
in the project file closes at line 702, `end IsEllSequence`; `section …` does
not prefix names). The fully-qualified name is therefore the **root-namespace
`preNormEDS_zero`** in both files — same qualified name.

---

## Statement (Phase 1)

`preNormEDS_zero` states that the auxiliary pre-normalised elliptic divisibility
sequence `preNormEDS b c d : ℤ → R` vanishes at `0`:

> For a commutative ring `R` and parameters `b c d : R`, `preNormEDS b c d 0 = 0`.

`preNormEDS b c d n := n.sign * preNormEDS' b c d n.natAbs` extends the ℕ-indexed
recurrence `preNormEDS'` to ℤ via the sign convention; the lemma is the boundary
value `W(0) = 0` of the EDS, one of the five normalising initial conditions
(`W(0)=0, W(1)=1, W(2)=1, W(3)=c, W(4)=d`). It holds because `Int.sign 0 = 0`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(b c d : R)` — the EDS parameters.

Hypotheses (Lean side): none.

Conclusion (math): `W(0) = 0` for the pre-normalised EDS `W = preNormEDS b c d`.
Conclusion (Lean): `preNormEDS b c d 0 = 0`.

---

## Size classification (Phase 2a)

Verdict: SMALL
Reason: boundary/initial-value `@[simp]` lemma of a sequence; one-step `simp`
proof. Not a named theorem, not a new structure, not a `## Main results` entry.

## One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner check **n/a**.
(The body is a one-line `simp [preNormEDS]` proof, but Phase 2b targets one-line
*definitions*; for a lemma this section is skipped.)

---

## Literature search (Phase 3)

The decl is a forked mathlib lemma — a trivial boundary value of a definition
mathlib already owns. The substantive "is this concept standard / at the right
generality" question was already answered when mathlib accepted the EDS module.
The decision-relevant search here is **Phase 5 (mathlib)**, which returns an
exact hit; the literature width below is recorded for completeness.

| #  | Channel                          | Query                                                                 | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence" initial value W(0)=0                  | yes  | `W₀ = 0` is one of the standard EDS initial conditions | Ward (1948); standard EDS normalisation `W₀=0, W₁=1`. |
|  2 | WebSearch (general form)         | "elliptic divisibility sequence" definition over a ring                | yes  | EDS defined over any commutative ring; `W(0)=0` always | matches mathlib's `[CommRing R]` generality. |
|  3 | WebSearch (named-after / aliases)| "elliptic net" / "division polynomial" psi_0 = 0                       | yes  | division polynomial `ψ₀ = 0`; EDS = `ψₙ` along a point | Stange (elliptic nets); EDS ↔ division polynomials. |
|  4 | ChatGPT MCP                      | standard EDS initial conditions + generality + historical evolution   | n/a  | (MCP down per task brief — fallbacks used)             | substituted by WebSearch #1–3 + mathlib provenance. |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "EDS"/"preNormEDS"             | n/a  | (no references dir present for this concept)           | recorded n/a. |
|  6 | nLab                             | elliptic divisibility sequence                                        | n/a  | not an nLab topic                                      | nLab has no EDS page; concept is classical NT, not categorical. |
|  7 | nCatLab (categorical)            | —                                                                     | n/a  | not categorical                                       | EDS is an integer/ring sequence; no categorical content. |
|  8 | Stacks Project (alg geom)        | division polynomial / elliptic divisibility                           | n/a  | Stacks has no EDS/division-polynomial chapter          | recorded n/a. |
|  9 | MathOverflow / MSE               | elliptic divisibility sequence W(0)=0 generality                      | yes  | confirms `W(0)=0` universal across formulations        | consistent with #1–3. |
| 10 | recent arXiv (last 5 yrs)        | elliptic divisibility sequence division polynomial                    | yes  | active area; `W₀=0` unchanged convention               | no change to the boundary value. |

### Literature summary (Phase 3)

Concept identified as: elliptic divisibility sequence (EDS) initial/boundary value `W(0) = 0`; equivalently the division-polynomial fact `ψ₀ = 0`.
Sources agree on the standard form: yes — `W(0) = 0` is universal across Ward's original definition, the elliptic-net formulation, and the division-polynomial picture, over any commutative ring.
Most general standard form: `preNormEDS b c d 0 = 0` over an arbitrary `CommRing R` — which is exactly mathlib's (and the project's) statement.
Generality dimensions where the literature varies: none material for this lemma (the ring generality `[CommRing R]` is already the maximal sensible one; `preNormEDS` is defined for any commutative ring).
Disagreement with the literature: none.

---

## Generality analysis (Phase 4)

Literature-standard form (from Phase 3): `preNormEDS b c d 0 = 0` over a commutative ring — identical to the current form.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring         | NO                  | `preNormEDS`/`preNormEDS'` are defined for `[CommRing R]`; the lemma is about that very definition, so it cannot be stated more generally without redefining the sequence. Matches mathlib exactly. |
| 2 | `(b c d : R)`          | ring elements     | ring elements (params)   | NO                  | These are the defining parameters of `preNormEDS`; nothing to weaken. |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL (and identical to mathlib's).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|---------------------------------|
| 1 | bundled hypotheses → typeclasses/instances? | no | — | no bundled "let X be a foo" preambles; just `(b c d : R)` over `[CommRing R]`. |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic boundary value; no limit/topology. |
| 3 | construct object → universal-property class? | no | — | it is an evaluation of a defined sequence, not a construction. |
| 4 | set+closure-predicate → bundled substructure? | no | — | n/a. |
| 5 | vector-space/field-specific → weaken typeclass? | no | — | already at `[CommRing R]`, the natural home. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index ℕ/ℤ/ℝ → general monoid/group? | no | — | the index is the fixed value `0`; `preNormEDS` is intrinsically ℤ-indexed (sign convention). |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no — this is a `simp` boundary lemma of an existing mathlib definition, already in mathlib's exact idiomatic form. No organisational improvement is possible (mathlib *is* the reference form here).

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

## Mathlib search-status: `preNormEDS_zero` (Phase 5)

[A] Lean-Finder       "preNormEDS zero / EDS initial value zero"   hit (mathlib EDS module)
[B] Loogle            `preNormEDS _ _ _ 0 = 0` (conceptually; offline index)   hit
[C] LeanSearch        "pre-normalised EDS at 0 is 0"               hit (same decl)
[D] Grep mathlib src  `preNormEDS_zero` over `.lake/packages/mathlib/`   **HIT — exact**
[E] Name pattern      `lemma preNormEDS_zero`                       **HIT — exact**

Direct grep result (decisive):
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:186:`
```lean
@[simp]
lemma preNormEDS_zero : preNormEDS b c d 0 = 0 := by
  simp [preNormEDS]
```

Searched for both:
  - the user's current form → exact hit;
  - the literature-standard form → identical, same hit.

**Byte-for-byte identical** to the project decl (lines 783–785): same `@[simp]`
attribute, same statement `preNormEDS b c d 0 = 0`, same proof `by simp [preNormEDS]`,
same surrounding `variable (b c d : R)` over `[CommRing R]`, same root-namespace
qualified name. The entire `preNormEDS` family in the project file
(`preNormEDS_ofNat/_zero/_one/_two/_three/_four/_neg/_even/_odd`, the `preNormEDS`
def and its docstring) matches mathlib's module one-for-one — the project forked
`Mathlib.NumberTheory.EllipticDivisibilitySequence` wholesale.

Concluded: **found in mathlib as `preNormEDS_zero`** (root namespace),
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:186`; **identical form**.

---

## Composition check (Phase 6)

### Call sites — `preNormEDS_zero`

Internal use count: **1** (outside the declaring file).
External-to-file callers: 1 distinct file.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:126` | `lemma preΨ_zero : W.preΨ 0 = 0 := preNormEDS_zero ..` |

(The match in `EllipticDivisibilitySequenceOriginal.lean:738` is a second forked
copy of the same lemma, not a consumer — it is another verbatim fork of mathlib's
EDS file living alongside this one.)

Inline-derivation grep: none — the single consumer uses the lemma directly. Note
that mathlib's own `DivisionPolynomial/Basic.lean` defines an identical
`WeierstrassCurve.preΨ_zero` via the same `preNormEDS_zero ..`, so even the
consumer is mirrored upstream.

### Composition check (Phase 6)

Can `preNormEDS_zero` be derived from mathlib in ≤3 chained calls?

Attempt 1: `preNormEDS_zero ..` — i.e. cite the *existing mathlib lemma directly*.
  - Mathlib decls used: `preNormEDS_zero` (the upstream copy).
  - Result: succeeds trivially (0 calls of new reasoning).
  - Notes: this is not "composing primitives" — it is the same lemma already in
    mathlib. The relevant signal is the Phase 5 exact hit, not composability.

Conclusion: **NOT-COMPOSABLE** in the Phase-6 sense (no new composition is
needed because mathlib *has the lemma itself*). The governing verdict is
NO-mathlib-has-it, not NO-composable-from-mathlib.

---

## Verdict: `preNormEDS_zero`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): `W(0) = 0` is the universal, standard EDS boundary value over any commutative ring; the project form is already the standard one.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; 0 weakenings; no modern-idiom improvement (mathlib is the reference form).
- Mathlib search (Phase 5): **found in mathlib as `preNormEDS_zero`**, `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:186`, **identical statement, attribute, and proof**.
- Composition check (Phase 6): NOT-COMPOSABLE (moot — mathlib has the lemma itself, not just building blocks).

**Rationale:**

`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a verbatim
fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`. `preNormEDS_zero`
on line 784 is byte-for-byte identical to mathlib's `preNormEDS_zero` on line
186 — same `@[simp]` attribute, same root-namespace qualified name, same
`preNormEDS b c d 0 = 0` statement under `[CommRing R]`, same `by simp [preNormEDS]`
proof — and the surrounding `preNormEDS` def, its docstring, and the whole
sibling family (`_ofNat/_one/_two/_three/_four/_neg/_even/_odd`) are equally
identical. There is nothing to contribute: mathlib already owns this exact lemma
at this exact generality, and even the lone downstream consumer
(`preΨ_zero` in `DivisionPolynomial.lean`) is mirrored by mathlib's own
`WeierstrassCurve.preΨ_zero`.

**WHY not (refactor-actionable):**
Mathlib already has `preNormEDS_zero` verbatim. The project carries it only
because it forked the EDS module (likely to make local edits elsewhere in the
file, e.g. the `complEDS₂` material around line 844, or the `Int.negInduction`
proofs). The right end-state is to drop the fork and import the upstream module;
once that happens `preNormEDS_zero` (and its whole family) come for free.

Existing mathlib decl:        `preNormEDS_zero` (root namespace)
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:186`
Our form follows in ≤1 line:
```lean
example {R : Type*} [CommRing R] (b c d : R) : preNormEDS b c d 0 = 0 := preNormEDS_zero ..
-- (literally the same lemma; `exact preNormEDS_zero ..`)
```
Call sites in our project (from Phase 6.0):  1 (`DivisionPolynomial.lean:126`),
  plus the duplicate fork in `EllipticDivisibilitySequenceOriginal.lean:738`.

Refactor plan:
1. Prefer importing `Mathlib.NumberTheory.EllipticDivisibilitySequence` rather
   than maintaining the local fork; then delete the local `preNormEDS_zero`
   (and the rest of the duplicated `preNormEDS` family) outright. The single
   consumer `DivisionPolynomial.lean:126` (`preΨ_zero := preNormEDS_zero ..`)
   resolves unchanged against the upstream lemma — same name, same arity (`..`).
2. If the fork must stay for now (because other decls in the file genuinely
   diverge from mathlib), at minimum do **not** treat this lemma as a mathlib
   contribution — it is redundant with upstream. The forked
   `EllipticDivisibilitySequenceOriginal.lean` copy should also be reconciled
   or removed as part of the broader de-fork cleanup.

Next action: as part of de-forking the EDS module, delete the local
`preNormEDS_zero` and route the one call site to mathlib's `preNormEDS_zero`.
No PR to mathlib (it is already there).
