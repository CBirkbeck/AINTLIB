# /mathlibable report — `complEDS₂`

**TL;DR — `NO-mathlib-has-it`.** The project's `EllipticDivisibilitySequence.lean`
is a literal **fork** of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
(same author header — David Kurniadi Angdinata — same docstrings, same proofs).
`complEDS₂` exists in mathlib at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:246`
with a **byte-identical** definition body, on the very mathlib pin this repo builds
against (`d90090f`). Delete the fork and `import` mathlib.

---

### Baseline (Phase 0)
- lake build:               not run (build stale per task note; reasoned from source — verdict does not depend on elaboration)
- decl `complEDS₂`:          ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:844`
- qualified name:           `complEDS₂` (top-level; the enclosing `namespace EllSequence` closes at line 597, so the decl is in the root namespace inside `section PreNormEDS`)
- kind:                     `def`
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences (EDS) and the construction of normalised EDSs from initial terms." — a fork of mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

---

### Statement (Phase 1)

`complEDS₂ b c d : ℤ → R` is the **2-complement sequence** `Wᶜ₂` for the normalised
elliptic divisibility sequence `W = normEDS b c d`. It is the explicit witness to the
divisibility `W(k) ∣ W(2·k)`: by design `W(k) · Wᶜ₂(k) = W(2·k)` for every `k ∈ ℤ`.

Concretely, over a commutative ring `R` with `b c d : R`, it is defined from the
auxiliary sequence `preNormEDS (b⁴) c d` by

  `complEDS₂ b c d k = (P(k−1)² · P(k+2) − P(k−2) · P(k+1)²) · (if Even k then 1 else b)`,

where `P = preNormEDS (b⁴) c d`. This is exactly the even-index duplication bracket of
the EDS recurrence (Ward's relation specialised to the `W(2m)` case), carrying the
parity factor of `b` that the normalisation convention requires.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring; mathematically the integral domain / ring in which the EDS lives.
- `(b c d : R)` — the four initial data of the normalised EDS (`W(2)=b`, `W(3)=c`, `W(4)=d·b`).

Hypotheses: none (it is a plain definition).

Conclusion (math): the integer-indexed sequence `Wᶜ₂` satisfying `W·Wᶜ₂ = W(2·)`.
Conclusion (Lean): `ℤ → R` (a definition; `complEDS₂ b c d : ℤ → R`).

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline)
Reason: it is a named `def` of a concept ("2-complement sequence") that appears in the
module's `## Main definitions` list and is the witness for the headline divisibility
property. It is not a person-named theorem, but it is a named mathematical object, so it
clears the BIG bar. (Literature width is EXHAUSTIVE regardless — recorded for framing.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (one arithmetic expression split across two lines).
One-liner verdict: **effectively ONE-LINER** (`def` with a single expression body).

Exemption analysis is moot for the verdict: mathlib already ships this exact def, so the
question "is the one-liner worth a name in mathlib?" is answered by mathlib itself — yes,
mathlib gave it the name `complEDS₂`. The relevant point for *this project* is that the
name and body are duplicated from mathlib, not that a one-liner needs justification.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                                                 | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|-------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence W(k) divides W(2k) complement sequence division polynomial"     | yes  | `W(k)·Wᶜ₂(k)=W(2k)`; EDS arising from division polynomials; `n∣m ⇒ Wₙ∣Wₘ`            | **Top hit was the mathlib docs page itself**, quoting this exact `complEDS₂` docstring; also Wikipedia "Elliptic divisibility sequence" |
|  2 | WebSearch (general / named-after)| "Ward 'Memoir on Elliptic Divisibility Sequences' divisibility W_n divides W_m duplication"      | yes  | Ward 1948 fundamental relation `W_{m+n}W_{m−n}W_r² = W_{m+r}W_{m−r}W_n² − W_{n+r}W_{n−r}W_m²`; recurrence `W_{h−2}W_{h+2}=W_2²W_{h−1}W_{h+1}−W_1W_3W_h²` | Source paper for the whole construction (Am. J. Math 70, 1948) |
|  3 | WebSearch (aliases)              | (covered by #1/#2) "2-complement sequence" / "complement sequence" EDS                          | yes  | term "2-complement sequence" is mathlib/Angdinata-specific terminology for the duplication witness | the *object* (duplication bracket of the EDS recurrence) is classical; the *name* is mathlib's |
|  4 | ChatGPT MCP                      | (not run)                                                                                       | n/a  | —                                                                                   | Deliberately skipped: verdict is settled by a byte-identical mathlib decl on the same pin; a second opinion cannot move `NO-mathlib-has-it`. MCP may also be down per environment note. |
|  5 | Local references                 | `ls .mathlib-quality/references/`                                                               | n/a  | (no references dir for NagellLutz)                                                   | directory absent — recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence"                                                                | n/a  | —                                                                                   | nLab has no dedicated EDS page; concept is number-theoretic, not categorical. Not load-bearing given #1. |
|  7 | nCatLab                          | —                                                                                              | n/a  | —                                                                                   | not a categorical concept |
|  8 | Stacks Project                   | —                                                                                              | n/a  | —                                                                                   | not an algebraic-geometry/scheme-theoretic concept (it is an explicit integer-indexed sequence) |
|  9 | MathOverflow / Math.SE           | EDS divisibility `W_n ∣ W_{2n}` (covered by #1)                                                 | yes  | standard divisibility property of EDS                                               | corroborates #1/#2 |
| 10 | recent arXiv (last 5 years)      | "recurrence relation for elliptic divisibility sequences" (surfaced in #1/#2)                   | yes  | arXiv:2102.07573, arXiv:math/0404124 ("Divisibility in elliptic divisibility sequences") | confirms divisibility laws are an active, well-established topic |

### Literature summary (Phase 3)

Concept identified as: the **2-complement / duplication witness of an elliptic divisibility
sequence** — the even-index bracket of Ward's EDS recurrence that exhibits `W(k) ∣ W(2k)`.
Standard mathematical name: this is the `W(2m)` case of the EDS duplication formula; the
specific term "2-complement sequence `Wᶜ₂`" is mathlib's (Angdinata's) naming.
Sources agree on the standard form: yes — `W(k)·Wᶜ₂(k) = W(2k)`, the underlying recurrence
is Ward (1948).
Most general standard form: defined over any commutative ring `R` (Ward works in an integral
domain; mathlib/the fork both generalise to `CommRing R`).
Generality dimensions where the literature varies:
  - coefficient ring: Ward uses ℤ / an integral domain; the modern (mathlib) form uses an arbitrary `CommRing R`. The fork matches the most general (`CommRing`).
Disagreement with the literature: none.

---

### Generality analysis — `complEDS₂`

Literature-standard form (Phase 3): the duplication witness over an integral domain; the
modern maximally-general form is over an arbitrary commutative ring.

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form     | Weaker form exists? | Reason |
|---|------------------------|--------------------------|------------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | arbitrary commutative ring | integral domain (Ward) → CommRing (modern) | NO        | already maximally general; the definition is a polynomial expression in `b,c,d` and needs only ring operations. Matches mathlib's `complEDS₂` exactly. |
| 2 | `(b c d : R)`          | three ring elements       | three ring elements          | NO                  | these are the EDS initial data; cannot be weakened |
| 3 | index `k : ℤ`          | integer index            | integer index                | NO                  | EDS are intrinsically ℤ-indexed (antisymmetric two-sided sequences) |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** — identical to mathlib's `complEDS₂` (`CommRing R`,
`b c d : R`, `k : ℤ`). Zero weakening opportunities.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Notes |
|----|----------|----------|-------|
| 1  | typeclass-ify "let X be a foo" preambles? | no | only typeclass is `[CommRing R]`, already idiomatic |
| 2  | sequences/metric → filters/topology? | no | purely algebraic; no topology |
| 3  | construction → universal-property class? | no | the witness is an explicit polynomial; no universal property to characterise |
| 4  | set+closure-predicate → bundled substructure? | no | not a substructure |
| 5  | vector-space/field-specific → weaken typeclasses? | no | already `CommRing`, the right level |
| 6  | 1-categorical → higher-categorical? | no | not categorical |
| 7  | concrete index → general additive structure? | no | ℤ-indexing is essential to the EDS notion |

Modern idiom available: **no**. mathlib's own `complEDS₂` *is* the modern idiom — the fork
reproduces it verbatim. There is nothing to modernise.

---

### Diamond / defeq risk — `complEDS₂`

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond            | none    | no instances introduced; plain `def : ℤ → R` |
| 2 | Reducibility leak            | none    | not `@[reducible]`; sealed def (matches mathlib) |
| 3 | Non-canonical unfolding      | none    | unfolds only via explicit `simp [complEDS₂]`, as the `complEDS₂_*` simp-lemmas do |
| 4 | Instance priority collision  | n/a     | not an instance |
| 5 | Universe-polymorphism issues | none    | `R : Type u`, no forced annotation |
| 6 | Coercion ambiguity           | none    | no `CoeFun`/`CoeSort` |

### Risk verdict (Phase 4.5)
Overall risk: **NONE**. (Moot anyway — mathlib already ships this exact def with no reported
diamond/defeq issues.)

---

### Mathlib search-status: `complEDS₂`

[A] Lean-Finder        "2-complement sequence EDS"        n/a (mathlib index server not queried; grep is decisive — see [D])
[B] Loogle             `complEDS₂`, `?R → ℤ → ?R`          n/a (grep decisive)
[C] LeanSearch         "complement sequence W(k) divides W(2k)" n/a (grep decisive)
[D] Grep mathlib src   `def complEDS₂`                    **HIT** — `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:246`
[E] Name pattern       `complEDS` across `Mathlib/`        **HIT** — exactly one file: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`

Searched for both:
  - the user's current form (`complEDS₂ b c d k`) — **found, identical**
  - the literature-standard form (duplication witness over `CommRing`) — **found, identical** (mathlib's is the same)

**Byte-level confirmation.** `diff` of the project def body (lines 844–846) against mathlib's
(lines 246–248) reports **IDENTICAL def body**. The surrounding API matches too:
`complEDS₂_zero` (=2), `complEDS₂_one` (=b), `complEDS₂_two` (=d), `complEDS₂_three`,
`complEDS₂_four`, `complEDS₂_neg`, `preNormEDS_mul_complEDS₂`, `normEDS_mul_complEDS₂`, and
`normEDS_dvd_normEDS_two_mul` are all present in mathlib verbatim. The project file even
carries the identical author header (David Kurniadi Angdinata) and docstrings — it is a
**fork** of the mathlib module.

Concluded: **found in mathlib as `complEDS₂`; identical form** (same name, same body, same
generality, same mathlib pin `d90090f` that this repo builds against).

---

### Call sites — `complEDS₂`

Internal use count (same file, excluding the declaring line): **33** (`grep -c` = 34 incl. the
`def`). The fork's own `complEDS₂_*` lemmas and `preNormEDS_mul_complEDS₂` consume it — exactly
mirroring mathlib's internal API.

External-to-file callers (within the project tree): the **HasseWeil** project uses `complEDS₂`
heavily —

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:621 | `rw [show (6:ℤ)=2*3 by rfl, ← normEDS_mul_complEDS₂, complEDS₂, …]` |
| HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:647 | `lemma complEDS₂_eq_aeval : complEDS₂ b c d = …` (new API atop it) |
| HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:855 | `lemma complEDS₂_eq_redInvarNum_sub : complEDS₂ b c d m = …` (new) |
| HasseWeil/Auxiliary/DivisionPolynomial.lean:69 | `def ψc : ℤ → R[X][Y] := complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)` |
| HasseWeil/Auxiliary/DivisionPolynomial.lean:114 | `normEDS_mul_complEDS₂ _ _ _ _` |

Crucially, HasseWeil's source comment at `OmegaPullbackCoeff.lean:431` explicitly attributes
the supporting lemma to mathlib: *"`p(4m) = complEDS₂(2m)·p(2m)` (mathlib's
`preNormEDS_mul_complEDS₂`)"* — i.e. consumers already treat this API as **mathlib's**, and
the HasseWeil `Auxiliary/EllipticDivisibilitySequence.lean` is itself another fork-with-extensions.

Inline-derivation grep: the def is re-derived (forked) in two other project files
(`NagellLutz/.../EllipticDivisibilitySequenceOriginal.lean:798` and the HasseWeil auxiliary
fork) — additional evidence of duplication, not of novelty.

Composability signal: K ≫ 3 internal + multiple external callers, **but** every use is of a
mathlib-provided form. Per the call-sites table this is the "re-derived inline at ≥1 site /
mathlib has it" row → **NO-mathlib-has-it**.

---

### Composition check (Phase 6)

Not applicable as a *composition* — the result is not "compose mathlib primitives", it is
"mathlib already has this exact declaration". No sketch needed; the refactor is a direct
symbol substitution / import, not an inlining.

Conclusion: **NOT-COMPOSABLE-and-not-needed** — mathlib *has* it outright (stronger than
composable).

---

## Verdict: `complEDS₂`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): concept = Ward (1948) EDS duplication witness; **the WebSearch top hit was the mathlib docs page quoting this exact docstring**.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical to mathlib (`CommRing R`).
- Mathlib search (Phase 5): **found in mathlib as `complEDS₂`; identical form** — `diff` reports a byte-identical def body, on the same pin `d90090f`.
- Composition check (Phase 6): not needed — mathlib has the decl outright.

**Rationale.**
The project's `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a
**verbatim fork** of mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
— same Apache header, same author (David Kurniadi Angdinata), same module docstring, same
proofs. `complEDS₂` is reproduced byte-for-byte (project lines 844–846 vs mathlib 246–248,
`diff` = identical), together with its entire satellite API (`complEDS₂_zero/one/two/three/four`,
`complEDS₂_neg`, `preNormEDS_mul_complEDS₂`, `normEDS_mul_complEDS₂`,
`normEDS_dvd_normEDS_two_mul`). This is the textbook `NO-mathlib-has-it` case: not "mathlib
has a more general form we'd specialise", but "mathlib has the *exact* form, at the *exact*
generality, on the *exact* commit this repo already depends on."

This matches the project's own stated context (the NagellLutz project "FORKS parts of mathlib
... `Mathlib.NumberTheory.EllipticDivisibilitySequence`"). The fork was presumably taken to add
project-specific results downstream; but `complEDS₂` itself adds nothing over upstream. Note
the genuinely-new work lives *elsewhere* — HasseWeil's `complEDS₂_eq_aeval`,
`complEDS₂_eq_redInvarNum_sub`, `ψc`, etc. build a new layer on top of mathlib's `complEDS₂`;
those are out of scope for this decl and would warrant their own `/mathlibable` runs.

**WHY not (refactor-actionable).**
Mathlib already has it, identically, at the pinned commit. The "gap" is purely a local
duplication: the project re-declares a mathlib symbol instead of importing it. Keeping the
fork risks definitional drift from upstream and forces the consolidation library to maintain a
copy of code mathlib already owns.

  Existing mathlib decl:        `complEDS₂` (root namespace)
  Located at:                   `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:246`
  Our form *is* the mathlib form (identical):
  ```lean
  -- mathlib (==) project:
  def complEDS₂ (k : ℤ) : R :=
    (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
      preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b
  ```
  Call sites in our project (Phase 6.0): 33 internal (fork's own lemmas) + multiple external
    (HasseWeil), all of the *mathlib* form.

  **Refactor plan.** This is not a one-symbol swap but a whole-file dedup, owned by `main`'s
  cleanup fleet (a `lane:cleanup` ticket), not by a producer:
    1. Determine which declarations in
       `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` are forked-from-mathlib
       (the entire `complEDS₂` family + `preNormEDS`/`normEDS` core are upstream) versus
       genuinely project-new (anything below the fork boundary, e.g. the `Complement` /
       `Divisibility` sections starting ~line 1011/1262 that are *not* in mathlib).
    2. Replace the forked portion with `public import Mathlib.NumberTheory.EllipticDivisibilitySequence`
       and delete the duplicated `complEDS₂` (+ satellite lemmas). All 33 internal references
       resolve to the imported mathlib symbol unchanged (same name, same namespace, same
       signature — no call-site edits needed).
    3. Keep only the project-new declarations in the project file, now sitting atop the mathlib
       import.
    4. Do the same for the sibling forks `EllipticDivisibilitySequenceOriginal.lean` and
       `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` (de-duplicate against mathlib;
       preserve their genuinely-new extensions like `complEDS₂_eq_aeval`).
  Because the names and signatures are identical to mathlib, the substitution is mechanical and
  cannot change any downstream statement.

  **Next action.** File a `lane:cleanup` (dedup) issue on `main` to collapse the mathlib fork in
  `EllipticDivisibilitySequence.lean` to an `import` of `Mathlib.NumberTheory.EllipticDivisibilitySequence`,
  retaining only the project-original sections. Do **not** open a mathlib PR — mathlib already
  has `complEDS₂`.

---

## Next step

File a `lane:cleanup` deduplication ticket on `CBirkbeck/AINTLIB` `main`: replace the
forked `complEDS₂` (and the rest of the mathlib-copied core in
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`) with
`public import Mathlib.NumberTheory.EllipticDivisibilitySequence`, keeping only the
project-original declarations. No mathlib PR — `complEDS₂` is already upstream and identical.
