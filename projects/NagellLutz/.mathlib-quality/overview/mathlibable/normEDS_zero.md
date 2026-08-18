# /mathlibable report — `normEDS_zero`

**TL;DR verdict: `NO-mathlib-has-it`.** This lemma is a verbatim fork of mathlib's
`normEDS_zero` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:298`) — same
name, same statement, same `[CommRing R]` generality, same `@[simp]`, same proof, same
author (David Kurniadi Angdinata, who wrote mathlib's EDS file). The whole project file
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a fork of that
mathlib module (extended with the `EllSequence` / `IsEllSequence` development on top),
and `normEDS` + `normEDS_zero` are copied unchanged.

---

### Baseline (Phase 0)
- lake build:                stale locally; assessment reasons from source (mathlib EDS module present in `.lake/packages/mathlib`).
- decl `normEDS_zero`:        resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:902`
- qualified name:            `normEDS_zero` (top-level — no enclosing `namespace`; only `section NormEDS`)
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences (EDS) and the construction of normalised EDSs from initial terms." (forked from `Mathlib.NumberTheory.EllipticDivisibilitySequence`)

Context: `variable {R : Type u} ... [CommRing R]` (line 85), `variable (b c d : R)` (line 883).

---

### Statement (Phase 1)

`normEDS_zero` states that the canonical normalised elliptic divisibility sequence
`normEDS b c d : ℤ → R` vanishes at index `0`:
$$ W(0) = 0, \qquad W := \mathrm{normEDS}\,b\,c\,d. $$
Here `normEDS b c d n := preNormEDS (b^4) c d n * (if Even n then b else 1)` is the
standard Ward normalised EDS with initial terms `W(0)=0, W(1)=1, W(2)=b, W(3)=c,
W(4)=d·b`. The lemma is the `n=0` base case: since the pre-normalised sequence
`preNormEDS` has value `0` at `0`, the product is `0`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (commutative ring).
- `(b c d : R)` — the three free initial parameters of the normalised EDS.

Hypotheses: none.

Conclusion (math): `W(0) = 0`.
Conclusion (Lean): `normEDS b c d 0 = 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a base-case evaluation lemma (one of `normEDS_zero/one/two/three/four`) for an
already-defined sequence; not a new structure, not a named theorem, not a project main
result. (Literature width still run exhaustively per the skill; recorded SMALL for framing.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — the one-liner-definition gate does
not apply. (The proof body `by simp [normEDS]` is a single tactic, but this is a theorem,
so n/a.)

---

### Literature search (Phase 3)

| #  | Channel                          | Query                                                                                   | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | elliptic divisibility sequence normalised initial term W(0)=0 W(1)=1 division polynomial | yes  | Normalised EDS: `W₀=0, W₁=1`, recursion from division polynomials (Ward) | mathlib's own EDS docs page is a top hit; Wikipedia "Elliptic divisibility sequence"; Stange "Elliptic nets". |
|  2 | WebSearch (general form)         | (same query, generality of coefficient ring)                                            | yes  | Defined over a general commutative ring `R`; classically over `ℤ` | The `W₀=0` normalisation `Dₙ → Dₙ/D₁` is the defining convention. |
|  3 | WebSearch (named-after / alias)  | Ward elliptic divisibility sequence / division polynomial ψₙ initial values             | yes  | `ψ₀ = 0` (division polynomials); `Wₙ = ψₙ(P)` | `W(0)=0` is forced by `ψ₀=0`. Standard since Ward 1948. |
|  4 | ChatGPT MCP                      | n/a — MCP flagged down in this environment; substituted by the three WebSearch generality levels + direct mathlib-source confirmation. | n/a | — | The decl is verbatim-present in mathlib (Phase 5), so the standard-form question is settled at the source. |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "EDS"/"normEDS"                                  | n/a  | (no references dir for this triage) | recorded n/a. |
|  6 | nLab                             | elliptic divisibility sequence                                                          | n/a  | — | Not an nLab/categorical concept; the canonical reference is mathlib's own module + Ward/Silverman-Stephens. |
|  7 | nCatLab                          | —                                                                                       | n/a  | — | Not categorical. |
|  8 | Stacks Project                   | —                                                                                       | n/a  | — | Not in Stacks' scope (no EDS / division-polynomial chapter). |
|  9 | MathOverflow / Math.SE           | (covered transitively by WebSearch #1–3)                                                | n/a  | — | The base case `W(0)=0` is textbook, not a research question. |
| 10 | recent arXiv (last 5 years)      | Stange "Division polynomials for arbitrary isogenies" (eprint 2025/521); EDS terms div. by index (1001.5303) | yes | confirms `ψ₀=0` / `W₀=0` normalisation persists in current literature | no more-general statement of *this base case* exists; it's `0` by definition. |

### Literature summary (Phase 3)

Concept identified as: **normalised elliptic divisibility sequence** (Ward's EDS / the
division-polynomial sequence `ψₙ`), evaluated at index `0`.
Sources agree on the standard form: **yes** — every reference takes `W₀ = 0` as part of
the normalisation (indeed `Dₙ → Dₙ/D₁` with `D₀ = 0`), matching `ψ₀ = 0`.
Most general standard form: the construction is given over an arbitrary commutative ring
`R` with three free parameters `b, c, d`; `W(0) = 0` holds identically.
Generality dimensions where the literature varies: coefficient domain (`ℤ` classically →
general commutative ring in modern/Lean treatments). mathlib (and this fork) already take
the **most general** position, `[CommRing R]`.
Disagreement with the literature: none — `W(0)=0` is the defining base value.

---

### Generality analysis (Phase 4)

Literature-standard form (Phase 3): `W(0) = 0` for the normalised EDS over a general
commutative ring.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring (classically `ℤ`) | NO | `normEDS` is defined via `preNormEDS` over `CommRing`; this is already the most general home and matches mathlib's definition exactly. |
| 2 | `(b c d : R)`          | three free ring elements | three free initial parameters | NO | These are the defining data of the canonical normalised EDS; cannot be weakened. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**.
Number of weakening opportunities found: 0.
Cost of restatement: n/a (already maximal, and identical to mathlib's).

### Modern-idiom check (Phase 4c)

Modern idiom available: **no**. This is a finite/definitional base-case identity
(`W(0)=0`) for a sequence `ℤ → R`. There is no preamble to typeclass-ify, no
sequence-to-filter move, no universal-property reformulation, no substructure, no
weaker-typeclass target, no categorification, and the index is already the maximally
general one used by the definition. mathlib itself states it in exactly this idiom.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no new definitional equalities or typeclass-search
paths introduced).

---

### Mathlib search-status: `normEDS_zero` (Phase 5)

[A] Lean-Finder       "normEDS zero" / "normalised EDS at 0"     hit (mathlib `normEDS_zero`)
[B] Loogle            `normEDS _ _ _ 0 = 0`                       hit — exact lemma exists
[C] LeanSearch        "normalised elliptic divisibility sequence value at zero is zero"  hit (mathlib EDS module)
[D] Grep mathlib src  `normEDS_zero` over `.lake/.../Mathlib/`    **HIT** ×2:
                        - `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:298` (the lemma)
                        - `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:408` (`normEDS_zero ..`, internal use)
[E] Name pattern      `lemma normEDS_(zero|one|two) ` over mathlib  HIT — the whole `normEDS_zero/one/two/three/four` family lives in mathlib.

Searched for both:
  - the user's current form (`normEDS b c d 0 = 0`) — present verbatim.
  - the literature-standard form — identical (it is the base case, nothing more general).

Concluded: **found in mathlib as `normEDS_zero` (`Mathlib.NumberTheory.EllipticDivisibilitySequence`,
line 298); identical form** — same statement, same `[CommRing R]` generality, same `@[simp]`,
same proof `by simp [normEDS]`, same underlying `normEDS` definition (byte-identical body),
same author. The project file is a fork of this mathlib module.

---

### Composition check (Phase 6)

#### Call sites — `normEDS_zero` (Phase 6.0)

Internal use count (NagellLutz project, excluding the declaring file): **2**
- `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:331` — `normEDS_zero ..`
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:961` — `... (normEDS_zero _ _ _)` (and `:1341` in the declaring file, `simp [normEDS_zero, ...]`).

External-to-project callers (other AINTLIB projects): **HasseWeil** also forks the same lemma
(`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:589, :795`) — i.e.
this base case is duplicated across the fork *and* its consumers, exactly mirroring how mathlib
uses its own `normEDS_zero` in `DivisionPolynomial/Basic.lean:408`.

Inline-derivation grep: the equivalent `simp [normEDS]` base case is what `normEDS_zero`
*is*; consumers use the named lemma, not an inline re-derivation.

Signal: there are real consumers — but they are consumers of a **forked copy** of a mathlib
lemma. The right fix is to drop the fork and import mathlib's `normEDS_zero`, not to upstream
anything.

#### Composition attempt (Phase 6)

Can `normEDS_zero` be derived from mathlib in ≤3 chained calls? Moot — mathlib has the exact
named lemma. (For completeness: it is also `by simp [normEDS]`, unfolding the definition plus
`Even 0`/`zero_mul`, a ≤1-step composition — but NO-mathlib-has-it dominates NO-composable.)

Conclusion: **NOT-COMPOSABLE is irrelevant — mathlib has the exact decl.**

---

## Verdict: `normEDS_zero`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): `W(0)=0` is the defining base value of the normalised EDS over a general commutative ring; sources unanimous; no more-general statement of the base case exists.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical to mathlib's `[CommRing R]` form; no modern-idiom move.
- Mathlib search (Phase 5): **found in mathlib as `normEDS_zero`**, `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:298`; identical statement, generality, attribute, and proof.
- Composition check (Phase 6): n/a — the exact named lemma already exists; 2 internal call sites (plus a parallel fork in HasseWeil) all consume a forked copy.

**Rationale:**

`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (same author, David Kurniadi Angdinata;
the module docstring and the `normEDS` definition are copied verbatim). Within it,
`normEDS_zero` is a line-for-line duplicate of the mathlib lemma: identical name, identical
statement `normEDS b c d 0 = 0`, identical `[CommRing R]` generality, identical `@[simp]`
attribute, and identical proof `by simp [normEDS]`. mathlib not only declares it (line 298)
but also *uses* it internally in `DivisionPolynomial/Basic.lean:408` — exactly as the fork
uses its own copy in `NagellLutz/.../DivisionPolynomial.lean:331`. There is nothing to add
to mathlib; mathlib already has this, at the maximal generality, in the canonical place.

**WHY not (refactor-actionable):**
Mathlib already contains `normEDS_zero` verbatim. The fork exists because the NagellLutz
project bundles a *modified/extended* EDS development (the `EllSequence` / `IsEllSequence`
API, ~1100 extra lines) in the same file and re-derives the base lemmas locally. But this
particular lemma is unmodified from mathlib. The refactor is to stop shadowing the mathlib
lemma and import it instead.

Existing mathlib decl:        `normEDS_zero` (in the root namespace)
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:298`
Our form follows in ≤0 lines (it IS the mathlib lemma):
```lean
-- the mathlib lemma, character-for-character:
@[simp] lemma normEDS_zero : normEDS b c d 0 = 0 := by simp [normEDS]
```

Call sites in the NagellLutz project (Phase 6.0): **2** (excluding the declaring file)
- `NagellLutz/LutzNagell/DivisionPolynomial.lean:331`  (`normEDS_zero ..`)
- `NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:961`  (`normEDS_zero _ _ _`)
- (+ in-file use at `:1341`; + a parallel fork in `HasseWeil/.../EllipticDivisibilitySequence.lean:589,795`)

Refactor plan: this is part of the larger "de-fork the EDS module" cleanup. If/when the
NagellLutz `EllipticDivisibilitySequence.lean` is rebased onto mathlib's
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (importing it rather than re-deriving
the base API), `normEDS_zero` is deleted from the project and the 2 call sites resolve to
the imported mathlib lemma automatically — the name, argument shape (`normEDS_zero ..` /
`normEDS_zero _ _ _`), and `@[simp]` behaviour are identical, so no call-site edits are
needed beyond the import swap. The same deletion applies to the HasseWeil fork. Until that
module-level de-fork happens, this lemma simply stays as a known mathlib duplicate; it must
**not** be sent to mathlib (NO-add).

Next action: do not PR to mathlib. Track under the project's EDS de-fork / dedup cleanup —
replace the forked `Mathlib.NumberTheory.EllipticDivisibilitySequence` copy with an import
of the upstream module; `normEDS_zero` (and its `normEDS_one/two/three/four/neg` siblings)
then come from mathlib.

---

## Next step

Do not PR to mathlib. `normEDS_zero` already exists upstream
(`Mathlib.NumberTheory.EllipticDivisibilitySequence`, line 298) verbatim. Fold this into the
project-level cleanup that de-forks the EDS module: import the mathlib EDS file instead of
re-deriving its base lemmas, then delete the duplicated `normEDS_zero` (the 2 NagellLutz call
sites — and the parallel HasseWeil fork — resolve to the mathlib lemma unchanged).
