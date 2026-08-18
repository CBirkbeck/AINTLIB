# /mathlibable report — `WeierstrassCurve.preΨ_zero`

## Verdict: **NO-mathlib-has-it** (verbatim fork of an existing mathlib lemma)

> One-line summary: this lemma is a byte-for-byte copy of `WeierstrassCurve.preΨ_zero`
> which already lives in `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:202`.
> Same namespace, same signature, same `@[simp]` attribute, same proof term.

---

### Baseline (Phase 0)
- lake build:               not re-run (env note: local build stale); assessment reasons from source — the decl elaborates in the upstream project and is a copy of a known-good mathlib lemma.
- decl `WeierstrassCurve.preΨ_zero`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:125`
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

**Qualified name (VERIFIED from source).** The file opens `namespace WeierstrassCurve`
(line 27) with `variable {R : Type r} [CommRing R] (W : WeierstrassCurve R)` (line 29).
The lemma `preΨ_zero` therefore has fully-qualified name **`WeierstrassCurve.preΨ_zero`** —
matching the prompt's guessed name exactly.

---

### Statement (Phase 1)

`WeierstrassCurve.preΨ_zero` states that the auxiliary univariate division polynomial
`preΨₙ` of a Weierstrass curve `W` over a commutative ring `R`, evaluated at index `n = 0`,
is the zero polynomial:
$$ \mathrm{pre}\Psi_0 = 0 \in R[X]. $$

Here `preΨ : ℤ → R[X]` is defined (line 117–118) as
`preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n`, i.e. the **pre-normalised elliptic divisibility
sequence** specialised to the curve's invariants. The statement is just the `n = 0` base
value of that EDS recurrence, lifted from the scalar EDS lemma `preNormEDS_zero`.

Variables / typeclasses (Lean side):
- `{R : Type r}` with `[CommRing R]` — the base ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve (supplies `Ψ₂Sq`, `Ψ₃`, `preΨ₄`).

Hypotheses: none.

Conclusion (math): `preΨ₀ = 0`.
Conclusion (Lean): `W.preΨ 0 = 0`.

Proof body: `preNormEDS_zero ..` — a single term, directly applying the EDS base-case lemma
(the `n = 0` case of `preNormEDS`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a base-case evaluation lemma for an auxiliary polynomial family; a one-term `@[simp]`
glue lemma, not a named theorem or a new structure.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner def check is **n/a**.
(Noted for completeness: the *proof* is a single term `preNormEDS_zero ..`, i.e. a glue
lemma whose value is entirely inherited from the EDS layer.)

---

### Literature search (Phase 3) — abbreviated, with justification

**Why abbreviated is correct here.** The exhaustive nine-channel literature sweep exists to
pin down the *standard form* and *right generality* of a concept whose mathlib status is
uncertain. That uncertainty is absent: Phase 5 finds the identical declaration already in
mathlib under the identical qualified name. The verdict (`NO-mathlib-has-it`) does not turn
on any literature judgment — there is no "should mathlib state it differently?" question to
resolve, because the question "does mathlib have it?" is answered YES with a verbatim hit.
Running the full lit sweep would change nothing about the verdict. The mathematical content
is nonetheless completely standard and recorded below.

| # | Channel | Query | Hit? | Standard form | Notes |
|---|---------|-------|------|----------------|-------|
| 1 | Domain knowledge / mathlib docstring | Weierstrass division polynomials `ψₙ`, base values | yes | `ψ₀ = 0`, `ψ₁ = 1`, `ψ₂`, `ψ₃`, `ψ₄` are the classical base cases of the division-polynomial recurrence | Silverman, *Arithmetic of Elliptic Curves*, Exercise 3.7; the `n=0` value `ψ₀ = 0` is the universally-standard seed of the EDS recurrence |
| 2 | mathlib source (authoritative) | `WeierstrassCurve.preΨ` / `preNormEDS` base cases | yes | `preΨ 0 = 0` via `preNormEDS 0 = 0` | exact target form; see Phase 5 |
| 3 | WebSearch / nLab / Stacks / MathOverflow / arXiv | (not run) | n/a | n/a | n/a — verdict is fixed by a verbatim mathlib hit (Phase 5); these channels cannot move a `NO-mathlib-has-it` verdict for a copied decl. The concept ("division polynomial", "elliptic divisibility sequence") is classical and already formalised upstream by D. Angdinata. |

### Literature summary (Phase 3)
Concept identified as: the zeroth value of the (pre-normalised) **division polynomial** /
**elliptic divisibility sequence** of a Weierstrass curve — `preΨ₀ = 0`.
Sources agree on the standard form: yes — `ψ₀ = 0` is the canonical EDS seed.
Most general standard form: over any `CommRing R` (exactly what mathlib uses).
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form: `preΨ₀ = 0` over an arbitrary commutative ring `R`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form? | Reason |
|---|------------------------|-------------------|----------------------|--------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring | NO | `preΨ`/`preNormEDS` are defined over `CommRing`; division polynomials genuinely need ring structure. This is already the maximally-general base. |

### Generality verdict (Phase 4b)
The current form is: **MAXIMALLY GENERAL** (it is literally mathlib's own form, verbatim).
Weakening opportunities: 0.

### Modern-idiom check (Phase 4c)
Modern idiom available: **no**. This is a finite/base-case evaluation of an existing mathlib
definition; there is no topology to filter-ise, no construction to replace with a universal
property, no index to generalise (the index is the literal constant `0`). The form is already
mathlib's chosen idiom because it *is* mathlib's lemma.

---

### Diamond / defeq risk (Phase 4.5)
**n/a** — declaration kind is `lemma` (introduces no definitional equalities or
typeclass-search paths).

---

### Mathlib search-status: `WeierstrassCurve.preΨ_zero` (Phase 5) — DECISIVE

Direct source inspection of the mathlib pinned in this very workspace
(`/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib/`):

```
Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:201-203
  @[simp]
  lemma preΨ_zero : W.preΨ 0 = 0 :=
    preNormEDS_zero ..
```

inside `namespace WeierstrassCurve` (line 104) with
`variable {R : Type r} [CommRing R] (W : WeierstrassCurve R)` (line 106).

| Method | Query | Result |
|--------|-------|--------|
| [D] Grep mathlib src | `preΨ_zero` in `DivisionPolynomial/Basic.lean` | **HIT — identical lemma at line 202** |
| [D] Grep mathlib src | `preNormEDS_zero` in `NumberTheory/EllipticDivisibilitySequence.lean` | HIT — the underlying lemma the proof delegates to (line 186) |
| [E] Name pattern | `WeierstrassCurve.preΨ_zero` | exact qualified-name match in mathlib |
| [A/B/C] Loogle / LeanSearch / Lean-Finder | not needed | n/a — a verbatim source hit under the exact qualified name supersedes index search |

**Comparison (project copy vs. mathlib):**

| | Project (`DivisionPolynomial.lean:124-126`) | Mathlib (`Basic.lean:201-203`) |
|---|---|---|
| attribute | `@[simp]` | `@[simp]` |
| signature | `W.preΨ 0 = 0` | `W.preΨ 0 = 0` |
| namespace | `WeierstrassCurve` | `WeierstrassCurve` |
| variables | `{R} [CommRing R] (W : WeierstrassCurve R)` | `{R} [CommRing R] (W : WeierstrassCurve R)` |
| proof | `preNormEDS_zero ..` | `preNormEDS_zero ..` |

**Identical in every respect.** The project's own file header (lines 12–16) states it is a
deliberate copy of `Mathlib...DivisionPolynomial.Basic`, forked only to re-point its import
at the project's local `EllipticDivisibilitySequence` (which itself duplicates
`Mathlib.NumberTheory.EllipticDivisibilitySequence`) to dodge a `normEDS`/`complEDS`
name clash.

Concluded: **"found in mathlib as `WeierstrassCurve.preΨ_zero`; identical form."**

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.preΨ_zero`
Internal use count: **0** (grep over `projects/NagellLutz/**/*.lean`, excluding the declaring
line, returns no matches).
External-to-file callers: 0.
Inline-derivation grep: the lemma is consumed only as a `@[simp]` rewrite (if at all); no
explicit named call sites in the project.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none) | — |

Note: as a `@[simp]` base-case lemma it may fire implicitly inside `simp` calls; that does not
change the verdict — mathlib's identical `@[simp]` lemma would fire the same way once the
project drops its fork in favour of the upstream file.

#### Composition (Phase 6a)
The proof already *is* a one-call composition: `preNormEDS_zero ..` (mathlib's
`WeierstrassCurve.preΨ_zero` proves it identically). But composition is moot — the exact
lemma already exists upstream, so the correct action is reuse, not inline-composition.

Conclusion: **NOT-COMPOSABLE is irrelevant**; the controlling fact is the verbatim mathlib hit.

---

## Verdict: `WeierstrassCurve.preΨ_zero`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): `preΨ₀ = 0` is the standard EDS seed; concept already
  formalised upstream (D. Angdinata).
- Generality analysis (Phase 4): MAXIMALLY GENERAL — it is mathlib's own form, verbatim.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.preΨ_zero`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:202`); **identical** form.
- Composition check (Phase 6): 0 project call sites; moot given the verbatim hit.

**WHY not (refactor-actionable):**
Mathlib already contains this exact lemma — identical namespace, signature, `@[simp]`
attribute, and proof term. The project's `DivisionPolynomial.lean` is, by its own docstring,
a hand-copy of `Mathlib...DivisionPolynomial.Basic`, forked purely to re-route its import to a
local duplicate of `Mathlib.NumberTheory.EllipticDivisibilitySequence` (to avoid a `normEDS` /
`complEDS` name collision). `preΨ_zero` carries no project-specific content whatsoever; it is
pure fork-duplication. There is no mathlib gap to fill: the gap is the *reverse* — the project
duplicates mathlib.

Existing mathlib decl:        `WeierstrassCurve.preΨ_zero`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:202`
Underlying lemma it delegates to: `WeierstrassCurve.preNormEDS_zero` (the project's local copy) ↔ `preNormEDS_zero` in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:186`

Our form follows in ≤1 line (it is literally the same proof):
```lean
example (W : WeierstrassCurve R) : W.preΨ 0 = 0 := WeierstrassCurve.preΨ_zero
```

Call sites in our project (from Phase 6.0): **0**.

**Refactor plan.** This lemma should not be carried by the project at all. The correct fix is
structural, not per-lemma: resolve the `normEDS`/`complEDS` name clash that forced the fork
(e.g. by `open`-scoping or qualifying the local EDS names, or by upstreaming the project's EDS
additions) so that `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean` can be deleted and
replaced by `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`. Once
that import is restored, `WeierstrassCurve.preΨ_zero` (and its siblings `preΨ_one`, `preΨ_two`,
`preΨ_three`, `preΨ_four`, `preΨ_neg`, `preΨ_even`, `preΨ_odd`, …) come for free from mathlib
and the local copies are removed. Since there are 0 internal call sites specific to this lemma,
removing it in isolation is trivial; the real work is dissolving the whole forked file back
onto its mathlib original.

**Next action:** do **not** upstream this lemma (mathlib has it). Track the fork as a
dedup/cleanup item: eliminate the `normEDS`/`complEDS` clash and re-point the project at
mathlib's `DivisionPolynomial.Basic`, deleting the duplicated file. This is a project-hygiene
task, not a mathlib contribution.

---

## Next step

Track a cleanup ticket to dissolve the forked `DivisionPolynomial.lean` back onto
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` (after resolving the local
EDS name clash). No mathlib PR — mathlib already has `WeierstrassCurve.preΨ_zero` verbatim.
