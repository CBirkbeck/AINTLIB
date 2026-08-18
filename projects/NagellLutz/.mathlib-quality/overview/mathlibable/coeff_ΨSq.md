## /mathlibable report — `WeierstrassCurve.coeff_ΨSq`

> Step-9 mathlibable assessment, NagellLutz project. Single declaration.
> Generated 2026-06-22. Read-only on `.lean`; only this report was written.

---

### Baseline (Phase 0)

- lake build:               not run (local build stale, per task brief). Decl read directly from source; statement + proof captured below.
- decl `WeierstrassCurve.coeff_ΨSq`:  ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:349`
- kind:                      `lemma` (theorem)
- has sorry:                 no
- module docstring summary:  "Division polynomials of Weierstrass curves" — computes leading terms of `preΨ`, `ΨSq`, `Φ`. The header explicitly states the file is **"a project copy of mathlib's Basic file"** (line 14).

**Qualified name (VERIFIED).** The decl sits under `namespace WeierstrassCurve` (opened at line 55, `open Polynomial` at 51) and is named `coeff_ΨSq`. Confirmed qualified name: **`WeierstrassCurve.coeff_ΨSq`** — matches the prompt's parsed guess.

---

### Statement (Phase 1)

`WeierstrassCurve.coeff_ΨSq` states: for a Weierstrass curve `W` over a commutative ring `R` and any integer `n`, the coefficient of the univariate polynomial `ΨSqₙ` (a polynomial in `R[X]` congruent to the square `ψₙ²` of the `n`-th division polynomial) in degree `|n|² − 1` equals `n²` (as an element of `R`, via the integer-to-`R` cast).

In Silverman's notation: writing `ψₙ` for the `n`-th division polynomial of `E`, the "square" polynomial `ΨSqₙ` (= `preΨₙ² · Ψ₂Sq` when `n` even, else `preΨₙ²`) has its degree-`(n²−1)` coefficient equal to `n²`. This is the explicit-leading-coefficient half of the classical degree computation `deg ψₙ² = n² − 1`, `lead ψₙ² = n²`.

Variables / typeclasses (Lean side):
- `{R : Type u}`, `[CommRing R]` — the base commutative ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve.
- `(n : ℤ)` — the multiplier index.

Hypotheses: none (holds for **all** `n : ℤ` over **any** commutative ring; no `NoZeroDivisors`, no characteristic hypothesis).

Conclusion (math): the degree-`(|n|² − 1)` coefficient of `ΨSqₙ` is `n²`.
Conclusion (Lean): `(W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = n ^ 2`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a coefficient-extraction helper lemma about a specific named polynomial; not a structure def, not a person-named theorem, not a top-level project goal. (It is one of several routine `coeff_*` / `natDegree_*` lemmas in a degree-bookkeeping file.)

(Literature width is EXHAUSTIVE regardless — but see Phase 5: this is settled at the mathlib-search step before the literature question even matters, because the decl is a *verbatim fork of an existing mathlib lemma*.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner check is **n/a**. (The body is a 3-line `Int.negInduction`, irrelevant to the def-inlining heuristic.)

---

### Literature search (Phase 3) — short-circuited by an exact mathlib hit

The mathlib search (Phase 5) returned an **exact, character-for-character identical** decl already in mathlib (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:351`), authored by the same person (David Kurniadi Angdinata) who wrote this project copy. When mathlib already contains the *identical* lemma with the *identical* proof, the literature-standard-form question is moot: the verdict is mechanically `NO-mathlib-has-it`, and the exhaustive nine-channel literature sweep cannot change it (no degree of literature generality makes a verbatim duplicate of a mathlib lemma a mathlib *contribution*).

For completeness, the underlying mathematics is fully standard and classical:

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---------|-------|------|---------------------|-------|
| 1 | Local references | reasoning from module docstring `## References` | yes | Silverman, *The Arithmetic of Elliptic Curves* (GTM 106), Exercise 3.7 / §III.3.7 division-polynomial recursion | The file cites `[silverman2009]`; the degree/leading-coeff facts `deg ψₙ = (n²−1)/2` (n odd) and `deg ψₙ² = n²−1`, `lead ψₙ² = n²` are the standard normalisation there. |
| 2 | Mathlib source (authoritative) | mathlib `Degree.lean` | yes | `(W.ΨSq n).coeff (n.natAbs^2 - 1) = n^2` | **Identical statement and proof already in mathlib** — this is the controlling evidence. |
| 3 | WebSearch / nLab / Stacks / MathOverflow / arXiv | n/a | n/a | n/a | Not run: an exact verbatim mathlib duplicate is dispositive (Phase 5). A wider literature sweep cannot turn a copy of an existing mathlib lemma into a contribution; running it would not move the verdict off NO-mathlib-has-it. Recorded as n/a per the skill's "exact-hit short-circuit". |

### Literature summary (Phase 3)

Concept identified as: leading coefficient / top coefficient of the squared elliptic division polynomial `ψₙ²` of a Weierstrass curve.
Sources agree on the standard form: yes — `deg(ψₙ²) = n² − 1` with leading coefficient `n²` is the textbook normalisation (Silverman GTM 106, §III.3 / Ex. 3.7).
Most general standard form: the result as stated already holds over an arbitrary commutative ring for all `n : ℤ` — this *is* the general form.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Not the operative question (the decl is an exact mathlib duplicate — Phase 5). Recorded briefly:

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|--------------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring | NO | already maximal: `ΨSq`/`preΨ`/`Ψ₂Sq` are defined over `CommRing`; no integral-domain or char hypothesis is imposed. |
| 2 | `(n : ℤ)` | arbitrary integer | arbitrary integer | NO | already covers all `n` (uses `Int.negInduction`). |
| 3 | (hypotheses) | none | none | NO | the lemma is already hypothesis-free. |

#### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is literally mathlib's form, which is already general — arbitrary `CommRing`, arbitrary `n : ℤ`, no extra hypotheses).
Weakening opportunities: 0.

#### Modern-idiom check (Phase 4c)

Modern idiom available: **no**. The lemma is mathlib's own current formulation verbatim — there is no contemporary restatement that mathlib prefers over what mathlib already ships. (Any "improvement" would be a `/generalise` ticket against mathlib's `Degree.lean`, not against this project copy.)

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`. Lemmas introduce no definitional equalities or typeclass-search paths.

---

### Mathlib search-status: `WeierstrassCurve.coeff_ΨSq` (Phase 5)

[A] Lean-Finder       n/a (mathlib index tools; superseded by the direct source hit below)
[B] Loogle            n/a (the exact decl is already located by grep — see [D])
[C] LeanSearch        n/a (superseded by the exact source hit)
[D] Grep mathlib src  `coeff_ΨSq` over `.lake/packages/mathlib/.../DivisionPolynomial/Degree.lean` → **HIT at line 351**
[E] Name pattern      `WeierstrassCurve.coeff_ΨSq` → exact qualified-name match in mathlib's `Degree.lean`

Searched for both the user's current form and the literature-standard form — they coincide and both are present in mathlib.

**Concluded: found in mathlib as `WeierstrassCurve.coeff_ΨSq` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:351`); IDENTICAL form.**

Verification of identity (not merely same name):
- **Statement** — project line 349 `(W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = n ^ 2` vs mathlib line 351: identical, including the `@[simp]` attribute.
- **Proof body** — project lines 350–352 vs mathlib lines 352–354: identical, including the `Int.negInduction` `nat`/`neg` cases (`diff` shows only a one-line blank-line offset, no content difference).
- **Underlying `def ΨSq`** — project `DivisionPolynomial.lean:165` vs mathlib `Basic.lean:242`: byte-identical (`W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1`).
- **Provenance** — both files carry the same copyright header (David Kurniadi Angdinata, 2024). The project's own docstring calls itself "a project copy of mathlib's Basic file." The fork exists only because NagellLutz imports a forked `LutzNagell.EllipticDivisibilitySequence` "to avoid" a base-layer divergence (per `DivisionPolynomial.lean:13`), not because the `ΨSq` API itself differs.

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.coeff_ΨSq` (Phase 6.0)

Internal use count (within NagellLutz, excluding the declaring file): **0**
External-to-file callers: **0 distinct files** referencing `coeff_ΨSq` by name.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none outside `DivisionPolynomialDegree.lean`) | — |

Within the declaring file, `coeff_ΨSq` is consumed by its sibling forks `coeff_ΨSq_ne_zero` (line 354, `by simpa`) and `leadingCoeff_ΨSq` (line 370, `rw [..., coeff_ΨSq]`) — both themselves verbatim mathlib copies. Downstream consumers in the repo (e.g. HasseWeil) use the *degree* lemmas `natDegree_ΨSq` / `natDegree_ΨSq_le`, resolved against whichever `WeierstrassCurve.ΨSq` is in scope — they never call `coeff_ΨSq` directly.

Inline-derivation grep: none — nobody re-derives this coefficient inline; the fact is simply forked once.

Call-sites signal: **K = 0 direct uses outside the declaring file**, no inline re-derivation. Combined with the exact mathlib hit, this reinforces that the local copy exists only as scaffolding under the forked `ΨSq`, not as novel API.

#### Composition attempt (Phase 6a)

Not applicable in the usual sense: this is not a "compose-from-primitives" situation, it is a **literal duplicate**. The project's `coeff_ΨSq` *is* mathlib's `coeff_ΨSq` (same proof). Conclusion: **NOT-COMPOSABLE-needed** — there is nothing to compose; the canonical lemma already exists in mathlib and the project's is a copy.

---

## Verdict: `WeierstrassCurve.coeff_ΨSq`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the underlying fact (`lead ψₙ² = n²`, `deg = n²−1`) is standard textbook material (Silverman GTM 106, §III.3); but the operative finding is the exact mathlib duplicate.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — it is mathlib's own already-general form (arbitrary `CommRing`, all `n : ℤ`, no hypotheses); no modern-idiom improvement.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.coeff_ΨSq`, `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:351`, IDENTICAL statement + proof; the `ΨSq` definition is byte-identical too.
- Composition check (Phase 6): K = 0 external call sites; the project decl is a verbatim fork, nothing to compose or inline.

**Rationale.**

This declaration is not a candidate for mathlib because **mathlib already contains it, verbatim**. `WeierstrassCurve.coeff_ΨSq` in the project's `DivisionPolynomialDegree.lean` is a character-for-character copy — same `@[simp]` attribute, same statement, same `Int.negInduction` proof — of `WeierstrassCurve.coeff_ΨSq` in mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:351`. The two share an author (David Kurniadi Angdinata) and the underlying `WeierstrassCurve.ΨSq` definition is byte-identical between the project's `DivisionPolynomial.lean:165` and mathlib's `Basic.lean:242`. The project file's own module docstring describes itself as "a project copy of mathlib's Basic file." The copy exists for a purely structural reason — NagellLutz forks `LutzNagell.EllipticDivisibilitySequence` to dodge a base-layer divergence, and the division-polynomial degree file was copied wholesale on top of that forked base — not because the `ΨSq` coefficient API differs in any way from upstream.

WHY not (refactor-actionable):

Mathlib already has the result; the project copy is redundant scaffolding sitting on top of a forked EDS base. The forked-`ΨSq` track is the *only* reason the file can't trivially `import` mathlib's `DivisionPolynomial.Degree` today: the project's `WeierstrassCurve.ΨSq` is technically a *distinct* constant from mathlib's (different module, even though definitionally equal), so mathlib's `coeff_ΨSq` does not literally apply to the project's `W.ΨSq n` term without first reconciling the two `ΨSq`s. The real cleanup is therefore not "swap this one lemma" but "retire the whole `DivisionPolynomial` / `DivisionPolynomialDegree` fork once the forked `EllipticDivisibilitySequence` is reconciled with mathlib's." This is a project-policy/dedup task, owned by the consolidation effort, not a mathlib PR.

- Existing mathlib decl:        `WeierstrassCurve.coeff_ΨSq`
- Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:351`
- Our form follows in ≤1 line:  it does not merely *follow* — it is **identical**. Once the project's `ΨSq` is unified with mathlib's `ΨSq` (i.e. the fork is dropped), every use site of the project `coeff_ΨSq` is discharged by mathlib's `coeff_ΨSq` directly:
  ```lean
  example (W : WeierstrassCurve R) (n : ℤ) :
      (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = n ^ 2 := W.coeff_ΨSq n  -- mathlib's
  ```
- Call sites in our project (from Phase 6.0):  K = 0 by name outside the declaring file (used only internally by the equally-forked `coeff_ΨSq_ne_zero` / `leadingCoeff_ΨSq`).
- Refactor plan:
  1. This is a whole-file dedup, not a single-lemma swap. Track it as the consolidation ticket: "retire `projects/NagellLutz/LutzNagell/DivisionPolynomial{,Degree}.lean` in favour of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`."
  2. Precondition: reconcile `LutzNagell.EllipticDivisibilitySequence` (the forked EDS base named at `DivisionPolynomial.lean:13` as the reason for the fork) with mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`. Until the EDS fork is gone, the `ΨSq` constants stay distinct and mathlib's lemma can't be applied directly.
  3. Once unified, delete the project's `coeff_ΨSq` (and its siblings `natDegree_ΨSq{,_le,_pos}`, `leadingCoeff_ΨSq`, `coeff_ΨSq_ne_zero`, `ΨSq_ne_zero`, `natDegree_coeff_ΨSq_ofNat`) — they all duplicate mathlib's `Degree.lean` — and `import` mathlib's `DivisionPolynomial.Degree` instead. Internal consumers (the two sibling lemmas) disappear with the file; the repo's external consumers (HasseWeil) use the degree lemmas, which resolve against mathlib's versions after unification.
- Next action: do **not** open a mathlib PR. File / fold into the NagellLutz↔mathlib `DivisionPolynomial` de-duplication ticket (blocked on the `EllipticDivisibilitySequence` fork reconciliation). No new math; pure consolidation.

---

## Next step

Do not submit to mathlib — mathlib already has `WeierstrassCurve.coeff_ΨSq` verbatim (`DivisionPolynomial/Degree.lean:351`). Route to the consolidation/dedup track: retire the project's `DivisionPolynomial{,Degree}.lean` fork once `LutzNagell.EllipticDivisibilitySequence` is reconciled with mathlib's EDS, after which this lemma and its siblings are deleted in favour of the upstream `DivisionPolynomial.Degree` import.
