# /mathlibable report — `WeierstrassCurve.natDegree_preΨ'`

**TL;DR — `NO-mathlib-has-it`.** This lemma is a *verbatim copy* of an existing
mathlib lemma. The NagellLutz file `DivisionPolynomialDegree.lean` is, by its own
docstring, "a project copy of mathlib's Basic file"; it forks
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`. The
declaration `WeierstrassCurve.natDegree_preΨ'` is present in mathlib with an
identical statement, identical `variable`/`open` context, identical `@[simp]`
attribute, and an identical proof term. There is nothing to upstream — the entire
forked file should eventually be deleted in favour of the mathlib import.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); decl read directly from source
- decl `WeierstrassCurve.natDegree_preΨ'`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:247`
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  "Division polynomials of Weierstrass curves" — explicitly "a project copy of mathlib's Basic file"; computes leading terms / degrees of `preΨ`, `ΨSq`, `Φ`.

Qualified name (VERIFIED from source): `WeierstrassCurve.natDegree_preΨ'`
(namespace `WeierstrassCurve` opened at line 55; lemma `natDegree_preΨ'` at line 247).

---

### Statement (Phase 1)

`WeierstrassCurve.natDegree_preΨ'` is a theorem stating that, for a Weierstrass
curve `W` over a commutative ring `R` and a natural number `n` whose image in `R`
is nonzero, the `n`-th "pre-ψ" division polynomial `preΨ' n` (a univariate
polynomial in `R[X]`) has `natDegree` exactly `(n² − 4)/2` when `n` is even and
`(n² − 1)/2` when `n` is odd.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the base commutative ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve (carries the `aᵢ` coefficients).

Hypotheses (Lean side):
- `{n : ℕ}` — the division-polynomial index.
- `(h : (n : R) ≠ 0)` — the index is nonzero in `R` (ensures the leading coefficient survives; e.g. characteristic does not divide `n`).

Conclusion (math): `deg(preΨ_n) = (n² − [4 if n even else 1]) / 2`.

Conclusion (Lean): `(W.preΨ' n).natDegree = (n ^ 2 - if Even n then 4 else 1) / 2`.

The proof is a one-liner combining the degree upper bound with a nonzero leading
coefficient:
`natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_preΨ'_le n) <| W.coeff_preΨ'_ne_zero h`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A helper degree-computation lemma (one-line proof from two sibling lemmas);
not a named theorem and not a `## Main results` headline — though it *is* listed under
the file's "Main statements" as part of the standard division-polynomial degree API.

(Note: literature width would be EXHAUSTIVE in general, but this phase is moot — the
decl is a byte-identical fork of an existing mathlib lemma, so Phase 5 short-circuits
the verdict. The literature/generality/composition phases below are recorded for
completeness but cannot change a verbatim-match outcome.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. No defeq/diamond surface.

---

### Literature search (Phase 3)

The mathematical content — degrees and leading coefficients of elliptic
division polynomials — is classical and standard.

| #  | Channel                          | Query / source                                                                 | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | Primary source (in-file ref)     | Silverman, *The Arithmetic of Elliptic Curves* (cited in file docstring, Exercise 3.7) | yes  | `ψ_n` has degree `(n²−1)/2` (n odd) / `(n²−4)/2`·(monomial) (n even) | The canonical reference; the file’s own `## References` |
|  2 | Standard text                    | Washington, *Elliptic Curves: Number Theory and Cryptography*, §3.2 division polynomials | yes  | Same degree/leading-coeff formulas for `ψ_n` | Division-polynomial recursion + degree count is textbook |
|  3 | Mathlib provenance               | mathlib `DivisionPolynomial/Degree.lean` module docstring + author             | yes  | Identical statement, by the same author (D. K. Angdinata) | The project file is a copy of this exact mathlib file |

(WebSearch / ChatGPT MCP / nLab / Stacks / arXiv channels not separately exhausted:
the literature standard is not in question, and they cannot alter a verbatim-mathlib
match. The decisive evidence is the mathlib source match in Phase 5, not the lit form.)

### Literature summary (Phase 3)

Concept identified as: degree (and leading coefficient) of the elliptic division
polynomial `ψ_n` / its "pre-ψ" normalisation `preΨ_n`.
Sources agree on the standard form: yes — degree `(n²−1)/2` for odd `n`,
`(n²−4)/2` for the even normalisation; leading coefficient `n` (odd) / `n/2` (even).
Most general standard form: the formula holds over any commutative ring once `n` is
invertible / nonzero in the ring — exactly mathlib's hypothesis `(n : R) ≠ 0`.
Disagreement with the literature: none. The mathlib/project form (`CommRing R`,
`(n : R) ≠ 0`) is already at the maximal natural generality.

---

### Generality analysis (Phase 4)

Literature-standard form: degree formula over a commutative ring with `n` nonzero.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring         | NO                  | Already the base; the whole division-polynomial API is built over `CommRing`. |
| 2 | `(h : (n : R) ≠ 0)`    | `n` nonzero in `R`| `n` invertible/nonzero in `R` | NO            | Necessary: if `n = 0` in `R` the leading term collapses and the degree drops. Minimal hypothesis. |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL.
Number of weakening opportunities found: 0.
This is moot for the verdict — mathlib already contains this exact form.

### Modern-idiom check (Phase 4c)

Modern idiom available: no. This is a concrete polynomial-degree identity stated at
the natural generality (`CommRing`, `(n : R) ≠ 0`). No filter/typeclass/universal-
property restatement applies, and mathlib already houses it in precisely this form.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search
paths introduced).

---

### Mathlib search-status: `WeierstrassCurve.natDegree_preΨ'`

[A] Lean-Finder       n/a (offline reasoning) — see [D]
[B] Loogle            n/a (offline reasoning) — see [D]
[C] LeanSearch        n/a (offline reasoning) — see [D]
[D] Grep mathlib src  `grep -rn "natDegree_preΨ'" .lake/packages/mathlib/Mathlib/`  →  **HIT**
[E] Name pattern      same grep                                                     →  **HIT**

Found in mathlib as **`WeierstrassCurve.natDegree_preΨ'`** at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:250`.

Verification of identity (project line 247 vs mathlib line 250):

```lean
-- project: projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:246–249
@[simp]
lemma natDegree_preΨ' {n : ℕ} (h : (n : R) ≠ 0) :
    (W.preΨ' n).natDegree = (n ^ 2 - if Even n then 4 else 1) / 2 :=
  natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_preΨ'_le n) <| W.coeff_preΨ'_ne_zero h

-- mathlib: .../DivisionPolynomial/Degree.lean:249–252
@[simp]
lemma natDegree_preΨ' {n : ℕ} (h : (n : R) ≠ 0) :
    (W.preΨ' n).natDegree = (n ^ 2 - if Even n then 4 else 1) / 2 :=
  natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_preΨ'_le n) <| W.coeff_preΨ'_ne_zero h
```

Identical: namespace (`WeierstrassCurve`), section context
(`open Polynomial`, `variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)`),
attribute (`@[simp]`), signature, and proof term. A line-level `diff` of the two
decl blocks confirms `natDegree_preΨ'` is byte-for-byte identical (the only nearby
divergence is in the *neighbouring* lemma `coeff_preΨ'`, where mathlib uses
`convert!` + a split `simp` and the project uses `convert ... <;>`; that does not
touch `natDegree_preΨ'`).

Concluded: **found in mathlib as `WeierstrassCurve.natDegree_preΨ'`; identical form.**

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.natDegree_preΨ'`

Internal use count (excluding the declaring file): **0**.
External-to-file callers: 0.

In-file uses (not counted, but shows the lemma is live API within the fork): it is
consumed at lines 252, 258, 262 (`natDegree_preΨ'_pos`, `leadingCoeff_preΨ'`,
`preΨ'_ne_zero`) and indirectly underpins the `preΨ`/`ΨSq`/`Φ` degree lemmas later
in the same file — exactly mirroring how mathlib's own `Degree.lean` uses it.

Inline-derivation grep: none — the project does not re-derive this; it forks the
whole file.

Composability signal: K = 0 external callers, but the lemma is not dead code — it is
one node of a forked copy of an entire mathlib module. The "composition" question is
moot: the form is already a single named mathlib lemma.

#### Composition attempt

Conclusion: NOT-COMPOSABLE-AND-IRRELEVANT — the result is not a composition target;
it is literally the same mathlib lemma. The verdict is decided by Phase 5, not 6.

---

## Verdict: `WeierstrassCurve.natDegree_preΨ'`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): standard classical result (Silverman Exercise 3.7;
  Washington §3.2); mathlib houses the same author's formalisation.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — no weakening, no modern-idiom
  restatement available; moot given the exact match.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.natDegree_preΨ'`**,
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:250` —
  identical statement, attribute, and proof.
- Composition check (Phase 6): n/a — verbatim duplicate, not a composition.

**Rationale:**

The NagellLutz file `DivisionPolynomialDegree.lean` is explicitly a fork of mathlib's
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` (the docstring
says "a project copy of mathlib's Basic file", the author, `## References`, `## Main
statements`, namespace, `variable` block and `open` are all identical to the mathlib
file). The specific declaration `WeierstrassCurve.natDegree_preΨ'` is present in
mathlib with a byte-for-byte identical statement and proof term. There is no
mathlibability question here: mathlib already has this exact lemma. It cannot be
"added" (it is already there) and there is no more-general or more-modern form to
upstream (the `CommRing R` + `(n : R) ≠ 0` form is already maximal).

WHY not (refactor-actionable):
Mathlib already has it, identically. The forked file duplicates an entire mathlib
module that the project could `import` directly. The right action is not a PR to
mathlib but a *de-duplication within NagellLutz*: replace the project's copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` with the upstream
imports, then delete `LutzNagell/DivisionPolynomial.lean` and
`LutzNagell/DivisionPolynomialDegree.lean` (or reduce them to whatever genuinely
diverges from mathlib, if anything). Since the project pins a recent mathlib that
*already contains* this file, the fork appears to be stale duplication left over from
before the upstreaming landed.

Existing mathlib decl:        `WeierstrassCurve.natDegree_preΨ'`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:250`
Our form follows in ≤1 line:  it *is* the mathlib decl — `exact W.natDegree_preΨ' h`.
Call sites in our project (Phase 6.0):  0 external to the declaring file (3 in-file
consumers that mathlib's own `Degree.lean` provides identically).

Refactor plan: this lemma is not consumed outside its forked file, so once the fork
is replaced by `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`
(and the sibling `Basic`/EDS files), the project decl simply disappears with the file.
No call-site rewriting is needed for this lemma specifically; the de-dup is at the
file/import level. Confirm whether any NagellLutz file deliberately diverges from
mathlib's division-polynomial API before deleting — if not, drop the whole fork.

Next action: delete the forked `DivisionPolynomial*` files from NagellLutz and import
mathlib's `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` instead;
`WeierstrassCurve.natDegree_preΨ'` then resolves to the mathlib lemma automatically.

---

## Next step

Delete `WeierstrassCurve.natDegree_preΨ'` (and its forked siblings) from the project;
replace the fork with `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`
(plus `Basic` / EDS as needed). No mathlib PR — mathlib already has this lemma identically.
