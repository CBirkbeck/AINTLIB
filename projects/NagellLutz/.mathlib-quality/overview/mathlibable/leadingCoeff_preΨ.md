# /mathlibable report — `WeierstrassCurve.leadingCoeff_preΨ`

## Verdict: NO-mathlib-has-it

Mathlib already contains this lemma **verbatim** — same name, same namespace,
same signature, same proof, same `@[simp]` attribute, same author. The project
file is a literal fork of the mathlib file it was copied from.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); reasoning from source
- decl `WeierstrassCurve.leadingCoeff_preΨ`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:308`
- kind:                      lemma (`theorem`)
- has sorry:                 no
- module docstring summary:  "computes the leading terms of certain polynomials associated to
  division polynomials of Weierstrass curves defined in `LutzNagell/DivisionPolynomial.lean`
  **(a project copy of mathlib's Basic file)**" — the docstring itself declares the fork.

---

### Statement (Phase 1)

`WeierstrassCurve.leadingCoeff_preΨ` states: for a Weierstrass curve `W` over a commutative
ring `R` and an integer `n` whose image in `R` is nonzero, the leading coefficient of the
`n`-th pre-division-polynomial `preΨₙ ∈ R[X]` equals `n / 2` if `n` is even and `n` if `n` is odd.

This is Silverman, *The Arithmetic of Elliptic Curves* (the file's cited reference): the
division polynomial `ψ_n` has leading coefficient `n` (for the normalised pre-version `preΨ`,
the even case carries the factor-of-two convention `n/2`).

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the base commutative ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve.
- `{n : ℤ}` — the index.

Hypotheses (Lean side):
- `(h : (n : R) ≠ 0)` — `n` is nonzero in `R` (i.e. `char R ∤ n`), so the leading term doesn't
  collapse.

Conclusion (math): `lead(preΨₙ) = n/2` if `n` even, else `n`.

Conclusion (Lean): `(W.preΨ n).leadingCoeff = if Even n then n / 2 else n`.

Exact statement (project, line 308):
```lean
@[simp]
lemma leadingCoeff_preΨ {n : ℤ} (h : (n : R) ≠ 0) :
    (W.preΨ n).leadingCoeff = if Even n then n / 2 else n := by
  rw [leadingCoeff, W.natDegree_preΨ h, coeff_preΨ]
```

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A one-step corollary (`leadingCoeff = coeff` at the established degree), not a named
theorem or a new structure. It is a helper packaging `natDegree_preΨ` + `coeff_preΨ`.

(Per skill: literature width would normally be EXHAUSTIVE regardless. Here the literature/
generality phases are **moot** — Phase 5 finds the *identical* declaration already in mathlib,
which is dispositive. The lemma did not originate in this project; it was copied out of mathlib.
Running a literature sweep on the leading coefficient of a division polynomial would only
re-derive what mathlib + Silverman already state and cannot change a verbatim-duplicate verdict.)

### One-line check (Phase 2b)

Kind is `lemma` → n/a (one-line check applies to `def`/`abbrev`/`structure`). The proof is a
3-rewrite one-liner, which is exactly mathlib's proof.

---

### Mathlib search (Phase 5) — DISPOSITIVE

[A] Lean-Finder / [C] LeanSearch — not needed; direct source hit is exact.
[B] Loogle — n/a; exact-name source match found.
[D] Grep mathlib src — **HIT.**
[E] Name pattern — **HIT.**

Direct grep of the mathlib package:
```
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:310:
@[simp]
lemma leadingCoeff_preΨ {n : ℤ} (h : (n : R) ≠ 0) :
    (W.preΨ n).leadingCoeff = if Even n then n / 2 else n := by
  rw [leadingCoeff, W.natDegree_preΨ h, coeff_preΨ]
```

**Identical to the project's lines 308–311.** A `diff` of the lemma body confirms the six lines
match byte-for-byte. The mathlib `Degree.lean` even shares the project file's *entire* module
docstring — same "Mathematical background" paragraph, same "Main statements" bullet list
(`WeierstrassCurve.leadingCoeff_preΨ` is listed), same Silverman reference, same author header
(David Kurniadi Angdinata). The underlying `preΨ` definition is likewise identical: project
`LutzNagell/DivisionPolynomial.lean` is a copy of mathlib `…/DivisionPolynomial/Basic.lean`
(same `noncomputable def preΨ`, `preΨ_ofNat`, `preΨ_neg`), so the two `leadingCoeff_preΨ`
statements are about the same object with the same `[CommRing R]` generality.

Concluded: **found in mathlib as `WeierstrassCurve.leadingCoeff_preΨ`; identical form**
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:310`).

---

### Generality analysis (Phase 4) — n/a (moot)

The project form and the mathlib form are the *same declaration* at the *same* generality
(`[CommRing R]`, integer index, hypothesis `(n : R) ≠ 0`). There is nothing to weaken or
modernise relative to mathlib; mathlib *is* the target. (No `NoZeroDivisors`/domain assumption is
needed here — the hypothesis `(n : R) ≠ 0` already suffices — and mathlib uses precisely that.)

### Diamond/defeq risk (Phase 4.5) — n/a

Declaration kind is `lemma`; no definitional content.

---

### Call sites (Phase 6.0)

Internal use count (excluding the declaring file): **2** genuine rewrite sites.
External-to-file callers: 2 distinct files, both inside this same project.

| Caller file:line                                                   | Usage pattern                                  |
|--------------------------------------------------------------------|------------------------------------------------|
| `LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean:129`              | `rw [W.leadingCoeff_preΨ hp_R_ne]`             |
| `LutzNagell/LutzNagellTheorem/GeneralPrimeOrder.lean:98`          | `have := W.leadingCoeff_preΨ hp_ne`            |

(Other grep hits at `DivisionPolynomialDegree.lean:32/141/256` are the docstring bullet and the
sibling lemmas `leadingCoeff_preΨ₄` / `leadingCoeff_preΨ'`, not this lemma.)

Both call sites use dot notation `W.leadingCoeff_preΨ`. Because mathlib's lemma has the identical
name, namespace, and argument shape, **both call sites work verbatim against mathlib's lemma**
once the import is switched.

Inline re-derivation grep: none — consumers use the lemma, they don't re-derive it. The API is
real; it just already lives upstream.

### Composition check (Phase 6) — n/a

No composition needed: the exact lemma is already in mathlib.

---

## Verdict: `WeierstrassCurve.leadingCoeff_preΨ`

**Category:** NO-mathlib-has-it

**Evidence:**
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.leadingCoeff_preΨ`,
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:310`; **identical form**
  (byte-for-byte same statement, proof, `@[simp]`, namespace, author, docstring).
- Generality (Phase 4): n/a — same declaration, same generality; nothing to weaken.
- Call sites (Phase 6.0): 2 internal rewrite sites, both portable to mathlib unchanged.
- Composition (Phase 6): n/a.

**Rationale:**

This lemma is not a NagellLutz contribution at all — it is a verbatim copy of an existing mathlib
declaration. The project's `DivisionPolynomialDegree.lean` is a fork of
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` (the file headers,
docstrings, author lines, and "Main statements" lists are the same; the `preΨ` object is defined
identically in the forked `DivisionPolynomial.lean` ↔ mathlib `Basic.lean`). `leadingCoeff_preΨ`
appears at the same place in both, with the same `[CommRing R]` generality and the same
three-rewrite proof. Mathlib unquestionably has it.

The actionable point is therefore not "add to mathlib" but "de-fork." This is consistent with the
sibling `/overview` mathlibable reports for the other declarations in this file
(`coeff_preΨ'`, `coeff_Ψ₃`, `natDegree_Ψ₃_pos`, `leadingCoeff_Ψ₂Sq`, …), which all independently
recommend deleting the duplicated copy and importing the mathlib originals.

**WHY not (refactor-actionable):**
Mathlib already has this exact lemma. The project re-declares it only because it forks the whole
`DivisionPolynomial.{Basic,Degree}` pair. Nothing about `leadingCoeff_preΨ` needs changing in
mathlib.

  Existing mathlib decl:        `WeierstrassCurve.leadingCoeff_preΨ`
  Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:310`
  Our form follows in ≤1 line:  it *is* the mathlib form — no derivation needed:
  ```lean
  example {R : Type*} [CommRing R] (W : WeierstrassCurve R) {n : ℤ} (h : (n : R) ≠ 0) :
      (W.preΨ n).leadingCoeff = if Even n then n / 2 else n :=
    W.leadingCoeff_preΨ h
  ```
  Call sites in our project (from Phase 6.0): **2**
  (`PIDPrimeOrder.lean:129`, `GeneralPrimeOrder.lean:98`).

  Refactor plan: this lemma should not be deleted in isolation — it is one line of a whole forked
  file. The correct cleanup (matching the other reports in this directory) is to **delete the fork
  files** `LutzNagell/DivisionPolynomialDegree.lean` and its companion
  `LutzNagell/DivisionPolynomial.lean` wholesale, and replace every downstream
  `import LutzNagell.DivisionPolynomialDegree` with
  `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`
  (and `.Basic` where the Basic copy was imported). Because the `WeierstrassCurve.*` names are
  unchanged, the 2 call sites above (`W.leadingCoeff_preΨ h`) need **no edit beyond the import
  line**. The one known blocker for the wholesale de-fork is the `normEDS`/`complEDS` /
  `EllipticDivisibilitySequence` naming clash flagged in the sibling reports; resolve that by
  `open`/alias rather than re-defining, then the deletion is mechanical.

  Next action: do not PR this lemma to mathlib (it is already there). Fold it into the file-level
  de-fork cleanup ticket for `DivisionPolynomial{,Degree}.lean`.

---

## Next step

Delete the forked `LutzNagell/DivisionPolynomialDegree.lean` (with its companion
`DivisionPolynomial.lean`) and `import` mathlib's `DivisionPolynomial.Degree` (+ `.Basic`)
instead. The two `W.leadingCoeff_preΨ` call sites resolve unchanged against the identical mathlib
lemma. This is part of the project-wide de-fork already recommended across the sibling reports.
