# /mathlibable report — `preNormEDS'_zero`

> AINTLIB /overview Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz theorem;
> elliptic curves; division polynomials; elliptic divisibility sequences).
> Target: `preNormEDS'_zero` at
> `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:739`.

## Verdict: **NO-mathlib-has-it**

`preNormEDS'_zero` is a **verbatim fork** of the existing mathlib lemma
`preNormEDS'_zero` in `Mathlib.NumberTheory.EllipticDivisibilitySequence`. Same name, same
root namespace, same statement, same one-line proof, same `@[simp]` attribute, over the same
`{R} [CommRing R] (b c d : R)` context.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); decl elaborates as written — trivial `rw`.
- decl `preNormEDS'_zero`:   ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:739`.
- qualified name:           `preNormEDS'_zero` (VERIFIED — root namespace; see below).
- kind:                     `lemma` (tagged `@[simp]`).
- has sorry:                no.
- module docstring summary: This file is a **fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`**
  (copyright header "Authors: David Kurniadi Angdinata" — the mathlib author of that file), extended with
  additional `EllSequence` / `IsEllSequence` API for the Nagell–Lutz development.

**Qualified-name verification.** The declaration sits in `section PreNormEDS` (opened at line 704).
Walking the `namespace … end` blocks before line 739: `namespace EllSequence … end EllSequence`
(lines 90–597) and `namespace IsEllSequence … end IsEllSequence` (lines 643–702) are both *closed*
before line 704. There is **no enclosing namespace** at line 739, so the qualified name is the bare
base name `preNormEDS'_zero`. (Mathlib's copy is likewise root-namespace.)

---

### Statement (Phase 1)

For a commutative ring `R` and parameters `b c d : R`,

> `preNormEDS' b c d 0 = 0`.

`preNormEDS'` is the ℕ-indexed auxiliary sequence for a normalised elliptic divisibility sequence,
defined recursively (lines 710–736) with initial values `W(0)=0, W(1)=1, W(2)=1, W(3)=c, W(4)=d` and
the standard even/odd EDS recurrences. `preNormEDS'_zero` is the base-case accessor reading off the
initial value `W(0)=0` — the formal restatement of the EDS normalisation convention `W(0)=0`. It is
one of five sibling accessors (`_zero`, `_one`, `_two`, `_three`, `_four`).

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (file-level `variable`, line 85).
- `(b c d : R)` — EDS parameters (section-level `variable`, line 706).

Proof (line 739–740):

```lean
@[simp]
lemma preNormEDS'_zero : preNormEDS' b c d 0 = 0 := by
  rw [preNormEDS']
```

One `rw [preNormEDS']` unfolds the equation lemma for the `0` case of the recursive definition.

---

### Literature search (Phase 2)

- WebSearch (`"mathlib preNormEDS' EllipticDivisibilitySequence preNormEDS'_zero"`) returns, as the top
  hit, the mathlib doc page
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.html`, confirming the lemma family lives in mathlib.
- The underlying mathematical object — Ward's normalised elliptic divisibility sequences with
  `W(0)=0, W(1)=1` — is classical (M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math.
  70 (1948); see also Silverman–Stephens, Shipsey's thesis). The condition `W(0)=0` is part of the
  definition of an EDS, not an independent theorem. arXiv references on EDS over commutative rings
  (e.g. 2604.05280) treat `W(0)=0` as a defining axiom.
- This is a base-case unfolding lemma — there is nothing to find in the literature beyond the
  definition itself; the "result" is entirely an artefact of the Lean recursive encoding.

### Mathlib search — five methods (Phase 3)

1. **Web doc lookup (authoritative).** `WebFetch` of the mathlib doc page returns, verbatim:
   ```
   theorem preNormEDS'_zero {R : Type u} [CommRing R] (b c d : R) :
     preNormEDS' b c d 0 = 0
   ```
   and lists the full sibling family `preNormEDS'_{zero,one,two,three,four,even,odd}`.

2. **Local mathlib package source (definitive).**
   `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`:
   - line 124: `def preNormEDS' : ℕ → R` — initial values `0,1,1,c,d` then the even/odd recurrence,
     **definitionally identical** to the fork (the fork merely adds explicit `have h4/h3/h2/h1`
     termination hints; the computed function is the same).
   - line 140–142:
     ```lean
     @[simp]
     lemma preNormEDS'_zero : preNormEDS' b c d 0 = 0 := by
       rw [preNormEDS']
     ```
     **byte-for-byte identical** to the fork at line 738–740.

3. **Name search.** Base name `preNormEDS'_zero` collides exactly with the mathlib declaration —
   same identifier, same root namespace.

4. **Statement/`simp`-shape search.** `preNormEDS' b c d 0 = 0` is the canonical `@[simp]` normal
   form already supplied by mathlib's lemma; nothing more general or differently-shaped is needed.

5. **Sibling cross-check.** The companion assessments in this same directory
   (`preNormEDS'_one.md`, `preNormEDS'.md`) reached the identical conclusion for the rest of the
   forked family — consistent with a wholesale fork of the mathlib EDS file.

**Conclusion of search:** the declaration is already in mathlib, identically.

### Generality analysis (Phase 4)

No generalisation is possible or meaningful: the statement is the `0`-case accessor of a fixed mathlib
definition over an arbitrary `CommRing` (already the natural minimal typeclass — the recurrence needs
ring subtraction). The literature-standard form is exactly `W(0)=0`. Mathlib's lemma and the fork are
the same maximally-general statement.

### Composition check (Phase 5)

`simp` / `rw [preNormEDS']` discharges it in one step from the definitional equation lemma — but this
is moot: the lemma is not *composable from* mathlib primitives, it **is** a mathlib primitive (the
named `@[simp]` accessor that mathlib already provides for exactly this purpose).

---

### Five-bucket decision

- **YES-add-as-is** — no; mathlib already has it.
- **YES-but-generalise-first** — no.
- **NO-mathlib-has-it** — **YES.** `Mathlib.NumberTheory.EllipticDivisibilitySequence.preNormEDS'_zero`
  is the same lemma (same name, namespace, statement, proof, attribute, typeclass context). The
  AINTLIB occurrence exists only because the project forked the mathlib EDS file.
- **NO-composable-from-mathlib** — not the primary reason (it is the primitive itself, not a
  composition), though `simp [preNormEDS']` would also close it.
- **BORDERLINE-needs-human** — no; the match is exact and unambiguous.

**Final verdict: NO-mathlib-has-it.**

Recommended action for the consolidation pass: drop the forked `preNormEDS'_zero` (and its sibling
`preNormEDS'` accessor family) in favour of `import Mathlib.NumberTheory.EllipticDivisibilitySequence`,
unless the fork must stay self-contained for the in-flight Nagell–Lutz `EllSequence`/`IsEllSequence`
extensions that build on top of it. Any downstream `simp` reliance is preserved — mathlib's lemma is
also `@[simp]`.

---

#### Evidence appendix

- Fork: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`
  - def `preNormEDS'`: lines 710–736
  - lemma `preNormEDS'_zero`: lines 738–740
- Mathlib (local pin): `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
  - def `preNormEDS'`: lines 124–138
  - lemma `preNormEDS'_zero`: lines 140–142
- Mathlib doc: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html`
