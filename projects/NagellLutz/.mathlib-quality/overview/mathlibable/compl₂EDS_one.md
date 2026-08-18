# Mathlibable assessment: `compl₂EDS_one`

**Verdict: NO-mathlib-has-it**

**One-line rationale:** Verbatim duplicate of mathlib's `complEDS₂_one` (same statement, same
`@[simp]`, same proof) — this project file is the pre-merge fork of that very mathlib module.

---

## 1. The declaration under review

- **Qualified name:** `compl₂EDS_one` (top-level; no enclosing `namespace`)
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1041`

```lean
@[simp] lemma compl₂EDS_one : compl₂EDS b c d 1 = b := by simp [compl₂EDS]
```

It sits in `section Complement` (opened at line 1011, a *section* not a namespace), under
`variable (b c d : R) (m : ℤ)` with `[CommRing R]`. The base name parses to the qualified name
`compl₂EDS_one` unchanged.

Its definition dependency, `compl₂EDS` (line 1032):

```lean
/-- The "complement" of W(m) in W(2m) for a normalised EDS W is the witness of W(m) ∣ W(2m). -/
def compl₂EDS : R :=
  letI p := preNormEDS (b ^ 4) c d
  (p (m - 1) ^ 2 * p (m + 2) - p (m - 2) * p (m + 1) ^ 2) * if Even m then 1 else b
```

The lemma is one of a family (`compl₂EDS_zero = 2`, `compl₂EDS_one = b`, `compl₂EDS_two = d`)
giving the closed-form base values of the 2-complement sequence.

## 2. Literature search

The 2-complement sequence `Wᶜ₂` is the witness of the divisibility `W(k) ∣ W(2k)` for a normalised
elliptic divisibility sequence `W` (i.e. `W(k) · Wᶜ₂(k) = W(2k)`). This is standard EDS theory
(Ward 1948; Shipsey; Stange). `compl₂EDS_one = b` is merely the evaluation of that witness at
`k = 1`, where `W(1) = 1`, `W(2) = b` for the normalised EDS, so `Wᶜ₂(1) = W(2)/W(1) = b`. It is a
definitional base-case computation, not an independently citable theorem.

WebSearch (June 2026) for the concept returns, as the top two hits, the mathlib docs pages
themselves — `Mathlib.NumberTheory.EllipticDivisibilitySequence` and
`…/DivisionPolynomial/Basic` — which already document `complEDS₂` as "the 2-complement sequence …
that witnesses `W(k) ∣ W(2 * k)`". The literature standard form is exactly what mathlib already
encodes.

Sources:
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html
- https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence

## 3. Mathlib search (five methods)

The decisive evidence is in the **repo's own pinned mathlib** (revision `d90090f`), file
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`:

```lean
-- mathlib line 246
def complEDS₂ (k : ℤ) : R :=
  (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
    preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b

-- mathlib line 254
@[simp]
lemma complEDS₂_one : complEDS₂ b c d 1 = b := by
  simp [complEDS₂]
```

Both `complEDS₂` and `complEDS₂_one` are **top-level** (the surrounding `section PreNormEDS` is a
section, not a namespace — confirmed: the only `^namespace/^end` markers around them are
`end IsEllDivSequence` / `end PreNormEDS`). So the mathlib qualified name is **`complEDS₂_one`**.

**Definitional identity.** The project's `compl₂EDS` and mathlib's `complEDS₂` are
character-for-character the same expression — the project's `letI p := preNormEDS (b ^ 4) c d` is
just a local abbreviation for the four `preNormEDS (b ^ 4) c d` occurrences mathlib writes inline.
The lemma, its `@[simp]` attribute, its statement `… 1 = b`, and its proof `by simp [compl₂EDS]`
vs `by simp [complEDS₂]` are identical up to the identifier spelling (`compl₂` ↔ `complEDS₂`).

**Provenance.** The project file carries the header `Copyright (c) 2024 David Kurniadi Angdinata`
— the same author as the mathlib module. The CLAUDE.md memo states this project "FORKS parts of
mathlib (`Mathlib.NumberTheory.EllipticDivisibilitySequence`)". This is precisely the pre-merge
fork: the project's `compl₂EDS*` naming was the original draft; mathlib upstreamed it as
`complEDS₂*` (and then built the richer `complEDS'` / `complEDS` general-complement API and the
`complEDSRec` recursors on top, all already in the pinned mathlib).

## 4. Generality analysis

No generalisation gap. Both versions live over an arbitrary `[CommRing R]` with the same three ring
parameters `b c d : R`. The literature-standard generality is already met by the mathlib form. There
is nothing to weaken or strengthen.

## 5. Composition check

Not applicable in the usual sense (the exact named lemma exists), but for completeness: even absent
the named lemma it is a one-line `simp [complEDS₂]` unfold — but mathlib already ships that exact
one-liner, attributed `@[simp]`, so consumers get it for free without even citing it.

## 6. Verdict

**NO-mathlib-has-it.** `compl₂EDS_one` is a verbatim fork-duplicate of mathlib's `complEDS₂_one`,
present in the exact mathlib revision (`d90090f`) this repository is pinned to. Same statement, same
`@[simp]`, same proof, same generality; the underlying `compl₂EDS` def is identical to mathlib's
`complEDS₂`. Nothing to add.

**Action for the consolidation:** drop the project's forked `compl₂EDS` / `compl₂EDS_*` block
(and the rest of the duplicated `section Complement` / `EllSequence` complement track) in favour of
mathlib's `complEDS₂` / `complEDS₂_*` and `complEDS` API; rewrite downstream NagellLutz / division
polynomial `ω` code (`DivisionPolynomialOmega.lean`, `EllipticDivisibilitySequence.lean`) to the
mathlib names.

**Mathlib equivalent:** `complEDS₂_one`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, def `complEDS₂`).
