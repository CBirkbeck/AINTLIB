# /mathlibable report — `WeierstrassCurve.preΨ'_odd`

## TL;DR

**Verdict: `NO-mathlib-has-it`.** This declaration is a **byte-for-byte copy** of
mathlib's `WeierstrassCurve.preΨ'_odd` (same namespace, same statement, same
proof). The project file's own module docstring states it is "a copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`", forked only
to import the project's own `EllipticDivisibilitySequence` instead of mathlib's
(to avoid a `normEDS` / `complEDS` name clash). Nothing to upstream; the fork
already shadows the upstream original.

---

### Baseline (Phase 0)
- lake build:               not run (local build is stale per task brief); assessment reasons from source — both project and mathlib sources read directly on disk
- decl `WeierstrassCurve.preΨ'_odd`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:104`
- kind:                      `lemma`
- has sorry:                 no  (body is `preNormEDS'_odd ..`)
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.)."

**Qualified name confirmed.** Declared inside `namespace WeierstrassCurve`
(opened at line 27) and `section preΨ'` (line 60). Parsed qualified name
`WeierstrassCurve.preΨ'_odd` is correct.

---

### Statement (Phase 1)

`WeierstrassCurve.preΨ'_odd` is the **odd-index recurrence** for the auxiliary
univariate division polynomials `preΨ'ₙ` of a Weierstrass curve `W` over a
commutative ring `R`. For `m : ℕ`, it states the value at index `2(m+2)+1` in
terms of five lower-index values, with the `Ψ₂Sq²` factor (the square of the
2-division polynomial congruent to `ψ₂²`) distributed by the parity of `m`:

```
preΨ'(2(m+2)+1) = preΨ'(m+4)·preΨ'(m+2)³·(Even m ? Ψ₂Sq² : 1)
               − preΨ'(m+1)·preΨ'(m+3)³·(Even m ? 1 : Ψ₂Sq²)
```

It is the curve-specialised instance of the generic elliptic-divisibility-sequence
odd recurrence `preNormEDS'_odd` (specialising the EDS parameters
`b, c, d := Ψ₂Sq², Ψ₃, preΨ₄`), and the proof is literally `preNormEDS'_odd ..`.

Variables / typeclasses (Lean side):
- `{R : Type r} [CommRing R]` — base commutative ring
- `(W : WeierstrassCurve R)` — the Weierstrass curve (provides `Ψ₂Sq`, `Ψ₃`, `preΨ₄`, `preΨ'`)
- `(m : ℕ)` — the recurrence index parameter

Hypotheses (Lean side): none.

Conclusion (math): the odd-step EDS recurrence for `preΨ'` on a Weierstrass curve.
Conclusion (Lean): an equation in `R[X]` (`Polynomial R`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a recurrence-step lemma, a one-line `:= preNormEDS'_odd ..` specialisation
of a generic EDS lemma; not a named theorem, not a `## Main results` entry, not a
new structure.

### One-line check (Phase 2b)

Body line count: 1 substantive line (`preNormEDS'_odd ..`).
One-liner verdict: n/a — kind is `lemma`, not `def`. (The 2b def-exemption table
applies only to `def`/`abbrev`/`structure`. A one-line *proof term* is normal and
not a negative signal in the same way.)

---

### Literature search (Phase 3)

**Phase 3 is moot here and is recorded as such.** The decl is provably identical
to an existing mathlib declaration (Phase 5), so the literature-standard-form
question — "is the project's form at the right generality?" — is already answered:
the project's form *is* mathlib's chosen form, character for character. The lit
search exists to ground a generality/novelty judgment for candidate *additions*;
there is no addition to make.

For completeness, the underlying mathematics is standard:

| # | Channel | Query | Hit? | Standard form | Notes |
|---|---------|-------|------|---------------|-------|
| 1 | Provenance (definitive) | mathlib `WeierstrassCurve.preΨ'_odd` | yes | identical decl | `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:181`; authored by David Kurniadi Angdinata (same copyright header as the project file) |
| 2 | Concept (background) | division polynomials of elliptic curves; recurrence relations | yes | Silverman, *The Arithmetic of Elliptic Curves*, Exercise 3.7 (division polynomials); Ward, "Memoir on elliptic divisibility sequences" (1948) | the ψₙ recurrence and EDS structure are classical |
| 3 | nLab / Stacks / MathOverflow / arXiv | — | n/a | — | not run: the decl is a verified mathlib copy, so external generality grounding cannot change the verdict. Recording as n/a (provenance-resolved) rather than spending the exhaustive sweep on an already-decided case. |

### Literature summary (Phase 3)

Concept identified as: elliptic divisibility sequence / division-polynomial odd
recurrence — but the operative fact is provenance, not literature: **the
declaration is a copy of an existing mathlib lemma by the same author.**

---

### Generality analysis (Phase 4)

Not applicable in the usual sense — there is no generality gap to assess because
the project decl and the mathlib decl are **identical**. Both are stated over an
arbitrary `[CommRing R]` with the recurrence indexed by `m : ℕ`. The generic EDS
lemma `preNormEDS'_odd` (over any `[CommRing R]`, parameters `b c d : R`) is the
maximally general form mathlib already carries; `preΨ'_odd` is the standard
curve-specialisation of it that mathlib also already carries. Verdict box:

- Current form vs mathlib: **IDENTICAL** (0 weakening opportunities; nothing to generalise).
- Phase 4c modern-idiom: n/a — kind is `lemma`; no reformulation can differ from
  the verbatim-equal mathlib lemma.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no new definitional equalities or
typeclass-search paths introduced).

---

### Mathlib search (Phase 5)

```
### Mathlib search-status: WeierstrassCurve.preΨ'_odd

[A] Lean-Finder       n/a — resolved by direct source read (stronger than index)
[B] Loogle            n/a — resolved by direct source read
[C] LeanSearch        n/a — resolved by direct source read
[D] Grep mathlib src  grep "preΨ'_odd" over .lake/packages/mathlib/  → HIT
[E] Name pattern      "WeierstrassCurve.preΨ'" + "preNormEDS'_odd"   → HIT (both)

Searched for both:
  - the project's current form  → found, identical
  - the generic/general form    → found: preNormEDS'_odd
```

**Concluded: found in mathlib as `WeierstrassCurve.preΨ'_odd`; IDENTICAL form.**

Evidence (on-disk, this repo):
- Project:  `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:104-107`
- Mathlib:  `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:181-184`

The two statements were read side by side and match token-for-token (same
namespace `WeierstrassCurve`, same signature `(m : ℕ)`, same RHS with the
`if Even m then W.Ψ₂Sq ^ 2 else 1` / `if Even m then 1 else W.Ψ₂Sq ^ 2` parity
split, same proof body `preNormEDS'_odd ..`).

The only difference between the project file and the mathlib file is the *import*:
the project's `DivisionPolynomial.lean` imports `LutzNagell.EllipticDivisibilitySequence`
(a sibling copy of `Mathlib.NumberTheory.EllipticDivisibilitySequence`), so its
`preNormEDS'_odd` resolves to the project's copy. Both copies of `preNormEDS'_odd`
are themselves identical (project `EllipticDivisibilitySequence.lean` vs mathlib
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:166`).

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.preΨ'_odd`

Internal use count (project, excluding the declaring file): see grep below.
The relevant point: even if there are internal consumers, they consume the
*project copy* only because the project re-derives the whole `DivisionPolynomial`
+ `EllipticDivisibilitySequence` stack locally; they would consume the mathlib
decl directly once the fork is collapsed.

```
grep -rn "preΨ'_odd" projects/NagellLutz --include=*.lean
  → DivisionPolynomial.lean:104  (the declaration itself)
```

(No other in-project references found; the lemma is part of the mirrored mathlib
API surface, kept so the copied file elaborates, not because NagellLutz proofs
call it directly. Mathlib's own `Basic.lean:385` uses it, e.g. inside `Ψ₃` /
small-index computations.)

#### Composition

n/a in the "build it from primitives" sense — the result already exists verbatim
upstream, so there is nothing to compose. The "composition" is trivial: it *is*
the mathlib lemma.

Conclusion: **NOT-COMPOSABLE (irrelevant)** — superseded by the exact-match Phase 5 hit.

---

## Verdict: `WeierstrassCurve.preΨ'_odd`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): provenance-decisive — the decl is a copy of an existing mathlib lemma by the same author (David Kurniadi Angdinata); underlying math is classical (Ward 1948; Silverman Ch. 3).
- Generality analysis (Phase 4): IDENTICAL to mathlib; 0 weakening opportunities.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.preΨ'_odd`; identical form.
- Composition check (Phase 6): n/a — exact match supersedes.

**Rationale.**

The project's `DivisionPolynomial.lean` is, by its own module docstring, a
deliberate copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`,
re-imported on top of a local copy of the EDS module so that the duplicated
`normEDS`/`complEDS` names do not clash with mathlib's. As a direct consequence,
`WeierstrassCurve.preΨ'_odd` here is character-for-character the same declaration
that already lives in mathlib at `DivisionPolynomial/Basic.lean:181` — same
namespace, same `(m : ℕ)` signature, same parity-split right-hand side, same
proof term `preNormEDS'_odd ..`. There is no new mathematical content, no
generality gap, and no naming divergence to reconcile. Mathlib does not merely
have "something like this" — it has *this*, verbatim.

This is the canonical `NO-mathlib-has-it` outcome for a known-fork project: the
correct disposition is not to upstream anything (mathlib already has it) but to
treat the entire local `DivisionPolynomial` + `EllipticDivisibilitySequence` fork
as a deduplication target — collapse it back onto mathlib once the name-clash that
motivated the fork is resolved (e.g. by qualifying or `open`-scoping the EDS names
rather than copying the module).

**WHY not (refactor-actionable).**
- Mathlib already has the identical lemma: `WeierstrassCurve.preΨ'_odd`.
- Existing mathlib decl:  `WeierstrassCurve.preΨ'_odd`
- Located at:             `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:181`
- Our form follows in 0 lines — it is the same declaration:
  ```lean
  -- project decl ≡ mathlib decl, both:
  lemma preΨ'_odd (m : ℕ) : W.preΨ' (2 * (m + 2) + 1) =
      W.preΨ' (m + 4) * W.preΨ' (m + 2) ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
        W.preΨ' (m + 1) * W.preΨ' (m + 3) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=
    preNormEDS'_odd ..
  ```
- Call sites in our project: 0 outside the declaring file (it is part of a mirrored
  API surface, kept so the copied file elaborates).
- Refactor plan: this lemma cannot be deleted in isolation — it is one line of a
  wholesale copy of a mathlib file. The actionable unit is the **whole fork**, not
  this decl:
  1. Resolve the `normEDS`/`complEDS` name clash that motivated copying
     `Mathlib.NumberTheory.EllipticDivisibilitySequence` →
     `LutzNagell.EllipticDivisibilitySequence` (prefer `open ... renaming` / local
     qualification, or namespacing, over duplicating the module).
  2. Delete `LutzNagell/DivisionPolynomial.lean` and
     `LutzNagell/EllipticDivisibilitySequence.lean`; `import` the mathlib modules
     `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` and
     `Mathlib.NumberTheory.EllipticDivisibilitySequence` instead.
  3. Repoint NagellLutz's downstream consumers (`Universal`, the General*/PID*
     tracks, etc.) at the mathlib `WeierstrassCurve.preΨ'…` / `preNormEDS…` API.
  4. Re-build NagellLutz; fix any residual skew from the de-fork.

  This is a project-policy / dedup ticket on `main` (the AINTLIB "reuse, don't
  duplicate" cardinal rule), not a mathlib PR.

**Next action:** do **not** open a mathlib PR. File an AINTLIB cleanup/dedup
ticket to collapse the `LutzNagell.DivisionPolynomial` +
`LutzNagell.EllipticDivisibilitySequence` fork back onto the mathlib originals
once the EDS name-clash is resolved; this lemma disappears with that refactor.

---

## Next step

File an AINTLIB dedup ticket (lane:cleanup / generalise-not-applicable) to
de-fork `LutzNagell.DivisionPolynomial` and `LutzNagell.EllipticDivisibilitySequence`
back onto `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` and
`Mathlib.NumberTheory.EllipticDivisibilitySequence`, resolving the `normEDS` /
`complEDS` name clash by qualification rather than duplication. `WeierstrassCurve.preΨ'_odd`
is already in mathlib verbatim and requires no upstreaming.
