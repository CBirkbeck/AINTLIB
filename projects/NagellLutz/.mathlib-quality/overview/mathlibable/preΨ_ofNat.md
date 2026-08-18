# /mathlibable report — `WeierstrassCurve.preΨ_ofNat`

### Baseline (Phase 0)
- lake build:               not re-run (env note: local build stale); decl reasoned from source
- decl `WeierstrassCurve.preΨ_ofNat`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:121`
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

The qualified name is verified as `WeierstrassCurve.preΨ_ofNat`: the declaration sits inside `namespace WeierstrassCurve` (open at line 27 of the project file), with `variable (W : WeierstrassCurve R)`.

---

### Statement (Phase 1)

`WeierstrassCurve.preΨ_ofNat` states that for a Weierstrass curve `W` over a commutative ring `R`, the auxiliary division-polynomial sequence `preΨ : ℤ → R[X]` agrees with its natural-number counterpart `preΨ' : ℕ → R[X]` on non-negative inputs: for every `n : ℕ`, `W.preΨ (↑n) = W.preΨ' n`.

This is a definitional bridge between the ℤ-indexed and ℕ-indexed forms of the pre-normalised elliptic divisibility sequence underlying the division polynomials. `preΨ` is defined as `preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄`, and `preΨ'` as `preNormEDS' (...)`; the lemma is the curve-specialised image of the generic `preNormEDS_ofNat`.

Variables / typeclasses (Lean side):
- `{R : Type r} [CommRing R]` — base ring of the Weierstrass curve.
- `(W : WeierstrassCurve R)` — the curve.
- `(n : ℕ)` — the index.

Hypotheses: none.

Conclusion (math): `preΨ_n(W) = preΨ'_n(W)` for `n ≥ 0`.
Conclusion (Lean): `W.preΨ ↑n = W.preΨ' n`.

Proof body: `preNormEDS_ofNat ..` (one term, the generic EDS lemma applied with the three curve-specific coefficients filled by `..`).

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a glue/casting lemma (`@[simp]`) bridging ℤ- and ℕ-indexed forms of an already-defined sequence; not a named theorem, not a new structure, not a `## Main results` entry. It is a verbatim copy of an existing mathlib lemma.

(Literature width would normally be EXHAUSTIVE, but Phase 5 located an *identical* mathlib declaration, which conclusively resolves the verdict — see the Phase 7 gate note. A full nine-channel literature sweep on a "ℤ-index agrees with ℕ-index" casting lemma cannot change a `NO-mathlib-has-it` once the identical decl is found in mathlib.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`preNormEDS_ofNat ..`).
One-liner verdict: n/a — kind is `lemma`, not a `def`. (The one-liner exemption analysis applies to definitions, not lemmas. Recorded for completeness; a one-line *lemma* with `@[simp]` bridging two forms of a sequence is entirely standard.)

---

### Literature search (Phase 3)

Short-circuited by Phase 5. The mathlib search located a byte-for-byte identical declaration `WeierstrassCurve.preΨ_ofNat` in the mathlib tree (see Phase 5). The skill's verdict gate for `NO-mathlib-has-it` requires only that Phase 5's conclusion be "found in mathlib as …"; a nine-channel literature sweep cannot overturn the existence of the identical decl in mathlib. The underlying mathematical content — division polynomials / elliptic divisibility sequences of Weierstrass curves — is the formalisation by D. K. Angdinata & J. Xu (the mathlib `EllipticCurve.DivisionPolynomial` and `NumberTheory.EllipticDivisibilitySequence` files, ultimately after Ward's elliptic divisibility sequences and the standard division-polynomial recurrences in Silverman, *The Arithmetic of Elliptic Curves*). This casting lemma itself is an implementation bridge, not a literature theorem.

Concept identified as: the ℤ→ℕ index agreement for the pre-normalised division-polynomial sequence `preΨ` of a Weierstrass curve.
Most general standard form: the generic `preNormEDS_ofNat` for an arbitrary elliptic divisibility sequence over a commutative ring (mathlib `NumberTheory/EllipticDivisibilitySequence.lean:180`); `preΨ_ofNat` is its curve-specialisation.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard / most-general form: the generic `preNormEDS_ofNat (b c d : R) (n : ℕ)` over any `CommRing R` — already in mathlib, and already what this lemma's proof invokes.

| # | Parameter / hypothesis        | Current Lean form         | Most general form                 | Weaker form exists? | Reason |
|---|-------------------------------|---------------------------|------------------------------------|---------------------|--------|
| 1 | `[CommRing R]`                | commutative ring          | commutative ring                   | NO                  | matches the generic `preNormEDS_ofNat`; coefficients `Ψ₂Sq²`, `Ψ₃`, `preΨ₄` are ring elements |
| 2 | `(W : WeierstrassCurve R)`    | a Weierstrass curve       | the three abstract coefficients `b,c,d` | (already exists)  | the maximally-general form `preNormEDS_ofNat` drops `W` and takes `b c d : R` directly — and it is already in mathlib |

### Generality verdict (Phase 4b)

The current form is: a curve-specialisation of the already-existing, strictly-more-general mathlib lemma `WeierstrassCurve.preNormEDS_ofNat` / `preNormEDS_ofNat`. It is the standard curve-level convenience wrapper and is itself already in mathlib verbatim. No weakening opportunity that mathlib does not already realise.

### Modern-idiom check (Phase 4c)

No modernisation move applies — this is a finite definitional bridge between two indexings of one sequence; there is no topology to filter-ise, no construction to replace with a universal property, no metric/vector-space typeclass to weaken. Row-by-row: all `no`. The curve-level statement is the idiomatic mathlib form (and is precisely what mathlib ships).

---

### Mathlib search (Phase 5)

```
### Mathlib search-status: WeierstrassCurve.preΨ_ofNat

[A] Lean-Finder       n/a (mathlib index not queried; direct source grep is conclusive)
[B] Loogle            n/a (direct source hit found)
[C] LeanSearch        n/a (direct source hit found)
[D] Grep mathlib src  grep "preΨ_ofNat\b" over .lake/packages/mathlib/Mathlib/  → HIT
[E] Name pattern      "preΨ_ofNat" / "preNormEDS_ofNat"                          → HIT (both)
```

**Found in mathlib as `WeierstrassCurve.preΨ_ofNat` — identical form.**

Exact match at
`/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:198-199`:

```lean
@[simp]
lemma preΨ_ofNat (n : ℕ) : W.preΨ n = W.preΨ' n :=
  preNormEDS_ofNat ..
```

inside `namespace WeierstrassCurve` (line 104) with `variable {R : Type r} [CommRing R] (W : WeierstrassCurve R)` (line 106). This is **byte-for-byte identical** to the project declaration: same name, same namespace, same `@[simp]` attribute, same statement, same one-term proof. The generic lemma it delegates to, `preNormEDS_ofNat`, is also already in mathlib at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:180`.

Concluded: **found in mathlib as `WeierstrassCurve.preΨ_ofNat`; identical form.**

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.preΨ_ofNat`

Internal use count (Lean, excluding the declaring file): the lemma is used as a `simp` rewrite at several sites in the project's *own forked copy* of the division-polynomial development:
- `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:283` (`Φ_ofNat` proof)
- `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:272, 279, 289, 302, 314` (degree/coeff lemmas)

External-to-file callers: 1 file (`DivisionPolynomialDegree.lean`).

| Caller file:line                         | Usage pattern |
|------------------------------------------|---------------|
| DivisionPolynomial.lean:283              | `simp_rw [ΨSq_ofNat, …, preΨ_ofNat]` |
| DivisionPolynomialDegree.lean:272        | `exact_mod_cast W.preΨ_ofNat n ▸ W.natDegree_preΨ'_le n` |
| DivisionPolynomialDegree.lean:279        | `exact_mod_cast W.preΨ_ofNat n ▸ W.coeff_preΨ' n` |
| DivisionPolynomialDegree.lean:289/302/314| `simpa only [preΨ_ofNat, …] using …` |

Crucially, these call sites are themselves copies of the corresponding mathlib call sites: the same usages appear in
`.lake/packages/mathlib/.../DivisionPolynomial/Basic.lean:360` and `.../Degree.lean:275, 282, 292, 305, 316`. The project consumers exist only because the project forked the whole file.

Inline-derivation grep: (none) — consumers use the lemma, but the lemma is redundant with mathlib's.

Composition: NOT-COMPOSABLE in the "≤3 mathlib primitives" sense and irrelevant here — the point is not to compose it but that mathlib already *has the identical lemma by the same name*. Conclusion: superseded by mathlib.

---

## Verdict: `WeierstrassCurve.preΨ_ofNat`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): short-circuited — Phase 5 found the identical mathlib decl.
- Generality analysis (Phase 4): the form is mathlib's exact curve-level form; the more general `preNormEDS_ofNat` is also already in mathlib.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.preΨ_ofNat`; **identical form** at `Basic.lean:198-199`.
- Composition check (Phase 6): superseded; project call sites are themselves copies of mathlib's.

**Rationale:**

This lemma is a verbatim copy of `WeierstrassCurve.preΨ_ofNat`, which already lives in mathlib at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:198-199` — same namespace, same `@[simp]` attribute, same statement `W.preΨ ↑n = W.preΨ' n`, same proof `preNormEDS_ofNat ..`. The project's own module docstring states plainly that `DivisionPolynomial.lean` "is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`," forked solely to import the project's local `LutzNagell.EllipticDivisibilitySequence` instead of mathlib's, so that the project's duplicated `normEDS`/`complEDS` track does not clash by name. There is nothing to upstream: mathlib has it, identically.

**WHY not (refactor-actionable):**

Mathlib already has the identical lemma. The reason the project carries a duplicate is the deliberate fork of the entire `DivisionPolynomial.Basic` module onto a private `EllipticDivisibilitySequence` (to dodge the `normEDS`/`complEDS` name collision with the project's own EDS development). The lemma's value is therefore zero beyond keeping the fork self-consistent — every one of its call sites mirrors an identical call site in the mathlib originals.

Existing mathlib decl: `WeierstrassCurve.preΨ_ofNat`
Located at: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:198`
Our form follows in ≤1 line — it is literally the same declaration:
```lean
example (W : WeierstrassCurve R) (n : ℕ) : W.preΨ ↑n = W.preΨ' n := W.preΨ_ofNat n
```
Call sites in our project (Lean): 1 in `DivisionPolynomial.lean` (same file), 5 in `DivisionPolynomialDegree.lean`.

Refactor plan: this is **not** a per-lemma refactor — it is a whole-file fork. The correct disposition is decided at the *file/track* level, not for this lemma alone:
1. If/when the project resolves the `normEDS`/`complEDS` name clash with mathlib (e.g. by renaming the project's local EDS track, or by deleting it in favour of mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`), the entire forked `LutzNagell/DivisionPolynomial.lean` copy — including `preΨ_ofNat` and its siblings `preΨ`, `preΨ_zero/one/two/three/four/neg/even/odd`, `ΨSq*`, `Ψ*`, `Φ*` — should be dropped and replaced by `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.
2. At that point the 6 Lean call sites resolve to the mathlib `WeierstrassCurve.preΨ_ofNat` automatically (identical name and namespace) — no per-site edit needed beyond removing the local copy.

This lemma should **not** be assessed or upstreamed in isolation: it is one line of a forked module, and its fate is tied to the fork. Verdict inheritance applies — its parent def `preΨ` is itself a mathlib copy (`NO-mathlib-has-it`), and this glue lemma inherits that verdict.

---

## Next step

Delete the forked `LutzNagell/DivisionPolynomial.lean` copy (this lemma included) once the project's `EllipticDivisibilitySequence` name collision with mathlib is resolved; the 6 Lean call sites then bind to mathlib's identical `WeierstrassCurve.preΨ_ofNat`. No standalone action for this lemma — it is fork-bound duplication of an existing mathlib declaration.
