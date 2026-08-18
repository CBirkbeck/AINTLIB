# Mathlibable assessment: `WeierstrassCurve.preΨ'_one`

**Verdict: NO-mathlib-has-it**

## Declaration under review

- **Qualified name:** `WeierstrassCurve.preΨ'_one`
- **Location:** `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:84`
- **Statement & proof (verbatim):**

  ```lean
  @[simp]
  lemma preΨ'_one : W.preΨ' 1 = 1 :=
    preNormEDS'_one ..
  ```

  Here `W : WeierstrassCurve R` (`[CommRing R]`), and
  `preΨ' n := preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n` is the univariate auxiliary
  ("pre-normalised") `n`-division polynomial of the Weierstrass curve `W`. The lemma records the
  initial value `preΨ'(1) = 1`.

## Mathematical content

`preΨ'` is the elliptic-divisibility-sequence / division-polynomial recursion specialised to a
Weierstrass curve. The base case `preΨ'(1) = 1` is true by definition: it unfolds to
`preNormEDS' b c d 1`, and `preNormEDS'` is defined by `| 1 => 1`. The whole lemma is one rewrite
(`preNormEDS'_one`), itself a single `rw [preNormEDS']`.

## Step 1 — Literature search

Not material to the verdict (see Step 2 — mathlib already contains this exact declaration), but for
completeness: division polynomials and their normalisations are standard (Silverman, *The
Arithmetic of Elliptic Curves*, Exercise 3.7; Washington, *Elliptic Curves: Number Theory and
Cryptography*, §3.2; M. Ward, *Memoir on Elliptic Divisibility Sequences*, the reference cited by
mathlib's own `EllipticDivisibilitySequence` file). The normalisation `ψ₁ = 1` is the universal
initial condition for these sequences. There is nothing novel here.

## Step 2 — Mathlib search (the decisive step)

This project **explicitly forks** two mathlib files. The header of
`DivisionPolynomial.lean` reads:

> "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that
> imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name
> conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

The identical declaration is present in the pinned mathlib:

- **`WeierstrassCurve.preΨ'_one`** —
  `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:161`:

  ```lean
  @[simp]
  lemma preΨ'_one : W.preΨ' 1 = 1 :=
    preNormEDS'_one ..
  ```

  Under `namespace WeierstrassCurve` (opened at line 104), so the fully-qualified name is
  `WeierstrassCurve.preΨ'_one` — **the same name, namespace, statement, and proof** as the local
  copy.

- The underlying lemma it delegates to, **`EllSequence`-free `preNormEDS'_one`**, is likewise in
  mathlib at
  `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:145`:

  ```lean
  @[simp]
  lemma preNormEDS'_one : preNormEDS' b c d 1 = 1 := by
    rw [preNormEDS']
  ```

So mathlib contains both the lemma itself and its only dependency. The local versions exist purely
because the project re-defines `preNormEDS'`/`normEDS`/`complEDS` in its own
`LutzNagell.EllipticDivisibilitySequence` (to experiment with an EDS API without clobbering
mathlib's `normEDS`), forcing a parallel copy of the `DivisionPolynomial` layer that points at the
local `preNormEDS'`. The fork is an engineering artefact of the NagellLutz development, not new
mathematics.

Search methods applied:
1. **Exact-name grep** across the pinned mathlib — direct hit on `preΨ'_one` (Basic.lean:161).
2. **Definitional grep** for `preΨ'` and `preNormEDS'` — both definitions present and identical.
3. **Namespace check** — both decls live in `WeierstrassCurve`, confirming name-for-name identity.
4. Loogle/leansearch (mathlib index) unnecessary: the source file is in-tree and matches verbatim.

## Step 3 — Generality analysis

N/A for the verdict: the mathlib declaration is already at exactly the generality of the local one
(`{R : Type*} [CommRing R]`, the maximal sensible generality for a polynomial identity over a
commutative ring). No weakening is possible or needed.

## Step 4 — Composition check

Trivially `≤ 3` mathlib calls: the lemma *is* a single mathlib lemma
(`WeierstrassCurve.preΨ'_one`), and even disregarding that, it is one rewrite by
`preNormEDS'_one`. But composition is moot because the full declaration already exists upstream.

## Step 5 — Verdict

**NO-mathlib-has-it.** `WeierstrassCurve.preΨ'_one` is a verbatim duplicate of the mathlib
declaration of the same fully-qualified name at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:161` (same statement, same
`preNormEDS'_one ..` proof), and its dependency `preNormEDS'_one` is also already in mathlib
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:145`). The local copy is a deliberate fork
to swap in the project's renamed EDS module, per this file's own header. It must **not** be added to
mathlib.

### Consolidation note (for the NagellLutz/AINTLIB cleanup track)
The whole `LutzNagell.DivisionPolynomial` + `LutzNagell.EllipticDivisibilitySequence` pair is a
General*/PID*-style fork of upstream. The right long-term move is to converge the local EDS API onto
mathlib's `normEDS`/`preNormEDS'` (resolving the `normEDS`/`complEDS` name clash that motivated the
fork) and then delete this duplicate, rather than to upstream anything from here.
