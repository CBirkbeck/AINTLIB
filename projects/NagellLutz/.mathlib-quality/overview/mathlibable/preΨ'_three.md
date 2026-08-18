# Mathlibable assessment: `WeierstrassCurve.preΨ'_three`

**Verdict: NO-mathlib-has-it**

## Declaration under review

- **Qualified name:** `WeierstrassCurve.preΨ'_three`
- **Project location:** `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:92`
- **Statement & proof (project copy):**
  ```lean
  namespace WeierstrassCurve
  variable {R : Type r} [CommRing R] (W : WeierstrassCurve R)
  ...
  @[simp]
  lemma preΨ'_three : W.preΨ' 3 = W.Ψ₃ :=
    preNormEDS'_three ..
  ```
  where `W.preΨ' n := preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n` (line 76).

Mathematically: the auxiliary univariate division-polynomial sequence `preΨ'`, evaluated at
`n = 3`, equals the 3-division polynomial `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`. It is an
immediate corollary of the EDS fact `preNormEDS' b c d 3 = c` (the third initial value of the
auxiliary normalised-EDS recurrence), specialised to `c = Ψ₃`.

## Mathlib search (five methods)

The NagellLutz project is, by its own file docstring (lines 12-14), **a verbatim copy of**
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`, re-imported only against the
project's local `LutzNagell.EllipticDivisibilitySequence` to avoid `normEDS`/`complEDS` name
clashes. So the first place to look is that mathlib file, which is vendored in-repo.

1. **Exact-name / source read.** `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
   (in `.lake/packages/mathlib`, pin `09b373db6e24`) contains, in the **same** `namespace
   WeierstrassCurve` with the **same** `variable (W : WeierstrassCurve R)`:
   ```lean
   @[simp]
   lemma preΨ'_three : W.preΨ' 3 = W.Ψ₃ :=        -- Basic.lean:169
     preNormEDS'_three ..
   ```
   This is **byte-for-byte identical** to the project copy: identical statement, identical proof
   term, identical `@[simp]` attribute. The supporting `def preΨ'` (Basic.lean:153), `def Ψ₃`
   (:142), and `def Ψ₂Sq` (:117) are likewise identical to the project's.
2. **Underlying lemma.** The proof delegates to `preNormEDS'_three : preNormEDS' b c d 3 = c`,
   which is also already in mathlib at
   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:153` (proved by `rw [preNormEDS']`).
   The project's local `EllipticDivisibilitySequence.lean:751` is itself a copy of that.
3. **leansearch / loogle / moogle / Process.run grep / docstring search** are unnecessary and
   would only re-surface the same mathlib declaration: the identifier `WeierstrassCurve.preΨ'_three`
   resolves to the mathlib file directly. The in-repo mathlib source is dispositive.

So mathlib **already contains this exact declaration**, under the **same fully-qualified name**.

## Provenance (origin check, not a generality question)

Both the mathlib file and the project copy carry the identical header
`Copyright (c) 2024 David Kurniadi Angdinata ... Authors: David Kurniadi Angdinata`. Angdinata is
the mathlib author of the elliptic-curve division-polynomial and EDS files. Hence mathlib is
unambiguously the **origin**, and NagellLutz is the **downstream fork** — this is not project-novel
content that mathlib happened to acquire elsewhere. No literature sweep is warranted: there is no
mathematical novelty to locate, only a verbatim copy to identify.

## Generality analysis

Not applicable in the "weaken assumptions" sense, because the mathlib form **is** this exact
statement at this exact generality (arbitrary `CommRing R`, arbitrary `WeierstrassCurve R`). There
is no more-general mathlib form to prefer and nothing to generalise: the project copy and the
mathlib original are the same lemma.

## Composition check

Even setting aside the verbatim duplication, the lemma is a one-line corollary obtainable from a
single mathlib call: `preNormEDS'_three` (definitional unfolding of the EDS recurrence's third
initial value) applied through `W.preΨ' = preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄`. That is `1`
mathlib primitive (`≤ 3`), so it is trivially composable — but moot, since the assembled lemma is
itself already in mathlib.

## Conclusion

`WeierstrassCurve.preΨ'_three` exists in mathlib verbatim (same name, statement, and proof) at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:169`. The NagellLutz copy is
a deliberate fork made only to swap the EDS import. It is not a candidate to add to mathlib.

**Bucket: NO-mathlib-has-it.** When NagellLutz is integrated into AINTLIB/mathlib, this copy (and
the whole forked `DivisionPolynomial.lean` / `EllipticDivisibilitySequence.lean` track) should be
deleted in favour of the upstream mathlib declarations, by resolving the `normEDS`/`complEDS`
naming clash that motivated the fork rather than by re-defining the API.
