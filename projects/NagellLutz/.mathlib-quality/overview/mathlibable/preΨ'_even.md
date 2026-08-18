# Mathlibable assessment: `WeierstrassCurve.preΨ'_even`

**Verdict: NO-mathlib-has-it**

## Declaration under review

- **Qualified name:** `WeierstrassCurve.preΨ'_even`
- **Project location:** `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:99`
- **Statement & proof (project copy):**
  ```lean
  namespace WeierstrassCurve
  variable {R : Type r} [CommRing R] (W : WeierstrassCurve R)
  ...
  lemma preΨ'_even (m : ℕ) : W.preΨ' (2 * (m + 3)) =
      W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 3) * W.preΨ' (m + 5) -
        W.preΨ' (m + 1) * W.preΨ' (m + 3) * W.preΨ' (m + 4) ^ 2 :=
    preNormEDS'_even ..
  ```
  where `W.preΨ' n := preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n` (line 76).

Mathematically: the even-index recurrence for the auxiliary univariate division-polynomial
sequence `preΨ'`. At an even argument `2(m+3)`, the term is expressed through five nearby terms
`preΨ'(m+1..m+5)`. It is the elliptic-divisibility-sequence "duplication / even" relation
specialised from the abstract `preNormEDS'` recurrence (parameters `b = Ψ₂Sq²`, `c = Ψ₃`,
`d = preΨ₄`) to the division-polynomial sequence of a Weierstrass curve `W`. It is an immediate
corollary of the EDS fact `preNormEDS'_even`, which itself just unfolds the defining recurrence of
`preNormEDS'` at the odd predecessor branch (`2(m+3) = (2m+1) + 5`).

## Literature note

No literature sweep is warranted (small, definitional wrapper of an existing mathlib lemma — not
`--exhaustive`). For the record, this even-index identity is the standard recurrence of elliptic
divisibility sequences / division polynomials (Ward, *Memoir on elliptic divisibility sequences*,
Amer. J. Math. 1948; Stange, *Elliptic nets*; Silverman, *Arithmetic of Elliptic Curves*, exercises
on division polynomials). There is no mathematical novelty to locate — only a verbatim copy to
identify.

## Mathlib search (five methods)

The NagellLutz project is, by its own file docstring (lines 12-14), **a verbatim copy of**
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`, re-imported only against the
project's local `LutzNagell.EllipticDivisibilitySequence` to avoid `normEDS`/`complEDS` name
clashes. So the first place to look is that mathlib file, which is vendored in-repo.

1. **Exact-name / source read.** `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
   (in `.lake/packages/mathlib`, pin `09b373db6e24`, dated 2026-06-21) contains, in the **same**
   `namespace WeierstrassCurve` with the **same** `variable (W : WeierstrassCurve R)`:
   ```lean
   lemma preΨ'_even (m : ℕ) : W.preΨ' (2 * (m + 3)) =        -- Basic.lean:176
       W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 3) * W.preΨ' (m + 5) -
         W.preΨ' (m + 1) * W.preΨ' (m + 3) * W.preΨ' (m + 4) ^ 2 :=
     preNormEDS'_even ..
   ```
   This is **byte-for-byte identical** to the project copy (project lines 99-102): identical
   statement, identical proof term `preNormEDS'_even ..`. The supporting `def preΨ'`
   (Basic.lean:153), `def Ψ₃` (:135), `def preΨ₄` (:~145), and `def Ψ₂Sq` are likewise identical to
   the project's.
2. **Underlying lemma.** The proof delegates to
   `preNormEDS'_even (m) : preNormEDS' b c d (2 * (m + 3)) = preNormEDS' b c d (m+2)^2 * … `,
   which is also already in mathlib at
   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:160` (proved by rewriting the recurrence
   `preNormEDS'` at the `dif_neg` / odd-predecessor branch plus `Nat.mul_add_div`). The project's
   local `EllipticDivisibilitySequence.lean` is itself a copy of that mathlib file.
3. **leansearch / loogle / moogle / Process.run grep / docstring search** are unnecessary and would
   only re-surface the same mathlib declaration: the identifier `WeierstrassCurve.preΨ'_even`
   resolves to the mathlib file directly. The in-repo mathlib source is dispositive.

So mathlib **already contains this exact declaration**, under the **same fully-qualified name**.

## Provenance (origin check, not a generality question)

Both the mathlib file and the project copy carry the identical header
`Copyright (c) 2024 David Kurniadi Angdinata ... Authors: David Kurniadi Angdinata`. Angdinata is
the mathlib author of the elliptic-curve division-polynomial and EDS files. Hence mathlib is
unambiguously the **origin**, and NagellLutz is the **downstream fork** — this is not project-novel
content that mathlib happened to acquire elsewhere. This matches the project's own ledger, which
already classifies the sibling declarations `preΨ'`, `preΨ'_zero`, and `preΨ'_three` as
`NO-mathlib-has-it`.

## Generality analysis

Not applicable in the "weaken assumptions" sense, because the mathlib form **is** this exact
statement at this exact generality (arbitrary `CommRing R`, arbitrary `WeierstrassCurve R`, all
`m : ℕ`). There is no more-general mathlib form to prefer and nothing to generalise: the project
copy and the mathlib original are the same lemma. (The truly general statement — the even-index
recurrence for the abstract `preNormEDS'` over any `CommRing` — is exactly `preNormEDS'_even`, which
this lemma already invokes and which is itself already in mathlib.)

## Composition check

Even setting aside the verbatim duplication, the lemma is a one-line corollary obtainable from a
single mathlib call: `preNormEDS'_even` (unfolding of the EDS recurrence at an even argument)
applied through the definitional equality `W.preΨ' = preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄`. That
is `1` mathlib primitive (`≤ 3`), so it is trivially composable — but moot, since the assembled
lemma is itself already in mathlib.

## Conclusion

`WeierstrassCurve.preΨ'_even` exists in mathlib verbatim (same name, statement, and proof) at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:176`, on top of
`preNormEDS'_even` at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:160`. The NagellLutz
copy is a deliberate fork made only to swap the EDS import. It is not a candidate to add to mathlib.

**Bucket: NO-mathlib-has-it.** When NagellLutz is integrated into AINTLIB/mathlib, this copy (and
the whole forked `DivisionPolynomial.lean` / `EllipticDivisibilitySequence.lean` track) should be
deleted in favour of the upstream mathlib declarations, by resolving the `normEDS`/`complEDS` naming
clash that motivated the fork rather than by re-defining the API.
