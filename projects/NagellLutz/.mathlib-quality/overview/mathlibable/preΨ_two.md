# Mathlibable assessment — `WeierstrassCurve.preΨ_two`

**Verdict: NO — mathlib already has it (verbatim).**

| field | value |
|---|---|
| Qualified name | `WeierstrassCurve.preΨ_two` |
| Source | `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:133` |
| Bucket | `NO-mathlib-has-it` |

## Statement (from source)

```lean
@[simp]
lemma preΨ_two : W.preΨ 2 = 1 :=
  preNormEDS_two ..
```

with context `namespace WeierstrassCurve`, `variable {R : Type r} [CommRing R] (W : WeierstrassCurve R)`,
and `preΨ (n : ℤ) : R[X] := preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n`.

So the true qualified name is **`WeierstrassCurve.preΨ_two`** (the prompt's parsed guess is correct).

The lemma says: the integer-indexed auxiliary division polynomial `preΨₙ` of a Weierstrass curve `W`,
evaluated at `n = 2`, equals the constant polynomial `1`. It is a `@[simp]` boundary-value lemma for
the `preΨ` recurrence, proved by reducing to the underlying elliptic-divisibility-sequence fact
`preNormEDS_two : preNormEDS b c d 2 = 1`.

## Search result — mathlib has it, identically

This file is, by its own header (lines 12–14), *"a copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports
`LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts
(both define `normEDS`, `complEDS`, etc.)."* The fork exists purely to redirect the EDS import; the
mathematical content is unchanged.

The mathlib original is present in the pinned mathlib (`rev = 09b373db6e24`) at:

- **`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:210–211`**

```lean
@[simp]
lemma preΨ_two : W.preΨ 2 = 1 :=
  preNormEDS_two ..
```

Same namespace (`WeierstrassCurve`), same variables, **byte-identical statement and proof**. Its
dependency `preNormEDS_two` is likewise already in mathlib at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:194` — the project re-derives it in its own
forked `EllipticDivisibilitySequence.lean:792` only to dodge the `normEDS`/`complEDS` name clash.

Mathlib's five search methods are not needed to settle the bucket here: a direct read of the file
this project explicitly declares itself a copy of locates the identical declaration. (For the record:
exact-name `WeierstrassCurve.preΨ_two`, namespace + symbol grep, and source inspection all land on
the same mathlib line. `loogle`/`leansearch` would confirm but cannot override a verbatim source
match.)

## Generality analysis

No generalisation gap. The mathlib version already carries the maximal natural generality:
`R` is an arbitrary `CommRing` and `W : WeierstrassCurve R` is arbitrary. The boundary value
`preΨ 2 = 1` is a definitional normalisation of the EDS, true over any commutative ring; there is no
weaker hypothesis to drop and no stronger ring/field assumption in play. The project's copy is not
more general — it is the same statement under the same `[CommRing R]`.

## Composition check

Trivially "composable" (it is a one-liner `preNormEDS_two ..`), but this is irrelevant to the verdict:
the *named lemma itself* already exists in mathlib, so there is nothing to add. Even setting the
verbatim match aside, the whole `preΨ`-at-small-`n` family (`preΨ_zero/one/two/three/four/neg`,
`preΨ_even/odd`) is the standard mathlib API for these division polynomials and ships together —
re-adding one member would be pure duplication.

## Conclusion

`WeierstrassCurve.preΨ_two` is a verbatim fork of an existing mathlib lemma. It belongs in the
project only as part of the deliberate import-redirect fork (so it can sit atop the project's own
`EllipticDivisibilitySequence`); it must **not** be PR'd to mathlib. If/when the project's forked
EDS is reconciled with mathlib's (resolving the `normEDS`/`complEDS` clash), this entire
`DivisionPolynomial.lean` copy — including `preΨ_two` — should be deleted in favour of the upstream
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.

**Bucket: `NO-mathlib-has-it`.**
