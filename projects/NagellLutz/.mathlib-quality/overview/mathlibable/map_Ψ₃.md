# Mathlibable assessment: `WeierstrassCurve.map_Ψ₃`

**Verdict: NO-mathlib-has-it**

**Declaration** (NagellLutz project)
`projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:428-430`

```lean
@[simp]
lemma map_Ψ₃ : (W.map f).Ψ₃ = W.Ψ₃.map f := by
  simp [Ψ₃]
```

Qualified name: `WeierstrassCurve.map_Ψ₃`
Context: `namespace WeierstrassCurve`,
`variable {R : Type r} {S : Type s} [CommRing R] [CommRing S] (W : WeierstrassCurve R)`,
`variable (f : R →+* S)`.

Statement in words: pushing a Weierstrass curve `W` over `R` forward along a ring
homomorphism `f : R →+* S` commutes with forming the 3-division polynomial `Ψ₃`; i.e. the
`Ψ₃` of the base-changed curve `W.map f` equals the coefficient-wise image `(W.Ψ₃).map f` of
the original `Ψ₃`. Here `Ψ₃ : R[X]` is `3 X⁴ + b₂ X³ + 3 b₄ X² + 3 b₆ X + b₈`.

---

## 1. Literature search

Division polynomials `ψ_n` of an elliptic curve, and the auxiliary univariate polynomials
`Ψ₃ = ψ₃`, are completely standard (Silverman, *The Arithmetic of Elliptic Curves*, Exercise
3.7; Washington, *Elliptic Curves: Number Theory and Cryptography*, §3.2). The specific
statement here — "the formation of the division polynomial is natural / functorial in the base
ring, commuting with pushforward of coefficients along a ring map" — is not a named theorem in
the literature; it is a routine naturality/compatibility lemma whose content is just that `Ψ₃`
is a fixed polynomial in the `bᵢ` invariants and those invariants transform by applying `f`. It
exists in formalised mathematics solely as plumbing for `map`/`baseChange` of division
polynomials. No `--exhaustive` nLab/Stacks/MathOverflow sweep is warranted: this is small,
mechanical naturality plumbing, not a mathematically notable result.

## 2. Mathlib search (five methods)

The project file is, by its own header (lines 12-17), a deliberate copy:

> "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that
> imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid
> name conflicts (both define `normEDS`, `complEDS`, etc.)."

Direct source inspection of the pinned mathlib
(`.lake/packages/mathlib`, `rev = 09b373db6e24`) confirms the lemma is present **verbatim**:

`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:505-507`
```lean
@[simp]
lemma map_Ψ₃ : (W.map f).Ψ₃ = W.Ψ₃.map f := by
  simp [Ψ₃]
```

Identical on every axis:
- **Name**: `WeierstrassCurve.map_Ψ₃` — same namespace `WeierstrassCurve` (mathlib `Basic.lean:104`).
- **Hypotheses / binders**: same `variable {R} {S} [CommRing R] [CommRing S] (W : WeierstrassCurve R)`
  (mathlib `Basic.lean:106`) and same `variable (f : R →+* S)` (mathlib `Basic.lean:495`).
- **Conclusion**: character-for-character identical: `(W.map f).Ψ₃ = W.Ψ₃.map f`.
- **Underlying def `Ψ₃`**: identical, `3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈`
  (mathlib `Basic.lean:142-143`, project `:65-66`).
- **Attribute**: both `@[simp]`. **Proof**: both `by simp [Ψ₃]`.
- **Author**: same (David Kurniadi Angdinata) in both file headers.

Method coverage: exact-name lookup hits (`map_Ψ₃`); statement/`simp`-normal-form search would
hit the same decl; the neighbours `map_ψ₂`, `map_Ψ₂Sq`, `map_preΨ₄`, `baseChange_Ψ₃` are also
all present in mathlib at `Basic.lean:498/502/510/559`. There is nothing left to find — it is
the same declaration.

## 3. Generality analysis

No generality gap: the binders are already maximally general for this statement — arbitrary
`CommRing R`, `CommRing S`, arbitrary ring hom `f`. The project copy and the mathlib original
have exactly the same generality. Nothing to weaken.

## 4. Composition check

Not applicable in the "could we instead compose mathlib primitives?" sense — mathlib does not
merely *imply* this, it *contains the identical declaration*. The proof is a one-line
`simp [Ψ₃]` in both places.

## 5. Verdict

**NO-mathlib-has-it.**

`WeierstrassCurve.map_Ψ₃` already exists in mathlib, verbatim, at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:506` — same name, same
namespace, same binders, same statement, same `@[simp]` attribute, same proof, same author. The
NagellLutz occurrence is an intentional fork of `DivisionPolynomial.Basic` (documented at the
top of the file) made only to dodge a `normEDS`/`complEDS` naming clash with the project's local
`EllipticDivisibilitySequence`; it carries no mathematical content not already upstream. There is
nothing to contribute. (If/when the project's EDS fork is reconciled with mathlib, this whole
copied block — `map_Ψ₃` included — should simply be deleted in favour of the mathlib import.)
