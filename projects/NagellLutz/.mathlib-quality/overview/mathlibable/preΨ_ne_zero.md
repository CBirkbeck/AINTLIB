# Mathlibable assessment: `WeierstrassCurve.preΨ_ne_zero`

**Verdict: NO-mathlib-has-it**

**Qualified name:** `WeierstrassCurve.preΨ_ne_zero`

---

## 1. Declaration under review (project source)

File: `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:312`
Namespace: `WeierstrassCurve` (opened at line 55), inside `section preΨ` (ends line 318).
Context variables: `{R : Type u} [CommRing R] (W : WeierstrassCurve R)`.

```lean
lemma preΨ_ne_zero [Nontrivial R] {n : ℤ} (h : (n : R) ≠ 0) : W.preΨ n ≠ 0 := by
  induction n using Int.negInduction with
  | nat n => simpa only [preΨ_ofNat] using W.preΨ'_ne_zero <| by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, neg_ne_zero]
        using ih n <| neg_ne_zero.mp <| by exact_mod_cast h
```

**Mathematical content.** For a Weierstrass curve `W` over a commutative ring `R`, the
(pre-)division polynomial `preΨ n` is nonzero whenever the integer `n` has nonzero image in `R`
(`R` nontrivial). Proof: reduce to the natural-number case via `Int.negInduction`; the `nat` case is
`preΨ'_ne_zero`, the `neg` case is the inductive hypothesis after `preΨ_neg`.

---

## 2. Mathlib search — exhaustive

The task flags that this project **forks** `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`.
That is exactly what happened, and the search is conclusive on the first method.

**Method 1 — grep the pinned mathlib source.** The pinned mathlib
(`lakefile.toml` rev `69aaaa313f44`, toolchain `v4.32.0-rc1`) at
`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:314`
contains:

```lean
lemma preΨ_ne_zero [Nontrivial R] {n : ℤ} (h : (n : R) ≠ 0) : W.preΨ n ≠ 0 := by
  induction n using Int.negInduction with
  | nat n => simpa only [preΨ_ofNat] using W.preΨ'_ne_zero <| by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, neg_ne_zero]
        using ih n <| neg_ne_zero.mp <| by exact_mod_cast h
```

This is **byte-identical** to the project declaration:
- same fully-qualified name `WeierstrassCurve.preΨ_ne_zero` (mathlib namespace `WeierstrassCurve`
  opened at line 59, `section preΨ` ends line 320 — same structure);
- same signature `[Nontrivial R] {n : ℤ} (h : (n : R) ≠ 0) : W.preΨ n ≠ 0`;
- same `{R : Type u} [CommRing R] (W : WeierstrassCurve R)` context;
- same proof term, verbatim (not even the `using` → `using!` skew seen on neighbouring lemmas).

**The whole file is a vendored fork.** Both files carry the identical header
`Copyright (c) 2024 David Kurniadi Angdinata … Authors: David Kurniadi Angdinata`, and the project's
own module docstring states it uses "`LutzNagell/DivisionPolynomial.lean` (a project copy of
mathlib's Basic file)". A line diff shows only cosmetic divergence (import lines, the `module` /
`public section` markers, and `using` vs `using!` plus a couple of tactic tweaks in *other* lemmas
such as `coeff_preΨ_ne_zero` / `natDegree_preΨ_pos`). `preΨ_ne_zero` itself is unchanged.

Methods 2–5 (loogle/leansearch/`exact?`/moogle, name-pattern, statement-shape) are unnecessary: the
exact declaration is physically present in the pinned mathlib, by the same author, in the file this
project copied.

---

## 3. Literature search

Not load-bearing for the verdict (the decl is already in mathlib by its original author), so kept
brief. The fact "a division polynomial `ψ_n` of an elliptic curve is a nonzero polynomial when the
characteristic does not divide `n`" is standard (Silverman, *The Arithmetic of Elliptic Curves*,
Exercise 3.7 / division-polynomial degree formulae; Washington, *Elliptic Curves: Number Theory and
Cryptography*, §3.2). Mathlib's `preΨ` is the "pre"-normalised division polynomial of
Angdinata's `DivisionPolynomial` development; `preΨ_ne_zero` is the natural nonvanishing companion to
the degree/leading-coefficient lemmas (`natDegree_preΨ`, `leadingCoeff_preΨ`) in the same file. No
more-general literature form is relevant — `Nontrivial R` + `(n : R) ≠ 0` is already the right
hypothesis (it is exactly "char R ∤ n" stated ring-theoretically).

---

## 4. Generality analysis

The mathlib statement is already at the natural generality:
- base ring is an arbitrary `CommRing R` with `Nontrivial R` (no domain/field assumption);
- the hypothesis `(n : R) ≠ 0` is the weakest sensible one (over `R` of characteristic `p`, `preΨ p`
  can genuinely vanish, so some hypothesis on `n` is required, and this is the minimal one).

There is nothing to weaken. The project copy and the mathlib original are identical, so there is no
"more general project form" to upstream either.

---

## 5. Composition check

Moot — the declaration is already a named lemma in mathlib, so no composition is needed. (For the
record, it is itself the ≤3-call composition `Int.negInduction` over `preΨ'_ne_zero` + `preΨ_neg`,
which is precisely why it lives in mathlib as a one-line bridge.)

---

## 6. Verdict

**NO-mathlib-has-it.**

`WeierstrassCurve.preΨ_ne_zero` exists **verbatim** in the pinned mathlib at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:314` — same name, same
signature, same proof, same author (David Kurniadi Angdinata, 2024). The project's
`DivisionPolynomialDegree.lean` is a vendored fork of that exact mathlib file. This is a pure
duplication, not a candidate for upstreaming.

**Action for the project:** this is a fork-tracking artifact. Once the NagellLutz development no
longer needs its private copy (e.g. after a mathlib bump that exposes the upstream file), drop the
local `preΨ_ne_zero` and `import`
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` instead. No PR to mathlib.
