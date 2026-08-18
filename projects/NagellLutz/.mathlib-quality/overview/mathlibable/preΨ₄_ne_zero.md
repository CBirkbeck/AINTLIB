# Mathlibable assessment: `WeierstrassCurve.preΨ₄_ne_zero`

**Verdict: NO-mathlib-has-it** — already in mathlib, verbatim (identical statement *and* proof),
in the very file this project copied.

---

## 1. The declaration under assessment

Source: `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:144`

```lean
namespace WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

lemma preΨ₄_ne_zero (h : (2 : R) ≠ 0) : W.preΨ₄ ≠ 0 :=
  ne_zero_of_natDegree_gt <| W.natDegree_preΨ₄_pos h
```

**Parsed/verified qualified name: `WeierstrassCurve.preΨ₄_ne_zero`** (the prompt's guess was
correct — verified from the `namespace WeierstrassCurve` opened at line 55 and never closed before
line 144; the `section preΨ₄` at line 119 introduces no namespace).

**What it says.** For a Weierstrass curve `W` over a commutative ring `R`, if `2 ≠ 0` in `R`, then
the univariate "pre-ψ₄" division polynomial `preΨ₄ ∈ R[X]` is nonzero. The proof: `preΨ₄` has
positive `natDegree` (which holds because, when `2 ≠ 0`, `natDegree preΨ₄ = 6` via its degree-6
coefficient being `2 ≠ 0`), and a polynomial of positive `natDegree` is nonzero
(`ne_zero_of_natDegree_gt`). This is the bottom rung of the `preΨ₄` degree-API ladder in the file
(`natDegree_preΨ₄_le` → `coeff_preΨ₄` → `coeff_preΨ₄_ne_zero` → `natDegree_preΨ₄` →
`natDegree_preΨ₄_pos` → `leadingCoeff_preΨ₄` → `preΨ₄_ne_zero`).

This is **not** mathematically deep on its own; the content lives in the surrounding degree/leading-
coefficient computation. It is a convenience corollary, exactly mirroring its siblings
`Ψ₂Sq_ne_zero` (line 84) and `Ψ₃_ne_zero` (line 114) in the same file.

---

## 2. Project context — this is a forked mathlib file

The file's own module docstring (lines 12-14) says:

> This file computes the leading terms of certain polynomials associated to division polynomials of
> Weierstrass curves defined in `LutzNagell/DivisionPolynomial.lean` (**a project copy of mathlib's
> Basic file**).

`DivisionPolynomialDegree.lean` is itself a project copy of mathlib's
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`. The NagellLutz project
vendors this code so it can patch/extend the division-polynomial API locally (it adds a `preΨ'`
degree/leading-coefficient track lower in the file). The copied lemmas therefore **already exist in
mathlib under the same names and namespace**.

---

## 3. Mathlib search — it is there, verbatim

Five-method search (mathlib index is live; local Lean build is stale).

### (a) Vendored mathlib tree in this very repo
`/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:148`:

```lean
lemma preΨ₄_ne_zero (h : (2 : R) ≠ 0) : W.preΨ₄ ≠ 0 :=
  ne_zero_of_natDegree_gt <| W.natDegree_preΨ₄_pos h
```

Byte-for-byte identical statement **and** proof. The `section preΨ₄` block (mathlib lines 123-151)
is the same as the project's (lines 119-147), modulo a constant 4-line offset — the same offset
already noted in the sibling reports `coeff_preΨ₄_ne_zero.md` and `natDegree_preΨ₄.md`.

### (b) Official mathlib4 docs (current master)
`https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.html`
documents:

```lean
theorem WeierstrassCurve.preΨ₄_ne_zero {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (h : 2 ≠ 0) : W.preΨ₄ ≠ 0
```

— same namespace (`WeierstrassCurve`), same file
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`), same signature. So the
lemma is present on master *today*, not merely in the local pin.

### (c) Cross-repo corroboration inside AINTLIB
A sibling project already treats this as a mathlib lemma:
`projects/HasseWeil/HasseWeil/Verschiebung/QthRoots.lean:2527`:

```lean
/-- **preΨ_4 ≠ 0 in char 3** — direct from mathlib's `preΨ₄_ne_zero` + `2 ≠ 0`. -/
… := W.preΨ₄_ne_zero two_ne_zero_of_char_three
```

i.e. another AINTLIB project consumes `W.preΨ₄_ne_zero` straight from mathlib — independent evidence
that the canonical home is mathlib, not this project.

### (d) Author
Both the project file and the mathlib file carry the same header: *Copyright (c) 2024 David Kurniadi
Angdinata … Authors: David Kurniadi Angdinata* — the mathlib division-polynomial author. The project
copy is a verbatim lift of his upstream file.

### (e) Dependencies are all mathlib
`ne_zero_of_natDegree_gt` lives in mathlib
(`Mathlib/Algebra/Polynomial/Degree/Operations.lean:147`); `natDegree_preΨ₄_pos` is the immediately-
preceding sibling, itself already in mathlib's `Degree.lean`.

---

## 4. Literature

The construction is standard: division polynomials ψₙ of an elliptic curve (Silverman, *The
Arithmetic of Elliptic Curves*, Exercise 3.7; the file cites `silverman2009`). "ψ₄ is a nonzero
polynomial in characteristic ≠ 2" is a routine bookkeeping fact used in torsion/division-point
arguments (and in Nagell–Lutz). There is no named theorem to weigh against; the literature-standard
content is the degree/leading-term computation, all of which mathlib already has for `preΨₙ`, `ΨSqₙ`,
`Φₙ` in general `n` (`Degree.lean`, lemmas `preΨ_ne_zero`, `ΨSq_ne_zero`, `Φ_ne_zero`). The `n = 4`
unfolded instance assessed here is strictly weaker than mathlib's general `preΨ_ne_zero`.

---

## 5. Generality / composition

No generalisation work is warranted: mathlib already carries **both** this exact `n = 4` lemma
*and* its general-`n` parent `WeierstrassCurve.preΨ_ne_zero`. The hypothesis `(2 : R) ≠ 0` over a
`CommRing` is already the natural/expected form (matching mathlib verbatim). Even if it were absent,
it would be a ≤2-call composition (`ne_zero_of_natDegree_gt ∘ natDegree_preΨ₄_pos`) — but that
question is moot because mathlib has the named lemma.

---

## 6. Verdict

**NO-mathlib-has-it.**

`WeierstrassCurve.preΨ₄_ne_zero` is already in mathlib — identical name, namespace, statement, and
proof — in `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`, confirmed in
the repo's vendored mathlib pin (line 148), on current mathlib master via the official docs, by the
shared upstream author header, and by another AINTLIB project (HasseWeil) already importing it from
mathlib. The project copy exists only because NagellLutz vendors mathlib's `Degree.lean` to extend
it locally. Nothing to upstream.

**Action:** none. When NagellLutz drops its fork of the division-polynomial files (or rebases onto
mathlib's), this lemma should resolve to `Mathlib…DivisionPolynomial.Degree.preΨ₄_ne_zero` directly;
no PR to mathlib is needed.

---

### Sources
- Project source: `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:144`
- Vendored mathlib: `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:148`
- Mathlib docs (master): https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.html
- Cross-repo consumer: `projects/HasseWeil/HasseWeil/Verschiebung/QthRoots.lean:2527`
- Dependency: `.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Degree/Operations.lean:147` (`ne_zero_of_natDegree_gt`)
