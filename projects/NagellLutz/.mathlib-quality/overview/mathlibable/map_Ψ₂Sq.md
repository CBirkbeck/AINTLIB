# Mathlibable assessment — `WeierstrassCurve.map_Ψ₂Sq`

**Verdict: NO-mathlib-has-it** (exact verbatim duplicate of an existing mathlib lemma)

---

## 1. Declaration under review

- **Qualified name:** `WeierstrassCurve.map_Ψ₂Sq`
  (base name `map_Ψ₂Sq`, inside `namespace WeierstrassCurve`; verified — no intervening namespace).
- **Location:** `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:425`
- **Project:** NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS).

### Source statement (project copy, lines 420–426)

```lean
variable (f : R →+* S)

@[simp]
lemma map_ψ₂ : (W.map f).ψ₂ = W.ψ₂.map (mapRingHom f) := by
  simp_rw [ψ₂, Affine.map_polynomialY]

@[simp]
lemma map_Ψ₂Sq : (W.map f).Ψ₂Sq = W.Ψ₂Sq.map f := by
  simp [Ψ₂Sq, map_ofNat]
```

Context: `W : WeierstrassCurve R`, `[CommRing R] [CommRing S]`, `f : R →+* S`.

### Mathematical content

A naturality / `map`-compatibility `@[simp]` lemma: forming the Weierstrass curve `W.map f`
(coefficients pushed across the ring hom `f`) and then taking its univariate `2`-division-square
polynomial `Ψ₂Sq` equals applying `Polynomial.map f` to `W.Ψ₂Sq`. Here
`Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆ ∈ R[X]`, the polynomial congruent to `ψ₂²`. The lemma simply says the
`bᵢ` are natural in `f` (they are, being ring-polynomial expressions in the `aᵢ`), so the formula
commutes with `Polynomial.map`.

---

## 2. Mathlib search (five-method)

The project file's own header is decisive:

> "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that
> imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name
> conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

**Method 1 — direct name search in mathlib source (pinned rev `09b373db6e24`, v4.32.0-rc1).**
`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
contains, at **lines 501–503**:

```lean
@[simp]
lemma map_Ψ₂Sq : (W.map f).Ψ₂Sq = W.Ψ₂Sq.map f := by
  simp [Ψ₂Sq, map_ofNat]
```

inside `namespace WeierstrassCurve` (opened line 104, closed line 588) — fully-qualified name
`WeierstrassCurve.map_Ψ₂Sq`. The surrounding context matches the project byte-for-byte:
`section Map`, `open WeierstrassCurve (Ψ Φ ψ φ)`, `variable (f : R →+* S)`, same neighbouring lemmas
`map_ψ₂` (line 498) and `map_Ψ₃` (line 506), same downstream consumer `baseChange_Ψ₂Sq` (line 556,
proof `rw [← map_Ψ₂Sq, map_baseChange]`).

This is a **verbatim** match: identical name, identical statement, identical proof, identical
namespace, identical `@[simp]` attribute. The underlying object `Ψ₂Sq` is also defined identically in
both files (mathlib `Basic.lean:117` vs project `DivisionPolynomial.lean:40`:
`C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆`), so this is the *same statement about the
same objects*, not merely a name collision.

Methods 2–5 (leansearch / loogle / moogle / informal) are unnecessary once an exact source-level
match is found, and would only re-surface the same `WeierstrassCurve.map_Ψ₂Sq`.

---

## 3. Generality analysis

Not applicable in the usual sense — mathlib's lemma **is** this lemma, at exactly the same generality
(`[CommRing R] [CommRing S]`, arbitrary `f : R →+* S`). There is no weaker hypothesis set or more
general target to chase: `CommRing → CommRing` ring homs are already the natural maximal generality
for `WeierstrassCurve.map`, and the conclusion is the universal naturality square. Nothing to
generalise.

---

## 4. Composition check

Moot — the result is not "composable from mathlib primitives", it **is** a named mathlib lemma. (For
completeness, its own one-line `simp [Ψ₂Sq, map_ofNat]` proof shows it is a trivial unfolding, but the
point is that mathlib already ships exactly this `@[simp]` lemma under exactly this name.)

---

## 5. Literature

No external literature search is warranted. This is a low-level Lean infrastructure lemma
(`map`-naturality of a coefficient polynomial), not a named mathematical theorem; and in any case the
exact decl already exists upstream. The mathematics (division polynomials of Weierstrass curves,
elliptic divisibility sequences à la Ward) is fully covered by the existing mathlib file this is
copied from.

---

## 6. Verdict

**NO-mathlib-has-it.**

`WeierstrassCurve.map_Ψ₂Sq` is a byte-for-byte copy of the existing
`WeierstrassCurve.map_Ψ₂Sq` in
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` (lines 501–503). The duplication is
intentional and structural: the NagellLutz project forks the whole `DivisionPolynomial.Basic` file
solely to swap its `import` to the project-local `EllipticDivisibilitySequence` (avoiding a
`normEDS`/`complEDS` name clash), per the file's own header. This lemma carries **no new
mathematical content** over mathlib.

**Action:** do not submit. This belongs to the "forked-from-mathlib, already upstream" bucket — the
right long-term fix is to drop the fork (or upstream the `EllipticDivisibilitySequence` divergence)
rather than to PR this lemma. No generalisation, no composition repackaging applies.

**Evidence:** exact source match at
`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:501-503`
(mathlib rev `09b373db6e24`), same `WeierstrassCurve` namespace, same statement/proof/attribute, same
`Ψ₂Sq` definition; corroborated by the project file header at `DivisionPolynomial.lean:12-16`.
