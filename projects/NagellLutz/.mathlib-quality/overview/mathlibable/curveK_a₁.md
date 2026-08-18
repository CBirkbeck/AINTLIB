# Mathlibable assessment: `LutzNagell.PID.curveK_a₁`

**Verdict: NO-mathlib-has-it**

## Declaration

- **Qualified name:** `LutzNagell.PID.curveK_a₁`
- **Location:** `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDCurve.lean:29`
- **Statement:**
  ```lean
  @[simp] lemma curveK_a₁ : (curveK R K W).a₁ = algebraMap R K W.a₁ := by simp [curveK]
  ```
  where (same file, lines 22–27):
  ```lean
  variable (R : Type*) [CommRing R]
  variable (K : Type*) [Field K] [Algebra R K]
  variable (W : WeierstrassCurve R)

  /-- The base change of `W` to the fraction field `K`. -/
  abbrev curveK : WeierstrassCurve K := W.map (algebraMap R K)
  ```

So unfolding the `curveK` abbreviation, the statement is literally:
`(W.map (algebraMap R K)).a₁ = algebraMap R K W.a₁`.

This is one of a family of five sibling lemmas (`curveK_a₁`…`curveK_a₆`, lines 29–33), all identical
in shape, restating the coefficient-projection of `W.map φ` for the project's local `curveK`
abbreviation.

## 1. Literature search

A "lemma" of the form *"the `a₁` coefficient of a base-changed Weierstrass curve is the image of
`a₁` under the ring map"* has no standing as a named mathematical result. It is the definitional
unfolding of base change: a Weierstrass model is a tuple `(a₁, a₂, a₃, a₄, a₆)` of ring elements,
and base change along `φ : R →+* A` is, *by definition*, the coefficient-wise pushforward
`(φ a₁, …, φ a₆)` (Silverman, *Arithmetic of Elliptic Curves*, III; this is the universal/functorial
Weierstrass model over commutative rings). WebSearch confirms this is exactly how the
construction is phrased — `W.map φ = {a₁ := φ a₁, …}` — with nothing further to prove.

## 2. Mathlib search — it is already there

Mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` defines, with `@[simps]`:

```lean
variable {A : Type v} [CommRing A] (f : R →+* A)

/-- The Weierstrass curve mapped over a ring homomorphism `f : R →+* A`. -/
@[simps]
def map : WeierstrassCurve A :=
  ⟨f W.a₁, f W.a₂, f W.a₃, f W.a₄, f W.a₆⟩
```
(`Weierstrass.lean:227–232`).

The `@[simps]` attribute on `map` **auto-generates the `@[simp]` lemma**
`WeierstrassCurve.map_a₁ : (W.map f).a₁ = f W.a₁`
(and `map_a₂`, `map_a₃`, `map_a₄`, `map_a₆`). These generated lemmas are used inside mathlib's own
proofs (`Weierstrass.lean:244, 249, 254, 259, …`) and across the AINTLIB HasseWeil project
(e.g. `projects/HasseWeil/HasseWeil/LocalExpansion.lean:542`,
`projects/HasseWeil/HasseWeil/RouteBGeneral.lean:363`).

The local `curveK_a₁` is precisely `WeierstrassCurve.map_a₁` instantiated at `f := algebraMap R K`:

```
LutzNagell.PID.curveK_a₁  ==  WeierstrassCurve.map_a₁ (f := algebraMap R K)   (after unfolding `curveK`)
```

In fact, because `curveK` is a reducible `abbrev` for `W.map (algebraMap R K)`, the mathlib
`@[simp]` lemma `map_a₁` already fires on `(curveK R K W).a₁` directly; the local lemma is redundant
even as a simp lemma (it exists only so the rewrite reads in terms of the `curveK` name and so
`simp [curveK_a₁]`-style call sites stay legible, e.g. `PIDMain.lean:277`).

## 3. Generality analysis

The local form is strictly *less* general than mathlib's: it fixes `A := K` a field with an
`Algebra R K` instance and `f := algebraMap R K`, whereas `WeierstrassCurve.map_a₁` holds for an
arbitrary ring map `f : R →+* A` into any `CommRing A`. There is no generalisation to perform — the
maximally general statement is already the mathlib lemma.

## 4. Composition check

Trivially yes — it is not even a composition, it is a single instantiation:
`WeierstrassCurve.map_a₁ W (algebraMap R K)` (1 mathlib lemma), or simply `by simp` (which closes it
via the generated `map_a₁` simp lemma). Well within the ≤3-call bound.

## 5. Verdict

**NO-mathlib-has-it.** The statement is `WeierstrassCurve.map_a₁` — an `@[simps]`-generated lemma on
`WeierstrassCurve.map` — specialised to `f := algebraMap R K` via the project's local `curveK`
abbreviation. Mathlib already provides it (more generally, for any ring map), uses it internally, and
the generated simp lemma already fires on `curveK` terms. The local copy is a convenience restatement
for the duplicated PID track, not new mathlib-worthy content. The same conclusion applies verbatim to
the siblings `curveK_a₂`/`curveK_a₃`/`curveK_a₄`/`curveK_a₆` (↔ `map_a₂`/`map_a₃`/`map_a₄`/`map_a₆`).

### Evidence pointers
- Local decl: `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDCurve.lean:27,29`
- Mathlib source (the thing it duplicates): `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230–232` (`@[simps] def map`)
- Mathlib internal uses of the generated `map_a₁`: same file, lines 244, 249, 254, 259
- Cross-project uses of `WeierstrassCurve.map_a₁`: `projects/HasseWeil/HasseWeil/LocalExpansion.lean:542`, `RouteBGeneral.lean:363`
