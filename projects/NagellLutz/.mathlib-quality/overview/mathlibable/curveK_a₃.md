# Mathlibable assessment: `LutzNagell.PID.curveK_a₃`

**Verdict: NO-mathlib-has-it**

## Declaration

- **Qualified name:** `LutzNagell.PID.curveK_a₃`
- **Location:** `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDCurve.lean:31`
- **Statement:**
  ```lean
  @[simp] lemma curveK_a₃ : (curveK R K W).a₃ = algebraMap R K W.a₃ := by simp [curveK]
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
`(W.map (algebraMap R K)).a₃ = algebraMap R K W.a₃`.

This is one of a family of five sibling lemmas (`curveK_a₁`…`curveK_a₆`, lines 29–33), all identical
in shape, restating the coefficient-projection of `W.map φ` for the project's local `curveK`
abbreviation. (The sibling report `curveK_a₁.md` reaches the identical conclusion and already names
`curveK_a₃ ↔ map_a₃`; this report is its `a₃` instance.)

## 1. Literature search

A "lemma" of the form *"the `a₃` coefficient of a base-changed Weierstrass curve is the image of
`a₃` under the ring map"* has no standing as a named mathematical result. It is the definitional
unfolding of base change: a Weierstrass model is a tuple `(a₁, a₂, a₃, a₄, a₆)` of ring elements,
and base change along `φ : R →+* A` is, *by definition*, the coefficient-wise pushforward
`(φ a₁, …, φ a₆)` (Silverman, *Arithmetic of Elliptic Curves*, Ch. III — the universal/functorial
Weierstrass model over commutative rings; base change of `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`
sends each `aᵢ ↦ φ(aᵢ)`). There is nothing further to prove: the equality holds by `rfl` after the
projection unfolds.

## 2. Mathlib search — it is already there

Mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` defines, with `@[simps]`:

```lean
variable {A : Type v} [CommRing A] (f : R →+* A)

/-- The Weierstrass curve mapped over a ring homomorphism `f : R →+* A`. -/
@[simps]
def map : WeierstrassCurve A :=
  ⟨f W.a₁, f W.a₂, f W.a₃, f W.a₄, f W.a₆⟩
```
(AINTLIB-pinned mathlib, `Weierstrass.lean:230–232`, verified locally.)

The `@[simps]` attribute on `map` **auto-generates the `@[simp]` lemma**
`WeierstrassCurve.map_a₃ : (W.map f).a₃ = f W.a₃`
(alongside `map_a₁`, `map_a₂`, `map_a₄`, `map_a₆`). These generated lemmas are used inside mathlib's
own proofs of the `b`-invariant push-forwards — `map_a₃` appears at `Weierstrass.lean:249, 254, 259`
(`simp only [b₄, map_a₁, map_a₃, map_a₄]`, etc.).

The local `curveK_a₃` is precisely `WeierstrassCurve.map_a₃` instantiated at `f := algebraMap R K`:

```
LutzNagell.PID.curveK_a₃  ==  WeierstrassCurve.map_a₃ (f := algebraMap R K)   (after unfolding `curveK`)
```

Because `curveK` is a reducible `abbrev` for `W.map (algebraMap R K)`, the mathlib `@[simp]` lemma
`map_a₃` already fires on `(curveK R K W).a₃` directly; the local lemma is redundant even as a simp
lemma — it exists only so the rewrite reads in terms of the `curveK` name and so `simp`/`rw`
call-sites within the PID track stay legible.

Search methods used:
1. **Read the mathlib source** (`Weierstrass.lean`, the `map` definition) — the canonical home of
   Weierstrass base change. Confirmed `@[simps]` ⇒ generated `map_a₃`.
2. **Definitional/`@[simps]` knowledge** — `@[simps]` on a structure constructor named after fields
   `a₁…a₆` generates exactly `map_a₁ … map_a₆`; mathlib's internal uses (lines 249/254/259) confirm
   the names exist and fire.
3. **Cross-repo grep** — `WeierstrassCurve.map_a₃` / the generated projection simp set is used across
   AINTLIB (e.g. HasseWeil), confirming it is the live, reused form.
4. **Name/shape search** — the statement is a single structure-projection equality; no more-general
   named lemma exists or is needed beyond `map_a₃` itself.
5. **Concept search** — "base change / map of Weierstrass curve coefficient" lands on
   `WeierstrassCurve.map` and its `@[simps]` projections, nothing else.

## 3. Generality analysis

The local form is strictly *less* general than mathlib's: it fixes `A := K` a field with an
`Algebra R K` instance and `f := algebraMap R K`, whereas `WeierstrassCurve.map_a₃` holds for an
arbitrary ring map `f : R →+* A` into any `CommRing A`. There is no generalisation to perform — the
maximally general statement is already the mathlib lemma. (Re-adding it "generalised" would just
reproduce `map_a₃`.)

## 4. Composition check

Trivially yes — it is not even a composition, it is a single instantiation:
`WeierstrassCurve.map_a₃ W (algebraMap R K)` (1 mathlib lemma), or simply `by simp` (which closes it
via the generated `map_a₃` simp lemma). Well within the ≤3-call bound.

## 5. Verdict

**NO-mathlib-has-it.** The statement is `WeierstrassCurve.map_a₃` — an `@[simps]`-generated lemma on
`WeierstrassCurve.map` — specialised to `f := algebraMap R K` via the project's local `curveK`
abbreviation. Mathlib already provides it (more generally, for any ring map), uses it internally
(`Weierstrass.lean:249/254/259`), and the generated simp lemma already fires on `curveK` terms. The
local copy is a convenience restatement for the duplicated PID track, not new mathlib-worthy content.
The same conclusion applies verbatim to the siblings
`curveK_a₁`/`curveK_a₂`/`curveK_a₄`/`curveK_a₆` (↔ `map_a₁`/`map_a₂`/`map_a₄`/`map_a₆`).

### Evidence pointers
- Local decl: `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDCurve.lean:27,31`
- Mathlib source (the thing it duplicates): `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230–232` (`@[simps] def map`)
- Mathlib internal uses of the generated `map_a₃`: same file, lines 249, 254, 259
- Sibling assessment with the same verdict: `projects/NagellLutz/.mathlib-quality/overview/mathlibable/curveK_a₁.md`
