# Mathlibable assessment: `WeierstrassCurve.Universal.pointedCurve_a₁`

**Verdict: NO-composable-from-mathlib**

**Rationale (≤20 words):** Specialization of mathlib's `@[simps] map_a₁` to bespoke `pointedCurve`/`polyToField`/`CC`; `rfl` from existing `map_a₁` + `coe_algebraMap_eq_CC`.

---

## 1. The declaration

Source: `projects/NagellLutz/LutzNagell/Universal.lean:160`

```lean
open Polynomial (CC)

@[simp] lemma pointedCurve_a₁ : pointedCurve.a₁ = polyToField (CC curve.a₁) := rfl
```

Sibling lemmas `pointedCurve_a₂ … pointedCurve_a₆` (lines 161–164) are identical in form, also `rfl`.

**True qualified name:** `WeierstrassCurve.Universal.pointedCurve_a₁`
(line 160 is inside `namespace WeierstrassCurve` at L69 → `namespace Universal` at L75, closing at L177). The prompt's parsed guess `WeierstrassCurve.Universal.pointedCurve_a₁` is **correct**.

### What the names mean (all bespoke to this file)
- `curve : Affine (MvPolynomial Coeff ℤ)` — the universal Weierstrass curve over `ℤ[A₁,A₂,A₃,A₄,A₆]`, with `curve.a₁ = MvPolynomial.X A₁` (L84).
- `Poly := (MvPolynomial Coeff ℤ)[X][Y]`, `Universal.Ring := curve.CoordinateRing`, `Universal.Field := FractionRing Universal.Ring` (L94–99).
- `polyToField : Poly →+* Universal.Field := (algebraMap Universal.Ring _).comp (AdjoinRoot.mk _)` (L108).
- `pointedCurve := baseChange curve Universal.Field` (L130).
- `CC` is mathlib's `Polynomial.CC`, the double-constant embedding `R → R[X][Y]`, `CC r := C (C r)`.

So the lemma asserts: the `a₁`-coefficient of the curve base-changed to the universal field equals the image of `curve.a₁ : MvPolynomial Coeff ℤ`, pushed first into `Poly` via `CC` and then to `Universal.Field` via `polyToField`.

---

## 2. Mathlib search (five methods)

**(a) The general principle is in mathlib.** `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`:

```lean
@[simps]                                          -- L230
def map : WeierstrassCurve A := ⟨f W.a₁, f W.a₂, f W.a₃, f W.a₄, f W.a₆⟩

def baseChange [Algebra R A] : WeierstrassCurve A := W.map (algebraMap R A)   -- L236
```

The `@[simps]` on `map` auto-generates the simp lemma
`WeierstrassCurve.map_a₁ : (W.map f).a₁ = f W.a₁`
(and `map_a₂ … map_a₆`). Since `baseChange W A = W.map (algebraMap R A)`, this gives, by `rfl`/simp,
`(W.baseChange A).a₁ = algebraMap R A W.a₁`.

Confirmed against the public docs (leanprover-community mathlib4_docs, Weierstrass page) — `map`, `map_a₁`, `baseChange` are all present; `@[simps]` "is used with definitions like `variable_change` to automatically generate simp lemmas corresponding to each of the five coefficients."

**(b) No `baseChange_a₁` in mathlib.** `baseChange` carries **no** `@[simps]` (grep over the EllipticCurve dir returns nothing), so mathlib has no literal `baseChange_a₁`. The `map_a₁ ∘ baseChange-def` route is the mathlib idiom for it.

**(c) The `CC = algebraMap` bridge is in mathlib.** `Mathlib/Algebra/Polynomial/Bivariate.lean`:
- `abbrev CC (r : R) : R[X][Y] := C (C r)` (L47)
- `coe_algebraMap_eq_CC : algebraMap R R[X][Y] = CC (R := R) := rfl` (L148)

So `CC` *is* the algebra map `R → R[X][Y]`, definitionally.

**(d) The remaining glue is the project's own lemma, not a mathlib gap.** This file already defines (L113):
```lean
lemma algebraMap_field_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Field = polyToField.comp (algebraMap _ _) := rfl
```
i.e. `algebraMap (MvPolynomial Coeff ℤ) Universal.Field x = polyToField (algebraMap _ Poly x) = polyToField (CC x)`. This is intrinsically about the bespoke `polyToField`/`Universal.Field` tower and cannot live in mathlib.

**(e) In-repo duplication note (not a mathlib fact, but flagged for cleanup):** the identical lemma exists at `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:163`. Both copies descend from Junyan Xu's universal-curve development. This is a *within-AINTLIB* dedup target, orthogonal to the mathlib question.

---

## 3. Generality analysis

There is **no more-general literature form** to aim for. The statement is a component-extraction identity for one specific curve (`curve`), one specific target ring (`Universal.Field`), and one specific factorization (`polyToField ∘ CC`) of its structure map. Every symbol but `CC` and `.a₁` is defined in this file. The genuinely general statement — "`(W.baseChange A).a₁ = algebraMap R A W.a₁`" — is **already** delivered by mathlib's `map_a₁` + the definition of `baseChange`. `pointedCurve_a₁` adds nothing general; it is a `@[simp]` *normal-form bridge* that rewrites the bespoke `pointedCurve.a₁` into the `polyToField (CC …)` shape the rest of the file's simp set expects (it feeds e.g. `DivisionPolynomial.lean` rewrites).

## 4. Composition check (≤ 3 mathlib calls)

`pointedCurve.a₁`
 = `(curve.baseChange Universal.Field).a₁`
 = `algebraMap (MvPolynomial Coeff ℤ) Universal.Field curve.a₁`  — **(1)** `map_a₁` + `baseChange` def (both mathlib)
 = `polyToField (CC curve.a₁)`  — **(2)** project `algebraMap_field_eq_comp` together with mathlib `coe_algebraMap_eq_CC`.

Two steps, and step (1) is pure mathlib. The only non-mathlib ingredient (step 2's `algebraMap_field_eq_comp`) is itself a local `rfl` about the bespoke tower. The whole lemma is `rfl` precisely because every arrow involved is the definitional constant/structure embedding. **Composable from mathlib + this file's own definitional plumbing in ≤ 3 calls.**

---

## 5. Five-bucket verdict

**NO-composable-from-mathlib.**

- Not `NO-mathlib-has-it`: mathlib has the *general* `map_a₁`, but cannot state `pointedCurve_a₁` itself — `pointedCurve`, `polyToField`, `curve`, `Universal.Field` are all defined in this file and do not exist in mathlib.
- Not `YES-add-as-is` / `YES-but-generalise-first`: the statement only typechecks relative to this project's `Universal.*` constructions; it is a `@[simp]` unfolding bridge with zero standalone mathematical content. Its general core (`map_a₁`) is already upstream.
- Not `BORDERLINE`: the analysis is unambiguous — it is a one-line `rfl` specialization that any user reproduces with `simp [map_a₁, baseChange, coe_algebraMap_eq_CC]` (or the file's `algebraMap_field_eq_comp`).

**Recommended action:** keep as a local `@[simp]` helper. The actionable item is the *in-repo* dedup with `HasseWeil/.../Universal.lean:163` (and the whole `pointedCurve_a₂…a₆` block), which belongs to a single shared `Common/` universal-curve module — a cleanup-lane ticket, not a mathlib PR.

---

### Evidence index
- Decl + bespoke defs: `projects/NagellLutz/LutzNagell/Universal.lean` (L84, L94–99, L108, L113, L130, L160).
- mathlib `map`/`baseChange`/`map_a₁`: `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230–237`.
- mathlib `CC` / `coe_algebraMap_eq_CC`: `.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Bivariate.lean:47, 148`.
- In-repo duplicate: `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:163`.
- Public docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.html ; https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Simps/Basic.html
