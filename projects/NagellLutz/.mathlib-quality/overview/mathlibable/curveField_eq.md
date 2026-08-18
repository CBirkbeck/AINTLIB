# Mathlibable assessment — `WeierstrassCurve.Universal.curveField_eq`

**Verdict: NO-composable-from-mathlib**

> Trivial `rfl` between two project-local abbreviations (`curveField`, `pointedCurve`) for the
> same `WeierstrassCurve.baseChange` term. No reusable content; mathlib cannot even state it.

---

## 1. The declaration

File: `projects/NagellLutz/LutzNagell/Universal.lean:175`
Qualified name (verified from namespace stack `WeierstrassCurve` → `Universal`):
**`WeierstrassCurve.Universal.curveField_eq`**

```lean
lemma curveField_eq : curveField = pointedCurve := rfl
```

The two sides are project-local abbreviations:

```lean
-- line 130
abbrev pointedCurve : WeierstrassCurve Universal.Field := baseChange curve Universal.Field

-- line 173
abbrev curveField : WeierstrassCurve Universal.Field := curve.baseChange Universal.Field
```

i.e. `pointedCurve = baseChange curve Universal.Field` and
`curveField = curve.baseChange Universal.Field`. These are **the same term written two ways**
— explicit application vs. dot-notation of the *same* function `WeierstrassCurve.baseChange`
(mathlib), applied to the *same* arguments (`Universal.curve`, `Universal.Field`). Hence the
proof is literally `rfl`.

Both `curve` (the universal Weierstrass curve over `MvPolynomial Coeff ℤ`, line 84),
`Universal.Field` (= `FractionRing Universal.Ring`, line 99) and `pointedCurve` are bespoke
constructions of this project; the universal pointed elliptic curve over the field of fractions
of `ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨P⟩`. `curveField_eq` exists only as internal glue, so later code can
rewrite freely between the names `curveField` and `pointedCurve`.

## 2. Literature search

- Mathlib's division-polynomial / EDS development
  (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html`,
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`) treats `ψₙ, φₙ, ωₙ` for a generic
  curve `W/R` but contains **no "universal Weierstrass/elliptic curve" object** and nothing of
  the `curveField`/`pointedCurve` shape.
- The mathematical "universal elliptic curve" appears in the p-adic EDS literature (Ayad;
  arXiv:math/0404412) and division-polynomial papers (arXiv:2503.15428, arXiv:2102.07573), but
  purely as mathematics — not as a formalised mathlib construction. None of it corresponds to a
  named-alias equality.

There is no literature-standard *lemma* here; this is a definitional bookkeeping identity, not a
theorem.

## 3. Mathlib search (five methods)

- The statement mentions `Universal.curve`, `Universal.Field`, `Universal.pointedCurve`,
  `curveField` — **none of these exist in mathlib** (`grep` over
  `Mathlib/AlgebraicGeometry/EllipticCurve/` and `EllipticDivisibilitySequence.lean` returns
  nothing for `Universal | pointedCurve | curveField | universal elliptic`). The lemma is
  therefore **inexpressible** in mathlib as written.
- The only mathlib ingredient is `WeierstrassCurve.baseChange`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:236`), which the project already
  uses. No mathlib lemma states an equality of two notations for the same `baseChange`
  application — because no such lemma is needed (it is `rfl`).
- loogle / leansearch by shape ("equality of two `baseChange` aliases") has no target: there is
  no general statement to match.

## 4. Generality analysis

There is no more-general form to extract. The content reduces to: *two `abbrev`s unfolding to the
identical term are equal*. That is reflexivity, already fully available in core Lean. Nothing
about Weierstrass curves, base change, or the universal construction is actually being proved.

## 5. Composition check (≤ 3 mathlib calls)

Zero mathlib calls required: the goal closes by `rfl`. Once a downstream user has two definitions
that are definitionally equal, `rfl` (or `Iff.rfl`/`rfl`) gives the bridge immediately. There is
no API gap and no reusable lemma worth landing — adding it to mathlib would only ship a name for a
reflexivity proof tied to two project-private aliases.

## 6. Five-bucket decision

- Not **NO-mathlib-has-it**: mathlib cannot even state it (the symbols are project-local).
- Not **YES-add-as-is** / **YES-but-generalise-first**: it carries no mathematical content beyond
  reflexivity and is welded to two bespoke local abbreviations.
- Not **BORDERLINE**: the call is unambiguous.
- **NO-composable-from-mathlib**: a trivial `rfl` identity between two local aliases of the same
  `WeierstrassCurve.baseChange` term; any consumer reconstructs it in one line. Pure internal
  convenience, not mathlib material.

**Final verdict: NO-composable-from-mathlib.**
