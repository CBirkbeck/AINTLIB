# Mathlibable assessment: `WeierstrassCurve.Universal.algebraMap_ring_eq_comp`

**Verdict: NO-mathlib-has-it**

## 1. Declaration under review

Source: `projects/NagellLutz/LutzNagell/Universal.lean:116-118`
Qualified name (verified from source — inside `namespace WeierstrassCurve` (L69) → `namespace Universal` (L75), closed L177/L243):

```
WeierstrassCurve.Universal.algebraMap_ring_eq_comp
```

Statement:

```lean
lemma algebraMap_ring_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Ring = (AdjoinRoot.mk _).comp (algebraMap _ _) :=
  rfl
```

Unfolding the local abbreviations:
- `Universal.Ring := curve.CoordinateRing` (L96).
- `curve.CoordinateRing := AdjoinRoot curve.polynomial` (mathlib `Affine.CoordinateRing`,
  `Affine/Point.lean:90`), where `curve.polynomial : Poly` and
  `Poly := (MvPolynomial Coeff ℤ)[X][Y]` (L94).

So the statement is, with `S := MvPolynomial Coeff ℤ`, `R := (MvPolynomial Coeff ℤ)[X]`,
`f := curve.polynomial : R[X][Y]`:

```
algebraMap S (AdjoinRoot f) = (AdjoinRoot.mk f).comp (algebraMap S Poly)
```

i.e. the structure map from the coefficient ring into the universal coordinate ring factors as
"include into the 7-variable polynomial ring `Poly`, then take the `AdjoinRoot` quotient `mk`".
Proof is `rfl`.

## 2. Role in the project (not dead code)

Used by `ringEval_comp_eq_specialize` (L229-230):

```lean
lemma ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap _ _) = W.specialize := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]
```

The lemma's only purpose is to rewrite `algebraMap … Universal.Ring` into a form ending in
`AdjoinRoot.mk _`, so the next rewrite `ringEval_comp_mk` (stated with `AdjoinRoot.mk`) can fire.
A byte-identical copy exists in `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:119`
(same consolidation fork), so it is duplicated, not unique.

## 3. Literature search

This is not a mathematical theorem; it is the universal-property bookkeeping identity
"the structure map to a quotient algebra over a sub-base factors through the larger ring's
structure map composed with the quotient projection". No textbook states it as a named result;
it is the standard `R → R[X]/(f)` factorization through `R[X] ↠ R[X]/(f)` (Atiyah–Macdonald-style
quotient functoriality), and is captured generically by scalar-tower / quotient-map lemmas in any
formalization. WebSearch over the mathlib docs confirms the mathlib lemma below is described as
"how the algebraMap from `S` to `AdjoinRoot f` relates to composition of the map with the base
ring's algebraMap" — exactly this statement.

## 4. Mathlib search (five methods) — IT IS ALREADY THERE

Direct source read of `Mathlib/RingTheory/AdjoinRoot.lean`:

```lean
-- AdjoinRoot.lean:103-104
def of : R →+* AdjoinRoot f := (mk f).comp C

-- AdjoinRoot.lean:146-148
@[simp] theorem algebraMap_eq : algebraMap R (AdjoinRoot f) = of f := rfl

-- AdjoinRoot.lean:150-153
variable (S) in
theorem algebraMap_eq' [CommSemiring S] [Algebra S R] :
    algebraMap S (AdjoinRoot f) = (of f).comp (algebraMap S R) := rfl
```

`AdjoinRoot.algebraMap_eq'` **is this lemma**. Instantiate it at `S = MvPolynomial Coeff ℤ`,
`R = (MvPolynomial Coeff ℤ)[X]`, `f = curve.polynomial`:

```
algebraMap S (AdjoinRoot f) = (of f).comp (algebraMap S R)
```

Now `of f = (mk f).comp C` and `algebraMap S R = algebraMap S S[X] = C`, so the RHS is

```
((mk f).comp C).comp C = (mk f).comp (C.comp C) = (AdjoinRoot.mk f).comp (algebraMap S Poly)
```

because `C.comp C = algebraMap (MvPolynomial Coeff ℤ) ((MvPolynomial Coeff ℤ)[X][Y]) = algebraMap S Poly`.
This is **definitionally identical** (both sides `rfl`) to `algebraMap_ring_eq_comp`. The project
lemma merely re-associates the two `C` layers as `mk ∘ (C∘C)` instead of mathlib's `(mk∘C) ∘ C`,
and renames `of` back to `mk`. There is no mathematical content beyond `algebraMap_eq'`.

Additionally, the strictly more general **`IsScalarTower.algebraMap_eq`** subsumes it:

```lean
-- Mathlib/Algebra/Algebra/Tower.lean:127
theorem algebraMap_eq : algebraMap R A = (algebraMap S A).comp (algebraMap R S)
```

for any tower `R → S → A`; here the tower is `MvPolynomial Coeff ℤ → Poly → AdjoinRoot curve.polynomial`
(`IsScalarTower R R[X] CoordinateRing` is a mathlib instance, `Affine/Point.lean:104`).

Methods cross-checked:
- exact-name / `algebraMap_eq` family — found `AdjoinRoot.algebraMap_eq`, `algebraMap_eq'`.
- type-shape (`algebraMap … = _.comp (algebraMap …)`) — found both `AdjoinRoot.algebraMap_eq'`
  and `IsScalarTower.algebraMap_eq`.
- WebSearch / mathlib4 docs — corroborated `algebraMap_eq'` is the intended lemma.
- definitional check — confirmed `rfl`-equality to `algebraMap_eq'` above.

## 5. Generality analysis

The project lemma is *less* general than `AdjoinRoot.algebraMap_eq'`: it is hard-wired to the
specific `curve.polynomial` over `MvPolynomial Coeff ℤ`, whereas `algebraMap_eq'` is stated for an
arbitrary base `S`, arbitrary `R`, arbitrary `f`. And `IsScalarTower.algebraMap_eq` is more general
still (no `AdjoinRoot` needed). So there is no "generalise-first" path that lands anywhere new —
the general statements already exist upstream.

## 6. Composition check (≤ 3 mathlib calls)

Trivially yes — zero non-trivial calls:
- `exact AdjoinRoot.algebraMap_eq' _` discharges it (modulo a `rfl`-level `of`/`mk` reassociation);
- or `rfl` directly (as written);
- the only reason the project keeps it as a named lemma is to expose the `AdjoinRoot.mk` spelling
  on the RHS so that `ringEval_comp_mk` rewrites cleanly. That is a local proof-ergonomics choice,
  not new API. The downstream `rw` could instead use `AdjoinRoot.algebraMap_eq'` followed by the
  existing `of`/`mk` defeq, or `IsScalarTower.algebraMap_eq`.

## 7. Verdict

**NO-mathlib-has-it.** `algebraMap_ring_eq_comp` is a `rfl` restatement of mathlib's
`AdjoinRoot.algebraMap_eq'` (and is subsumed by the more general `IsScalarTower.algebraMap_eq`),
specialized to the universal Weierstrass curve. It carries no mathematical content not already in
mathlib; it is project-local glue whose only added value is the RHS spelling with `AdjoinRoot.mk`.
Do not upstream. (Cleanup note for the project, not for mathlib: the lemma — and its HasseWeil twin —
could be replaced at its single use site by `AdjoinRoot.algebraMap_eq'`/`IsScalarTower.algebraMap_eq`,
but that is a local dedup decision, outside the scope of this mathlibability verdict.)

### Evidence anchors
- Project lemma: `projects/NagellLutz/LutzNagell/Universal.lean:116-118`; use site L229-230.
- Duplicate: `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:119`.
- `Universal.Ring = AdjoinRoot curve.polynomial`: L96 + `Affine/Point.lean:90`.
- mathlib hit: `AdjoinRoot.algebraMap_eq'`, `.lake/.../Mathlib/RingTheory/AdjoinRoot.lean:150-153`
  (`of` at L103-104, `algebraMap_eq` at L146-148).
- general form: `IsScalarTower.algebraMap_eq`, `.lake/.../Mathlib/Algebra/Algebra/Tower.lean:127`.
