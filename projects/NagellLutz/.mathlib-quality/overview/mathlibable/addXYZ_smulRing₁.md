# Mathlibable assessment — `WeierstrassCurve.Universal.Jacobian.addXYZ_smulRing₁`

- **Date:** 2026-06-22
- **Project:** NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS)
- **Source:** `projects/NagellLutz/LutzNagell/ZSMul.lean:537`
- **Author of file:** Junyan Xu (per copyright header)
- **Verdict:** **YES-but-generalise-first**

---

## 0. The declaration (verified from source)

Qualified name (verified against the namespace stack `WeierstrassCurve` → `Universal` → `Jacobian`,
lines 76 / 86 / 395): **`WeierstrassCurve.Universal.Jacobian.addXYZ_smulRing₁`**.

```lean
lemma addXYZ_smulRing₁ :
    addXYZ curveRing (smulRing n) (smulRing (n + 1)) = smulRing (2 * n + 1) := by
  rw [addXYZ_smulRing, add_sub_cancel_left, ψ_one, map_one,
    show (1 : Universal.Ring) • smulRing (n + 1 + n) = smulRing (n + 1 + n) from by
      simp only [smul_fin3, one_pow, one_mul, fin3_def]]
  congr 1; omega
```

with `{n : ℤ}` an implicit variable (`variable {m n : ℤ}`, line 97).

### What it means
- `Universal.Ring` is the *universal* coefficient ring `ℤ[a₁,a₂,a₃,a₄,a₆,X,Y] / ⟨W-polynomial⟩`
  (the universal Weierstrass curve with a generic point `(X,Y)`).
- `curveRing := WeierstrassCurve.baseChange curve Universal.Ring`.
- `smulRing n : Fin 3 → Universal.Ring` is the triple of division polynomials assembled into
  Jacobian coordinates: `(φₙ, ωₙ, ψₙ)` mod the Weierstrass polynomial (lines 414–416). It is exactly
  the Jacobian coordinates of `n • point` (see `zsmul_point_eq_smulField`, line 424).
- `addXYZ` is mathlib's Jacobian-coordinate point-addition formula
  (`Mathlib/.../Jacobian/Formula.lean:661`).

So the statement is the **addition formula for consecutive multiples**: adding `n • P` and
`(n+1) • P` (in Jacobian coordinates given by division polynomials over the universal curve) yields
`(2n+1) • P`. It is the universal-ring incarnation of one of the two recurrences
(`addXYZ` for odd, `dblXYZ` for even) that drive the even–odd induction proving the headline result
`zsmul_eq_smulEval` (`n • (x,y) = (φₙ(x,y), ωₙ(x,y), ψₙ(x,y))`, line 590).

### The proof
A one-liner: specialise the **general** addition lemma `addXYZ_smulRing` (line 524,
`addXYZ curveRing (smulRing m) (smulRing n) = mk(ψ(n−m)) • smulRing(n+m)`) at `m → n`, `n → n+1`;
then `(n+1)−n = 1`, `ψ 1 = 1` (`ψ_one`), and `1 • v = v`, and reindex `n+1+n = 2n+1` by `omega`.

---

## 1. Literature search

- **WebSearch** ("mathlib elliptic curve division polynomial multiplication by n Jacobian
  coordinates smulEval …"): returns only the general mathematical background (Sutherland's 18.783
  notes; division-polynomial scalar-multiplication papers; the Mumford-coordinate preprint
  arXiv:2412.10284) and mathlib's *generic* Jacobian formula docs. **No** existing formalization of
  "`n • P` = division-polynomial triple in Jacobian coordinates", and nothing on a `smulEval` /
  `smulRing` API. This is the standard textbook fact (Silverman, *AEC*, exercise 3.7; Washington
  §3.2) that division polynomials compute scalar multiples — but its *formalization* is novel.
- The construction and naming (`Universal.Ring`, `smulRing`, `addXYZ_smulRing`, `zsmul_eq_smulEval`)
  are original to this file (Junyan Xu), not drawn from a published formalization.

## 2. Mathlib search (five methods)

Searched the pinned mathlib (`09b373db6e24`) at `.lake/packages/mathlib`:

- `grep` for `addXYZ_smulRing`, `smulRing`, `smulField`, `smulPoly`, `smulEval`,
  `zsmul_eq_smulEval` across all of `Mathlib/` → **zero hits**.
- `grep` for `namespace Universal` / `Universal.Ring` / `Universal.Field` in
  `Mathlib/AlgebraicGeometry/` → **zero hits** (only an unrelated `UniversallyOpen.lean`).
- mathlib **has the primitives**: `addXYZ`, `addZ`, `addXYZ_smul`, `addXYZ_self`, `map_addXYZ`,
  `dblXYZ`, `map_dblXYZ` (`Jacobian/Formula.lean`); and the division-polynomial / EDS theory:
  `DivisionPolynomial/Basic.lean` + `Degree.lean` (defines `ψ, φ, ω, ψ_one = 1`),
  `NumberTheory/EllipticDivisibilitySequence.lean` (`IsEllSequence`, `normEDS`, `preNormEDS`, …).
- mathlib **lacks the bridge**: nothing in `DivisionPolynomial/*` or `EllipticDivisibilitySequence`
  connects the polynomials `ψ/φ/ω` to actual point multiplication `n • P` or to Jacobian
  coordinates. `grep` of `DivisionPolynomial/Basic.lean` for `smul | n • | Point | Jacobian` finds
  only coordinate-ring prose, no scalar-multiple theorem.

**Conclusion:** neither this lemma nor any more-general "division polynomials give `n • P`" statement
exists in mathlib. The project genuinely forks mathlib's `DivisionPolynomial` (cf. project
`DivisionPolynomial.lean:334` `ψ_one`, byte-identical to mathlib `Basic.lean:411`) and *adds* the
multiplication-by-`n` layer on top.

## 3. Generality analysis

`addXYZ_smulRing₁` is deliberately stated over the **fixed** `Universal.Ring`. This is by design: the
file's strategy (module docstring, lines 24–56) is to prove each identity **once** over the universal
ring, then transport it to an arbitrary nonsingular point `(x,y)` over any `CommRing`/field via the
specialisation homomorphism `ringEval` (`ringEval_comp_smulRing`, line 557). The transported, fully
general statement already exists a few lines below:

```lean
addXYZ_smulEval₁ (n : ℤ) :                                        -- line 580
    addXYZ W (smulEval W x y n) (smulEval W x y (n + 1)) = smulEval W x y (2 * n + 1)
```

over an arbitrary `W : WeierstrassCurve R`, `[CommRing R]`, with `eqn : W.Equation x y`. So
`addXYZ_smulRing₁` is the **universal-ring shadow** of `addXYZ_smulEval₁`; it cannot itself be
weakened (it is already the most-general object — the universal ring — and is consumed precisely to
produce the general `…Eval₁` form).

## 4. Composition check (≤ 3 mathlib calls?)

**No.** The proof's load-bearing step is `addXYZ_smulRing` — a project-local lemma whose own proof
descends through `addXYZ_smulField` (line 499; a 25-line case analysis using
`equiv_iff_eq_of_Z_eq`, `zsmul_point_eq_smulField`, `addZ_smulPoly`, `ψᵤ_ne_zero`, …), which in turn
rests on the universal-point multiplication theorem `zsmul_point_eq_smulField` (line 424) and the
`Universal` curve construction (`Universal.lean`). None of `smulRing`, `addXYZ_smulRing`, the
`Universal` ring, or `zsmul_point_eq_smulField` exist in mathlib. The only *mathlib* calls in this
lemma's own body (`ψ_one`, `map_one`, `add_sub_cancel_left`, `smul_fin3`, `omega`) are trivial
plumbing around the missing project-local engine. Hence it is **not** composable from ≤ 3 mathlib
primitives.

## 5. Verdict — YES-but-generalise-first

The mathematics (division polynomials compute scalar multiples on an elliptic curve, as the
Jacobian-coordinate addition recurrence `addXYZ(n•P, (n+1)•P) = (2n+1)•P`) is **standard, correct,
and absent from mathlib** — the whole `zsmul_eq_smulEval` development it serves is squarely
mathlib-worthy and would be a valuable addition.

It is **not** `NO-mathlib-has-it` (verified absent, §2) and **not** `NO-composable-from-mathlib`
(the engine is entirely project-local, §4).

It is **not** `YES-add-as-is`, because as an *isolated* declaration this is the universal-ring
intermediate, not the statement a mathlib user wants. Its public-facing general form is its sibling
`addXYZ_smulEval₁` (arbitrary curve/ring/point, §3). If this development is upstreamed, the
multiplication-by-`n` corollaries should be exposed at the general (`…Eval` / point) level — the
universal-ring lemmas (`addXYZ_smulRing`, `addXYZ_smulRing₁`, …) belong in as `private`/internal
scaffolding, not as the headline API. Hence **generalise first**: contribute the bundle
(`addXYZ_smulEval₁` / `zsmul_eq_smulEval` as the API, with the `smulRing`/universal layer as the
proof's internals), rather than this single universal-ring corollary on its own.

Not `BORDERLINE`: the call is mechanical — the decl is genuinely new, the only question is the level
of generality at which to expose it, and the answer (the existing `…Eval₁` sibling) is unambiguous.

### Recommendation for a mathlib PR
Port the entire `Universal` + `smulRing`/`smulField`/`smulEval` machinery as one contribution whose
public theorems are `zsmul_eq_smulEval` and its even/odd recurrence corollaries `dblXYZ_smulEval`,
`addXYZ_smulEval₁` (general curve/ring). Keep `addXYZ_smulRing₁` (and the rest of the universal-ring
layer) as internal lemmas of that file.
