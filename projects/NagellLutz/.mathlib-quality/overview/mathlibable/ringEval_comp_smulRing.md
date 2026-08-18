# Mathlibable assessment — `WeierstrassCurve.ringEval_comp_smulRing`

**Verdict bucket:** `NO-composable-from-mathlib`
**Qualified name:** `WeierstrassCurve.ringEval_comp_smulRing`
**One-line rationale:** Two-line definitional naturality glue over three project-private objects; an internal helper, not a standalone mathlib decl.

---

## 1. The declaration (verified from source)

File: `projects/NagellLutz/LutzNagell/ZSMul.lean:557`
Namespace: `WeierstrassCurve` (confirmed: `namespace WeierstrassCurve` at L76, `end Universal` at L546, this lemma at L557, `end`/`end WeierstrassCurve` at L625/627). Section variables in scope: `{R} [CommRing R] (W : WeierstrassCurve R)`, `{x y : R}`, and `variable {W} (eqn : W.toAffine.Equation x y)` (L553).

```lean
lemma ringEval_comp_smulRing (n : ℤ) : ringEval eqn ∘ smulRing n = smulEval W x y n := by
  conv_rhs => rw [smulEval, ← W.map_specialize, map_φ, map_ω, map_ψ, ← coe_mapRingHom,
    ← Jacobian.comp_fin3, ← Function.comp_assoc, ← smulPoly, ← coe_evalEvalRingHom,
    ← RingHom.coe_comp, ← eval₂RingHom_eval₂RingHom]
  rw [smulRing, ← Function.comp_assoc, ← RingHom.coe_comp, ringEval_comp_mk, polyEval]
```

### What it says
`smulRing n` and `smulEval W x y n` are both `Fin 3 → _` tuples of division-polynomial data:

- `smulPoly n := ![curve.φ n, curve.ω n, curve.ψ n]` — the universal division polynomials in
  `Poly = ℤ[A₁,…,A₆][X][Y]` (ZSMul L414).
- `smulRing n := AdjoinRoot.mk _ ∘ smulPoly n : Fin 3 → Universal.Ring` — their images in the
  **universal coordinate ring** `Universal.Ring = curve.CoordinateRing` (ZSMul L416).
- `smulEval W x y n := evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n] : Fin 3 → R` — the division
  polynomials of the *concrete* curve `W`, evaluated at the point `(x,y)` (ZSMul L551).
- `ringEval eqn : Universal.Ring →+* R` — the **specialization homomorphism**
  `AdjoinRoot.lift (eval₂RingHom W.specialize x) y …` induced by a point `(x,y)` on `W`
  (Universal.lean L215), valid because `eqn : Affine.Equation W x y`.

The lemma is the **naturality square**: applying the specialization map `ringEval eqn` to the
universal tuple `smulRing n` yields exactly the evaluated concrete tuple `smulEval W x y n`. I.e.
"forming the division-polynomial Jacobian tuple commutes with specialization at a point."

### Its proof
Pure rewriting that unfolds the four project abbreviations and pushes the ring hom through the
`Fin 3` tuple, reduced to the project's own computation rule `ringEval_comp_mk` (the `AdjoinRoot.lift`
β-rule, Universal.lean L223) and `map_φ/ω/ψ` + `map_specialize`. The only mathlib-native atom used for
the tuple is `Jacobian.comp_fin3` (already in `Mathlib/.../Jacobian/Basic.lean:130`). No mathematical
content beyond "specialization is a ring hom and the division polynomials are functorial."

### Its only consumers (all in-project)
`ringEval_ψ` (L563), `dblXYZ_smulEval` (L568), `addXYZ_smulEval` (L572), `addXYZ_smulEval₁` (L580) —
which feed the genuinely interesting theorem `zsmul_eq_smulEval` (L590), the multiplication-by-`n`
formula `n • (x,y) = ⟦(φₙ, ωₙ, ψₙ)⟧` in Jacobian coordinates.

---

## 2. Literature search

- **Standard result.** `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)` (division-polynomial multiplication formula) is
  classical — Silverman, *AEC* III/Exercise 3.7; Washington, *Elliptic Curves* §3.2; arXiv:2302.03650
  (multiplication polynomials over local rings). **But that named result is the project's
  `zsmul_eq_smulEval`, not this lemma.** `ringEval_comp_smulRing` is the internal "specialization
  commutes with the tuple" step and has **no name / no statement in the literature** — it is a Lean
  bookkeeping artifact of the universal-curve proof strategy.
- **Provenance.** File `Authors: Junyan Xu`; this is the Angdinata–Xu Weierstrass group-law line of
  work (ITP 2023, LIPIcs vol. 268). The `Universal`/`ZSMul` development extends mathlib's existing
  division-polynomial files and is **not yet upstreamed**. So this lemma is a private helper inside a
  development that, *as a whole*, is plausibly mathlib-bound — but the helper itself is not the unit
  that would be contributed.

## 3. Mathlib search (five methods) — NOT PRESENT

Searched the pinned mathlib tree at `.lake/packages/mathlib/Mathlib`:

1. **Exact name** `ringEval_comp_smulRing` → absent.
2. **Constituents** `ringEval` / `smulRing` / `smulEval` / `smulPoly` → all absent. The statement
   cannot even be *typed* in mathlib: none of its subjects exist there.
3. **Concept** — a universal-coordinate-ring + specialization-homomorphism scaffold for division
   polynomials → absent. (`grep "universal Weierstrass" / "the universal ring"` → only the unrelated
   `RingTheory/Polynomial/UniversalFactorizationRing.lean`.)
4. **The theorem it serves** (`[n]P = (φₙ:ωₙ:ψₙ)`) → also absent from mathlib's
   `AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean`; those define `ψ, φ, ω`
   and compute degrees but stop short of the multiplication formula. So even the *parent* result is
   not yet in mathlib.
5. **Shape / loogle-style** (a `RingHom` intertwining two `Fin 3 → _` tuples via `∘`) → the only
   reusable atom, `comp_fin3`, is **already in mathlib** (`Jacobian/Basic.lean:130`); there is no
   general "map commutes with a coordinate tuple" lemma worth extracting, and this instance is too
   specialized to be one.

## 4. Generality analysis

The statement is maximally specialized to project-private objects (`ringEval`, `smulRing`,
`smulEval`). There is no more-general literature form to weaken toward — it is already an instance of
the trivial schema "a ring hom commutes with a finite tuple of functorial polynomials," whose general
form is just `comp_fin3` + `map_φ/ω/ψ`. Nothing to generalise.

## 5. Composition check (≤ 3 mathlib calls?)

Trivially "composable" in the sense that the proof is 2 lines of `rw` over project lemmas
(`ringEval_comp_mk`, `map_specialize`, `map_φ/ω/ψ`, `comp_fin3`). **But it is NOT composable from
mathlib primitives**, because three of its four ingredients are not in mathlib at all. It is glue
internal to an unupstreamed development, reconstructible in-line wherever needed.

## 6. Verdict

**`NO-composable-from-mathlib`.**

Do **not** add this as a standalone mathlib declaration. It is a two-line definitional-naturality
helper whose entire purpose is to carry the universal division-polynomial tuple across the project's
specialization homomorphism; it has no name or content in the literature and no independent
re-use value. The genuinely mathlibable object in this file is the **multiplication-by-`n` formula
`zsmul_eq_smulEval`** (and the universal-ring machinery that supports it). If/when that development is
upstreamed by its author, `ringEval_comp_smulRing` would travel along **as a `private`/file-internal
lemma of the same module**, named identically — never as a separately contributed public lemma.

Edge note for a human: the "NO" here is "not as a standalone unit," not "this math doesn't belong in
mathlib." The parent theorem plausibly does. If the reviewer is assessing the *whole* `Universal`/
`ZSMul` track rather than this single decl, re-run the assessment on `zsmul_eq_smulEval`
(`ZSMul.lean:590`) instead.

---

### Sources
- mathlib (pinned, local): `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean`, `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Basic.lean` (`comp_fin3`).
- Project: `projects/NagellLutz/LutzNagell/{Universal,ZSMul}.lean`.
- Silverman, *The Arithmetic of Elliptic Curves*, ch. III; Washington, *Elliptic Curves*, §3.2.
- Angdinata & Xu, *An Elementary Formal Proof of the Group Law on Weierstrass Elliptic Curves in Any Characteristic*, ITP 2023 (LIPIcs vol. 268): https://drops.dagstuhl.de/storage/00lipics/lipics-vol268-itp2023/LIPIcs.ITP.2023.6/LIPIcs.ITP.2023.6.pdf
- *Multiplication polynomials for elliptic curves over finite local rings*, arXiv:2302.03650: https://arxiv.org/pdf/2302.03650
