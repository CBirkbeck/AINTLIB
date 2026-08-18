# Mathlibable assessment: `WeierstrassCurve.Universal.cusp_ψ₂`

> Qualified name **verified from source**. The lemma sits at
> `projects/NagellLutz/LutzNagell/ZSMul.lean:110`, inside `namespace WeierstrassCurve`
> (opened line 76) → `namespace Universal` (opened line 86). Hence the full name is
> **`WeierstrassCurve.Universal.cusp_ψ₂`** (the parsed name in the prompt was correct).

## The declaration

```lean
lemma cusp_ψ₂ : cusp.ψ₂ = 2 * Y := by simp [cusp, ψ₂, Affine.polynomialY, C_ofNat]
```

- `cusp` is the **project-local** singular cubic `Y² = X³`, defined at
  `projects/NagellLutz/LutzNagell/Universal.lean:180` as
  `def cusp : Affine ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }`,
  i.e. the Weierstrass record `⟨0,0,0,0,0⟩`.
- `ψ₂` is the 2-division polynomial. In this project (a fork of mathlib's
  `DivisionPolynomial.*`) it is `noncomputable def ψ₂ := W.toAffine.polynomialY`
  (`projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:36`) — identical to mathlib's
  `WeierstrassCurve.ψ₂` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:113`).
- `Y` is mathlib's `Polynomial.Bivariate` notation for the second variable
  (`scoped[Polynomial.Bivariate] notation3:max "Y" => Polynomial.X (R := Polynomial _)`,
  `Mathlib/Algebra/Polynomial/Bivariate.lean:26`).

**Mathematical content.** The 2-division polynomial of any Weierstrass curve is
`ψ₂ = polynomialY = 2Y + a₁X + a₃` (mathlib:
`def polynomialY := C (C 2) * Y + C (C W.a₁ * X + C W.a₃)`,
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:192-193`). Substituting the cusp's
coefficients `a₁ = a₃ = 0` kills the affine term, leaving `ψ₂ = 2Y`. So this lemma is a single
**numeric specialisation** of an already-existing mathlib formula to one fixed singular curve.

## Role in the project

`cusp_ψ₂` is one of three companion value lemmas on the same source line block:

```lean
lemma cusp_ψ₂   : cusp.ψ₂   = 2 * Y       := …   -- ZSMul.lean:110  (this decl)
lemma cusp_Ψ₃   : cusp.Ψ₃   = 3 * X ^ 4   := …   -- ZSMul.lean:111
lemma cusp_preΨ₄ : cusp.preΨ₄ = 2 * X ^ 6 := …   -- ZSMul.lean:112
```

These three feed `polyEval_cusp_ψ : polyEval cusp 1 1 (curve.ψ n) = n` (ZSMul.lean:114), via
`rw [ψ, map_normEDS, ← evalEval_ψ₂, …, cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]` and
`normEDS_two_three_two`. That in turn drives `ψᵤ_ne_zero` (ZSMul.lean:142): the universal
division polynomial `ψₙ` is non-zero for `n ≠ 0`, proved by specialising the universal ring to
`ℤ` at the cusp point `(1,1)` (where `ψₙ(1,1) = n`). This is the project's **bespoke
"degenerate-fibre" technique** for universal non-vanishing — exactly the same plumbing that the
sibling lemma `cusp_equation_one_one` supports (see that report).

**Call sites of `cusp_ψ₂`:** used once, inside `polyEval_cusp_ψ` (ZSMul.lean:115). K = 1. No
external consumers.

## (3) Literature search

- The general identity `ψ₂ = 2y + a₁x + a₃` is the textbook definition of the 2-division
  polynomial (Silverman, *Arithmetic of Elliptic Curves*, Exercise 3.7; Ward's EDS theory,
  where `Wₙ = λ^{n²-1} Ψₙ(x,y)` over an elliptic curve **or singular cubic** — see the
  EDS literature: arXiv:2102.07573, arXiv:0710.1316, Wikipedia "Elliptic divisibility sequence").
- The specialisation to the cuspidal cubic `Y²=X³` (giving `ψ₂ = 2y`) is a one-line substitution
  recorded by **no source as a named statement**. Using the singular fibre `Y²=X³` to read off
  EDS values (here `ψₙ(1,1)=n`, the "degenerate EDS" `Wₙ = n`) is a known computational device but
  not a quotable theorem with a name.
- Verdict of this phase: the *underlying* general formula is standard and already in mathlib; the
  cusp specialisation is trivial arithmetic, not literature-named.

## (5) Mathlib search (five methods)

Mathlib **already has the general lemma this specialises**:

| object | mathlib location |
|---|---|
| `WeierstrassCurve.Affine.polynomialY := C (C 2) * Y + C (C a₁ * X + C a₃)` | `Affine/Basic.lean:192` |
| `WeierstrassCurve.ψ₂ := W.toAffine.polynomialY` | `DivisionPolynomial/Basic.lean:113` |
| `evalEval_polynomialY : polynomialY.evalEval x y = 2*y + a₁*x + a₃` | `Affine/Basic.lean:195` |

Targeted searches for the *specialised* statement:
- `grep` for `cusp_ψ`, `cusp.ψ₂`, `2 * Y` over `Mathlib/` → **no hit** for a cusp 2-division-poly
  lemma. The only `2 * Y` / `polynomialY` hits are unrelated (`FLT/Three.lean`,
  `Jacobian/Basic.lean:328 polynomialY_eq`, `Projective/Basic.lean:322`).
- `grep` for `cusp` over `Mathlib/` → only the **modular-forms** sense
  (`cuspFunction` in `Analysis/Complex/Periodic.lean`, `ModularForms/Cusps.lean`). Mathlib has
  **no singular-cubic / cusp-curve object** — `Y²=X³` is singular and outside the elliptic-curve
  API's interest, so there is nothing for this lemma to specialise *to* within mathlib.

Conclusion: the **general** formula is in mathlib; the **cusp specialisation as a named lemma** is
not, and mathlib has no `cusp` definition to attach it to.

## (6) Composition check

Trivially composable from existing mathlib in ≤2 calls. Given the general formula
`ψ₂ = C (C 2) * Y + C (C a₁ * X + C a₃)`, for `cusp` (`a₁=a₃=0`) the affine summand is `0`:

```lean
example : cusp.ψ₂ = 2 * Y := by
  simp [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY, cusp]  -- a₁=a₃=0 ⇒ term drops
-- equivalently: rw [ψ₂, polynomialY]; simp [cusp]; ring
```

The project's own one-liner (`simp [cusp, ψ₂, Affine.polynomialY, C_ofNat]`) is exactly this
composition. So COMPOSABLE: ≤2 mathlib calls (`ψ₂`/`polynomialY` unfold + `simp`/`ring` on the
zero coefficients). No new general lemma is implied.

## Generality analysis

The lemma is **MAXIMALLY SPECIALISED** (a numeric value at one fixed singular curve), the opposite
of a generalisation target. Its general parent — `ψ₂ = 2Y + a₁X + a₃` over an arbitrary
`[CommRing R]` curve — **already lives in mathlib** (`polynomialY`, line 192). There is no
"weaker-hypothesis" or "more-general" restatement to upstream: any generalisation *is* mathlib's
existing `polynomialY`/`ψ₂` definition, which this lemma merely evaluates.

---

## Verdict: `WeierstrassCurve.Universal.cusp_ψ₂`

**Category:** NO-composable-from-mathlib

**Evidence:**
- **Literature (3):** the general `ψ₂ = 2y + a₁x + a₃` is textbook (Silverman; Ward EDS theory over
  curves *and* singular cubics). The cusp specialisation `ψ₂ = 2Y` is a one-line substitution named
  by no source.
- **Mathlib (5):** the general formula is *already in mathlib* (`polynomialY`, `Affine/Basic.lean:192`;
  `ψ₂`, `DivisionPolynomial/Basic.lean:113`). No `cusp` object and no cusp-`ψ₂` lemma exist in
  mathlib ("cusp" there = modular forms only). `Y²=X³` is singular, deliberately outside the EC API.
- **Generality (4):** maximally specialised; its general parent *is* mathlib's `polynomialY`. Nothing
  to generalise/upstream.
- **Composition (6):** COMPOSABLE in ≤2 calls — unfold `ψ₂`/`polynomialY`, then `simp`/`ring` using
  `cusp`'s zero coefficients. The project's existing one-liner is precisely this.

**Rationale.**
`cusp_ψ₂` is project-local scaffolding, not a mathlib candidate. It says only that the 2-division
polynomial of the cuspidal cubic `Y²=X³` is `2Y` — a single evaluation of mathlib's existing
`WeierstrassCurve.ψ₂ = polynomialY = 2Y + a₁X + a₃` at the coefficient record `⟨0,0,0,0,0⟩`, where
the `a₁X + a₃` term vanishes. Mathlib already owns the general formula and has no notion of a "cusp
curve" to which a named specialisation could attach (`Y²=X³` is singular and out of scope for the
elliptic-curve API; the word "cusp" in mathlib is the unrelated modular-forms sense). This is exactly
the situation of the sibling lemma `cusp_equation_one_one` (also `NO-composable-from-mathlib`): both
are bespoke witnesses in *this* project's degenerate-fibre proof that the universal `ψₙ` is non-zero
(via `ψₙ(1,1) = n` on the cusp).

**WHY not (refactor-actionable):** the building block is mathlib's
`WeierstrassCurve.ψ₂` / `WeierstrassCurve.Affine.polynomialY`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:192`). The user's statement is a ≤2-call
specialisation of it for `cusp`. No new mathlib lemma is needed.

**Composition sketch (≤3 lines):**
```lean
example : cusp.ψ₂ = 2 * Y := by
  simp [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY, cusp]
-- (this is essentially the project's existing one-liner)
```

**Important caveat for the refactor — do NOT delete.** Like `cusp_equation_one_one`, this is a
*named* intermediate value reused inside `polyEval_cusp_ψ` (the engine for universal `ψₙ`
non-vanishing). Keeping the three companion value lemmas (`cusp_ψ₂`, `cusp_Ψ₃`, `cusp_preΨ₄`) as
tidy project-local helpers is correct mathlib-style practice — inlining the `simp`/`ring`
computation at the `rw […]` site in `polyEval_cusp_ψ` would be strictly worse for readability. So
"NO-composable" here means **it does not belong *in mathlib***; it should remain a private/local
helper in the NagellLutz project (alongside `def cusp`, `cusp_equation_one_one`, `cusp_Ψ₃`,
`cusp_preΨ₄`).

**Next action:** keep `WeierstrassCurve.Universal.cusp_ψ₂` as project-local scaffolding for the
universal-`ψₙ`-non-vanishing argument. No mathlib PR; no deletion.

Mathlib building blocks: `WeierstrassCurve.ψ₂`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:113`),
`WeierstrassCurve.Affine.polynomialY`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:192`).

### Sources
- [A recurrence relation for elliptic divisibility sequences](https://arxiv.org/pdf/2102.07573)
- [Elliptic nets and elliptic curves](https://arxiv.org/pdf/0710.1316)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
