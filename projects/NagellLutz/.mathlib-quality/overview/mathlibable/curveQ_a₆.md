# Mathlibable assessment: `LutzNagell.LutzNagellTheorem.curveQ_a₆`

**Verdict: NO-mathlib-has-it**

> One-line rationale: This is `WeierstrassCurve.map_a₆` (already in mathlib, `@[simp]`) specialised to `f = algebraMap ℤ ℚ`.

---

## 1. The declaration

File: `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralCurve.lean:31`

Qualified name (verified from source): `LutzNagell.LutzNagellTheorem.curveQ_a₆`
(inside `namespace LutzNagell` → `namespace LutzNagellTheorem`).

```lean
open WeierstrassCurve
variable (W : WeierstrassCurve ℤ)

/-- The base change of `W` to `ℚ`. -/
abbrev curveQ (W : WeierstrassCurve ℤ) : WeierstrassCurve ℚ :=
  W.map (algebraMap ℤ ℚ)

@[simp] lemma curveQ_a₆ : (curveQ W).a₆ = (W.a₆ : ℚ) := by simp [curveQ]
```

So the statement, after unfolding the `curveQ` abbreviation, is:

```lean
(W.map (algebraMap ℤ ℚ)).a₆ = (W.a₆ : ℚ)
```

Proof: `simp [curveQ]` (one line). It is one of five sibling lemmas `curveQ_a₁ … curveQ_a₆`,
all of the identical shape, fixing the ring hom to `algebraMap ℤ ℚ` and rewriting the RHS
`algebraMap ℤ ℚ W.a₆` to the `Int.cast` coercion `(W.a₆ : ℚ)`.

This is pure project-local glue: `curveQ` is a renamed, ℤ→ℚ-fixed alias for mathlib's
`WeierstrassCurve.baseChange`, and `curveQ_a₆` is the corresponding coefficient-rewrite lemma
expressed through the `↑ : ℤ → ℚ` coercion rather than `algebraMap`.

## 2. Literature search

Not applicable as a *mathematical* result — there is no theorem here. "The constant
coefficient of a Weierstrass curve is preserved (applied through the hom) under base change /
ring-hom mapping" is a definitional bookkeeping fact, not a named result in any reference
(Silverman, AEC; Washington, *Elliptic Curves: Number Theory and Cryptography*; etc.). It is
exactly the kind of `@[simps]`-generated projection lemma that lives in mathlib's
elliptic-curve API, never in the literature.

## 3. Mathlib search — IT IS ALREADY THERE (general form)

Mathlib defines, in `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` (local copy at
`.lake/packages/mathlib/...`, lines 229–232):

```lean
/-- The Weierstrass curve mapped over a ring homomorphism `f : R →+* A`. -/
@[simps]
def map : WeierstrassCurve A :=
  ⟨f W.a₁, f W.a₂, f W.a₃, f W.a₄, f W.a₆⟩
```

The `@[simps]` attribute auto-generates the five `@[simp]` projection lemmas, including:

```lean
@[simp]
theorem WeierstrassCurve.map_a₆ {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {A : Type v} [CommRing A] (f : R →+* A) :
    (W.map f).a₆ = f W.a₆
```

Confirmed two independent ways:
- **Local mathlib source**: `map` is `@[simps]` (Weierstrass.lean:230); downstream lemmas in the
  same file (`map_b₂`, `map_b₄`, `map_b₆`, `map_b₈`) explicitly call `map_a₁ … map_a₆` in their
  proofs, proving these projection lemmas exist and carry exactly these names (lines 243–259).
- **mathlib4 docs** (leanprover-community.github.io/mathlib4_docs): `WeierstrassCurve.map_a₁ …
  map_a₆`, all `@[simp]`, all over a ring hom `f : R →+* A`, statement `(W.map f).aᵢ = f W.aᵢ`.

`WeierstrassCurve.map_a₆` is **strictly more general** than `curveQ_a₆`: it holds for any
`f : R →+* A` between commutative rings, whereas `curveQ_a₆` fixes `R = ℤ`, `A = ℚ`,
`f = algebraMap ℤ ℚ`.

Note: the prompt flagged that this project forks `Mathlib.AlgebraicGeometry.EllipticCurve.
DivisionPolynomial.*` and `Mathlib.NumberTheory.EllipticDivisibilitySequence`. That fork is
irrelevant here — `curveQ_a₆` lives in the base-change layer (`Weierstrass.lean`), which is **not**
forked, and the upstream `map_a₆` is present and unmodified in the pinned mathlib.

## 4. Generality analysis

`curveQ_a₆` is a strict specialisation of `WeierstrassCurve.map_a₆`:
- general: `(W.map f).a₆ = f W.a₆`, any `f : R →+* A`;
- project: `(W.map (algebraMap ℤ ℚ)).a₆ = (W.a₆ : ℚ)`, with the RHS rewritten from
  `algebraMap ℤ ℚ W.a₆` to `Int.cast W.a₆` via `algebraMap_int_eq` / `eq_intCast` / `map_intCast`.

There is nothing to generalise *into mathlib*: the maximally-general statement is already the
mathlib lemma. The ℤ→ℚ version exists only to (a) talk about the project's `curveQ` alias and
(b) present the coefficient as an `Int.cast` coercion, which is local presentation sugar.

## 5. Composition check (≤ 3 mathlib calls)

`curveQ_a₆` follows from mathlib in essentially one rewrite:

```lean
example (W : WeierstrassCurve ℤ) :
    (W.map (algebraMap ℤ ℚ)).a₆ = (W.a₆ : ℚ) := by
  rw [WeierstrassCurve.map_a₆]   -- (1) the mathlib lemma  → algebraMap ℤ ℚ W.a₆
  simp                            -- (2) algebraMap ℤ ℚ = Int.cast, e.g. eq_intCast/map_intCast
```

That is ≤ 2 mathlib calls (the project's own proof is the single `simp [curveQ]`, since `simp`
already knows `map_a₆` and the `algebraMap ℤ ℚ = Int.cast` simp set). Fully composable, and the
core fact is verbatim in mathlib.

## 6. Verdict

**NO-mathlib-has-it.**

The general result — coefficient `a₆` mapped through `f` under `WeierstrassCurve.map` — is
already in mathlib as the `@[simp]` lemma `WeierstrassCurve.map_a₆`, generated by the `@[simps]`
on `WeierstrassCurve.map` (`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`).
`curveQ_a₆` is merely that lemma specialised to `algebraMap ℤ ℚ` and restated via the `Int.cast`
coercion, tied to the project's local `curveQ` (= `baseChange`-over-ℤ→ℚ) alias.

Recommendation for the consolidation pass: keep `curveQ_a₆` (and its `a₁…a₄` siblings) as local
convenience `@[simp]` lemmas if `curveQ` stays, but do **not** propose them to mathlib. Better
still, downstream proofs can drop them entirely and let mathlib's `map_a₆` + `simp` fire, or
inline `curveQ` to `W.baseChange ℚ` and use the existing `map_*` / `baseChange` API directly.

### Evidence index
- Source decl: `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralCurve.lean:24,31`
- Mathlib `map` (`@[simps]`): `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:229–232`
- Mathlib usages confirming `map_a₆` name: same file, lines 243–259 (`map_b₂…map_b₈`)
- mathlib4 docs: `WeierstrassCurve.map_a₆` (and `map_a₁…map_a₄`), all `@[simp]`, ring-hom general
