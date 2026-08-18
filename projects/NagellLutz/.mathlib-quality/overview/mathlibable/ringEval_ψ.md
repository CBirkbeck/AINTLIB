# Mathlibable assessment: `WeierstrassCurve.ringEval_ψ`

**Verdict: NO-composable-from-mathlib** (internal naturality glue; a ≤1-call projection of `ringEval_comp_smulRing`, resting on a project-private universal-ring construction)

- **Declaration:** `ringEval_ψ`
- **True qualified name:** `WeierstrassCurve.ringEval_ψ`
  (file opens `namespace WeierstrassCurve` at L76 and closes at L627; `end Universal` is at L546, so this L563 lemma lives directly in `WeierstrassCurve`, NOT `WeierstrassCurve.Universal`. The prompt's guess `WeierstrassCurve.ringEval_ψ` is correct.)
- **Location:** `projects/NagellLutz/LutzNagell/ZSMul.lean:563-565`
- **Author:** Junyan Xu (file header).
- **Assessed against repo-pinned mathlib rev** `09b373db6e24` (`lake-manifest.json`).

---

## 1. Exact statement and proof (from source)

```lean
lemma ringEval_ψ (n : ℤ) :
    ringEval eqn (AdjoinRoot.mk _ <| curve.ψ n) = evalEval x y (W.ψ n) :=
  congr_fun (ringEval_comp_smulRing eqn n) 2
```

with the ambient binders (L80, L84, L553):
`{R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)`, `{x y : R}`,
`(eqn : W.toAffine.Equation x y)`.

**What it says.** `ringEval eqn : Universal.Ring →+* R` is the *specialization
homomorphism* induced by a point `(x,y)` on `W`: from the universal coordinate ring
`Universal.Ring := curve.CoordinateRing = ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨P⟩`
(an `AdjoinRoot` quotient by the universal Weierstrass polynomial `P`), it sends each
universal coefficient `Aᵢ ↦ aᵢ` and `X,Y ↦ x,y` (`Universal.lean:215`, via `AdjoinRoot.lift`).
The lemma states that applying this specialization to the **universal** division polynomial
`curve.ψ n ∈ Universal.Ring` recovers the **concrete** division polynomial
`W.ψ n ∈ R[X][Y]` evaluated at `(x,y)` (`evalEval x y`). It is the `ψ`-component
(index `2`) of the packaged triple-naturality lemma

```lean
lemma ringEval_comp_smulRing (n : ℤ) : ringEval eqn ∘ smulRing n = smulEval W x y n
```

which handles `(φ, ω, ψ)` simultaneously (`ZSMul.lean:557-561`). The proof is literally a
single `congr_fun … 2`.

**Role.** Pure scaffolding inside the `zsmul_eq_smulEval` development: it is consumed by
`addXYZ_smulEval` (L575) to rewrite the addition formula's scaling factor `evalEval x y (W.ψ (n-m))`.
It is a leaf naturality/compatibility fact, not a headline result.

---

## 2. Literature search

- **WebSearch** (division-polynomial / universal-curve specialization / Nagell-Lutz / Lean):
  returns the standard corpus (Silverman-style division polynomials, EDS recurrences, the 2025
  "Nagell-Lutz over imaginary quadratic fields" paper, the Lean group-law formalization). None
  names this micro-lemma as a citable result. "Division polynomials specialize from the universal
  Weierstrass curve" is textbook folklore (the Weierstrass model is universal; everything in the
  generic coefficients `Aᵢ` specializes by a ring map). It is a *technique*, not a named theorem.
- **ChatGPT MCP:** unavailable in this environment (Codex binary fails on stdin — confirmed by two
  attempts); assessment made from source as instructed.

**Conclusion:** not a standard citable theorem. Routine functoriality glue specific to this
formalization's universal-curve design.

---

## 3. Mathlib search (five methods)

Searched the repo-pinned mathlib (`.lake/packages/mathlib`), the relevant fork targets, and by name.

- **By name / framework (grep).** `ringEval`, `smulEval`, `smulRing`, `polyEval`,
  `zsmul_eq_smulEval`, and the `AdjoinRoot`-quotient `Universal.Ring` specialization apparatus
  appear **nowhere** in mathlib. The only hit for these tokens is the *docstring* of
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` (L36), which uses the
  phrase "universal ring" to mean the **base-change** construction `ℤ[A₁..A₆][X,Y] → R[X,Y]`, a
  different object from this project's `AdjoinRoot` coordinate-ring quotient.
- **Closest mathlib API (the real naturality lemmas).** `DivisionPolynomial/Basic.lean` provides
  only **coefficientwise** naturality:
  - `WeierstrassCurve.map_ψ (n : ℤ) : (W.map f).ψ n = (W.ψ n).map (mapRingHom f)` (L536)
  - and the `baseChange_ψ` variant (L580), plus the `φ/ω/Ψ/Φ` analogues.
  These commute `ψ` with a ring hom `f : R →+* S` applied to **coefficients** of the bivariate
  polynomial. They are genuinely *different* from `ringEval_ψ`, which evaluates the *universal*
  `ψ` through a quotient-ring specialization down to a *scalar* in `R`.
- **`CoordinateRing`.** Exists in mathlib (`Affine/Point.lean`, `DivisionPolynomial/Basic.lean`);
  the project reuses it (`Universal.Ring := curve.CoordinateRing`). But no specialization
  `ringEval`-style lift, and no division-polynomial-in-the-coordinate-ring API, exists upstream.
- **n-torsion / `n • P` via division polynomials.** No mathlib result expresses `n • P` in
  Jacobian/affine coordinates via `(φₙ, ωₙ, ψₙ)`. The whole `smulEval`/`zsmul_eq_smulEval`
  development (the reason `ringEval_ψ` exists) is **absent** from mathlib.
- **leansearch/loogle:** the live mathlib-index MCP tools are not exposed here and LSP needs a
  fresh build (stale); however the on-disk grep over the pinned mathlib is decisive for
  these project-private identifiers.

**Conclusion:** mathlib has the coefficientwise naturality (`map_ψ`/`baseChange_ψ`) but **not**
`ringEval_ψ` nor the universal-ring specialization framework it lives in.

---

## 4. Generality analysis

The statement is already at a reasonable generality (`W` over any `CommRing R`, any `n : ℤ`,
any point satisfying `Equation`). There is nothing to weaken: the constraint is not the
hypotheses but the **vocabulary** — `ringEval`, `Universal.Ring`, `curve.ψ`, `smulRing` are all
project-defined. The lemma cannot be stated in mathlib as-is because none of its constituent
objects exist there. So "generalise first" does not apply; the gating question is purely whether
the underlying *framework* should be upstreamed.

---

## 5. Composition check (≤3 mathlib calls?)

Two layers:

1. **Within the project**, once `ringEval_comp_smulRing` exists, `ringEval_ψ` is exactly
   `congr_fun (ringEval_comp_smulRing eqn n) 2` — a **single** function-projection step. It carries
   no independent mathematical content; it is a packaging convenience (extract the `ψ` slot from a
   triple). This alone makes it a non-candidate as a *standalone* mathlib lemma: it is trivially
   composable from its parent.

2. **From mathlib's primitives**, the lemma is *not* directly composable, because the parent
   `ringEval` / `smulRing` / `Universal.Ring` machinery is not in mathlib. But that cuts the other
   way: it means the lemma is **inseparable from a bespoke framework**, not that it is a missing
   primitive. If that framework (`Universal.Ring` + `ringEval` specialization + `smulEval` +
   `zsmul_eq_smulEval`) were ever upstreamed, this one-liner would be an internal step that would
   most plausibly be **inlined** or kept only as the packaged `ringEval_comp_smulRing`, not added
   as its own public API.

**Conclusion:** trivially composable from its own parent (≤1 call); and the parent rests on a
project-private construction, so there is no mathlib-primitive route either.

---

## 6. Verdict

**NO-composable-from-mathlib.**

`WeierstrassCurve.ringEval_ψ` is internal naturality glue: a one-line `congr_fun … 2` projection of
`ringEval_comp_smulRing`, whose only purpose is to feed the `zsmul_eq_smulEval` proof. It is not a
named/citable result; it is the routine "division polynomials specialize from the universal curve"
functoriality fact, expressed entirely in the project's own `Universal.Ring` / `ringEval` /
`smulRing` vocabulary — none of which is in mathlib (mathlib offers only the *different*,
coefficientwise `map_ψ` / `baseChange_ψ`). On its own it is a ≤1-step composition of an existing
lemma and therefore not worth adding as standalone API; and because it depends on a bespoke
specialization framework absent upstream, it is also not a mathlib primitive in disguise. It should
travel — if ever — only as part of upstreaming the whole universal-curve `ringEval`/`smulEval`
apparatus (the genuinely interesting, mathlib-worthy unit there is the headline
`zsmul_eq_smulEval`, assessed separately), and even then this exact one-liner would likely be
inlined.

### Notes for the consolidation pass
- **Verbatim duplicate** in this same monorepo:
  `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:638-640` (identical statement and
  identical `congr_fun (ringEval_comp_smulRing eqn n) 2` proof; the whole `Universal`/`ringEval`
  framework is copied into `HasseWeil/Auxiliary/Universal.lean`). This is a clear cross-project
  **dedup** target for a cleanup ticket — both forks should share one `Common/` copy rather than
  each re-deriving the universal-curve machinery.
