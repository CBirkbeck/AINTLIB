# Mathlibable assessment — `WeierstrassCurve.Universal.Affine.smulY_zero`

**Verdict: NO-composable-from-mathlib**

One-line rationale: `simp`-true boundary case (`div_zero` after `normEDS_zero`) of a **project-local** definition `smulY` that does not exist in mathlib.

---

## 1. Declaration under review

Source: `projects/NagellLutz/LutzNagell/ZSMul.lean:172`

```lean
namespace WeierstrassCurve  -- (then) Universal  -- (then) Affine
...
def smulY : Universal.Field := polyToField (curve.ω n) / (ψᵤ n) ^ 3   -- line 168
...
@[simp] lemma smulY_zero : smulY 0 = 0 := by simp [smulY, ψᵤ]          -- line 172
```

**Verified qualified name:** `WeierstrassCurve.Universal.Affine.smulY_zero`
(namespace nesting confirmed: `WeierstrassCurve` (L76) → `Universal` (L86) → `Affine` (L157); the
declaration at L172 sits inside all three; `end Affine` is at L393.)

**Statement (unfolded).** `smulY n` is the rational function `ωₙ / ψₙ³` in the *universal field*
`Frac(ℤ[A₁,…,A₆,X,Y]/⟨P⟩)`, the conjectured affine `Y`-coordinate of `n • (X,Y)` on the universal
Weierstrass curve (docstring L166–167). The lemma asserts the `n = 0` value is `0`.

**Why it is true (junk-value boundary case).**
- `curve.ω 0 = 1` (mathlib-fork `DivisionPolynomialOmega.lean:95`, `ω_zero`), so the numerator
  `polyToField (curve.ω 0) = polyToField 1 = 1 ≠ 0`.
- `ψᵤ 0 = polyToField (curve.ψ 0) = normEDS … 0 = 0` (mathlib's `normEDS_zero`,
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:298`).
- Hence `smulY 0 = 1 / 0³ = 1 / 0 = 0` by the field junk-value convention `div_zero`.

So the proof is morally `simp only [smulY, ψᵤ, ψ_zero/normEDS_zero, div_zero]` — a single
composition step. It is **not** a theorem with mathematical content; it is the `n = 0` normalization
of a definition, marked `@[simp]`, and the project inventory records it as "unused in file"
(`.mathlib-quality/overview/inventory/LutzNagell_ZSMul.md`, `### lemma Affine.smulY_zero`, "Used by:
unused in file").

---

## 2. Literature search

The multiplication-by-`n` formula `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)` is completely standard:
- Sutherland, MIT 18.783 *Elliptic Curves*, Lecture 6 (Isogeny kernels and division polynomials):
  `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`, with `φₙ = x ψₙ² − ψₙ₋₁ ψₙ₊₁` and `4y ωₙ = ψₙ₋₁² ψₙ₊₂ − ψₙ₋₂ ψₙ₊₁²`.
- Silverman, *The Arithmetic of Elliptic Curves*, Exercise 3.7 (division polynomials).
- Stange, "Elliptic nets" / "Sequences associated to elliptic curves" (arXiv:1909.12654) — the EDS
  viewpoint underlying `normEDS`.

None of these references states, or has any reason to state, the degenerate `n = 0` value of the
`Y`-coordinate rational function: it is purely a formalization artefact of working with a total
`div` (junk value at the zero denominator). There is **no literature-standard "theorem"** here to
generalise toward — the literature object is the *family* `smulY`, not its zero case.

WebSearch corroboration: results returned the standard `(φₙ/ψₙ², ωₙ/ψₙ³)` formula and EDS papers,
with no independent statement of the `n = 0` boundary.

---

## 3. Mathlib search (five methods)

Target object: the universal-field `smul`-coordinate `smulY` and its `n = 0` value.

1. **Name guess** — no `smulY` / `smulX` / `smulField` / `smulRing` / `zsmul_point` anywhere in
   mathlib (`grep -rn` over `Mathlib/AlgebraicGeometry/EllipticCurve/` returns nothing).
2. **Namespace sweep** — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` contains only
   `Basic.lean` and `Degree.lean`. They define `ψ`, `φ`, `ψ₂`, `Ψ₃`, `preΨ₄`, `ω` (via `normEDS`)
   and their degrees, but **no** universal ring/field, no `polyToField`, and **no** multiplication
   formula / affine `smul`-coordinate. The whole `Universal.*` apparatus (`Universal.Field`,
   `polyToField`, `ψᵤ`, `smulX`, `smulY`, `zsmul_point_eq_smulX_smulY`) is project-original.
3. **`normEDS` neighbourhood** — mathlib *does* have the relevant primitive
   `normEDS_zero : normEDS b c d 0 = 0` (`EllipticDivisibilitySequence.lean:298`) and
   `div_zero`/`zero_div` — these are precisely the two facts the proof composes.
4. **loogle/leansearch (mathlib index)** — no hit for a lemma of shape
   `(polyToField (ω 0)) / (ψ 0)^3 = 0` or any `smulY`-named result; `smulY` is not an indexed
   mathlib identifier.
5. **Consumer search** — mathlib's elliptic-curve scalar multiplication lives on `W.Point`
   (`Affine/Point.lean`, `Jacobian/Point.lean`) as the abstract group operation; it is **not**
   expressed through division-polynomial rational functions at all, so there is no mathlib lemma
   that this could be a special case of.

Conclusion of search: mathlib has neither the definition `smulY` nor any equivalent of
`smulY_zero`. It *does* have every primitive the proof needs.

---

## 4. Generality analysis

The lemma is already at the only generality it can have: it is a single concrete value
(`n = 0`) of a fixed definition over the fixed universal field. There is no ambient type variable to
weaken (the universal field is canonical) and no hypothesis to drop. So "generalise first" is not
applicable.

The broader, genuinely-mathlibable object is the **package**: the universal division-polynomial
multiplication formula `Universal.Affine.zsmul_point_eq_smulX_smulY` and its supporting `smulX` /
`smulY` API, of which `smulY_zero` is one internal `@[simp]` boundary lemma. That package as a whole
is a plausible future mathlib contribution (it is exactly Sutherland/Silverman's formula). But an
individual zero-case `simp` lemma is not an independent contribution — it would only ever land
*alongside* the `smulY` definition, never on its own.

---

## 5. Composition check (≤ 3 mathlib calls)

Given the definition `smulY n = polyToField (curve.ω n) / (ψᵤ n) ^ 3`, the lemma is obtained by:

1. unfold `smulY`, `ψᵤ`;
2. `normEDS_zero` (mathlib) ⟹ `ψᵤ 0 = 0`, hence `(ψᵤ 0)^3 = 0` (`zero_pow`/`pow_eq_zero`);
3. `div_zero` (mathlib) ⟹ `_ / 0 = 0`.

That is ≤ 3 mathlib lemmas after one definitional unfold — which is exactly why the project proof is
the single tactic `by simp [smulY, ψᵤ]`. **Composable from mathlib primitives.**

---

## 6. Verdict

**NO-composable-from-mathlib.**

- It is not in mathlib (Method-1/2/4) — but only because the *definition* `smulY` it refers to is
  project-local, so it *cannot* be in mathlib in this form (this is the reason it is not
  `NO-mathlib-has-it`).
- It is a `simp`-true junk-value boundary lemma: `div_zero ∘ normEDS_zero`, a ≤ 3-call composition
  over mathlib primitives (§5). No mathematical content beyond the definition unfold.
- It is an internal `@[simp]` normalization step (inventory: "unused in file") for the genuinely
  interesting result `zsmul_point_eq_smulX_smulY`. If/when that whole `smulX`/`smulY` package is
  upstreamed, `smulY_zero` rides along as a private/auxiliary `simp` lemma — it is never an
  independent target.

If a reviewer is instead assessing the **whole universal multiplication-formula package** (not this
single lemma), that package would be a `YES-but-generalise-first` candidate (state it for an
arbitrary base curve, deduplicate against the identical copy in
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean`). That is an orthogonal,
human-scoped decision and does not change this single declaration's verdict.

---

### Appendix — cross-project duplication note
An identical `smulY` / `smulY_zero` pair exists at
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:243,247`. This is the expected
General/PID-track fork noted in the project context; it reinforces that the right unit of any
upstreaming decision is the whole package (dedup the two copies first), not this lemma.
