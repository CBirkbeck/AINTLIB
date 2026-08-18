# Mathlibable assessment — `WeierstrassCurve.Universal.Affine.smulY_neg`

**Verdict: BORDERLINE-needs-human**

> The lemma is a correct, textbook fact, but it is stated entirely in *project-defined*
> vocabulary (`smulX`, `smulY`, `ω`, `pointedCurve`, `Universal.Field`) that does **not**
> exist in mathlib. It is an internal stepping-stone in an in-progress upstream development
> (Junyan Xu's affine multiplication-by-`n` formula). Whether this specific helper should be a
> public mathlib lemma is a packaging decision tied to how/whether the whole `Universal.Affine`
> framework lands — a maintainer call.

---

## 0. The declaration (verified from source)

- **File:** `projects/NagellLutz/LutzNagell/ZSMul.lean:290`
- **Parsed name confirmed.** Namespaces: `WeierstrassCurve` (L76) → `Universal` (L86) →
  `Affine` (L157). So the true qualified name is exactly
  **`WeierstrassCurve.Universal.Affine.smulY_neg`**.

```lean
lemma smulY_neg (h0 : n ≠ 0) :
    smulY (-n) = pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  simp only [Affine.negY, smulX, smulY, ψ_neg, ω_neg, map_add, map_neg, map_mul, map_pow, ψᵤ]
  exact smulY_neg_aux (ψᵤ_ne_zero h0)
```

with the private field-arithmetic core

```lean
private lemma smulY_neg_aux {F} [Field F] {a₁ a₃ x y z : F} (hz : z ≠ 0) :
    (y + a₁ * x * z + a₃ * z ^ 3) / (-z) ^ 3 = -(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃ := by
  rw [neg_pow]; field_simp; ring
```

### What it says, mathematically
On the **universal** Weierstrass curve, the affine coordinates of `n • (X,Y)` are the rational
functions `smulX n = φₙ/ψₙ²` and `smulY n = ωₙ/ψₙ³` (defs at `ZSMul.lean:164,168`). The lemma is
the **negation-of-multiplier** identity:

  the `Y`-coordinate of `(-n) • P` equals `negY` applied to the coordinates of `n • P`.

It is the `Y`-analogue of the already-proved `smulX_neg` (`ZSMul.lean:201`,
`smulX (-n) = smulX n`). Together they say `(-n) • P = -(n • P)` *at the level of the
division-polynomial coordinate formulas*. The proof is pure bookkeeping: feed the oddness/evenness
lemmas `ψ_neg` (ψ odd), `φ_neg` (φ even) and the project's `ω_neg`
(`ωₙ(-) = ωₙ + a₁·φₙ·ψₙ + a₃·ψₙ³`) into one `field_simp; ring`.

---

## 1. Literature search

| # | Tool / source | Query angle | Hit? | Finding |
|---|---|---|---|---|
| 1 | WebSearch | "smulX smulY Junyan Xu zsmul division polynomial" | partial | confirms the standard formula `[n]P = (φ/ψ², ω/ψ³)`; mathlib's **Projective/Jacobian** `Formula` has the *homogeneous* `nP = (Φₙ Ψₙ : Ωₙ : Ψₙ³)` machinery — a **separate** proof effort, not the affine `smulX/smulY` framework here. |
| 2 | WebSearch | negation, `Y`-coord, ω, `-n • P` | yes | Wikipedia *Division polynomials*, Stanford/MIT (Sutherland L6) notes, arXiv:2102.07573: `[n]P=(φ/ψ², ω/ψ³)`; negation `(x,y) ↦ (x, negY)` is standard; `ω` defined `ωₙ = (ψₙ₊₂ψₙ₋₁² − ψₙ₋₂ψₙ₊₁²)/(4v)`. The content is **textbook**. |
| 3 | Local sibling reports | `.mathlib-quality/overview/mathlibable/` (`addMulSub_neg₀.md`, `addMulSub_neg₁.md`) | yes | Same project, same pattern, prior conclusion: *"mathlib proves negation lemmas but for its own sequences (`preNormEDS_neg`, `normEDS_neg`)"*; these per-object negation helpers are **"formalisation-internal."** Directly analogous. |

**Provenance.** Headers attribute `ZSMul.lean`, `Universal.lean`, `DivisionPolynomialOmega.lean`
to **Junyan Xu** (and D. K. Angdinata for the ω file) — this is the upstream
multiplication-by-`n` / `zsmul_eq_smulEval` development being grown in the fork. The *framework*
is genuinely destined for mathlib; this lemma is a leaf inside it.

**Conclusion:** the mathematical statement (`(-n)•P` has `Y` = `negY` of `n•P`) is well-known and
unnamed — nobody gives this trivial symmetry a citable name; it is glue.

---

## 2. Mathlib search — is it there, or a more general form?

Five methods over the pinned mathlib (`.lake/packages/mathlib`):

1. **Name grep.** No `smulX` / `smulY` / `smulEval` / `smulField` / `zsmul_eq_smulEval` anywhere in
   mathlib. The *entire* "affine coordinates of `n • P` via division polynomials" framework is
   **absent** upstream.
2. **`ω` (omega) division polynomial.** mathlib's `DivisionPolynomial/Basic.lean` defines `ψ`, `φ`
   only — **no `ω`/`Ω`**. The project defines `WeierstrassCurve.ω` itself
   (`DivisionPolynomialOmega.lean:74`, via `compl₂EDS`). So even the object in the conclusion
   (`smulY = ω/ψ³`) cannot be named in mathlib.
3. **`negY`.** Present (`Affine/Formula.lean:113` `def negY`; also Jacobian/Projective variants),
   but it is just the curve's point-negation `Y`-map. mathlib's `negY_smul`
   (`Jacobian/Formula.lean:95`: `negY (u•P) = u³·negY P`) is about **coordinate scaling** of a
   single representative — unrelated to integer `n`-multiples.
4. **Negation-of-`n`-multiple coordinate lemma.** No mathlib lemma relates the coordinates of
   `n • P` and `(-n) • P` via the affine division-polynomial formulas (because those formulas are
   not in mathlib).
5. **Closest mathlib analogues** (`ψ_neg`, `φ_neg`, `normEDS_neg`, `preNormEDS_neg`): these are the
   *ingredients*, all present in mathlib **and forked here**. But the *combination* into a statement
   about `smulX`/`smulY` is project-only.

**Conclusion:** mathlib does **not** contain `smulY_neg` nor any generalisation of it. Rules out
`NO-mathlib-has-it`.

---

## 3. Generality analysis

- The lemma is stated on the **universal curve** over `ℤ[A₁..A₆,X,Y]/⟨P⟩` (`Universal.Field`),
  which is the maximally-general base for division-polynomial identities — every other curve is a
  ring-hom specialisation. This is the *correct* generality for its role; there is no weaker
  hypothesis or broader base to move to. The single side condition `n ≠ 0` is forced
  (`ψₙ` must be invertible to divide).
- It is the textbook-standard statement of "`Y`-coordinate of `-n•P`", already at the right level.
  So there is nothing to *generalise first* → rules out `YES-but-generalise-first`.

---

## 4. Composition check (≤ 3 mathlib calls?)

**No — and not even one.** To compose this from mathlib primitives you must first *name* `smulY`,
`smulX`, `pointedCurve`, `Universal.Field`, and the `ω` division polynomial — **none of which exist
in mathlib**. The proof here is not a composition of mathlib lemmas about a mathlib object; it is a
`field_simp; ring` over project-defined rational functions, fed by `ψ_neg`/`φ_neg`/`ω_neg`. Since the
*statement itself* is unexpressible in mathlib's current vocabulary, the composition bucket
(`NO-composable-from-mathlib`) does not apply.

---

## 5. Why BORDERLINE (not the other four buckets)

- **NOT `NO-mathlib-has-it`** — §2: no `smulX/smulY/ω` framework, no equivalent lemma upstream.
- **NOT `NO-composable-from-mathlib`** — §4: the objects don't exist in mathlib, so there is nothing
  to compose; this is new infrastructure, not a corollary.
- **NOT `YES-add-as-is`** — it is not a standalone, independently-reusable result. It is a private
  leaf (with a `private … aux`) inside the `Universal.Affine` scaffolding, whose only consumer is the
  even/strong induction proving `zsmul_point_eq_smulX_smulY`. mathlib would never accept `smulY_neg`
  *alone*; it only makes sense bundled with the whole multiplication-by-`n` development.
- **NOT `YES-but-generalise-first`** — §3: already at universal-curve generality; no weakening
  available or wanted. The "issue" is packaging, not generality.
- **→ `BORDERLINE-needs-human`** — The *enclosing framework* (`n • P = (φ/ψ², ω/ψ³)` in affine
  coordinates, `zsmul_eq_smulEval`) is genuinely mathlib-grade and is exactly the kind of thing being
  upstreamed (Junyan Xu authorship). Whether **this specific helper** should surface as a public
  mathlib lemma, stay `private`, or be absorbed into a larger negation result is a decision that can
  only be made *in the context of how the whole `Universal.Affine` API is structured for mathlib* —
  i.e. a maintainer/human call, which is precisely what this bucket is for. The prior sibling reports
  in this directory reached the same "formalisation-internal" reading for the analogous
  `addMulSub_neg₀/₁` helpers.

---

## Recommendation

Carry `smulY_neg` along with the rest of the affine multiplication-by-`n` framework when/if that
framework is proposed for mathlib (it is the natural `Y`-companion to `smulX_neg`). On its own it is
an internal step, not a PR-worthy standalone lemma. No action needed in the fork — it is correctly
placed as a building block here.

### Sources
- [Division polynomials — Wikipedia](https://en.wikipedia.org/wiki/Division_polynomials)
- [Elliptic curve point multiplication — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication)
- [Sutherland, 18.783 Elliptic Curves, Lecture 6 (MIT)](https://math.mit.edu/classes/18.783/2015/LectureNotes6.pdf)
- [Stanford — Elliptic Curves: Explicit Addition Formulae](https://crypto.stanford.edu/pbc/notes/elliptic/explicit.html)
- [A recurrence relation for elliptic divisibility sequences (arXiv:2102.07573)](https://arxiv.org/pdf/2102.07573)
- [Mathlib Projective.Formula docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.html)
- Pinned mathlib sources: `Mathlib/AlgebraicGeometry/EllipticCurve/{Affine,Jacobian,Projective}/Formula.lean`, `DivisionPolynomial/Basic.lean`, `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (verified locally — no `smulX/smulY/ω`).
