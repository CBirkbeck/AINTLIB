# Mathlibable assessment: `smulPoly_zero`

- **Qualified name:** `WeierstrassCurve.Universal.Jacobian.smulPoly_zero`
- **Location:** `projects/NagellLutz/LutzNagell/ZSMul.lean:496`
- **Verdict bucket:** `BORDERLINE-needs-human`
- **Date:** 2026-06-22

## Exact statement and proof (from source)

```lean
namespace WeierstrassCurve
namespace Universal            -- variables fix a Weierstrass curve W over R; `curve` is the
namespace Jacobian             -- universal curve, `Poly` the universal bivariate poly ring

/-- The three families of universal division polynomials as a 3-tuple. -/
abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, curve.ω n, curve.ψ n]

lemma smulPoly_zero : smulPoly 0 = ![1, 1, 0] := by simp [smulPoly]
```

So the parsed/verified qualified name is `WeierstrassCurve.Universal.Jacobian.smulPoly_zero`
(namespaces `WeierstrassCurve` → `Universal` → `Jacobian`; opened at lines 76 / 86 / 395). The
prompt's guessed name is correct.

Mathematically the lemma says: the Jacobian-coordinate triple of division polynomials
`(φₙ, ωₙ, ψₙ)` at `n = 0` is the point at infinity `(1 : 1 : 0)`. The proof is a one-line `simp`
that unfolds the local abbreviation `smulPoly` and rewrites the three `@[simp]` component lemmas
`φ_zero : φ 0 = 1`, `ω_zero : ω 0 = 1`, `ψ_zero : ψ 0 = 0` into the literal vector `![1, 1, 0]`.

## Step 1 — Literature search

- Standard reference fact: for an elliptic curve, `[n]P = (φₙ(x,y)/ψₙ²,  ωₙ(x,y)/ψₙ³)`, where
  `ψ, φ, ω` are the three division-polynomial families and `ω` is the "y-coordinate" polynomial
  (Silverman, *Arithmetic of Elliptic Curves*, Exercise 3.7; Washington, *Elliptic Curves*
  §3.2). In projective/Jacobian coordinates `[n]P = (φₙ : ωₙ : ψₙ)`, and at `n = 0` this is the
  identity `(1 : 1 : 0)` because `φ₀ = 1, ω₀ = 1, ψ₀ = 0`.
- WebSearch ("mathlib elliptic curve division polynomial omega n smul Jacobian … Junyan Xu")
  surfaced only mathlib's `DivisionPolynomial.Basic` docs (which define `φ` and `ψ` but **not**
  the `n • P` formula and **not** `ω`), the arXiv note "Division polynomials in Mumford
  coordinates" (2412.10284), and general EC references. No source treats this particular
  zero-index triple identity as a named result — it is universally a trivial base case inside the
  multiplication-by-`n` formula, never a standalone theorem.

Conclusion: `smulPoly_zero` is not a named theorem in the literature; it is boilerplate inside the
`[n]P` division-polynomial formula. Its mathlib status is therefore entirely **derivative** of
whether that parent formula (and the `ω` family + the `smulPoly` packaging) is upstreamed.

## Step 2 — Mathlib search (five methods)

Searched the pinned mathlib tree at
`.lake/packages/mathlib/` (commit per `lakefile.toml`).

1. **Name/grep** — `grep -rn "smulPoly|smulEval|smulRing|smulField"` over
   `Mathlib/AlgebraicGeometry/EllipticCurve/` and all of `Mathlib/`: **no hits**. The whole
   `smul`-via-division-polynomial layer is project-local (introduced in this `ZSMul.lean`, the
   Junyan Xu development).
2. **The `n • P` formula** — `grep` for `smul_eq_divisionPolynomial`, `zsmul_eq_smulEval`,
   `divisionPolynomial.*smul`: **no hits**. Mathlib does **not** yet have the multiplication-by-`n`
   formula in terms of division polynomials.
3. **The `ω` division polynomial** — mathlib's `DivisionPolynomial/Basic.lean` defines
   `Ψ, ψ, preΨ, φ` and proves `ψ_zero` (line 407) and `φ_zero` (line 454), but there is **no**
   division-polynomial `ω`. A repo-wide `grep` for a `def ω` in `Mathlib/` finds only unrelated
   objects (`ωSup`, Lucas–Lehmer `ω`, category-theory `ω₁/ω₂`, root-system `ω`). The project
   supplies `ω` itself in `DivisionPolynomialOmega.lean` (`ω_zero` at line 95). So the *vocabulary*
   of `smulPoly_zero` (the symbol `ω`, hence `smulPoly`) does not exist in mathlib.
4. **Component zero-lemmas** — mathlib **has** `WeierstrassCurve.ψ_zero` and
   `WeierstrassCurve.φ_zero` (both `@[simp]`), but **lacks** `ω_zero` (no `ω`). The project fork
   re-declares `ψ_zero`/`φ_zero` (`DivisionPolynomial.lean:330,377`) plus the new `ω_zero`.
5. **Index search** — leansearch/loogle index (mathlib) returns the `ψ`/`φ`/`Ψ` division-polynomial
   API but nothing for an `![φ, ω, ψ]` Jacobian triple or its zero value, consistent with 1–4.

Conclusion: mathlib does **not** contain `smulPoly_zero`, cannot even state it (no `ω`, no
`smulPoly`), and does not contain the parent `n • P` formula.

## Step 3 — Generality analysis

The statement is already at full generality *within its own layer*: it holds over the universal
ring `Poly` for the universal curve, so it specialises to every Weierstrass curve over every
commutative ring by a ring map (this is exactly why the file works universally). There is nothing
to weaken — it is a closed-form evaluation at a fixed index. The only "generalisation" question is
the packaging choice: should the triple `(φₙ, ωₙ, ψₙ)` be a named def (`smulPoly`) at all, or
inlined? That is a mathlib-API design decision, not a logical-strength one.

## Step 4 — Composition check (≤ 3 mathlib calls?)

Mathematically `smulPoly 0 = ![φ 0, ω 0, ψ 0] = ![1, 1, 0]` is `[φ_zero, ω_zero, ψ_zero]` packed
into a `Fin 3 →` vector — a one-`simp` glue lemma. **But the statement names `smulPoly`, a symbol
mathlib does not have**, and `ω 0 = 1` likewise needs the project's `ω` (absent upstream). So you
cannot compose existing *mathlib* primitives to even write the goal, let alone prove it. The
"composable" verdict only applies to statements expressible in mathlib's current vocabulary; this
one is not. Hence not `NO-composable-from-mathlib`.

## Step 5 — Five-bucket verdict

- Not `NO-mathlib-has-it`: mathlib has neither the lemma nor its vocabulary (`ω`, `smulPoly`).
- Not `NO-composable-from-mathlib`: the goal references `smulPoly`/`ω`, which mathlib lacks, so no
  short composition of mathlib lemmas reproduces it today.
- Not `YES-add-as-is`: as a standalone lemma it has no home — it is a base-case glue lemma for the
  local `smulPoly` abbreviation. It only makes sense in mathlib bundled with the parent development.
- Not `YES-but-generalise-first`: there is no assumption to weaken; the open question is packaging,
  not generality.

**`BORDERLINE-needs-human`.** This lemma is trivially mathlib-quality **conditional on** upstreaming
the project's missing prerequisites: the division-polynomial `ω` family (genuinely mathlib-worthy —
it completes mathlib's existing `ψ`/`φ`/`Ψ` story and the standard `[n]P = (φ/ψ², ω/ψ³)` formula)
and the `smulPoly`/`smulEval` Jacobian-coordinate layer (the Junyan Xu `zsmul_eq_smulEval`
development). Whether to upstream that `smulPoly` packaging at all — and if so whether
`smulPoly_zero` survives as a named `@[simp]` boundary lemma or is inlined into the base case of the
`n • P` proof — is a mathlib-maintainer design call. A human should decide the parent-API question;
`smulPoly_zero` then rides along with it.

### Recommendation to a human reviewer
1. Decide on upstreaming `WeierstrassCurve.ω` (division-polynomial omega) + the `n • P` division-
   polynomial formula. This is the real mathlib target; `smulPoly_zero` is incidental to it.
2. If the `smulPoly := ![φ, ω, ψ]` abbreviation is adopted upstream, add `smulPoly_zero` (and its
   siblings `smulPoly_neg`, `smulField_zero`, …) as `@[simp]` glue, likely marking it `@[simp]`.
3. If instead the base case is inlined, `smulPoly_zero` does not need to exist separately.
