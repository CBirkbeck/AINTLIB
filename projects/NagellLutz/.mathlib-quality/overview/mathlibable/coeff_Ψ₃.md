# /mathlibable report — `WeierstrassCurve.coeff_Ψ₃`

**Verdict: NO-mathlib-has-it** (verbatim duplicate — this declaration is already in mathlib, identical in every respect).

---

## Baseline (Phase 0)

- lake build: not run (local build stale per task brief); reasoning from source + vendored mathlib tree.
- decl `WeierstrassCurve.coeff_Ψ₃`: resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:96` (the `@[simp] lemma` head is line 96; body line 100 = mathlib's line numbering offset).
- kind: `lemma` (theorem-like; carries `@[simp]`).
- has sorry: no.
- module docstring summary: "Division polynomials of Weierstrass curves … a project copy of mathlib's Basic file" — the file header (line 14) and the imported `DivisionPolynomial.lean` header both state it is **a verbatim copy of mathlib**, forked only to swap in the project's own `EllipticDivisibilitySequence` (to avoid `normEDS`/`complEDS` name clashes).

Qualified name (VERIFIED from source): **`WeierstrassCurve.coeff_Ψ₃`**. The enclosing `namespace WeierstrassCurve` (file line 55) + bare name `coeff_Ψ₃` (file line 96) confirm it. Matches the parsed name in the task brief.

---

## Statement (Phase 1)

`WeierstrassCurve.coeff_Ψ₃` states: for a Weierstrass curve `W` over a commutative ring `R`, the coefficient of `X⁴` in the 3-division polynomial `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` is `3`.

- Parameters: `{R : Type u} [CommRing R]`, `(W : WeierstrassCurve R)`.
- Hypotheses: none.
- Conclusion (math): `[X⁴] Ψ₃ = 3`.
- Conclusion (Lean): `W.Ψ₃.coeff 4 = 3`.

Proof: `rw [Ψ₃]; compute_degree!` — unfold the definition, let the `compute_degree!` tactic read off the coefficient.

This is one rung of the standard degree/leading-coefficient ladder for division polynomials (`natDegree_Ψ₃_le` → `coeff_Ψ₃` → `coeff_Ψ₃_ne_zero` → `natDegree_Ψ₃` → `leadingCoeff_Ψ₃` → `Ψ₃_ne_zero`), all present identically in both trees.

---

## Size classification (Phase 2a)

Verdict: SMALL. A single coefficient-extraction helper lemma for one concrete polynomial; not a named theorem, not a new structure, not a project main result.

## One-line check (Phase 2b)

n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`. No one-liner-definition concern.

---

## Phases 3–4 — Literature / generality (SHORT-CIRCUITED, justified)

The skill's literature and generality phases exist to answer "*should* mathlib have this, and in what form?". That question is **already answered**: mathlib has this exact lemma, about this exact definition, with this exact proof. There is no open generality question — the project's `Ψ₃` is **byte-identical** to mathlib's `Ψ₃` (both `3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈`, over the same `[CommRing R]`), so the only "literature standard" form is the one mathlib already ships. For completeness:

- Concept: leading coefficient of the 3-division polynomial of an elliptic/Weierstrass curve. Standard reference: J. Silverman, *The Arithmetic of Elliptic Curves*, Exercise 3.7 / §III.3 (cited in the file's own `## References`). The degree-4, leading-coefficient-3 fact for `ψ₃` is textbook.
- Generality: `[CommRing R]` with no further hypotheses is already the maximal generality for a pure coefficient identity (the statement is a polynomial identity in the `bᵢ`; no domain/characteristic assumption is needed or possible to weaken). mathlib's form is identical, hence maximally general. No modern-idiom restatement applies (it is a concrete coefficient identity — nothing to filter-ise, classify, or typeclass-ify).

No literature-driven improvement is available because the target already exists upstream in its final form.

## Phase 4.5 — Diamond/defeq risk

n/a — declaration kind is `lemma` (proof-irrelevant; introduces no definitional equality or instance path).

---

## Mathlib search-status (Phase 5)

Five-method search collapsed to a direct hit (the vendored mathlib tree is on disk at `.lake/packages/mathlib`):

- [D] Grep mathlib src — `grep -rn "coeff_Ψ₃" .lake/packages/mathlib/Mathlib/` → **HIT**: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:100`.
- [E] Name pattern / namespace — `namespace WeierstrassCurve` at `Degree.lean:59`; bare `coeff_Ψ₃` at line 100 ⇒ qualified `WeierstrassCurve.coeff_Ψ₃`. Exact namespace + name agreement.
- [A] Lean-Finder / [B] Loogle / [C] LeanSearch — not needed; an exact-source grep hit on the identical qualified name is conclusive. (Loogle pattern `?W.Ψ₃.coeff 4 = 3` would resolve to the same decl.)

Side-by-side (mathlib `Degree.lean:99-102` vs. project `DivisionPolynomialDegree.lean:95-98`):

```lean
@[simp]
lemma coeff_Ψ₃ : W.Ψ₃.coeff 4 = 3 := by
  rw [Ψ₃]
  compute_degree!
```

Identical: `@[simp]` attribute, name, signature, variable context (`{R : Type u} [CommRing R] (W : WeierstrassCurve R)`, declared identically at line 61/57 of each file), proof term, and the `Ψ₃` definition it unfolds. The project file even carries mathlib's original copyright header ("Copyright (c) 2024 David Kurniadi Angdinata").

**Concluded: found in mathlib as `WeierstrassCurve.coeff_Ψ₃`; identical form** (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:100`).

---

## Call sites (Phase 6.0)

Internal use count (excluding the declaring file): **0**.
External-to-file callers: **0 distinct files**.

`grep -rn "coeff_Ψ₃" projects/NagellLutz --include=*.lean | grep -v DivisionPolynomialDegree.lean` returns nothing. The lemma is used only within its own file's ladder (`coeff_Ψ₃_ne_zero`, `leadingCoeff_Ψ₃` reference it locally), exactly as in mathlib.

Inline-derivation grep: none — no other site re-derives the coefficient.

Interpretation: K = 0 external uses is expected and not a defect signal here — the whole file is a wholesale verbatim fork of mathlib's `Degree.lean`, dragged in to namespace the project's alternative `EllipticDivisibilitySequence`. The downstream consumers (`GeneralIntegralMultiple.lean`, `PIDPrimeOrder.lean`, etc., which `import LutzNagell.DivisionPolynomialDegree`) consume the *ladder's top results* (e.g. `natDegree_Ψ₃`, `leadingCoeff_Ψ₃`), not `coeff_Ψ₃` directly — and every one of those is likewise already in mathlib.

## Composition check (Phase 6)

Can `WeierstrassCurve.coeff_Ψ₃` be derived from mathlib in ≤1 line? Trivially — it **is** the mathlib lemma:

```lean
example {R : Type u} [CommRing R] (W : WeierstrassCurve R) : W.Ψ₃.coeff 4 = 3 :=
  W.coeff_Ψ₃            -- the mathlib lemma, once the project imports it instead of forking
```

Conclusion: redundant with an identical upstream decl (a degenerate NO-mathlib-has-it, stronger than COMPOSABLE).

---

## Verdict: `WeierstrassCurve.coeff_Ψ₃`

**Category: NO-mathlib-has-it**

**Evidence:**
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.coeff_Ψ₃`, `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:100` — identical statement, proof, `@[simp]` attribute, and variable context.
- The definition it concerns (`WeierstrassCurve.Ψ₃`) is byte-identical between the project fork and mathlib.
- Generality (Phases 3–4): no open question — mathlib's form is already maximal (`[CommRing R]`, no hypotheses) and identical to the project's.
- Call sites (Phase 6.0): 0 external; the lemma exists only because the file is a verbatim mathlib copy.

**WHY not (refactor-actionable):**
Mathlib already contains this lemma verbatim. The project's `LutzNagell/DivisionPolynomialDegree.lean` is, by its own module docstring, "a project copy of mathlib's Basic file"; the imported `LutzNagell/DivisionPolynomial.lean` header states it is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` forked **only** to import the project's own `EllipticDivisibilitySequence` (avoiding the `normEDS`/`complEDS` name conflict). So this is not a new mathlib contribution — it is one rung of a duplicated ladder. Nothing should be upstreamed; the duplication is the thing to resolve, on the project side, not mathlib's.

Existing mathlib decl: `WeierstrassCurve.coeff_Ψ₃`
Located at: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:100`
Our form follows in 0 lines (it is the same lemma):
```lean
example : W.Ψ₃.coeff 4 = 3 := W.coeff_Ψ₃
```

Call sites in our project (from Phase 6.0): K = 0 (for this specific lemma).

**Refactor plan (project-side, NOT a mathlib PR):**
The proper fix is not to delete `coeff_Ψ₃` in isolation but to retire the whole fork. The fork exists to dodge a `normEDS` name collision with `LutzNagell.EllipticDivisibilitySequence`. Two routes:
1. **Preferred — de-fork.** Make the project use mathlib's `EllipticDivisibilitySequence` + `DivisionPolynomial.{Basic,Degree}` directly (resolving the `normEDS`/`complEDS` clash by `open`/alias rather than re-defining), then delete `LutzNagell/DivisionPolynomial.lean` and `LutzNagell/DivisionPolynomialDegree.lean` wholesale. Every downstream `import LutzNagell.DivisionPolynomialDegree` becomes `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`; the `WeierstrassCurve.*` names are unchanged, so call sites need no edit beyond the import line.
2. **If the alternative `EllipticDivisibilitySequence` must stay distinct** (genuine mathematical divergence), then the fork is intentional infrastructure and this lemma is collateral — in which case the decision is a project-policy call (see note), not a mathlibable contribution. The lemma still should never be PR'd to mathlib (it's already there).

This is a cleanup/dedup ticket for the NagellLutz project, not a mathlib upstreaming action.

Next action: do not open a mathlib PR. File a project dedup ticket to retire the `DivisionPolynomial*` fork against mathlib's `DivisionPolynomial.{Basic,Degree}` (route 1 above); if the forked `EllipticDivisibilitySequence` is a deliberate divergence, escalate the keep-vs-dedup decision to a human (the fork as a whole, not this lemma).

---

## Next step

Do not upstream. `WeierstrassCurve.coeff_Ψ₃` is already in mathlib verbatim (`DivisionPolynomial/Degree.lean:100`). File a NagellLutz dedup ticket to retire the `LutzNagell.DivisionPolynomial*` fork in favour of mathlib's, which deletes this lemma along with the rest of the duplicated ladder; switch the ~5 downstream importers to the mathlib module path (names unchanged).
