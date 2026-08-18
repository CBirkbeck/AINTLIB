# /mathlibable report — `WeierstrassCurve.leadingCoeff_Ψ₃`

**Verdict: NO-mathlib-has-it** (verbatim duplicate — this declaration is already in mathlib, byte-identical in statement, attribute, proof, and the definition it concerns).

---

## Baseline (Phase 0)

- lake build: not run (local build stale per task brief); reasoning from source + the vendored mathlib tree on disk at `.lake/packages/mathlib`.
- decl `WeierstrassCurve.leadingCoeff_Ψ₃`: resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:111` (the `@[simp] lemma` head is line 110; the `by` body opens at line 111 — the brief's pointer).
- kind: `lemma` (theorem-like; carries `@[simp]`).
- has sorry: no.
- module docstring summary: the file header (line 13–14) states it "computes the leading terms of certain polynomials associated to division polynomials … defined in `LutzNagell/DivisionPolynomial.lean` (**a project copy of mathlib's Basic file**)." The imported `LutzNagell/DivisionPolynomial.lean` header (line 11–15) states it "is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.)."

Qualified name (VERIFIED from source): **`WeierstrassCurve.leadingCoeff_Ψ₃`**. Enclosing `namespace WeierstrassCurve` (file line 55) + bare name `leadingCoeff_Ψ₃` (file line 110) ⇒ qualified `WeierstrassCurve.leadingCoeff_Ψ₃`. Matches the parsed name in the task brief.

---

## Statement (Phase 1)

`WeierstrassCurve.leadingCoeff_Ψ₃` states: for a Weierstrass curve `W` over a commutative ring `R` in which `3 ≠ 0`, the leading coefficient of the 3-division polynomial `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` equals `3`.

- Parameters: `{R : Type u} [CommRing R]`, `(W : WeierstrassCurve R)`.
- Hypotheses: `(h : (3 : R) ≠ 0)`.
- Conclusion (math): `leadingCoeff Ψ₃ = 3`.
- Conclusion (Lean): `W.Ψ₃.leadingCoeff = 3`.

Proof (3 lines, verbatim):
```lean
@[simp]
lemma leadingCoeff_Ψ₃ (h : (3 : R) ≠ 0) : W.Ψ₃.leadingCoeff = 3 := by
  rw [leadingCoeff, W.natDegree_Ψ₃ h, coeff_Ψ₃]
```
Unfold `leadingCoeff` to `coeff (natDegree)`, rewrite the degree to `4` via `natDegree_Ψ₃` (needs `3 ≠ 0`), then read off `coeff 4 = 3` via `coeff_Ψ₃`.

This is the capstone rung of the standard degree/leading-coefficient ladder for the 3-division polynomial:
`natDegree_Ψ₃_le` → `coeff_Ψ₃` → `coeff_Ψ₃_ne_zero` → `natDegree_Ψ₃` → `natDegree_Ψ₃_pos` → **`leadingCoeff_Ψ₃`** → `Ψ₃_ne_zero` — all present identically in both trees.

---

## Size classification (Phase 2a)

Verdict: SMALL. A single leading-coefficient helper for one concrete polynomial; not a named theorem, not a new structure, not a project main result. (`--exhaustive` not triggered.)

## One-line check (Phase 2b)

n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`. No one-liner-definition concern.

---

## Phases 3–4 — Literature / generality (SHORT-CIRCUITED, justified)

The literature and generality phases exist to answer "*should* mathlib have this, and in what form?". That question is **already settled**: mathlib has this exact lemma, about this exact definition, with this exact proof and the same `@[simp]` attribute. There is no open generality question — the project's `Ψ₃` is **byte-identical** to mathlib's `Ψ₃` (both `3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈`, over the same `[CommRing R]`), so the only "literature standard" form is the one mathlib already ships. For completeness:

- Concept: leading coefficient (and degree) of the 3-division polynomial `ψ₃` of an elliptic/Weierstrass curve. Standard reference: J. Silverman, *The Arithmetic of Elliptic Curves* (2nd ed.), §III.3 / Exercise 3.7 — cited in the file's own `## References` (`[silverman2009]`). That `ψ₃` has degree 4 with leading coefficient 3 (when `char ≠ 3`) is textbook; it is exactly the fact used in the classical Nagell–Lutz argument bounding torsion.
- Generality: the hypothesis `(3 : R) ≠ 0` is exactly the necessary and sufficient condition for the leading coefficient to *be* the degree-4 coefficient (otherwise `3` could vanish in `R` and the natDegree could drop). `[CommRing R]` is the maximal sensible base — the statement is a coefficient identity in the `bᵢ`; no domain/field/characteristic-typeclass strengthening is warranted or possible. mathlib's form is identical, hence already maximal. No modern-idiom restatement applies (it is a concrete coefficient identity — nothing to filter-ise, classify, or typeclass-ify).

No literature-driven improvement is available because the target already exists upstream in its final, maximally-general form. (ChatGPT MCP not consulted — possibly down per brief, and unnecessary: a source-grep hit on the identical qualified name + identical definition is conclusive, matching the methodology of the sibling `coeff_Ψ₃` and `natDegree_Ψ₃_le` reports in this same folder.)

## Phase 4.5 — Diamond/defeq risk

n/a — declaration kind is `lemma` (proof-irrelevant; introduces no definitional equality or instance path).

---

## Mathlib search-status (Phase 5)

Five-method search collapses to a direct source hit (the vendored mathlib tree is on disk):

- [D] Grep mathlib src — `grep -n "leadingCoeff_Ψ₃" .lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` → **HIT at line 115**.
- [E] Name pattern / namespace — `section Ψ₃` at `Degree.lean:93`; `namespace WeierstrassCurve` governs the file; bare `leadingCoeff_Ψ₃` at line 115 ⇒ qualified `WeierstrassCurve.leadingCoeff_Ψ₃`. Exact namespace + name agreement with the project decl.
- [A] Lean-Finder / [B] Loogle / [C] LeanSearch — not needed; an exact-source grep hit on the identical qualified name is conclusive. (A Loogle query `?W.Ψ₃.leadingCoeff = 3` would resolve to the same decl.)

Side-by-side (mathlib `Degree.lean:114-116` vs. project `DivisionPolynomialDegree.lean:110-112`):

```lean
@[simp]
lemma leadingCoeff_Ψ₃ (h : (3 : R) ≠ 0) : W.Ψ₃.leadingCoeff = 3 := by
  rw [leadingCoeff, W.natDegree_Ψ₃ h, coeff_Ψ₃]
```

A `diff` of the 3 lemma lines reports **byte-identical** (no differences). Identical in every respect: `@[simp]` attribute, name, signature, hypothesis `(3 : R) ≠ 0`, variable context (`{R : Type u} [CommRing R] (W : WeierstrassCurve R)`, declared identically at line 57 of the project file / line 61 of mathlib's), and proof term. The supporting lemmas it invokes (`natDegree_Ψ₃`, `coeff_Ψ₃`) are themselves byte-identical duplicates, and the `Ψ₃` definition it concerns is byte-identical (project `DivisionPolynomial.lean:65-66` vs. mathlib `Basic.lean:142-143`). The project file even carries mathlib's original copyright header ("Copyright (c) 2024 David Kurniadi Angdinata").

**Concluded: found in mathlib as `WeierstrassCurve.leadingCoeff_Ψ₃`; identical form** (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:115`).

---

## Call sites (Phase 6.0)

Internal use count (excluding the declaring file): **0**.
External-to-file callers: **0 distinct files**.

- `grep -rn --include='*.lean' "leadingCoeff_Ψ₃" projects/ | grep -v DivisionPolynomialDegree.lean` → nothing.
- Inline-derivation grep `grep -rn --include='*.lean' "Ψ₃.leadingCoeff" projects/ | grep -v DivisionPolynomialDegree.lean` → nothing (no other site re-derives the leading coefficient).

Interpretation: K = 0 external uses is expected and not a defect signal — the whole file is a wholesale verbatim fork of mathlib's `Degree.lean`, dragged in only to namespace the project's alternative `EllipticDivisibilitySequence`. `leadingCoeff_Ψ₃` is terminal leaf API (it is among the file's "exported-for-downstream-use" leaves per the inventory), shipped for completeness of the ladder; downstream consumers (e.g. `GeneralIntegralMultiple.lean`, `PIDPrimeOrder.lean`) draw on the ladder's results, and every one of those is likewise already in mathlib.

## Composition check (Phase 6)

Can `WeierstrassCurve.leadingCoeff_Ψ₃` be obtained from mathlib in ≤3 calls? Trivially in 0 — it **is** the mathlib lemma:

```lean
example {R : Type u} [CommRing R] (W : WeierstrassCurve R) (h : (3 : R) ≠ 0) :
    W.Ψ₃.leadingCoeff = 3 :=
  W.leadingCoeff_Ψ₃ h            -- the mathlib lemma, once the project imports it instead of forking
```

Conclusion: redundant with an identical upstream decl (a degenerate NO-mathlib-has-it, stronger than COMPOSABLE — there is nothing to compose, the lemma already exists verbatim).

---

## Verdict: `WeierstrassCurve.leadingCoeff_Ψ₃`

**Category: NO-mathlib-has-it**

**Evidence:**
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.leadingCoeff_Ψ₃`, `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:115` — `diff`-confirmed byte-identical statement, proof, `@[simp]` attribute, and variable context.
- The definition it concerns (`WeierstrassCurve.Ψ₃`) and the two lemmas it invokes (`natDegree_Ψ₃`, `coeff_Ψ₃`) are all byte-identical between the project fork and mathlib.
- Generality (Phases 3–4): no open question — mathlib's form is already maximal (`[CommRing R]`, the necessary-and-sufficient `(3 : R) ≠ 0`) and identical to the project's.
- Call sites (Phase 6.0): 0 external; 0 inline re-derivations. The lemma exists only because the file is a verbatim mathlib copy.

**WHY not (refactor-actionable):**
Mathlib already contains this lemma verbatim. The project's `LutzNagell/DivisionPolynomialDegree.lean` is, by its own module docstring, a "project copy of mathlib's Basic file"; the imported `LutzNagell/DivisionPolynomial.lean` is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` forked **only** to import the project's own `EllipticDivisibilitySequence` (avoiding the `normEDS`/`complEDS` name conflict). So this is not a new mathlib contribution — it is the top rung of a duplicated ladder. Nothing should be upstreamed; the duplication is the thing to resolve, on the project side, not mathlib's.

Existing mathlib decl: `WeierstrassCurve.leadingCoeff_Ψ₃`
Located at: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:115`
Our form follows in 0 lines (it is the same lemma):
```lean
example (h : (3 : R) ≠ 0) : W.Ψ₃.leadingCoeff = 3 := W.leadingCoeff_Ψ₃ h
```

Call sites in our project (from Phase 6.0): K = 0 (for this specific lemma).

**Refactor plan (project-side, NOT a mathlib PR):**
The proper fix is not to delete `leadingCoeff_Ψ₃` in isolation but to retire the whole fork. The fork exists to dodge a `normEDS`/`complEDS` name collision with `LutzNagell.EllipticDivisibilitySequence`. Two routes (identical to the sibling `coeff_Ψ₃` report):
1. **Preferred — de-fork.** Make the project use mathlib's `EllipticDivisibilitySequence` + `DivisionPolynomial.{Basic,Degree}` directly (resolving the `normEDS`/`complEDS` clash by `open`/alias rather than re-defining), then delete `LutzNagell/DivisionPolynomial.lean` and `LutzNagell/DivisionPolynomialDegree.lean` wholesale. Every downstream `import LutzNagell.DivisionPolynomialDegree` becomes `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`; the `WeierstrassCurve.*` names are unchanged, so call sites need no edit beyond the import line.
2. **If the alternative `EllipticDivisibilitySequence` must stay distinct** (genuine mathematical divergence), then the fork is intentional infrastructure and this lemma is collateral — a project-policy call (escalate the fork-wide keep-vs-dedup decision to a human), not a mathlibable contribution. The lemma still must never be PR'd to mathlib (it is already there).

This is a cleanup/dedup ticket for the NagellLutz project, not a mathlib upstreaming action.

---

## Next step

Do not upstream. `WeierstrassCurve.leadingCoeff_Ψ₃` is already in mathlib verbatim (`DivisionPolynomial/Degree.lean:115`). File (or fold into the existing) NagellLutz dedup ticket to retire the `LutzNagell.DivisionPolynomial*` fork in favour of mathlib's, which deletes this lemma along with the rest of the duplicated ladder; switch downstream importers to the mathlib module path (names unchanged). If the forked `EllipticDivisibilitySequence` is a deliberate divergence, escalate the keep-vs-dedup decision for the fork as a whole to a human.
