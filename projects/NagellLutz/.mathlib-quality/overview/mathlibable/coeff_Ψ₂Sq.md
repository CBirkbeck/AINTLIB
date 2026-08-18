# /mathlibable report — `WeierstrassCurve.coeff_Ψ₂Sq`

**Verdict: NO-mathlib-has-it** — this declaration is a verbatim fork of an
existing mathlib lemma (identical statement, identical proof, identical `@[simp]`
attribute, identical underlying `Ψ₂Sq` definition).

---

## Baseline (Phase 0)

- lake build:               not re-run (stale local build per task note); decl read directly from source
- decl `WeierstrassCurve.coeff_Ψ₂Sq`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:70` (lemma head;
  the prompt's line 66 is the `rw [Ψ₂Sq]` proof-body line of the same lemma)
- kind:                      lemma (`theorem`)
- has sorry:                 no
- module docstring summary:  "Division polynomials of Weierstrass curves … a project
  copy of mathlib's Basic file" — the file header **explicitly states it is a fork**
  of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`.

Qualified-name verification: file opens `namespace WeierstrassCurve`
(DivisionPolynomialDegree.lean:55) with `variable {R : Type u} [CommRing R]
(W : WeierstrassCurve R)` (line 57); the lemma is `W.Ψ₂Sq.coeff 3 = 4` via dot
notation. Parsed qualified name **confirmed**: `WeierstrassCurve.coeff_Ψ₂Sq`.

---

## Statement (Phase 1)

`WeierstrassCurve.coeff_Ψ₂Sq` states: for a Weierstrass curve `W` over a commutative
ring `R`, the coefficient of `X³` in the univariate two-torsion polynomial
`Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆ ∈ R[X]` equals `4`.

```lean
@[simp]
lemma coeff_Ψ₂Sq : W.Ψ₂Sq.coeff 3 = 4 := by
  rw [Ψ₂Sq]
  compute_degree!
```

- `R : Type u`, `[CommRing R]` — coefficient ring.
- `W : WeierstrassCurve R` — the curve (supplies `b₂, b₄, b₆`).
- Conclusion (math): the leading (degree-3) coefficient of `4X³ + b₂X² + 2b₄X + b₆` is `4`.
- Conclusion (Lean): `W.Ψ₂Sq.coeff 3 = 4`.

It is a trivial coefficient extraction from an explicit cubic; mathematically it is
"the `X³` coefficient of `Ψ₂Sq` is the visible leading constant `4`."

---

## Size classification (Phase 2a)

Verdict: SMALL. A one-coefficient computation about an explicit degree-3 polynomial;
a helper feeding `natDegree_Ψ₂Sq` / `leadingCoeff_Ψ₂Sq`. Not a named theorem, not a
new structure, not a `## Main results` headline.

## One-line check (Phase 2b)

n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`. (Proof is two tactic lines;
no defeq/diamond/API-anchor question arises.)

---

## Literature search (Phase 3) — short-circuited by an exact mathlib match

The standard `Ψ₂Sq` (a.k.a. the 2-division / two-torsion polynomial
`4x³ + b₂x² + 2b₄x + b₆`, equivalently `ψ₂² = 4x³ + ... `) is textbook material
(Silverman, *The Arithmetic of Elliptic Curves*, III.2 / Exercise 3.7 — the very
reference cited in this file's docstring). That its leading coefficient is `4` is
immediate from the explicit formula.

The full nine-channel exhaustive literature sweep is **not the deciding factor
here**: mathlib already contains this exact declaration (Phase 5), so the verdict is
fixed at `NO-mathlib-has-it` regardless of literature framing. Recording the
literature anchor for completeness:

| # | Channel | Query | Hit? | Standard form | Notes |
|---|---------|-------|------|---------------|-------|
| 1 | Textbook (local-context) | Silverman AEC two-torsion polynomial `4x³+b₂x²+2b₄x+b₆` | yes | leading coeff `4`, degree `3` | cited in this file's own `## References` |
| 2–10 | (remaining channels) | — | n/a | — | Not run: an **exact verbatim mathlib decl exists** (Phase 5). Per the verdict table, `NO-mathlib-has-it` requires only the cited mathlib decl + ≤1-line follow; no literature/generality/composition gate applies once mathlib has the identical lemma. |

### Literature summary (Phase 3)

Concept: the coefficient `[X³] Ψ₂Sq = 4` of the (uni­variate) two-torsion division
polynomial of a Weierstrass curve. Standard, trivial, textbook. No disagreement.

---

## Generality analysis (Phase 4) — not load-bearing

The mathlib decl this forks is **already** stated at full generality:
`{R : Type u} [CommRing R] (W : WeierstrassCurve R)` — an arbitrary commutative ring,
which is the weakest sensible hypothesis (the polynomial `Ψ₂Sq` and its coefficients
are defined over any `CommRing`). The project copy uses the **identical** signature.

- 4a/4b: current form = MAXIMALLY GENERAL; identical to mathlib's. No weakening exists.
- 4c (modern idiom): no — a `Polynomial.coeff` value over a `CommRing` is already the
  contemporary mathlib idiom; nothing to filter-ise/typeclass-ify. The mathlib
  original is the modern form, and this is a byte-for-byte copy of it.

Generality is moot: you cannot be "more general than" an exact duplicate of the
already-maximally-general mathlib lemma.

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`.

---

## Mathlib search (Phase 5) — EXACT MATCH

Located by direct grep of the pinned mathlib source in this workspace
(`.lake/packages/mathlib/`):

```
[D] Grep mathlib src   "Ψ₂Sq", "coeff_Ψ₂Sq"   HIT — exact duplicate
[E] Name pattern       coeff_Ψ₂Sq               HIT — same qualified name WeierstrassCurve.coeff_Ψ₂Sq
[A]/[B]/[C] Loogle/LeanSearch/Lean-Finder       n/a — direct source hit already dispositive
```

**Found in mathlib as `WeierstrassCurve.coeff_Ψ₂Sq`; identical form.**

- Location: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:69-72`
  (the `@[simp] lemma coeff_Ψ₂Sq : W.Ψ₂Sq.coeff 3 = 4 := by rw [Ψ₂Sq]; compute_degree!`).
- The underlying `def Ψ₂Sq` is also a verbatim copy: mathlib
  `Basic.lean:117-118` (`C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆`)
  vs project copy `DivisionPolynomial.lean:40-41` — character-for-character identical.
- `diff` of the project's entire `section Ψ₂Sq` degree block against mathlib's shows
  **no differences in the lemma block** (only the surrounding namespace header above
  and the start of the next `section Ψ₃` below appear in the context diff).

The project's `DivisionPolynomialDegree.lean` is a fork of mathlib's
`DivisionPolynomial/Degree.lean`, and `coeff_Ψ₂Sq` is reproduced unchanged —
statement, proof tactic block, and `@[simp]` attribute all identical.

---

## Composition check (Phase 6)

### Call sites — `WeierstrassCurve.coeff_Ψ₂Sq`

Internal use count: **0** (within the NagellLutz project, excluding the declaring
file and the distinct `coeff_Ψ₂Sq_ne_zero` lemma).
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none outside the declaring file) | — |

Within the declaring file the lemma is used by `coeff_Ψ₂Sq_ne_zero`
(DivisionPolynomialDegree.lean:71) and `leadingCoeff_Ψ₂Sq` (line 82) — exactly as in
mathlib's own file. In mathlib, `coeff_Ψ₂Sq` additionally feeds the `expCoeff`/`Φ`
degree machinery (`Degree.lean:227,229,341,414,415`). The project file's consumers
mirror mathlib's; there are **no project-specific consumers** that would justify a
local copy.

Inline-derivation grep: none — it is not re-derived elsewhere; it is simply the
forked copy.

Composition: COMPOSABLE in the trivial sense (it *is* a 1-call use of the mathlib
lemma — `WeierstrassCurve.coeff_Ψ₂Sq` itself). But this is the
`NO-mathlib-has-it` path, not `NO-composable`: the form is not *composed from*
primitives, it is the *identical lemma*, present verbatim in mathlib.

---

## Verdict: `WeierstrassCurve.coeff_Ψ₂Sq`

**Category: NO-mathlib-has-it**

**Evidence:**
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.coeff_Ψ₂Sq`,
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:69-72`;
  **identical** statement, proof, and `@[simp]` attribute.
- Generality (Phase 4): MAXIMALLY GENERAL and identical to mathlib's (`[CommRing R]`).
- Literature (Phase 3): standard textbook fact (Silverman AEC); not load-bearing.
- Composition (Phase 6): 0 project-external call sites; consumers mirror mathlib's.

**Rationale:**

This project FORKS `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`
(the file's own module docstring says so: "a project copy of mathlib's Basic file"),
and `coeff_Ψ₂Sq` is reproduced from mathlib **without any change** — same signature,
same `:= by rw [Ψ₂Sq]; compute_degree!` proof, same `@[simp]`. The underlying
`def Ψ₂Sq` is likewise a byte-for-byte copy. There is nothing to contribute: mathlib
already has precisely this lemma at precisely this generality. This is the textbook
`NO-mathlib-has-it` case — the verdict is determined entirely by Phase 5's exact-match
hit, which is why the literature/generality/composition phases are not load-bearing.

**WHY not (refactor-actionable):**

Mathlib already has the identical lemma. Our form is not a specialisation or a
follow — it is the *same* lemma. The whole forked degree file should ultimately be
replaced by `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`
(this is exactly what the project's existing `-- TODO: remove twoTorsionPolynomial in
favour of Ψ₂Sq` comments and the "project copy of mathlib's Basic file" docstring
foreshadow). Note: the fork exists to let the NagellLutz development add *new* division-
polynomial lemmas not yet upstream; `coeff_Ψ₂Sq` is simply collateral duplication
inside that fork, not part of the new content.

Existing mathlib decl:        `WeierstrassCurve.coeff_Ψ₂Sq`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:69`
Our form follows in 0 lines (it is the same statement):
```lean
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.Ψ₂Sq.coeff 3 = 4 :=
  W.coeff_Ψ₂Sq          -- the mathlib lemma, verbatim
```
Call sites in our project (Phase 6.0): 0 external to the declaring file.

Refactor plan:
1. Do **not** upstream this lemma — mathlib has it identically.
2. The duplication is removed for free when the NagellLutz fork is reconciled with
   upstream mathlib: drop the local `Ψ₂Sq` section copies from
   `DivisionPolynomial.lean` / `DivisionPolynomialDegree.lean` and `import` mathlib's
   `DivisionPolynomial/Basic` + `DivisionPolynomial/Degree` instead, keeping only the
   genuinely-new lemmas the fork was created to host.
3. Until that reconciliation, no action on this specific decl: it is correct and
   `@[simp]`-consistent with mathlib; it is just redundant.

**Next action:** delete the forked `coeff_Ψ₂Sq` (and its `Ψ₂Sq` degree-section
siblings) once the NagellLutz project re-bases its division-polynomial files onto
mathlib's upstream `DivisionPolynomial.{Basic,Degree}`; no mathlib PR (mathlib already
has it).

---

## Next step

No mathlib PR. When reconciling the NagellLutz division-polynomial fork with upstream,
replace the copied `Ψ₂Sq` degree section with an `import` of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`; `coeff_Ψ₂Sq` is
already in mathlib verbatim.
