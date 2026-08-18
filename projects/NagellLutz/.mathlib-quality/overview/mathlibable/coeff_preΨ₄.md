# Mathlibable assessment — `WeierstrassCurve.coeff_preΨ₄`

**Verdict: NO-mathlib-has-it**

> The identical declaration (same name, same namespace, same statement, same proof)
> is already in upstream mathlib — this file is a fork-copy of it.

---

## 1. Declaration under assessment

- **Qualified name:** `WeierstrassCurve.coeff_preΨ₄` (verified: section `preΨ₄` inside
  `namespace WeierstrassCurve`, opened at line 55, closed at line 452).
- **Location:** `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:126`
- **Statement & proof (verbatim):**

```lean
@[simp]
lemma coeff_preΨ₄ : W.preΨ₄.coeff 6 = 2 := by
  rw [preΨ₄]
  compute_degree!
```

  Context: `variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)`, `open Polynomial`.

- **Math content:** the degree‑6 coefficient of the auxiliary 4‑division polynomial
  `preΨ₄` (where `ψ₄ = Ψ₄ = preΨ₄ · ψ₂`) equals `2`. This is the "leading coefficient `n/2`
  for even `n`" fact specialised to `n = 4` (`4/2 = 2`, degree `(16−4)/2 = 6`); it serves as
  the `four` base case of the strong induction `natDegree_coeff_preΨ'` (used at line 207).

## 2. Literature search

This is not a named theorem; it is an internal coefficient-bookkeeping lemma in the
development of division polynomials of Weierstrass curves (Silverman, *The Arithmetic of
Elliptic Curves*, exercise 3.7 / §III.3 — the reference the file itself cites). The general
"leading term of `preΨₙ`" statement is the mathematical content; the `n = 4` coefficient is
a computational sub-fact with no independent literature identity. No separate, more-general
"standard form" exists to upstream beyond what mathlib already has.

## 3. Mathlib search — IT IS ALREADY THERE (exact)

The project file is a **fork-copy** of mathlib's
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`
(same Copyright header, same author *David Kurniadi Angdinata*, same module docstring,
same Silverman reference, same lemma layout).

Found in the repo's own pinned mathlib (`lakefile.toml` rev `09b373db6e24`, toolchain
`v4.32.0-rc1`):

- `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:130`

```lean
@[simp]
lemma coeff_preΨ₄ : W.preΨ₄.coeff 6 = 2 := by
  rw [preΨ₄]
  compute_degree!
```

inside `namespace WeierstrassCurve` (Degree.lean:59 … `end WeierstrassCurve` at 452), so the
upstream fully-qualified name is **exactly** `WeierstrassCurve.coeff_preΨ₄`.

**This is byte-for-byte identical** to the project decl: same name, same `@[simp]`,
same `W.preΨ₄.coeff 6 = 2`, same `rw [preΨ₄]; compute_degree!` proof.

`diff` of the two files: only **28** changed lines total, none of them in the `preΨ₄` block.
The differences are entirely (a) the import/module preamble (project imports its local
`LutzNagell.DivisionPolynomial` copy of `…/Basic.lean`; mathlib uses the `module` /
`public import` system) and (b) cosmetic proof-syntax skew elsewhere in the file
(`convert!`/`convert`, `using!`/`using`, `=>`/`↦`, a few `Int.natAbs_natCast` simp args).

Confirmed live in the public mathlib4 docs:
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` lists this declaration
together with its `…_ne_zero`, `natDegree_preΨ₄`, and `leadingCoeff_preΨ₄` siblings — see
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.html>.

The CLAUDE/project notes flag exactly this: NagellLutz "FORKS parts of mathlib
(`…DivisionPolynomial.*`)". This decl is one of the forked-in copies.

### Mathlib five-method search outcome
1. **Exact name** `WeierstrassCurve.coeff_preΨ₄` — **HIT** (Degree.lean:130).
2. **By statement / `simp` set** — it is `@[simp]`; `simp` over `preΨ₄`/`compute_degree`
   reproduces it. **HIT.**
3. **More general form** (`coeff_preΨ` / `coeff_preΨ'`) — also present (Degree.lean:233, 276),
   `n = 4` instance. **HIT.**
4. **Docs/loogle/leansearch** — appears in mathlib4 docs (web). **HIT.**
5. **Grep in pinned mathlib tree** — present. **HIT.**

## 4. Generality analysis

Not applicable for upstreaming: mathlib already contains both this `n = 4` instance **and**
the fully general statements `coeff_preΨ'` / `coeff_preΨ` (leading coefficient
`if Even n then n/2 else n`, degree `(n² − {4|1})/2`). There is nothing more general to add.

## 5. Composition check

Trivially yes — it *is* mathlib, and it is also a 1-line instance of the general
`coeff_preΨ` (`n = 4`). No composition argument needed; the decl is literally present.

## 6. Five-bucket verdict

**NO-mathlib-has-it.**

Evidence: identical declaration `WeierstrassCurve.coeff_preΨ₄` at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:130` in the very
mathlib this repo pins — same fully-qualified name, same `@[simp]` statement
`W.preΨ₄.coeff 6 = 2`, same `rw [preΨ₄]; compute_degree!` proof. The project file is a
fork-copy of that mathlib file (same author, 28 cosmetic diff lines, none in this lemma).

**Action for the consolidation:** drop the project copy and `import` mathlib's
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` (a deduplication chore,
not a mathlib contribution). Note this applies to the whole
`DivisionPolynomialDegree.lean` file, not just this one lemma.

### Sources
- mathlib4 docs — `…DivisionPolynomial.Degree`:
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.html>
- mathlib4 docs — `…DivisionPolynomial.Basic`:
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html>
- Pinned mathlib source in-repo:
  `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:130`
- Silverman, *The Arithmetic of Elliptic Curves* (the file's own cited reference).
