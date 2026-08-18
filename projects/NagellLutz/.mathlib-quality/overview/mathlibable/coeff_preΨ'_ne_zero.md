# /mathlibable report — `WeierstrassCurve.coeff_preΨ'_ne_zero`

## TL;DR

**Verdict: `NO-mathlib-has-it`.** This declaration is a *byte-for-byte identical
fork* of an existing mathlib lemma. The project file
`projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean` is explicitly a
project copy of mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`,
and the lemma exists upstream with the **same qualified name, same statement, and
same proof**:

- Project:  `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:239`
- Mathlib:  `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:242`

The same mathlib (`rev = 09b373db6e24`, toolchain `v4.32.0-rc1`) is the workspace's
pinned dependency, so the upstream lemma is already on the import path; the fork
merely shadows it. A `diff` of the two decl bodies returns **no differences**.

---

### Baseline (Phase 0)
- lake build:               not re-run (build is stale per task brief); verdict is independent of build — it rests on direct source equality with upstream mathlib
- decl `WeierstrassCurve.coeff_preΨ'_ne_zero`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:239`
- qualified name (VERIFIED): `WeierstrassCurve.coeff_preΨ'_ne_zero` — namespace `WeierstrassCurve` opened at file line 59; decl sits inside `section preΨ'` (lines 153–265). The parsed name in the task brief is correct.
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "Division polynomials of Weierstrass curves" — computes leading terms (degree + leading coefficient) of `preΨₙ`, `ΨSqₙ`, `Φₙ`. Header states the file is "a project copy of mathlib's Basic file".

### Statement (Phase 1)

`WeierstrassCurve.coeff_preΨ'_ne_zero` states: let `W` be a Weierstrass curve over
a commutative ring `R`, and let `n : ℕ` with `(n : R) ≠ 0`. Then the coefficient
of the univariate polynomial `preΨ' n` (the "pre-ψ" division polynomial, indexed
by `ℕ`) at degree `d = (n² − [4 if n even else 1]) / 2` is nonzero.

Mathematically: the `n`-th division polynomial `ψₙ` (here its `preΨ'` normal form,
the part not involving the universal `ψ₂`-factor) attains its *expected leading
coefficient* — `n/2` when `n` is even and `n` when `n` is odd — and that leading
coefficient is nonzero whenever the characteristic of `R` does not divide `n`.
This is the nonvanishing half of the standard "ψₙ has degree (n²−1)/2 and leading
coefficient n" fact (Silverman, *Arithmetic of Elliptic Curves*, Exercise 3.7).

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the base commutative ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve.
- `{n : ℕ}` — the division-polynomial index.

Hypotheses (Lean side):
- `(h : (n : R) ≠ 0)` — `n` is invertible/nonzero in `R` (i.e. `char R ∤ n`).

Conclusion (math): the top-degree coefficient of `preΨ'ₙ` is nonzero.
Conclusion (Lean): `(W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) ≠ 0`.

The two-line proof case-splits on `n` even/odd via `n.even_or_odd'`, rewrites by
the companion `coeff_preΨ'` (which evaluates the coefficient to `n/2` or `n`), and
discharges nonvanishing from `h` using `right_ne_zero_of_mul` / `Nat.cast_mul`.

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma (the nonvanishing companion to `coeff_preΨ'`), used only to
prove `natDegree_preΨ'`. Not a named theorem, not a `## Main statement`, not a new
structure. (Literature width run EXHAUSTIVE regardless; recorded for framing.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. No defeq/diamond exemption
analysis applies.

### Literature search (Phase 3)

| #  | Channel                          | Query                                                                                   | Hit? | Standard form found                                            | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------|------|----------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial elliptic curve degree leading coefficient psi_n Silverman"         | yes  | `deg ψₙ = (n²−1)/2`, `lead ψₙ = n`; `ψₙ²` has degree `n²−1`, lead `n²`; `φₙ` degree `n²`, lead `1` | standard; matches the file's stated background exactly. WebSearch *also surfaced the mathlib `DivisionPolynomial/Degree` doc page itself.* |
|  2 | WebSearch (general / nonvanishing) | (same query, nonvanishing-of-leading-coeff angle)                                       | yes  | leading coeff `n` is nonzero ⟺ `char R ∤ n`                    | the `≠ 0` is exactly the char-coprimality condition |
|  3 | WebSearch (named-after / aliases)| "division polynomial" / "ψ_n" leading term (Silverman Exercise 3.7)                     | yes  | same standard form; classical                                 | Silverman *Arithmetic of Elliptic Curves* is the canonical reference (cited verbatim in both the project and the mathlib file) |
|  4 | ChatGPT MCP                      | not invoked                                                                              | n/a  | —                                                              | unnecessary: the verdict is fixed by direct byte-equality with the upstream mathlib source, not by any taste/standard-form judgment that a second opinion could move. |
|  5 | Local references                 | (no `.mathlib-quality/references/` PDFs for NagellLutz)                                  | n/a  | —                                                             | dir not populated with source PDFs; the in-file Silverman citation suffices |
|  6 | nLab                             | "division polynomial"                                                                    | n/a  | —                                                             | not an nLab-style categorical concept; classical algebraic identity |
|  7 | nCatLab                          | —                                                                                       | n/a  | —                                                             | not categorical |
|  8 | Stacks Project                   | division polynomial of a Weierstrass curve                                               | n/a  | —                                                             | Stacks does not treat classical division polynomials of elliptic curves |
|  9 | MathOverflow / MSE               | division polynomial degree leading coefficient                                          | yes  | confirms the classical `deg`/`lead` values                    | folklore-standard |
| 10 | arXiv (last 5 yrs)               | "coefficients of division polynomials" (jtnb / arXiv 1303.5002, 1207.5387)              | yes  | confirm degree/leading-coeff formulas                          | the result is classical and reconfirmed in recent literature |

### Literature summary (Phase 3)

Concept identified as: **the leading term of the `n`-th division polynomial of a
Weierstrass curve** (`ψₙ` / its `preΨₙ` normalisation).
Sources agree on the standard form: **yes** — `lead ψₙ = n`, `deg ψₙ = (n²−1)/2`;
nonvanishing of the leading coefficient is exactly `char R ∤ n`.
Most general standard form: stated over an arbitrary commutative ring `R` with the
hypothesis `(n : R) ≠ 0` — which is precisely the Lean form here.
Generality dimensions where the literature varies: classical statements are over
fields / ℂ; the mathlib (and forked) form is already over an arbitrary `CommRing`,
i.e. **at or above** the literature's generality.
Disagreement with the literature: **none**.

### Generality analysis (Phase 4)

Literature-standard form: leading coefficient of `ψₙ` over a comm. ring, nonzero
iff `char R ∤ n`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | field / ℂ in classical texts | NO (already more general) | mathlib intentionally states the whole division-polynomial API over `CommRing`; cannot meaningfully weaken below `CommRing` (polynomial coefficients, `Even`/division arithmetic). |
| 2 | `(h : (n : R) ≠ 0)`    | `n` nonzero in `R` | `char R ∤ n`             | NO                  | this is the minimal hypothesis making the leading coefficient nonzero; weakening it makes the statement false (e.g. `char R ∣ n` kills the top coefficient). |
| 3 | `{n : ℕ}`              | natural-number index | ℕ (the `preΨ'` indexing) | NO                  | `preΨ'` is by construction the ℕ-indexed normal form; the ℤ generalisation already exists upstream as `coeff_preΨ_ne_zero`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is identical to mathlib's, which is
already at/above the literature standard). Weakening opportunities: 0.

### Modern-idiom check (Phase 4c)

Modern idiom available: **no**. Every row (typeclass-ification, filters-over-
sequences, universal property, bundled substructure, weaker-typeclass, higher-
category, index generalisation) is `no`: this is a finite polynomial-coefficient
nonvanishing fact, already stated over a general `CommRing` with the canonical
hypothesis, and the ℤ-index generalisation already lives upstream
(`coeff_preΨ_ne_zero`). There is nothing to modernise — it is *already* the
mathlib-idiomatic form, because it literally is the mathlib lemma.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities / typeclass-search
paths introduced).

### Mathlib search-status: `WeierstrassCurve.coeff_preΨ'_ne_zero` (Phase 5)

[A] Lean-Finder       "division polynomial leading coefficient nonzero"   → hit: the `DivisionPolynomial/Degree` module
[B] Loogle            `(WeierstrassCurve.preΨ' _ _).coeff _ ≠ 0`            → hit: `WeierstrassCurve.coeff_preΨ'_ne_zero`
[C] LeanSearch        "coefficient of division polynomial preΨ' is nonzero" → hit: same decl (WebSearch surfaced the doc page for `DivisionPolynomial/Degree`)
[D] Grep mathlib src  `coeff_preΨ'_ne_zero` over `.lake/.../mathlib/Mathlib/` → **EXACT HIT** at `DivisionPolynomial/Degree.lean:242`
[E] Name pattern      `coeff_preΨ'` in `WeierstrassCurve` namespace          → hit: `coeff_preΨ'`, `coeff_preΨ'_ne_zero`, `coeff_preΨ_ne_zero` all present upstream

Searched for both the current form and the (identical) literature-standard form.

Concluded: **found in mathlib as `WeierstrassCurve.coeff_preΨ'_ne_zero`; IDENTICAL
form.** A direct `diff` of the project decl (`DivisionPolynomialDegree.lean`
lines 239–244) against mathlib (`Degree.lean` lines 242–247) returns **no
differences** — same signature, same proof. The surrounding context matches too:
same `namespace WeierstrassCurve`, same `variable {R : Type u} [CommRing R]
(W : WeierstrassCurve R)`, same `section preΨ'`, and even the file's module
docstring (Main-statements list + Silverman reference + tags) is identical. The
mathlib pin in the workspace `lakefile.toml` (`rev = 09b373db6e24`) is the very
file that contains this lemma.

### Call sites — `WeierstrassCurve.coeff_preΨ'_ne_zero` (Phase 6.0)

Internal use count (excluding the declaring line): **2**, both within the same
forked file (and both also present identically upstream):

| Caller file:line                                   | Usage pattern |
|----------------------------------------------------|---------------|
| `DivisionPolynomialDegree.lean:249`                | `natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_preΨ'_le n) <| W.coeff_preΨ'_ne_zero h` (proving `natDegree_preΨ'`) |
| `DivisionPolynomialDegree.lean:290`                | `... using W.coeff_preΨ'_ne_zero <| by exact_mod_cast h` (proving `coeff_preΨ_ne_zero`) |

External-to-file callers: **0**. The lemma is purely an internal helper of the
fork. Both consumers (`natDegree_preΨ'`, `coeff_preΨ_ne_zero`) are themselves
verbatim forks of upstream mathlib lemmas, so nothing project-specific depends on
the forked copy.

Inline-derivation grep: (none) — no re-derivation; it is simply the forked twin of
the upstream lemma.

### Composition check (Phase 6)

Not applicable as the decisive factor: the result is not "composable from
primitives" — it is *literally already a named mathlib lemma*. (For completeness:
mathlib's own one-line consumers `natDegree_preΨ'`/`coeff_preΨ_ne_zero` show the
intended downstream use; but the lemma itself is the canonical statement, not a
composition.) Conclusion: **N/A — superseded by the exact mathlib hit.**

---

## Verdict: `WeierstrassCurve.coeff_preΨ'_ne_zero`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): standard Silverman fact; WebSearch even returned the mathlib `DivisionPolynomial/Degree` doc page itself.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical to upstream; nothing to weaken or modernise.
- Mathlib search (Phase 5): **EXACT hit** — `WeierstrassCurve.coeff_preΨ'_ne_zero` at `DivisionPolynomial/Degree.lean:242`; `diff` shows no differences.
- Composition check (Phase 6): N/A — it *is* the mathlib lemma, not a composition.

**Rationale:**

This is the cleanest possible `NO-mathlib-has-it`. The NagellLutz project
deliberately *forks* mathlib's elliptic-curve division-polynomial files (the file
header literally says it depends on "a project copy of mathlib's Basic file"), and
`coeff_preΨ'_ne_zero` is one of those forked lemmas. It is identical to the
upstream lemma in **qualified name** (`WeierstrassCurve.coeff_preΨ'_ne_zero`),
**statement**, and **proof** — a byte-for-byte `diff` between
`DivisionPolynomialDegree.lean:239–244` and mathlib's `Degree.lean:242–247`
produces no output. The surrounding declaration context (namespace, variables,
section, even the module docstring and Silverman citation) is identical as well,
confirming the file is a wholesale copy rather than an independent reproof. The
same mathlib revision that hosts this lemma is the workspace's pinned dependency,
so the project's copy strictly *shadows* an importable upstream lemma.

There is no generalisation to make (the form is already over an arbitrary
`CommRing` with the minimal `(n : R) ≠ 0` hypothesis, matching the literature) and
no modern-idiom improvement (the ℤ-indexed generalisation `coeff_preΨ_ne_zero`
already exists upstream too). The only correct action is to *not* contribute this
to mathlib — it is already there — and, when the fork is eventually reconciled, to
drop the project copy and import the upstream module.

**WHY not (refactor-actionable):**
Mathlib already has the result, identically.
- Existing mathlib decl:  `WeierstrassCurve.coeff_preΨ'_ne_zero`
- Located at:             `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:242` (in-workspace: `.lake/packages/mathlib/...`)
- Our form follows in 0 lines — it is the same lemma:
  ```lean
  example {R : Type u} [CommRing R] (W : WeierstrassCurve R) {n : ℕ} (h : (n : R) ≠ 0) :
      (W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) ≠ 0 :=
    W.coeff_preΨ'_ne_zero h   -- the mathlib lemma, verbatim
  ```
- Call sites in our project (Phase 6.0): K = 2, both inside the forked
  `DivisionPolynomialDegree.lean` (lines 249, 290); 0 external.

**Refactor plan.** This lemma should be removed as part of *retiring the whole
`LutzNagell/DivisionPolynomial*` fork*, not surgically on its own — its two
consumers (`natDegree_preΨ'`, `coeff_preΨ_ne_zero`) are likewise verbatim forks.
Concretely: replace `import LutzNagell.DivisionPolynomial` /
`LutzNagell.DivisionPolynomialDegree` with
`import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` and
`...DivisionPolynomial.Degree`, delete the duplicated `WeierstrassCurve.*`
declarations in `DivisionPolynomialDegree.lean` (including this one), and let the
upstream `WeierstrassCurve.coeff_preΨ'_ne_zero` resolve. No call-site edits are
needed beyond the import swap, since names and signatures are identical (the
project's downstream NagellLutz files already call `W.coeff_preΨ'_ne_zero` /
`W.natDegree_preΨ'` by the same names). Verify only that the forked file holds no
*local* divergences from upstream before deleting (the `diff` above shows it does
not for this lemma).

**Next action:** delete `WeierstrassCurve.coeff_preΨ'_ne_zero` from the project as
part of dropping the `DivisionPolynomial*` fork; import
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` and rely on the
upstream lemma.

---

## Next step

Delete the forked `WeierstrassCurve.coeff_preΨ'_ne_zero` (and its sibling forked
division-polynomial lemmas) and import
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.{Basic,Degree}` instead —
the identical lemma is already upstream at `DivisionPolynomial/Degree.lean:242`.

Sources (literature anchor, Phase 3):
- [Mathlib `DivisionPolynomial/Degree` docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.html)
- [Coefficients of division polynomials (J. Théor. Nombres Bordeaux)](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.881.pdf)
- [One half log discriminant and division polynomials (arXiv:1207.5387)](https://arxiv.org/pdf/1207.5387)
