# /mathlibable report — `WeierstrassCurve.natDegree_preΨ₄_pos`

> **Verdict: `NO-mathlib-has-it`.** This declaration is a **byte-for-byte verbatim fork** of
> mathlib's own `WeierstrassCurve.natDegree_preΨ₄_pos`
> (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:141`). Same qualified
> name, same `WeierstrassCurve` namespace, same `preΨ₄` definition (mathlib's), same statement,
> same proof. The whole project file `DivisionPolynomialDegree.lean` is a copy of mathlib's
> `Degree.lean` (its own docstring says so).

---

### Baseline (Phase 0)
- lake build:               (not re-run; local build stale per task brief) — reasoning from source
- decl `WeierstrassCurve.natDegree_preΨ₄_pos`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:137`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  "Division polynomials of Weierstrass curves … (a project copy of
  mathlib's Basic file)." Computes leading terms/degrees of `preΨₙ`, `ΨSqₙ`, `Φₙ`.

---

### Statement (Phase 1)

`WeierstrassCurve.natDegree_preΨ₄_pos` states: for a Weierstrass curve `W` over a commutative ring
`R`, if `2 ≠ 0` in `R`, then the auxiliary 4th pre-division-polynomial `preΨ₄ ∈ R[X]` has strictly
positive `natDegree`.

`preΨ₄` is the (computable, normalised) polynomial part of the 4th division polynomial — concretely
the degree-6 polynomial whose leading coefficient is `2` and degree is `(4² − 4)/2 = 6`. Positivity
of the degree is an immediate corollary of the exact degree being `6`.

Variables / typeclasses involved (Lean side):
- `{R : Type u}` `[CommRing R]` — the base ring.
- `(W : WeierstrassCurve R)` — a Weierstrass curve (mathlib's `WeierstrassCurve` structure).

Hypotheses (Lean side):
- `(h : (2 : R) ≠ 0)` — needed so the leading coefficient `2` is nonzero, pinning the degree at `6`.

Conclusion (math): `deg(preΨ₄) > 0`.
Conclusion (Lean): `0 < W.preΨ₄.natDegree`.

Proof body (verbatim, both project and mathlib):
```lean
lemma natDegree_preΨ₄_pos (h : (2 : R) ≠ 0) : 0 < W.preΨ₄.natDegree := by
  linarith only [W.natDegree_preΨ₄ h]
```
i.e. it just reads off `0 < 6` from the exact-degree lemma `natDegree_preΨ₄ : … natDegree = 6`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step positivity corollary of an exact-degree computation; a helper lemma, not a
main result, not named after a person/place, introduces no new structure.

(Note: literature width is EXHAUSTIVE regardless; recorded for framing only.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — one-liner def check is **n/a**. (The body is a
single `linarith only` tactic line, but the one-liner gate concerns definitions, not lemmas.)

---

## PHASE 3 — Literature search

This lemma is internal degree bookkeeping ("the 4th pre-division-polynomial has positive degree")
— the *mathematically interesting* statement is the surrounding degree/leading-coefficient
computation, which is classical (Silverman, *Arithmetic of Elliptic Curves*, Exercise 3.7 / §III).
The literature sweep targets that surrounding fact; the positivity itself is a `0 < 6` triviality.

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | division polynomial elliptic curve degree ψₙ leading coeff (n²−1)/2 Silverman          | yes  | ψₙ²: deg n²−1, lead n²; φₙ: deg n², lead 1; ψₙ: deg (n²−1)/2 | classical; Silverman V.4 / III.3.7 |
|  2 | WebSearch (general form)         | (same sweep returned the general degree formulas for all ψₙ, ψₙ², φₙ)                  | yes  | general n formulas  | the n=4 `preΨ₄` (deg 6) is one instance |
|  3 | WebSearch (named-after / aliases)| "division polynomial" / "Weierstrass division polynomial" degree                       | yes  | same                | concept name stable: "division polynomial" |
|  4 | ChatGPT MCP                      | n/a — MCP down per task brief; covered by #1–#3 + the in-repo Silverman citation       | n/a  | —                   | docstring cites [silverman2009] directly |
|  5 | Local references                 | grep `.mathlib-quality/references/` for division polynomial / degree                   | n/a  | (no references dir for this concept) | file's own `## References` cites Silverman |
|  6 | nLab                             | "division polynomial"                                                                  | n/a  | —                   | not an nLab-style categorical concept; nLab has no division-polynomial page |
|  7 | nCatLab                          | —                                                                                     | n/a  | —                   | not a categorical concept |
|  8 | Stacks Project                   | —                                                                                     | n/a  | —                   | elliptic-specific arithmetic, not in Stacks' scope |
|  9 | MathOverflow / MSE               | division polynomial degree positivity                                                 | n/a  | —                   | a `0 < 6` corollary is below MO/MSE granularity; the parent degree formula is textbook |
| 10 | recent arXiv (last 5 yrs)        | coefficients of division polynomials (1303.5002, jtnb.881, 1801.02664, …)              | yes  | confirms general degree/leading-coeff formulas | modern work assumes these as standard |

### Literature summary (Phase 3)

Concept identified as: **division polynomials of an elliptic / Weierstrass curve** (the normalised
"pre" variant `preΨₙ` is mathlib's own bookkeeping name for the polynomial part).
Sources agree on the standard form: **yes** — for `n` even, `preΨₙ` has degree `(n²−4)/2` and leading
coefficient `n/2`; for `n=4` that is degree `6`, leading coefficient `2`. The *positivity* corollary
is not stated as a named result anywhere because it is the trivial `0 < 6`.
Most general standard form: the full family `natDegree_preΨ {n : ℤ}` (already in mathlib, see Phase 5)
subsumes this `n=4` instance.
Disagreement with the literature: none.

---

## PHASE 4 — Generality analysis

### Generality analysis — `WeierstrassCurve.natDegree_preΨ₄_pos`

Literature-standard form: the degree/positivity statement for **general `n`**, not the hard-coded
`n=4`. Mathlib already provides exactly this general form: `natDegree_preΨ'_pos {n : ℕ} (hn : 2 < n)`
and `natDegree_preΨ_pos {n : ℤ} (hn : 2 < n.natAbs)`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | index fixed at `4`     | the single `preΨ₄` | general `preΨ n`         | yes — already in mathlib | `natDegree_preΨ_pos` covers all `2 < n.natAbs` |
| 2 | `(h : (2:R) ≠ 0)`      | `2 ≠ 0`            | `(n:R) ≠ 0`              | (this is the right hyp for n=4) | for n=4 the relevant char is 2 |
| 3 | `[CommRing R]`         | comm ring          | comm ring (same)         | NO                  | mathlib's general lemma uses the same |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is the `n=4` specialisation), **but**
mathlib already contains BOTH the narrow `n=4` lemma *and* the general-`n` lemma. So this is not a
"generalise-first" opportunity — it is pure duplication. → Phase 7 bucket is NO-mathlib-has-it, not
YES-but-generalise-first.

Number of weakening opportunities: 0 actionable (the general form already exists upstream).
Cost of restatement: n/a (nothing to restate; mathlib has both forms).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Notes |
|---|----------|----------|-------|
| 1 | typeclass-ify "let W be a foo" preamble? | no | `WeierstrassCurve R` is already the bundled mathlib structure |
| 2 | sequences→filters? | no | finite-degree statement; no limits |
| 3 | construction→universal property? | no | concrete polynomial degree |
| 4 | set+closure→bundled substructure? | no | n/a |
| 5 | vector-space/field→weaker typeclass? | no | already `CommRing`, the mathlib-general base |
| 6 | 1-categorical→higher? | no | n/a |
| 7 | concrete index ℕ/ℤ/ℝ → general additive structure? | **yes (already done upstream)** | mathlib's `natDegree_preΨ_pos {n : ℤ}` is exactly the index-generalised form; the project's `_preΨ₄_` is the `n=4` slice |

Modern idiom available: **no new move** — the index-generalisation row is already realised in
mathlib (`natDegree_preΨ_pos`). Nothing for this project to contribute.

(Phase 4.5 diamond/defeq risk: **n/a** — declaration kind is `lemma`.)

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `WeierstrassCurve.natDegree_preΨ₄_pos`

[A] Lean-Finder       n/a (index queries skipped; direct source hit found) — see [D]
[B] Loogle            `0 < Polynomial.natDegree (WeierstrassCurve.preΨ₄ _)` — subsumed by direct hit
[C] LeanSearch        "natDegree of preΨ₄ positive" — subsumed by direct hit
[D] **Grep mathlib src** `natDegree_preΨ₄_pos` in `.lake/packages/mathlib/` → **EXACT HIT** at
    `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:141`
[E] Name pattern      `natDegree_preΨ₄_pos` / `natDegree_preΨ_pos` → both present in the same mathlib file

Searched for both:
  - the user's current form (`preΨ₄`, n=4) → mathlib `Degree.lean:141`, **identical** (same name,
    namespace, signature, proof — verified byte-for-byte with `diff`, no difference)
  - the general form (`preΨ n`) → mathlib `Degree.lean:302` `natDegree_preΨ_pos {n : ℤ}
    (hn : 2 < n.natAbs) (h : (n:R) ≠ 0) : 0 < (W.preΨ n).natDegree`

Concluded: **found in mathlib as `WeierstrassCurve.natDegree_preΨ₄_pos`; identical form** (and the
strictly more general `WeierstrassCurve.natDegree_preΨ_pos` is also present). The entire project file
`DivisionPolynomialDegree.lean` is a verbatim fork of mathlib's `Degree.lean` — 37 of these
degree/coeff/leadingCoeff bookkeeping lemmas are copied, all matching mathlib names.

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `WeierstrassCurve.natDegree_preΨ₄_pos`

Internal use count (excluding the declaring file): **0**
External-to-file callers: **0** distinct files (the file is imported by 4 downstream files —
`GeneralIntegralMultiple`, `PIDPrimeOrder`, `PIDIntegralMultiple`, `GeneralPrimeOrder` — but none
reference *this* lemma).

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none in project) | — |
| `DivisionPolynomialDegree.lean:145` (declaring file, not counted) | `ne_zero_of_natDegree_gt <| W.natDegree_preΨ₄_pos h` (inside `preΨ₄_ne_zero`) |

Inline-derivation grep: (none) — no site re-derives `0 < preΨ₄.natDegree` by hand.

Signal: **K = 0 external uses.** The lemma exists only because it was copied wholesale with the rest
of mathlib's Degree.lean; it has no project-specific consumer. Per the call-sites table, this is a
verbatim-fork wrapper that consumers bypass — combined with the Phase 5 exact mathlib hit, the case
for NO-mathlib-has-it is maximal.

### Composition check (Phase 6)

Trivially derivable from mathlib in **1 call**: it *is* a mathlib lemma. If one preferred not to
keep the n=4 form at all, the general mathlib lemma gives it directly:
```lean
example {R} [CommRing R] (W : WeierstrassCurve R) (h : (2 : R) ≠ 0) :
    0 < W.preΨ₄.natDegree :=
  W.natDegree_preΨ₄_pos h                 -- the mathlib lemma itself
-- or from the exact-degree mathlib lemma:
--   by linarith only [W.natDegree_preΨ₄ h]   (mathlib `natDegree_preΨ₄`)
```
Conclusion: **COMPOSABLE / already-present** — but the dominant fact is that mathlib *has the lemma
itself*, so the verdict is NO-mathlib-has-it (the stronger NO), not NO-composable.

---

## Verdict: `WeierstrassCurve.natDegree_preΨ₄_pos`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the surrounding degree formula is classical (Silverman §III/V.4); the
  positivity corollary is the trivial `0 < 6`, not a named result.
- Generality analysis (Phase 4): STRICTLY NARROWER (n=4 slice), but the general form is *also* already
  upstream — so duplication, not a generalise-first opportunity.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.natDegree_preΨ₄_pos`, identical
  form** (`DivisionPolynomial/Degree.lean:141`); byte-for-byte equal by `diff`. General form
  `natDegree_preΨ_pos` also present (`:302`).
- Composition check (Phase 6): K = 0 project call sites; the lemma is part of a wholesale verbatim
  fork of mathlib's Degree.lean.

**Rationale:**

This is not a borderline mathlibability question — the declaration *is already in mathlib*, under the
exact same qualified name `WeierstrassCurve.natDegree_preΨ₄_pos`, in the exact file
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`, with the same
`WeierstrassCurve` namespace, the same `preΨ₄` definition (mathlib's `noncomputable def preΨ₄`, which
the project's `DivisionPolynomial.lean` copies verbatim), the same signature `(h : (2 : R) ≠ 0) :
0 < W.preΨ₄.natDegree`, and the same proof `by linarith only [W.natDegree_preΨ₄ h]`. A `diff` of the
two lines shows no difference. The project's own module docstring states the file is "a project copy
of mathlib's Basic file," and AINTLIB's CLAUDE.md flags this project as one that "FORKS parts of
mathlib (`…DivisionPolynomial.*`)." So the lemma is a pure fork artifact, kept only so the project's
self-contained `DivisionPolynomial`/`EllipticDivisibilitySequence` copies build without depending on
the mathlib originals.

Mathlib additionally carries the strictly more general `natDegree_preΨ_pos {n : ℤ} (hn : 2 < n.natAbs)`
(`Degree.lean:302`), of which the `preΨ₄` lemma is the `n = 4` specialisation — so even if mathlib
lacked the n=4 form, the n=4 statement would follow from the general one. But mathlib has *both*. The
lemma has zero call sites in the NagellLutz project (only the adjacent `preΨ₄_ne_zero` uses it inside
the same forked file), so nothing project-specific depends on the local copy.

**WHY not (refactor-actionable):**
Mathlib already proves this exact lemma. The local copy exists purely because `DivisionPolynomialDegree.lean`
re-derives mathlib's `Degree.lean` so the project's forked `DivisionPolynomial`/`EllipticDivisibilitySequence`
basics are self-contained. The right long-term move is to **drop the fork and import mathlib's
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`** once the project's reasons for
forking (the EDS-track divergence noted in `DivisionPolynomial.lean:13`) are resolved upstream — at which
point this lemma, and the other 36 copied degree/coeff lemmas in the file, all disappear in favour of the
mathlib originals.

Existing mathlib decl:        `WeierstrassCurve.natDegree_preΨ₄_pos`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:141`
More general mathlib decl:    `WeierstrassCurve.natDegree_preΨ_pos`  (`…/Degree.lean:302`)
Our form follows in 0 lines (it is literally the same lemma):
```lean
example {R} [CommRing R] (W : WeierstrassCurve R) (h : (2 : R) ≠ 0) :
    0 < W.preΨ₄.natDegree := W.natDegree_preΨ₄_pos h   -- mathlib's lemma
```
Call sites in our project (from Phase 6.0):  **0** (outside the declaring file).
Refactor plan:
1. This is a whole-file fork issue, not a single-lemma issue. The actionable unit is the file
   `DivisionPolynomialDegree.lean` (and its sibling forked basics): once the project no longer needs
   its private `DivisionPolynomial`/`EllipticDivisibilitySequence` copies, delete `DivisionPolynomialDegree.lean`
   and `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` instead.
2. No call-site rewrites are needed for *this* lemma (K = 0). The only in-file consumer,
   `preΨ₄_ne_zero`, is itself a verbatim mathlib duplicate (`Degree.lean:148`) and is removed with the file.
3. Until the fork is retired, leave the lemma as-is — it is correct and matches mathlib exactly; there is
   no per-lemma cleanup to do.

Next action: track this under the project's "retire the mathlib `DivisionPolynomial` fork" effort;
do **not** open a mathlib PR (mathlib already has it). No standalone refactor for this single lemma.

---

## Next step

Track under the project-level effort to retire the verbatim fork of mathlib's `DivisionPolynomial`
files; replace `import LutzNagell.DivisionPolynomialDegree` with the mathlib Degree import once the
EDS-track divergence is resolved. No mathlib PR — `WeierstrassCurve.natDegree_preΨ₄_pos` is already in
mathlib at `DivisionPolynomial/Degree.lean:141`.
