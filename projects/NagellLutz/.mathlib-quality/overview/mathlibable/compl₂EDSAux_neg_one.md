# Mathlibable assessment — `compl₂EDSAux_neg_one`

**Verdict: BORDERLINE-needs-human** (strongly leaning NO)
**Qualified name:** `compl₂EDSAux_neg_one` (root namespace — no enclosing `namespace`)
**Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1021`
**Date:** 2026-06-21 (re-run; independently re-verified every load-bearing claim against the
repo-pinned mathlib `09b373db6e24` at `.lake/packages/mathlib/`)

---

## 0. The declaration (verified from source)

```lean
section Complement
variable (b c d : R) (m : ℤ)

/-- An auxiliary expression that appears in the definition of the numerator of
the reduced invariant and in the definition of the `ω` family of division polynomials. -/
def compl₂EDSAux : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * if Even m then 1 else b

@[simp] lemma compl₂EDSAux_zero    : compl₂EDSAux b c d 0    = -1 := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_one     : compl₂EDSAux b c d 1    = -b := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_neg_one : compl₂EDSAux b c d (-1) = 0  := by simp [compl₂EDSAux]  -- ← TARGET (line 1021)
@[simp] lemma compl₂EDSAux_two     : compl₂EDSAux b c d 2    = 0  := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_neg_two : compl₂EDSAux b c d (-2) = -d := by simp [compl₂EDSAux]
```

- **Qualified-name check.** Line 1021 sits inside `section Complement` (line 1010) inside the file's
  `@[expose] public section` (line 81) — both are `section`s, which add **no** namespace prefix. The
  enclosing `namespace EllSequence` blocks close before this point (`end EllSequence` at line 597) and
  the next one opens *after* it (line 1079). So the fully-qualified name is exactly
  **`compl₂EDSAux_neg_one`** (root namespace). The parsed name in the task is correct.
- **Kind:** `@[simp] lemma`. **Has sorry:** no.
- **What it says.** Evaluation of the project-local `def compl₂EDSAux` at the fixed integer `m = -1`:
  the result is `0`. The zero arises because the middle factor is
  `preNormEDS (b^4) c d ((-1)+1)^2 = preNormEDS (b^4) c d 0 ^ 2 = 0^2 = 0` (via `preNormEDS_zero`),
  which annihilates the product regardless of the parity factor `b` (`m=-1` is odd, so the parity
  factor is `b`). One-line `simp [compl₂EDSAux]` proof. Mathematically it is a numeral evaluation with
  no independent standing.
- **Role.** `compl₂EDSAux b c d m` is the single product term `W(m-2)·W(m+1)²` up to the parity factor
  `b` (project lemma `compl₂EDSAux_mul_b`, line 1025: `compl₂EDSAux·b = W(m-2)·W(m+1)²`). It is the
  **subtrahend half** of the EDS 2-complement bracket. Downstream it feeds (i) `redInvarNum`
  (line 1359, the reduced-invariant numerator) and (ii) `WeierstrassCurve.ω` (DivisionPolynomialOmega
  .lean:78, the division-free ω division polynomial). These five `@[simp]` eval lemmas
  (`compl₂EDSAux_zero/one/neg_one/two/neg_two`) are the boundary-value API of that def.

---

## 1. Literature search

- WebSearch ("elliptic divisibility sequence 2-complement preNormEDS division polynomial omega Stange
  auxiliary product term W(m-2) W(m+1)^2"). Hits: mathlib4 docs for
  `Mathlib.NumberTheory.EllipticDivisibilitySequence` and `…/DivisionPolynomial/Basic`, the EDS
  Wikipedia page, Stange "Division polynomials for arbitrary isogenies" (eprint 2025/521), and the
  EDS/ECDLP literature (eprint 2008/444; Warwick CM-EDS notes).
- **Finding.** The *concepts* — a normalised EDS, its 2-complement `W(2m)/W(m)` witnessing
  `W(m) ∣ W(2m)`, and the `ωₙ` division polynomial — are standard (Ward / Shipsey / Stange / Wikipedia).
  The literature uniformly names the **whole bracket** `ψ_{n-1}²ψ_{n+2} − ψ_{n-2}ψ_{n+1}²` and the
  complement; it **never** separately names the single subtrahend product `ψ_{n-2}ψ_{n+1}²` (=
  `compl₂EDSAux·b`). So `compl₂EDSAux` is a Lean-implementation convenience with no named literature
  counterpart, and the specific fact "value at `m=-1` is `0`" is a numeral evaluation with no
  independent mathematical content. No `--exhaustive` deep sweep is warranted for a trivial `@[simp]`
  eval lemma. (The def-level report `compl₂EDSAux.md` ran the full EXHAUSTIVE sweep — nLab / Stacks /
  MathOverflow / arXiv ≤5yr — and reached the same conclusion: the named atoms are `ω_n` / the full
  bracket / the complement, never the half-term.)

Sources:
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html
- https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence
- https://eprint.iacr.org/2025/521.pdf
- https://eprint.iacr.org/2008/444.pdf

---

## 2. Mathlib search (five methods) — re-verified against `09b373db6e24`

This NagellLutz file is an explicit **fork** of `Mathlib.NumberTheory.EllipticDivisibilitySequence`
(same header, `Authors: David Kurniadi Angdinata`, ~1667 lines vs mathlib's ~547). So mathlib was
checked directly against the *pinned* tree under `.lake/packages/mathlib/`.

1. **Name grep — the symbol.** `grep -rln "compl₂EDSAux" .lake/packages/mathlib/Mathlib/` → **no files,
   exit 1**. `compl₂EDSAux` does **not exist anywhere in mathlib**. (Re-verified this run.)
2. **`*EDSAux` companion grep.** `grep -rln "EDSAux"` over all of mathlib → **no files, exit 1**.
   Mathlib has **no** split-out auxiliary for the 2-complement under any spelling. (Re-verified.)
3. **The parent definition IS in mathlib, but whole.** `complEDS₂`
   (`…/EllipticDivisibilitySequence.lean:246`):
   ```lean
   def complEDS₂ (k : ℤ) : R :=
     (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
       preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b
   ```
   This is **line-for-line** the project's own `compl₂EDS` (lines 1031–1033), and its subtrahend
   `preNormEDS (b^4) c d (k-2) * preNormEDS (b^4) c d (k+1)^2 * (parity b)` is **exactly the body of
   `compl₂EDSAux`**. Mathlib keeps the complement as a single subtraction and **never names the
   individual summand**. (Verified the byte-level body this run.)
4. **Evaluation lemmas for the parent.** Mathlib has `complEDS₂_zero/one/two/three/four`
   (lines 251–269) and `complEDS₂_neg` (272), plus `complEDS₂_mul_b` (329),
   `preNormEDS_mul_complEDS₂` (276), `normEDS_mul_complEDS₂` (321). So mathlib **does** provide
   `@[simp]` boundary evals — but for the *consolidated* `complEDS₂`, with **no** "Aux"-summand
   analogue of `compl₂EDSAux_neg_one` (because no such summand exists upstream). (Verified this run.)
5. **lean_loogle / lean_leansearch (mathlib index).** A query for a lemma of shape
   `compl…Aux … (-1) = 0` over the EDS namespace returns nothing — consistent with (1)–(4): the indexed
   mathlib carries `complEDS₂_*` only.

Adjacent fact confirming the design tension: `ωₙ` is an **explicit mathlib TODO**
(`DivisionPolynomial/Basic.lean:71,83`), and mathlib's own docstring defines it as
`ωₙ := (ψ₂ₙ/ψₙ − ψₙ·(a₁φₙ + a₃ψₙ²))/2` (line 30) — i.e. routed through `ψ₂ₙ/ψₙ` (the complement),
**not** through a named subtrahend. (Verified this run.)

**Conclusion of search.** The target lemma's statement *mentions a symbol mathlib does not have*
(`compl₂EDSAux`). Therefore:
- `NO-mathlib-has-it` is **impossible** — the lemma cannot already be in mathlib because its very
  statement is not expressible there.
- Mathlib's visible **design choice** is the opposite of this project's: expose the full `complEDS₂`,
  with its boundary evals, and *deliberately not* factor out `compl₂EDSAux`.

---

## 3. Generality analysis

Nothing to generalise. The statement is an evaluation at a *fixed numeral* (`m = -1`) of a fully-applied
definition over an arbitrary `[CommRing R]` with free `b c d : R`. It is already maximally general in
its parameters (the `preNormEDS` `b⁴`-reduced, division-free form is the modern `CommRing`-general
idiom mathlib itself adopted); specialising the index to a constant is the entire point. There is no
weaker-hypothesis or more-general-form variant to seek. The mechanical "generalise the index" move just
reproduces the parent identities `compl₂EDSAux_neg` (line 1035) / `compl₂EDSAux_mul_b` (line 1025),
which already sit adjacent in the file. (4b: 0 weakening opportunities. 4c: already the modern idiom.)

---

## 4. Composition check (≤ 3 mathlib calls)

Can mathlib's primitives give this lemma? **No — for a structural reason, not a difficulty reason.**

The obstruction is that the *subject* of the lemma, `compl₂EDSAux`, is not a mathlib object. You cannot
state, let alone prove, `compl₂EDSAux b c d (-1) = 0` using only mathlib, because mathlib has no
`compl₂EDSAux`. The underlying arithmetic *is* a ≤3-step `simp` (`compl₂EDSAux` unfold →
`preNormEDS_zero` kills the `(m+1)^2 = 0^2` factor → `mul_zero`/`zero_mul`), and every primitive it uses
(`preNormEDS`, `preNormEDS_zero`, `Even`, `mul_zero`) is in mathlib. So this is **not** a case of
"mathlib primitives compose to give a missing fact" — it is a one-line consequence *of a definition that
lives only in this project*. `NO-composable-from-mathlib` does not fit: that bucket is for facts mathlib
*could* state but happens not to record; here mathlib cannot even *state* it.

(The cleaner upstream route — derive the boundary value from `complEDS₂` instead — would still not yield
*this* lemma; it would yield `complEDS₂`-level facts. Under mathlib's `ψ₂ₙ/ψₙ` phrasing of `ωₙ`, the
subtrahend `compl₂EDSAux` is subsumed by `complEDS₂` and the lemma simply would not exist.)

---

## 5. Five-bucket verdict

| Bucket | Fits? | Why |
|---|---|---|
| YES-add-as-is | ✗ (conditionally) | It is a `@[simp]` micro-eval of a **project-internal `def`** (`compl₂EDSAux`) that mathlib intentionally does not have. Adding this lemma alone is meaningless without first adding the def — and mathlib chose to keep only the consolidated `complEDS₂`, not its summands. It would only ship **bundled** with `compl₂EDSAux` *if* the ω-PR keeps the division-free definition (see below). |
| YES-but-generalise-first | ✗ | Nothing to generalise — fixed-numeral evaluation, already maximally general in `R, b, c, d`. |
| NO-mathlib-has-it | ✗ | Impossible: `compl₂EDSAux` is absent from all of mathlib (grep exit 1, twice, re-verified this run), so this exact lemma cannot already be there. Its **parent** `complEDS₂` and the parent's boundary evals *are* in mathlib — but there is no `complEDS₂`-named analogue of *this* (sub)lemma. |
| NO-composable-from-mathlib | ✗ | The arithmetic is a trivial ≤3-step `simp`, but it is about a symbol mathlib does not define; mathlib's primitives cannot even *state* it. |
| **BORDERLINE-needs-human** | **✓** | The lemma's fate is **entirely bound to the def `compl₂EDSAux`**, whose disposition is itself BORDERLINE: it is genuinely absent from mathlib, but mathlib already owns the consolidated equivalent `complEDS₂` (whole, with its own boundary evals) and the `ωₙ` it feeds is an explicit TODO defined via `ψ₂ₙ/ψₙ` (i.e. *through* the complement, not a named subtrahend). Whether upstream `ω` keeps the project's division-free definition (which names `compl₂EDSAux`, so these five evals ship as its bundle) or rides on the already-upstream `complEDS₂` (so `compl₂EDSAux` and this lemma are subsumed) is an **API-design decision for the ω-PR author** — a human call. |

### Recommendation to the human

**Do not upstream this lemma in isolation, and most likely not at all.** Mathlib already provides the
2-complement as `complEDS₂` together with its `@[simp]` boundary evals
(`complEDS₂_zero/one/two/three/four`, `complEDS₂_neg`) and the value relation `complEDS₂_mul_b`,
covering the divisibility-witness role *without* exposing the individual summand `compl₂EDSAux`. The
NagellLutz `compl₂EDSAux` track is a local refactor that splits out one summand to streamline the
reduced-invariant / `ω`-division-polynomial development; that split is useful **inside this project** but
duplicates, in more granular form, machinery mathlib deliberately keeps consolidated.

This lemma travels — or does not — **as a bundle** with `compl₂EDSAux` and its four siblings
(`compl₂EDSAux_zero/one/two/neg_two`), and that bundle ships only if the def itself is upstreamed. The
single decision that fixes everything:

1. If `WeierstrassCurve.ω` is upstreamed with the project's **current division-free definition** (which
   names `compl₂EDSAux` as a subterm), then `compl₂EDSAux` + these five `@[simp]` evals ship **with that
   ω PR** as supporting API (grouped with `redInvarDenom`, `compl₂EDS`/`complEDS₂`, `redInvarNum`,
   `two_mul_ω`, `map_ω`, discharging the `DivisionPolynomial/Basic.lean:71,83` TODO) → resolves to
   **YES-add-as-is**.
2. If upstream `ω` is instead defined via mathlib's docstring formula
   `ωₙ = (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ + a₃ψₙ²))/2`, routed through `complEDS₂`/`complEDS₂_mul_b`, then
   `compl₂EDSAux` is **subsumed** and this eval lemma vanishes → effectively **NO** (subsumed by the
   already-upstream `complEDS₂`).

**Net:** BORDERLINE-needs-human, strongly leaning NO — mathlib has the consolidated equivalent
(`complEDS₂`) and has not adopted the split-out auxiliary; this is a `@[simp]` boundary value of that
non-upstream split, so it lives or dies with the ω-PR design decision. Decide it **jointly** with the
whole `ω`-family of this fork, never for this single lemma in isolation. (Consistent with the def-level
verdict `compl₂EDSAux` → BORDERLINE and the sibling ledger.)
