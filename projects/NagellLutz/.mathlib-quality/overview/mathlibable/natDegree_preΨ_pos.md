# /mathlibable report — `WeierstrassCurve.natDegree_preΨ_pos`

**Verdict: NO-mathlib-has-it** — mathlib already has this declaration, byte-for-byte
identical, in the same namespace, by the same author. The project file is an admitted
fork of mathlib's `DivisionPolynomial/Degree.lean`.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; assessment reasons from source — does not affect this verdict, which is decided by a direct mathlib hit)
- decl `WeierstrassCurve.natDegree_preΨ_pos`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:299`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  "This file computes the leading terms of certain polynomials associated to division polynomials of Weierstrass curves … **(a project copy of mathlib's Basic file)**" — the file header (line 14) explicitly states it is a fork.

### Statement (Phase 1)

`WeierstrassCurve.natDegree_preΨ_pos` states: for a Weierstrass curve `W` over a
commutative ring `R` and an integer `n` with `|n| > 2` whose image in `R` is nonzero,
the `n`-th pre-division polynomial `preΨₙ ∈ R[X]` has strictly positive degree.

Mathematically: the auxiliary division polynomial `preΨₙ` (the part of the division
polynomial `Ψₙ` stripped of the `Ψ₂`-factor parity correction) is non-constant once
`|n| ≥ 3`, provided the characteristic of `R` does not divide `n`. This is the
positive-degree corollary of the exact degree formula
`deg preΨₙ = (n² − (4 if n even else 1)) / 2`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the base commutative ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve (carries the `aᵢ` coefficients).
- `{n : ℤ}` — the multiplication index.

Hypotheses (Lean side):
- `(hn : 2 < n.natAbs)` — `|n| > 2`, i.e. `n ∉ {−2,−1,0,1,2}`.
- `(h : (n : R) ≠ 0)` — `n` is nonzero in `R` (char `R ∤ n`).

Conclusion (math): `deg preΨₙ > 0`.
Conclusion (Lean): `0 < (W.preΨ n).natDegree`.

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a positivity corollary of the degree formula `natDegree_preΨ`; a helper lemma
(used in mathlib to derive `preΨ_ne_zero`), not a named theorem or a structure.

### One-line check (Phase 2b)

n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`. (No defeq/diamond/API surface.)

### Literature search (Phase 3)

**This phase is short-circuited by a decisive mathlib hit (Phase 5).** When mathlib
already contains the *byte-identical* declaration in the *same namespace*, the
literature-standard-form question is moot: the lemma's "standard form" is, definitionally,
the mathlib form it was copied from. The minimal channels below were nonetheless run.

| # | Channel                 | Query                                                                                  | Hit? | Finding |
|---|-------------------------|----------------------------------------------------------------------------------------|------|---------|
| 1 | WebSearch (specific)    | "mathlib WeierstrassCurve division polynomial natDegree preΨ degree DivisionPolynomial Degree.lean" | yes  | Top hit is the mathlib doc page for `…DivisionPolynomial.Degree`; lists `natDegree_preΨ_le`, `natDegree_preΨ`, `leadingCoeff_preΨ`, etc. |
| 2 | WebFetch (mathlib docs) | fetched `…/DivisionPolynomial/Degree.html`                                              | yes  | Confirms `WeierstrassCurve.natDegree_preΨ_pos {n : ℤ} (hn : 2 < n.natAbs) (h : ↑n ≠ 0) : 0 < (W.preΨ n).natDegree` — **identical signature**. |
| 3 | Source reference        | file docstring cites [Silverman, *The Arithmetic of Elliptic Curves*]; division polynomials Ψₙ, Exercise 3.7 | yes  | Division polynomials are classical (Silverman III; Lang, *Elliptic Curves*). preΨ is mathlib's own bookkeeping split of Ψ; the positive-degree fact is a triviality once the degree is computed. |
| 4 | ChatGPT MCP             | (not required — mathlib hit is decisive; MCP noted as possibly-down in task)            | n/a  | Skipped: no standard-form ambiguity to resolve once the identical mathlib decl is found. |
| 5 | Local references        | no `.mathlib-quality/references/` PDFs needed for this verdict                          | n/a  | The decl is a direct fork; provenance is in the file header itself. |
| 6 | nLab / Stacks / nCatLab | —                                                                                      | n/a  | Not a categorical/scheme-theoretic concept at the level of this helper lemma; the underlying object (division polynomial) is classical, already in mathlib. |

#### Literature summary (Phase 3)

Concept identified as: degree-positivity of the (pre-)division polynomial `preΨₙ` of a
Weierstrass curve — a corollary of the classical degree formula for division polynomials
(Silverman, *Arithmetic of Elliptic Curves*, III). Mathlib's `preΨ` is its own
normalisation; the lemma is mathlib-internal API. Sources agree; no generality variance
relevant here because the question is settled by the identical mathlib declaration.

### Generality analysis (Phase 4)

**Moot — mathlib has the identical statement.** For completeness: the project form is
already at mathlib's chosen generality (`[CommRing R]`, `n : ℤ`, hypotheses `2 < n.natAbs`
and `(n : R) ≠ 0`). There is nothing to weaken relative to mathlib because the project
copied mathlib verbatim. Generality verdict: SAME-AS-MATHLIB (not a candidate for
YES-but-generalise-first). Modern-idiom check (4c): n/a — no reformulation is owed for a
lemma that is already the upstream lemma.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional content, no instance/coercion).

### Mathlib search (Phase 5)

| Method | Query | Result |
|--------|-------|--------|
| [D] Grep vendored mathlib | `grep -rn natDegree_preΨ_pos .lake/packages/mathlib/Mathlib/` | **HIT** — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:302` |
| [D] Grep (whole machine)  | `grep -rn natDegree_preΨ_pos / --include=*.lean` (excl. project) | only the project copy + the vendored mathlib copy; no third instance |
| [C] WebSearch / docs      | mathlib4_docs `DivisionPolynomial/Degree.html`                  | **HIT** — page documents `WeierstrassCurve.natDegree_preΨ_pos` with identical signature |
| [E] Name pattern          | declaration-head diff of project fork vs mathlib `Degree.lean`  | `diff` exit code 0 — **all declaration heads identical** (whole file is a verbatim fork) |
| [A]/[B] Lean-Finder/Loogle| (not needed — exact-name grep + published docs already pin the hit) | n/a |

Searched for both the project's current form and the (identical) mathlib form.

Concluded: **found in mathlib as `WeierstrassCurve.natDegree_preΨ_pos`; identical form**, at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:302`. The mathlib
statement is byte-for-byte the project statement. The only textual difference is in the
*proof body*: current mathlib uses the `using!` term-mode-elaboration tactic syntax
(`simpa only [preΨ_ofNat] using! W.natDegree_preΨ'_pos hn …`) whereas the project copy
uses `using` — a cosmetic skew introduced by mathlib's daily evolution since the fork was
taken, not a difference in the statement or its mathematical content.

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.natDegree_preΨ_pos`

Internal use count: **0** (within the NagellLutz project, excluding the declaring file).
External-to-file callers: 0 distinct files.

Machine-wide grep finds the symbol in exactly two places: the project's declaring file
and the vendored mathlib `Degree.lean`. There are no consumers anywhere in the NagellLutz
project. (Inside the fork file itself, the analogous parent lemma `natDegree_preΨ'_pos` is
referenced by `preΨ'_ne_zero`/`preΨ_ne_zero`, mirroring mathlib — but `natDegree_preΨ_pos`
itself is not invoked by any other project file.)

Inline-derivation grep: (none) — no file re-derives this statement.

#### Composition (Phase 6)

Not applicable as a *composition-from-primitives* question: the lemma is not "a 1–3 mathlib-
call composition of building blocks", it is **the mathlib lemma itself**. The correct
classification is NO-mathlib-has-it, not NO-composable-from-mathlib. (For reference, were one
re-deriving it from the project's own degree formula, it is a one-liner:
`by simpa [W.natDegree_preΨ h] using …` after `natDegree_preΨ` — exactly mathlib's proof —
but that is irrelevant since the whole result is already upstream.)

Conclusion: mathlib HAS IT.

---

## Verdict: `WeierstrassCurve.natDegree_preΨ_pos`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): mathlib4 doc page for `DivisionPolynomial/Degree` lists the lemma; division polynomials are classical (Silverman III), `preΨ` is mathlib-internal API.
- Generality analysis (Phase 4): SAME-AS-MATHLIB — the project copied mathlib's generality verbatim; nothing to weaken.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.natDegree_preΨ_pos`; **identical form**; `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:302`.
- Composition check (Phase 6): mathlib HAS IT; 0 call sites in the project.

**Rationale:**

The NagellLutz project forks mathlib's elliptic-curve division-polynomial files into
`LutzNagell/DivisionPolynomial.lean` (copy of `…DivisionPolynomial/Basic`) and
`LutzNagell/DivisionPolynomialDegree.lean` (copy of `…DivisionPolynomial/Degree`). The
file header (line 14) states this outright: "a project copy of mathlib's Basic file". A
declaration-head `diff` of the project's `Degree` fork against mathlib's `Degree.lean`
returns exit code 0 — every lemma signature is identical — and the specific lemma
`natDegree_preΨ_pos` matches mathlib at `Degree.lean:302` with the exact signature
`{n : ℤ} (hn : 2 < n.natAbs) (h : (n : R) ≠ 0) : 0 < (W.preΨ n).natDegree`, confirmed both
in the locally vendored mathlib and on the public mathlib4 docs page. This is not "a more
general mathlib form we'd specialise from" nor "building blocks that compose" — it is the
same author's same lemma, already in mathlib. The only divergence is a proof-body `using` →
`using!` skew from mathlib's daily churn, which does not touch the statement.

Because mathlib already contains the identical declaration, the literature / generality /
modern-idiom phases are moot: there is nothing to add and nothing to generalise. The lemma
has zero call sites within the NagellLutz project, so removing the fork in favour of mathlib
imports costs nothing locally.

**WHY not (refactor-actionable):**
Mathlib already has it, verbatim. The NagellLutz fork of the division-polynomial degree API
exists only because the project predates (or pins behind) the mathlib version it was copied
from, or needs a couple of *additional* downstream lemmas this file does not itself contain.
The right move is to stop vendoring the duplicated mathlib content and depend on the upstream
files.

  Existing mathlib decl:        `WeierstrassCurve.natDegree_preΨ_pos`
  Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:302`
  Our form follows in ≤1 line:  it *is* the mathlib lemma — `exact W.natDegree_preΨ_pos hn h` (after `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`).
  Call sites in our project (from Phase 6.0):  K = 0

  Refactor plan:
  1. Delete `natDegree_preΨ_pos` (and the rest of the duplicated `preΨ`/`ΨSq`/`Φ` degree
     API) from `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean`.
  2. Replace the two fork files
     (`LutzNagell/DivisionPolynomial.lean`, `LutzNagell/DivisionPolynomialDegree.lean`)
     with `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` and
     `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`.
  3. Because the namespace is the same (`WeierstrassCurve`) and the names are identical,
     no call-site edits are needed for `natDegree_preΨ_pos` specifically (K = 0). Any other
     project files that consumed the fork's `WeierstrassCurve.*` degree lemmas resolve
     against the mathlib versions unchanged.
  4. Keep in the project *only* the genuinely-new lemmas (if any) that the fork added on top
     of mathlib's API, and import the rest from mathlib.

  Caveat for the refactor worker: the fork may have been taken to pin a *specific* mathlib
  commit while the project needed an as-yet-unmerged extension. Before deleting, confirm the
  currently-pinned mathlib (`rev = 69aaaa313f44` in `lakefile.toml`) actually exports these
  files (it does — they are present in `.lake/packages/mathlib/…/DivisionPolynomial/`), and
  diff the *whole* fork file against mathlib's to surface any project-only additions worth
  preserving. (Note: this is a producer/dedup action on a `dev/<project>` branch or a
  cleanup ticket on `main`; per AINTLIB rules, `sorry`-free dedup like this is fleet-eligible.)

  Next action: delete the duplicated mathlib `Degree` content from the NagellLutz fork and
  import `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` instead; no
  call-site changes required for this lemma (K = 0).

---

## Next step

Delete `WeierstrassCurve.natDegree_preΨ_pos` from the NagellLutz fork and import it from
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` (the entire
`DivisionPolynomialDegree.lean` file is a verbatim mathlib fork — dedup the whole file, not
just this lemma). No call-site edits are needed (0 internal uses, same namespace/name).
