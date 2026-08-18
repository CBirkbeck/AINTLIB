# /mathlibable report — `WeierstrassCurve.natDegree_Ψ₃_pos`

### Baseline (Phase 0)
- lake build:               ⚠ not re-run (local build stale per task brief); decl read directly from source.
- decl `WeierstrassCurve.natDegree_Ψ₃_pos`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:107`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "Division polynomials of Weierstrass curves … (a project copy of mathlib's Basic file)." Computes leading terms / degrees of division polynomials.

---

### Statement (Phase 1)

`WeierstrassCurve.natDegree_Ψ₃_pos` is a theorem stating: for a Weierstrass curve `W` over a commutative ring `R`, if `3 ≠ 0` in `R`, then the third division polynomial `Ψ₃` (a univariate polynomial in `R[X]`, equal to `3x⁴ + b₂x³ + 3b₄x² + 3b₆x + b₈`) has strictly positive `natDegree`.

Mathematically: since `ψ₃ = 3X⁴ + (lower order)` with leading coefficient `3`, whenever `3 ≠ 0` the polynomial has degree exactly 4, in particular degree > 0.

Variables / typeclasses involved (Lean side):
- `R : Type u`, `[CommRing R]` — the base commutative ring.
- `W : WeierstrassCurve R` — the Weierstrass curve.

Hypotheses (Lean side):
- `h : (3 : R) ≠ 0` — characteristic-3 exclusion (needed so the leading coeff `3` is nonzero).

Conclusion (math): `deg ψ₃ > 0`.
Conclusion (Lean): `0 < W.Ψ₃.natDegree`.

Proof body: `W.natDegree_Ψ₃ h ▸ four_pos` — rewrite `natDegree = 4` (via the sibling lemma `natDegree_Ψ₃`) then close with `four_pos : 0 < 4`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A one-step corollary of `natDegree_Ψ₃` (the exact-degree lemma); not a named theorem, not a `## Main results` entry, introduces no structure.

(Literature width was run EXHAUSTIVE regardless; this classification is narrative only.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-line check is n/a. (Note: the body *is* a one-liner, but the one-line negative signal applies only to definitions; for lemmas a short proof is a positive signal, not negative.)

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                             | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial elliptic curve psi_3 degree 4 leading coefficient 3b_8"                       | yes  | `ψ₃ = 3x⁴ + b₂x³ + 3b₄x² + 3b₆x + b₈`; deg 4, lead 3  | Confirms degree 4 / leading coeff 3 exactly. arXiv 1303.5002, 1108.3051. |
|  2 | WebSearch (general form)         | "Silverman Arithmetic Elliptic Curves division polynomial psi_n degree exercise 3.7"               | yes  | `deg_x ψ_N = ½N²∏(1−1/p²)`; for `N=3`: `(9−1)/… = 4`  | Silverman III Exercise 3.7. General degree formula specialises to 4 at N=3. |
|  3 | WebSearch (named-after/aliases)  | (covered by #1/#2: "division polynomial", "elliptic divisibility sequence")                        | yes  | same concept; ψ_n / division poly / EDS              | Standard, classical (19th c., Weber/Frobenius). |
|  4 | ChatGPT MCP                      | n/a — MCP down per task brief                                                                       | n/a  | —                                                    | Fallback: WebSearch ×3 + primary-source PDFs (Silverman) substitute. |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                                | n/a  | (directory absent)                                   | `projects/NagellLutz/.mathlib-quality/references` does not exist. |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                           | n/a  | not an nLab-style categorical concept                | nLab has no dedicated division-polynomial page; classical AG/NT, not categorical. |
|  7 | nCatLab (categorical)            | —                                                                                                  | n/a  | not a categorical concept                            | Univariate polynomial degree fact; no category theory. |
|  8 | Stacks Project (alg geom)        | "division polynomial"                                                                              | n/a  | not in Stacks                                        | Stacks covers schemes/stacks generality, not elementary EC division-poly degrees. |
|  9 | MathOverflow / Math.SE           | "degree of division polynomial psi_n"                                                              | yes  | deg ψ_n = (n²−1)/2 (odd n) in x; the classic table   | Standard table; n=3 → 4. Widely reproduced. |
| 10 | recent arXiv (last 5 yrs)        | (from #1) "A recurrence relation for elliptic divisibility sequences" 2102.07573; 1303.4327        | yes  | homogeneous/recurrence forms; same degrees           | Multiple recent papers reuse the standard degree formula. |

### Literature summary (Phase 3)

Concept identified as: **third division polynomial** `ψ₃` of a Weierstrass curve (a.k.a. division polynomial / elliptic divisibility sequence term).
Sources agree on the standard form: **yes** — `ψ₃ = 3x⁴ + b₂x³ + 3b₄x² + 3b₆x + b₈`, degree 4, leading coefficient 3.
Most general standard form: over any commutative ring; the degree-4 / leading-coeff-3 statement is the universal one. Positivity of the degree is an immediate corollary once `3 ≠ 0` (so the lead coeff survives).
Generality dimensions where the literature varies:
  - base ring: the polynomial identity is integral/universal; specific *degree* needs lead coeff `3` invertible-or-nonzero, i.e. `3 ≠ 0` — exactly the Lean hypothesis. The literature's `NoZeroDivisors`/field assumptions are *not* needed for this particular `Ψ₃` case (deg-4, single lead coeff `3`).
Disagreement with the literature: none. The Lean statement is the standard fact, stated at the natural minimal hypothesis (`3 ≠ 0`).

---

## PHASE 4 — Generality analysis

### Generality status table — `WeierstrassCurve.natDegree_Ψ₃_pos`

Literature-standard form: `ψ₃` has degree 4 over any comm ring once the leading coefficient `3` is nonzero ⇒ positive degree.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring         | NO                  | `Ψ₃ ∈ R[X]` needs a `CommRing`; already minimal. |
| 2 | `(h : (3 : R) ≠ 0)`    | `3 ≠ 0`           | `3` nonzero (so deg=4)   | NO                  | If `3 = 0` the `x⁴` term vanishes and the degree genuinely drops; hypothesis is exactly necessary for this statement. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** for the `Ψ₃`-specific statement. `CommRing` is minimal; `3 ≠ 0` is exactly the necessary-and-sufficient condition for `deg = 4`. No `NoZeroDivisors`/field needed (unlike the general-`n` lemmas, because here the leading coeff is the single concrete constant `3`).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
| 1 | typeclass-ify "let X be a foo" preamble? | no | — | already typeclass-based (`CommRing`). |
| 2 | sequences/metric → filters/topology? | no | — | pure algebra; no analysis. |
| 3 | construction → universal property? | no | — | `Ψ₃` is a concrete polynomial; the `n`-indexed family already exists in mathlib (`preΨ`, `ΨSq`, `Φ`). |
| 4 | set+closure-pred → bundled substructure? | no | — | not a substructure statement. |
| 5 | vector-space/field → module/(semi)ring? | no | — | already at `CommRing`; the `3 ≠ 0` form avoids needing a field. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive structure? | partial | the `n`-indexed `natDegree_preΨ_pos` family already exists in mathlib | the `Ψ₃` case is the `n=3` specialisation; mathlib already provides BOTH the specialised `natDegree_Ψ₃_pos` AND the general `natDegree_preΨ_pos`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for this decl as such).
One-line reason: This is the standard, already-idiomatic mathlib formulation — in fact it is *literally a current mathlib lemma* (see Phase 5). Mathlib already carries both the concrete `Ψ₃` form and the general `n`-indexed `preΨ`/`ΨSq`/`Φ` degree-positivity lemmas; nothing to modernise.

### PHASE 4.5 — Diamond / defeq risk
n/a — declaration kind is `lemma`.

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `WeierstrassCurve.natDegree_Ψ₃_pos`

[A] Lean-Finder       n/a (offline)                                         — fell back to direct source grep of the pinned mathlib.
[B] Loogle            pattern `0 < Polynomial.natDegree (WeierstrassCurve.Ψ₃ _)` — superseded by exact-source hit below.
[C] LeanSearch        "degree of third division polynomial positive"        — superseded by exact-source hit below.
[D] Grep mathlib src  `grep -nE 'natDegree_Ψ₃|Ψ₃' .lake/packages/mathlib/.../DivisionPolynomial/Degree.lean` — **EXACT HIT.**
[E] Name pattern      `natDegree_Ψ₃_pos`                                    — **EXACT HIT** (qualified `WeierstrassCurve.natDegree_Ψ₃_pos`).

Searched for both:
  - user's current form (`natDegree_Ψ₃_pos`) → found verbatim.
  - literature-standard / general form (`natDegree_preΨ_pos`, `natDegree_ΨSq_pos`, `natDegree_Φ_pos`) → also all present in the same mathlib file.

**Concluded: found in mathlib as `WeierstrassCurve.natDegree_Ψ₃_pos`; IDENTICAL form** — at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:111`.

Decisive evidence — the project file is a **byte-for-byte copy** of the mathlib file. Diff of the `Ψ₃` section (project lines 89–119 vs mathlib lines 93–119) is identical, including:

```lean
lemma natDegree_Ψ₃_pos (h : (3 : R) ≠ 0) : 0 < W.Ψ₃.natDegree :=
  W.natDegree_Ψ₃ h ▸ four_pos
```

Same namespace `WeierstrassCurve`, same signature, same proof term. The project's own module docstring states the file is "a project copy of mathlib's Basic file". This is a fork, not a new contribution.

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `WeierstrassCurve.natDegree_Ψ₃_pos`

Internal use count: **1** (within the project, excluding the declaring lemma itself).
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:115` | `ne_zero_of_natDegree_gt <| W.natDegree_Ψ₃_pos h` (inside the immediately following lemma `Ψ₃_ne_zero`) |

Inline-derivation grep: (none) — no re-derivation elsewhere; but note the single consumer (`Ψ₃_ne_zero`) is *also* a verbatim copy of a mathlib lemma in the same file.

Signal: the only consumer is the next lemma in the same forked block, which is itself already in mathlib. So the entire dependency chain (`natDegree_Ψ₃` → `natDegree_Ψ₃_pos` → `Ψ₃_ne_zero`) is duplicated wholesale from mathlib.

### Composition check (Phase 6)

Can `natDegree_Ψ₃_pos` be derived from mathlib in ≤3 chained calls? Moot — it **already exists** in mathlib by the same name (Phase 5). For completeness, the trivial composition from the sibling lemma is:

Attempt 1: `W.natDegree_Ψ₃ h ▸ four_pos` (this IS the proof; uses `WeierstrassCurve.natDegree_Ψ₃` + `four_pos`).
  - Mathlib decls used: `WeierstrassCurve.natDegree_Ψ₃`, `four_pos`.
  - Result: succeeds (1 rewrite + 1 term).

Conclusion: **N/A — already in mathlib verbatim** (a `NO-mathlib-has-it`, not a `NO-composable`). Even reduced to building blocks it is a ≤2-call composition off `natDegree_Ψ₃`, but the point is moot since the exact lemma is shipped.

---

## Verdict: `WeierstrassCurve.natDegree_Ψ₃_pos`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): standard fact — `ψ₃` has degree 4 / leading coeff 3 (Silverman III.3.7; arXiv 1303.5002, 1108.3051). Positivity is the immediate corollary.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; `CommRing` + `3 ≠ 0` are both minimal/necessary. No modernisation available.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.natDegree_Ψ₃_pos`, identical form**, at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:111`. The whole project `Ψ₃` block is a byte-identical copy.
- Composition check (Phase 6): N/A — exact lemma already present; sole consumer is the next (also-duplicated) lemma in the same file.

**Rationale:**

This declaration is not a candidate for mathlib because **it is already in mathlib, verbatim**. The project file `DivisionPolynomialDegree.lean` is an explicit, byte-for-byte fork of `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` (its own docstring says "a project copy of mathlib's Basic file"), authored by the same person (David Kurniadi Angdinata) under the same copyright header. The lemma `WeierstrassCurve.natDegree_Ψ₃_pos` — same namespace, same signature `(h : (3 : R) ≠ 0) : 0 < W.Ψ₃.natDegree`, same proof term `W.natDegree_Ψ₃ h ▸ four_pos` — sits at line 111 of that mathlib file. The literature search merely confirms the underlying mathematics (ψ₃ is a degree-4 polynomial with leading coefficient 3, so its degree is positive whenever 3 ≠ 0) and that the hypotheses are at the right minimal generality; but the inclusion question is settled the moment we observe the identical mathlib lemma.

The project presumably forked this file to add downstream Nagell–Lutz machinery (division-polynomial degree facts feeding torsion-point arguments) and the fork froze a copy of the upstream degree lemmas alongside. For mathlib purposes there is nothing to add: the canonical home already contains this exact lemma plus the more general `n`-indexed family (`natDegree_preΨ_pos`, `natDegree_ΨSq_pos`, `natDegree_Φ_pos`).

WHY not (refactor-actionable):
- Mathlib already has it, identically. `WeierstrassCurve.natDegree_Ψ₃_pos` is defined at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:111`. The project's copy follows from it trivially (it *is* it).

Existing mathlib decl:        `WeierstrassCurve.natDegree_Ψ₃_pos`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:111`
Our form follows in ≤1 line (it is the same statement; nothing to re-derive):
```lean
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (h : (3 : R) ≠ 0) :
    0 < W.Ψ₃.natDegree := W.natDegree_Ψ₃_pos h   -- the mathlib lemma, same name
```
Call sites in our project (from Phase 6.0): K = 1 (`DivisionPolynomialDegree.lean:115`, inside `Ψ₃_ne_zero`).

Refactor plan (this is a fork-dedup, not a call-site rewrite):
1. The project copies an entire mathlib file. The right cleanup is to **delete the duplicated copy** `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean` (and likewise its companion `DivisionPolynomial.lean`, the copy of mathlib's Basic) and instead `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` (and `.Basic`).
2. With that import, the single internal call site at line 115 (`W.natDegree_Ψ₃_pos h`) resolves to the mathlib lemma unchanged — name, namespace, and argument order are identical, so no edit to the call is needed.
3. Verify the rest of the forked file contains no project-original additions before deleting; if the fork *added* lemmas beyond the mathlib copy, keep only those (in a thin file that imports the mathlib Degree file) and drop every duplicated decl, `natDegree_Ψ₃_pos` included.

Next action: delete the duplicated `natDegree_Ψ₃_pos` (and the surrounding mathlib-copied block) from the project; replace the file's copied content with an `import` of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`. (Caveat: confirm via `lake build` that the project doesn't depend on a fork-specific edit — e.g. a relaxed typeclass or an extra lemma — before removing the copy. If it does, that delta is the only thing worth keeping, and it should be assessed separately.)

---

## Next step

Delete `WeierstrassCurve.natDegree_Ψ₃_pos` from the project and import `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`; the lone internal call site (`DivisionPolynomialDegree.lean:115`) then binds to the identical mathlib lemma with no change. Before deleting, `lake build` to confirm the fork carries no project-specific delta on this block.
