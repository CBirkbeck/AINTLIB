# /mathlibable report — `WeierstrassCurve.natDegree_Φ`

> Step-9 mathlibable assessment (NagellLutz project). Single declaration.
> Generated as part of `/overview` Step 9 (mathlibable triage → full check).

## Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoning from source — the decl is a verbatim fork of a building mathlib decl, so elaboration is not in doubt)
- decl `WeierstrassCurve.natDegree_Φ`:  ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:433` (`@[simp]` line 432; statement line 433)
- kind:                     lemma (theorem)
- has sorry:                no
- module docstring summary: "Division polynomials of Weierstrass curves … computes the leading terms of certain polynomials associated to division polynomials … **a project copy of mathlib's Basic file**."

## Statement (Phase 1)

`WeierstrassCurve.natDegree_Φ` states: for a Weierstrass curve `W` over a commutative ring `R` that is **nontrivial** (`[Nontrivial R]`), and any integer `n`, the `Φ`-division polynomial `Φₙ` of `W` has degree exactly `|n|²`:
$$\deg \Phi_n = (\,|n|\,)^2 = n^2.$$
Here `Φₙ ∈ R[X]` is the standard "x-coordinate denominator/numerator" division polynomial of the elliptic-curve multiplication-by-`n` map (Silverman, *Arithmetic of Elliptic Curves*, Exercise 3.7 / division-polynomial recursions). Over an integral domain this gives the exact degree of the numerator of `[n]` on the `x`-line.

Exact Lean statement (verified from source):
```lean
@[simp]
lemma natDegree_Φ [Nontrivial R] (n : ℤ) : (W.Φ n).natDegree = n.natAbs ^ 2 :=
  natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_Φ_le n) <| W.coeff_Φ_ne_zero n
```

Variables / typeclasses:
- `{R : Type u} [CommRing R]` — the base ring.
- `[Nontrivial R]` — needed so the leading coefficient `1` is `≠ 0`, hence the degree bound is attained.
- `(W : WeierstrassCurve R)` — the curve.
- `(n : ℤ)` — the multiplier.

Conclusion (math): `deg Φₙ = n²`.
Conclusion (Lean): `(W.Φ n).natDegree = n.natAbs ^ 2`.

## Size classification (Phase 2a)

Verdict: **SMALL** (a named consequence: combine a degree upper bound with non-vanishing of the top coefficient via `natDegree_eq_of_le_of_coeff_ne_zero`). It *is* listed under the file's `## Main statements`, but the file itself is an exact mathlib fork, so "main statement of the project" carries no novelty weight here.

## One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`. (Body is a single-term application but the def-specific one-liner gate does not apply to lemmas.)

## Literature search (Phase 3)

The deciding evidence (Phases 5–6) is that this is a **byte-for-byte fork of an existing mathlib lemma**, so the literature sweep is recorded for completeness rather than as the verdict driver. The literature-standard form *is* mathlib's own form; both the project file and the mathlib file cite the same source.

| #  | Channel | Query | Hit? | Standard form | Notes |
|----|---------|-------|------|---------------|-------|
| 1 | Local refs (provenance) | header + docstring of both files | yes | `deg Φₙ = n²` | Both files: `Authors: David Kurniadi Angdinata`; both cite `[silverman2009]`. The fork's own docstring says "a project copy of mathlib's Basic file." |
| 2 | mathlib source (the literature, as formalised) | `Mathlib/.../DivisionPolynomial/Degree.lean` | yes | identical | mathlib `natDegree_Φ` at line 435 is character-identical (see Phase 5). |
| 3 | WebSearch (standard form) | "elliptic curve division polynomial degree n^2" | yes | `deg Φₙ = n²`, `deg ψₙ² = n²−1` | Standard: Silverman, *Arithmetic of Elliptic Curves*, III.3 + Ex. 3.7; the multiplication-by-`n` map has `x([n]P) = Φₙ(x)/ψₙ(x)²` with `deg Φₙ = n²`. Universally agreed. |
| 4 | WebSearch (named-after / aliases) | "psi phi omega division polynomials Weierstrass" | yes | same | `Φ` is the canonical name for the x-numerator; degree `n²` is textbook (also Washington, *Elliptic Curves*, §3.2). |
| 5 | ChatGPT MCP | (server down per task; fallback to refs #1–#2 which are dispositive) | n/a | — | MCP unavailable; not needed — mathlib provenance is conclusive. |
| 6 | nLab | "division polynomial" | n/a | — | nLab has no dedicated division-polynomial degree page; concept is classical/computational, not categorical. |
| 7 | nCatLab | — | n/a | — | not a categorical concept. |
| 8 | Stacks Project | "division polynomial" | n/a | — | Stacks does not cover classical elliptic-curve division polynomials in this elementary form. |
| 9 | MathOverflow / MSE | "degree of division polynomial phi_n" | yes | `n²` | Confirms `deg Φₙ = n²`; multiple answers reference Silverman. |
| 10 | recent arXiv | n/a | n/a | — | Classical 19th–20th century result; no recent-arXiv dependence. |

### Literature summary (Phase 3)

Concept identified as: the **x-coordinate division polynomial `Φₙ`** of a Weierstrass/elliptic curve, and the classical degree formula `deg Φₙ = n²`.
Sources agree on the standard form: **yes** — Silverman III.3 / Ex. 3.7, Washington §3.2, and mathlib's own formalisation all give `deg Φₙ = n²`.
Most general standard form: over any nontrivial commutative ring the leading coefficient is `1` (monic-after-the-fact), so the degree equality holds with just `[Nontrivial R]` — exactly the Lean hypothesis. This is *already* the maximally general formalised form (mathlib's).
Disagreement with the literature: none.

## Generality analysis (Phase 4)

Literature-standard / mathlib form: `[Nontrivial R] → (W.Φ n).natDegree = n.natAbs ^ 2` over `[CommRing R]`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring | NO | `Φ` and the recursion are defined over `CommRing`; this is already minimal. |
| 2 | `[Nontrivial R]` | nontrivial | nontrivial | NO | Required: in the trivial ring `1 = 0`, the leading coeff vanishes and the degree drops. Cannot be removed. |
| 3 | `(n : ℤ)` | integer | integer | NO | The `natAbs²` formulation already covers all `n ∈ ℤ` (via `Φ_neg`); this is the general index. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is mathlib's own canonical statement; 0 weakening opportunities).
Number of weakening opportunities found: 0.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation |
|---|----------|----------|---------------|
| 1 | bundled hypotheses → typeclasses? | no | already a typeclass (`[Nontrivial R]`). |
| 2 | sequences/metric → filters/topology? | no | purely algebraic polynomial-degree identity. |
| 3 | construction → universal property? | no | `Φ` is a concrete polynomial; degree is a property, not a construction. |
| 4 | set+closure → bundled substructure? | no | no substructure involved. |
| 5 | field/metric-specific → weaken typeclass? | no | already at `CommRing` + `Nontrivial`. |
| 6 | 1-categorical → higher-categorical? | no | n/a. |
| 7 | concrete index → general algebraic index? | no | `n : ℤ` with `natAbs²` is the right index already. |

Modern idiom available: **no**. This is already mathlib's idiomatic form (it *is* the mathlib lemma).

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instance-search paths introduced).

## Mathlib search-status: `WeierstrassCurve.natDegree_Φ` (Phase 5)

[A] Lean-Finder       — not needed; direct source hit found
[B] Loogle            `(WeierstrassCurve.Φ _ _).natDegree = _ ^ 2`   → mathlib hit (see [D])
[C] LeanSearch        "degree of division polynomial Phi equals n squared" → mathlib `WeierstrassCurve.natDegree_Φ`
[D] Grep mathlib src  `natDegree_Φ` in `.lake/packages/mathlib/` → **HIT**:
    `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:435`
[E] Name pattern      `WeierstrassCurve.natDegree_Φ` → exact qualified-name match in mathlib

Searched for both the user's current form and the literature-standard form — they are **the same form**.

The mathlib decl (`Degree.lean:435`) is **character-identical** to the project's:
```lean
@[simp]
lemma natDegree_Φ [Nontrivial R] (n : ℤ) : (W.Φ n).natDegree = n.natAbs ^ 2 :=
  natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_Φ_le n) <| W.coeff_Φ_ne_zero n
```
A direct `diff` of the project block against the mathlib block shows zero differences in the `natDegree_Φ` lines (the only diff hunks are the surrounding neighbours shifting by the constant 1-line file offset). The underlying `WeierstrassCurve.Φ` definition is also byte-identical between `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:272` and `Mathlib/.../DivisionPolynomial/Basic.lean:349`. Same author (David Kurniadi Angdinata, the mathlib author of these files).

**Concluded: found in mathlib as `WeierstrassCurve.natDegree_Φ` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:435`); identical form.**

The NagellLutz project does **not** `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`; it maintains its own pre-module-system fork (`LutzNagell/DivisionPolynomial.lean` + `DivisionPolynomialDegree.lean`). That fork is the *only* reason this duplicate exists. (Mathlib's file now uses `module` syntax the fork predates.)

## Composition check (Phase 6)

### Call sites — `WeierstrassCurve.natDegree_Φ`

Internal use count (NagellLutz, excluding the declaring file): **1**
- `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:35` — `_ = (W.Φ n).natDegree := (natDegree_Φ _ n).symm`

(Many further uses live in the *sibling* HasseWeil project — `OrdAtInftyBridge.lean:156`, `MulByIntPullback.lean:348`, `EC/MulByIntUnramified.lean:249`, `Verschiebung/Genuine.lean:575/579/936`, `WeilPairing/PairingNondeg.lean:113`, `Auxiliary/DivisionPolynomial.lean:809` — several explicitly commented as referring to "mathlib's `natDegree_Φ`". These resolve against whichever `WeierstrassCurve.natDegree_Φ` is in scope and would bind to the mathlib lemma after the fork is dropped.)

Inline-derivation grep: none re-derive the degree from scratch — they all call `natDegree_Φ`.

### Composition check

Can `natDegree_Φ` be derived from mathlib in ≤3 chained calls? **It does not need to be — mathlib has the lemma itself, verbatim.** Trivially, `example : (W.Φ n).natDegree = n.natAbs ^ 2 := W.natDegree_Φ n` once the mathlib file is imported.

Conclusion: **COMPOSABLE is moot — NO-mathlib-has-it (exact decl) takes precedence.**

## Verdict: `WeierstrassCurve.natDegree_Φ`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): standard `deg Φₙ = n²` (Silverman III.3 / Ex. 3.7); same source cited by both the fork and mathlib; same author.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — it *is* the mathlib form; no weakening, no modern-idiom move.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.natDegree_Φ` at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:435`, **character-identical** statement and proof; `Φ` def identical too.
- Composition check (Phase 6): moot; the exact lemma exists upstream.

**Rationale:**

This declaration is a verbatim fork of an existing mathlib lemma. The NagellLutz project keeps a private, pre-module-system copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.{Basic,Degree}` (under `LutzNagell/DivisionPolynomial.lean` and `DivisionPolynomialDegree.lean`) rather than importing the mathlib originals. The statement, the proof term, the `@[simp]` attribute, the docstring, the `WeierstrassCurve.Φ` definition it relies on, and even the file author (David Kurniadi Angdinata, the mathlib author of these files) all match mathlib exactly — a direct `diff` of the `natDegree_Φ` block shows no differences. There is therefore nothing to upstream: mathlib already has precisely this lemma at the precisely-right generality (`[CommRing R] [Nontrivial R]`, `n : ℤ`). The decl exists in the project only because the fork is not wired to the upstream module.

WHY not (refactor-actionable):
Mathlib already has it, in identical form. The right move is to delete the project's fork of these two files and re-point the project at mathlib's `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` + `.Degree`. Because the names and namespaces are identical (`WeierstrassCurve.natDegree_Φ`, `WeierstrassCurve.Φ`, etc.), call sites need no edits — only the `import` graph changes.

Existing mathlib decl:        `WeierstrassCurve.natDegree_Φ`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:435`
Our form follows in ≤1 line (in fact it is the same term):
```lean
example [Nontrivial R] (n : ℤ) : (W.Φ n).natDegree = n.natAbs ^ 2 := W.natDegree_Φ n
```
Call sites in this project (NagellLutz, from Phase 6.0): K = 1
(`LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:35`). Plus several in sibling project HasseWeil.

Refactor plan:
1. This is a **whole-fork dedup**, not a single-lemma swap: `LutzNagell/DivisionPolynomial.lean` and `LutzNagell/DivisionPolynomialDegree.lean` together duplicate two mathlib files. The cleanest fix is to delete both fork files and replace their imports with `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` and `…DivisionPolynomial.Degree`.
2. The single NagellLutz call site (`PIDIntegralMultiple.lean:35`, `(natDegree_Φ _ n).symm`) and all HasseWeil call sites use the identical name `WeierstrassCurve.natDegree_Φ`, so they continue to typecheck against the mathlib lemma with no source change.
3. Caveat: the fork is pre-`module`-system; mathlib's current files use `module` syntax. Confirm the project's Lean/mathlib pin supports importing them (it does — the same mathlib provides them), and that no *other* lemma in the fork files diverged from upstream before bulk-deleting (a file-level `diff` of both fork files vs. their mathlib counterparts should be run as part of the dedup ticket).

Next action: file a dedup cleanup ticket to drop the `DivisionPolynomial` / `DivisionPolynomialDegree` fork in favour of the mathlib modules; do not upstream `natDegree_Φ` (it is already there). This is a project-wide dedup, best handled as one ticket covering both fork files rather than per-lemma.

---

## Next step

File a dedup ticket: delete the NagellLutz fork of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.{Basic,Degree}` and import the mathlib originals; the K=1 local call site (and the HasseWeil ones) need no edits because the qualified name is identical. Nothing to upstream.
