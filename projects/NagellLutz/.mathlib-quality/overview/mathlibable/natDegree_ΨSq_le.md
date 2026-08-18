# /mathlibable report — `WeierstrassCurve.natDegree_ΨSq_le`

**TL;DR — `NO-mathlib-has-it`.** This declaration is a *byte-for-byte fork* of
mathlib's `WeierstrassCurve.natDegree_ΨSq_le`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:345`).
Same statement, same proof, same private helper, same `ΨSq` definition, same
typeclass context, same author and copyright header. The project file's own
docstring states it is "a project copy of mathlib's Basic file." There is no
generality, literature, or composition question to resolve — mathlib already
has the identical lemma. Delete the fork; import the mathlib module.

---

### Baseline (Phase 0)
- lake build:               not run (build stale per task); decl read directly from source — sufficient, the assessment is a provenance/identity match, not a typecheck question
- decl `WeierstrassCurve.natDegree_ΨSq_le`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:343`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  "Division polynomials of Weierstrass curves … (a project copy of mathlib's Basic file)" — computes leading terms / degree bounds of `preΨ`, `ΨSq`, `Φ`

Qualified name **verified**: file opens `namespace WeierstrassCurve` at line 55,
no nested namespace before line 343, `end WeierstrassCurve` at line 450 ⇒
qualified name is `WeierstrassCurve.natDegree_ΨSq_le` (matches the parsed name).

---

### Statement (Phase 1)

`WeierstrassCurve.natDegree_ΨSq_le` is a theorem stating a degree bound: for a
Weierstrass curve `W` over a commutative ring `R` and any integer `n`, the
univariate polynomial `ΨSqₙ` (the square of the `n`-th division polynomial,
viewed as a polynomial in `x`) has natural degree at most `|n|² − 1`.

Mathematically: `deg(Ψ_n² ) ≤ n² − 1`. This is the upper half of the standard
fact (Silverman, *Arithmetic of Elliptic Curves*, Exercise 3.7 / the division-
polynomial degree table) that `Ψ_n²` is a polynomial in `x` of degree exactly
`n² − 1` (with leading coefficient `n²`); the matching lower bound / exact
degree is the neighbouring lemma `natDegree_ΨSq` under `[NoZeroDivisors R]`.

Variables / typeclasses (Lean side):
- `{R : Type u}` — the base ring
- `[CommRing R]` — commutative ring (no domain/field hypothesis)
- `(W : WeierstrassCurve R)` — the Weierstrass curve

Hypotheses (Lean side): none beyond the variables (`n : ℤ` is the only explicit argument).

Conclusion (math): `deg(Ψ_n²) ≤ n² − 1`.
Conclusion (Lean): `(W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a one-line degree-bound helper lemma about a forked mathlib definition;
not a named theorem, not a new structure. (It is a named `## Main statement`
of the *file*, but the file is itself a mathlib fork, so this is mathlib's
"main statement", not a novel project result.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` ⇒ one-liner check is n/a.

---

### Literature search (Phase 3)

This phase is short-circuited *legitimately*: the declaration is not a candidate
for "should mathlib have this?" — **mathlib already has the verbatim
declaration** (established in Phase 5). The literature question ("is this the
standard form?") is therefore settled by mathlib itself: David Kurniadi
Angdinata authored this exact lemma in mathlib in 2024, sourced from Silverman.

For completeness, the standard reference is recorded:

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---------|-------|------|---------------------|-------|
| 1 | Local source (mathlib tree) | `natDegree_ΨSq_le` in `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` | yes | `deg(Ψ_n²) ≤ n² − 1`, `[CommRing R]` | identical statement + proof; cited reference `[Silverman2009]` |
| 2 | Project docstring | file header line 14 | yes | self-declared "project copy of mathlib's Basic file" | provenance is explicit |
| 3 | Literature (Silverman, AEC) | division-polynomial degree table / Exercise 3.7 | yes | `Ψ_n²` has degree `n²−1` in `x` | mathlib's reference; the `≤` half is exactly this lemma |

### Literature summary (Phase 3)

Concept identified as: degree bound for the square of the elliptic-curve division
polynomial, `deg_x(Ψ_n²) ≤ n² − 1`.
Sources agree on the standard form: yes — mathlib's lemma is the canonical Lean
encoding, authored from Silverman.
Most general standard form: over an arbitrary commutative ring `R`, with the
`≤` (bound) form so no integral-domain hypothesis is needed. **This is exactly
the form here.**
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form: `(W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1` over
`[CommRing R]`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring | NO | `ΨSq`/division polynomials are defined over a commutative ring; this is already the minimal sensible hypothesis. The bound form deliberately avoids `[NoZeroDivisors R]` (that stronger hypothesis is only needed for the *exact* degree `natDegree_ΨSq`). |
| 2 | `(n : ℤ)` | integer index | integer index | NO | division polynomials are indexed by `ℤ` via `Int.negInduction`; this is intrinsic. |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL.
Number of weakening opportunities found: 0.
Cost of restatement: n/a — identical to mathlib, nothing to restate.

### Modern-idiom check (Phase 4c)

Modern idiom available: no. The lemma is already the idiomatic mathlib
formulation — it *is* the mathlib formulation, verbatim. No filter-isation,
typeclass-bundling, or universal-property move applies to a `natDegree ≤`
bound on a concrete polynomial. (All seven rows answer `no`: finite
degree-arithmetic statement, no topology/category/index-generalisation to make.)

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equality or typeclass-search
path introduced).

---

### Mathlib search (Phase 5)

[A] Lean-Finder        — n/a: identity already established by direct source read
[B] Loogle             — n/a: identity already established by direct source read
[C] LeanSearch         — n/a: identity already established by direct source read
[D] Grep mathlib src   `natDegree_ΨSq_le` over `.lake/packages/mathlib/Mathlib/` → **HIT**
[E] Name pattern       `^lemma natDegree_ΨSq_le` in `.../DivisionPolynomial/Degree.lean` → **HIT (line 345)**

Searched for both the current form and the literature-standard form — they are
the same form, and it is present in mathlib.

**Identity evidence (decisive):**
- `diff` of project lines 322–346 (`natDegree_coeff_ΨSq_ofNat` helper +
  `natDegree_ΨSq_le`) against mathlib lines 324–348 → **exit 0 (identical)**.
- `diff` of the `ΨSq` definition (project `DivisionPolynomial.lean:165–170` vs
  mathlib `Basic.lean:242–247`) → **exit 0 (identical)**.
- `variable` line identical in both files: `{R : Type u} [CommRing R] (W : WeierstrassCurve R)`.
- Identical copyright header (David Kurniadi Angdinata, 2024) and identical
  module docstring `## Main statements` list.

Concluded: **found in mathlib as `WeierstrassCurve.natDegree_ΨSq_le`; identical
form** (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:345`).

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.natDegree_ΨSq_le`

Internal use count (within the NagellLutz project, excluding the declaring file): 0
direct applications. The module is imported by four `LutzNagell/LutzNagellTheorem/*`
files (`GeneralIntegralMultiple`, `PIDPrimeOrder`, `PIDIntegralMultiple`,
`GeneralPrimeOrder`) but the lemma is applied in the sibling **HasseWeil** project,
which carries its own parallel fork:

| Caller file:line | Usage pattern |
|------------------|---------------|
| HasseWeil/OrdAtInftyBridge.lean:272 | `… := W.natDegree_ΨSq_le n` |
| HasseWeil/OrdAtInftyBridge.lean:325 | `… := W.natDegree_ΨSq_le n` |
| HasseWeil/MulByIntPullback.lean:352 | `(Polynomial.natDegree_map_le.trans (W.natDegree_ΨSq_le n))` |
| HasseWeil/EC/MulByIntUnramified.lean:251 | `(Polynomial.natDegree_C_mul_le _ _).trans (W.natDegree_ΨSq_le ℓ)` |
| HasseWeil/WeilPairing/PairingNondeg.lean:117 | `(Polynomial.natDegree_C_mul_le _ _).trans (W.natDegree_ΨSq_le ℓ)` |
| HasseWeil/Auxiliary/DivisionPolynomial.lean:810 | `… ((W.natDegree_ΨSq_le n).trans (Nat.sub_le _ _))` |

Inline-derivation grep: the bound `(W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1` is
re-stated as a `have` in OrdAtInftyBridge (lines 272, 325) immediately before
applying the lemma — i.e. consumers depend on exactly this statement.

#### Composition check (Phase 6)

Can `natDegree_ΨSq_le` be derived from mathlib in ≤3 chained calls?

Attempt 1: `exact WeierstrassCurve.natDegree_ΨSq_le n` (with mathlib imported).
  - Mathlib decls used: `WeierstrassCurve.natDegree_ΨSq_le`.
  - Result: succeeds **trivially** — it is literally the same lemma.

Conclusion: COMPOSABLE in the degenerate sense (0 new reasoning — it is the
identical mathlib lemma). This is the NO-mathlib-has-it case, not a genuine
"compose from primitives" case.

---

## Verdict: `WeierstrassCurve.natDegree_ΨSq_le`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): standard Silverman degree fact; mathlib's own lemma is the canonical encoding.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — and identical to mathlib's (`CommRing`, `≤`-form).
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.natDegree_ΨSq_le`; **identical form** (byte-for-byte `diff` exit 0).
- Composition check (Phase 6): degenerate — it *is* the mathlib lemma.

**Rationale:**

This is not a borderline or judgment call. The project file
`projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean` is an explicit,
acknowledged fork of `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`
— the docstring at line 14 says "a project copy of mathlib's Basic file", the
copyright header and `## Main statements` list are copied verbatim, and a
line-level `diff` of the lemma (and its private helper `natDegree_coeff_ΨSq_ofNat`)
against the mathlib source returns **no differences**. The underlying `ΨSq`
definition is likewise byte-identical to mathlib's `WeierstrassCurve.ΨSq`, and
the ambient typeclass context (`[CommRing R]`) matches exactly. There is
therefore nothing for mathlib to gain: it already contains this declaration, at
this generality, under this name.

The lemma is already maximally general (commutative-ring base, `≤`-bound form
that needs no `NoZeroDivisors`), so there is no "generalise first" angle, and no
modern-idiom restatement applies to a concrete `natDegree ≤` bound. The only
correct action is de-duplication against upstream.

**WHY not (refactor-actionable):**

Mathlib already has it: `WeierstrassCurve.natDegree_ΨSq_le`. Because the project's
`ΨSq` *is* mathlib's `WeierstrassCurve.ΨSq` (forked identically) and the
qualified name is the same, the user's form does not merely "follow from" the
mathlib lemma — it **is** the mathlib lemma. Once the fork is removed and the
project imports the upstream module, every call site resolves to the same
`W.natDegree_ΨSq_le n` with zero signature or argument-order changes.

- Existing mathlib decl:  `WeierstrassCurve.natDegree_ΨSq_le`
- Located at:             `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:345`
- Our form follows in 0 lines:
  ```lean
  example (W : WeierstrassCurve R) (n : ℤ) :
      (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 := W.natDegree_ΨSq_le n  -- the mathlib lemma, unchanged
  ```
- Call sites in the repo (Phase 6.0): 0 in NagellLutz's own non-declaring files;
  6 applications in the sibling **HasseWeil** project (which forks the same file
  under `HasseWeil/Auxiliary/DivisionPolynomial.lean`); 4 NagellLutz
  `LutzNagellTheorem/*` files import the module.

**Refactor plan (whole-fork deduplication, not a single-lemma swap):**
The right unit of action is the *file*, not this one lemma — the entire
`DivisionPolynomialDegree.lean` (and its companion `DivisionPolynomial.lean`)
duplicates `Mathlib/.../DivisionPolynomial/{Degree,Basic}.lean`.

1. Delete the project fork files `LutzNagell/DivisionPolynomial.lean` and
   `LutzNagell/DivisionPolynomialDegree.lean` (verify the *whole* files are
   identical to upstream first — the two diffs above already confirm the `ΨSq`
   def and this lemma; do the same `diff` over the full files before deleting).
2. Replace `import LutzNagell.DivisionPolynomialDegree` with
   `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`
   in the four `LutzNagell/LutzNagellTheorem/*` consumers.
3. No edit needed at any application of `W.natDegree_ΨSq_le n` — the qualified
   name and signature are identical upstream.
4. Coordinate with the parallel **HasseWeil** fork
   (`HasseWeil/Auxiliary/DivisionPolynomial.lean`), which has the same 6 call
   sites; it should switch to the mathlib import in the same dedup sweep.
5. **Caveat for the AINTLIB fleet:** this is a `/cleanup`-lane dedup. If the
   forks exist because the project needed a *newer/older* division-polynomial
   API than the pinned mathlib at fork time, confirm the current daily-bumped
   mathlib `Degree.lean` still matches before deleting (the diffs above say it
   does on this checkout). If any divergence is later introduced upstream,
   re-evaluate — but as of this checkout the fork is redundant.

**Next action:** delete the project's `DivisionPolynomial{,Degree}.lean` forks
and repoint the four NagellLutz importers (and the HasseWeil consumers) at
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`. No new
mathlib PR — mathlib already has this.

---

## Next step

Delete `WeierstrassCurve.natDegree_ΨSq_le` (and the whole
`DivisionPolynomialDegree.lean` / `DivisionPolynomial.lean` fork) from the
NagellLutz project; switch the four `LutzNagellTheorem/*` importers — and the
sibling HasseWeil consumers — to `import
Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`. Call sites
need no change.
