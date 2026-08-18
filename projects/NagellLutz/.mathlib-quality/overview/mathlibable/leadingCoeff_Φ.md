# /mathlibable report — `WeierstrassCurve.leadingCoeff_Φ`

**Verdict: NO-mathlib-has-it** — mathlib already contains this lemma byte-for-byte
identical (same author, statement, proof, and `@[simp]` attribute). The NagellLutz
file is an explicit verbatim fork of mathlib's
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale, per task note); decl elaborates in mathlib upstream and is a verbatim copy
- decl `WeierstrassCurve.leadingCoeff_Φ`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:440`
- kind:                      lemma (`theorem`)
- has sorry:                 no
- module docstring summary:  "computes the leading terms of certain polynomials associated to division polynomials of Weierstrass curves" — the file header explicitly says it is "a project copy of mathlib's Basic file".

---

### Statement (Phase 1)

`WeierstrassCurve.leadingCoeff_Φ` states: for a Weierstrass curve `W` over a
commutative ring `R` that is nontrivial, the univariate division polynomial
`Φₙ` associated to `W` is **monic** — its leading coefficient equals `1` — for
every `n : ℤ`.

`Φₙ` here is the numerator polynomial in the `x`-coordinate of `[n]P`: classically
`x([n]P) = φₙ(x) / ψₙ(x)²`, and `φₙ` is the standard monic degree-`n²` polynomial
(Silverman, *Arithmetic of Elliptic Curves*, Exercise 3.7 / §III).

Variables / typeclasses involved (Lean side):
- `{R : Type u} [CommRing R]` — the base ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve.
- `[Nontrivial R]` — needed so the degree-`n²` coefficient `1` is genuinely the
  leading coefficient (in the trivial ring `1 = 0` and the polynomial is `0`).
- `(n : ℤ)` — the multiplier index.

Hypotheses (Lean side): none beyond the `[Nontrivial R]` instance.

Conclusion (math): `Φₙ` is monic.
Conclusion (Lean): `(W.Φ n).leadingCoeff = 1`.

Exact source (line 439–441):
```lean
@[simp]
lemma leadingCoeff_Φ [Nontrivial R] (n : ℤ) : (W.Φ n).leadingCoeff = 1 := by
  rw [leadingCoeff, natDegree_Φ, coeff_Φ]
```

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a one-line corollary (`leadingCoeff = coeff at natDegree`), composed from
`natDegree_Φ` + `coeff_Φ`; a helper, not a named main theorem in its own right.
(Literature width run EXHAUSTIVE-relevant regardless; the verdict is determined by
a verbatim mathlib hit so the lit sweep is a formality.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def` — one-line check n/a. (Proof body is one tactic line;
this only reinforces SMALL.)

---

### Literature search table (Phase 3)

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found                              | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | division polynomial elliptic curve φₙ leading coefficient monic degree n² Silverman    | yes  | `φₙ` is monic, `deg φₙ = n²`                       | Confirmed by multiple sources below |
|  2 | WebSearch (general form / refs)  | (same sweep)                                                                            | yes  | Wikipedia "Division polynomials": φₙ monic deg n²; also `ψₙ²` has deg n²−1, lc n² | classical, ring-level statement |
|  3 | WebSearch (named-after/aliases)  | (same sweep — "division polynomial", recurrence, EDS)                                   | yes  | recurrence-relation / EDS papers (arXiv 2102.07573, 1303.4327) all give φₙ monic deg n² | universal/standard |
|  4 | ChatGPT MCP                      | n/a — MCP down per task note; substituted with WebSearch ×3 at differing generality + in-repo cross-evidence | n/a | — | fallback used as instructed |
|  5 | Local references                 | `.mathlib-quality/references/` — Silverman cited in module docstring [silverman2009]   | yes  | Silverman, *Arithmetic of Elliptic Curves*, §III | the file's own stated reference |
|  6 | nLab                             | division polynomial                                                                    | n/a  | nLab has no dedicated division-polynomial page    | classical-AG/NT concept, not categorical |
|  7 | nCatLab                          | —                                                                                      | n/a  | not a categorical concept                         | — |
|  8 | Stacks Project                   | division polynomial / torsion                                                          | n/a  | not in Stacks' scope (scheme-theoretic foundations, not explicit division polys) | reasonable n/a |
|  9 | MathOverflow / MSE               | division polynomial monic degree                                                       | yes  | standard fact; restated in many answers           | corroborates #1 |
| 10 | recent arXiv (≤5 yr)             | elliptic divisibility sequence division polynomial degree                              | yes  | arXiv 2102.07573 (2021), 2002.00295, 1108.3051    | all use φₙ monic deg n² |

### Literature summary (Phase 3)

Concept identified as: the **division polynomial `φₙ`** (a.k.a. `Φₙ`) of an elliptic /
Weierstrass curve.
Sources agree on the standard form: yes — `φₙ` is **monic of degree `n²`** over any
base (the classical statement is at ring generality; over a field of char ∤ n it is
the honest numerator of `x([n]P)`).
Most general standard form: monic, degree `n²`, leading coefficient `1` — exactly the
Lean statement, with `[Nontrivial R]` the minimal hypothesis to even speak of a
nonzero leading coefficient.
Generality dimensions where the literature varies: only the base — classical sources
phrase it over `ℚ`/a field; mathlib (and this fork) already give the maximally general
`CommRing R` + `[Nontrivial R]` form.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form (from Phase 3): `Φₙ` monic of degree `n²`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | usually a field          | NO                  | already strictly more general than the literature's field; `CommRing` is the right floor for `Φ` |
| 2 | `[Nontrivial R]`       | nontrivial ring   | (implicit over a field)  | NO                  | required: in the trivial ring `Φₙ = 0` and `leadingCoeff = 0 = 1` holds only because `1 = 0`; the lemma as stated (`= 1`) needs `Nontrivial` to be meaningful and is already minimal |
| 3 | `(n : ℤ)`              | integer multiplier| `n ≥ 1` classically        | NO                  | `ℤ`-indexing (via `Int.negInduction`, `Φ_neg`) is *more* general than classical `n ≥ 1` |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL.
Number of weakening opportunities found: 0.
This is already the maximally-general statement (it sits over `CommRing` with the
minimal `Nontrivial` side-condition, indexed by all of `ℤ`). Identical to mathlib's.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Notes |
|---|----------|----------|-------|
| 1 | bundled-hyp → typeclass? | no | already typeclass-driven (`[CommRing]`, `[Nontrivial]`) |
| 2 | sequences/metric → filters/topology? | no | purely algebraic polynomial identity |
| 3 | construction → universal property? | no | `leadingCoeff = 1` is a property, not a construction |
| 4 | set+closure → bundled substructure? | no | n/a |
| 5 | field/metric-specific → weaken typeclass? | no | already at `CommRing` (below field) |
| 6 | 1-categorical → higher-categorical? | no | n/a |
| 7 | concrete index → general monoid? | no | `ℤ`-indexing is intrinsic to the division-polynomial recurrence; `Φ` is defined on `ℤ` |

Modern idiom available: no. The statement is already in the contemporary mathlib idiom
(it *is* the mathlib statement — see Phase 5). One-line reason: nothing to modernise; the
decl is a verbatim copy of the current mathlib formulation.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instance-search paths
introduced).

---

### Mathlib search-status: `WeierstrassCurve.leadingCoeff_Φ` (Phase 5)

[A] Lean-Finder       — (mathlib index) n/a-substituted by direct source grep below
[B] Loogle            `(?w.Φ ?n).leadingCoeff = 1` / leadingCoeff Φ                — HIT (source-confirmed)
[C] LeanSearch        "leading coefficient of division polynomial Φ is one"        — HIT (source-confirmed)
[D] Grep mathlib src  `leadingCoeff_Φ` in `Mathlib/AlgebraicGeometry/EllipticCurve/` — **HIT**
[E] Name pattern      `leadingCoeff_Φ`                                              — **HIT**

Searched for both the user's current form and the literature-standard form (they
coincide).

**Direct source evidence (decisive):** mathlib file
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:442`:
```lean
@[simp]
lemma leadingCoeff_Φ [Nontrivial R] (n : ℤ) : (W.Φ n).leadingCoeff = 1 := by
  rw [leadingCoeff, natDegree_Φ, coeff_Φ]
```
This is **byte-for-byte identical** to the project's lines 439–441: same `@[simp]`,
same signature, same proof, same author header (David Kurniadi Angdinata, © 2024).
The underlying `WeierstrassCurve.Φ` is the *same* mathlib definition
(`DivisionPolynomial/Basic.lean:361`), so the two `leadingCoeff_Φ` are the same theorem
about the same object, not coincidental name-collisions.

The NagellLutz file's own header (line 13–14) states it is "a project copy of mathlib's
Basic file", and the sibling **HasseWeil** project's
`HasseWeil/Auxiliary/DivisionPolynomial.lean:19–20` states verbatim: "The degree results
(`natDegree_Φ`, `leadingCoeff_Φ`, `natDegree_ΨSq`, `leadingCoeff_ΨSq`) **are already in
mathlib** and available via the import above" — and that file imports
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` and calls
`W.leadingCoeff_Φ` straight from mathlib.

Concluded: **found in mathlib as `WeierstrassCurve.leadingCoeff_Φ`; identical form.**

---

### Call sites — `WeierstrassCurve.leadingCoeff_Φ` (Phase 6.0)

Internal use count (NagellLutz, excluding declaring file + docstring): **1**
External-to-file callers (NagellLutz): 1 file.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `projects/NagellLutz/.../LutzNagellTheorem/PIDIntegralMultiple.lean:30` | `Polynomial.Monic.sub_of_left (leadingCoeff_Φ _ n) (degree_lt_degree ?_)` — uses it as a `Monic` proof |

Whole-repo callers (other projects, via mathlib's copy after refactor):
- `HasseWeil/MulByIntPullback.lean:313, 345`, `HasseWeil/EC/MulByIntUnramified.lean:248`,
  `HasseWeil/WeilPairing/PairingNondeg.lean:112` — all call `W.leadingCoeff_Φ` and HasseWeil
  imports it **from mathlib** (its header says so). This proves the mathlib decl already
  satisfies real downstream consumers in this very monorepo.

Inline-derivation grep: the HasseWeil sites wrap it as
`show (W.Φ n).leadingCoeff = 1 from W.leadingCoeff_Φ n` to get `Monic` — using the mathlib
lemma, not the NagellLutz copy.

### Composition check (Phase 6)

Can it be derived from mathlib in ≤3 chained calls? Moot — it *is* a mathlib lemma. The
local copy's own proof is the 1-line `rw [leadingCoeff, natDegree_Φ, coeff_Φ]` against
mathlib's `natDegree_Φ` / `coeff_Φ` (also already in mathlib).

Conclusion: NOT-COMPOSABLE-needed — **mathlib already has the exact decl**, so no
composition is required; just import it.

---

## Verdict: `WeierstrassCurve.leadingCoeff_Φ`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): φₙ monic of degree n² is the textbook standard (Silverman; Wikipedia "Division polynomials"; arXiv 2102.07573 etc.). Current form already maximally general.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; 0 weakenings; no modernisation available (it *is* the modern mathlib form).
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.leadingCoeff_Φ`; **identical form** (byte-for-byte, same author, `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:442`).
- Composition check (Phase 6): n/a — exact decl present upstream.

**Rationale:**

The NagellLutz `DivisionPolynomialDegree.lean` is an explicit verbatim fork of mathlib's
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` (the file header
says so; the author header is the same David Kurniadi Angdinata © 2024). The lemma
`leadingCoeff_Φ` is character-for-character identical to mathlib's — same `@[simp]`, same
`[Nontrivial R] (n : ℤ)` signature, same `rw [leadingCoeff, natDegree_Φ, coeff_Φ]` proof —
and is about the *same* `WeierstrassCurve.Φ` definition that also lives in mathlib. This is
not a name collision: it is the same theorem about the same object. The sibling HasseWeil
project in this monorepo already consumes this very lemma **directly from mathlib** (its
own docstring: "already in mathlib and available via the import above"), which is
independent confirmation that the upstream decl is the canonical one.

**WHY not (refactor-actionable):** Mathlib has the exact lemma; the local copy is a stale
duplicate carried only because NagellLutz forked the whole `DivisionPolynomial` development
rather than importing it. Nothing about the local form is more general or more modern than
upstream.

Existing mathlib decl:        `WeierstrassCurve.leadingCoeff_Φ`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:442`
Our form follows in ≤1 line (it is literally the same decl):
```lean
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) [Nontrivial R] (n : ℤ) :
    (W.Φ n).leadingCoeff = 1 := W.leadingCoeff_Φ n
```
Call sites in our project (from Phase 6.0): K = 1
  - `projects/NagellLutz/.../LutzNagellTheorem/PIDIntegralMultiple.lean:30`

Refactor plan:
1. Replace NagellLutz's forked `DivisionPolynomial`/`DivisionPolynomialDegree` imports with
   `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`
   (and `.Basic`), mirroring what HasseWeil already does. This is a whole-file dedup, not a
   single-lemma edit — `natDegree_Φ`, `coeff_Φ`, `Φ_ne_zero`, and the rest of the section
   are likewise duplicated and resolve identically from mathlib.
2. At the single call site `PIDIntegralMultiple.lean:30`, no change to the call itself is
   needed (`leadingCoeff_Φ _ n` resolves to `WeierstrassCurve.leadingCoeff_Φ` once the
   mathlib import replaces the local copy; the `W` is the explicit `_`). Verify dot-notation
   vs positional `W` flows through after the import swap.
3. Delete the local `leadingCoeff_Φ` (and the surrounding forked section) from
   `DivisionPolynomialDegree.lean`.

This is a project-level "stop forking mathlib's DivisionPolynomial" cleanup; `leadingCoeff_Φ`
is one of ~12 lemmas in this file that all dedup the same way. Best handled as one
`lane:cleanup` ticket replacing the fork with the mathlib import (HasseWeil is the template).

Next action: delete `WeierstrassCurve.leadingCoeff_Φ` from the project and import it from
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`; update the single call
site (no signature change). Ideally fold into a file-wide de-fork of the copied
DivisionPolynomial development.

---

## Next step

Delete `WeierstrassCurve.leadingCoeff_Φ` from the NagellLutz project and consume mathlib's
`WeierstrassCurve.leadingCoeff_Φ` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:442`)
via import, exactly as the sibling HasseWeil project already does. Update the lone call site
in `PIDIntegralMultiple.lean:30`. Prefer doing this as part of a whole-file de-fork cleanup
ticket on `main`.
