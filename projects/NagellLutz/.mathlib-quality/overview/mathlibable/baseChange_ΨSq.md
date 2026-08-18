# /mathlibable report — `WeierstrassCurve.baseChange_ΨSq`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz theorem; elliptic
> curves; division polynomials; elliptic divisibility sequences).
> **Bottom line: NO-mathlib-has-it.** The declaration is a *verbatim fork* of an
> identically-named mathlib lemma. The project file says so in its own module
> docstring. No literature/generality/composition analysis can change a literal
> identity.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; assessment from source — permitted)
- decl `WeierstrassCurve.baseChange_ΨSq`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:494`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  *"This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid [an import cycle]."* (lines 12–13)

Qualified-name verification: the decl sits in `namespace WeierstrassCurve`
(opened line 27, closed line 511) inside `section BaseChange` (line 469). The
requested base name `baseChange_ΨSq` resolves to **`WeierstrassCurve.baseChange_ΨSq`**.
(Note: line 501 in the brief is actually `baseChange_Φ`; the requested
`baseChange_ΨSq` is at line 494. Assessed the named declaration `baseChange_ΨSq`.)

---

### Statement (Phase 1)

`WeierstrassCurve.baseChange_ΨSq` states: for a Weierstrass curve `W` over a
commutative ring `R`, and a tower of `R`/`S`-algebras `A`, `B` with an
`S`-algebra homomorphism `f : A →ₐ[S] B`, the `n`-th squared-division-polynomial
`ΨSqₙ` commutes with base change: the polynomial `(W.baseChange B).ΨSq n` equals
the image of `(W.baseChange A).ΨSq n` under the coefficient-wise map induced by
`f`. In symbols: `(W⁄B).ΨSqₙ = ((W⁄A).ΨSqₙ).map f`.

It is a naturality / compatibility lemma: base-changing the curve and then
forming the division polynomial = forming the division polynomial and then
base-changing (mapping coefficients).

Variables / typeclasses (Lean side):
- `{R} [CommRing R]`, `(W : WeierstrassCurve R)` — the base curve.
- `{S} [CommRing S] [Algebra R S]` — intermediate base ring.
- `{A} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]` — source algebra.
- `{B} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]` — target algebra.
- `(f : A →ₐ[S] B)` — the `S`-algebra hom along which we base-change.
- `(n : ℤ)` — the division-polynomial index.

Hypotheses: none beyond the typeclass/parameter setup.

Conclusion (math): `ΨSq` is natural with respect to base change along `f`.
Conclusion (Lean): `(W.baseChange B).ΨSq n = ((W.baseChange A).ΨSq n).map f`.

Proof body (2 mathlib-call rewrite):
```lean
lemma baseChange_ΨSq (n : ℤ) : (W.baseChange B).ΨSq n = ((W.baseChange A).ΨSq n).map f := by
  rw [← map_ΨSq, map_baseChange]
```
where `map_ΨSq` (line 445) is the ring-hom version and `map_baseChange` is the
fact that `(W.baseChange B) = (W.baseChange A).map f.toRingHom` (via the scalar
tower). It is a *glue lemma*.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a naturality helper lemma (one of an 11-lemma `baseChange_*` family),
glue-style `rw` proof; not a named theorem, not a project main result.

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. (For the record the body
is a 1-line `rw`, i.e. a glue lemma — relevant to Phase 6, not Phase 2b.)

---

### Literature search (Phase 3) — SHORT-CIRCUITED (justified)

The literature/standard-form protocol is **moot for this declaration** and is
recorded as deliberately short-circuited, not skipped. Reason: this is not a
question of "what is the standard form of this result and is mathlib's
generality right" — the declaration is a **byte-identical copy of a lemma that
already exists in mathlib under the very same qualified name**
`WeierstrassCurve.baseChange_ΨSq` (see Phase 5). When mathlib already contains
the *literal decl with the literal name*, the verdict is settled at Phase 5 and
the generality/idiom anchors have nothing to compare against (the "mathlib form"
*is* this form).

| #  | Channel                          | Query / action                                                        | Hit? | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|-------|
|  1 | mathlib source (decisive)        | grep mathlib `DivisionPolynomial/Basic.lean` for `baseChange_ΨSq`     | YES  | identical lemma at line 571 — see Phase 5; this resolves the verdict |
|  2 | Project's own module docstring   | read header of the project file                                       | YES  | states verbatim it *is a copy of* the mathlib file |
|  3 | WebSearch (concept, context)     | n/a — superseded                                                       | n/a  | "naturality of division polynomials under base change" is the content; mathlib already formalises it (this very lemma). No standard-form question remains once the identical decl is found. |
|  4 | ChatGPT MCP                       | n/a — superseded; MCP down per brief                                   | n/a  | nothing to adjudicate: it is a literal mathlib copy |
|  5 | Local references                 | n/a                                                                   | n/a  | source paper is mathlib itself (author David Kurniadi Angdinata, same on both copies) |
|  6 | nLab / Stacks / arXiv / MO       | n/a                                                                   | n/a  | not needed — see above; this is an internal naturality lemma already in mathlib |

### Literature summary (Phase 3)

Concept identified as: naturality of the (squared) division polynomial `ΨSqₙ`
under base change of a Weierstrass curve. Mathlib already encodes exactly this
as `WeierstrassCurve.baseChange_ΨSq`. No standard-form disagreement exists
because the declaration under assessment and the mathlib declaration are the
same statement and the same proof.

---

### Generality analysis (Phase 4) — n/a (identity with mathlib)

The mathlib lemma and the project lemma share the **same signature**: identical
`variable` block
`[Algebra R S] {A} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {B} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[S] B)`
(project lines 473–474 = mathlib lines 550–551) and identical conclusion. There
is therefore **no** generality gap to analyse: the current form is *exactly*
mathlib's form (which already weakens to `CommRing` + scalar-tower algebras and
indexes over `ℤ`).

Generality verdict (Phase 4b): EQUAL TO MATHLIB (neither narrower nor more
general). Weakening opportunities: 0 (any weakening would be a `/generalise`
ticket against mathlib's copy, not this fork).

Modern-idiom check (Phase 4c): n/a — the form is already mathlib's chosen
idiom (`AlgHom` base change + `Polynomial.map`); there is nothing to modernise
that wouldn't equally apply to the upstream lemma.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`.

---

### Mathlib search-status: `WeierstrassCurve.baseChange_ΨSq` (Phase 5)

[A] Lean-Finder       n/a (mathlib index): superseded by direct source grep (decisive hit below)
[B] Loogle            n/a: direct source match found; pattern search unnecessary
[C] LeanSearch        n/a: direct source match found
[D] Grep mathlib src  `grep -rn baseChange_ΨSq .lake/packages/mathlib/.../DivisionPolynomial/`  → **HIT**
[E] Name pattern      qualified name `WeierstrassCurve.baseChange_ΨSq` → **HIT (identical)**

Decisive evidence — the entire `section BaseChange` is duplicated verbatim:

mathlib `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:571`
```lean
lemma baseChange_ΨSq (n : ℤ) : (W⁄B).ΨSq n = ((W⁄A).ΨSq n).map f := by
  rw [← map_ΨSq, map_baseChange]
```
project `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:494`
```lean
lemma baseChange_ΨSq (n : ℤ) : (W.baseChange B).ΨSq n = ((W.baseChange A).ΨSq n).map f := by
  rw [← map_ΨSq, map_baseChange]
```
`W⁄B` is mathlib's *notation* for `W.baseChange B` — the two statements are the
same term up to notation; the proofs are character-identical. Same namespace
(`WeierstrassCurve`), same author (David Kurniadi Angdinata), same supporting
lemmas (`map_ΨSq`, `map_baseChange`). All 11 sibling `baseChange_*` lemmas match
line-for-line too.

Concluded: **found in mathlib as `WeierstrassCurve.baseChange_ΨSq`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:571`);
identical form.**

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.baseChange_ΨSq`
Internal use count: **0** (no occurrence anywhere in `projects/`, excluding the
declaring file). External-to-file callers: 0.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | —             |

Inline re-derivation grep: (none). The lemma is forked as a wholesale block, not
because any downstream proof in NagellLutz calls it. Files importing the forked
`LutzNagell.DivisionPolynomial` (`DivisionPolynomialDegree.lean`,
`DivisionPolynomialOmega.lean`, `LutzNagellTheorem/EvalBridge.lean`) do not
reference `baseChange_ΨSq`.

Composability: trivially derivable in mathlib already — it *is* a 2-call
`rw [← map_ΨSq, map_baseChange]`. But that is academic here: mathlib already
ships this exact lemma, so there is nothing to compose; consumers should use the
mathlib name directly.

Conclusion: NOT-A-NEW-LEMMA (mathlib has it verbatim).

---

## Verdict: `WeierstrassCurve.baseChange_ΨSq`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): superseded — the project's own docstring declares the file *a copy of* the mathlib source; same author.
- Generality analysis (Phase 4): EQUAL — identical signature to mathlib's copy; no gap.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.baseChange_ΨSq`, `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:571`; identical statement + proof (`W⁄B` = `W.baseChange B` notation).
- Composition check (Phase 6): 0 internal call sites; not a new lemma.

**Rationale:**

This declaration is not a candidate for mathlib because **mathlib already
contains it, verbatim, under the identical qualified name**
`WeierstrassCurve.baseChange_ΨSq`. The NagellLutz project forks the whole file
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` — its module
docstring says so explicitly (lines 12–13) — solely to swap one import
(`LutzNagell.EllipticDivisibilitySequence` for the mathlib
`Mathlib.NumberTheory.EllipticDivisibilitySequence`) and break an import cycle,
**not** because of any mathematical difference. The statement, the typeclass
context (scalar-tower `R`/`S`-algebras `A`, `B` with `f : A →ₐ[S] B`, index
`n : ℤ`), and the proof (`rw [← map_ΨSq, map_baseChange]`) coincide character-
for-character with mathlib lines 571–572; the only textual difference is
mathlib's `W⁄B` notation for `W.baseChange B`, which denotes the same term. All
ten sibling `baseChange_*` lemmas in the same section are likewise verbatim
copies.

Because the upstream lemma is literally present, every mathlibable phase is moot:
there is no generality gap (same signature), no modern-idiom improvement that
wouldn't apply equally upstream, and no composition to inline (mathlib exposes
the finished lemma). The project's copy has **zero internal call sites**, so it
is not even load-bearing within NagellLutz; it rides along only as part of the
forked block.

**WHY not (refactor-actionable):**
Mathlib already has the result, identically named. The project does not *need*
to delete this single lemma; the right disposition is the file-level one this
fork was created for. Two coherent paths:

1. **Preferred (whole-file dedup, a cleanup-lane concern, not a per-lemma one):**
   eliminate the forked `LutzNagell/DivisionPolynomial.lean` by removing the
   import cycle that forced the fork — make `LutzNagell.EllipticDivisibilitySequence`
   compatible with (or re-export) `Mathlib.NumberTheory.EllipticDivisibilitySequence`
   so the project can `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`
   and drop the entire copied file. All 11 `baseChange_*` lemmas (and the rest of
   the file) then come from mathlib for free.
2. **If the fork must stay** (cycle genuinely unbreakable for now): leave
   `baseChange_ΨSq` exactly as-is — it is correct and matches mathlib — and never
   submit it upstream (it is already there). Track the fork as a known mathlib
   duplication in the project's dedup notes.

Existing mathlib decl:        `WeierstrassCurve.baseChange_ΨSq`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:571`
Our form follows in 0 lines:  it is the same lemma (notation aside):
```lean
-- mathlib's lemma IS our statement; `W⁄B` unfolds to `W.baseChange B`
example (n : ℤ) : (W.baseChange B).ΨSq n = ((W.baseChange A).ΨSq n).map f :=
  WeierstrassCurve.baseChange_ΨSq f n
```
Call sites in our project (Phase 6.0): **K = 0**.
Refactor plan: there are no call sites to rewrite. Disposition is at the file
level — prefer path (1): break the `EllipticDivisibilitySequence` import cycle,
delete the forked `LutzNagell/DivisionPolynomial.lean`, and let the three
importers (`DivisionPolynomialDegree.lean`, `DivisionPolynomialOmega.lean`,
`LutzNagellTheorem/EvalBridge.lean`) pick up the mathlib module instead. If the
cycle cannot yet be broken, keep the lemma untouched and record it as an
intentional mathlib mirror — **do not** open a mathlib PR for it (it already
exists).
Next action: do **not** submit upstream. Route the fork to the cleanup lane as a
whole-file deduplication-against-mathlib item (import-cycle removal), not a
single-lemma deletion.

---

## Next step

Do not submit `baseChange_ΨSq` to mathlib — it is already there verbatim as
`WeierstrassCurve.baseChange_ΨSq`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:571`).
File a cleanup-lane item to dedup the forked `LutzNagell/DivisionPolynomial.lean`
against mathlib by removing the `EllipticDivisibilitySequence` import cycle that
forced the fork; if the cycle is currently unbreakable, leave the lemma as an
intentional mirror with zero call sites.
