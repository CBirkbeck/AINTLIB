# /mathlibable report — `WeierstrassCurve.natDegree_ΨSq`

**Verdict: NO-mathlib-has-it** (mathlib has this *literal* declaration — the project
file is a verbatim fork of the mathlib source).

---

### Baseline (Phase 0)
- lake build:               (stale locally; reasoned from source + pinned mathlib tree under `.lake/packages/mathlib/`)
- decl `WeierstrassCurve.natDegree_ΨSq`:  ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:359`
- kind:                      lemma (`theorem`)
- has sorry:                 no
- module docstring summary:  "computes the leading terms of certain polynomials associated to division
  polynomials of Weierstrass curves" — file header states it is "a project copy of mathlib's Basic file".

---

### Statement (Phase 1)

`WeierstrassCurve.natDegree_ΨSq` states: for a Weierstrass curve `W` over a commutative ring `R`
with no zero divisors, and an integer `n` whose image in `R` is nonzero, the univariate polynomial
`ΨSqₙ` (the square of the `n`-th division polynomial `ψₙ`, i.e. `ψₙ²`, expressed as a polynomial in `x`)
has `natDegree` exactly `|n|² − 1`.

Mathematically: `deg(ψₙ²) = n² − 1`. This is the standard Silverman fact (deg `ψₙ² = n²−1`,
leading coefficient `n²`), valid over an integral domain of characteristic not dividing `n`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the base ring.
- `[NoZeroDivisors R]` — integral-domain-like hypothesis (needed so the leading coefficient `n²` is nonzero).
- `(W : WeierstrassCurve R)` — the curve.
- `{n : ℤ}` — the multiplication index.

Hypotheses (Lean side):
- `(h : (n : R) ≠ 0)` — `n` is nonzero in `R` (characteristic does not divide `n`); ensures the top coefficient survives.

Conclusion (math): `deg(ΨSqₙ) = |n|² − 1`.
Conclusion (Lean): `(W.ΨSq n).natDegree = n.natAbs ^ 2 - 1`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: helper degree-lemma; one-line proof composing two prior lemmas (`natDegree_ΨSq_le`,
`coeff_ΨSq_ne_zero`) via `natDegree_eq_of_le_of_coeff_ne_zero`. Not a named theorem, not a new
structure. (Literature width run regardless; result moot — see Phase 5.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def` — one-line `def` check is **n/a**. (The proof body is a single term,
but the one-liner heuristic targets definitions; this is a theorem.)

---

### Literature search (Phase 3)

This phase is essentially moot: Phase 5 finds the **literal declaration already in mathlib**, so
the "is the form standard / is it in the literature" question is settled by mathlib itself. Recorded
for completeness.

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific) | "division polynomial psi_n degree n^2-1 leading coefficient Silverman" | yes | `deg(ψₙ²) = n²−1`, leading coeff `n²` | **top hit is the mathlib doc page** `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` — confirms upstream presence; Sutherland MIT 18.783 Lecture 6 and Silverman *Arithmetic of Elliptic Curves* Ch. III give the same fact |
| 2 | WebSearch (general) | (degree of ψₙ² over a domain) | yes | same; valid over integral domain, char ∤ n | matches the `[NoZeroDivisors R]` + `(n:R)≠0` hypotheses exactly |
| 3 | WebSearch (aliases) | "division polynomial" "leading coefficient" | yes | ψₙ standard; ΨSq = ψₙ² is the project/mathlib name for the *polynomial* square | name `ΨSq` is mathlib's own |
| 4 | ChatGPT MCP | (standard form + generality) | n/a | — | MCP flagged down in this environment; substituted by the mathlib doc-page hit, which is authoritative for "is this the mathlib form" |
| 5 | Local references | `refs/NagellLutz/` Silverman | n/a | — | refs are local-only/gitignored; Silverman is the cited source (`[silverman2009]`) and the fact is textbook-standard |
| 6 | nLab | "division polynomial" | n/a | — | not an nLab-style categorical concept |
| 7 | nCatLab | — | n/a | — | not categorical |
| 8 | Stacks Project | — | n/a | — | elementary elliptic-curve fact, not in Stacks' scope |
| 9 | MathOverflow / MSE | division polynomial degree | yes | `n²−1` confirmed | standard |
| 10 | recent arXiv | "division polynomial" degree | yes | eprint 2010/630, arXiv:1801.02664 etc. all use `deg ψₙ = (n²−1)/2`, `deg ψₙ² = n²−1` | consistent |

### Literature summary (Phase 3)

Concept identified as: **degree of the (squared) division polynomial of an elliptic / Weierstrass curve** (`deg ψₙ² = n² − 1`).
Sources agree on the standard form: **yes** — Silverman, Sutherland, and the mathlib doc page all give `n² − 1`.
Most general standard form: over an integral domain with `n ≠ 0` in the ring — exactly the Lean hypotheses.
Disagreement with the literature: none. The Lean statement *is* the standard fact, at the standard generality.

---

### Generality analysis (Phase 4)

Moot (mathlib has the identical decl), but the form is already maximally general for this fact.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring | NO | division polynomials are defined over a CommRing; can't weaken. |
| 2 | `[NoZeroDivisors R]` | no zero divisors | integral domain | NO | needed so leading coeff `n²` ≠ 0 fixes the degree; this is the weakest hypothesis that works (weaker than `IsDomain`, which would also force nontriviality). |
| 3 | `(h : (n : R) ≠ 0)` | `n` nonzero in `R` | char ∤ n | NO | exactly the needed condition; the `_le` bound version drops it, and mathlib already has that too (`natDegree_ΨSq_le`). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**. Weakening opportunities: 0.
This is mathlib's own chosen form (`[NoZeroDivisors R]` rather than `[IsDomain R]` is already the
weaker, more general idiom). Nothing to generalise.

### Modern-idiom check (Phase 4c)

Modern idiom available: **no**. This is a finite degree identity over a ring; there is no
sequence→filter, construction→universal-property, or set→bundled-substructure move. mathlib's own
formulation (the one this file copies) is already the idiomatic one — `natAbs` index over `ℤ`,
`NoZeroDivisors` typeclass, `@[simp]`. n/a.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (theorem). No definitional equalities or instances introduced.

---

### Mathlib search-status: `WeierstrassCurve.natDegree_ΨSq` (Phase 5)

[A] Lean-Finder       (index unavailable offline)   n/a — substituted by direct source read of pinned mathlib tree
[B] Loogle            `(WeierstrassCurve.ΨSq _ _).natDegree = _`   hits — `WeierstrassCurve.natDegree_ΨSq` (via mathlib doc page)
[C] LeanSearch        "natDegree of ΨSq division polynomial"        hit — mathlib doc page surfaced by WebSearch #1
[D] Grep mathlib src  `natDegree_ΨSq` in `.lake/packages/mathlib/`  **HIT** — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:361`
[E] Name pattern      `lemma natDegree_ΨSq`                          **HIT** — same file/line, `@[simp]`, same signature

Searched for both the user's form and the literature-standard form: same form.

**Concluded: found in mathlib as `WeierstrassCurve.natDegree_ΨSq`; IDENTICAL form (verbatim copy).**

Decisive evidence — the mathlib decl is **byte-for-byte identical** to the project decl:

mathlib `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:361`:
```lean
@[simp]
lemma natDegree_ΨSq [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
    (W.ΨSq n).natDegree = n.natAbs ^ 2 - 1 :=
  natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_ΨSq_le n) <| W.coeff_ΨSq_ne_zero h
```
project `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:359` — character-identical
(`@[simp]`, same signature, same proof term).

Further confirmation this is the *same object*, not a renamed variant:
- The underlying def `WeierstrassCurve.ΨSq` is mathlib's own (`.../DivisionPolynomial/Basic.lean:242`).
- Same author (David Kurniadi Angdinata, 2024), same module docstring, same "Main statements" list.
- A `diff` of the two whole files (modulo the `module`/`public import` header lines) shows only the
  docstring reference line and a few **cosmetic** proof differences in *other* lemmas (`convert!` vs
  `convert`, `↦` vs `=>`, an extra `Int.natAbs_natCast` rewrite). The `natDegree_ΨSq` statement and
  proof differ in **zero** characters. The project file is a fork of mathlib's `Degree.lean`.
- The current mathlib pin (`69aaaa313f44`, lakefile.toml) already contains this file — i.e. it is in
  *upstream* mathlib today, independent of AINTLIB.

---

### Composition check (Phase 6)

### Call sites — `WeierstrassCurve.natDegree_ΨSq`

Internal use count (across AINTLIB, excluding the declaring file): **2 real call sites** (+2 doc mentions).

| Caller file:line | Usage pattern |
|------------------|---------------|
| `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:33` | `_ = n.natAbs ^ 2 - 1 := natDegree_ΨSq _ hn` |
| `projects/HasseWeil/HasseWeil/OrdAtInftyBridge.lean:168` | `..., W.natDegree_ΨSq hnF]` (rw) |
| `projects/HasseWeil/HasseWeil/OrdAtInftyBridge.lean:146` | docstring mention ("mathlib's `natDegree_Φ` / `natDegree_ΨSq`") |
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:20` | docstring mention |

Telling detail: the HasseWeil docstring at `OrdAtInftyBridge.lean:146` literally calls these
"**mathlib's** `natDegree_Φ` / `natDegree_ΨSq`" — the consumers already regard this as a mathlib
lemma. They resolve to the project fork only because NagellLutz re-declares it in the same
`WeierstrassCurve` namespace within the one Lake workspace.

Inline re-derivation grep: none — consumers call the lemma by name, they don't re-derive the degree.

### Composition check (Phase 6a)

Not applicable in the usual sense (we don't need to *compose* mathlib primitives — mathlib has the
finished lemma). For completeness: the proof itself is a 1-line composition of
`natDegree_eq_of_le_of_coeff_ne_zero` with the two sibling lemmas `natDegree_ΨSq_le` and
`coeff_ΨSq_ne_zero` — but those siblings are *also* already in mathlib's `Degree.lean`. So the
correct action is not "inline a composition" but "drop the fork and use the mathlib lemma".

Conclusion: **NOT-COMPOSABLE (irrelevant)** — superseded by the exact-match in Phase 5.

---

## Verdict: `WeierstrassCurve.natDegree_ΨSq`

**Category: NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): standard Silverman fact `deg ψₙ² = n²−1`; the top web hit is the
  mathlib doc page for this very declaration.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — and it is mathlib's own chosen form.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.natDegree_ΨSq`, verbatim-identical**,
  at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:361`.
- Composition check (Phase 6): n/a — exact match supersedes.

**Rationale:**

This is not a "mathlib has something equivalent" case — it is the strongest possible NO. The project's
`DivisionPolynomialDegree.lean` is a *fork* of mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`
(same author, same docstring, same lemma list), and the `natDegree_ΨSq` declaration is byte-for-byte
identical to the upstream one, including its `@[simp]` attribute and its one-line proof. The underlying
`ΨSq` definition is likewise mathlib's. The current mathlib pin (`69aaaa313f44`) already contains this
file, so the lemma is in upstream mathlib *today*. Contributing it would be re-submitting an existing
mathlib lemma.

**WHY not (refactor-actionable):**
Mathlib already has the literal lemma. The project copy exists only because the NagellLutz project
forked mathlib's division-polynomial degree file (per its own module docstring: "a project copy of
mathlib's Basic file"). The whole `section ΨSq` of the fork — `natDegree_ΨSq_le`, `coeff_ΨSq`,
`coeff_ΨSq_ne_zero`, `natDegree_ΨSq`, `natDegree_ΨSq_pos`, `leadingCoeff_ΨSq`, `ΨSq_ne_zero` — is
duplicated from mathlib. None of it is new.

Existing mathlib decl:        `WeierstrassCurve.natDegree_ΨSq`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:361`
Our form follows in ≤1 line:  it *is* the mathlib form (identical statement + proof) — nothing to derive.

Call sites in AINTLIB (from Phase 6.0): 2 real (`PIDIntegralMultiple.lean:33`, `OrdAtInftyBridge.lean:168`).

Refactor plan (consolidation):
1. Delete the forked `DivisionPolynomial.lean` / `DivisionPolynomialDegree.lean` copies from
   NagellLutz (or at minimum the duplicated `ΨSq`/`preΨ`/`Φ` degree sections) and replace
   `import LutzNagell.DivisionPolynomialDegree` with
   `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`.
2. The two call sites already use the exact name `WeierstrassCurve.natDegree_ΨSq` with the same
   argument shape (`W.natDegree_ΨSq h` / `natDegree_ΨSq _ hn`), so they need **no edit** — they will
   resolve to the mathlib lemma once the fork is removed. Verify argument order is unchanged (it is:
   `(h : (n:R) ≠ 0)` is the sole explicit arg, `W` via dot-notation or `_`).
3. Build to confirm the mathlib lemma satisfies both consumers (it must — same statement).

Caveat for the human consolidator: confirm *why* NagellLutz forked the file in the first place. The
cosmetic proof diffs in *other* lemmas (e.g. `convert` vs `convert!`) suggest the fork may predate a
mathlib bump and exists to pin a specific proof under an older toolchain, or to expose decls without
the new `module`/`public` system. If the fork is purely historical, the entire copied file should be
deleted in favour of the mathlib import. `natDegree_ΨSq` specifically carries no project-specific
change, so it is safe to drop regardless.

Next action: delete the NagellLutz fork of `DivisionPolynomial*.lean` (the `ΨSq` degree section at
minimum); switch consumers to `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`.
No PR to mathlib — the lemma is already there.

---

## Next step

Delete `WeierstrassCurve.natDegree_ΨSq` (and its duplicated siblings) from the NagellLutz fork;
replace the project import with `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`.
The 2 call sites need no change (identical name + signature). Flag the broader fork-removal to the
consolidation coordinator.

Sources:
- [Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.html)
- [Sutherland, MIT 18.783 Lecture 6](https://math.mit.edu/classes/18.783/2015/LectureNotes6.pdf)
