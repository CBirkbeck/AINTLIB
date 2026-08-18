# /mathlibable report — `WeierstrassCurve.coeff_preΨ_ne_zero`

> Step-9 (overview) mathlibable assessment, NagellLutz project.
> Date: 2026-06-22. Read-only on `.lean`; this report is the only file written.

## TL;DR

**Verdict: `NO-mathlib-has-it`.** The declaration is a **verbatim fork** of
mathlib's own `WeierstrassCurve.coeff_preΨ_ne_zero`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:289`).
Same qualified name, same signature, same proof (modulo cosmetic `using!`/`using`
and one extra `simp` lemma). The project's `LutzNagell/DivisionPolynomial*.lean`
files are explicitly "a project copy of mathlib's Basic file" (file docstring,
line 14). Action: delete the local copy and `import` mathlib's `Degree.lean`.

---

### Baseline (Phase 0)

- lake build:               not run (sandbox build stale per task brief); reasoned from source. Both decls elaborate in their respective trees.
- decl `WeierstrassCurve.coeff_preΨ_ne_zero`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:286`
- kind:                      lemma (`theorem`)
- has sorry:                 no
- module docstring summary:  "Division polynomials of Weierstrass curves … (a project copy of mathlib's Basic file)" — leading-term/degree computations for `preΨ`, `ΨSq`, `Φ`.

Parsed/verified qualified name: namespace `WeierstrassCurve` (opened at line 55),
base name `coeff_preΨ_ne_zero` ⇒ **`WeierstrassCurve.coeff_preΨ_ne_zero`** (the
task's guessed qualified name is correct).

---

### Statement (Phase 1)

`WeierstrassCurve.coeff_preΨ_ne_zero` states: for a Weierstrass curve `W` over a
commutative ring `R` and an integer `n` whose image in `R` is non-zero
(`(n : R) ≠ 0`), the coefficient of the *expected leading degree*
`d = (|n|² − (4 if n even else 1)) / 2` of the auxiliary division polynomial
`preΨ_n ∈ R[X]` is non-zero. Combined with the matching degree bound
`natDegree_preΨ_le`, this pins down `preΨ_n` as having exactly degree `d` and the
stated leading coefficient — the engine for `natDegree_preΨ` / `leadingCoeff_preΨ`.

Variables / typeclasses:
- `{R : Type u} [CommRing R]` — the base ring.
- `(W : WeierstrassCurve R)` — the curve (`preΨ` is `W.preΨ`).

Hypotheses:
- `{n : ℤ}` — the division index (the `ℤ`-indexed `preΨ`, defined from the `ℕ`-indexed `preΨ'`).
- `(h : (n : R) ≠ 0)` — characteristic condition: `n` is invertible-enough that the leading coeff (`n` or `n/2`) survives in `R`.

Conclusion (math): `[x^d] preΨ_n ≠ 0` in `R`, where `d = (|n|² − (4 if 2∣n else 1))/2`.

Conclusion (Lean): `(W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) ≠ 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL.**
Reason: helper `coeff … ≠ 0` lemma; the `ℤ`-index lift of the `ℕ`-case
`coeff_preΨ'_ne_zero`; not a named theorem, not a `## Main results` headline goal
of NagellLutz (the project's goal is Nagell–Lutz; this is reused machinery).
(Literature width is exhaustive regardless — but see Phase 3 note: the dominating
fact is that this is a mathlib fork, which short-circuits the standard-form hunt.)

### One-line check (Phase 2b)

Kind is `theorem`/`lemma`, not a `def`/`abbrev`/`structure` ⇒ **n/a.** No
one-liner analysis required.

---

### Literature search (Phase 3) — dominated by the fork finding

**Dominating observation.** This declaration is a **byte-near-identical fork of an
existing mathlib declaration with the same fully-qualified name.** Per the
mathlibable verdict gate, that fact alone fixes the bucket at `NO-mathlib-has-it`:
a fork of a live mathlib decl cannot be "absent from mathlib", "more general than
mathlib", or "a modernisation mathlib lacks" — it *is* the mathlib decl. The
literature/standard-form hunt (whose purpose is to decide the right form for a
*novel* contribution) is therefore not load-bearing here and is recorded as
not-applicable-by-dominance. For completeness:

| #  | Channel                          | Query                                                       | Hit? | Standard form found | Notes |
|----|----------------------------------|-------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | n/a — see dominating observation                            | n/a  | —                   | Concept (division-polynomial leading term) is Silverman *AEC* Exercise 3.7 / Ch. III; mathlib's file already cites `silverman2009`. |
|  2 | WebSearch (general form)         | n/a — dominated                                             | n/a  | —                   | The "general form" question is moot: the decl already lives in mathlib over an arbitrary `CommRing R`. |
|  3 | WebSearch (named-after/aliases)  | n/a — dominated                                             | n/a  | —                   | "division polynomial" / "ψ_n"; not a person-named theorem. |
|  4 | ChatGPT MCP                      | n/a — MCP down per brief; dominated                         | n/a  | —                   | Would not change a fork verdict. |
|  5 | Local references                 | (no `.mathlib-quality/references/` PDFs consulted)          | n/a  | —                   | Source is Silverman *AEC*; mathlib file header already records it. |
|  6 | nLab                             | n/a — dominated                                             | n/a  | —                   | Elementary polynomial-degree fact; not an nLab concept. |
|  7 | nCatLab                          | n/a                                                          | n/a  | —                   | Not categorical. |
|  8 | Stacks Project                   | n/a                                                          | n/a  | —                   | Not the relevant register (concrete `R[X]` coefficient computation). |
|  9 | MathOverflow / MSE               | n/a — dominated                                             | n/a  | —                   | — |
| 10 | recent arXiv                     | n/a — dominated                                             | n/a  | —                   | Classical (19th-c. division polynomials); no recent-form question. |

### Literature summary (Phase 3)

Concept identified as: leading-term / degree-`d`-coefficient non-vanishing for the
(reduced) division polynomial `ψ_n` of a Weierstrass curve — classical (Silverman,
*The Arithmetic of Elliptic Curves*, III.3 and Exercise 3.7).
Sources agree on the standard form: yes (over a domain / char ∤ n); mathlib has
generalised it to an arbitrary `CommRing` with the explicit `(n : R) ≠ 0` hypothesis.
Most general standard form: exactly the mathlib form (arbitrary `CommRing R`,
`(n : R) ≠ 0`) — which is what the project copy also states.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4) — not-applicable-by-dominance

The decl is identical to mathlib's, over the same typeclass (`CommRing R`) with the
same hypothesis. There is no generality gap to close: the project form *is* the
mathlib form.

| # | Parameter / hypothesis | Current Lean form | Mathlib form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------|---------------------|--------|
| 1 | `[CommRing R]`         | comm ring         | comm ring (identical) | NO          | `preΨ` needs ring structure; mathlib already states it at this generality. |
| 2 | `(h : (n : R) ≠ 0)`    | `(n:R) ≠ 0`       | `(n:R) ≠ 0` (identical) | NO          | Sharp: the leading coeff is `n` (odd) / `n/2` (even); it can vanish in `R` exactly when this fails. |

**Generality verdict (4b):** MAXIMALLY GENERAL — and identical to mathlib's. K = 0
weakening opportunities. No restatement.

**Modern-idiom verdict (4c):** No modern-idiom move. The decl is already mathlib's
own contemporary formulation (ℤ-indexed `preΨ` via `Int.negInduction`, `coeff`
spelled with `natAbs`). Rows 1–7 of the Bourbaki-2.0 table are all `no` — there is
nothing to modernise relative to mathlib because this *is* the mathlib decl.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities / typeclass-search
paths introduced).

---

### Mathlib search-status: `WeierstrassCurve.coeff_preΨ_ne_zero` (Phase 5)

[A] Lean-Finder       n/a (offline) — superseded by direct source grep below.
[B] Loogle            n/a (offline) — superseded by direct source grep below.
[C] LeanSearch        n/a (offline) — superseded by direct source grep below.
[D] Grep mathlib src  `coeff_preΨ_ne_zero` over `.lake/packages/mathlib/…/DivisionPolynomial/` → **HIT**, exact name.
[E] Name pattern      `coeff_preΨ`, `natDegree_preΨ` → full family present in mathlib `Degree.lean`.

Searched for both the user's current form and the (identical) literature-standard
form.

**Concluded:** found in mathlib as **`WeierstrassCurve.coeff_preΨ_ne_zero`**;
**identical form** —
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:289`.

Side-by-side (project / mathlib):

```lean
-- project: DivisionPolynomialDegree.lean:286
lemma coeff_preΨ_ne_zero {n : ℤ} (h : (n : R) ≠ 0) :
    (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) ≠ 0 := by
  induction n using Int.negInduction with
  | nat n => simpa only [preΨ_ofNat, Int.even_coe_nat, Int.natAbs_natCast]
      using W.coeff_preΨ'_ne_zero <| by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, coeff_neg, neg_ne_zero, Int.natAbs_neg, even_neg]
        using ih n <| neg_ne_zero.mp <| by exact_mod_cast h

-- mathlib: Degree.lean:289 (same author: David Kurniadi Angdinata)
lemma coeff_preΨ_ne_zero {n : ℤ} (h : (n : R) ≠ 0) :
    (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) ≠ 0 := by
  induction n using Int.negInduction with
  | nat n => simpa only [preΨ_ofNat, Int.even_coe_nat]
      using! W.coeff_preΨ'_ne_zero <| by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, coeff_neg, neg_ne_zero, Int.natAbs_neg, even_neg]
        using! ih n <| neg_ne_zero.mp <| by exact_mod_cast h
```

Only differences: `using!` (mathlib) vs `using` (project), and the project's `nat`
branch carries one extra simp lemma `Int.natAbs_natCast`. Both are the same David
Angdinata file, drifted slightly across a mathlib bump. The underlying object is
the same: `preΨ` is defined identically (`DivisionPolynomial.lean:117` ≡
`Basic.lean:194`), as are `preΨ_ofNat` / `preΨ_neg`.

---

### Composition check (Phase 6)

**Call sites — `WeierstrassCurve.coeff_preΨ_ne_zero`**

Internal use count (outside declaring file): **0.**
External-to-file callers: **0 distinct files.**

| Caller file:line | Usage pattern |
|------------------|---------------|
| (within declaring file) DivisionPolynomialDegree.lean:297 | `natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_preΨ_le n) <| W.coeff_preΨ_ne_zero h` |

Inline-derivation grep elsewhere: (none) — it is used exactly as in mathlib, only
as the engine of `natDegree_preΨ` in the same file.

**Composable from mathlib primitives in ≤3 calls?**

Attempt 1: the proof is an `Int.negInduction` with two `simpa … using …` branches
that delegate to the ℕ-case `coeff_preΨ'_ne_zero` (itself an even/odd case split).
This is a genuine ~6-line inductive proof, not a `.symm`/`.trans`/single-call
composition.
- Result: fails as a composition.

**Conclusion: NOT-COMPOSABLE** (which is correct and expected — we do not want
`NO-composable`; we want `NO-mathlib-has-it`, because mathlib already *has* the
finished lemma, identically named). The right move is `import`, not inline.

---

## Verdict: `WeierstrassCurve.coeff_preΨ_ne_zero`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): not load-bearing — dominated by the fork finding; concept is classical (Silverman *AEC* III.3), already in mathlib.
- Generality analysis (Phase 4): MAXIMALLY GENERAL and **identical** to mathlib (same `CommRing R`, same `(n:R)≠0`). No modern-idiom gap.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.coeff_preΨ_ne_zero`; identical form** at `Degree.lean:289`.
- Composition check (Phase 6): NOT-COMPOSABLE (genuine inductive proof) — so the disposition is *import/delete*, not *inline*.

**Rationale.**

The NagellLutz project carries a private fork of mathlib's elliptic-curve
division-polynomial files (`LutzNagell/DivisionPolynomial.lean` and
`…DivisionPolynomialDegree.lean`), explicitly described in its own docstring as "a
project copy of mathlib's Basic file" and bearing the same author header (David
Kurniadi Angdinata) as the mathlib originals. `coeff_preΨ_ne_zero` is one decl in
that fork. Mathlib's
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` contains a
declaration with the **same fully-qualified name** `WeierstrassCurve.coeff_preΨ_ne_zero`,
the **same signature** verbatim, and the **same proof** up to a cosmetic `using!`
vs `using` and one redundant simp lemma. Because `preΨ`, `preΨ_ofNat`, and
`preΨ_neg` are also defined identically in both trees, the two lemmas are about the
same mathematical object, not a coincidental name clash. There is therefore nothing
to upstream: this is the mathlib lemma.

**WHY not (refactor-actionable):**
Mathlib already has it — `WeierstrassCurve.coeff_preΨ_ne_zero`. It is not a
specialisation we'd derive; it is the same lemma. The reason a project copy exists
is the AINTLIB consolidation context: this fork predates (or sits beside) the
upstreamed mathlib version, and the file was copied wholesale to let the project
build before the bump that pulled the real file into mathlib.

- Existing mathlib decl:        `WeierstrassCurve.coeff_preΨ_ne_zero`
- Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:289`
- Our form follows in ≤1 line (it *is* the same statement):
  ```lean
  example {n : ℤ} (h : (n : R) ≠ 0) :
      (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) ≠ 0 :=
    W.coeff_preΨ_ne_zero h   -- the mathlib lemma, same name
  ```
- Call sites in our project (Phase 6.0): **0** external (used only at
  `DivisionPolynomialDegree.lean:297` inside the same forked file, exactly as in
  mathlib).

**Refactor plan.** Do not delete this single lemma in isolation — it is one decl of
a whole forked pair of files. The correct consolidation move is to **drop the
project's `LutzNagell/DivisionPolynomial.lean` + `LutzNagell/DivisionPolynomialDegree.lean`
fork entirely and replace their `import` with mathlib's**
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` and
`…DivisionPolynomial.Degree`. Then every internal user of `W.preΨ` / `coeff_preΨ` /
`natDegree_preΨ` (all in the same namespace `WeierstrassCurve`, same names)
resolves against mathlib with no call-site edits. If a downstream NagellLutz file
needs a `preΨ` fact mathlib lacks, add *that* fact on top of mathlib's file rather
than re-forking. (Verify only that no project decl depends on the cosmetic proof
difference — it cannot, since the *statement* is identical.)

**Next action:** delete the forked `DivisionPolynomial*.lean` pair from NagellLutz
and import mathlib's `DivisionPolynomial.Basic` + `DivisionPolynomial.Degree`;
`coeff_preΨ_ne_zero` (and its whole `preΨ`/`ΨSq`/`Φ` family) then comes from mathlib
unchanged.

---

## Next step

Delete `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean` and
`projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean` (the mathlib fork)
and replace their imports with
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` and
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`. No new lemma
is contributed; `WeierstrassCurve.coeff_preΨ_ne_zero` is already in mathlib,
identically.
