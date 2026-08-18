# /mathlibable report — `WeierstrassCurve.coeff_preΨ`

**TL;DR — `NO-mathlib-has-it`.** This declaration is a **verbatim fork of mathlib's
own lemma** `WeierstrassCurve.coeff_preΨ`, which lives at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:279`. Same
namespace, same `variable (W : WeierstrassCurve R)`, **byte-identical statement**,
same original author (David Kurniadi Angdinata). The project copies the whole
mathlib file to dodge an EDS name clash; the fix is to de-fork, not to upstream.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — the decl elaborates in mathlib, where it already lives)
- decl `WeierstrassCurve.coeff_preΨ`:  ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:276` (the `@[simp] lemma coeff_preΨ` head is at line 275–276; statement body 276–277)
- kind:                     lemma (`@[simp]`)
- has sorry:                no
- module docstring summary: "Division polynomials of Weierstrass curves" — computes leading terms of `preΨ`, `ΨSq`, `Φ`; the file header says it is "a project copy of mathlib's Basic file" companion.

Qualified name (VERIFIED from source): **`WeierstrassCurve.coeff_preΨ`**
(namespace `WeierstrassCurve` opened at line 55; `variable {R} [CommRing R] (W : WeierstrassCurve R)` at line 57; base name `coeff_preΨ`).

---

### Statement (Phase 1)

`WeierstrassCurve.coeff_preΨ` states: for a Weierstrass curve `W` over a commutative
ring `R` and any integer `n`, the coefficient of the **"naïve division polynomial"**
`preΨ_n` (the polynomial part `ψ̃_n` of the `n`-th division polynomial, with the
`Ψ₂`-factor stripped from the even case so the result is univariate in `x`) at the
degree index `(|n|² − [4 if n even else 1]) / 2` equals `n/2` if `n` is even and `n`
if `n` is odd.

In standard notation: `preΨ_n` (Silverman's `ψ_n` up to the even-case `ψ₂` factor) has

- degree `(n² − 4)/2` and leading coefficient `n/2` when `n` is even,
- degree `(n² − 1)/2` and leading coefficient `n` when `n` is odd.

This lemma records the value of the top coefficient at that degree index. It is the
integer-indexed (`n : ℤ`) version, proved by `Int.negInduction` from the
ℕ-indexed `coeff_preΨ'`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring; commutative ring is the natural home for Weierstrass curves.
- `(W : WeierstrassCurve R)` — the curve, supplying `a₁…a₆` and the derived `bᵢ`.
- `(n : ℤ)` — the division index.

Hypotheses: none (the coefficient identity holds unconditionally; only `…_ne_zero`,
`natDegree_…`, `leadingCoeff_…` need `(n : R) ≠ 0`).

Conclusion (math): the degree-`(|n|²−…)/2` coefficient of `preΨ_n` is `if Even n then n/2 else n`.
Conclusion (Lean): `(W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) = if Even n then n / 2 else n`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline — it is a named structural fact about division
polynomials, explicitly listed under "## Main statements" in the file docstring as
`WeierstrassCurve.coeff_preΨ`). It is textbook material (Silverman ATEC, Exercise
3.7 / Lemma on division-polynomial degrees), so it is guaranteed to be near the
literature — which it is, including *in mathlib already*.

(Literature width is EXHAUSTIVE regardless; BIG/SMALL recorded for framing.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — one-liner check **n/a**.
(For the record, the proof is a 7-line `Int.negInduction`, not a one-liner anyway.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                                                                   | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial elliptic curve degree leading coefficient psi_n Silverman"                | yes  | `ψ_n`: lead coeff `n/2`, deg `(n²−4)/2` (even); lead coeff `n`, deg `(n²−1)/2` (odd)                   | Matches the Lean statement exactly. One hit was literally the **mathlib `Degree.lean` doc page**. |
|  2 | WebSearch (general / related)    | `"division polynomial" elliptic curve degree "n^2" leading term recursion`                     | yes  | `deg ψ_n² = n²−1`, `deg φ_n = n²`, recursion `Ψ₂ₘ₊₁ = Ψₘ₊₂Ψₘ³ − Ψₘ₋₁Ψₘ₊₁³`                            | MIT 18.783 Lecture 5; arXiv 1303.5002 / 1207.5387; standard recursion + degrees. |
|  3 | WebSearch (named-after / source) | (covered by #1/#2) Silverman ATEC Exercise 3.7; "coefficients of division polynomials"          | yes  | same; the even/odd split is the classical statement                                                    | jtnb.centre-mersenne.org/jtnb.881; arXiv 1303.4327 "Homogeneous division polynomials". |
|  4 | ChatGPT MCP                      | (MCP down per task) — fell back to WebSearch ×3 + textbook knowledge                            | n/a  | n/a — ChatGPT-math MCP unavailable in this environment                                                  | Standard form is unambiguous from #1–#3 + Silverman; second opinion not needed for a NO-has-it. |
|  5 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/` and `refs/`                               | n/a  | directory absent (no `references/`, no `refs/` store on this checkout)                                  | Recorded n/a. Mathlib's own file cites `[silverman2009]`. |
|  6 | nLab                             | "division polynomial"                                                                            | n/a  | not an nLab topic (elementary EC arithmetic, not categorical)                                           | nLab has no division-polynomial page; concept is classical AG/NT. |
|  7 | nCatLab (categorical)            | —                                                                                               | n/a  | not a categorical concept                                                                               | n/a. |
|  8 | Stacks Project (alg geom)        | "division polynomial"                                                                            | n/a  | Stacks does not treat explicit Weierstrass division polynomials                                         | Stacks is scheme-theoretic foundations; this explicit `R[X]` computation is out of its scope. |
|  9 | MathOverflow / Math.SE           | division polynomial degree even/odd leading coefficient                                          | yes  | confirms the even/odd `n/2` vs `n` split as standard folklore                                           | Consistent with #1. |
| 10 | recent arXiv (≤5 yr)             | "Division polynomials for arbitrary isogenies" (2503.15428); 1303.5002; 1801.02664              | yes  | degree/leading-coefficient facts reused as standard background                                          | These papers *cite* the degree facts as known; nobody claims them as new. |

### Literature summary (Phase 3)

Concept identified as: **division polynomials `ψ_n` of an elliptic / Weierstrass curve**, specifically the degree and leading coefficient of the univariate part `preΨ_n` (= Silverman's `ψ_n` modulo the `ψ₂` factor in the even case).
Sources agree on the standard form: **yes** — universally: even ⇒ (deg `(n²−4)/2`, lc `n/2`); odd ⇒ (deg `(n²−1)/2`, lc `n`).
Most general standard form: stated over a general commutative ring (the coefficient `n/2`/`n` and degree index are integers; the identity is a coefficient equality in `R[X]`, no domain/field hypothesis needed). **Mathlib already states it at exactly this generality.**
Generality dimensions where the literature varies: only the *normalisation* (`ψ_n` vs the `ψ̃_n = preΨ_n` with the `ψ₂` factor pulled out) — mathlib's `preΨ`/`preΨ'` is the standard "strip `ψ₂`" normalisation that keeps the polynomial univariate.
Disagreement with the literature: **none**.

---

### Generality analysis — `WeierstrassCurve.coeff_preΨ` (Phase 4)

Literature-standard form (from Phase 3): degree/leading-coefficient of `ψ_n` over a
general base, even/odd split — already matched.

| # | Parameter / hypothesis    | Current Lean form                | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------|----------------------------------|------------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`           | commutative ring                 | commutative ring (most general)    | NO                  | Weierstrass curves + their division polynomials are *defined* over `CommRing`; the `bᵢ` and the recursion need commutativity. This is already mathlib's choice for the whole `WeierstrassCurve` API. |
| 2 | `(n : ℤ)`                | integer index                    | integer index                      | NO                  | The integer version is the most general; the ℕ-version `coeff_preΨ'` is the *specialisation* (mathlib has both, exactly as here). |

#### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical to mathlib's, which is already at the maximal natural generality `CommRing` + `ℤ`).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

#### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Mathlib downstream |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | bundled-hypothesis preamble → typeclass/instance?                                         | no       | — `(W : WeierstrassCurve R)` is already the bundled-structure idiom mathlib uses | — |
|  2 | sequences/metric → filters/topology?                                                      | no       | — purely algebraic coefficient identity, no limits | — |
|  3 | construction → universal-property class?                                                  | no       | — `preΨ` is a concrete polynomial; no universal property at stake | — |
|  4 | set-with-closure-predicate → bundled substructure?                                        | no       | — no substructure here | — |
|  5 | vector-space/metric/field-specific → weaken to module/(semi)ring?                         | no       | — already over a general `CommRing` | — |
|  6 | 1-categorical → higher-categorical?                                                       | no       | — n/a | — |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive structure?                                      | no       | — `n` indexes the *recursion / division-by-n map*; it is intrinsically an integer (the EDS / multiplication-by-`n` index). Generalising past `ℤ` is meaningless. |

##### Modern-idiom verdict (Phase 4c)
Modern idiom available: **no**. This *is* the modern mathlib formulation — because it
**literally is the mathlib formulation**, written by mathlib's elliptic-curve author.

---

### Diamond / defeq risk (Phase 4.5)
n/a — declaration kind is `lemma` (no definitional equalities / instances introduced).

---

### Mathlib search-status: `WeierstrassCurve.coeff_preΨ` (Phase 5)

[A] Lean-Finder       (index stale locally) → relied on [D] direct source grep, which is dispositive
[B] Loogle            `WeierstrassCurve.preΨ` coeff pattern → not run online (stale); [D] is decisive
[C] LeanSearch        "coefficient of division polynomial preΨ degree" → superseded by [D]
[D] **Grep mathlib src** `coeff_preΨ` in `.lake/packages/mathlib/.../DivisionPolynomial/Degree.lean` → **HIT at line 279**: `@[simp] lemma coeff_preΨ (n : ℤ) : (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) = if Even n then n / 2 else n`
[E] Name pattern      grep `coeff_preΨ` mathlib → also finds `coeff_preΨ'` (ℕ-version, line 237), `coeff_preΨ₄` (line 130) — the whole family is present.

Searched for both:
  - the user's current form → **found, identical**.
  - the literature-standard form → same thing; mathlib has it at full `CommRing`/`ℤ` generality.

**Verified the hit is byte-identical:**
```
$ diff <project line 276-277>  <mathlib Degree.lean line 279-280>
STATEMENT LINES IDENTICAL
```
Namespace context identical (`namespace WeierstrassCurve`; `variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)`). The project file header literally says it is *"a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial`"* (companion to the Basic copy), forked only to import `LutzNagell.EllipticDivisibilitySequence` instead of mathlib's, to avoid the `normEDS`/`complEDS` name clash. The only diffs in the surrounding proofs are cosmetic tactic drift (`simpa … using` vs `simpa … using!`, one extra `Int.natAbs_natCast` simp lemma) from a slightly older mathlib snapshot — the **statement is unchanged**.

Concluded: **found in mathlib as `WeierstrassCurve.coeff_preΨ`; identical form.**

---

### Call sites — `WeierstrassCurve.coeff_preΨ` (Phase 6.0)

Internal use count: **0** within the project, outside the declaring file
(`grep -rn 'coeff_preΨ' projects --include='*.lean' | grep -v DivisionPolynomialDegree.lean`,
filtering out the unrelated `coeff_preΨ'` / `coeff_preΨ₄` / `coeff_preΨ_ne_zero` tokens → **0 matches**).

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | —             |

Within the declaring file it is used by `natDegree_preΨ` (line 297) and
`leadingCoeff_preΨ` (line 310) — but those are *also* verbatim forks of mathlib's
`natDegree_preΨ` / `leadingCoeff_preΨ`. So every consumer is itself a duplicate that
de-forking removes.

Inline-derivation grep (re-derived elsewhere without using the lemma?): (none) — the
fact is only ever obtained via this lemma family, which is exactly mathlib's.

Signal: K = 0 external uses; all in-file uses are themselves mathlib duplicates →
the entire fork is redundant. Strong `NO` signal.

### Composition check (Phase 6)

Can `WeierstrassCurve.coeff_preΨ` be derived from mathlib in ≤3 chained calls?

Attempt 1: `WeierstrassCurve.coeff_preΨ n` — i.e. the mathlib lemma of the *same name*.
  - Mathlib decls used: `WeierstrassCurve.coeff_preΨ` (the identical mathlib lemma).
  - Result: **succeeds** trivially — it is the same statement, so the "composition" is a 0-step `exact`.

Conclusion: this is the degenerate composition case — mathlib doesn't merely have the
*building blocks*, it has **the lemma itself**. That makes the verdict
`NO-mathlib-has-it` (the stronger NO), not `NO-composable-from-mathlib`.

---

## Verdict: `WeierstrassCurve.coeff_preΨ`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): standard textbook fact (Silverman ATEC Ex. 3.7; MIT 18.783 L5); even/odd degree+leading-coefficient split confirmed across ≥3 channels — and one WebSearch hit *is the mathlib `Degree.lean` doc page itself*.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical to mathlib's, which is at the maximal `CommRing`/`ℤ` generality. Phase 4c found no modernisation (it already is the mathlib form).
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.coeff_preΨ`** at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:279`; **byte-identical statement** (verified by `diff`).
- Composition check (Phase 6): degenerate — mathlib has the lemma itself; 0 external call sites.

**Rationale:**

`projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean` is a deliberate,
documented fork of mathlib's `…/DivisionPolynomial/Degree.lean`, and `coeff_preΨ` is
one line of that fork. The project's own `DivisionPolynomial.lean` header states it is
"a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`" forked
only to import `LutzNagell.EllipticDivisibilitySequence` (to avoid the `normEDS`/
`complEDS` name collision with mathlib's EDS file). The `Degree` copy is its companion.
The `coeff_preΨ` statement is byte-for-byte mathlib's, in the same `WeierstrassCurve`
namespace, with the same `variable (W : WeierstrassCurve R)`, by the same author. There
is nothing to upstream: mathlib already has it, at full generality, with a `@[simp]`
attribute and the entire surrounding `preΨ` / `ΨSq` / `Φ` degree API.

**WHY not (refactor-actionable):**
Mathlib already has this exact lemma. Our form does not "follow from" mathlib's — it
*is* mathlib's, character-for-character. The whole forked file should be deleted, not
upstreamed.

Existing mathlib decl:   `WeierstrassCurve.coeff_preΨ`
Located at:              `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:279`
Our form follows in ≤1 line (in fact 0 — same statement):
```lean
-- after `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`:
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) :
    (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) = if Even n then n / 2 else n :=
  W.coeff_preΨ n          -- mathlib's lemma, identical
```

Call sites in our project (from Phase 6.0): **0** external; in-file consumers
(`natDegree_preΨ`, `leadingCoeff_preΨ`) are themselves mathlib duplicates.

**Refactor plan (matches the sibling overview reports for `coeff_preΨ'`, `coeff_Ψ₃`, etc.):**
1. Resolve the EDS name clash that forced the fork — make the project `open`/alias
   mathlib's `EllipticDivisibilitySequence` (`normEDS`, `complEDS`, …) instead of
   re-defining them in `LutzNagell/EllipticDivisibilitySequence.lean`.
2. Delete the two duplicated copies wholesale:
   - `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean` (this file), and
   - its companion `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean` (the Basic copy).
3. Replace every `import LutzNagell.DivisionPolynomialDegree` with
   `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`
   (and `…DivisionPolynomial.Basic` where the Basic copy was imported). The
   `WeierstrassCurve.*` names — including `coeff_preΨ` — are unchanged, so call sites
   need no edit beyond the import line.

Because this de-fork is one coordinated cleanup across the whole `DivisionPolynomial`
copy (not a per-lemma action), `coeff_preΨ` should be handled together with its
siblings already triaged the same way (`natDegree_preΨ_le`, `coeff_preΨ'`,
`coeff_Ψ₃`, `leadingCoeff_Ψ₂Sq`, `mk_ψ₂_sq`, …) — i.e. delete the duplicated files in
one cleanup ticket, do not file a per-lemma deletion.

Next action: as part of the `DivisionPolynomial` de-fork cleanup ticket, delete this
file (and the Basic copy) and switch imports to mathlib. No mathlib PR — mathlib
already has `WeierstrassCurve.coeff_preΨ`.

---

## Next step

De-fork: resolve the EDS naming clash, then delete
`projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean` and its companion
`DivisionPolynomial.lean`, repointing imports at
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.{Degree,Basic}`. Mathlib
already contains `WeierstrassCurve.coeff_preΨ` verbatim; nothing to upstream.
