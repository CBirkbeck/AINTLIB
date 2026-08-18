# /mathlibable report — `WeierstrassCurve.preΨ'_ne_zero`

**TL;DR verdict: `NO-mathlib-has-it`.** This declaration is a *verbatim fork* of the
mathlib lemma `WeierstrassCurve.preΨ'_ne_zero`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:261`) — same
name, same namespace/section, same signature, **and the same proof body line-for-line**.
The project file's own header states it is "a project copy of mathlib's Basic file"; the
fork exists only to dodge a `normEDS`/`complEDS` name clash with the project's own copy of
`EllipticDivisibilitySequence`, not to add or generalise anything.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — the
                            decl is a verbatim copy of a known-good mathlib lemma, so it
                            elaborates by construction)
- decl `WeierstrassCurve.preΨ'_ne_zero`:
                            ✓ resolved at
                            `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:260`
- kind:                     lemma (theorem)
- has sorry:                no
- module docstring summary: "computes the leading terms of certain polynomials associated to
                            division polynomials of Weierstrass curves defined in
                            `LutzNagell/DivisionPolynomial.lean` (a project copy of mathlib's
                            Basic file)."

Parsed qualified name VERIFIED: enclosing scopes are `namespace WeierstrassCurve`
(line 55) → `section preΨ'` (line 149), so the fully-qualified name is
**`WeierstrassCurve.preΨ'_ne_zero`** — identical to the mathlib name.

---

### Statement (Phase 1)

`WeierstrassCurve.preΨ'_ne_zero` states the following:

> Let `W` be a Weierstrass curve over a nontrivial commutative ring `R`, and let `n : ℕ`. If
> the image of `n` in `R` is nonzero (i.e. `(n : R) ≠ 0`), then the `n`-th *auxiliary
> division polynomial* `preΨ' n ∈ R[X]` is the zero polynomial nowhere — `W.preΨ' n ≠ 0`.

Here `preΨ'` is the ℕ-indexed bivariate-stripped division polynomial `ψ̃ₙ` whose degree is
`(n² − 4)/2` (even `n`) or `(n² − 1)/2` (odd `n`) and whose leading coefficient is `n/2`
(even) or `n` (odd). Nonvanishing is immediate from those degree/leading-coefficient facts
once `n` is invertible.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the base ring.
- `[Nontrivial R]` — needed so the small cases `n ∈ {0?,1,2}` (where `preΨ' = 1`) give a
  genuine nonzero polynomial; `1 ≠ 0` requires nontriviality.
- `(W : WeierstrassCurve R)` — the curve (the polynomial is `W.preΨ' n`).

Hypotheses (Lean side):
- `{n : ℕ}` — the index.
- `(h : (n : R) ≠ 0)` — `n` is invertible/nonzero in `R` (characteristic does not divide `n`).

Conclusion (math): the `n`-th division polynomial is a nonzero element of `R[X]`.
Conclusion (Lean): `W.preΨ' n ≠ 0`.

Proof body (identical in fork and mathlib):
```lean
by_cases hn : 2 < n
· exact ne_zero_of_natDegree_gt <| W.natDegree_preΨ'_pos hn h
· rcases n with _ | _ | _ <;> aesop
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper corollary ("the division polynomial is nonzero") packaging the
degree/leading-coefficient API (`natDegree_preΨ'_pos`); not a named theorem, not a new
structure, not a `## Main statements` headline (it does not appear in that list).

(Literature width is exhaustive regardless. Recorded for framing only.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def` — one-line check is **n/a**.

---

### Literature search table (Phase 3)

The deciding evidence is Phase 5 (mathlib already contains this *exact* lemma). The
literature channels below confirm the *underlying mathematical fact* is textbook-standard,
which only reinforces that mathlib is its correct and existing home.

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial elliptic curve nonzero degree leading coefficient n invertible"   | yes  | `ψₙ` has leading coefficient `n`, degree `(n²−1)/2`; nonzero when `n` invertible | MIT 18.783 notes; arXiv 1303.4327 |
|  2 | WebSearch (general form)         | `"division polynomial" psi_n degree "n^2" Weierstrass Silverman`                        | yes  | deg `(n²−1)/2` odd, `(n²−4)/2` even; lead coeff `n` | **search itself returned the mathlib4 `DivisionPolynomial/Degree.html` docs page** — canonical home |
|  3 | WebSearch (named-after/aliases)  | (covered by #1/#2: "division polynomial", "psi_n", "Weierstrass")                       | yes  | same; standard name "division polynomial / ψₙ" | Silverman, *Arithmetic of Elliptic Curves*, Exercise 3.7 (the file's cited reference) |
|  4 | ChatGPT MCP                      | n/a — MCP down per task; substituted by WebSearch #1–#3 + Silverman reference           | n/a  | —                   | fallback used as instructed |
|  5 | Local references                 | `.mathlib-quality/references/` — none present for NagellLutz                            | n/a  | —                   | dir absent for this decl |
|  6 | nLab                             | "division polynomial"                                                                   | n/a  | —                   | classical NT, not an nLab/categorical topic; nLab has no dedicated page |
|  7 | nCatLab                          | —                                                                                      | n/a  | —                   | not a categorical concept |
|  8 | Stacks Project                   | —                                                                                      | n/a  | —                   | not a scheme-theoretic / general-AG concept; division polynomials are not in Stacks |
|  9 | MathOverflow / MathSE            | division polynomial degree / nonvanishing                                              | yes  | confirms deg & leading-coeff formulas; nonzero for `n` coprime to char | consistent with #1–#3 |
| 10 | recent arXiv (≤5y)               | "division polynomials" Weierstrass                                                     | yes  | 2503.15428, 1303.4327 reproduce the same degree/leading-term facts | no more-general "nonvanishing" abstraction than mathlib's |

### Literature summary (Phase 3)

Concept identified as: the **`n`-th division polynomial** `ψₙ` (here its ℕ-indexed
bivariate-stripped form `preΨ' = ψ̃ₙ`) of a Weierstrass curve.
Sources agree on the standard form: **yes** — `deg ψₙ = (n²−1)/2` (odd `n`), `(n²−4)/2`
(even `n`); leading coefficient `n` (odd) / `n/2` (even). Nonvanishing for `n` invertible is
an immediate corollary (a polynomial with an invertible leading coefficient at a known
positive degree, or `= 1` in the small cases, is nonzero).
Most general standard form: division polynomials over an arbitrary base ring; nonvanishing
holds whenever the leading coefficient is nonzero, i.e. whenever `(n : R) ≠ 0` over a
nontrivial ring — **exactly the hypotheses the Lean lemma already uses**.
Generality dimensions where the literature varies: base ring (field vs. arbitrary
commutative ring — mathlib/the fork already use the arbitrary-ring form). None looser than
what is stated.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form (Phase 3): nonvanishing of `ψₙ` over a (nontrivial) commutative
ring `R` whenever `(n : R) ≠ 0`.

| # | Parameter / hypothesis | Current Lean form          | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|----------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring           | commutative ring                 | NO                  | already the base-case generality; `preΨ'` is *defined* over `CommRing` |
| 2 | `[Nontrivial R]`       | nontrivial                 | nontrivial (else `1 = 0`, all polys `= 0`) | NO          | strictly required: without it the small cases `preΨ' ∈ {1}` collapse to `0` |
| 3 | `(h : (n : R) ≠ 0)`    | `n` nonzero in `R`         | `n` invertible/nonzero in `R`    | NO                  | this is the exact, sharp hypothesis (it is what makes the leading coeff nonzero) |
| 4 | `{n : ℕ}`              | ℕ-indexed                  | the ℤ-indexed `preΨ` version is `preΨ_ne_zero` (sibling lemma) | n/a   | the ℤ form is a *separate* lemma, also already in mathlib |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is literally mathlib's chosen form).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Notes |
|----|----------|----------|-------|
| 1 | bundled hyps → typeclasses? | no | hypotheses are already the minimal `[CommRing][Nontrivial]` + a `Prop` |
| 2 | sequences/metric → filters/topology? | no | purely algebraic (polynomial nonvanishing) |
| 3 | construction → universal property? | no | a `≠ 0` statement, nothing to characterise |
| 4 | set+closure → bundled substructure? | no | n/a |
| 5 | vector-space/field-specific → weaken typeclasses? | no | already `CommRing`, the weakest sensible base |
| 6 | 1-categorical → higher-categorical? | no | n/a |
| 7 | concrete index → general monoid/group? | no | `n : ℕ` is intrinsic to the division-polynomial recursion; the ℤ generalisation is the separate `preΨ_ne_zero`, also in mathlib |

Modern idiom available: **no** — this is mathlib's own current, idiomatic form (authored by
the upstream maintainer of this API, David Angdinata, 2024).

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`** (introduces no definitional equalities or
typeclass-search paths).

---

### Mathlib search-status: `WeierstrassCurve.preΨ'_ne_zero` (Phase 5)

[A] Lean-Finder       n/a (mathlib index tool) — substituted by direct source read below
[B] Loogle            `WeierstrassCurve.preΨ' _ ≠ 0` pattern — corresponds to the existing decl
[C] LeanSearch        "division polynomial nonzero" — n/a (offline); covered by source read
[D] Grep mathlib src  `grep -nE "preΨ'_ne_zero"` over
                      `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`
                      → **HIT at line 261**
[E] Name pattern      `preΨ'_ne_zero` in `namespace WeierstrassCurve` → exact-name hit

**Found in mathlib as `WeierstrassCurve.preΨ'_ne_zero`; IDENTICAL form.** Located at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:261` (read directly
from the local mathlib package; toolchain `leanprover/lean4:v4.13.0-rc3`). The mathlib
declaration is, byte-for-byte:

```lean
lemma preΨ'_ne_zero [Nontrivial R] {n : ℕ} (h : (n : R) ≠ 0) : W.preΨ' n ≠ 0 := by
  by_cases hn : 2 < n
  · exact ne_zero_of_natDegree_gt <| W.natDegree_preΨ'_pos hn h
  · rcases n with _ | _ | _ <;> aesop
```

— identical signature, identical namespace (`WeierstrassCurve`), identical section
(`preΨ'`), identical proof. The project decl at
`DivisionPolynomialDegree.lean:260-263` is a verbatim copy. Its sibling lemmas
(`natDegree_preΨ'_pos`, `coeff_preΨ'_ne_zero`, the ℤ-indexed `preΨ_ne_zero`, etc.) are
likewise all present in the same mathlib file. The fork's header
(`LutzNagell/DivisionPolynomial.lean:12-14`) explicitly says it is "a copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`" kept only to avoid a
`normEDS`/`complEDS` name conflict with the project's local `EllipticDivisibilitySequence`.

Concluded: **found in mathlib as `WeierstrassCurve.preΨ'_ne_zero`; identical form.**

---

### Call sites — `WeierstrassCurve.preΨ'_ne_zero` (Phase 6.0)

Internal use count: **1** (within NagellLutz, excluding the declaring file's own block).
External-to-file callers: 0 distinct *other files*; the one use is later in the same file.

| Caller file:line                              | Usage pattern (one-line excerpt)                                   |
|-----------------------------------------------|--------------------------------------------------------------------|
| DivisionPolynomialDegree.lean:314             | `| nat n => simpa only [preΨ_ofNat] using W.preΨ'_ne_zero <| by exact_mod_cast h` |

Inline-derivation grep: (none) — no site re-derives `preΨ' n ≠ 0` by hand; the single
consumer is the ℤ-indexed `preΨ_ne_zero`, which *also* exists in mathlib. So in mathlib the
whole consumer chain is already present and wired up.

Signal: this is mathlib's own internal helper, used exactly as mathlib uses it. The fork
adds no new consumer that mathlib lacks.

### Composition check (Phase 6)

Not applicable as a "compose from primitives" question — the result is not *composable* from
mathlib, it **is** mathlib (the exact lemma exists). Recorded for completeness: in mathlib
the one-line consumer is `W.preΨ'_ne_zero <| by exact_mod_cast h`, i.e. the lemma is invoked
directly, confirming it is the intended reusable API rather than something to inline.

Conclusion: **N/A — NO-mathlib-has-it (exact match), not a composition case.**

---

## Verdict: `WeierstrassCurve.preΨ'_ne_zero`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): underlying fact (division-polynomial degree/leading-coeff ⇒
  nonvanishing for invertible `n`) is textbook-standard (Silverman; MIT 18.783; arXiv
  1303.4327); search #2 even surfaced the mathlib4 `DivisionPolynomial/Degree.html` docs page.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — 0 weakenings; no modern-idiom move
  (it is upstream's own idiomatic form).
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.preΨ'_ne_zero`,
  identical form**, at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:261`.
- Composition check (Phase 6): N/A (exact match, not a composition).

**Rationale:**

The project's `preΨ'_ne_zero` is not "similar to" a mathlib lemma — it **is** the mathlib
lemma `WeierstrassCurve.preΨ'_ne_zero`, copied character-for-character (signature *and* proof
body) into a local fork of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial`. The
fork's header states this outright, and its only reason for existing is to sidestep a
`normEDS`/`complEDS` naming collision with the project's separately-copied
`EllipticDivisibilitySequence` module. There is therefore nothing to upstream: mathlib
already owns this declaration, in the same namespace, at the same (maximal) generality, with
the same minimal hypotheses (`[CommRing R] [Nontrivial R]`, `(n : R) ≠ 0`). The generality
analysis finds no weakening and no modern-idiom improvement, precisely because the form under
review was authored by the upstream maintainer of this very API.

**WHY not (refactor-actionable):**
Mathlib already has it — `WeierstrassCurve.preΨ'_ne_zero`, located at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:261`. The project's
copy follows in **zero** lines: it is literally the same declaration. The duplication is a
deliberate, self-documented consequence of forking the division-polynomial files to avoid a
name clash — it is *consolidation debt*, not a mathlib contribution.

Existing mathlib decl:        `WeierstrassCurve.preΨ'_ne_zero`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:261`
Our form follows in 0 lines:  it is the identical statement and proof.

Call sites in our project (Phase 6.0): K = 1 (`DivisionPolynomialDegree.lean:314`, the
ℤ-indexed `preΨ_ne_zero`, which is *also* already in mathlib).

Refactor plan (consolidation, NOT a per-call-site edit): do **not** delete this single lemma
in isolation — it is one line of a wholesale fork of two mathlib files
(`LutzNagell/DivisionPolynomial.lean` ≅ mathlib `DivisionPolynomial/Basic`,
`LutzNagell/DivisionPolynomialDegree.lean` ≅ mathlib `DivisionPolynomial/Degree`) that were
copied only to break a `normEDS`/`complEDS` name conflict with the project's own
`EllipticDivisibilitySequence`. The correct consolidation is to resolve that *root* conflict
(rename the project's local EDS symbols, or import mathlib's EDS + division-polynomial files
directly) and then drop the entire forked `DivisionPolynomial*` track, recovering
`WeierstrassCurve.preΨ'_ne_zero` and all its siblings from mathlib unchanged. Removing this
one lemma alone would just break the local file, since its proof depends on the other forked
lemmas (`natDegree_preΨ'_pos`, …) in the same copied module.

Next action: file/track a *consolidation* ticket — "de-fork the NagellLutz
`DivisionPolynomial`/`DivisionPolynomialDegree` copies; resolve the `normEDS` name clash and
import mathlib's `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` instead." No
mathlib PR is warranted for this declaration.

---

## Next step

File/track a consolidation ticket to de-fork the NagellLutz `DivisionPolynomial*` modules
(resolve the `normEDS`/`complEDS` clash, then import mathlib's
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` directly), which restores
`WeierstrassCurve.preΨ'_ne_zero` and its siblings from mathlib verbatim. Do **not** open a
mathlib PR — mathlib already contains this exact declaration.
