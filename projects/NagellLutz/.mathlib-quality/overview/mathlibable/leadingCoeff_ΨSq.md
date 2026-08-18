# /mathlibable report — `WeierstrassCurve.leadingCoeff_ΨSq`

**Verdict: NO-mathlib-has-it** — mathlib already contains this lemma *verbatim*
(statement **and** proof) at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:370`.
This project file is an explicit fork of that very mathlib file.

---

### Baseline (Phase 0)
- lake build:               not re-run (build stale per task note); decl reasoned from source.
- decl `WeierstrassCurve.leadingCoeff_ΨSq`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:368`
- kind:                      `lemma` (with `@[simp]`)
- has sorry:                 no
- module docstring summary:  "computes the leading terms of certain polynomials
  associated to division polynomials of Weierstrass curves defined in
  `LutzNagell/DivisionPolynomial.lean` (**a project copy of mathlib's Basic file**)."

---

### Statement (Phase 1)

`WeierstrassCurve.leadingCoeff_ΨSq` states: for a Weierstrass curve `W` over a
commutative ring `R` with no zero divisors, and an integer `n` whose image in `R`
is nonzero, the leading coefficient of the univariate polynomial `ΨSqₙ` (the
"squared division polynomial", congruent to `ψₙ²`) equals `n²`.

In standard notation: `lc(ψ_n²) = n²`, i.e. the squared n-th division polynomial
of an elliptic/Weierstrass curve has leading coefficient `n²` (and degree `n²−1`).

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the base commutative ring.
- `[NoZeroDivisors R]` — needed so the degree equality (`natDegree_ΨSq`) holds:
  the top coefficient `n²` must not vanish, which requires `(n : R) ≠ 0` to force
  `natDegree = n.natAbs² − 1`.
- `(W : WeierstrassCurve R)` — the curve.
- `{n : ℤ}` — the multiplication index.

Hypotheses:
- `(h : (n : R) ≠ 0)` — the index is invertible-enough: its image in `R` is
  nonzero (characteristic ∤ n). Without it the leading coefficient `n²` could be `0`.

Conclusion (math): `lc(ΨSqₙ) = n²`.
Conclusion (Lean): `(W.ΨSq n).leadingCoeff = n ^ 2`.

Proof body (one line):
```lean
rw [leadingCoeff, W.natDegree_ΨSq h, coeff_ΨSq]
```
i.e. unfold `leadingCoeff` to `coeff (natDegree)`, rewrite the degree via
`natDegree_ΨSq`, then read off the top coefficient via `coeff_ΨSq`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line corollary lemma combining two prior results
(`natDegree_ΨSq` + `coeff_ΨSq`); not a named theorem, not a new structure, not a
project main goal. (Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. No defeq/diamond/API
considerations apply to a propositional lemma.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found                              | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic curve division polynomial psi_n leading coefficient degree n^2 - 1"          | yes  | `deg(ψ_n²)=n²−1`, `lc(ψ_n²)=n²`                   | MIT 18.783 lecture notes (Sutherland); arXiv 1801.02664; **mathlib4 docs page for this exact file surfaced** |
|  2 | WebSearch (general/source form)  | "Silverman Arithmetic Elliptic Curves division polynomial psi_n leading term"          | yes  | `lc(ψ_n)=n`, hence `lc(ψ_n²)=n²`                  | Silverman, *Arithmetic of Elliptic Curves* (project's cited reference [silverman2009]); Exercise 3.7 / §III.3 |
|  3 | WebSearch (aliases)              | `"division polynomial" degree "leading coefficient" n^2 elliptic curve psi_n^2`        | yes  | same; `ΨSqₙ` ↔ `ψ_n²`                             | Confirms mathlib doc page (`...DivisionPolynomial.Degree`) as a top hit — direct evidence mathlib hosts this |
|  4 | ChatGPT MCP                      | (not run — MCP reported down per task note; covered by channels 1-3 + 6-10)            | n/a  | —                                                | Fallback: WebSearch ×3 + nLab + arXiv suffice; the fact is textbook-standard and unambiguous |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "division polynomial"                          | n/a  | (no references dir present for this triage)      | Project cites Silverman 2009 in the module docstring; that is the source. |
|  6 | nLab                             | "division polynomial" / "elliptic curve division polynomial"                           | n/a  | nLab has no division-polynomial degree page      | Not an nLab-style abstract concept; recorded n/a. |
|  7 | nCatLab                          | —                                                                                      | n/a  | not a categorical concept                        | Concrete polynomial-degree fact; no categorical content. |
|  8 | Stacks Project                   | "division polynomial"                                                                  | n/a  | Stacks does not treat division polynomials        | Arithmetic-of-EC topic, outside Stacks' scheme-theory scope. |
|  9 | MathOverflow / MSE               | "leading coefficient division polynomial psi_n^2"                                       | yes  | `lc(ψ_n)=n`, `deg ψ_n = (n²−1)/2` (n odd) — standard | Multiple Q&A restate the same; no disagreement. |
| 10 | recent arXiv (≤5y)               | (covered by #1-#3 hits: 1303.4327, 1801.02664, 1303.5002)                              | yes  | homogeneous/coeff papers all assume `lc(ψ_n²)=n²` | Treated as background fact in current literature. |

### Literature summary (Phase 3)

Concept identified as: **leading coefficient of the (squared) division polynomial
of an elliptic / Weierstrass curve** (`ψ_n²`, mathlib's `ΨSqₙ`).
Sources agree on the standard form: **yes** — universally, `lc(ψ_n) = n` and hence
`lc(ψ_n²) = n²`, with `deg(ψ_n²) = n²−1`. Textbook (Silverman III) and lecture
notes (Sutherland 18.783) and recent arXiv all agree.
Most general standard form: stated over the coordinate ring; mathlib's universal /
integral-domain phrasing with hypothesis `(n : R) ≠ 0` is the natural ring-level
generalisation and matches the literature.
Generality dimensions where the literature varies: only base ring (field in most
textbooks vs. mathlib's `CommRing R` + `NoZeroDivisors R`). mathlib is already at
or above the textbook generality.
Disagreement with the literature: **none**.

---

### Generality analysis (Phase 4)

Literature-standard form: `lc(ψ_n²) = n²` over a base where `n ≠ 0`.

| # | Parameter / hypothesis      | Current Lean form              | Literature-standard       | Weaker form exists? | Reason |
|---|-----------------------------|--------------------------------|---------------------------|---------------------|--------|
| 1 | `[CommRing R]`              | commutative ring               | usually a field           | NO (already weaker) | mathlib already generalises the textbook field to a comm. ring — strictly *more* general than literature. |
| 2 | `[NoZeroDivisors R]`        | no zero divisors               | (field ⇒ implies it)      | NO                  | required so `natDegree_ΨSq` pins the degree; the `n²` top coeff must be a non-zero-divisor witness. Cannot drop in general. |
| 3 | `(h : (n : R) ≠ 0)`         | index nonzero in `R`           | char ∤ n                  | NO                  | exactly the textbook hypothesis (characteristic coprime to `n`); minimal. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (in fact already more general than the
textbook field statement). Number of weakening opportunities: 0.
Cost of restatement: n/a. This is moot — see Phase 5: mathlib *already has this
exact lemma at this exact generality*.

### Modern-idiom check (Phase 4c)

Modern idiom available: **no.** This is a concrete polynomial-degree identity
(`leadingCoeff = n^2`). No "let X be a foo" preamble to classify, no
sequence-vs-filter axis, no universal-property reformulation, no
substructure-bundling, no typeclass weakening beyond what mathlib already does
(comm-ring + NoZeroDivisors), no higher-categorical lift, and the index `n : ℤ`
is intrinsic to division polynomials (not a generalisable concrete index).
Rows 1-7 all `no`. One-line reason: it is a finite algebraic coefficient identity
already stated in mathlib's idiomatic ring-level form.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (propositional). No definitional equalities or
typeclass-search paths introduced.

---

### Mathlib search-status (Phase 5)

[A] Lean-Finder       "leading coefficient division polynomial squared"   → hit: the mathlib `DivisionPolynomial.Degree` namespace.
[B] Loogle            `WeierstrassCurve.ΨSq ?n |>.leadingCoeff = ?n ^ 2`  → hit: `WeierstrassCurve.leadingCoeff_ΨSq`.
[C] LeanSearch        "leading coefficient of squared division polynomial of Weierstrass curve" → hit: same decl.
[D] Grep mathlib src  `grep "leadingCoeff_ΨSq" .lake/packages/mathlib/...` → **HIT**:
      `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:370`.
[E] Name pattern      `leadingCoeff_ΨSq`                                  → exact-name hit in mathlib.

Searched for both the user's form and the literature-standard form — both resolve
to the same mathlib lemma.

**Concluded: found in mathlib as `WeierstrassCurve.leadingCoeff_ΨSq`; IDENTICAL
form (and identical proof).** Direct byte comparison:

- Project (`DivisionPolynomialDegree.lean:368-370`):
  ```lean
  @[simp]
  lemma leadingCoeff_ΨSq [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
      (W.ΨSq n).leadingCoeff = n ^ 2 := by
    rw [leadingCoeff, W.natDegree_ΨSq h, coeff_ΨSq]
  ```
- Mathlib (`DivisionPolynomial/Degree.lean:369-372`): **character-for-character
  identical** (same `@[simp]`, signature, `[NoZeroDivisors R]`, hypothesis, and
  one-line proof). Verified by `diff`.

Moreover the underlying `WeierstrassCurve.ΨSq` definition is itself identical
(project `DivisionPolynomial.lean:165` vs mathlib `Basic.lean:242`):
`W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1`. The project forked mathlib's
`Basic`/`Degree` files **solely** to swap the EDS import
(`LutzNagell.EllipticDivisibilitySequence` instead of mathlib's) and avoid
`normEDS`/`complEDS` name conflicts — not to change any mathematics.

---

### Call sites (Phase 6.0) — `WeierstrassCurve.leadingCoeff_ΨSq`

Internal use count (NagellLutz, excluding declaring file): **0**
External-to-file callers: 0 (the only other repo mention is a docstring bullet in
`HasseWeil/.../Auxiliary/DivisionPolynomial.lean:20`, which is prose, not a call —
and HasseWeil maintains its *own* parallel fork of these results).

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | no `leadingCoeff_ΨSq` applications anywhere in the project |

Inline-derivation grep: (none) — no site re-derives `lc(ΨSqₙ)=n²` by hand either.

Signal: `K = 0` internal uses, no inline re-derivation. Combined with "mathlib has
it verbatim", this is a textbook NO-mathlib-has-it: the lemma exists only because
the file is a wholesale copy of mathlib's `Degree.lean`.

### Composition check (Phase 6)

Can it be derived from mathlib in ≤3 calls? Trivially — it **is** a mathlib lemma.
Attempt 1: `exact WeierstrassCurve.leadingCoeff_ΨSq h` (0 work; direct reference).
Conclusion: **COMPOSABLE / redundant** — but the precise verdict is the stronger
NO-mathlib-has-it (mathlib has the named lemma itself, not merely building blocks).

---

## Verdict: `WeierstrassCurve.leadingCoeff_ΨSq`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): standard textbook fact (`lc(ψ_n²)=n²`); Silverman
  III + Sutherland 18.783; the mathlib4 docs page for this exact file appeared as a
  top web hit.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (already ≥ textbook generality);
  modern-idiom check: no reformulation applies.
- Mathlib search (Phase 5): **found in mathlib as
  `WeierstrassCurve.leadingCoeff_ΨSq`**, byte-identical statement and proof, at
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:370`.
- Composition check (Phase 6): redundant; `exact …leadingCoeff_ΨSq h`. Call sites: 0.

**Rationale:**

This is the clearest possible NO-mathlib-has-it. The project's
`DivisionPolynomialDegree.lean` is, by its own module docstring, a copy of
mathlib's `DivisionPolynomial/Degree.lean`, and `leadingCoeff_ΨSq` is reproduced
character-for-character — same `@[simp]` attribute, same `WeierstrassCurve`
namespace, same `[NoZeroDivisors R]` hypothesis, same `(n : R) ≠ 0` side
condition, same one-line proof `rw [leadingCoeff, W.natDegree_ΨSq h, coeff_ΨSq]`.
The companion definition `WeierstrassCurve.ΨSq` is likewise identical to mathlib's.
The fork exists for a purely technical reason — to import the project's local
`EllipticDivisibilitySequence` (avoiding a `normEDS`/`complEDS` clash) — not to
state any new mathematics. There is nothing to upstream: mathlib authored this
exact lemma (David Kurniadi Angdinata, the same author credited in both file
headers).

**WHY not (refactor-actionable):**
Mathlib already has the result, identically. The project copy is redundant; it
exists only as collateral of forking the whole file to swap one import.

Existing mathlib decl:        `WeierstrassCurve.leadingCoeff_ΨSq`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:370`
Our form follows in ≤1 line (in fact it *is* the same decl):
```lean
example [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
    (W.ΨSq n).leadingCoeff = n ^ 2 :=
  WeierstrassCurve.leadingCoeff_ΨSq h
```
Call sites in our project (Phase 6.0): **K = 0**.

Refactor plan: this decl is not a candidate for a mathlib PR. The only project-side
action is the standard fork-deduplication question for the *whole* file: if/when
NagellLutz can use mathlib's `DivisionPolynomial.*` directly (i.e. once the local
`EllipticDivisibilitySequence` fork is reconciled with mathlib's `normEDS`/`complEDS`
— the actual reason for the copy), then `DivisionPolynomialDegree.lean` (including
`leadingCoeff_ΨSq` and its siblings `natDegree_ΨSq`, `coeff_ΨSq`, `leadingCoeff_Φ`,
…) should be deleted wholesale in favour of importing mathlib. Since `K = 0`, no
in-project call sites need rewiring for this particular lemma. This is a
file-level dedup ticket, not a per-lemma one, and it is **gated on the EDS-fork
reconciliation**, which is the genuine blocker (out of scope for this single-decl
triage).

Next action: no mathlib PR. Track the whole-file fork-dedup (and its EDS-fork
prerequisite) as a consolidation ticket; this lemma rides along with the file.

---

## Next step

No mathlib PR — mathlib already contains `WeierstrassCurve.leadingCoeff_ΨSq`
verbatim. File/track a consolidation ticket to retire the NagellLutz fork of
`DivisionPolynomial/Degree.lean` once the local `EllipticDivisibilitySequence`
fork (the reason for the copy) is reconciled with mathlib.
