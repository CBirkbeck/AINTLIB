# /mathlibable report — `WeierstrassCurve.preΨ'_four`

## TL;DR

**Verdict: `NO-mathlib-has-it`.** This declaration is a **byte-for-byte copy** of
`WeierstrassCurve.preΨ'_four` already in mathlib at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:173-174`
(same namespace, same `@[simp]`, same proof `preNormEDS'_four ..`). The project
file's own module docstring states it is a deliberate copy of that mathlib file,
forked only to import the project's local `EllipticDivisibilitySequence` (to dodge
`normEDS`/`complEDS` name conflicts). Nothing new to upstream.

---

### Baseline (Phase 0)
- lake build:               not re-run (build is known-stale per task brief); mathlib package present and read directly from `.lake/packages/mathlib`.
- decl `WeierstrassCurve.preΨ'_four`:  ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:96`
- kind:                      lemma (glue lemma — body is a single `preNormEDS'_four ..` call)
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

---

### Statement (Phase 1)

`WeierstrassCurve.preΨ'_four` is the lemma stating that the auxiliary
division-polynomial sequence `preΨ'`, evaluated at `n = 4`, equals the explicit
degree-6 polynomial `preΨ₄`:

> For a Weierstrass curve `W` over a commutative ring `R`, `W.preΨ' 4 = W.preΨ₄`,
> where `preΨ' n := preNormEDS' (W.Ψ₂Sq²) W.Ψ₃ W.preΨ₄ n` is the normalised
> elliptic-divisibility-sequence auxiliary, and
> `preΨ₄ = 2X⁶ + b₂X⁵ + 5b₄X⁴ + 10b₆X³ + 10b₈X² + (b₂b₈ − b₄b₆)X + (b₄b₈ − b₆²)`.

Mathematically this is just the **base case `n = 4`** of the `preNormEDS'`
recurrence: `preNormEDS'` is defined to take the value `d` at 4, and here
`d = preΨ₄`. So the lemma is a one-step definitional unfolding, not a named
theorem.

Variables / typeclasses (Lean side):
- `{R : Type r} [CommRing R]` — base commutative ring.
- `(W : WeierstrassCurve R)` — the curve whose `b`-invariants feed `preΨ₄`.

Hypotheses (Lean side): none.

Conclusion (math): `preΨ'(4) = preΨ₄` (the 4th auxiliary equals its defining 4th term).
Conclusion (Lean): `W.preΨ' 4 = W.preΨ₄` (an equation in `R[X]`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: helper/glue lemma — a single `@[simp]` unfolding of a recurrence base
case; not a named result, not a `def`, not a project main goal.

### One-line check (Phase 2b)

Body line count: 1 (`preNormEDS'_four ..`). Kind is `lemma`, not `def` — the
one-liner-def exemption machinery does not apply. Recorded as a one-line note; no
defeq/diamond/API-anchor analysis needed (those gate `def`/`class`/`instance`).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic curve division polynomial psi_4 formula b2 b4 b6 b8 normalised elliptic divisibility sequence" | yes  | `ψ₄ = ψ₂·(2x⁶+b₂x⁵+5b₄x⁴+10b₆x³+10b₈x²+(b₂b₈−b₄b₆)x+(b₄b₈−b₆²))` | The auxiliary factor is exactly `preΨ₄`. Matches Silverman AEC III.3 / standard refs. |
|  2 | WebSearch (general form)         | "division polynomial" elliptic curve recurrence initial values psi_3 psi_4 standard form        | yes  | general-Weierstrass ψ₃, ψ₄ + the `ψ_{2m+1}`, `ψ₂ψ_{2m}` recurrences | Confirms the EDS recurrence `preΨ'` implements; `preΨ₄` is the universal n=4 datum. |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2) "elliptic divisibility sequence" recurrence                                  | yes  | Ward's EDS / normalised EDS | `preNormEDS'`/`normEDS` = normalised EDS (Ward 1948); arXiv 2102.07573 gives the recurrence. |
|  4 | ChatGPT MCP                      | n/a                                                                                            | n/a  | —                   | MCP down per task brief; substituted with extra WebSearch + direct mathlib-source read, which is dispositive (exact-copy match). |
|  5 | Local references                 | grep `.mathlib-quality/references/` for division polynomial                                     | n/a  | —                   | No references dir for this concept in NagellLutz; recorded n/a. |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                        | n/a  | —                   | nLab has no dedicated division-polynomial page; concept is classical AG, covered by #1/#2. Not load-bearing — the decl is an exact mathlib copy. |
|  7 | nCatLab                          | —                                                                                              | n/a  | —                   | Not a categorical concept. |
|  8 | Stacks Project                   | division polynomial                                                                             | n/a  | —                   | Stacks does not treat elliptic-curve division polynomials; not its scope. |
|  9 | MathOverflow / MSE               | division polynomial psi_4 general Weierstrass                                                   | yes  | same as #1          | Standard formula widely reproduced; no controversy on the form. |
| 10 | recent arXiv (last 5 years)      | (returned by #1/#2) arXiv 2102.07573, 1108.3051, 2503.15428                                     | yes  | EDS recurrence + division-poly valuations | Confirms the `preNormEDS'` recurrence and the ψ₄ factor are the contemporary standard. |

### Literature summary (Phase 3)

Concept identified as: **the 4th division polynomial / 4th term of the normalised
elliptic divisibility sequence** of a Weierstrass curve (Ward EDS; Silverman AEC
exercise 3.7 / III.3).
Sources agree on the standard form: **yes** — the auxiliary factor
`2x⁶+b₂x⁵+5b₄x⁴+10b₆x³+10b₈x²+(b₂b₈−b₄b₆)x+(b₄b₈−b₆²)` is the universally-quoted
general-Weierstrass ψ₄/ψ₂.
Most general standard form: division polynomials over the **general Weierstrass
model** (the `aᵢ`/`bᵢ` form), over an arbitrary commutative base ring — which is
**exactly** what mathlib (and this copy) already implement.
Generality dimensions where the literature varies: model choice (short vs general
Weierstrass) — mathlib uses the most general (general Weierstrass, arbitrary
`CommRing`). No dimension is left un-generalised.
Disagreement with the literature: none.

Note: `preΨ'_four` itself is **not** a named literature theorem — it is the
n = 4 base-case readout of the recurrence. The standard material it rests on
(the ψ₄ formula, the EDS recurrence) is fully classical and **already in mathlib**.

---

### Generality analysis — `WeierstrassCurve.preΨ'_four`

Literature-standard form (from Phase 3): general-Weierstrass division polynomials
over an arbitrary commutative ring.

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form        | Weaker form exists? | Reason |
|---|------------------------|--------------------------|----------------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring         | commutative ring (general Weierstrass) | NO            | Already maximal; division polynomials need ring structure (the `bᵢ` are ring elements); mathlib states it at exactly this generality. |
| 2 | `(W : WeierstrassCurve R)` | general Weierstrass curve | general Weierstrass model     | NO                  | Most general elliptic-curve model; short-Weierstrass would be a *specialisation*, not a generalisation. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical to mathlib's, which is the
maximal sensible generality: general Weierstrass model over an arbitrary
`CommRing`). Number of weakening opportunities found: **0**.
Cost of restatement: n/a — no restatement available or needed.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Notes |
|----|----------|----------|-------|
| 1 | typeclasses instead of bundled hyps? | no | already typeclass-based (`[CommRing R]`); curve is the natural bundled object. |
| 2 | filters/topology instead of sequences/metric? | no | purely algebraic identity in `R[X]`; no topology. |
| 3 | universal-property class instead of construction? | no | `preΨ'` is a concrete recurrence; mathlib's chosen formulation. |
| 4 | bundled substructure instead of set+predicate? | no | n/a. |
| 5 | weaken vector-space/field/metric to module/(semi)ring? | no | already over arbitrary `CommRing`. |
| 6 | higher-categorical generalisation? | no | n/a. |
| 7 | concrete index → arbitrary monoid/group? | no | `n = 4` is a literal base-case readout; "generalising the index" is the *recurrence itself* (`preΨ'_even`/`preΨ'_odd`), which mathlib also already has. |

Modern idiom available: **no**. This is the contemporary mathlib formulation
verbatim (it *is* the source of truth being copied). One-line reason: the decl is
an exact copy of the current mathlib idiom, authored by the same person (Angdinata).

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search
paths introduced).

---

### Mathlib search-status: `WeierstrassCurve.preΨ'_four`

[A] Lean-Finder       n/a (offline) — superseded by direct source hit
[B] Loogle            n/a (offline) — superseded by direct source hit
[C] LeanSearch        n/a (offline) — superseded by direct source hit
[D] Grep mathlib src  `grep "preΨ'_four" .lake/packages/mathlib/.../DivisionPolynomial/Basic.lean`  → **HIT, line 173-174**, byte-identical (`@[simp] lemma preΨ'_four : W.preΨ' 4 = W.preΨ₄ := preNormEDS'_four ..`)
[E] Name pattern      grep `preNormEDS'_four` in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` → **HIT, line 157** (the lemma this proof cites also exists in mathlib)

Searched for both the user's current form and the literature-standard form; both
are present in mathlib.

Concluded: **"found in mathlib as `WeierstrassCurve.preΨ'_four`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:173`);
identical form."** The supporting `preNormEDS'_four` is likewise already in mathlib
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:157`). The entire
surrounding API in the project file (`preΨ'`, `preΨ₄`, `Ψ₃`, `Ψ₂Sq`,
`preΨ'_zero/one/two/three`, `preΨ'_even/odd`, …) is a line-for-line copy of the
mathlib file.

---

### Call sites — `WeierstrassCurve.preΨ'_four`

Internal use count: **4** (within NagellLutz, outside the declaring statement).
External-to-file callers: 1 distinct file (DivisionPolynomialDegree.lean) + 2
further uses inside the declaring file's later lemmas.

| Caller file:line                          | Usage pattern (one-line excerpt) |
|-------------------------------------------|-----------------------------------|
| DivisionPolynomial.lean:303               | `... preΨ'_four, preΨ'_two, mul_one, if_pos even_two]` (rewrite in a `Φ`-lemma) |
| DivisionPolynomial.lean:307               | `... Φ_ofNat, preΨ'_four, if_neg <| by decide, ...` |
| DivisionPolynomial.lean:308               | `... preΨ'_odd, preΨ'_four, preΨ'_two, if_pos Even.zero, ...` |
| DivisionPolynomialDegree.lean:207         | `| four => simpa only [preΨ'_four] using ⟨W.natDegree_preΨ₄_le, ...⟩` |

Inline-derivation grep: (none) — every consumer goes through the named lemma.
These call sites are themselves copies of the analogous mathlib uses; in mathlib
they resolve against `Mathlib`'s own `preΨ'_four`. Within the project they resolve
against the local copy purely because the file forks the import.

### Composition check (Phase 6)

Can `preΨ'_four` be derived from mathlib in ≤3 chained calls? — **Yes, trivially:
it IS a mathlib lemma.** `WeierstrassCurve.preΨ'_four` (mathlib) is the same
statement; the proof `preNormEDS'_four ..` is one mathlib call. But the relevant
finding is stronger than "composable": the exact lemma already exists, so the
question is moot.

Conclusion: **NOT-COMPOSABLE is irrelevant — mathlib HAS the lemma outright.**

---

## Verdict: `WeierstrassCurve.preΨ'_four`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the ψ₄ / normalised-EDS material is classical and
  standard; `preΨ'_four` is a base-case readout, not a named theorem.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical to mathlib's form;
  no modern-idiom improvement (it *is* the mathlib idiom, same author).
- Mathlib search (Phase 5): **found in mathlib as
  `WeierstrassCurve.preΨ'_four`,
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:173-174`,
  byte-for-byte identical** (incl. `@[simp]` and proof). Supporting lemma
  `preNormEDS'_four` also in mathlib (`EllipticDivisibilitySequence.lean:157`).
- Composition check (Phase 6): moot — the lemma exists verbatim.

**Rationale:**

This is the cleanest possible `NO-mathlib-has-it`. The declaration is not merely
*derivable* from mathlib — it is a **verbatim copy** of an existing mathlib lemma,
character-for-character (same namespace `WeierstrassCurve`, same `@[simp]`
attribute, same signature `W.preΨ' 4 = W.preΨ₄`, same proof term
`preNormEDS'_four ..`). The project's own module docstring is explicit: the file
"is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`"
that swaps in the project's local `EllipticDivisibilitySequence` to avoid the
`normEDS`/`complEDS` name clash. It was authored by David Kurniadi Angdinata, who
is also the mathlib author of the original — this is a fork-for-import-hygiene, not
a new contribution. There is nothing to upstream.

**WHY not (refactor-actionable):**
Mathlib already has it. The user's form does not merely *follow* from the mathlib
decl — it *is* the mathlib decl. The only reason the project carries its own copy
is the upstream forking of `Mathlib.NumberTheory.EllipticDivisibilitySequence`
(the project's `LutzNagell.EllipticDivisibilitySequence` redefines `normEDS`,
`complEDS`, etc., so importing mathlib's `DivisionPolynomial.Basic` directly would
double-define those names). `preΨ'_four` cannot be a mathlib contribution because
mathlib is where it came from.

Existing mathlib decl:        `WeierstrassCurve.preΨ'_four`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:173`
Our form follows in ≤1 line (it is identical):
```lean
-- mathlib already proves exactly this:
@[simp] lemma WeierstrassCurve.preΨ'_four {R} [CommRing R] (W : WeierstrassCurve R) :
    W.preΨ' 4 = W.preΨ₄ := preNormEDS'_four ..
```
Call sites in our project (from Phase 6.0):  **K = 4**
(DivisionPolynomial.lean:303, 307, 308; DivisionPolynomialDegree.lean:207)

Refactor plan: this lemma is **not independently deletable**. It is one entry in a
whole copied file (`LutzNagell/DivisionPolynomial.lean`), and that copy exists
solely because the project forks `EllipticDivisibilitySequence`. The correct
disposition is at the *file/project* level, not this single decl:

1. The right fix is to **reconcile the forked `LutzNagell.EllipticDivisibilitySequence`
   with mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`** (eliminate
   the `normEDS`/`complEDS` redefinitions, or rename the project's versions). Once
   the fork is removed, the whole `LutzNagell/DivisionPolynomial.lean` copy —
   including `preΨ'_four` and its siblings — can be deleted and every call site
   (the K = 4 above, plus all the other `preΨ'_*`/`preΨ_*`/`Ψ*` uses) re-pointed at
   `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` by adjusting
   imports only. No argument-order changes are needed — the names and signatures
   are identical.
2. Until that reconciliation happens, the copy is load-bearing for the project's
   build and should stay. This is consolidation/dedup work for the AINTLIB `main`
   fleet (a `lane:cleanup` cross-project dedup ticket against the *whole* forked
   file), **not** a mathlib PR and not a single-lemma deletion.

Next action: do **not** open a mathlib PR. File an AINTLIB cleanup/dedup ticket to
de-fork `LutzNagell.EllipticDivisibilitySequence` vs. mathlib, after which
`LutzNagell/DivisionPolynomial.lean` (this lemma included) is deleted wholesale and
its call sites re-imported from mathlib.

---

## Next step

File an AINTLIB cross-project dedup ticket: reconcile the forked
`LutzNagell.EllipticDivisibilitySequence` with
`Mathlib.NumberTheory.EllipticDivisibilitySequence`, then delete the copied
`LutzNagell/DivisionPolynomial.lean` (containing `preΨ'_four`) and re-point all
`preΨ'_*` call sites at mathlib's `DivisionPolynomial.Basic`. No mathlib PR — the
lemma already lives in mathlib verbatim.
