# /mathlibable report — `LutzNagell.LutzNagellTheorem.shortCurveQ_equation_iff`

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); reasoning from source
- decl `LutzNagell.LutzNagellTheorem.shortCurveQ_equation_iff`: resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean:53`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Sets up the short Weierstrass curve `y² = x³ + A·x + B` over ℤ and its
  base change to ℚ, and proves basic rewriting lemmas (equation, discriminant).

### Statement (Phase 1)

`shortCurveQ_equation_iff` states: for integers `A B` and rationals `x y`, the affine point `(x, y)`
lies on the short Weierstrass curve `shortCurveQ A B` (the ℚ-base-change of `{a₁=a₂=a₃=0, a₄=A, a₆=B}`)
**iff** `y² = x³ + (A:ℚ)·x + (B:ℚ)`.

It is a convenience rewriting lemma: it unfolds mathlib's generic `Affine.Equation` predicate for the
*specific* short model used by the Nagell–Lutz development, collapsing the five-coefficient Weierstrass
polynomial to the textbook short form by killing `a₁=a₂=a₃=0` and casting `A,B` from ℤ.

Variables / typeclasses (Lean side):
- `A B : ℤ` — the short Weierstrass coefficients.
- `x y : ℚ` — coordinates of the candidate affine point.

Hypotheses: none.

Conclusion (math): `(x,y) ∈ shortCurveQ A B  ⟺  y² = x³ + Ax + B`.
Conclusion (Lean): `(shortCurveQ A B).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + (A : ℚ) * x + (B : ℚ)`.

Proof body (one line):
```lean
simpa [shortCurveQ, shortCurveZ, add_assoc, add_comm, add_left_comm, mul_assoc]
  using (WeierstrassCurve.Affine.equation_iff (W := shortCurveQ A B) x y)
```
i.e. it is mathlib's `equation_iff` post-processed by `simp` to drop the zero coefficients and reorder.

### Size classification (Phase 2a)

Verdict: SMALL
Reason: Helper rewriting lemma — a specialisation of mathlib's `equation_iff` to one concrete model.
Not a named theorem, not a new structure, not a `## Main results` entry (the file docstring explicitly
calls it a "basic rewriting lemma").

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner def check is **n/a**. (The proof body is
a single `simpa`, but the one-liner gate concerns definitions, not lemmas.)

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found                              | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | short Weierstrass equation y²=x³+Ax+B affine point definition                           | yes  | `y² = x³ + Ax + B` (char ≠ 2,3 reduced model)    | Stanford crypto notes, LMFDB, Wikipedia all agree; standard textbook (Silverman AEC III.1) |
|  2 | WebSearch (general form)         | (covered by #1 results) general Weierstrass `y²+a₁xy+a₃y = x³+a₂x²+a₄x+a₆`              | yes  | full 5-coeff Weierstrass equation                | The short form is the char≠2,3 specialisation; mathlib's `Affine.Equation` is the general form |
|  3 | WebSearch (named-after / aliases)| "reduced Weierstrass equation" / "Weierstrass model"                                    | yes  | same as #1, aka reduced/short Weierstrass         | LMFDB ec.weierstrass_coeffs knowl |
|  4 | ChatGPT MCP                      | (MCP down per task note — fallback to WebSearch #1–3 + Silverman recall)               | n/a  | n/a — server unavailable                         | Standard form is uncontroversial textbook material; no second opinion needed |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                 | n/a  | (no references dir — only `overview/` present)   | dir absent; recorded n/a |
|  6 | nLab                             | "Weierstrass equation / elliptic curve"                                                 | n/a  | (textbook; nLab adds nothing beyond #1)          | Not a categorical subtlety; the affine equation is elementary |
|  7 | nCatLab                          | —                                                                                      | n/a  | not a categorical concept                        | n/a |
|  8 | Stacks Project                   | "Weierstrass equation"                                                                  | n/a  | not the relevant abstraction level               | Stacks treats Weierstrass models scheme-theoretically; the pointwise `Equation x y` predicate is mathlib-/Silverman-level |
|  9 | MathOverflow / MSE               | short vs general Weierstrass equation                                                   | yes  | confirms #1; char≠2,3 reduction standard          | No controversy on the form |
| 10 | recent arXiv (last 5 yrs)        | (search #1) formal proof Weierstrass group law                                          | yes  | arXiv 2302.10640 (Lean group-law formalisation)  | Confirms mathlib's general `Equation` is the community-standard formal encoding |

### Literature summary (Phase 3)

Concept identified as: the **affine (short / reduced) Weierstrass equation** of an elliptic curve,
`y² = x³ + Ax + B`.
Sources agree on the standard form: **yes**.
Most general standard form: the *full* Weierstrass equation
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` over a commutative ring — of which `y² = x³ + Ax + B` is the
char-≠-2,3 specialisation. Mathlib already encodes the general form as `WeierstrassCurve.Affine.Equation`
with rewriting lemma `WeierstrassCurve.Affine.equation_iff`.
Generality dimensions where the literature varies:
  - coefficient ring: short form usually stated over a field of char ≠ 2,3; general form over any comm ring (mathlib uses any comm ring).
  - coefficients: short form fixes `a₁=a₂=a₃=0`; general form keeps all five.
Disagreement with the literature: **none**. The lemma is just the general identity specialised to one
concrete model.

### Generality analysis — `shortCurveQ_equation_iff`

Literature-standard form (from Phase 3): the **general** Weierstrass `equation_iff`, already in mathlib
as `WeierstrassCurve.Affine.equation_iff` (any comm ring `R`, arbitrary `a₁…a₆`).

| # | Parameter / hypothesis        | Current Lean form                       | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|------------------------------------------|--------------------------------------------|---------------------|---------------------------------|
| 1 | base field                    | ℚ (`shortCurveQ`)                        | arbitrary comm ring `R`                     | yes                 | The general `equation_iff` is over any `R`; fixing ℚ is a pure specialisation |
| 2 | coefficients                  | `a₁=a₂=a₃=0`, `a₄=A`, `a₆=B` from ℤ     | arbitrary `a₁…a₆`                           | yes                 | Killing three coefficients is specialisation, not a new fact |
| 3 | curve                         | the concrete `shortCurveQ A B`           | arbitrary `W : WeierstrassCurve R`          | yes                 | `shortCurveQ` is a project-local def; the general lemma quantifies over all `W` |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — it is a triple specialisation (ring fixed to
ℚ, three coefficients zeroed, the curve pinned to `shortCurveQ A B`) of the mathlib-existing general
`equation_iff`.
Number of weakening opportunities found: 3 (all collapse to "use the general lemma").
Proposed restatement: **none for mathlib** — the maximally general statement *already exists in mathlib*
as `WeierstrassCurve.Affine.equation_iff`. This is therefore not a "generalise-then-add" case; it is a
"mathlib already has the general form" case.
Cost of restatement: n/a (the general form is already upstream).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                  | Applies? | Proposed reformulation | Mathlib downstream |
|----|---------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | bundled hypotheses → typeclasses?                                         | no       | —                      | the general lemma already uses the `WeierstrassCurve` structure |
|  2 | sequences/metric → filters/topology?                                      | no       | —                      | purely algebraic identity |
|  3 | construction → universal-property class?                                   | no       | —                      | n/a |
|  4 | set-with-predicate → bundled substructure?                                 | no       | —                      | n/a |
|  5 | field/metric-specific → weaken typeclasses?                                | yes      | use `equation_iff` over any comm ring | already done upstream |
|  6 | 1-categorical → higher-categorical?                                        | no       | —                      | n/a |
|  7 | concrete index → arbitrary monoid/group?                                   | no       | —                      | n/a |

Modern idiom available: **no** (the only "modernisation" — generalise the ring — is already realised by
the existing mathlib lemma). One-line reason: this is an elementary algebraic rewriting identity; the
contemporary mathlib form already exists and is what the proof calls.

### Diamond / defeq risk — n/a

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

### Mathlib search-status: `shortCurveQ_equation_iff`

[A] Lean-Finder       "Weierstrass affine equation iff y^2 = x^3"   not run (index stale); covered by [D]/[E]
[B] Loogle            `WeierstrassCurve.Affine.Equation _ _ ↔ _`     hit: `WeierstrassCurve.Affine.equation_iff` (general form)
[C] LeanSearch        "elliptic curve affine point on curve iff equation" hit: same `equation_iff`
[D] Grep mathlib src  `equation_iff` in `Mathlib/.../EllipticCurve/Affine/Basic.lean` → `equation_iff`
                      (line 156) + `equation_iff'` (152); no short-Weierstrass specialisation anywhere
[E] Name pattern      grep `short.*Weierstrass | shortWeierstrass | y ^ 2 = x ^ 3` in mathlib EllipticCurve/
                      → **no hits**. Mathlib has no `shortCurve`/`shortWeierstrass` def, hence no specialised
                      `equation_iff` for it.

Searched for both:
  - the user's current form (short model over ℚ) — **not in mathlib** (mathlib has no such concrete model)
  - the literature-standard / general form — **found**: `WeierstrassCurve.Affine.equation_iff`
    at `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:156`.

Concluded: **found building blocks** — the exact lemma `WeierstrassCurve.Affine.equation_iff` is the
general form; the project lemma is a one-`simp` specialisation of it. The short-model form itself is not
(and arguably should not be) in mathlib, because `shortCurveQ`/`shortCurveZ` are project-local
definitions tailored to Nagell–Lutz.

### Call sites — `shortCurveQ_equation_iff`

Internal use count: **1** (within NagellLutz, excluding the declaring file)
External-to-file callers: **1** distinct file

| Caller file:line                                                  | Usage pattern (one-line excerpt)                                   |
|-------------------------------------------------------------------|---------------------------------------------------------------------|
| projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralMain.lean:171 | `have hcurve := (shortCurveQ_equation_iff A B x y).mp hpt.left`   |

Inline-derivation grep: The **general** analogue `curveQ_equation_iff` (GeneralCurve.lean:33) and the
PID analogue `curveK_equation_iff` (PIDCurve.lean:35) are the *same wrapper pattern* over
`WeierstrassCurve.Affine.equation_iff`, used at ~9 sites across General*/PID* files. So within the
project the *general-coefficient* version of this wrapper is the heavily-used one; `shortCurveQ_equation_iff`
is the short-model twin used at exactly one site in the (legacy) short-model `GeneralMain` track.

### Composition check (Phase 6)

Can `shortCurveQ_equation_iff` be derived from mathlib in ≤3 chained calls?

Attempt 1: the proof *is already* a one-call composition:
```lean
(WeierstrassCurve.Affine.equation_iff (W := shortCurveQ A B) x y)  -- then `simp` to drop a₁=a₂=a₃=0 and cast
```
  - Mathlib decls used: `WeierstrassCurve.Affine.equation_iff` + the project's own `@[simp]` coefficient
    lemmas (`shortCurveQ_a₁…a₆`, all `rfl`/`simp`).
  - Result: **succeeds** — a single `simpa … using equation_iff` closes it (verbatim the current proof).
  - Notes: the only non-mathlib ingredients are the project's `shortCurveZ`/`shortCurveQ` defs and their
    `simp`-coefficient lemmas, which exist solely because the short model is project-local.

Conclusion: **COMPOSABLE** (1 mathlib call + `simp`). No new mathlib lemma is warranted.

## Verdict: `LutzNagell.LutzNagellTheorem.shortCurveQ_equation_iff`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): standard form is the general Weierstrass equation; the short form is its
  char≠2,3 specialisation; both well-known (Silverman AEC III.1, LMFDB).
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — a triple specialisation (ℚ, three
  zero coefficients, the concrete `shortCurveQ`) of the general lemma.
- Mathlib search (Phase 5): the general form `WeierstrassCurve.Affine.equation_iff` is in mathlib
  (`Affine/Basic.lean:156`); no short-model specialisation exists or is wanted (mathlib has no
  `shortCurveQ`).
- Composition check (Phase 6): COMPOSABLE — the existing proof is a single `equation_iff` call + `simp`.

**Rationale:**

`shortCurveQ_equation_iff` is not new mathematics: it is mathlib's `WeierstrassCurve.Affine.equation_iff`
specialised to one concrete, project-local Weierstrass model (`shortCurveQ A B`, the ℚ-base-change of
`{a₁=a₂=a₃=0, a₄=A, a₆=B}`). Its entire proof is `simpa … using (WeierstrassCurve.Affine.equation_iff …)`
— one mathlib call followed by `simp` to clear the zero coefficients and casts. Mathlib should **not**
gain a short-model variant, because the model `shortCurveQ`/`shortCurveZ` is bespoke to the Nagell–Lutz
development; the right mathlib primitive (`equation_iff`, in the general five-coefficient form over any
commutative ring) already exists and is exactly what the proof invokes.

This is therefore NO-composable-from-mathlib rather than NO-mathlib-has-it: mathlib has the *building
block*, not this exact specialised statement, and the statement is a ≤2-step composition (one
`equation_iff` + `simp`). It is a legitimate, convenient *project-internal* rewriting lemma — keeping it
in the project is fine — but it is below mathlib's bar as a standalone contribution. Note the project
already carries the more useful general-coefficient twin, `curveQ_equation_iff` (GeneralCurve.lean:33),
used at ~9 sites; `shortCurveQ_equation_iff` is the short-model variant used at exactly one site
(GeneralMain.lean:171).

**WHY not (refactor-actionable detail):**
Mathlib has the building block `WeierstrassCurve.Affine.equation_iff`; the project lemma is the
specialisation of it to `shortCurveQ A B`. No new mathlib lemma is needed.

Mathlib building blocks:
  - `WeierstrassCurve.Affine.equation_iff` — `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:156`
  - (project-side `@[simp]` glue: `shortCurveQ_a₁ … a₆`, all definitional)

Composition sketch (≤3 lines), exactly the current proof:
```lean
example (A B : ℤ) (x y : ℚ) :
    (shortCurveQ A B).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + (A : ℚ) * x + (B : ℚ) := by
  simpa [shortCurveQ, shortCurveZ, add_assoc, add_comm, add_left_comm, mul_assoc]
    using WeierstrassCurve.Affine.equation_iff (W := shortCurveQ A B) x y
```

Call sites in our project (from Phase 6.0): **K = 1** (GeneralMain.lean:171).

Refactor plan: this is a *project-internal* convenience lemma, not a mathlib candidate. Two acceptable
on-`main` outcomes — neither is a mathlib PR:
  1. **Keep as-is** (recommended): it is a clean, named, single-use wrapper that reads better than an
     inline `simpa` at the call site; harmless project API. The verdict only says "do not upstream".
  2. **Inline** (optional dedup): at GeneralMain.lean:171, replace
     `(shortCurveQ_equation_iff A B x y).mp hpt.left` with
     `((WeierstrassCurve.Affine.equation_iff (W := shortCurveQ A B) x y).mp hpt.left)` plus the `simp`
     normalisation, then delete the lemma. Given K=1 this is mechanical, but offers little benefit.

If a generalisation pass wants to *reduce duplication within the project*, the move is to drop
`shortCurveQ_equation_iff` in favour of the already-present general `curveQ_equation_iff` specialised at
the call site — but that is a project cleanup choice, not mathlib work.

**Next action:** Do **not** open a mathlib PR. Treat as project-internal: keep the lemma, or (optional
on-`main` cleanup) inline its single call site / fold it into the existing general `curveQ_equation_iff`.

---

## Next step

Do not upstream. Keep `shortCurveQ_equation_iff` as a project-internal wrapper, or optionally inline its
one call site (GeneralMain.lean:171) using `WeierstrassCurve.Affine.equation_iff` directly — a project
cleanup decision, not a mathlib contribution.

Sources:
- [Elliptic Curves — The Weierstrass Form (Stanford)](https://crypto.stanford.edu/pbc/notes/elliptic/weier.html)
- [LMFDB — Weierstrass equation/model](https://www.lmfdb.org/knowledge/show/ec.weierstrass_coeffs)
- [Elliptic curve — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_curve)
- [An Elementary Formal Proof of the Group Law on Weierstrass Elliptic Curves (arXiv 2302.10640)](https://arxiv.org/pdf/2302.10640)
