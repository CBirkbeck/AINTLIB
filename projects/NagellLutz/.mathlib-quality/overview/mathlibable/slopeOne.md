# /mathlibable report — `WeierstrassCurve.Universal.Affine.slopeOne`

## Verdict: **NO-composable-from-mathlib**

One-line rationale: a one-line `def` = mathlib's general `Affine.slope` at the
coincident generic point `(X,Y)`; inline `slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)`.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — task-sanctioned)
- decl `WeierstrassCurve.Universal.Affine.slopeOne`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:241`
- kind:                      `def` (noncomputable, in `noncomputable section`; `Classical.propDecidable` is a local instance)
- has sorry:                 no
- module docstring summary:  Proves `WeierstrassCurve.zsmul_eq_smulEval`: `n • P = (φₙ : ωₙ : ψₙ)`
  (Jacobian) / `(φₙ/ψₙ², ωₙ/ψₙ³)` (affine) for any integer `n` and nonsingular affine point `P`
  on a Weierstrass curve over a field. `slopeOne` is the n=1 doubling-slope helper en route.

Qualified name verified from source: namespaces `WeierstrassCurve` (line 76) →
`Universal` (line 86) → `Affine` (line 157); `def slopeOne` at line 241. The
parsed name `WeierstrassCurve.Universal.Affine.slopeOne` is **correct**.

Source (verbatim):
```lean
/-- The slope of the tangent line at the point (X,Y) on the universal curve. -/
def slopeOne : Universal.Field :=
  pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)
```
where (proved in the same file) `smulX 1 = polyToField (C X)` and
`smulY 1 = polyToField Y` are the coordinates of the generic point `(X,Y)`, and
`pointedCurve := baseChange curve Universal.Field` (Universal.lean:130) is the
universal Weierstrass curve over its fraction field `Universal.Field`.

---

### Statement (Phase 1)

`slopeOne` is the **slope of the tangent line to the universal Weierstrass curve
at its own generic point `(X, Y)`** — i.e. the slope used when *doubling* the
generic point. Concretely, it is mathlib's general chord–tangent slope function
`WeierstrassCurve.Affine.slope` applied to the generic point twice:
`slope X X Y Y`. Because the two argument points coincide and `(X,Y)` is not
2-torsion on the universal curve (`smulY 1 ≠ negY …`, proved at
`smulY_one_ne_negY`), this evaluates to the tangent-slope branch
`(3X² + 2a₂X + a₄ − a₁Y) / (2Y + a₁X + a₃)`. The file immediately proves the
closed form `slopeOne = −polyToField(curve.polynomialX) / ψᵤ 2`
(`slopeOne_eq_neg_div`, line 244) — i.e. `λ = −W_X(X,Y)/ψ₂` — and uses it only
to derive the doubling formulae `addX (smulX 1) (smulX 1) slopeOne = smulX 2`
and `addY … slopeOne = smulY 2`.

Variables / typeclasses involved (Lean side):
- No parameters of its own. Everything is fixed by the ambient `Universal`
  namespace: `pointedCurve : WeierstrassCurve Universal.Field`, the generic
  coordinates `smulX 1, smulY 1 : Universal.Field`. The base field
  `Universal.Field = Frac(ℤ[A₁..A₆,X,Y]/⟨W⟩)` is the universal/most-general
  Weierstrass base.
- Mathlib dependency: `WeierstrassCurve.Affine.slope (x₁ x₂ y₁ y₂ : F)`
  requires `[Field F] [DecidableEq F]` (supplied here by the local
  `Classical.propDecidable`).

Hypotheses (Lean side): none on the def.

Conclusion (math): the element `slope(X,X,Y,Y) = (3X²+2a₂X+a₄−a₁Y)/(2Y+a₁X+a₃) ∈
Frac(ℤ[A₁..A₆,X,Y]/⟨W⟩)`.
Conclusion (Lean): n/a — definition; type is `Universal.Field`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line helper `def` that fixes a general mathlib function
(`Affine.slope`) at a specific point. It introduces no new mathematical
structure, is not a named theorem, and is not a `## Main results` entry — it is
the `n = 1` rung of the doubling-formula scaffolding for the main result
`zsmul_eq_smulEval`. (Note: lit width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)`)
One-liner verdict: **ONE-LINER**

| Exemption                         | Applies? | Evidence                                                                 |
|-----------------------------------|----------|---------------------------------------------------------------------------|
| Avoid defeq abuse                 | no       | Downstream proofs immediately `rw [slopeOne, …]` or `rw [slopeOne_eq_neg_div]` to *unfold* it; the name is a label, not a defeq barrier. Nothing relies on it staying sealed. |
| Avoid typeclass diamonds          | no       | No instance is anchored by it; it returns a plain `Universal.Field` element. The only typeclass in play is `DecidableEq` on `slope`, resolved by the local classical instance independently of this def. |
| Mark semantic intent / API name   | weak/no  | It does carry a docstring ("slope of the tangent line at (X,Y)"), but the only consumers are 3 lemmas in the *same file*; no other file/project imports the name (HasseWeil re-derives its own copy). The semantic intent is fully carried by `slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)` itself. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** → biases Phase 7 toward
NO-composable-from-mathlib / NO-mathlib-has-it. (Carried into Phase 7.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic curve doubling formula tangent slope … (3x²+2a₂x+a₄−a₁y)/ψ₂"                                  | yes  | λ = (3x₁²+2a₂x₁+a₄−a₁y₁)/(2y₁+a₁x₁+a₃) | Trustica / Stanford-pbc / UConn-CTNT notes. The exact tangent-slope used for doubling on a general Weierstrass curve. |
|  2 | WebSearch (general/named form)   | "Silverman arithmetic elliptic curves duplication formula φₙ/ψₙ² generic point universal Weierstrass"   | yes  | [n]P = (φ/ψ², ω/ψ³); φₙ = xψₙ²−ψₙ₋₁ψₙ₊₁ | Silverman AEC; the *division-polynomial* x-coordinate formula. The slope is an unnamed step in deriving it. |
|  3 | WebFetch (Stanford explicit)     | crypto.stanford.edu/pbc/notes/elliptic/explicit.html — is the doubling slope a *named* object?          | yes  | "gradient of the tangent at the point", = (dE/dX)/(dE/dY) | Explicitly: "the document doesn't assign this a special formal name … contextually the slope needed to compute point doubling." |
|  4 | ChatGPT MCP                      | "Is the tangent/doubling slope a named standalone object, or the general chord-tangent slope at P=P?"   | n/a  | — | MCP/Codex down this session (Command failed, per task note). Fell back to channels 1–3 + 5–10, which answer the question conclusively. |
|  5 | Local references                 | `.mathlib-quality/references/` exists?                                                                  | n/a  | — | Directory is empty (`ls` returned nothing). Recorded n/a. |
|  6 | nLab                             | "elliptic curve" / "Weierstrass" tangent slope                                                          | n/a  | — | nLab treats elliptic curves scheme/moduli-theoretically; the affine doubling slope is not an nLab concept. n/a with reason. |
|  7 | nCatLab                          | (categorical reformulation of doubling slope)                                                           | n/a  | — | Not a categorical concept — a rational function on one curve. n/a. |
|  8 | Stacks Project                   | division polynomials / tangent slope                                                                    | n/a  | — | Stacks has no elliptic-curve division-polynomial / explicit-arithmetic chapter. n/a with reason. |
|  9 | MathOverflow / MSE               | "slope tangent line elliptic curve doubling Weierstrass name"                                           | yes  | same as #1; called "tangent slope" / "doubling slope" informally | Consistently an intermediate quantity, never a named definition. |
| 10 | recent arXiv (last 5 yrs)        | arXiv:0706.4379 (2-division), arXiv:1107.0506 (mean value formula on EC)                                | yes  | division-poly arithmetic; no named "slopeOne" | The slope appears only inside derivations; no paper elevates it to a named object. |

### Literature summary (Phase 3)

Concept identified as: **the tangent/doubling slope of a Weierstrass curve at a
point** — `λ = (3x²+2a₂x+a₄−a₁y)/(2y+a₁x+a₃)`, equivalently `−W_X(x,y)/W_Y(x,y)`
by implicit differentiation; here specialised to the **generic point `(X,Y)`** of
the universal curve.
Sources agree on the standard form: **yes** (channels 1, 3, 9 give the identical
generalized-Weierstrass tangent slope; channel 2 confirms it as the doubling step
feeding the φ/ψ² division-polynomial formula).
Most general standard form: the chord–tangent slope `slope(x₁,x₂,y₁,y₂)` of which
the doubling slope is the `(x₁,y₁)=(x₂,y₂)` case — exactly what mathlib's
`Affine.slope` already packages.
Generality dimensions where the literature varies: only the curve model (short
Weierstrass `y²=x³+ax+b` vs. general `a₁..a₆`). The project (and mathlib) use the
fully general model, so this is the maximal model.
Disagreement with the literature: **none** — but the literature **never names this
slope as a standalone object**. It is universally an unnamed intermediate equal to
the general chord–tangent slope evaluated at coincident points.

---

### Generality analysis — `WeierstrassCurve.Universal.Affine.slopeOne` (Phase 4)

Literature-standard form (from Phase 3): the chord–tangent slope at coincident
points, on a general Weierstrass curve over any field — i.e. `W.slope x x y y`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | base / curve           | `pointedCurve` over `Universal.Field` (the universal curve at its generic point) | any Weierstrass curve `W/F` and any non-2-torsion point `(x,y)` | yes | The general statement is `W.slope x x y y`; fixing the universal curve + generic point is a *specialisation*, not a generalisation. The general object already exists as `Affine.slope`. |
| 2 | point                  | the two coincident args are hard-wired to `smulX 1, smulY 1` (the generic point) | free `(x₁,y₁),(x₂,y₂)` | yes | `slopeOne` discards mathlib `slope`'s 4 arguments by fixing all four. This is strictly *less* general. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is a full
specialisation of mathlib's already-existing general `Affine.slope`).
Number of weakening opportunities found: 2 (curve+point both hard-wired).
Proposed restatement: there is nothing to restate *as a new def* — the maximally
general form is `WeierstrassCurve.Affine.slope`, which **already exists in
mathlib**. So the "generalise-first" target is not a new declaration; it is "use
the existing general `slope`". That makes this a NO bucket, not
YES-but-generalise-first (see Phase 7 gate).
Cost of "restatement": CHEAP — it is literally `slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)`.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream |
|---|----------|----------|------------------------|--------------------|
| 1 | bundled-hypothesis → typeclass? | no | the def has no hypotheses to bundle | — |
| 2 | sequences/metric → filters/topology? | no | purely algebraic rational function | — |
| 3 | construction → universal-property class? | no | it is one element of a field, not a constructed object with a UP | — |
| 4 | set+closure-pred → bundled substructure? | no | not a substructure | — |
| 5 | field/metric-specific → weaken typeclass? | no | already at the general Weierstrass model; `slope` needs `Field` essentially (division) | — |
| 6 | 1-categorical → higher-categorical? | no | not categorical | — |
| 7 | concrete index ℕ/ℤ/ℝ → general monoid? | no | the "1" in `slopeOne` is just "the n=1 doubling case", not an index to generalise; the right object is the *un-indexed* general `slope` | — |

Modern-idiom verdict: **no** — the contemporary mathlib idiom for "tangent slope
at a point" is *already* `WeierstrassCurve.Affine.slope x x y y`. There is no
further modernisation; `slopeOne` is a step *away* from the idiom (it hides the
general function behind a point-specific name).
One-line reason: the general, idiomatic object already exists in mathlib and is
what the def calls.

---

### Diamond / defeq risk — `WeierstrassCurve.Universal.Affine.slopeOne` (Phase 4.5)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | Returns a `Universal.Field` element; anchors no instance; no search path depends on it. |
| 2 | Reducibility leak | none | Not `@[reducible]`; sealed `def`. Even if unfolded it is just a `slope` application. |
| 3 | Non-canonical unfolding | low | Downstream proofs *deliberately* `rw [slopeOne]`/`rw [slopeOne_eq_neg_div]`; unfolding is intended and controlled, not surprising. |
| 4 | Instance priority collision | n/a | Not an `instance`. |
| 5 | Universe-polymorphism issues | none | Monomorphic in the fixed `Universal.Field`. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)
Overall risk: **NONE**. Top risks: none. (Risk is not what blocks this from
mathlib; redundancy is.)

---

### Mathlib search-status: `WeierstrassCurve.Universal.Affine.slopeOne` (Phase 5)

[A] Lean-Finder       "tangent slope elliptic curve doubling", "slope of curve at point"   no hit on a `slopeOne`/tangent-slope helper (only the general `slope`)
[B] Loogle            `WeierstrassCurve.Affine.slope`, `_ → _ → _ → _ → F` slope pattern    HIT: `WeierstrassCurve.Affine.slope` is THE general object; no specialised `slopeOne`
[C] LeanSearch        "slope of tangent line to Weierstrass curve at a point"                returns `Affine.slope` + its `slope_of_Y_ne` lemmas; no dedicated doubling-slope def
[D] Grep mathlib src  `def .*[Ss]lope` under `AlgebraicGeometry/EllipticCurve/`             only `Affine/Formula.lean:168 def slope`; no `slopeOne`, `tangentSlope`, `dblSlope`; `Universal`/generic-point EDS development absent from mathlib entirely
[E] Name pattern      `slopeOne`, `Universal.Affine.slope*`                                  no hit in mathlib; the *only* in-repo hits are this project + an independent duplicate in HasseWeil

Searched for both:
  - user's current form (`slope` at the generic point twice) — not in mathlib
  - literature-standard form (general chord–tangent slope) — **IS** in mathlib as
    `WeierstrassCurve.Affine.slope` (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean:168`),
    with full API: `slope_of_Y_eq`, `slope_of_Y_ne`, `slope_of_Y_ne'`,
    `slope_of_X_ne`, `slope_of_Y_ne_eq_evalEval`.

Concluded: **found the building block** — mathlib has the general
`WeierstrassCurve.Affine.slope`; `slopeOne` is that function specialised to the
generic point. Mathlib does NOT have a dedicated `slopeOne`/tangent-slope def,
and has no universal-curve / generic-point division-polynomial development at all.

---

### Call sites — `WeierstrassCurve.Universal.Affine.slopeOne` (Phase 6.0)

Internal use count: **K = 3** (within NagellLutz, excluding the declaring lines 241 + the closed-form lemma 244)
External-to-file callers: **0 distinct files** (every use is inside `ZSMul.lean`; nothing else in NagellLutz imports it)

| Caller file:line               | Usage pattern (one-line excerpt)                                                  |
|--------------------------------|-----------------------------------------------------------------------------------|
| LutzNagell/ZSMul.lean:246      | `rw [slopeOne, Affine.slope_of_Y_ne rfl smulY_one_ne_negY, …]` (proving `slopeOne_eq_neg_div`) |
| LutzNagell/ZSMul.lean:262      | `pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2`               |
| LutzNagell/ZSMul.lean:278      | `pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2`     |

Inline-derivation grep (re-derived elsewhere without using `slopeOne`?):
  - **HasseWeil** independently re-derives the *same* def:
    `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:312 def slopeOne := … slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)`
    (+ its own `slopeOne_eq_neg_div`, `addX_smul_one_smul_one`, `addY_smul_one_smul_one`).
    HasseWeil's `EC/GenericPointZsmul.lean:319` defines yet another `slopeOne`
    abbreviation for `(W_KE W).toAffine.slope …` over a different field model.
    → This is a cross-project *duplicate* of the same one-liner, confirming it is
    boilerplate scaffolding, not a singular API surface.

Signal (per the call-sites table): K = 3 internal uses but all confined to the
declaring file, no external consumers, and the identical statement is
independently re-derived in another project → **NO-composable** leaning: it is a
file-local convenience wrapper around mathlib's `slope`, not a shared abstraction.

### Composition check (Phase 6)

Can `slopeOne` be derived from mathlib in ≤3 chained calls?

Attempt 1: it is *definitionally* one mathlib call.
  - `slopeOne` ≡ `pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)`
  - Mathlib decls used: `WeierstrassCurve.Affine.slope` (1 call; `smulX 1`,
    `smulY 1` are the project's already-defined generic coordinates).
  - Result: **succeeds** — this is the literal body of the def. Zero reasoning
    steps; a single application of an existing mathlib function.
  - Notes: the closed form `−W_X/ψ₂` (`slopeOne_eq_neg_div`) is a *separate*
    lemma the project still wants; that lemma is genuine content about the
    universal curve, but `slopeOne` the *def* is pure specialisation.

Conclusion: **COMPOSABLE** — `slopeOne = pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)` is a single mathlib call (≤3). The def adds a name, not mathematics.

---

## Verdict: `WeierstrassCurve.Universal.Affine.slopeOne`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the tangent/doubling slope is a *standard but
  unnamed* intermediate = the general chord–tangent slope at `P=P`; no source
  elevates it to a named object.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — a full
  specialisation of the general `slope`; the maximally-general form already
  exists in mathlib (`Affine.slope`), so there is no *new* def to generalise to.
- Mathlib search (Phase 5): the general `WeierstrassCurve.Affine.slope` exists
  (`Affine/Formula.lean:168`) with full API; no dedicated `slopeOne` / tangent-
  slope helper; no universal-curve EDS development in mathlib.
- Composition check (Phase 6): **COMPOSABLE** — `slopeOne` is a single
  `Affine.slope` call at the generic point.

**Rationale:**

`slopeOne` is a one-line, hypothesis-free `def` whose entire body is mathlib's
general `WeierstrassCurve.Affine.slope` applied to the universal curve's generic
point `(X,Y)` in both argument slots: `slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)`.
The literature (Silverman AEC; the standard explicit-arithmetic notes) treats the
"tangent slope when doubling a point" as an *unnamed* intermediate quantity equal
to the chord–tangent slope specialised to coincident points — exactly the object
mathlib already packages as `Affine.slope`. So this is not new mathematical
content: it is mathlib's `slope` with all four arguments fixed. The Phase-4b
generality verdict (STRICTLY NARROWER) combined with "the general form already
exists in mathlib" places this firmly in a NO bucket rather than
YES-but-generalise-first (there is nothing new to add — the general object is
already upstream). Because the body is a single mathlib call (≤3, zero reasoning),
the precise bucket is NO-composable-from-mathlib: inline the `slope` application
at each call site. The one-liner-without-exemption finding (Phase 2b) and the
call-site pattern (K=3, all in the declaring file, plus an independent duplicate
in HasseWeil) reinforce this — it is file-local boilerplate, not a shared API.

Note this verdict is about **`slopeOne` in isolation**. The surrounding *result*
— the universal-curve division-polynomial doubling/`n`-torsion apparatus
(`smulX`, `smulY`, `slopeOne_eq_neg_div = −W_X/ψ₂`, `addX_smul_one_smul_one`,
`zsmul_eq_smulEval`) — is genuine, non-trivial content and is plausibly
mathlib-worthy as a package; that is a separate assessment (see the sibling
`smulX.md` report, which lands BORDERLINE for exactly this packaging reason). The
`slopeOne` *definition*, however, contributes no mathematics on its own.

**WHY not (refactor-actionable):**
Mathlib has the building block — `WeierstrassCurve.Affine.slope` — and `slopeOne`
is the 1-call specialisation `slope x x y y` at the generic point. No new lemma is
justified for the *definition* (the genuinely new fact is the *closed form*
`slopeOne_eq_neg_div`, which is a separate lemma and would be re-stated directly
about `pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)`).

Mathlib building blocks:
  - `WeierstrassCurve.Affine.slope` — `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean:168`
  - (supporting, already used at the call sites) `WeierstrassCurve.Affine.slope_of_Y_ne`
    — `…/Affine/Formula.lean:184`

Composition sketch (the def *is* the composition):
```lean
-- in place of `slopeOne`, everywhere:
pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)
```

Call sites in our project (from Phase 6.0): **K = 3** — all in `LutzNagell/ZSMul.lean`
(lines 246, 262, 278).

Refactor plan (NagellLutz-local; do **not** upstream the def):
- This is project scaffolding, not a mathlib candidate, so the action is to keep
  it as a private/file-local helper **or** inline it — not to PR it.
- If inlining: at line 246 (`slopeOne_eq_neg_div`), 262
  (`addX_smul_one_smul_one`), and 278 (`addY_smul_one_smul_one`), replace
  `slopeOne` with `pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)`
  (argument types already match — all four are `smulX 1 / smulY 1 : Universal.Field`).
  The `slopeOne_eq_neg_div` lemma is then a statement *about that `slope`
  expression* and stays as the project's genuine contribution.
- Cross-project: the identical duplicate in HasseWeil
  (`Auxiliary/DivisionPolynomial.lean:312`) is a separate `/cleanup` dedup target
  — if the universal-curve apparatus is ever consolidated into `Common/`, the two
  `slopeOne` copies collapse to one (or vanish via inlining).

Next action: do **not** open a mathlib PR for `slopeOne`. Treat it as a file-local
helper (optionally mark `private`/inline at the 3 call sites). Route the genuine
content (the universal-curve doubling closed forms) through the package-level
assessment (`smulX.md`, BORDERLINE) rather than this definition.

---

## Next step

Do not upstream `slopeOne` as its own declaration — it is `Affine.slope` at the
generic point. Either keep it as a `private`/file-local helper or inline
`pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)` at the three
NagellLutz call sites (ZSMul.lean:246,262,278). The mathlib-worthiness question
belongs to the surrounding universal-curve division-polynomial *package*
(`smulX`/`smulY`/`zsmul_eq_smulEval`), assessed separately as BORDERLINE — not to
this one-line definition.
